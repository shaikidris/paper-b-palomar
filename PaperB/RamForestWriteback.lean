module

public import PaperB.RamForestSeed
public import PaperB.RamSliceCopy
public import PaperB.RamRegisterTrace
public import PaperB.RamForestPhaseLink

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram
open PaperB.Machine (Word)

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw
local notation "Small" => PaperB.RamSliceCopy.layout bits inputCap workCap hi hw
local notation "RamState" => PaperB.RamProgram.State

private def copyRegs : Fin 7 → Fin 15
  | 0 => registers.ptr
  | 1 => childrenBase
  | 2 => tinBase
  | 3 => toutBase
  | 4 => registers.one
  | 5 => registers.value
  | 6 => registers.tmp

private theorem copyRegs_injective : ∀ {i j}, copyRegs i = copyRegs j → i = j :=
  fun {i j} => (by decide : ∀ (i j : Fin 7), copyRegs i = copyRegs j → i = j) i j

private def wideCopy (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  embedProgram copyRegs (PaperB.RamSliceCopy.standalone bits inputCap workCap hi hw)

private theorem run_wideCopy (input : Input L)
    (x : PaperB.RamSliceCopy.Transfer bits workCap) (s : RamState L)
    (pc : s.pc = 0) (cursor : (reg s registers.ptr).val = 0)
    (words : (reg s childrenBase).val = x.count)
    (source : (reg s tinBase).val = x.src)
    (target : (reg s toutBase).val = x.dst)
    (unit : (reg s registers.one).val = 1) :
    ∃ t, run (wideCopy hi hw) input (7 * x.count + 2) s = some ⟨t, 7 * x.count + 2⟩ ∧
      SliceCopy.Prefix s.data t.data x.src x.dst x.count := by
  let small : RamState Small :=
    ⟨Array.ofFn (fun i : Fin 7 => reg s (copyRegs i)), s.data, s.pc,
      Array.size_ofFn, s.data_size⟩
  let readOnly : Input Small := ⟨input.words, input.size_eq⟩
  have agree : ArenaAgreement copyRegs s small s := by
    refine ⟨rfl, rfl, ?_, fun _ _ => rfl⟩
    intro r
    have idx : r.val < (Array.ofFn (fun i : Fin 7 => reg s (copyRegs i))).size := by
      rw [Array.size_ofFn]; exact r.isLt
    change (Array.ofFn (fun i : Fin 7 => reg s (copyRegs i)))[r.val]'idx = _
    rw [Array.getElem_ofFn]
    exact congrArg (fun i : Fin 7 => reg s (copyRegs i)) (Fin.ext rfl)
  have cfg : PaperB.RamSliceCopy.Invariant x small.data 0 0 small :=
    ⟨pc, (congrArg Fin.val (agree.reg_eq (0 : Fin 7))).trans cursor,
      (congrArg Fin.val (agree.reg_eq (1 : Fin 7))).trans words,
      (congrArg Fin.val (agree.reg_eq (2 : Fin 7))).trans source,
      (congrArg Fin.val (agree.reg_eq (3 : Fin 7))).trans target,
      (congrArg Fin.val (agree.reg_eq (4 : Fin 7))).trans unit, SliceCopy.Prefix.zero _ _ _⟩
  obtain ⟨t, _, hr, copied, _, _⟩ := PaperB.RamSliceCopy.standalone_exact readOnly x small cfg
  obtain ⟨work, halt, route, stop, count⟩ := run_has_steps_then_halt hr
  obtain ⟨_, wide, steps, haltWide, finish⟩ :=
    route.embedRegisterFramesWithStore_thenHalt stop copyRegs_injective
      (show readOnly.words = input.words from rfl) agree
  have exactWork := steps.halts haltWide
  change 7 * x.count + 2 = work + 1 at count
  rw [← count] at exactWork
  have data := finish.data_eq
  change t.data = wide.data at data
  change SliceCopy.Prefix s.data t.data x.src x.dst x.count at copied
  exact ⟨wide, exactWork, data ▸ copied⟩

private def copySetup : List (Instr bits 15) :=
  [.add childrenBase count count, .sub toutBase registers.stackBase childrenBase]

/-- Copy the two interval columns to the two adjacent banks immediately
before the working arena. Other already-encoded columns may precede them. -/
def writebackProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  copySetup.toArray ++ (wideCopy hi hw).map (relocateInstr 2)

private theorem writebackPlaced :
    RelocatedSlice (wideCopy hi hw) (writebackProgram hi hw) 2 := by
  intro i op fetch
  have position : 2 ≤ 2 + i := by omega
  unfold writebackProgram
  rw [Array.getElem?_append_right (by exact position)]
  change ((wideCopy hi hw).map (relocateInstr 2))[2 + i - 2]? = _
  rw [show 2 + i - 2 = i by omega, Array.getElem?_map, fetch, Option.map_some]

private theorem writebackSize : (writebackProgram hi hw).size = 10 := by
  rw [writebackProgram, Array.size_append, Array.size_map]
  have size : (wideCopy hi hw).size = 8 :=
    @size_embedProgram bits Small L copyRegs _
  rw [size]
  rfl

/-- Exact transfer from the live DFS endpoint banks. The code computes its
copy length and destination itself and runs in the same 15-register arena. -/
theorem run_writeback (input : Input L) {a : Arena bits workCap n}
    (reserved : 2 * n ≤ a.base) (s : RamState L) (pc : s.pc = 0)
    (ctrl : Control a s) (empty : (reg s registers.ptr).val = 0) :
    let dst := a.base - 2 * n
    ∃ t trace,
      run (writebackProgram hi hw) input (14 * n + 4) s = some ⟨t, 14 * n + 4⟩ ∧
      SliceCopy.Prefix s.data t.data a.tin dst (2 * n) ∧
      SuccessfulTrace (writebackProgram hi hw) input s trace ⟨t, 14 * n + 4⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let code := writebackProgram hi hw
  have size : code.size = 10 := writebackSize
  have width := a.wordFits
  have room := a.room
  let spec : PaperB.RamSliceCopy.Transfer bits workCap :=
    { src := a.tin, dst := a.base - 2 * n, count := 2 * n,
      src_end := by unfold Arena.tin; omega,
      dst_end := by omega,
      disjoint := Or.inl (by unfold Arena.tin; omega),
      count_fits := by omega }
  have get0 : code[s.pc]? = some (.add childrenBase count count) := by
    rw [pc]
    unfold code writebackProgram
    rw [Array.getElem?_append_left (show 0 < 2 by decide)]
    rfl
  obtain ⟨p, pstep, ppc, pval, pregs, pdata⟩ := step_add_at (input := input) get0 (by omega)
  have sumFit : (reg s count).val + (reg s count).val < 2 ^ bits := by
    rw [ctrl.count_eq]; omega
  have pLength : (reg p childrenBase).val = 2 * n := by
    rw [pval, PaperB.WordOps.add_no_wrap _ _ sumFit, ctrl.count_eq]
    omega
  have get1 : code[p.pc]? = some (.sub toutBase registers.stackBase childrenBase) := by
    rw [ppc, pc]
    unfold code writebackProgram
    rw [Array.getElem?_append_left (show 0 + 1 < 2 by decide)]
    rfl
  obtain ⟨q, qstep, qpc, qval, qregs, qdata⟩ := step_sub_at (input := input) get1 (by omega)
  have pBase : (reg p registers.stackBase).val = a.base :=
    (congrArg Fin.val (pregs _ (show registers.stackBase ≠ childrenBase by decide))).trans
      ctrl.stackBase_eq
  have noWrap : (reg p childrenBase).val ≤ (reg p registers.stackBase).val := by
    rwa [pLength, pBase]
  have qTarget : (reg q toutBase).val = spec.dst := by
    rw [qval, PaperB.WordOps.sub_val, pBase, pLength]
    change (2 ^ bits + a.base - 2 * n) % (2 ^ bits) = a.base - 2 * n
    rw [show 2 ^ bits + a.base - 2 * n = 2 ^ bits + (a.base - 2 * n) by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have follow (r : Fin 15) (keepTar : r ≠ toutBase) (keepLen : r ≠ childrenBase) :
      reg q r = reg s r := (qregs r keepTar).trans (pregs r keepLen)
  let start : RamState L := {q with pc := 0}
  have startPtr : (reg start registers.ptr).val = 0 :=
    (congrArg Fin.val (follow _ (show registers.ptr ≠ toutBase by decide)
      (show registers.ptr ≠ childrenBase by decide))).trans empty
  have startLen : (reg start childrenBase).val = spec.count :=
    (congrArg Fin.val (qregs _ (show childrenBase ≠ toutBase by decide))).trans pLength
  have startSrc : (reg start tinBase).val = spec.src :=
    (congrArg Fin.val (follow _ (show tinBase ≠ toutBase by decide)
      (show tinBase ≠ childrenBase by decide))).trans ctrl.tin_eq
  have startUnit : (reg start registers.one).val = 1 :=
    (congrArg Fin.val (follow _ (show registers.one ≠ toutBase by decide)
      (show registers.one ≠ childrenBase by decide))).trans ctrl.one
  obtain ⟨t, hr, copied⟩ :=
    run_wideCopy input spec start rfl startPtr startLen startSrc qTarget startUnit
  obtain ⟨k, u, localSteps, localHalt, exactCount⟩ := run_has_steps_then_halt hr
  have placed : RelocatedSlice (wideCopy hi hw) code 2 := writebackPlaced
  have nextPC : q.pc = 2 := by rw [qpc, ppc, pc]
  have initialEq : relocateStatePC 2 start = q := by
    cases q
    cases nextPC
    rfl
  have runCopy := localSteps.relocate placed
  rw [initialEq] at runCopy
  have execute := (Steps.cons pstep (Steps.cons qstep (Steps.zero q))).append runCopy
  obtain ⟨haltSlot, finalEq⟩ := halted_fetch_and_state localHalt
  have stop : step code input (relocateStatePC 2 u) =
      some (.halted (relocateStatePC 2 t)) := by
    change t = u at finalEq
    rw [finalEq]
    exact step_halt_at (s := relocateStatePC 2 u) (placed u.pc .halt haltSlot)
  have total := execute.halts stop
  change 7 * (2 * n) + 2 = k + 1 at exactCount
  have totalCost : 2 + k + 1 = 14 * n + 4 := by omega
  rw [totalCost] at total
  obtain ⟨trace, success⟩ := run_has_successfulTrace total
  have sameData : start.data = s.data := qdata.trans pdata
  refine ⟨relocateStatePC 2 t, trace, total, ?_, success, success.peak_eq⟩
  rw [sameData] at copied
  exact copied

private theorem seededSize : (seededProgram hi hw).size = 43 := by
  unfold seededProgram FixedROM.join
  erw [Array.size_append, Array.size_set, Array.size_map, program_size]
  rfl

private def isNotHalt {r : Nat} : Instr bits r → Bool
  | .halt => false
  | _ => true

private theorem seededHaltIndex {i : Nat}
    (hit : (seededProgram hi hw)[i]? = some .halt) : i = 42 := by
  have bound : i < (seededProgram hi hw).size := by
    by_cases hi' : i < (seededProgram hi hw).size
    · exact hi'
    · have absent : (seededProgram hi hw)[i]? = none := getElem?_neg _ _ hi'
      rw [absent] at hit
      cases hit
  rw [seededSize] at bound
  by_cases before : i < 42
  · have all : ((seededProgram hi hw).toList.take 42).all isNotHalt = true := by
      unfold seededProgram FixedROM.join
      simp only [Array.toList_append, Array.toList_map]
      rfl
    have cell : ((seededProgram hi hw).toList.take 42)[i]? = some .halt := by
      rw [List.getElem?_take_of_lt before, Array.getElem?_toList, hit]
    have no : isNotHalt (.halt : Instr bits 15) =
        true := List.all_eq_true.mp all _ (List.mem_of_getElem? cell)
    cases no
  · omega

/-- One fixed program runs the seed, the DFS, and the final writeback.
The two output columns occupy the last two banks before the DFS arena. -/
def serializedProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  FixedROM.join (seededProgram hi hw) (writebackProgram hi hw) 42
    (seededSize ▸ (show 42 < 43 by decide))

/-- The serialized traversal is a phase in the parent-to-output program. -/
def serializationPhase : FixedROM.Phase L :=
  let traversal : FixedROM.Phase L :=
    ⟨seededProgram hi hw, 42, by rw [seededSize]; decide,
      FixedROM.relocated_right (seedCode hi hw) (program hi hw)
        (haltIdx := 10) (show 10 < 11 by decide) 31 .halt halt_fetch,
      fun _ hit => seededHaltIndex hit⟩
  let copy : FixedROM.Phase L := FixedROM.Phase.ofLast (writebackProgram hi hw) 9
    writebackSize (by
      unfold writebackProgram
      rw [Array.getElem?_append_right (show 2 ≤ 9 by decide), Array.getElem?_map,
        show (copySetup (bits := bits)).toArray.size = 2 from rfl]
      unfold wideCopy embedProgram
      rw [Array.getElem?_map]
      rfl) (by
      unfold writebackProgram wideCopy embedProgram
      simp only [Array.toList_append, Array.toList_map]
      rfl)
  traversal.link copy

theorem serializationPhase_code :
    (serializationPhase (hi := hi) (hw := hw)).code = serializedProgram hi hw := rfl

/-- From the prepared CSR image, actual single-program execution creates
the two serialized interval columns and preserves all earlier output
cells. The bound counts every instruction, and peak counts the input,
whole reserved work arena and registers at every step. -/
theorem run_serialized_tree (input : Input L) {a : Arena bits workCap n}
    {g : PaperB.ForestLayout.ChildLists n} {root : Fin n} {parent : Fin n → Fin n}
    {depth : Fin n → Nat}
    (tree : PaperB.LabelledQuotient.ValidDepthTree root parent depth)
    (rows : g = PaperB.ForestLayout.bucketChildLists root parent)
    (mass : a.children ≤ n) (reserved : 2 * n ≤ a.base)
    (s : RamState L) (ready : SeedInput a g root s) :
    let dst := a.base - 2 * n
    let final := PaperB.ForestLayout.layout g root (2 * n)
    ∃ (u : RamState L) (states : List (RamState L)) (work : Nat),
      ColumnAt (n := n) dst final.entries u.data ∧
      ColumnAt (n := n) (dst + n) final.ends u.data ∧
      (∀ j < dst, u.data[j]? = s.data[j]?) ∧
      work ≤ 64 * n + 13 ∧
      run (serializedProgram hi hw) input work s = some ⟨u, work⟩ ∧
      SuccessfulTrace (serializedProgram hi hw) input s states ⟨u, work⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 := by
  let rom := serializedProgram hi hw
  have slot : 42 < (seededProgram hi hw).size := by rw [seededSize]; decide
  obtain ⟨u, _, work, entries, ends, limit, dfs, _, _, regValues, ptr, _, prefixFrame⟩ :=
    run_seeded_tree input tree rows mass s ready
  let init : RamState L := {u with pc := 0}
  have control : Control a init :=
    ⟨regValues.count_eq, regValues.one, regValues.zero, regValues.stackBase_eq,
      regValues.tin_eq, regValues.tout_eq, regValues.offset_eq, regValues.child_eq⟩
  have segment : Steps rom input work s (relocateStatePC 43 init) := by
    have start : relocateStatePC 0 s = s := by cases s; simp [relocateStatePC]
    have jump := linked_return_of_run_multi (linked := rom) (base := 0)
      (ret := fun _ => 43) dfs
      (fun i op hit nonhalt => by
        have distinct : i ≠ 42 := by
          intro eq
          subst i
          have endFetch : (seededProgram hi hw)[42]? = some .halt := by
            have h := FixedROM.relocated_right (seedCode hi hw) (program hi hw)
              (haltIdx := 10) (show 10 < 11 by decide) 31 .halt halt_fetch
            exact h
          exact nonhalt (Option.some.inj (hit.symm.trans endFetch))
        have fetch := FixedROM.fetch_left (seededProgram hi hw) (writebackProgram hi hw)
          slot distinct hit
        have eq : relocateInstr 0 op = op := by cases op <;> simp [relocateInstr]
        simpa only [rom, serializedProgram, Nat.zero_add, eq] using fetch)
      (fun i hit => by
        have eq := seededHaltIndex hit
        subst i
        have fetch := FixedROM.fetch_halt (seededProgram hi hw) (writebackProgram hi hw) slot
        rw [seededSize] at fetch
        exact ⟨fetch.1, fetch.2 (by rw [writebackSize]; decide)⟩)
    rw [start] at jump
    exact jump
  obtain ⟨t, _, copy, copied, _, _⟩ := run_writeback input reserved init rfl control ptr
  obtain ⟨k, h, steps, halt, cost⟩ := run_has_steps_then_halt copy
  have placed : RelocatedSlice (writebackProgram hi hw) rom 43 := by
    have slice := FixedROM.relocated_right (seededProgram hi hw) (writebackProgram hi hw) slot
    unfold RelocatedSlice at slice
    intro i op hit
    have fetch := slice i op hit
    change rom[(seededProgram hi hw).size + i]? =
      some (relocateInstr (seededProgram hi hw).size op) at fetch
    rw [seededSize] at fetch
    exact fetch
  have execute := segment.append (steps.relocate placed)
  obtain ⟨fetch, equal⟩ := halted_fetch_and_state halt
  have stop : step rom input (relocateStatePC 43 h) =
      some (.halted (relocateStatePC 43 t)) := by
    change t = h at equal
    rw [equal]
    exact step_halt_at (s := relocateStatePC 43 h) (placed h.pc .halt fetch)
  have result := execute.halts stop
  obtain ⟨states, complete⟩ := run_has_successfulTrace result
  change 14 * n + 4 = k + 1 at cost
  refine ⟨relocateStatePC 43 t, states, work + k + 1, ?_, ?_, ?_, ?_,
    result, complete, complete.peak_eq⟩
  · intro i
    change (t.data[a.base - 2 * n + i.val]?).map Fin.val = _
    rw [copied.copied i.val (by have := i.isLt; omega)]
    exact entries i
  · intro i
    change (t.data[(a.base - 2 * n) + n + i.val]?).map Fin.val = _
    rw [Nat.add_assoc, copied.copied (n + i.val) (by have := i.isLt; omega)]
    have addr : a.tin + (n + i.val) = a.tout + i.val := by
      unfold Arena.tin Arena.tout
      omega
    rw [addr]
    exact ends i
  · intro i small
    change t.data[i]? = _
    exact (copied.untouched i (Or.inl small)).trans (prefixFrame i (by omega))
  · omega

theorem serializationPhase_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) :
    (serializationPhase (bits := bits) (inputCap := c₁) (workCap := d₁) (hi := h₁) (hw := k₁)).code =
      (serializationPhase (bits := bits) (inputCap := c₂) (workCap := d₂) (hi := h₂) (hw := k₂)).code ∧
    (serializationPhase (bits := bits) (inputCap := c₁) (workCap := d₁) (hi := h₁) (hw := k₁)).haltPC =
      (serializationPhase (bits := bits) (inputCap := c₂) (workCap := d₂) (hi := h₂) (hw := k₂)).haltPC := by
  have hSeed : seededProgram (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ =
      seededProgram (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ := by
    unfold seededProgram
    have h1 : seedCode (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ =
        seedCode (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ := rfl
    have h2 : program (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ =
        program (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ :=
      program_cap_indep h₁ k₁ h₂ k₂
    simp only [FixedROM.join, h1, h2]
  have hWide : wideCopy (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ =
      wideCopy (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ := by
    apply Array.ext
    · rw [wideCopy, @size_embedProgram bits (PaperB.RamSliceCopy.layout bits c₁ d₁ h₁ k₁) (layout bits c₁ d₁ h₁ k₁) copyRegs,
        wideCopy, @size_embedProgram bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) copyRegs]
      rfl
    · intro i hi1 hi2
      have eq1 := getElem?_pos (wideCopy h₁ k₁) i hi1
      have eq2 := getElem?_pos (wideCopy h₂ k₂) i hi2
      apply Option.some.inj
      rw [← eq1, ← eq2, wideCopy, wideCopy,
        @getElem?_embedProgram bits (PaperB.RamSliceCopy.layout bits c₁ d₁ h₁ k₁) (layout bits c₁ d₁ h₁ k₁) copyRegs,
        @getElem?_embedProgram bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) copyRegs]
      have hEq : (PaperB.RamSliceCopy.standalone bits c₁ d₁ h₁ k₁ : Array (Instr bits 7)) =
          PaperB.RamSliceCopy.standalone bits c₂ d₂ h₂ k₂ := rfl
      cases hOp1 : (PaperB.RamSliceCopy.standalone bits c₁ d₁ h₁ k₁ : Array (Instr bits 7))[i]? with
      | none =>
        have hOp2 : (PaperB.RamSliceCopy.standalone bits c₂ d₂ h₂ k₂ : Array (Instr bits 7))[i]? = none :=
          (congrArg (fun (a : Array (Instr bits 7)) => a[i]?) hEq.symm).trans hOp1
        exact (congrArg (Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) copyRegs)) hOp2).symm
      | some op =>
        have hOp2 : (PaperB.RamSliceCopy.standalone bits c₂ d₂ h₂ k₂ : Array (Instr bits 7))[i]? = some op :=
          (congrArg (fun (a : Array (Instr bits 7)) => a[i]?) hEq.symm).trans hOp1
        have hMid : Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₁ d₁ h₁ k₁) (layout bits c₁ d₁ h₁ k₁) copyRegs) (some op) =
            Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) copyRegs) (some op) := by
          dsimp only [Option.map]; cases op <;> rfl
        exact hMid.trans
          (congrArg (Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) copyRegs)) hOp2).symm
  have hWb : writebackProgram (bits := bits) (inputCap := c₁) (workCap := d₁) h₁ k₁ =
      writebackProgram (bits := bits) (inputCap := c₂) (workCap := d₂) h₂ k₂ := by
    change copySetup.toArray ++ (wideCopy h₁ k₁).map (relocateInstr 2) =
      copySetup.toArray ++ (wideCopy h₂ k₂).map (relocateInstr 2)
    rw [hWide]
  refine ⟨?_, ?_⟩
  · simp only [serializationPhase_code, serializedProgram, FixedROM.join, hSeed, hWb]
  · unfold serializationPhase FixedROM.Phase.link FixedROM.Phase.ofLast
    dsimp only
    rw [hSeed]

end PaperB.RamForestProgram.Finish
