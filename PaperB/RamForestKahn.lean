module

public import PaperB.RamForestRawInterface

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.RawBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.ArcParents
open PaperB.RamForestProgram.ArcDecode
open PaperB.ForestHead (Vertex)
open PaperB.ForestPreparedBuild (IsTopologicalOrder orderRanks orderRanks_at orderRanks_increasing orderRanks_rankArc isTopologicalOrder_of_rank)
open PaperB.KahnDecreasing (readRank)
open _root_.EX24.PreparedSweep (orderedVertexAt)

/-! ### Shared RAM step, phase-linking, and upper-frame helpers -/

section RamHelpers

variable {bits : Nat} {L : Layout bits}

private def putReg (s : State L) (d : Fin L.registerCount) (w : Word bits) : State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_putReg (s : State L) (d r : Fin L.registerCount) (w : Word bits) :
    reg (putReg s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp only [he, ite_false]
    exact Array.getElem_set_ne hd hr hv.symm

private theorem putReg_data (s : State L) (d : Fin L.registerCount) (w : Word bits) :
    (putReg s d w).data = s.data := rfl

private theorem putReg_pc (s : State L) (d : Fin L.registerCount) (w : Word bits) :
    (putReg s d w).pc = s.pc + 1 := rfl

theorem step_imm_at {code : Program L} {input : Input L} {s : State L}
    {d : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  have hs : step code input s = some (.next (putReg s d w)) := by
    unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  refine ⟨putReg s d w, hs, putReg_pc s d w, ?_, ?_, putReg_data s d w⟩
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

theorem step_loadInput_at {code : Program L} {input : Input L} {s : State L}
    {d a : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a)) (hn : s.pc + 1 < code.size)
    (hw : input.words[(reg s a).val]? = some w) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  have hs : step code input s = some (.next (putReg s d w)) := by
    unfold step
    rw [hf]
    change (input.words[(reg s a).val]? >>= fun v =>
      if s.pc + 1 < code.size then some (Transition.next (putReg s d v)) else none) = _
    rw [hw]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d w)) else none) = _
    rw [ite_eq_left hn]
  refine ⟨putReg s d w, hs, putReg_pc s d w, ?_, ?_, putReg_data s d w⟩
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

theorem sub_exact (x y : Word bits) (hle : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  have hx := x.isLt
  have hlt : x.val - y.val < 2 ^ bits := by omega
  rw [sub_val, show 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits by omega, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hlt]

theorem branchLt_true {x y : Word bits} (h : x.val < y.val) : ltb x y = true :=
  (ltb_eq_true x y).mpr h

theorem branchLt_false {x y : Word bits} (h : y.val ≤ x.val) : ltb x y = false := by
  cases hc : ltb x y with
  | false => rfl
  | true =>
    have hlt := (ltb_eq_true x y).mp hc
    omega

theorem place_slice (pre block suffix : List (Instr bits L.registerCount)) :
    Placed (L := L) (pre ++ (block ++ suffix)).toArray pre.length block :=
  placed_link pre block suffix

theorem placed_sub {code : Program L} {entry : Nat} {a b c : List (Instr bits L.registerCount)}
    (hp : Placed code entry (a ++ b ++ c)) : Placed code (entry + a.length) b := by
  intro i op hi
  have hsum : entry + (a.length + i) = (entry + a.length) + i := by omega
  rw [← hsum]
  apply hp (a.length + i) op
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    show a.length + i - a.length = i by omega]
  have hlt : i < b.length := by
    by_cases h : i < b.length
    · exact h
    · have hn : b[i]? = none := List.getElem?_eq_none (by omega)
      rw [hn] at hi
      cases hi
  exact (List.getElem?_append_left hlt).trans hi

/-- Convert a list of `Phase`s into a single `Phase` whose `.code` equals `pipeline phases`. -/
def pipelinePhase : List (Phase L) → Phase L
  | [] => Phase.ofLast #[.halt] 0 rfl rfl rfl
  | p :: ps => Phase.link p (pipelinePhase ps)

theorem pipelinePhase_code (phases : List (Phase L)) :
    (pipelinePhase phases).code = pipeline phases := by
  induction phases with
  | nil => rfl
  | cons p ps ih =>
    change join p.code (pipelinePhase ps).code p.haltPC p.haltFits =
      join p.code (pipeline ps) p.haltPC p.haltFits
    rw [ih]

theorem reg_eq_of_regs_eq {s t : State L} (h : t.regs = s.regs) (r : Fin L.registerCount) :
    reg t r = reg s r := by
  change t.regs[r.val]'(by rw [t.regs_size]; exact r.isLt) =
    s.regs[r.val]'(by rw [s.regs_size]; exact r.isLt)
  simp only [h]

theorem step_mov_at {code : Program L} {input : Input L} {s : State L}
    {d src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s src ∧ (∀ r : Fin L.registerCount, r ≠ d → reg t r = reg s r) ∧
      t.data = s.data := by
  have hs : step code input s = some (.next (putReg s d (reg s src))) := by
    unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next (putReg s d (reg s src))) else none) = _
    rw [ite_eq_left hn]
  refine ⟨putReg s d (reg s src), hs, putReg_pc s d (reg s src), ?_, ?_, putReg_data s d (reg s src)⟩
  · simp [reg_putReg]
  · intro r hr
    simp [reg_putReg, hr]

end RamHelpers

section Ram15Helpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L15" => layout bits inputCap workCap hi hw

theorem step_imm15 {code : Program L15} {input : Input L15} {s : State L15}
    {d : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L15, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_imm_at hf hn

theorem step_mov15 {code : Program L15} {input : Input L15} {s : State L15}
    {d src : Fin 15}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L15, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = reg s src ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_mov_at hf hn

theorem step_loadInput15 {code : Program L15} {input : Input L15} {s : State L15}
    {d a : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a)) (hn : s.pc + 1 < code.size)
    (hw' : input.words[(reg s a).val]? = some w) :
    ∃ t : State L15, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t d = w ∧ (∀ r : Fin 15, r ≠ d → reg t r = reg s r) ∧ t.data = s.data :=
  step_loadInput_at hf hn hw'

theorem step_add15 {code : Program L15} {input : Input L15} {s : State L15}
    {dst lhs rhs : Fin 15}
    (hf : code[s.pc]? = some (.add dst lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L15, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t dst = add (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  step_add_at hf hn

theorem step_sub15 {code : Program L15} {input : Input L15} {s : State L15}
    {dst lhs rhs : Fin 15}
    (hf : code[s.pc]? = some (.sub dst lhs rhs)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L15, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t dst = sub (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  step_sub_at hf hn

theorem indexedInputRead15 {code : Program L15} {input : Input L15}
    {s : State L15} {entry : Nat} {dst base index : Fin 15}
    (placed : Placed code entry (indexedInputRead dst base index))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hbound : (reg s base).val + (reg s index).val < inputCap) :
    ∃ t : State L15, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      some (reg t dst) = input.words[(reg s base).val + (reg s index).val]? ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  indexedInputRead_steps placed hpc hexit hbound

theorem indexedDataRead15 {code : Program L15} {input : Input L15}
    {s : State L15} {entry : Nat} {dst base index : Fin 15}
    (placed : Placed code entry (indexedDataRead dst base index))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hbound : (reg s base).val + (reg s index).val < workCap) :
    ∃ t : State L15, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      some (reg t dst) = s.data[(reg s base).val + (reg s index).val]? ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  indexedDataRead_steps placed hpc hexit hbound

theorem indexedDataWrite15 {code : Program L15} {input : Input L15}
    {s : State L15} {entry : Nat} {tmp base index src : Fin 15}
    (placed : Placed code entry (indexedDataWrite tmp base index src))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hsrc : src ≠ tmp)
    (hbound : (reg s base).val + (reg s index).val < workCap) :
    ∃ t : State L15, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      t.data = s.data.set ((reg s base).val + (reg s index).val)
        (reg s src) (by simpa only [s.data_size] using hbound) ∧
      reg t tmp = add (reg s base) (reg s index) ∧
      (∀ r : Fin 15, r ≠ tmp → reg t r = reg s r) :=
  indexedDataWrite_steps placed hpc hexit hsrc hbound

end Ram15Helpers

/-! ### Upper-frame guarantee for `rawIncomingProgram` -/

section RawIncomingFrame

variable {vertices arcs bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw
local notation "K" => (vertices + 1 + arcs)

private def fiParentPrepPhase : Phase L :=
  Phase.ofLast (ArcParents.code hi hw) 12 rfl rfl rfl

private def fiPrepPhase : Phase L :=
  Phase.ofLast (prepareParentPhase hi hw) 3 rfl rfl rfl

private def fiClearPhase : Phase L :=
  Phase.ofLast (zeroDegreeProgram hi hw) 5 rfl rfl rfl

private def fiHistPhase : Phase L :=
  Phase.ofLast (parentScanCode histogramBody) 13 rfl rfl rfl

private def fiOffsetPhase : Phase L :=
  Phase.ofLast (offsetProgram hi hw) 10 rfl rfl rfl

private def fiScatterPhase : Phase L :=
  Phase.ofLast (parentScanCode scatterBody) 18 rfl rfl rfl

private def fiCsrPhases : List (Phase L) :=
  [fiPrepPhase, fiClearPhase, fiPrepPhase, fiHistPhase, fiPrepPhase, fiOffsetPhase,
    fiPrepPhase, fiScatterPhase]

/-- `Phase L` wrapper around `rawIncomingProgram`. -/
def rawIncomingPhase : Phase L :=
  Phase.link (fiParentPrepPhase (hi := hi) (hw := hw)) (pipelinePhase fiCsrPhases)

theorem rawIncomingPhase_code :
    (rawIncomingPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw)).code = rawIncomingProgram := by
  change join (ArcParents.code hi hw) (pipelinePhase fiCsrPhases).code 12 _ =
    join (ArcParents.code hi hw) (pipeline _) 12 _
  rw [pipelinePhase_code]
  rfl

private theorem fiOnEntry {a : Arena bits workCap K} {r : Fin K} {i : Nat}
    {s : State L} (h : ParentCursor a r i s) : ParentCursor a r i (Phase.initial s) :=
  h.unchanged (fun _ _ => rfl)

private theorem fiOffsetCursor {a : Arena bits workCap K} {s t : State L} {r : Fin K}
    (h : ParentCursor a r 0 s)
    (frame : ∀ q : Fin 15, q ≠ registers.ptr → q ≠ clk → q ≠ registers.value →
      q ≠ registers.tmp → reg t q = reg s q)
    (ptr : (reg t registers.ptr).val = K) : ParentCursor a r K t := by
  have eq (q : Fin 15) (hp : q ≠ registers.ptr) (hc : q ≠ clk) (hv : q ≠ registers.value)
      (ht : q ≠ registers.tmp) : (reg t q).val = (reg s q).val :=
    congrArg Fin.val (frame q hp hc hv ht)
  refine ⟨⟨(eq count (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.count_eq,
      (eq registers.one (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.one,
      (eq registers.zero (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.zero,
      (eq registers.stackBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.stackBase_eq,
      (eq tinBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.tin_eq,
      (eq toutBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.tout_eq,
      (eq offsetBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.offset_eq,
      (eq childrenBase (by decide) (by decide) (by decide) (by decide)).trans h.ctrl.child_eq⟩,
    (eq cmd (by decide) (by decide) (by decide) (by decide)).trans h.rootVal, ptr⟩

private structure UpperScatterInv (a : Arena bits workCap K) (root : Fin K)
    (parent : Fin K → Fin K) (orig : Array (Word bits)) (i : Nat)
    (data : Array (Word bits)) : Prop where
  parents : ParentAt a parent data
  offsets : OffsetAt a root parent data
  counters : ∀ p : Fin K, (data[a.tin + p.val]?).map Fin.val = some (vacant root parent i p)
  upperFrame : ∀ j, a.payload + a.children ≤ j → data[j]? = orig[j]?

private theorem upperScatter_skip {a : Arena bits workCap K} {root : Fin K}
    {parent : Fin K → Fin K} {orig data : Array (Word bits)}
    (h : UpperScatterInv a root parent orig root.val data) :
    UpperScatterInv a root parent orig (root.val + 1) data := by
  have same (p : Fin K) : visitedRows root parent (root.val + 1) p =
      visitedRows root parent root.val p := by rw [visitedRows_succ]; simp
  refine ⟨h.parents, h.offsets, ?_, h.upperFrame⟩
  intro p
  simpa only [vacant, same] using h.counters p

private theorem upperScatter_body (input : Input L) {a : Arena bits workCap K}
    {root : Fin K} {parent : Fin K → Fin K} {orig : Array (Word bits)}
    (mass : rowPrefix (parentDegree root parent) K ≤ a.children) :
    ParentBodySpec input scatterBody a root (UpperScatterInv a root parent orig) := by
  intro u nonroot s pc cursor old
  let code : Program L := parentScanCode (scatterBody (bits := bits))
  have placed : Placed code 4 (scatterBody (bits := bits)) := parentBody_placed _
  have size : code.size = 19 := parentScan_size scatterBody
  have room := a.room
  have width := a.wordFits
  have ul := u.isLt
  have pl := (parent u).isLt
  let start := rowStart root parent (parent u)
  let left := vacant root parent (u.val + 1) (parent u)
  have free : vacant root parent u.val (parent u) = left + 1 :=
    vacant_step root parent u nonroot
  have rowRoom : start + left < a.children := by
    have len : vacant root parent u.val (parent u) ≤ parentDegree root parent (parent u).val :=
      Nat.sub_le _ _
    have endpoint : start + parentDegree root parent (parent u).val ≤
        rowPrefix (parentDegree root parent) K :=
      rowPrefix_mono _ (parent u).isLt
    omega
  have placePair {entry : Nat} {op0 op1 : Instr bits 15}
      (h0 : code[entry]? = some op0) (h1 : code[entry + 1]? = some op1) :
      Placed code entry [op0, op1] := by
    intro i op h
    cases i with
    | zero => rw [Nat.add_zero]; exact h0.trans h
    | succ i =>
      cases i with
      | zero => exact h1.trans h
      | succ i => simp at h
  have keepCursor (d : Fin 15) (hd : d ∈ parentScratch) {p q : State L}
      (hc : ParentCursor a root u.val p) (hf : ∀ r, r ≠ d → reg q r = reg p r) :
      ParentCursor a root u.val q :=
    hc.unchanged (fun r hr => hf r (fun eq => hr (eq ▸ hd)))
  have read0 : Placed code 4 (indexedDataRead registers.remain registers.stackBase registers.ptr) :=
    placePair (placed 0 _ rfl) (placed 1 _ rfl)
  have bound0 : (reg s registers.stackBase).val + (reg s registers.ptr).val < workCap := by
    rw [cursor.ctrl.stackBase_eq, cursor.ptrVal]; omega
  obtain ⟨v, sv, vpc, pvRead, vr, vm⟩ :=
    indexedDataRead_steps (input := input) (s := s) read0 pc (by omega) bound0
  have pVal : (reg v registers.remain).val = (parent u).val := by
    rw [cursor.ctrl.stackBase_eq, cursor.ptrVal] at pvRead
    have vv := congrArg (Option.map Fin.val) pvRead
    rw [old.parents u] at vv
    exact Option.some.inj vv
  have vc := keepCursor registers.remain (by decide +revert) cursor vr
  have read1 : Placed code 6 (indexedDataRead registers.value tinBase registers.remain) :=
    placePair (placed 2 _ rfl) (placed 3 _ rfl)
  have bound1 : (reg v tinBase).val + (reg v registers.remain).val < workCap := by
    rw [vc.ctrl.tin_eq, pVal]; unfold Arena.tin; omega
  obtain ⟨w, vw, wpc, wRead, wr, wm⟩ :=
    indexedDataRead_steps (input := input) read1 vpc (by omega) bound1
  have wc := keepCursor registers.value (by decide +revert) vc wr
  have wValue : (reg w registers.value).val = left + 1 := by
    rw [vc.ctrl.tin_eq, pVal, vm] at wRead
    have vv := congrArg (Option.map Fin.val) wRead
    rw [old.counters (parent u), free] at vv
    exact Option.some.inj vv
  have dec : code[w.pc]? = some (.sub registers.value registers.value registers.one) := by
    rw [wpc]; exact placed 4 _ rfl
  obtain ⟨x, wx, xpc, xValue, xr, xm⟩ := step_sub_at (input := input) dec (by omega)
  have xc := keepCursor registers.value (by decide +revert) wc xr
  have xLeft : (reg x registers.value).val = left := by
    rw [xValue, sub_val, wValue, wc.ctrl.one]
    rw [show 2 ^ bits + (left + 1) - 1 = 2 ^ bits + left by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have xParent : (reg x registers.remain).val = (parent u).val := by
    rw [xr _ (show registers.remain ≠ registers.value by decide),
      wr _ (show registers.remain ≠ registers.value by decide), pVal]
  have put0 : Placed code 9 (indexedDataWrite registers.tmp tinBase registers.remain registers.value) :=
    placePair (placed 5 _ rfl) (placed 6 _ rfl)
  have bound2 : (reg x tinBase).val + (reg x registers.remain).val < workCap := by
    rw [xc.ctrl.tin_eq, xParent]; unfold Arena.tin; omega
  obtain ⟨y, xy, ypc, yMem, _, yr⟩ := indexedDataWrite_steps (input := input)
    (s := x) put0 (by omega) (by omega) (show registers.value ≠ registers.tmp by decide) bound2
  have yc := keepCursor registers.tmp (by decide +revert) xc yr
  have yParent : (reg y registers.remain).val = (parent u).val := by
    rw [yr _ (show registers.remain ≠ registers.tmp by decide), xParent]
  have degreeWrite : y.data = s.data.set (a.tin + (parent u).val) (reg x registers.value)
      (by rw [s.data_size]; change a.tin + (parent u).val < workCap; unfold Arena.tin; omega) := by
    simpa only [xc.ctrl.tin_eq, xParent, xm, wm, vm] using yMem
  have degreeFrame (j : Nat) (hne : j ≠ a.tin + (parent u).val) : y.data[j]? = s.data[j]? := by
    rw [degreeWrite]
    exact Array.getElem?_set_ne _ hne.symm
  have read2 : Placed code 11 (indexedDataRead clk offsetBase registers.remain) :=
    placePair (placed 7 _ rfl) (placed 8 _ rfl)
  have bound3 : (reg y offsetBase).val + (reg y registers.remain).val < workCap := by
    rw [yc.ctrl.offset_eq, yParent]; unfold Arena.offsets; omega
  obtain ⟨z, yz, zpc, zRead, zr, zm⟩ := indexedDataRead_steps (input := input)
    (s := y) read2 ypc (by omega) bound3
  have zc := keepCursor clk (by decide +revert) yc zr
  have zOffset : (reg z clk).val = start := by
    rw [yc.ctrl.offset_eq, yParent, degreeFrame _ (by unfold Arena.tin Arena.offsets; omega)] at zRead
    have vv := congrArg (Option.map Fin.val) zRead
    rw [old.offsets (parent u).val (by omega)] at vv
    exact Option.some.inj vv
  have zLeft : (reg z registers.value).val = left := by
    rw [zr _ (show registers.value ≠ clk by decide),
      yr _ (show registers.value ≠ registers.tmp by decide), xLeft]
  have addInstr : code[z.pc]? = some (.add clk clk registers.value) := by
    rw [zpc]; exact placed 9 _ rfl
  obtain ⟨b, zb, bpc, bVal, br, bm⟩ := step_add_at (input := input) addInstr (by omega)
  have bc := keepCursor clk (by decide +revert) zc br
  have sumFits : (reg z clk).val + (reg z registers.value).val < 2 ^ bits := by
    rw [zOffset, zLeft]; omega
  have index : (reg b clk).val = start + left := by
    rw [bVal, add_no_wrap _ _ sumFits, zOffset, zLeft]
  have put1 : Placed code 14 (indexedDataWrite registers.tmp childrenBase clk registers.ptr) :=
    placePair (placed 10 _ rfl) (placed 11 _ rfl)
  have bound4 : (reg b childrenBase).val + (reg b clk).val < workCap := by
    rw [bc.ctrl.child_eq, index]; unfold Arena.payload; omega
  obtain ⟨t, bt, tpc, tm, _, tr⟩ := indexedDataWrite_steps (input := input)
    (s := b) put1 (by omega) (by omega) (show registers.ptr ≠ registers.tmp by decide) bound4
  have tc := keepCursor registers.tmp (by decide +revert) bc tr
  have payloadWrite : t.data = y.data.set (a.payload + start + left) (reg b registers.ptr)
      (by rw [y.data_size]; change a.payload + start + left < workCap; unfold Arena.payload; omega) := by
    simpa only [bc.ctrl.child_eq, index, bm, zm, Nat.add_assoc] using tm
  have payloadFrame (j : Nat) (hne : j ≠ a.payload + start + left) : t.data[j]? = y.data[j]? := by
    rw [payloadWrite]
    exact Array.getElem?_set_ne _ hne.symm
  have keepBoth (j : Nat) (h0 : j ≠ a.tin + (parent u).val) (h1 : j ≠ a.payload + start + left) :
      t.data[j]? = s.data[j]? :=
    (payloadFrame j h1).trans (degreeFrame j h0)
  refine ⟨t, sv.append (vw.append (.cons wx (xy.append (yz.append (.cons zb bt))))),
    tpc, tc, ?_, ?_, ?_, ?_⟩
  · intro q
    have nq := q.isLt
    rw [keepBoth _ (by unfold Arena.tin; omega) (by unfold Arena.payload; omega)]
    exact old.parents q
  · intro j hj
    rw [keepBoth _ (by unfold Arena.tin Arena.offsets; omega)
      (by unfold Arena.offsets Arena.payload; omega)]
    exact old.offsets j hj
  · intro p
    by_cases e : p = parent u
    · subst p
      have sep : a.tin + (parent u).val ≠ a.payload + start + left := by
        unfold Arena.tin Arena.payload; omega
      rw [payloadFrame _ sep, degreeWrite, Array.getElem?_set_self, Option.map_some, xLeft]
    · have sameVis : visitedRows root parent (u.val + 1) p = visitedRows root parent u.val p := by
        rw [visitedRows_succ]
        exact ite_eq_right (fun h => e h.2)
      rw [keepBoth _ (fun h => e (Fin.ext (Nat.add_left_cancel h)))
        (by unfold Arena.tin Arena.payload; dsimp only [start, left]; have := p.isLt; omega)]
      simpa only [vacant, sameVis] using old.counters p
  · intro j hj
    rw [keepBoth j (by unfold Arena.tin Arena.payload at *; dsimp only [start, left] at *; omega)
      (by dsimp only [start, left] at *; omega)]
    exact old.upperFrame j hj

private theorem run_parent_scatter_upper_frame (input : Input L) {a : Arena bits workCap K}
    (root : Fin K) (parent : Fin K → Fin K) (s : State L)
    (pc : s.pc = 0) (cursor : ParentCursor a root 0 s)
    (par : ParentAt a parent s.data) (offsets : OffsetAt a root parent s.data)
    (counters : ∀ p : Fin K, (s.data[a.tin + p.val]?).map Fin.val =
      some (parentDegree root parent p.val))
    (mass : rowPrefix (parentDegree root parent) K ≤ a.children) :
    ∃ t work, work ≤ 17 * K + 2 ∧
      run (parentScanCode (scatterBody (bits := bits))) input work s = some ⟨t, work⟩ ∧
      (∀ j, a.payload + a.children ≤ j → t.data[j]? = s.data[j]?) := by
  have start : UpperScatterInv a root parent s.data 0 s.data := by
    refine ⟨par, offsets, ?_, fun _ _ => rfl⟩
    simpa only [vacant, visitedRows_zero, List.length_nil, Nat.sub_zero] using counters
  obtain ⟨t, _, work, bound, exec, _, inv, _, _⟩ :=
    run_parent_scan input scatterBody (upperScatter_body input mass)
      (fun _ c => upperScatter_skip c) s pc cursor start
  exact ⟨t, work, bound, exec, inv.upperFrame⟩

/-- `run_raw_incoming` paired with an explicit upper-frame preservation guarantee
for all addresses `j ≥ a.payload + a.children`. -/
theorem run_raw_incoming_framed (input : Input L) (a : Arena bits workCap K)
    (heads : Fin arcs → Fin vertices) (headAddr : Nat) (inputFit : headAddr + arcs ≤ inputCap)
    (raw : HeadsAt input headAddr heads) (space : K - 1 ≤ a.children) (s : State L)
    (cursor : ParentCursor a (root vertices arcs) 0 s)
    (split : (reg s clk).val = vertices + 1)
    (headBase : (reg s registers.childBase).val = headAddr) :
    ∃ t trace work, work ≤ 52 * K + 29 ∧ IncomingAt a heads t.data ∧
      (∀ j, a.payload + a.children ≤ j → t.data[j]? = s.data[j]?) ∧
      run (rawIncomingPhase (hi := hi) (hw := hw)).code input work (Phase.initial s) =
        some ⟨t, work⟩ ∧
      SuccessfulTrace (rawIncomingPhase (hi := hi) (hw := hw)).code input (Phase.initial s)
        trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨t, trace, work, wBound, inc, exec, sTrace, peak⟩ :=
    run_raw_incoming input a heads headAddr inputFit raw space s cursor split headBase
  have upper : ∀ j, a.payload + a.children ≤ j → t.data[j]? = s.data[j]? := by
    obtain ⟨p, _, _, _, pr, state, parents, pFrame, _, _⟩ :=
      run_arc_parents input heads headAddr inputFit raw (Phase.initial s) rfl
        (cursor.unchanged (fun _ _ => rfl)) split headBase
    let x : PaperB.PackedStaticLayout.Input K :=
      ⟨root vertices arcs, PaperB.PackedStaticLayout.tabulate (parent heads),
        PaperB.PackedStaticLayout.tabulate (depth (vertices := vertices) (arcs := arcs))⟩
    have mass : rowPrefix (parentDegree (root vertices arcs) (parent heads)) K ≤ a.children := by
      have hp : x.parent.read = parent heads := funext (PaperB.PackedStaticLayout.read_tabulate _)
      have hd : x.depth.read = depth (vertices := vertices) (arcs := arcs) :=
        funext (PaperB.PackedStaticLayout.read_tabulate _)
      have ht : ValidDepthTree x.root x.parent.read x.depth.read := by
        rw [show x.root = root vertices arcs from rfl, hp, hd]
        exact parent_tree heads
      have pm := packed_parent_mass x ht
      change rowPrefix (parentDegree (root vertices arcs) x.parent.read) K = K - 1 at pm
      rw [hp] at pm
      omega
    have current : ParentCursor a (root vertices arcs) (reg p registers.ptr).val p :=
      ⟨state.ctrl, state.rootVal, rfl⟩
    obtain ⟨z0, f0, zcur, _, _, zdat⟩ := run_prepare_parent_phase input _ rfl (fiOnEntry current)
    obtain ⟨z, _, cz, zdone, zeroes, zkeep, _, _⟩ := run_zero_degrees input _ rfl (fiOnEntry zcur)
    obtain ⟨h0, f1, hcur, _, _, hdat⟩ := run_prepare_parent_phase input _ rfl (fiOnEntry zdone)
    simp only [Phase.initial_data] at zdat zkeep hdat
    have hp : ParentAt a (parent heads) h0.data := by
      intro v
      have vlt := v.isLt
      rw [hdat, zkeep _ (Or.inl (by unfold Arena.tin; omega)), zdat]
      exact parents v
    have hz : ∀ q : Fin K, (h0.data[a.tin + q.val]?).map Fin.val = some 0 := by
      intro q; rw [hdat]; exact zeroes q
    obtain ⟨h, _, _, _, ch, hdone, hpar, hdeg, hkeep, _, _⟩ :=
      run_parent_histogram input (root vertices arcs) (parent heads) _ rfl (fiOnEntry hcur) hp hz
    obtain ⟨o0, f2, ocur, clock, _, odat⟩ := run_prepare_parent_phase input _ rfl (fiOnEntry hdone)
    simp only [Phase.initial_data] at hkeep odat
    have oi : OffsetInput a (parentDegree (root vertices arcs) (parent heads)) (Phase.initial o0) := by
      refine ⟨rfl, ocur.ptrVal, clock, (fiOnEntry ocur).ctrl, ?_, mass⟩
      intro j hj
      change (o0.data[a.tin + j]?).map Fin.val = _
      rw [odat]; exact hdeg ⟨j, hj⟩
    obtain ⟨o, _, co, off, okeep, _, _, oframe, optr⟩ := run_csr_offsets_with_frame input _ oi
    have odone := fiOffsetCursor (fiOnEntry ocur) oframe optr
    obtain ⟨c0, f3, ccur, _, _, cdat⟩ := run_prepare_parent_phase input _ rfl (fiOnEntry odone)
    simp only [Phase.initial_data] at okeep cdat
    have cp : ParentAt a (parent heads) c0.data := by
      intro v
      have vlt := v.isLt
      rw [cdat, okeep _ (Or.inl (by unfold Arena.offsets; omega)), odat]
      exact hpar v
    have cd : ∀ q : Fin K, (c0.data[a.tin + q.val]?).map Fin.val =
        some (parentDegree (root vertices arcs) (parent heads) q.val) := by
      intro q
      have qlt := q.isLt
      rw [cdat, okeep _ (Or.inl (by unfold Arena.offsets Arena.tin; omega)), odat]
      exact hdeg q
    have cOff : OffsetAt a (root vertices arcs) (parent heads) c0.data := by
      intro j jle; rw [cdat]; exact off j jle
    obtain ⟨c, _, _, cc, cFrame⟩ := run_parent_scatter_upper_frame input (root vertices arcs)
      (parent heads) _ rfl (fiOnEntry ccur) cp cOff cd mass
    have phases : PhasesRun input (fiCsrPhases (hi := hi) (hw := hw)) p (Phase.initial c) _ :=
      .cons f0 (.cons cz (.cons f1 (.cons ch (.cons f2 (.cons co (.cons f3 (.cons cc .nil)))))))
    obtain ⟨q, _, _, qData, qExec, _, _⟩ := run_pipeline phases
    have fullNonempty : 0 < (pipeline (fiCsrPhases (bits := bits) (inputCap := inputCap)
        (workCap := workCap) (hi := hi) (hw := hw))).size := pipeline_nonempty _
    obtain ⟨u, _, _, uData, uExec, _, _⟩ :=
      run_linked_pair fiParentPrepPhase (pipeline fiCsrPhases) fullNonempty pr qExec
    have eqRes := run_success_unique exec uExec
    have eqState : t = u := congrArg Result.finalState eqRes
    intro j hj
    have hjBase : a.base + K ≤ j := by unfold Arena.payload at hj; omega
    have hjTin : a.tin + K ≤ j := by unfold Arena.payload at hj; unfold Arena.tin; omega
    have hjOff : a.offsets + K + 1 ≤ j := by unfold Arena.payload at hj; unfold Arena.offsets; omega
    rw [eqState, uData, qData]
    simp only [Phase.initial_data] at *
    rw [cFrame j hj, cdat, okeep j (Or.inr hjOff), odat,
      hkeep j (Or.inr hjTin), hdat, zkeep j (Or.inr hjTin), zdat, pFrame j (Or.inr hjBase)]
  rw [rawIncomingPhase_code]
  exact ⟨t, trace, work, wBound, inc, upper, exec, sTrace, peak⟩

end RawIncomingFrame

/-! ### Reusable zero-fill kernel (`zeroBankPhase`) -/

section ZeroBank

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def zeroBankAssembly : List (Instr bits 15) :=
  [.branchLt registers.ptr count 1 5] ++
    indexedDataWrite registers.tmp tinBase registers.ptr registers.zero ++
    [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]

/-- Zero-fill `s.data[tinBase .. tinBase + count)` in `5 * count + 2` steps. -/
def zeroBankPhase : Phase L :=
  Phase.ofLast zeroBankAssembly.toArray 5 rfl rfl rfl

structure ZeroBankParams (base len : Nat) (s : State L) : Prop where
  ptr : (reg s registers.ptr).val = 0
  countVal : (reg s count).val = len
  baseVal : (reg s tinBase).val = base
  zeroVal : (reg s registers.zero).val = 0
  oneVal : (reg s registers.one).val = 1
  room : base + len ≤ workCap

private theorem zeroBank_step (input : Input L) (base len : Nat) (origState : State L)
    (room : base + len ≤ workCap) (k : Nat) (hk : k < len) :
    BlockSpec (zeroBankPhase (hi := hi) (hw := hw)).code input 5
      (fun s => s.pc = 0 ∧ (reg s registers.ptr).val = k ∧ (reg s count).val = len ∧
        (reg s tinBase).val = base ∧ (reg s registers.zero).val = 0 ∧
        (reg s registers.one).val = 1 ∧
        (∀ i < k, (s.data[base + i]?).map Fin.val = some 0) ∧
        (∀ j, (j < base ∨ base + k ≤ j) → s.data[j]? = origState.data[j]?) ∧
        (∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.tmp → reg s r = reg origState r))
      (fun s => s.pc = 0 ∧ (reg s registers.ptr).val = k + 1 ∧ (reg s count).val = len ∧
        (reg s tinBase).val = base ∧ (reg s registers.zero).val = 0 ∧
        (reg s registers.one).val = 1 ∧
        (∀ i < k + 1, (s.data[base + i]?).map Fin.val = some 0) ∧
        (∀ j, (j < base ∨ base + (k + 1) ≤ j) → s.data[j]? = origState.data[j]?) ∧
        (∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.tmp → reg s r = reg origState r)) := by
  intro s ⟨hpc, hptr, hcnt, hbase, hzero, hone, hzs, hfr, hregs⟩
  let code := (zeroBankPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 6 := rfl
  have hlt : ltb (reg s registers.ptr) (reg s count) = true :=
    branchLt_true (by rw [hptr, hcnt]; exact hk)
  have hf0 : code[s.pc]? = some (.branchLt registers.ptr count 1 5) := by rw [hpc]; rfl
  let u : State L := { s with pc := 1 }
  have su : step code input s = some (.next u) := by
    simpa only [u, hlt, ite_true] using
      step_branchLt_at (input := input) hf0 (by rw [hlt, hSize]; decide)
  have hPut : Placed code 1 (indexedDataWrite registers.tmp tinBase registers.ptr registers.zero) := by
    have hp := @place_slice bits L [.branchLt registers.ptr count 1 5]
      (indexedDataWrite registers.tmp tinBase registers.ptr registers.zero)
      [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]
    rw [show ([Instr.branchLt registers.ptr count 1 5] : List (Instr bits 15)).length = 1 from rfl] at hp
    simpa only [code, zeroBankPhase, Phase.ofLast, zeroBankAssembly, List.append_assoc] using hp
  have hBound : (reg u tinBase).val + (reg u registers.ptr).val < workCap := by
    change (reg s tinBase).val + (reg s registers.ptr).val < workCap
    rw [hbase, hptr]; omega
  obtain ⟨v, uv, vpc, vMem, _, vr⟩ := indexedDataWrite15 (input := input) (s := u)
    hPut rfl (by rw [hSize]; omega) (show registers.zero ≠ registers.tmp by decide) hBound
  have hf3 : code[v.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [vpc]; rfl
  obtain ⟨w, vw, wpc, wPtr, wr, wm⟩ := step_add15 (input := input) hf3
    (by rw [vpc, hSize]; omega)
  have hf4 : code[w.pc]? = some (.goto 0) := by rw [wpc, vpc]; rfl
  let t : State L := { w with pc := 0 }
  have wt : step code input w = some (.next t) := step_goto_at hf4 (by rw [hSize]; omega)
  have vPtr : (reg v registers.ptr).val = k :=
    (congrArg Fin.val (vr _ (show registers.ptr ≠ registers.tmp by decide))).trans hptr
  have vOne : (reg v registers.one).val = 1 :=
    (congrArg Fin.val (vr _ (show registers.one ≠ registers.tmp by decide))).trans hone
  have addFit : (reg v registers.ptr).val + (reg v registers.one).val < 2 ^ bits := by
    have hle : base + len ≤ 2 ^ bits := Nat.le_trans room hw
    rw [vPtr, vOne]; omega
  have tPtr : (reg t registers.ptr).val = k + 1 := by
    change (reg w registers.ptr).val = _
    rw [wPtr, add_no_wrap _ _ addFit, vPtr, vOne]
  have keep (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp) : reg t r = reg s r :=
    (wr r hp).trans (vr r ht)
  have keepVal (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp) :
      (reg t r).val = (reg s r).val := congrArg Fin.val (keep r hp ht)
  have memEq : t.data = s.data.set (base + k) (reg s registers.zero)
      (by rw [s.data_size]; change base + k < workCap; omega) := by
    change w.data = _
    rw [wm]
    simpa only [show u.data = s.data from rfl, show (reg u tinBase).val = base from hbase,
      show (reg u registers.ptr).val = k from hptr,
      show reg u registers.zero = reg s registers.zero from rfl] using vMem
  have keepCell (j : Nat) (hne : j ≠ base + k) : t.data[j]? = s.data[j]? := by
    rw [memEq]; exact Array.getElem?_set_ne _ hne.symm
  refine ⟨t, (Steps.cons su uv).append (.cons vw (.cons wt (.zero t))), rfl, tPtr,
    (keepVal count (by decide) (by decide)).trans hcnt,
    (keepVal tinBase (by decide) (by decide)).trans hbase,
    (keepVal registers.zero (by decide) (by decide)).trans hzero,
    (keepVal registers.one (by decide) (by decide)).trans hone, ?_, ?_, ?_⟩
  · intro i hi
    by_cases e : i = k
    · subst i; rw [memEq, Array.getElem?_set_self, Option.map_some, hzero]
    · rw [keepCell _ (by omega)]; exact hzs i (by omega)
  · intro j hj
    rw [keepCell _ (by omega)]
    exact hfr j (by omega)
  · intro r hp ht
    exact (keep r hp ht).trans (hregs r hp ht)

theorem run_zeroBank (input : Input L) (base len : Nat) (s : State L)
    (pc : s.pc = 0) (params : ZeroBankParams base len s) :
    ∃ t trace,
      run (zeroBankPhase (hi := hi) (hw := hw)).code input (5 * len + 2) s =
        some ⟨t, 5 * len + 2⟩ ∧
      (∀ i < len, (t.data[base + i]?).map Fin.val = some 0) ∧
      (∀ j, (j < base ∨ base + len ≤ j) → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.tmp → reg t r = reg s r) ∧
      SuccessfulTrace (zeroBankPhase (hi := hi) (hw := hw)).code input s trace ⟨t, 5 * len + 2⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let code := (zeroBankPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 6 := rfl
  let inv : Nat → State L → Prop := fun k q =>
    q.pc = 0 ∧ (reg q registers.ptr).val = k ∧ (reg q count).val = len ∧
    (reg q tinBase).val = base ∧ (reg q registers.zero).val = 0 ∧
    (reg q registers.one).val = 1 ∧
    (∀ i < k, (q.data[base + i]?).map Fin.val = some 0) ∧
    (∀ j, (j < base ∨ base + k ≤ j) → q.data[j]? = s.data[j]?) ∧
    (∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.tmp → reg q r = reg s r)
  have h5 : ∀ m, iterationCost (fun _ => 5) m = 5 * m := by
    intro m; induction m with | zero => rfl | succ m ih => simp [iterationCost, ih, Nat.mul_succ]
  have start : inv 0 s :=
    ⟨pc, params.ptr, params.countVal, params.baseVal, params.zeroVal, params.oneVal,
      fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl, fun _ _ _ => rfl⟩
  obtain ⟨u, steps, upc, uptr, ucnt, _, _, _, uzs, ufr, uregs⟩ :=
    loop_steps (code := code) (input := input) len (fun _ => 5) inv
      (zeroBank_step input base len s params.room) s start
  rw [h5] at steps
  have no : ltb (reg u registers.ptr) (reg u count) = false :=
    branchLt_false (by rw [uptr, ucnt]; exact Nat.le_refl _)
  let t : State L := { u with pc := 5 }
  have hf0 : code[u.pc]? = some (.branchLt registers.ptr count 1 5) := by rw [upc]; rfl
  have ut : step code input u = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hf0 (by rw [no, hSize]; decide)
  have exec := (steps.append (.cons ut (.zero t))).halts (step_halt_at rfl)
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  refine ⟨t, trace, exec, uzs, ufr, uregs, ok, ok.peak_eq⟩

end ZeroBank

/-! ### Stage 1A: Outgoing CSR + Indegrees + Kahn Topological Sort + Rank Scatter -/

section KahnStage

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def initCsrRegsAssembly (h1 : 1 < 2 ^ bits) (headOffset : Nat) (hhead : headOffset < 2 ^ bits) :
    List (Instr bits 15) :=
  [ .imm registers.zero ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.one ⟨1, h1⟩,
    .imm registers.ptr ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.stackBase ⟨0, Nat.two_pow_pos bits⟩,
    .imm cmd ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.childBase ⟨headOffset, hhead⟩,
    .loadInput registers.value registers.zero,
    .loadInput registers.remain registers.one,
    .add clk registers.value registers.one,
    .add count clk registers.remain,
    .add tinBase count count,
    .add toutBase tinBase count,
    .add offsetBase toutBase count,
    .add childrenBase offsetBase count,
    .add childrenBase childrenBase registers.one,
    .halt ]

/-- Initialize all registers for `rawIncomingPhase` from arbitrary initial register values. -/
def initOutgoingCsrRegsPhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (initCsrRegsAssembly (by omega) 3 (by omega)).toArray 15 rfl rfl rfl

theorem run_initOutgoingCsrRegs (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State L) :
    let n := H.vertexCount
    let m := H.arcCount
    let K := n + 1 + m
    let a : Arena bits workCap K :=
      ⟨0, n + m, by unfold rawWorkCap at workRoom; omega,
        by have := Nat.lt_of_lt_of_le (show 0 + 5 * K + 1 + (n + m) < rawWorkCap n m by
            unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
           exact this⟩
    ∃ t : State L,
      run (initOutgoingCsrRegsPhase (hi := hi) (hw := hw) (by
        have := Nat.le_trans (show 4 ≤ rawWorkCap n m by unfold rawWorkCap; omega)
          (Nat.le_trans workRoom hw)
        exact this)).code input 16 (Phase.initial s) = some ⟨t, 16⟩ ∧
      ParentCursor a (root n m) 0 t ∧
      (reg t clk).val = n + 1 ∧
      (reg t registers.childBase).val = 3 ∧
      t.data = s.data := by
  intro n m K a
  have h4 : 4 ≤ 2 ^ bits :=
    Nat.le_trans (show 4 ≤ rawWorkCap n m by unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
  let code := (initOutgoingCsrRegsPhase (hi := hi) (hw := hw) h4).code
  have hSize : code.size = 16 := rfl
  have h5K1 : 5 * K + 1 < 2 ^ bits :=
    Nat.lt_of_lt_of_le (show 5 * K + 1 < rawWorkCap n m by unfold rawWorkCap; omega)
      (Nat.le_trans workRoom hw)
  have hnWord : ∃ wn, input.words[0]? = some wn ∧ wn.val = n := by
    cases hw0 : input.words[0]? with
    | none => have h := raw.hdr_n; simp [hw0] at h
    | some w => have h := raw.hdr_n; simp [hw0] at h; exact ⟨w, rfl, h⟩
  have hmWord : ∃ wm, input.words[1]? = some wm ∧ wm.val = m := by
    cases hw1 : input.words[1]? with
    | none => have h := raw.hdr_m; simp [hw1] at h
    | some w => have h := raw.hdr_m; simp [hw1] at h; exact ⟨w, rfl, h⟩
  obtain ⟨wn, hwn, hwnV⟩ := hnWord
  obtain ⟨wm, hwm, hwmV⟩ := hmWord
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1z, fr1, d1⟩ := step_imm15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2o, fr2, d2⟩ := step_imm15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3p, fr3, d3⟩ := step_imm15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  obtain ⟨s4, hs34, p4, r4s, fr4, d4⟩ := step_imm15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s5, hs45, p5, r5c, fr5, d5⟩ := step_imm15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s6, hs56, p6, r6cb, fr6, d6⟩ := step_imm15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, p1]; rfl) (by rw [p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hZero6 : (reg s6 registers.zero).val = 0 := by
    rw [fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide),
      fr2 _ (by decide), r1z]
  have hOne6 : (reg s6 registers.one).val = 1 := by
    rw [fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), r2o]
  obtain ⟨s7, hs67, p7, r7n, fr7, d7⟩ := step_loadInput15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p6, p5, p4, p3, p2, p1, hSize, s0]; omega) (by rw [hZero6]; exact hwn)
  have hOne7 : (reg s7 registers.one).val = 1 := by rw [fr7 _ (by decide), hOne6]
  obtain ⟨s8, hs78, p8, r8m, fr8, d8⟩ := step_loadInput15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega) (by rw [hOne7]; exact hwm)
  obtain ⟨s9, hs89, p9, r9clk, fr9, d9⟩ := step_add15 (code := code) (input := input)
    (s := s8) (by rw [p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s10, hs910, p10, r10cnt, fr10, d10⟩ := step_add15 (code := code) (input := input)
    (s := s9) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s11, hs1011, p11, r11tin, fr11, d11⟩ := step_add15 (code := code) (input := input)
    (s := s10) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s12, hs1112, p12, r12tout, fr12, d12⟩ := step_add15 (code := code) (input := input)
    (s := s11) (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s13, hs1213, p13, r13off, fr13, d13⟩ := step_add15 (code := code) (input := input)
    (s := s12) (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s14, hs1314, p14, r14cb, fr14, d14⟩ := step_add15 (code := code) (input := input)
    (s := s13) (by rw [p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s15, hs1415, p15, r15cb, fr15, d15⟩ := step_add15 (code := code) (input := input)
    (s := s14) (by rw [p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 15 (Phase.initial s) s15 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67
      (.cons hs78 (.cons hs89 (.cons hs910 (.cons hs1011 (.cons hs1112 (.cons hs1213
        (.cons hs1314 (.cons hs1415 (.zero s15)))))))))))))))
  have halt : step code input s15 = some (.halted s15) :=
    step_halt_at (by rw [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
  have exec := hSteps.halts halt
  have vZero : (reg s15 registers.zero).val = 0 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), hZero6]
  have vOne : (reg s15 registers.one).val = 1 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), hOne7]
  have vPtr : (reg s15 registers.ptr).val = 0 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), r3p]
  have vStack : (reg s15 registers.stackBase).val = 0 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide), r4s]
  have vCmd : (reg s15 cmd).val = 0 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), r5c]
  have vChildBase : (reg s15 registers.childBase).val = 3 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), r6cb]
  have vVal8 : (reg s8 registers.value).val = n := by rw [fr8 _ (by decide), r7n, hwnV]
  have vOne8 : (reg s8 registers.one).val = 1 := by rw [fr8 _ (by decide), hOne7]
  have vClk9 : (reg s9 clk).val = n + 1 := by
    rw [r9clk, add_no_wrap _ _ (by rw [vVal8, vOne8]; omega), vVal8, vOne8]
  have vRemain9 : (reg s9 registers.remain).val = m := by rw [fr9 _ (by decide), r8m, hwmV]
  have vCnt10 : (reg s10 count).val = K := by
    rw [r10cnt, add_no_wrap _ _ (by rw [vClk9, vRemain9]; change K < 2 ^ bits; omega),
      vClk9, vRemain9]
  have vTin11 : (reg s11 tinBase).val = 2 * K := by
    rw [r11tin, add_no_wrap _ _ (by rw [vCnt10]; omega), vCnt10]; omega
  have vCnt11 : (reg s11 count).val = K := by rw [fr11 _ (by decide), vCnt10]
  have vTout12 : (reg s12 toutBase).val = 3 * K := by
    rw [r12tout, add_no_wrap _ _ (by rw [vTin11, vCnt11]; omega), vTin11, vCnt11]; omega
  have vCnt12 : (reg s12 count).val = K := by rw [fr12 _ (by decide), vCnt11]
  have vOff13 : (reg s13 offsetBase).val = 4 * K := by
    rw [r13off, add_no_wrap _ _ (by rw [vTout12, vCnt12]; omega), vTout12, vCnt12]; omega
  have vCnt13 : (reg s13 count).val = K := by rw [fr13 _ (by decide), vCnt12]
  have vCb14 : (reg s14 childrenBase).val = 5 * K := by
    rw [r14cb, add_no_wrap _ _ (by rw [vOff13, vCnt13]; omega), vOff13, vCnt13]; omega
  have vOne14 : (reg s14 registers.one).val = 1 := by
    rw [fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide), fr11 _ (by decide),
      fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), hOne7]
  have vCb15_raw : (reg s15 childrenBase).val = 5 * K + 1 := by
    rw [r15cb, add_no_wrap _ _ (by rw [vCb14, vOne14]; omega), vCb14, vOne14]
  have vCb15 : (reg s15 childrenBase).val = a.payload := by
    simpa only [Arena.payload, a, Nat.zero_add] using vCb15_raw
  have vClk : (reg s15 clk).val = n + 1 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), vClk9]
  have vCnt : (reg s15 count).val = K := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide), vCnt11]
  have vTin : (reg s15 tinBase).val = a.tin := by
    change (reg s15 tinBase).val = 0 + 2 * K
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide), vTin11, Nat.zero_add]
  have vTout : (reg s15 toutBase).val = a.tout := by
    change (reg s15 toutBase).val = 0 + 3 * K
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), vTout12, Nat.zero_add]
  have vOff : (reg s15 offsetBase).val = a.offsets := by
    change (reg s15 offsetBase).val = 0 + 4 * K
    rw [fr15 _ (by decide), fr14 _ (by decide), vOff13, Nat.zero_add]
  have vData : s15.data = s.data :=
    d15.trans (d14.trans (d13.trans (d12.trans (d11.trans (d10.trans (d9.trans
      (d8.trans (d7.trans (d6.trans (d5.trans (d4.trans (d3.trans (d2.trans d1)))))))))))))
  refine ⟨s15, exec, ⟨⟨vCnt, vOne, vZero, vStack, vTin, vTout, vOff, vCb15⟩, vCmd, vPtr⟩,
    vClk, vChildBase, vData⟩

private def initIndegSetupList (hbits : 2 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm registers.zero ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.one ⟨1, hbits⟩,
    .imm registers.ptr ⟨0, Nat.two_pow_pos bits⟩,
    .loadInput count registers.zero,
    .loadInput registers.remain registers.one,
    .add registers.tmp count registers.remain,
    .add registers.tmp registers.tmp registers.one,
    .add tinBase registers.tmp registers.tmp,
    .add registers.value tinBase registers.tmp,
    .add tinBase registers.value registers.value,
    .add tinBase tinBase registers.one,
    .halt ]

/-- Set `ptr = 0`, `zero = 0`, `one = 1`, `count = n`, `remain = m`, `tinBase = indegBase n m`. -/
def initIndegSetupPhase (hbits : 2 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (initIndegSetupList hbits).toArray 11 rfl rfl rfl

theorem run_initIndegSetup (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State L) :
    let n := H.vertexCount
    let m := H.arcCount
    ∃ t : State L,
      run (initIndegSetupPhase (hi := hi) (hw := hw) (by
        have := Nat.le_trans (show 2 ≤ rawWorkCap n m by unfold rawWorkCap; omega)
          (Nat.le_trans workRoom hw)
        exact this)).code input 12 (Phase.initial s) = some ⟨t, 12⟩ ∧
      ZeroBankParams (indegBase n m) n t ∧
      (reg t registers.remain).val = m ∧
      t.data = s.data := by
  intro n m
  have h2 : 2 ≤ 2 ^ bits :=
    Nat.le_trans (show 2 ≤ rawWorkCap n m by unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
  let code := (initIndegSetupPhase (hi := hi) (hw := hw) h2).code
  have hSize : code.size = 12 := rfl
  have hIndegFit : indegBase n m + n ≤ workCap := by
    unfold indegBase csrArenaWords rawWorkCap at *
    omega
  have hIndegBits : indegBase n m < 2 ^ bits :=
    Nat.lt_of_lt_of_le (show indegBase n m < rawWorkCap n m by
      unfold indegBase csrArenaWords rawWorkCap; omega) (Nat.le_trans workRoom hw)
  have hnWord : ∃ wn, input.words[0]? = some wn ∧ wn.val = n := by
    cases hw0 : input.words[0]? with
    | none => have h := raw.hdr_n; simp [hw0] at h
    | some w => have h := raw.hdr_n; simp [hw0] at h; exact ⟨w, rfl, h⟩
  have hmWord : ∃ wm, input.words[1]? = some wm ∧ wm.val = m := by
    cases hw1 : input.words[1]? with
    | none => have h := raw.hdr_m; simp [hw1] at h
    | some w => have h := raw.hdr_m; simp [hw1] at h; exact ⟨w, rfl, h⟩
  obtain ⟨wn, hwn, hwnV⟩ := hnWord
  obtain ⟨wm, hwm, hwmV⟩ := hmWord
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1z, fr1, d1⟩ := step_imm15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2o, fr2, d2⟩ := step_imm15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3p, fr3, d3⟩ := step_imm15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  have hz3 : (reg s3 registers.zero).val = 0 := by
    rw [fr3 _ (by decide), fr2 _ (by decide), r1z]
  have ho3 : (reg s3 registers.one).val = 1 := by
    rw [fr3 _ (by decide), r2o]
  obtain ⟨s4, hs34, p4, r4n, fr4, d4⟩ := step_loadInput15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega) (by rw [hz3]; exact hwn)
  have ho4 : (reg s4 registers.one).val = 1 := by rw [fr4 _ (by decide), ho3]
  obtain ⟨s5, hs45, p5, r5m, fr5, d5⟩ := step_loadInput15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
    (by rw [ho4]; exact hwm)
  obtain ⟨s6, hs56, p6, r6t, fr6, d6⟩ := step_add15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, p1]; rfl) (by rw [p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s7, hs67, p7, r7t, fr7, d7⟩ := step_add15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, p1]; rfl) (by rw [p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s8, hs78, p8, r8tin, fr8, d8⟩ := step_add15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, p1]; rfl) (by rw [p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s9, hs89, p9, r9val, fr9, d9⟩ := step_add15 (code := code) (input := input)
    (s := s8) (by rw [p8, p7, p6, p5, p4, p3, p2, p1]; rfl) (by rw [p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s10, hs910, p10, r10tin, fr10, d10⟩ := step_add15 (code := code) (input := input)
    (s := s9) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s11, hs1011, p11, r11tin, fr11, d11⟩ := step_add15 (code := code) (input := input)
    (s := s10) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 11 (Phase.initial s) s11 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67
      (.cons hs78 (.cons hs89 (.cons hs910 (.cons hs1011 (.zero s11)))))))))))
  have halt : step code input s11 = some (.halted s11) :=
    step_halt_at (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
  have exec := hSteps.halts halt
  have vCnt5 : (reg s5 count).val = n := by rw [fr5 _ (by decide), r4n, hwnV]
  have vRem5 : (reg s5 registers.remain).val = m := by rw [r5m, hwmV]
  have vOne5 : (reg s5 registers.one).val = 1 := by rw [fr5 _ (by decide), ho4]
  have vTmp6 : (reg s6 registers.tmp).val = n + m := by
    rw [r6t, add_no_wrap _ _ (by rw [vCnt5, vRem5]; unfold indegBase csrArenaWords at hIndegBits; omega),
      vCnt5, vRem5]
  have vOne6 : (reg s6 registers.one).val = 1 := by rw [fr6 _ (by decide), vOne5]
  have vTmp7 : (reg s7 registers.tmp).val = n + 1 + m := by
    rw [r7t, add_no_wrap _ _ (by rw [vTmp6, vOne6]; unfold indegBase csrArenaWords at hIndegBits; omega),
      vTmp6, vOne6]; omega
  have vTin8 : (reg s8 tinBase).val = 2 * (n + 1 + m) := by
    rw [r8tin, add_no_wrap _ _ (by rw [vTmp7]; unfold indegBase csrArenaWords at hIndegBits; omega),
      vTmp7]; omega
  have vTmp8 : (reg s8 registers.tmp).val = n + 1 + m := by rw [fr8 _ (by decide), vTmp7]
  have vVal9 : (reg s9 registers.value).val = 3 * (n + 1 + m) := by
    rw [r9val, add_no_wrap _ _ (by rw [vTin8, vTmp8]; unfold indegBase csrArenaWords at hIndegBits; omega),
      vTin8, vTmp8]; omega
  have vTin10 : (reg s10 tinBase).val = 6 * (n + 1 + m) := by
    rw [r10tin, add_no_wrap _ _ (by rw [vVal9]; unfold indegBase csrArenaWords at hIndegBits; omega),
      vVal9]; omega
  have vOne10 : (reg s10 registers.one).val = 1 := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide), vOne6]
  have vTin11 : (reg s11 tinBase).val = indegBase n m := by
    rw [r11tin, add_no_wrap _ _ (by rw [vTin10, vOne10]; unfold indegBase csrArenaWords at *; omega),
      vTin10, vOne10]
    rfl
  have vPtr : (reg s11 registers.ptr).val = 0 := by
    rw [fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), r3p]
  have vCnt : (reg s11 count).val = n := by
    rw [fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), vCnt5]
  have vZero : (reg s11 registers.zero).val = 0 := by
    rw [fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), hz3]
  have vOne : (reg s11 registers.one).val = 1 := by rw [fr11 _ (by decide), vOne10]
  have vRem : (reg s11 registers.remain).val = m := by
    rw [fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), vRem5]
  have vData : s11.data = s.data :=
    d11.trans (d10.trans (d9.trans (d8.trans (d7.trans (d6.trans (d5.trans (d4.trans
      (d3.trans (d2.trans d1)))))))))
  exact ⟨s11, exec, ⟨vPtr, vCnt, vTin11, vZero, vOne, hIndegFit⟩, vRem, vData⟩

-- Count occurrences in prefix `[0..k)` of `f : Fin m → Fin n` hitting `v`.
def countOccPrefix {m n : Nat} (f : Fin m → Fin n) (v : Fin n) : Nat → Nat
  | 0 => 0
  | k + 1 => countOccPrefix f v k + if hk : k < m then (if f ⟨k, hk⟩ = v then 1 else 0) else 0

theorem countOccPrefix_le {m n : Nat} (f : Fin m → Fin n) (v : Fin n) (k : Nat) :
    countOccPrefix f v k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    unfold countOccPrefix
    split <;> (try split) <;> omega

private def countIndegSetupList (hbits : 4 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm registers.ptr ⟨0, Nat.two_pow_pos bits⟩,
    .mov count registers.remain,
    .imm registers.childBase ⟨3, hbits⟩,
    .add registers.childBase registers.childBase registers.remain,
    .halt ]

/-- Setup for `countIndegPhase`: preserves `tinBase` (`indegBase`), `zero`, `one`, `data`. -/
def countIndegSetupPhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (countIndegSetupList hbits).toArray 4 rfl rfl rfl

theorem run_countIndegSetup (input : Input L) {n m : Nat}
    (hbits : 4 ≤ 2 ^ bits) (hm : 3 + 2 * m ≤ inputCap) (s : State L)
    (hmReg : (reg s registers.remain).val = m)
    (hTin : (reg s tinBase).val = indegBase n m)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1) :
    ∃ t : State L,
      run (countIndegSetupPhase (hi := hi) (hw := hw) hbits).code input 5 (Phase.initial s) =
        some ⟨t, 5⟩ ∧
      (reg t registers.ptr).val = 0 ∧
      (reg t count).val = m ∧
      (reg t registers.childBase).val = 3 + m ∧
      (reg t tinBase).val = indegBase n m ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      t.data = s.data := by
  let code := (countIndegSetupPhase (hi := hi) (hw := hw) hbits).code
  have hSize : code.size = 5 := rfl
  have hmBits : 3 + m < 2 ^ bits := by
    have := Nat.le_trans hm hi
    omega
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1p, fr1, d1⟩ := step_imm15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2c, fr2, d2⟩ := step_mov15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3cb, fr3, d3⟩ := step_imm15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  obtain ⟨s4, hs34, p4, r4cb, fr4, d4⟩ := step_add15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 4 (Phase.initial s) s4 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.zero s4))))
  have halt : step code input s4 = some (.halted s4) :=
    step_halt_at (by rw [p4, p3, p2, p1]; rfl)
  have vRem3 : (reg s3 registers.remain).val = m := by
    rw [fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hmReg
  have vCb3 : (reg s3 registers.childBase).val = 3 := by rw [r3cb]
  refine ⟨s4, hSteps.halts halt, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), r1p]
  · rw [fr4 _ (by decide), fr3 _ (by decide), r2c, fr1 _ (by decide)]; exact hmReg
  · rw [r4cb, add_no_wrap _ _ (by rw [vCb3, vRem3]; exact hmBits), vCb3, vRem3]
  · rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hTin
  · rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hZero
  · rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hOne
  · exact d4.trans (d3.trans (d2.trans d1))

private def countIndegList : List (Instr bits 15) :=
  [.branchLt registers.ptr count 1 10] ++
    indexedInputRead registers.value registers.childBase registers.ptr ++
    indexedDataRead registers.remain tinBase registers.value ++
    [.add registers.remain registers.remain registers.one] ++
    indexedDataWrite registers.tmp tinBase registers.value registers.remain ++
    [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]

/-- Scan `input.words[headAddr .. headAddr + m)` and accumulate indegrees in `tinBase[0..n)`. -/
def countIndegPhase : Phase L :=
  Phase.ofLast countIndegList.toArray 10 rfl rfl rfl

theorem run_countIndeg (input : Input L) {n m headAddr : Nat}
    (heads : Fin m → Fin n) (raw : HeadsAt input headAddr heads)
    (hHeadPos : 1 ≤ headAddr)
    (hmInput : headAddr + m ≤ inputCap) (hnWork : indegBase n m + n ≤ workCap)
    (s : State L) (pc : s.pc = 0)
    (hPtr : (reg s registers.ptr).val = 0)
    (hCnt : (reg s count).val = m)
    (hHead : (reg s registers.childBase).val = headAddr)
    (hTin : (reg s tinBase).val = indegBase n m)
    (hOne : (reg s registers.one).val = 1)
    (hZeroes : ∀ v : Fin n, (s.data[indegBase n m + v.val]?).map Fin.val = some 0) :
    ∃ t trace,
      run (countIndegPhase (hi := hi) (hw := hw)).code input (10 * m + 2) s =
        some ⟨t, 10 * m + 2⟩ ∧
      (∀ v : Fin n, (t.data[indegBase n m + v.val]?).map Fin.val =
        some (countOccPrefix heads v m)) ∧
      (∀ j, (j < indegBase n m ∨ indegBase n m + n ≤ j) → t.data[j]? = s.data[j]?) ∧
      (reg t tinBase).val = indegBase n m ∧
      (reg t registers.one).val = 1 ∧
      reg t registers.zero = reg s registers.zero ∧
      SuccessfulTrace (countIndegPhase (hi := hi) (hw := hw)).code input s trace ⟨t, 10 * m + 2⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let code := (countIndegPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 11 := rfl
  let inv : Nat → State L → Prop := fun k q =>
    q.pc = 0 ∧ (reg q registers.ptr).val = k ∧ (reg q count).val = m ∧
    (reg q registers.childBase).val = headAddr ∧ (reg q tinBase).val = indegBase n m ∧
    (reg q registers.one).val = 1 ∧ reg q registers.zero = reg s registers.zero ∧
    (∀ v : Fin n, (q.data[indegBase n m + v.val]?).map Fin.val =
      some (countOccPrefix heads v k)) ∧
    (∀ j, (j < indegBase n m ∨ indegBase n m + n ≤ j) → q.data[j]? = s.data[j]?)
  have stepSpec : ∀ k, k < m → BlockSpec code input 10 (inv k) (inv (k + 1)) := by
    intro k hk q ⟨qpc, qptr, qcnt, qcb, qtin, qone, qzero, qocc, qfr⟩
    have hlt : ltb (reg q registers.ptr) (reg q count) = true :=
      branchLt_true (by rw [qptr, qcnt]; exact hk)
    have hf0 : code[q.pc]? = some (.branchLt registers.ptr count 1 10) := by rw [qpc]; rfl
    let u : State L := { q with pc := 1 }
    have qu : step code input q = some (.next u) := by
      simpa only [u, hlt, ite_true] using
        step_branchLt_at (input := input) hf0 (by rw [hlt, hSize]; decide)
    have p1 : Placed code 1 (indexedInputRead registers.value registers.childBase registers.ptr) := by
      have hp := @place_slice bits L [.branchLt registers.ptr count 1 10]
        (indexedInputRead registers.value registers.childBase registers.ptr)
        (indexedDataRead registers.remain tinBase registers.value ++
          [.add registers.remain registers.remain registers.one] ++
          indexedDataWrite registers.tmp tinBase registers.value registers.remain ++
          [.add registers.ptr registers.ptr registers.one, .goto 0, .halt])
      rw [show ([Instr.branchLt registers.ptr count 1 10] : List (Instr bits 15)).length = 1 from rfl] at hp
      simpa only [code, countIndegPhase, Phase.ofLast, countIndegList, List.append_assoc] using hp
    have b1 : (reg u registers.childBase).val + (reg u registers.ptr).val < inputCap := by
      change (reg q registers.childBase).val + (reg q registers.ptr).val < inputCap
      rw [qcb, qptr]; omega
    obtain ⟨v, uv, vpc, vWord, vr, vm⟩ := indexedInputRead15 (input := input) (s := u)
      p1 rfl (by rw [hSize]; omega) b1
    let e : Fin m := ⟨k, hk⟩
    let wHead := heads e
    have vVal : (reg v registers.value).val = wHead.val := by
      change some (reg v registers.value) =
        input.words[(reg q registers.childBase).val + (reg q registers.ptr).val]? at vWord
      rw [qcb, qptr] at vWord
      have h := congrArg (Option.map Fin.val) vWord
      rw [raw e] at h
      exact Option.some.inj h
    have vTin : (reg v tinBase).val = indegBase n m :=
      (congrArg Fin.val (vr _ (by decide))).trans qtin
    have p2 : Placed code 3 (indexedDataRead registers.remain tinBase registers.value) := by
      have hp := @place_slice bits L
        ([.branchLt registers.ptr count 1 10] ++
          indexedInputRead registers.value registers.childBase registers.ptr)
        (indexedDataRead registers.remain tinBase registers.value)
        ([.add registers.remain registers.remain registers.one] ++
          indexedDataWrite registers.tmp tinBase registers.value registers.remain ++
          [.add registers.ptr registers.ptr registers.one, .goto 0, .halt])
      rw [show ([Instr.branchLt registers.ptr count 1 10] ++
        indexedInputRead registers.value registers.childBase registers.ptr :
          List (Instr bits 15)).length = 3 from rfl] at hp
      simpa only [code, countIndegPhase, Phase.ofLast, countIndegList, List.append_assoc] using hp
    have b2 : (reg v tinBase).val + (reg v registers.value).val < workCap := by
      have := wHead.isLt; rw [vTin, vVal]; omega
    obtain ⟨w, vw, wpc, wWord, wr, wm⟩ := indexedDataRead15 (input := input) (s := v)
      p2 vpc (by rw [hSize]; omega) b2
    have wRem : (reg w registers.remain).val = countOccPrefix heads wHead k := by
      rw [vTin, vVal, vm] at wWord
      have h := congrArg (Option.map Fin.val) wWord
      rw [qocc wHead] at h
      exact Option.some.inj h
    have hf5 : code[w.pc]? = some (.add registers.remain registers.remain registers.one) := by
      rw [wpc]; rfl
    obtain ⟨x, wx, xpc, xRem, xr, xm⟩ := step_add15 (input := input) hf5
      (by rw [wpc, hSize]; omega)
    have wOne : (reg w registers.one).val = 1 :=
      (congrArg Fin.val ((wr _ (by decide)).trans (vr _ (by decide)))).trans qone
    have mFit : m < 2 ^ bits := Nat.lt_of_lt_of_le (by omega) hi
    have addFit : (reg w registers.remain).val + (reg w registers.one).val < 2 ^ bits := by
      have := countOccPrefix_le heads wHead k
      rw [wRem, wOne]; omega
    have xRemVal : (reg x registers.remain).val = countOccPrefix heads wHead k + 1 := by
      rw [xRem, add_no_wrap _ _ addFit, wRem, wOne]
    have xTin : (reg x tinBase).val = indegBase n m :=
      (congrArg Fin.val ((xr _ (by decide)).trans (wr _ (by decide)))).trans vTin
    have xVal : (reg x registers.value).val = wHead.val :=
      (congrArg Fin.val ((xr _ (by decide)).trans (wr _ (by decide)))).trans vVal
    have p3 : Placed code 6 (indexedDataWrite registers.tmp tinBase registers.value registers.remain) := by
      have hp := @place_slice bits L
        ([.branchLt registers.ptr count 1 10] ++
          indexedInputRead registers.value registers.childBase registers.ptr ++
          indexedDataRead registers.remain tinBase registers.value ++
          [.add registers.remain registers.remain registers.one])
        (indexedDataWrite registers.tmp tinBase registers.value registers.remain)
        ([Instr.add registers.ptr registers.ptr registers.one, .goto 0, .halt])
      rw [show ([Instr.branchLt registers.ptr count 1 10] ++
        indexedInputRead registers.value registers.childBase registers.ptr ++
        indexedDataRead registers.remain tinBase registers.value ++
        [Instr.add registers.remain registers.remain registers.one] :
          List (Instr bits 15)).length = 6 from rfl] at hp
      simpa only [code, countIndegPhase, Phase.ofLast, countIndegList, List.append_assoc] using hp
    have b3 : (reg x tinBase).val + (reg x registers.value).val < workCap := by
      have := wHead.isLt; rw [xTin, xVal]; omega
    obtain ⟨y, xy, ypc, yMem, _, yr⟩ := indexedDataWrite15 (input := input) (s := x)
      p3 (by omega) (by rw [hSize]; omega) (show registers.remain ≠ registers.tmp by decide) b3
    have hf8 : code[y.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
      rw [ypc]; rfl
    obtain ⟨z, yz, zpc, zPtr, zr, zm⟩ := step_add15 (input := input) hf8
      (by rw [ypc, hSize]; omega)
    have hf9 : code[z.pc]? = some (.goto 0) := by rw [zpc, ypc]; rfl
    let t : State L := { z with pc := 0 }
    have zt : step code input z = some (.next t) := step_goto_at hf9 (by rw [hSize]; omega)
    have keep (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp)
        (hr : r ≠ registers.remain) (hv : r ≠ registers.value) : reg t r = reg q r :=
      (zr r hp).trans ((yr r ht).trans ((xr r hr).trans ((wr r hr).trans (vr r hv))))
    have keepVal (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp)
        (hr : r ≠ registers.remain) (hv : r ≠ registers.value) :
        (reg t r).val = (reg q r).val := congrArg Fin.val (keep r hp ht hr hv)
    have yPtr' : (reg y registers.ptr).val = k := by
      rw [yr _ (by decide), xr _ (by decide), wr _ (by decide), vr _ (by decide)]; exact qptr
    have yOne : (reg y registers.one).val = 1 :=
      (congrArg Fin.val ((yr _ (by decide)).trans ((xr _ (by decide)).trans
        ((wr _ (by decide)).trans (vr _ (by decide)))))).trans qone
    have ptrFit : (reg y registers.ptr).val + (reg y registers.one).val < 2 ^ bits := by
      rw [yPtr', yOne]; omega
    have tPtr : (reg t registers.ptr).val = k + 1 := by
      change (reg z registers.ptr).val = _
      rw [zPtr, add_no_wrap _ _ ptrFit, yPtr', yOne]
    have memEq : t.data = q.data.set (indegBase n m + wHead.val) (reg x registers.remain)
        (by rw [q.data_size]; have := wHead.isLt; change indegBase n m + wHead.val < workCap; omega) := by
      change z.data = _
      rw [zm]
      simpa only [xTin, xVal, xm, wm, vm] using yMem
    have keepCell (j : Nat) (hne : j ≠ indegBase n m + wHead.val) : t.data[j]? = q.data[j]? := by
      rw [memEq]; exact Array.getElem?_set_ne _ hne.symm
    refine ⟨t, (Steps.cons qu uv).append (vw.append (.cons wx (xy.append (.cons yz (.cons zt (.zero t)))))),
      rfl, tPtr, keepVal count (by decide) (by decide) (by decide) (by decide) |>.trans qcnt,
      keepVal registers.childBase (by decide) (by decide) (by decide) (by decide) |>.trans qcb,
      keepVal tinBase (by decide) (by decide) (by decide) (by decide) |>.trans qtin,
      keepVal registers.one (by decide) (by decide) (by decide) (by decide) |>.trans qone,
      (keep registers.zero (by decide) (by decide) (by decide) (by decide)).trans qzero, ?_, ?_⟩
    · intro v
      unfold countOccPrefix
      simp only [hk, dite_true]
      by_cases ev : wHead = v
      · subst v
        split
        · rw [memEq, Array.getElem?_set_self, Option.map_some, xRemVal]
        · next hc => exact absurd rfl hc
      · have hne : ¬ (heads ⟨k, hk⟩ = v) := ev
        simp only [hne, ite_false, Nat.add_zero]
        rw [keepCell _ (fun h => ev (Fin.ext (Nat.add_left_cancel h).symm))]
        exact qocc v
    · intro j hj
      have := wHead.isLt
      rw [keepCell _ (by omega)]
      exact qfr j hj
  have h10 : ∀ m', iterationCost (fun _ => 10) m' = 10 * m' := by
    intro m'; induction m' with | zero => rfl | succ m' ih => simp [iterationCost, ih, Nat.mul_succ]
  have start : inv 0 s :=
    ⟨pc, hPtr, hCnt, hHead, hTin, hOne, rfl, fun v => by simpa [countOccPrefix] using hZeroes v,
      fun _ _ => rfl⟩
  obtain ⟨u, steps, ⟨upc, uptr, ucnt, _, utin, uone, uzero, uocc, ufr⟩⟩ :=
    loop_steps (code := code) (input := input) m (fun _ => 10) inv stepSpec s start
  rw [h10] at steps
  have no : ltb (reg u registers.ptr) (reg u count) = false :=
    branchLt_false (by rw [uptr, ucnt]; exact Nat.le_refl _)
  let t : State L := { u with pc := 10 }
  have hf0 : code[u.pc]? = some (.branchLt registers.ptr count 1 10) := by rw [upc]; rfl
  have ut : step code input u = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hf0 (by rw [no, hSize]; decide)
  have exec := (steps.append (.cons ut (.zero t))).halts (step_halt_at rfl)
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  exact ⟨t, trace, exec, uocc, ufr, utin, uone, uzero, ok, ok.peak_eq⟩

private def seedQueueSetupList : List (Instr bits 15) :=
  [ .add registers.ptr registers.zero registers.zero,
    .add clk registers.zero registers.zero,
    .loadInput count registers.zero,
    .add offsetBase tinBase count,
    .add offsetBase offsetBase count,
    .halt ]

/-- Setup for `seedQueuePhase`: sets `ptr = 0`, `clk = 0`, `count = n`, `offsetBase = orderBase n m`. -/
def seedQueueSetupPhase : Phase L :=
  Phase.ofLast seedQueueSetupList.toArray 5 rfl rfl rfl

theorem run_seedQueueSetup (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State L)
    (hTin : (reg s tinBase).val = indegBase H.vertexCount H.arcCount)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1) :
    let n := H.vertexCount
    let m := H.arcCount
    ∃ t : State L,
      run (seedQueueSetupPhase (hi := hi) (hw := hw)).code input 6 (Phase.initial s) = some ⟨t, 6⟩ ∧
      (reg t registers.ptr).val = 0 ∧
      (reg t clk).val = 0 ∧
      (reg t count).val = n ∧
      (reg t tinBase).val = indegBase n m ∧
      (reg t offsetBase).val = orderBase n m ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      t.data = s.data := by
  intro n m
  let code := (seedQueueSetupPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 6 := rfl
  have hOrderFit : orderBase n m < 2 ^ bits :=
    Nat.lt_of_lt_of_le (show orderBase n m < rawWorkCap n m by
      unfold orderBase stampsBase indegBase csrArenaWords rawWorkCap; omega) (Nat.le_trans workRoom hw)
  have hnWord : ∃ wn, input.words[0]? = some wn ∧ wn.val = n := by
    cases hw0 : input.words[0]? with
    | none => have h := raw.hdr_n; simp [hw0] at h
    | some w => have h := raw.hdr_n; simp [hw0] at h; exact ⟨w, rfl, h⟩
  obtain ⟨wn, hwn, hwnV⟩ := hnWord
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1p, fr1, d1⟩ := step_add15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2c, fr2, d2⟩ := step_add15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  have hz2 : (reg s2 registers.zero).val = 0 := by
    rw [fr2 _ (by decide), fr1 _ (by decide)]; exact hZero
  obtain ⟨s3, hs23, p3, r3cnt, fr3, d3⟩ := step_loadInput15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega) (by rw [hz2]; exact hwn)
  obtain ⟨s4, hs34, p4, r4off, fr4, d4⟩ := step_add15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s5, hs45, p5, r5off, fr5, d5⟩ := step_add15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 5 (Phase.initial s) s5 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.zero s5)))))
  have halt : step code input s5 = some (.halted s5) :=
    step_halt_at (by rw [p5, p4, p3, p2, p1]; rfl)
  have vZero : (reg s5 registers.zero).val = 0 := by
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), hz2]
  have vOne : (reg s5 registers.one).val = 1 := by
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide),
      fr1 _ (by decide)]; exact hOne
  have vTin3 : (reg s3 tinBase).val = indegBase n m := by
    rw [fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hTin
  have vCnt3 : (reg s3 count).val = n := by rw [r3cnt, hwnV]
  have vOff4 : (reg s4 offsetBase).val = indegBase n m + n := by
    rw [r4off, add_no_wrap _ _ (by rw [vTin3, vCnt3]; unfold orderBase stampsBase at hOrderFit; omega),
      vTin3, vCnt3]
  have vCnt4 : (reg s4 count).val = n := by rw [fr4 _ (by decide), vCnt3]
  have vOff5 : (reg s5 offsetBase).val = orderBase n m := by
    rw [r5off, add_no_wrap _ _ (by rw [vOff4, vCnt4]; unfold orderBase stampsBase at hOrderFit; omega),
      vOff4, vCnt4]
    rfl
  have hz0 : (reg (Phase.initial s) registers.zero).val = 0 := hZero
  have vPtr : (reg s5 registers.ptr).val = 0 := by
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide),
      r1p, add_no_wrap _ _ (by rw [hz0]; exact Nat.two_pow_pos bits), hz0]
  have vClk : (reg s5 clk).val = 0 := by
    have hz1 : (reg s1 registers.zero).val = 0 := by rw [fr1 _ (by decide)]; exact hz0
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), r2c,
      add_no_wrap _ _ (by rw [hz1]; exact Nat.two_pow_pos bits), hz1]
  have vCnt : (reg s5 count).val = n := by rw [fr5 _ (by decide), vCnt4]
  have vTin : (reg s5 tinBase).val = indegBase n m := by
    rw [fr5 _ (by decide), fr4 _ (by decide), vTin3]
  exact ⟨s5, hSteps.halts halt, vPtr, vClk, vCnt, vTin, vOff5, vZero, vOne,
    d5.trans (d4.trans (d3.trans (d2.trans d1)))⟩

private def seedQueueList : List (Instr bits 15) :=
  [.branchLt registers.ptr count 1 9] ++
    indexedDataRead registers.value tinBase registers.ptr ++
    [.branchLt registers.value registers.one 4 7] ++
    indexedDataWrite registers.tmp offsetBase clk registers.ptr ++
    [.add clk clk registers.one, .add registers.ptr registers.ptr registers.one, .goto 0, .halt]

/-- Seed the Kahn queue at `orderBase[0..qTail)` with all vertices of indegree 0. -/
def seedQueuePhase : Phase L :=
  Phase.ofLast seedQueueList.toArray 9 rfl rfl rfl

theorem run_seedQueue (input : Input L) {n m : Nat}
    (deg : Fin n → Nat)
    (hOrderFit : orderBase n m + n ≤ workCap)
    (s : State L) (pc : s.pc = 0)
    (hPtr : (reg s registers.ptr).val = 0)
    (hClk : (reg s clk).val = 0)
    (hCnt : (reg s count).val = n)
    (hTin : (reg s tinBase).val = indegBase n m)
    (hOff : (reg s offsetBase).val = orderBase n m)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1)
    (hIndeg : ∀ v : Fin n, (s.data[indegBase n m + v.val]?).map Fin.val = some (deg v)) :
    ∃ (t : State L) (trace : List (State L)) (work : Nat) (q : List (Fin n)),
      work ≤ 9 * n + 2 ∧
      run (seedQueuePhase (hi := hi) (hw := hw)).code input work s = some ⟨t, work⟩ ∧
      q.Nodup ∧ q.length ≤ n ∧
      (reg t clk).val = q.length ∧
      (∀ i : Fin q.length, (t.data[orderBase n m + i.val]?).map Fin.val = some (q[i.val]'i.isLt).val) ∧
      (∀ v : Fin n, v ∈ q ↔ deg v = 0) ∧
      (∀ j, (j < orderBase n m ∨ orderBase n m + n ≤ j) → t.data[j]? = s.data[j]?) ∧
      (reg t tinBase).val = indegBase n m ∧
      (reg t offsetBase).val = orderBase n m ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      SuccessfulTrace (seedQueuePhase (hi := hi) (hw := hw)).code input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let code := (seedQueuePhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 10 := rfl
  let costFn : Nat → Nat := fun k => if hk : k < n then (if deg ⟨k, hk⟩ = 0 then 9 else 6) else 6
  let inv : Nat → State L → Prop := fun k st =>
    st.pc = 0 ∧ (reg st registers.ptr).val = k ∧ (reg st count).val = n ∧
    (reg st tinBase).val = indegBase n m ∧ (reg st offsetBase).val = orderBase n m ∧
    (reg st registers.zero).val = 0 ∧ (reg st registers.one).val = 1 ∧
    (∀ j, (j < orderBase n m ∨ orderBase n m + n ≤ j) → st.data[j]? = s.data[j]?) ∧
    ∃ q : List (Fin n), q.Nodup ∧ q.length ≤ k ∧ (reg st clk).val = q.length ∧
      (∀ i : Fin q.length, (st.data[orderBase n m + i.val]?).map Fin.val = some (q[i.val]'i.isLt).val) ∧
      (∀ v : Fin n, v ∈ q ↔ v.val < k ∧ deg v = 0)
  have stepSpec : ∀ k, k < n → BlockSpec code input (costFn k) (inv k) (inv (k + 1)) := by
    intro k hk st ⟨spc, sptr, scnt, stin, soff, szero, sone, sfr, q, qnd, qlen, sclk, qmem, qmem_iff⟩
    have hlt : ltb (reg st registers.ptr) (reg st count) = true :=
      branchLt_true (by rw [sptr, scnt]; exact hk)
    have hf0 : code[st.pc]? = some (.branchLt registers.ptr count 1 9) := by rw [spc]; rfl
    let u : State L := { st with pc := 1 }
    have su : step code input st = some (.next u) := by
      simpa only [u, hlt, ite_true] using
        step_branchLt_at (input := input) hf0 (by rw [hlt, hSize]; decide)
    have p1 : Placed code 1 (indexedDataRead registers.value tinBase registers.ptr) := by
      have hp := @place_slice bits L [.branchLt registers.ptr count 1 9]
        (indexedDataRead registers.value tinBase registers.ptr)
        ([.branchLt registers.value registers.one 4 7] ++
          indexedDataWrite registers.tmp offsetBase clk registers.ptr ++
          [.add clk clk registers.one, .add registers.ptr registers.ptr registers.one, .goto 0, .halt])
      rw [show ([Instr.branchLt registers.ptr count 1 9] : List (Instr bits 15)).length = 1 from rfl] at hp
      simpa only [code, seedQueuePhase, Phase.ofLast, seedQueueList, List.append_assoc] using hp
    have b1 : (reg u tinBase).val + (reg u registers.ptr).val < workCap := by
      change (reg st tinBase).val + (reg st registers.ptr).val < workCap
      rw [stin, sptr]
      unfold orderBase stampsBase at hOrderFit
      omega
    obtain ⟨v, uv, vpc, vWord, vr, vm⟩ := indexedDataRead15 (input := input) (s := u)
      p1 rfl (by rw [hSize]; omega) b1
    let kv : Fin n := ⟨k, hk⟩
    have vVal : (reg v registers.value).val = deg kv := by
      change some (reg v registers.value) =
        st.data[(reg st tinBase).val + (reg st registers.ptr).val]? at vWord
      rw [stin, sptr, sfr _ (Or.inl (by unfold orderBase stampsBase; omega))] at vWord
      have h := congrArg (Option.map Fin.val) vWord
      rw [hIndeg kv] at h
      exact Option.some.inj h
    have vOne : (reg v registers.one).val = 1 :=
      (congrArg Fin.val (vr _ (by decide))).trans sone
    have hf3 : code[v.pc]? = some (.branchLt registers.value registers.one 4 7) := by
      rw [vpc]; rfl
    have nFit : n ≤ 2 ^ bits :=
      Nat.le_trans (by unfold orderBase stampsBase indegBase csrArenaWords at hOrderFit; omega) hw
    have vPtr : (reg v registers.ptr).val = k :=
      (congrArg Fin.val (vr _ (by decide))).trans sptr
    have vClk : (reg v clk).val = q.length :=
      (congrArg Fin.val (vr _ (by decide))).trans sclk
    have vOff : (reg v offsetBase).val = orderBase n m :=
      (congrArg Fin.val (vr _ (by decide))).trans soff
    have vTin : (reg v tinBase).val = indegBase n m :=
      (congrArg Fin.val (vr _ (by decide))).trans stin
    have vZero : (reg v registers.zero).val = 0 :=
      (congrArg Fin.val (vr _ (by decide))).trans szero
    have vCnt : (reg v count).val = n :=
      (congrArg Fin.val (vr _ (by decide))).trans scnt
    by_cases hdz : deg kv = 0
    · have hCost : costFn k = 9 := by simp [costFn, hk, kv, hdz]
      rw [hCost]
      have hlt1 : ltb (reg v registers.value) (reg v registers.one) = true :=
        branchLt_true (by rw [vVal, vOne, hdz]; decide)
      let w : State L := { v with pc := 4 }
      have vw : step code input v = some (.next w) := by
        simpa only [w, hlt1, ite_true] using
          step_branchLt_at (input := input) hf3 (by rw [hlt1, hSize]; decide)
      have p2 : Placed code 4 (indexedDataWrite registers.tmp offsetBase clk registers.ptr) := by
        have hp := @place_slice bits L
          ([.branchLt registers.ptr count 1 9] ++
            indexedDataRead registers.value tinBase registers.ptr ++
            [.branchLt registers.value registers.one 4 7])
          (indexedDataWrite registers.tmp offsetBase clk registers.ptr)
          [.add clk clk registers.one, .add registers.ptr registers.ptr registers.one, .goto 0, .halt]
        rw [show ([Instr.branchLt registers.ptr count 1 9] ++
          indexedDataRead registers.value tinBase registers.ptr ++
          [Instr.branchLt registers.value registers.one 4 7] :
            List (Instr bits 15)).length = 4 from rfl] at hp
        simpa only [code, seedQueuePhase, Phase.ofLast, seedQueueList, List.append_assoc] using hp
      have b2 : (reg w offsetBase).val + (reg w clk).val < workCap := by
        change (reg v offsetBase).val + (reg v clk).val < workCap
        rw [vOff, vClk]; omega
      obtain ⟨x, wx, xpc, xMem, _, xr⟩ := indexedDataWrite15 (input := input) (s := w)
        p2 rfl (by rw [hSize]; omega) (show registers.ptr ≠ registers.tmp by decide) b2
      have hf6 : code[x.pc]? = some (.add clk clk registers.one) := by rw [xpc]; rfl
      obtain ⟨y, xy, ypc, yClk, yr, ym⟩ := step_add15 (input := input) hf6
        (by rw [xpc, hSize]; omega)
      have hf7 : code[y.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
        rw [ypc, xpc]; rfl
      obtain ⟨z, yz, zpc, zPtr, zr, zm⟩ := step_add15 (input := input) hf7
        (by rw [ypc, xpc, hSize]; omega)
      have hf8 : code[z.pc]? = some (.goto 0) := by rw [zpc, ypc, xpc]; rfl
      let t : State L := { z with pc := 0 }
      have zt : step code input z = some (.next t) := step_goto_at hf8 (by rw [hSize]; omega)
      have keep (r : Fin 15) (hp : r ≠ registers.ptr) (hc : r ≠ clk) (ht : r ≠ registers.tmp) :
          reg t r = reg v r :=
        (zr r hp).trans ((yr r hc).trans (xr r ht))
      have keepVal (r : Fin 15) (hp : r ≠ registers.ptr) (hc : r ≠ clk) (ht : r ≠ registers.tmp) :
          (reg t r).val = (reg v r).val := congrArg Fin.val (keep r hp hc ht)
      have xClk : (reg x clk).val = q.length :=
        (congrArg Fin.val (xr _ (by decide))).trans vClk
      have xOne : (reg x registers.one).val = 1 :=
        (congrArg Fin.val (xr _ (by decide))).trans vOne
      have clkFit : (reg x clk).val + (reg x registers.one).val < 2 ^ bits := by
        rw [xClk, xOne]; omega
      have tClk : (reg t clk).val = q.length + 1 := by
        change (reg z clk).val = _
        rw [zr _ (by decide), yClk, add_no_wrap _ _ clkFit, xClk, xOne]
      have yPtr : (reg y registers.ptr).val = k :=
        (congrArg Fin.val ((yr _ (by decide)).trans (xr _ (by decide)))).trans vPtr
      have yOne : (reg y registers.one).val = 1 :=
        (congrArg Fin.val ((yr _ (by decide)).trans (xr _ (by decide)))).trans vOne
      have ptrFit : (reg y registers.ptr).val + (reg y registers.one).val < 2 ^ bits := by
        rw [yPtr, yOne]; omega
      have tPtr : (reg t registers.ptr).val = k + 1 := by
        change (reg z registers.ptr).val = _
        rw [zPtr, add_no_wrap _ _ ptrFit, yPtr, yOne]
      have memEq : t.data = st.data.set (orderBase n m + q.length) (reg v registers.ptr)
          (by rw [st.data_size]; change orderBase n m + q.length < workCap; omega) := by
        change z.data = _
        rw [zm, ym]
        simpa only [show w.data = st.data from vm, show (reg w offsetBase).val = orderBase n m from vOff,
          show (reg w clk).val = q.length from vClk,
          show reg w registers.ptr = reg v registers.ptr from rfl] using xMem
      have keepCell (j : Nat) (hne : j ≠ orderBase n m + q.length) : t.data[j]? = st.data[j]? := by
        rw [memEq]; exact Array.getElem?_set_ne _ hne.symm
      have kFresh : kv ∉ q := fun hm => by
        have h := (qmem_iff kv).mp hm
        change k < k ∧ _ at h
        omega
      have q'nd : (q ++ [kv]).Nodup := by
        rw [List.nodup_append]
        exact ⟨qnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, fun a ha b hb h => by
          subst h; exact kFresh ((List.mem_singleton.mp hb) ▸ ha)⟩
      refine ⟨t, (Steps.cons su uv).append (.cons vw (wx.append (.cons xy (.cons yz (.cons zt (.zero t)))))),
        rfl, tPtr, (keepVal count (by decide) (by decide) (by decide)).trans vCnt,
        (keepVal tinBase (by decide) (by decide) (by decide)).trans vTin,
        (keepVal offsetBase (by decide) (by decide) (by decide)).trans vOff,
        (keepVal registers.zero (by decide) (by decide) (by decide)).trans vZero,
        (keepVal registers.one (by decide) (by decide) (by decide)).trans vOne,
        fun j hj => (keepCell j (by omega)).trans (sfr j hj),
        q ++ [kv], q'nd, by simp; omega, by simp [tClk], ?_, ?_⟩
      · intro i
        have hi := i.isLt
        simp only [List.length_append, List.length_cons, List.length_nil] at hi
        by_cases hlt' : i.val < q.length
        · rw [List.getElem_append_left hlt', keepCell _ (by omega)]
          exact qmem ⟨i.val, hlt'⟩
        · have heq : i.val = q.length := by omega
          have hget : (q ++ [kv])[i.val]'i.isLt = kv := by
            simp [heq]
          rw [hget, heq, memEq, Array.getElem?_set_self, Option.map_some, vPtr]
      · intro u'
        rw [List.mem_append, List.mem_singleton, qmem_iff]
        constructor
        · rintro (⟨h1, h2⟩ | rfl)
          · exact ⟨by omega, h2⟩
          · exact ⟨by change k < k + 1; omega, hdz⟩
        · rintro ⟨h1, h2⟩
          by_cases he : u'.val = k
          · exact Or.inr (Fin.ext he)
          · exact Or.inl ⟨by omega, h2⟩
    · have hCost : costFn k = 6 := by simp [costFn, hk, kv, hdz]
      rw [hCost]
      have hge : ltb (reg v registers.value) (reg v registers.one) = false :=
        branchLt_false (by rw [vVal, vOne]; omega)
      let w : State L := { v with pc := 7 }
      have vw : step code input v = some (.next w) := by
        simpa only [w, hge, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf3 (by rw [hge, hSize]; decide)
      have hf7 : code[w.pc]? = some (.add registers.ptr registers.ptr registers.one) := rfl
      obtain ⟨z, wz, zpc, zPtr, zr, zm⟩ := step_add15 (input := input) hf7
        (by rw [show w.pc = 7 from rfl, hSize]; omega)
      have hf8 : code[z.pc]? = some (.goto 0) := by rw [zpc]; rfl
      let t : State L := { z with pc := 0 }
      have zt : step code input z = some (.next t) := step_goto_at hf8 (by rw [hSize]; omega)
      have ptrFit : (reg v registers.ptr).val + (reg v registers.one).val < 2 ^ bits := by
        rw [vPtr, vOne]; omega
      have tPtr : (reg t registers.ptr).val = k + 1 := by
        change (reg z registers.ptr).val = _
        rw [zPtr]
        change (add (reg v registers.ptr) (reg v registers.one)).val = k + 1
        rw [add_no_wrap _ _ ptrFit, vPtr, vOne]
      have tData : t.data = st.data := zm.trans vm
      refine ⟨t, (Steps.cons su uv).append (.cons vw (.cons wz (.cons zt (.zero t)))),
        rfl, tPtr, (congrArg Fin.val (zr _ (by decide))).trans vCnt,
        (congrArg Fin.val (zr _ (by decide))).trans vTin,
        (congrArg Fin.val (zr _ (by decide))).trans vOff,
        (congrArg Fin.val (zr _ (by decide))).trans vZero,
        (congrArg Fin.val (zr _ (by decide))).trans vOne,
        fun j hj => by rw [tData]; exact sfr j hj,
        q, qnd, by omega, (congrArg Fin.val (zr _ (by decide))).trans vClk,
        fun i => by rw [tData]; exact qmem i, ?_⟩
      intro u'
      rw [qmem_iff]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        have hne : u'.val ≠ k := fun e => hdz (by
          have : u' = kv := Fin.ext e
          subst u'; exact h2)
        exact ⟨by omega, h2⟩
  have hCostBound : ∀ m', iterationCost costFn m' ≤ 9 * m' := by
    intro m'
    induction m' with
    | zero => simp [iterationCost]
    | succ m' ih =>
      simp only [iterationCost, Nat.mul_succ]
      have h1 : costFn m' ≤ 9 := by dsimp [costFn]; split <;> (try split) <;> omega
      omega
  have start : inv 0 s :=
    ⟨pc, hPtr, hCnt, hTin, hOff, hZero, hOne, fun _ _ => rfl, [], List.nodup_nil,
      Nat.le_refl 0, hClk, fun i => i.elim0, fun v => by simp⟩
  obtain ⟨u, steps, ⟨upc, uptr, ucnt, utin, uoff, uzero, uone, ufr, q, qnd, qlen, uclk, qmem, qmem_iff⟩⟩ :=
    loop_steps (code := code) (input := input) n costFn inv stepSpec s start
  have no : ltb (reg u registers.ptr) (reg u count) = false :=
    branchLt_false (by rw [uptr, ucnt]; exact Nat.le_refl _)
  let t : State L := { u with pc := 9 }
  have hf0 : code[u.pc]? = some (.branchLt registers.ptr count 1 9) := by rw [upc]; rfl
  have ut : step code input u = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hf0 (by rw [no, hSize]; decide)
  have exec := (steps.append (.cons ut (.zero t))).halts (step_halt_at rfl)
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  refine ⟨t, trace, iterationCost costFn n + 2, q, by have := hCostBound n; omega, exec,
    qnd, qlen, uclk, qmem, fun v => (qmem_iff v).trans (by simp [v.isLt]), ufr,
    utin, uoff, uzero, uone, ok, ok.peak_eq⟩

theorem bits_ge_four_of_raw {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {input : Input (layout bits inputCap workCap hi hw)} {H : LabelledQuotient}
    (raw : RawQuotientInput input H) : 4 ≤ 2 ^ bits := by
  have h3 : 3 ≤ 2 ^ bits := by
    have := raw.cap_ge
    unfold rawInputCap at this
    omega
  cases bits with
  | zero => simp at h3
  | succ b =>
    cases b with
    | zero => simp at h3
    | succ b =>
      have : 4 = 2 ^ 2 := rfl
      rw [this]
      exact Nat.pow_le_pow_right (by decide) (by omega)

private def countWhere {m : Nat} (p : Fin m → Bool) : Nat → Nat
  | 0 => 0
  | k + 1 => countWhere p k + if h : k < m then (if p ⟨k, h⟩ then 1 else 0) else 0

private theorem countWhere_le {m : Nat} (p : Fin m → Bool) (k : Nat) :
    countWhere p k ≤ k := by
  induction k with
  | zero => exact Nat.le_refl 0
  | succ k ih =>
    unfold countWhere
    split <;> (try split) <;> omega

private theorem countWhere_ext {m : Nat} {p q : Fin m → Bool} (h : ∀ e, p e = q e) (k : Nat) :
    countWhere p k = countWhere q k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold countWhere
    rw [ih]
    split
    · next hk => rw [h ⟨k, hk⟩]
    · rfl

private theorem countWhere_flip_one {m : Nat} {p q : Fin m → Bool} (e₀ : Fin m)
    (hp : p e₀ = true) (hq : q e₀ = false) (hother : ∀ e, e ≠ e₀ → p e = q e) (k : Nat) :
    countWhere p k = countWhere q k + if e₀.val < k then 1 else 0 := by
  induction k with
  | zero => simp [countWhere]
  | succ k ih =>
    unfold countWhere
    rw [ih]
    by_cases hk : k < m
    · simp only [hk, dite_true]
      by_cases he : e₀.val = k
      · have h1 : ¬ (e₀.val < k) := by omega
        have h2 : e₀.val < k + 1 := by omega
        simp only [h1, ite_false, h2, ite_true]
        have heq : e₀ = ⟨k, hk⟩ := Fin.ext he
        rw [heq] at hp hq
        rw [hp, hq]
        simp
      · have hne : (⟨k, hk⟩ : Fin m) ≠ e₀ := fun h => he (congrArg Fin.val h).symm
        rw [hother ⟨k, hk⟩ hne]
        by_cases hlt1 : e₀.val < k
        · have hlt2 : e₀.val < k + 1 := by omega
          simp only [hlt1, ite_true, hlt2]
          omega
        · have hlt2 : ¬ (e₀.val < k + 1) := by omega
          simp only [hlt1, ite_false, hlt2]
          omega
    · simp only [hk, dite_false, Nat.add_zero]
      have := e₀.isLt
      have hlt1 : e₀.val < k := by omega
      have hlt2 : e₀.val < k + 1 := by omega
      simp only [hlt1, ite_true, hlt2]

private theorem countOccPrefix_eq_countWhere {m n : Nat} (f : Fin m → Fin n) (v : Fin n) (k : Nat) :
    countOccPrefix f v k = countWhere (fun e => decide (f e = v)) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold countOccPrefix countWhere
    rw [ih]
    split
    · next hk =>
      by_cases h : f ⟨k, hk⟩ = v <;> simp [h]
    · rfl

private theorem countWhere_pos_exists {m : Nat} {p : Fin m → Bool} (k : Nat)
    (hpos : 0 < countWhere p k) : ∃ e : Fin m, e.val < k ∧ p e = true := by
  induction k with
  | zero => simp [countWhere] at hpos
  | succ k ih =>
    unfold countWhere at hpos
    by_cases hk : k < m
    · simp only [hk, dite_true] at hpos
      by_cases hp : p ⟨k, hk⟩ = true
      · exact ⟨⟨k, hk⟩, Nat.lt_succ_self k, hp⟩
      · have hzero : (if p ⟨k, hk⟩ = true then 1 else 0) = 0 := by simp [hp]
        rw [hzero, Nat.add_zero] at hpos
        obtain ⟨e, he, hpe⟩ := ih hpos
        exact ⟨e, Nat.lt_trans he (Nat.lt_succ_self k), hpe⟩
    · simp only [hk, dite_false, Nat.add_zero] at hpos
      obtain ⟨e, he, hpe⟩ := ih hpos
      exact ⟨e, Nat.lt_trans he (Nat.lt_succ_self k), hpe⟩

private theorem list_nodup_length_le_of_subset {α : Type} [DecidableEq α]
    (xs ys : List α) (hnd : xs.Nodup) (hsub : ∀ x ∈ xs, x ∈ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    have hnd' := List.nodup_cons.mp hnd
    have ha : a ∈ ys := hsub a (by simp)
    have hsub' : ∀ x ∈ xs, x ∈ ys.erase a := fun x hx =>
      (List.mem_erase_of_ne (a := x) (b := a) (l := ys)
        (fun he => hnd'.1 (he ▸ hx))).mpr (hsub x (List.mem_cons_of_mem a hx))
    have hlen := ih (ys.erase a) hnd'.2 hsub'
    have hmem_len : (ys.erase a).length + 1 = ys.length := by
      have := List.length_erase_of_mem ha
      have hpos : 0 < ys.length := List.length_pos_of_mem ha
      omega
    simp only [List.length_cons]
    omega

private theorem list_fin_nodup_length_le {n : Nat} (xs : List (Fin n)) (hnd : xs.Nodup) :
    xs.length ≤ n := by
  have h := list_nodup_length_le_of_subset xs (List.finRange n) hnd (fun x _ => List.mem_finRange x)
  simpa only [List.length_finRange] using h

private theorem list_fin_nodup_eq_length_of_mem {n : Nat} (xs : List (Fin n))
    (hnd : xs.Nodup) (hmem : ∀ x : Fin n, x ∈ xs) : xs.length = n := by
  have h1 := list_fin_nodup_length_le xs hnd
  have h2 := list_nodup_length_le_of_subset (List.finRange n) xs (List.nodup_finRange n)
    (fun x _ => hmem x)
  rw [List.length_finRange] at h2
  omega

private def kahnBfsSetupList (hbits : 4 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .add registers.ptr registers.zero registers.zero,
    .loadInput cmd registers.zero,
    .loadInput registers.value registers.one,
    .imm registers.stackBase ⟨3, hbits⟩,
    .add registers.stackBase registers.stackBase registers.value,
    .add cmd cmd registers.one,
    .add count cmd registers.value,
    .add toutBase count count,
    .add toutBase toutBase toutBase,
    .add childrenBase toutBase count,
    .add childrenBase childrenBase registers.one,
    .add toutBase toutBase registers.one,
    .halt ]

/-- Setup for `kahnBfsPhase`: preserves `clk` (`qTail`), `tinBase` (`indegBase`),
`offsetBase` (`orderBase`), `zero`, `one`, `data`. -/
def kahnBfsSetupPhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (kahnBfsSetupList hbits).toArray 12 rfl rfl rfl

theorem run_kahnBfsSetup (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hbits : 4 ≤ 2 ^ bits) (s : State L)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1)
    (hClk : (reg s clk).val ≤ H.vertexCount)
    (hTin : (reg s tinBase).val = indegBase H.vertexCount H.arcCount)
    (hOff : (reg s offsetBase).val = orderBase H.vertexCount H.arcCount) :
    let n := H.vertexCount
    let m := H.arcCount
    let K := n + 1 + m
    ∃ t : State L,
      run (kahnBfsSetupPhase (hi := hi) (hw := hw) hbits).code input 13 (Phase.initial s) =
        some ⟨t, 13⟩ ∧
      (reg t registers.ptr).val = 0 ∧
      (reg t registers.stackBase).val = 3 + m ∧
      (reg t cmd).val = n + 1 ∧
      (reg t clk).val = (reg s clk).val ∧
      (reg t tinBase).val = indegBase n m ∧
      (reg t toutBase).val = 4 * K + 1 ∧
      (reg t offsetBase).val = orderBase n m ∧
      (reg t childrenBase).val = 5 * K + 1 ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      t.data = s.data := by
  intro n m K
  let code := (kahnBfsSetupPhase (hi := hi) (hw := hw) hbits).code
  have hSize : code.size = 13 := rfl
  have hInFit : 3 + m < 2 ^ bits := by
    have := raw.cap_ge; unfold rawInputCap at this; have := Nat.le_trans this hi; omega
  have hWorkFit : 5 * K + 1 < 2 ^ bits :=
    Nat.lt_of_lt_of_le (show 5 * K + 1 < rawWorkCap n m by unfold rawWorkCap; omega)
      (Nat.le_trans workRoom hw)
  have hnWord : ∃ wn, input.words[0]? = some wn ∧ wn.val = n := by
    cases hw0 : input.words[0]? with
    | none => have h := raw.hdr_n; simp [hw0] at h
    | some w => have h := raw.hdr_n; simp [hw0] at h; exact ⟨w, rfl, h⟩
  have hmWord : ∃ wm, input.words[1]? = some wm ∧ wm.val = m := by
    cases hw1 : input.words[1]? with
    | none => have h := raw.hdr_m; simp [hw1] at h
    | some w => have h := raw.hdr_m; simp [hw1] at h; exact ⟨w, rfl, h⟩
  obtain ⟨wn, hwn, hwnV⟩ := hnWord
  obtain ⟨wm, hwm, hwmV⟩ := hmWord
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1p, fr1, d1⟩ := step_add15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  have hZero1 : (reg s1 registers.zero).val = 0 := by rw [fr1 _ (by decide)]; exact hZero
  obtain ⟨s2, hs12, p2, r2cmd, fr2, d2⟩ := step_loadInput15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega) (by rw [hZero1]; exact hwn)
  have hOne2 : (reg s2 registers.one).val = 1 := by
    rw [fr2 _ (by decide), fr1 _ (by decide)]; exact hOne
  obtain ⟨s3, hs23, p3, r3val, fr3, d3⟩ := step_loadInput15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega) (by rw [hOne2]; exact hwm)
  obtain ⟨s4, hs34, p4, r4sb, fr4, d4⟩ := step_imm15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s5, hs45, p5, r5sb, fr5, d5⟩ := step_add15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s6, hs56, p6, r6cmd, fr6, d6⟩ := step_add15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, p1]; rfl) (by rw [p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s7, hs67, p7, r7cnt, fr7, d7⟩ := step_add15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, p1]; rfl) (by rw [p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s8, hs78, p8, r8tout, fr8, d8⟩ := step_add15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s9, hs89, p9, r9tout, fr9, d9⟩ := step_add15 (code := code) (input := input)
    (s := s8) (by rw [p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s10, hs910, p10, r10cb, fr10, d10⟩ := step_add15 (code := code) (input := input)
    (s := s9) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s11, hs1011, p11, r11cb, fr11, d11⟩ := step_add15 (code := code) (input := input)
    (s := s10) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s12, hs1112, p12, r12tout, fr12, d12⟩ := step_add15 (code := code) (input := input)
    (s := s11) (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 12 (Phase.initial s) s12 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67
      (.cons hs78 (.cons hs89 (.cons hs910 (.cons hs1011 (.cons hs1112 (.zero s12))))))))))))
  have halt : step code input s12 = some (.halted s12) :=
    step_halt_at (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
  have vZero12 : (reg s12 registers.zero).val = 0 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), hZero1]
  have vOne12 : (reg s12 registers.one).val = 1 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), hOne2]
  have vPtr : (reg s12 registers.ptr).val = 0 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), r1p,
      add_no_wrap _ _ (by rw [show (reg (Phase.initial s) registers.zero).val = 0 from hZero]; exact Nat.two_pow_pos bits),
      show (reg (Phase.initial s) registers.zero).val = 0 from hZero]
  have vVal4 : (reg s4 registers.value).val = m := by
    rw [fr4 _ (by decide), r3val, hwmV]
  have vSb4 : (reg s4 registers.stackBase).val = 3 := by rw [r4sb]
  have vSb5 : (reg s5 registers.stackBase).val = 3 + m := by
    rw [r5sb, add_no_wrap _ _ (by rw [vSb4, vVal4]; exact hInFit), vSb4, vVal4]
  have vSb : (reg s12 registers.stackBase).val = 3 + m := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), vSb5]
  have vCmd5 : (reg s5 cmd).val = n := by
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), r2cmd, hwnV]
  have vOne5 : (reg s5 registers.one).val = 1 := by
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), hOne2]
  have vCmd6 : (reg s6 cmd).val = n + 1 := by
    rw [r6cmd, add_no_wrap _ _ (by rw [vCmd5, vOne5]; omega), vCmd5, vOne5]
  have vCmd : (reg s12 cmd).val = n + 1 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), vCmd6]
  have vVal6 : (reg s6 registers.value).val = m := by
    rw [fr6 _ (by decide), fr5 _ (by decide), vVal4]
  have vCnt7 : (reg s7 count).val = K := by
    rw [r7cnt, add_no_wrap _ _ (by rw [vCmd6, vVal6]; change K < 2 ^ bits; omega), vCmd6, vVal6]
  have vTout8 : (reg s8 toutBase).val = 2 * K := by
    rw [r8tout, add_no_wrap _ _ (by rw [vCnt7]; omega), vCnt7]; omega
  have vTout9 : (reg s9 toutBase).val = 4 * K := by
    rw [r9tout, add_no_wrap _ _ (by rw [vTout8]; omega), vTout8]; omega
  have vCnt9 : (reg s9 count).val = K := by
    rw [fr9 _ (by decide), fr8 _ (by decide), vCnt7]
  have vCb10 : (reg s10 childrenBase).val = 5 * K := by
    rw [r10cb, add_no_wrap _ _ (by rw [vTout9, vCnt9]; omega), vTout9, vCnt9]; omega
  have vOne10 : (reg s10 registers.one).val = 1 := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide),
      fr6 _ (by decide), vOne5]
  have vCb11 : (reg s11 childrenBase).val = 5 * K + 1 := by
    rw [r11cb, add_no_wrap _ _ (by rw [vCb10, vOne10]; omega), vCb10, vOne10]
  have vCb : (reg s12 childrenBase).val = 5 * K + 1 := by
    rw [fr12 _ (by decide), vCb11]
  have vTout11 : (reg s11 toutBase).val = 4 * K := by
    rw [fr11 _ (by decide), fr10 _ (by decide), vTout9]
  have vOne11 : (reg s11 registers.one).val = 1 := by
    rw [fr11 _ (by decide), vOne10]
  have vTout : (reg s12 toutBase).val = 4 * K + 1 := by
    rw [r12tout, add_no_wrap _ _ (by rw [vTout11, vOne11]; omega), vTout11, vOne11]
  have vClk : (reg s12 clk).val = (reg s clk).val := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; rfl
  have vTin : (reg s12 tinBase).val = indegBase n m := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hTin
  have vOff : (reg s12 offsetBase).val = orderBase n m := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hOff
  have vData : s12.data = s.data :=
    d12.trans (d11.trans (d10.trans (d9.trans (d8.trans (d7.trans (d6.trans
      (d5.trans (d4.trans (d3.trans (d2.trans d1))))))))))
  exact ⟨s12, hSteps.halts halt, vPtr, vSb, vCmd, vClk, vTin, vTout, vOff, vCb,
    vZero12, vOne12, vData⟩

private def kahnBfsList : List (Instr bits 15) :=
  [ .branchLt registers.ptr clk 1 27,
    .add registers.value offsetBase registers.ptr,
    .loadData registers.value registers.value,
    .add registers.childBase toutBase registers.value,
    .loadData registers.childBase registers.childBase,
    .add registers.value registers.value registers.one,
    .add registers.remain toutBase registers.value,
    .loadData registers.remain registers.remain,
    .branchLt registers.childBase registers.remain 9 25,
    .add registers.value childrenBase registers.childBase,
    .loadData registers.value registers.value,
    .sub registers.value registers.value cmd,
    .add registers.value registers.stackBase registers.value,
    .loadInput registers.value registers.value,
    .add count tinBase registers.value,
    .loadData count count,
    .sub count count registers.one,
    .add registers.tmp tinBase registers.value,
    .storeData registers.tmp count,
    .branchLt count registers.one 20 23,
    .add registers.tmp offsetBase clk,
    .storeData registers.tmp registers.value,
    .add clk clk registers.one,
    .add registers.childBase registers.childBase registers.one,
    .goto 8,
    .add registers.ptr registers.ptr registers.one,
    .goto 0,
    .halt ]

private def kahnBfsArray : Array (Instr bits 15) :=
  { toList := kahnBfsList }

/-- Kahn BFS queue loop over outgoing CSR rows (`orderBase`, `indegBase`), returning
a full topological permutation of `H` when `H.IsAcyclic`. -/
def kahnBfsPhase : Phase L :=
  Phase.ofLast kahnBfsArray 27
    (by simp only [kahnBfsArray, kahnBfsList, List.size_toArray, List.length_cons, List.length_nil])
    (by simp only [kahnBfsArray, kahnBfsList]; rfl)
    (by simp only [kahnBfsArray, kahnBfsList, List.take_succ_cons, List.take_zero,
      List.all_cons, List.all_nil, nonHalt, Bool.and_true])

private theorem kahnBfs_placed2 {entry : Nat} {op0 op1 : Instr bits 15}
    (h0 : (kahnBfsPhase (hi := hi) (hw := hw)).code[entry]? = some op0)
    (h1 : (kahnBfsPhase (hi := hi) (hw := hw)).code[entry + 1]? = some op1) :
    Placed (kahnBfsPhase (hi := hi) (hw := hw)).code entry [op0, op1] := by
  intro i op h
  cases i with
  | zero => rw [Nat.add_zero]; exact h0.trans h
  | succ i =>
    cases i with
    | zero => exact h1.trans h
    | succ i => simp at h

private theorem nodup_getElem_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    (i j : Nat) (hi : i < xs.length) (hj : j < xs.length) (he : xs[i]'hi = xs[j]'hj) :
    i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
    obtain ⟨ha, htail⟩ := List.nodup_cons.mp hnd
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
        change a = xs[j]'hj' at he
        exact (ha (he ▸ List.getElem_mem hj')).elim
    | succ i =>
      have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
      cases j with
      | zero =>
        change xs[i]'hi' = a at he
        exact (ha (he.symm ▸ List.getElem_mem hi')).elim
      | succ j =>
        have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
        exact congrArg Nat.succ (ih htail i j hi' hj' he)

private theorem nodup_map_of_inj {α β : Type} {f : α → β} (hinj : ∀ a b, f a = f b → a = b)
    {xs : List α} (hnd : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons a xs ih =>
    obtain ⟨ha, htail⟩ := List.nodup_cons.mp hnd
    refine List.nodup_cons.mpr ⟨?_, ih htail⟩
    intro hm
    obtain ⟨b, hb, hfb⟩ := List.mem_map.mp hm
    exact ha (hinj b a hfb ▸ hb)

private theorem countWhere_eq_zero {m : Nat} {p : Fin m → Bool}
    (hz : countWhere p m = 0) (e : Fin m) : p e = false := by
  apply Classical.byContradiction
  intro h
  have hp : p e = true := by cases hpe : p e <;> simp_all
  have hpos : 0 < countWhere p m := by
    have : ∀ k, e.val < k → 0 < countWhere p k := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
        unfold countWhere
        by_cases eq : e.val = k
        · have ek : k < m := eq ▸ e.isLt
          have h1 : (⟨k, ek⟩ : Fin m) = e := Fin.ext eq.symm
          simp only [ek, dite_true, h1, hp, ite_true]
          omega
        · have hk' : e.val < k := by omega
          exact Nat.lt_of_lt_of_le (ih hk') (Nat.le_add_right _ _)
    exact this m e.isLt
  omega

private structure KahnInnerInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) (origData : Array (Word bits))
    (k : Nat) (processed : List (Fin H.vertexCount)) (u : Fin H.vertexCount)
    (lo stop : Nat) (row : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length → Fin H.arcCount)
    (c : Nat) (st : State (layout bits inputCap workCap hi hw)) : Type where
  pc : st.pc = 8
  ptr : (reg st registers.ptr).val = k
  sb : (reg st registers.stackBase).val = 3 + H.arcCount
  cmdV : (reg st cmd).val = H.vertexCount + 1
  tin : (reg st tinBase).val = indegBase H.vertexCount H.arcCount
  tout : (reg st toutBase).val = 4 * (H.vertexCount + 1 + H.arcCount) + 1
  off : (reg st offsetBase).val = orderBase H.vertexCount H.arcCount
  cb : (reg st childrenBase).val = 5 * (H.vertexCount + 1 + H.arcCount) + 1
  zeroV : (reg st registers.zero).val = 0
  oneV : (reg st registers.one).val = 1
  cur : (reg st registers.childBase).val = lo + c
  stopV : (reg st registers.remain).val = stop
  frame : ∀ j, (j < indegBase H.vertexCount H.arcCount ∨
      (indegBase H.vertexCount H.arcCount + H.vertexCount ≤ j ∧ j < orderBase H.vertexCount H.arcCount) ∨
      orderBase H.vertexCount H.arcCount + H.vertexCount ≤ j) → st.data[j]? = origData[j]?
  q : List (Fin H.vertexCount)
  qnd : q.Nodup
  kLt : k < q.length
  qtake : q.take k = processed
  qu : q[k]'kLt = u
  clkV : (reg st clk).val = q.length
  qmem : ∀ i : Fin q.length,
    (st.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val = some (q[i.val]'i.isLt).val
  degAt : ∀ v : Fin H.vertexCount,
    (st.data[indegBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
      some (countWhere (fun e : Fin H.arcCount =>
        decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ processed ∧
          ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length, j.val < c → row j ≠ e))
        H.arcCount)
  zeroMem : ∀ v : Fin H.vertexCount, v ∈ q ↔
    countWhere (fun e : Fin H.arcCount =>
      decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ processed ∧
        ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length, j.val < c → row j ≠ e))
      H.arcCount = 0
  topo : ∀ i : Fin q.length, ∀ x : Fin H.vertexCount,
    H.HasQuotientArc x (q[i.val]'i.isLt) →
      ∃ j : Fin q.length, j.val < min i.val (k + 1) ∧ q[j.val]'j.isLt = x

private theorem kahnBfs_inner (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (origData : Array (Word bits))
    (k : Nat) (processed : List (Fin H.vertexCount)) (u : Fin H.vertexCount)
    (huOut : u ∉ processed)
    (lo stop : Nat) (row : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length → Fin H.arcCount)
    (hStop : stop = lo + (rowNodes (fun e => (rawOccurrence H e).1) u).length)
    (hStopLe : stop ≤ H.vertexCount + H.arcCount)
    (hTokens : TokensAt (bits := bits) (vertices := H.vertexCount) origData
      (5 * (H.vertexCount + 1 + H.arcCount) + 1 + lo) row)
    (hRowSrc : ∀ j, (rawOccurrence H (row j)).1 = u)
    (hRowInj : ∀ j₁ j₂, row j₁ = row j₂ → j₁ = j₂) :
    ∀ rem c, rem + c = (rowNodes (fun e => (rawOccurrence H e).1) u).length →
    ∀ st : State L, KahnInnerInv H origData k processed u lo stop row c st →
    ∃ t : State L, ∃ stepsDone : Nat,
      stepsDone ≤ 17 * rem + 1 ∧
      Steps (kahnBfsPhase (hi := hi) (hw := hw)).code input stepsDone st t ∧
      t.pc = 25 ∧
      (reg t registers.ptr).val = k ∧
      (reg t registers.stackBase).val = 3 + H.arcCount ∧
      (reg t cmd).val = H.vertexCount + 1 ∧
      (reg t tinBase).val = indegBase H.vertexCount H.arcCount ∧
      (reg t toutBase).val = 4 * (H.vertexCount + 1 + H.arcCount) + 1 ∧
      (reg t offsetBase).val = orderBase H.vertexCount H.arcCount ∧
      (reg t childrenBase).val = 5 * (H.vertexCount + 1 + H.arcCount) + 1 ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (∀ j, (j < indegBase H.vertexCount H.arcCount ∨
          (indegBase H.vertexCount H.arcCount + H.vertexCount ≤ j ∧
            j < orderBase H.vertexCount H.arcCount) ∨
          orderBase H.vertexCount H.arcCount + H.vertexCount ≤ j) →
        t.data[j]? = origData[j]?) ∧
      ∃ q' : List (Fin H.vertexCount), q'.Nodup ∧ k < q'.length ∧
        q'.take k = processed ∧
        (∀ hlt : k < q'.length, q'[k]'hlt = u) ∧
        (reg t clk).val = q'.length ∧
        (∀ i : Fin q'.length, (t.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val =
          some (q'[i.val]'i.isLt).val) ∧
        (∀ v : Fin H.vertexCount,
          (t.data[indegBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
            some (countWhere (fun e : Fin H.arcCount =>
              decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ processed ∧
                ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length,
                  j.val < (rowNodes (fun e => (rawOccurrence H e).1) u).length → row j ≠ e))
              H.arcCount)) ∧
        (∀ v : Fin H.vertexCount, v ∈ q' ↔
          countWhere (fun e : Fin H.arcCount =>
            decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ processed ∧
              ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length,
                j.val < (rowNodes (fun e => (rawOccurrence H e).1) u).length → row j ≠ e))
            H.arcCount = 0) ∧
        (∀ i : Fin q'.length, ∀ x : Fin H.vertexCount,
          H.HasQuotientArc x (q'[i.val]'i.isLt) →
            ∃ j : Fin q'.length, j.val < min i.val (k + 1) ∧ q'[j.val]'j.isLt = x) := by
  let n := H.vertexCount
  let m := H.arcCount
  let K := n + 1 + m
  let code := (kahnBfsPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 28 := rfl
  have hWorkFit : rawWorkCap n m ≤ 2 ^ bits := Nat.le_trans workRoom hw
  have hwRoom : rawWorkCap n m ≤ workCap := workRoom
  have hInFit : 3 + 2 * m ≤ inputCap := by simpa [rawInputCap] using raw.cap_ge
  have hInBits : 3 + 2 * m ≤ 2 ^ bits := Nat.le_trans hInFit hi
  intro rem
  induction rem with
  | zero =>
    intro c hsum st inv
    have hcurEq : lo + c = stop := by omega
    have hge : ltb (reg st registers.childBase) (reg st registers.remain) = false :=
      branchLt_false (by rw [inv.cur, inv.stopV, hcurEq]; exact Nat.le_refl _)
    have hf8 : code[st.pc]? = some (.branchLt registers.childBase registers.remain 9 25) := by
      rw [inv.pc]; rfl
    let t : State L := { st with pc := 25 }
    have st_step : step code input st = some (.next t) := by
      simpa only [t, hge, Bool.false_eq_true, ite_false] using
        step_branchLt_at (input := input) hf8 (by rw [hge, hSize]; decide)
    have hcEq : c = (rowNodes (fun e => (rawOccurrence H e).1) u).length := by omega
    refine ⟨t, 1, by omega, .cons st_step (.zero t), rfl,
      inv.ptr, inv.sb, inv.cmdV, inv.tin, inv.tout, inv.off, inv.cb, inv.zeroV, inv.oneV,
      inv.frame, inv.q, inv.qnd, inv.kLt, inv.qtake, fun _ => inv.qu, inv.clkV, inv.qmem,
      hcEq ▸ inv.degAt, hcEq ▸ inv.zeroMem, inv.topo⟩
  | succ rem ih =>
    intro c hsum st inv
    have hlt : ltb (reg st registers.childBase) (reg st registers.remain) = true :=
      branchLt_true (by rw [inv.cur, inv.stopV, hStop]; omega)
    have hf8 : code[st.pc]? = some (.branchLt registers.childBase registers.remain 9 25) := by
      rw [inv.pc]; rfl
    let s9 : State L := { st with pc := 9 }
    have hs89 : step code input st = some (.next s9) := by
      simpa only [s9, hlt, ite_true] using
        step_branchLt_at (input := input) hf8 (by rw [hlt, hSize]; decide)
    have pTok : Placed code 9 (indexedDataRead registers.value childrenBase registers.childBase) :=
      kahnBfs_placed2 rfl rfl
    have hcLt : c < (rowNodes (fun e => (rawOccurrence H e).1) u).length := by omega
    let jc : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length := ⟨c, hcLt⟩
    let e₀ : Fin m := row jc
    let w₀ : Fin n := rawHead H e₀
    have bTok : (reg s9 childrenBase).val + (reg s9 registers.childBase).val < workCap := by
      change (reg st childrenBase).val + (reg st registers.childBase).val < workCap
      rw [inv.cb, inv.cur]
      unfold rawWorkCap at workRoom
      omega
    obtain ⟨s11, hs911, p11, r11tok, fr11, d11⟩ := indexedDataRead15 (input := input) (s := s9)
      pTok rfl (by rw [hSize]; omega) bTok
    have vTok11 : (reg s11 registers.value).val = n + 1 + e₀.val := by
      have hOrig := inv.frame (5 * K + 1 + (lo + c)) (Or.inl (by
        unfold indegBase csrArenaWords; omega))
      have hTok := hTokens jc
      change (origData[5 * K + 1 + lo + c]?).map Fin.val = some (arcNode n (row jc)).val at hTok
      have hSame : s9.data[(reg s9 childrenBase).val + (reg s9 registers.childBase).val]? =
          origData[5 * K + 1 + lo + c]? := by
        change st.data[(reg st childrenBase).val + (reg st registers.childBase).val]? = _
        rw [inv.cb, inv.cur, ← Nat.add_assoc] at ⊢
        rw [Nat.add_assoc (5 * K + 1) lo c]
        exact hOrig
      rw [hSame] at r11tok
      have hmap := congrArg (Option.map Fin.val) r11tok.symm
      rw [hTok] at hmap
      exact Option.some.inj hmap.symm
    have hf11 : code[s11.pc]? = some (.sub registers.value registers.value cmd) := by
      rw [p11]; rfl
    obtain ⟨s12, hs1112, p12, r12arc, fr12, d12⟩ := step_sub15 (input := input) hf11
      (by rw [p11, hSize]; omega)
    have vCmd11 : (reg s11 cmd).val = n + 1 :=
      (congrArg Fin.val (fr11 _ (by decide))).trans inv.cmdV
    have vArc12 : (reg s12 registers.value).val = e₀.val := by
      rw [r12arc, sub_exact _ _ (by rw [vTok11, vCmd11]; omega), vTok11, vCmd11]; omega
    have pHead : Placed code 12 (indexedInputRead registers.value registers.stackBase registers.value) :=
      kahnBfs_placed2 rfl rfl
    have vSb12 : (reg s12 registers.stackBase).val = 3 + m :=
      (congrArg Fin.val ((fr12 _ (by decide)).trans (fr11 _ (by decide)))).trans inv.sb
    have bHead : (reg s12 registers.stackBase).val + (reg s12 registers.value).val < inputCap := by
      have := e₀.isLt; rw [vSb12, vArc12]; omega
    obtain ⟨s14, hs1214, p14, r14head, fr14, d14⟩ := indexedInputRead15 (input := input) (s := s12)
      pHead (by rw [p12, p11]) (by rw [hSize]; omega) bHead
    have vHead14 : (reg s14 registers.value).val = w₀.val := by
      rw [vSb12, vArc12] at r14head
      have hmap := congrArg (Option.map Fin.val) r14head.symm
      rw [raw.heads e₀] at hmap
      exact Option.some.inj hmap.symm
    have pDeg : Placed code 14 (indexedDataRead count tinBase registers.value) :=
      kahnBfs_placed2 rfl rfl
    have vTin14 : (reg s14 tinBase).val = indegBase n m :=
      (congrArg Fin.val ((fr14 _ (by decide)).trans ((fr12 _ (by decide)).trans (fr11 _ (by decide))))).trans inv.tin
    have bDeg : (reg s14 tinBase).val + (reg s14 registers.value).val < workCap := by
      have := w₀.isLt; rw [vTin14, vHead14]; unfold rawWorkCap at workRoom; unfold indegBase csrArenaWords; omega
    obtain ⟨s16, hs1416, p16, r16deg, fr16, d16⟩ := indexedDataRead15 (input := input) (s := s14)
      pDeg p14 (by rw [hSize]; omega) bDeg
    let pCur : Fin n → Fin m → Bool := fun v e =>
      decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ processed ∧
        ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length, j.val < c → row j ≠ e)
    let pNext : Fin n → Fin m → Bool := fun v e =>
      decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ processed ∧
        ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length, j.val < c + 1 → row j ≠ e)
    have hFlipW0 : countWhere (pCur w₀) m = countWhere (pNext w₀) m + 1 := by
      have hp1 : pCur w₀ e₀ = true := by
        simp only [pCur, decide_eq_true_eq]
        refine ⟨rfl, ?_, fun j hj hEq => ?_⟩
        · rw [hRowSrc jc]; exact huOut
        · have := hRowInj j jc hEq
          have : j.val = c := congrArg Fin.val this
          omega
      have hp2 : pNext w₀ e₀ = false := by
        simp only [pNext, decide_eq_false_iff_not]
        intro h
        exact h.2.2 jc (Nat.lt_succ_self c) rfl
      have hother : ∀ e, e ≠ e₀ → pCur w₀ e = pNext w₀ e := by
        intro e he
        apply Bool.eq_iff_iff.mpr
        simp only [pCur, pNext, decide_eq_true_eq]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun j hj => ?_⟩
          by_cases hjc : j.val = c
          · have : j = jc := Fin.ext hjc
            subst this; exact he.symm
          · exact h3 j (by omega)
        · rintro ⟨h1, h2, h3⟩
          exact ⟨h1, h2, fun j hj => h3 j (by omega)⟩
      have hf := countWhere_flip_one e₀ hp1 hp2 hother m
      have : e₀.isLt = e₀.isLt := rfl
      simpa only [e₀.isLt, ite_true] using hf
    have hSameOther : ∀ v, v ≠ w₀ → countWhere (pCur v) m = countWhere (pNext v) m := by
      intro v hne
      apply countWhere_ext
      intro e
      apply Bool.eq_iff_iff.mpr
      simp only [pCur, pNext, decide_eq_true_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h1, h2, fun j hj => ?_⟩
        by_cases hjc : j.val = c
        · have : j = jc := Fin.ext hjc
          subst this
          intro he
          exact hne (by rw [← h1, ← he])
        · exact h3 j (by omega)
      · rintro ⟨h1, h2, h3⟩
        exact ⟨h1, h2, fun j hj => h3 j (by omega)⟩
    have s14Data : s14.data = st.data := d14.trans (d12.trans d11)
    have vDeg16 : (reg s16 count).val = countWhere (pCur w₀) m := by
      rw [vTin14, vHead14, s14Data] at r16deg
      have hmap := congrArg (Option.map Fin.val) r16deg.symm
      rw [inv.degAt w₀] at hmap
      exact Option.some.inj hmap.symm
    have hf16 : code[s16.pc]? = some (.sub count count registers.one) := by rw [p16]; rfl
    obtain ⟨s17, hs1617, p17, r17dec, fr17, d17⟩ := step_sub15 (input := input) hf16
      (by rw [p16, hSize]; omega)
    have vOne16 : (reg s16 registers.one).val = 1 :=
      (congrArg Fin.val ((fr16 _ (by decide)).trans ((fr14 _ (by decide)).trans
        ((fr12 _ (by decide)).trans (fr11 _ (by decide)))))).trans inv.oneV
    have vNewDeg17 : (reg s17 count).val = countWhere (pNext w₀) m := by
      rw [r17dec, sub_exact _ _ (by rw [vDeg16, vOne16, hFlipW0]; omega), vDeg16, vOne16, hFlipW0]
      omega
    have pWriteDeg : Placed code 17 (indexedDataWrite registers.tmp tinBase registers.value count) :=
      kahnBfs_placed2 rfl rfl
    have vTin17 : (reg s17 tinBase).val = indegBase n m :=
      (congrArg Fin.val ((fr17 _ (by decide)).trans (fr16 _ (by decide)))).trans vTin14
    have vHead17 : (reg s17 registers.value).val = w₀.val :=
      (congrArg Fin.val ((fr17 _ (by decide)).trans (fr16 _ (by decide)))).trans vHead14
    have bWriteDeg : (reg s17 tinBase).val + (reg s17 registers.value).val < workCap := by
      have := w₀.isLt; rw [vTin17, vHead17]; unfold rawWorkCap at workRoom; unfold indegBase csrArenaWords; omega
    obtain ⟨s19, hs1719, p19, s19Mem, _, fr19⟩ := indexedDataWrite15 (input := input) (s := s17)
      pWriteDeg (by rw [p17, p16]) (by rw [hSize]; omega) (by decide) bWriteDeg
    have s19DataEq : s19.data = st.data.set (indegBase n m + w₀.val) (reg s17 count)
        (by rw [st.data_size]; have := w₀.isLt; change indegBase n m + w₀.val < workCap
            unfold rawWorkCap at workRoom; unfold indegBase csrArenaWords; omega) := by
      simpa only [d17, d16, s14Data, vTin17, vHead17] using s19Mem
    have keepRegs19 : ∀ r : Fin 15, r ≠ registers.tmp → r ≠ registers.value → r ≠ count →
        reg s19 r = reg st r := by
      intro r ht hv hc
      exact (fr19 r ht).trans ((fr17 r hc).trans ((fr16 r hc).trans
        ((fr14 r hv).trans ((fr12 r hv).trans (fr11 r hv)))))
    have vCnt19 : (reg s19 count).val = countWhere (pNext w₀) m :=
      (congrArg Fin.val (fr19 _ (by decide))).trans vNewDeg17
    have vOne19 : (reg s19 registers.one).val = 1 :=
      (congrArg Fin.val (keepRegs19 _ (by decide) (by decide) (by decide))).trans inv.oneV
    have vHead19 : (reg s19 registers.value).val = w₀.val :=
      (congrArg Fin.val (fr19 _ (by decide))).trans vHead17
    have hf19 : code[s19.pc]? = some (.branchLt count registers.one 20 23) := by rw [p19]; rfl
    have degAt19 : ∀ v : Fin n,
        (s19.data[indegBase n m + v.val]?).map Fin.val = some (countWhere (pNext v) m) := by
      intro v
      by_cases ev : v = w₀
      · subst v
        rw [s19DataEq, Array.getElem?_set_self, Option.map_some, vNewDeg17]
      · have hne : indegBase n m + v.val ≠ indegBase n m + w₀.val :=
          fun h => ev (Fin.ext (Nat.add_left_cancel h))
        rw [s19DataEq, Array.getElem?_set_ne _ hne.symm, inv.degAt v, hSameOther v ev]
    have frame19 : ∀ j, (j < indegBase n m ∨ (indegBase n m + n ≤ j ∧ j < orderBase n m) ∨
        orderBase n m + n ≤ j) → s19.data[j]? = origData[j]? := by
      intro j hj
      have := w₀.isLt
      have hne : j ≠ indegBase n m + w₀.val := by
        unfold orderBase stampsBase at hj
        omega
      rw [s19DataEq, Array.getElem?_set_ne _ hne.symm]
      exact inv.frame j hj
    have qmem19 : ∀ i : Fin inv.q.length,
        (s19.data[orderBase n m + i.val]?).map Fin.val = some (inv.q[i.val]'i.isLt).val := by
      intro i
      have := w₀.isLt
      have hne : orderBase n m + i.val ≠ indegBase n m + w₀.val := by
        unfold orderBase stampsBase
        omega
      rw [s19DataEq, Array.getElem?_set_ne _ hne.symm]
      exact inv.qmem i
    by_cases hZeroNext : countWhere (pNext w₀) m = 0
    · have hlt20 : ltb (reg s19 count) (reg s19 registers.one) = true :=
        branchLt_true (by rw [vCnt19, vOne19, hZeroNext]; decide)
      let s20 : State L := { s19 with pc := 20 }
      have hs1920 : step code input s19 = some (.next s20) := by
        simpa only [s20, hlt20, ite_true] using
          step_branchLt_at (input := input) hf19 (by rw [hlt20, hSize]; decide)
      have wFresh : w₀ ∉ inv.q := by
        intro hm
        have := (inv.zeroMem w₀).mp hm
        rw [hFlipW0] at this
        omega
      let q' := inv.q ++ [w₀]
      have q'nd : q'.Nodup := by
        rw [List.nodup_append]
        exact ⟨inv.qnd, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
          fun a ha b hb h => by subst h; exact wFresh ((List.mem_singleton.mp hb) ▸ ha)⟩
      have q'lenLe : q'.length ≤ n := list_fin_nodup_length_le q' q'nd
      have qLenLt : inv.q.length < n := by
        simp only [q', List.length_append, List.length_cons, List.length_nil] at q'lenLe
        omega
      have pEnq : Placed code 20 (indexedDataWrite registers.tmp offsetBase clk registers.value) :=
        kahnBfs_placed2 rfl rfl
      have vOff20 : (reg s20 offsetBase).val = orderBase n m :=
        (congrArg Fin.val (keepRegs19 _ (by decide) (by decide) (by decide))).trans inv.off
      have vClk20 : (reg s20 clk).val = inv.q.length :=
        (congrArg Fin.val (keepRegs19 _ (by decide) (by decide) (by decide))).trans inv.clkV
      have bEnq : (reg s20 offsetBase).val + (reg s20 clk).val < workCap := by
        rw [vOff20, vClk20]
        unfold rawWorkCap at workRoom
        unfold orderBase stampsBase indegBase csrArenaWords
        omega
      obtain ⟨s22, hs2022, p22, s22Mem, _, fr22⟩ := indexedDataWrite15 (input := input) (s := s20)
        pEnq rfl (by rw [hSize]; omega) (by decide) bEnq
      have hf22 : code[s22.pc]? = some (.add clk clk registers.one) := by rw [p22]; rfl
      obtain ⟨s23, hs2223, p23, r23clk, fr23, d23⟩ := step_add15 (input := input) hf22
        (by rw [p22, hSize]; omega)
      have hf23 : code[s23.pc]? = some (.add registers.childBase registers.childBase registers.one) := by
        rw [p23, p22]; rfl
      obtain ⟨s24, hs2324, p24, r24cb, fr24, d24⟩ := step_add15 (input := input) hf23
        (by rw [p23, p22, hSize]; omega)
      have hf24 : code[s24.pc]? = some (.goto 8) := by rw [p24, p23, p22]; rfl
      let stNext : State L := { s24 with pc := 8 }
      have hs24next : step code input s24 = some (.next stNext) :=
        step_goto_at hf24 (by rw [hSize]; omega)
      have vClk22 : (reg s22 clk).val = inv.q.length :=
        (congrArg Fin.val (fr22 _ (by decide))).trans vClk20
      have vOne22 : (reg s22 registers.one).val = 1 :=
        (congrArg Fin.val (fr22 _ (by decide))).trans vOne19
      have clkFit : (reg s22 clk).val + (reg s22 registers.one).val < 2 ^ bits := by
        rw [vClk22, vOne22]; unfold rawWorkCap at hwRoom; omega
      have vClkNext : (reg stNext clk).val = q'.length := by
        change (reg s24 clk).val = _
        rw [fr24 _ (by decide), r23clk, add_no_wrap _ _ clkFit, vClk22, vOne22]
        simp [q']
      have vCb23 : (reg s23 registers.childBase).val = lo + c :=
        (congrArg Fin.val ((fr23 _ (by decide)).trans (fr22 _ (by decide)))).trans
          ((congrArg Fin.val (keepRegs19 _ (by decide) (by decide) (by decide))).trans inv.cur)
      have vOne23 : (reg s23 registers.one).val = 1 :=
        (congrArg Fin.val (fr23 _ (by decide))).trans vOne22
      have cbFit : (reg s23 registers.childBase).val + (reg s23 registers.one).val < 2 ^ bits := by
        rw [vCb23, vOne23]; unfold rawWorkCap at hwRoom; omega
      have vCbNext : (reg stNext registers.childBase).val = lo + (c + 1) := by
        change (reg s24 registers.childBase).val = _
        rw [r24cb, add_no_wrap _ _ cbFit, vCb23, vOne23]; omega
      have keepNext (r : Fin 15) (hc : r ≠ clk) (hcb : r ≠ registers.childBase)
          (ht : r ≠ registers.tmp) (hv : r ≠ registers.value) (hcnt : r ≠ count) :
          reg stNext r = reg st r :=
        (fr24 r hcb).trans ((fr23 r hc).trans ((fr22 r ht).trans (keepRegs19 r ht hv hcnt)))
      have keepValNext (r : Fin 15) (hc : r ≠ clk) (hcb : r ≠ registers.childBase)
          (ht : r ≠ registers.tmp) (hv : r ≠ registers.value) (hcnt : r ≠ count) :
          (reg stNext r).val = (reg st r).val := congrArg Fin.val (keepNext r hc hcb ht hv hcnt)
      have memNext : stNext.data = s19.data.set (orderBase n m + inv.q.length) (reg s20 registers.value)
          (by rw [s19.data_size]; change orderBase n m + inv.q.length < workCap
              unfold rawWorkCap at hwRoom; unfold orderBase stampsBase indegBase csrArenaWords; omega) := by
        change s24.data = _
        rw [d24, d23]
        simpa only [vOff20, vClk20] using s22Mem
      have kLtNext : k < q'.length := by have := inv.kLt; simp [q']; omega
      have invNext : KahnInnerInv H origData k processed u lo stop row (c + 1) stNext := by
        refine ⟨rfl, keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.ptr,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.sb,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.cmdV,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.tin,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.tout,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.off,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.cb,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.zeroV,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.oneV,
          vCbNext, keepValNext _ (by decide) (by decide) (by decide) (by decide) (by decide) |>.trans inv.stopV,
          ?_, q', q'nd, kLtNext, ?_, ?_, vClkNext, ?_, ?_, ?_, ?_⟩
        · intro j hj
          change j < indegBase n m ∨
              (indegBase n m + n ≤ j ∧ j < orderBase n m) ∨ orderBase n m + n ≤ j at hj
          have hne : j ≠ orderBase n m + inv.q.length := by
            unfold orderBase stampsBase at hj ⊢
            have := qLenLt
            omega
          rw [memNext, Array.getElem?_set_ne _ hne.symm]
          exact frame19 j hj
        · rw [List.take_append_of_le_length (Nat.le_of_lt inv.kLt), inv.qtake]
        · rw [List.getElem_append_left inv.kLt, inv.qu]
        · intro i
          change (stNext.data[orderBase n m + i.val]?).map Fin.val = some (q'[i.val]'i.isLt).val
          by_cases hi' : i.val < inv.q.length
          · have hne : orderBase n m + i.val ≠ orderBase n m + inv.q.length := by omega
            rw [memNext, Array.getElem?_set_ne _ hne.symm, qmem19 ⟨i.val, hi'⟩,
              List.getElem_append_left hi']
          · have hiEq : i.val = inv.q.length := by
              have := i.isLt
              simp only [q', List.length_append, List.length_cons, List.length_nil] at this
              omega
            have hget : (q'[i.val]'i.isLt).val = w₀.val := by
              have : q'[i.val]'i.isLt = w₀ := by simp [q', hiEq]
              exact congrArg Fin.val this
            have hw20 : (reg s20 registers.value).val = w₀.val := vHead19
            rw [hget, memNext, hiEq, Array.getElem?_set_self, Option.map_some, hw20]
        · intro v
          have hne : indegBase n m + v.val ≠ orderBase n m + inv.q.length := by
            unfold orderBase stampsBase; omega
          rw [memNext, Array.getElem?_set_ne _ hne.symm]
          exact degAt19 v
        · intro v
          by_cases ev : v = w₀
          · subst v
            simpa only [q', List.mem_append, List.mem_singleton, or_true, true_iff] using hZeroNext
          · simp only [q', List.mem_append, List.mem_singleton, ev, or_false]
            rw [inv.zeroMem v, hSameOther v ev]
        · intro i x hx
          by_cases hi' : i.val < inv.q.length
          · rw [List.getElem_append_left hi'] at hx
            obtain ⟨j, hj, hqx⟩ := inv.topo ⟨i.val, hi'⟩ x hx
            exact ⟨⟨j.val, by simp [q']; omega⟩, hj, by rw [List.getElem_append_left j.isLt]; exact hqx⟩
          · have hiEq : i.val = inv.q.length := by
              have := i.isLt
              simp only [q', List.length_append, List.length_cons, List.length_nil] at this
              omega
            have hget : q'[i.val]'i.isLt = w₀ := by simp [q', hiEq]
            rw [hget] at hx
            obtain ⟨e, heSrc, heHead⟩ := (rawOccurrence_membership H x w₀).mpr hx
            have hxProc : x ∈ processed ∨ x = u := by
              apply Classical.byContradiction
              intro hNot
              have h1 : x ∉ processed := fun hm => hNot (Or.inl hm)
              have h2 : x ≠ u := fun eq => hNot (Or.inr eq)
              have hBad : pNext w₀ e = true := by
                simp only [pNext, decide_eq_true_eq]
                refine ⟨heHead, heSrc ▸ h1, fun j _ hEq => h2 ?_⟩
                rw [← heSrc, ← hEq, hRowSrc j]
              have hz := countWhere_eq_zero hZeroNext e
              rw [hz] at hBad
              cases hBad
            rcases hxProc with hxProc | rfl
            · rw [← inv.qtake] at hxProc
              obtain ⟨j, hj, hqx⟩ := List.mem_iff_getElem.mp hxProc
              rw [List.getElem_take] at hqx
              have hjTake : j < (inv.q.take k).length := hj
              have hjQ : j < inv.q.length := by
                rw [List.length_take] at hjTake
                exact Nat.lt_of_lt_of_le hjTake (Nat.min_le_right _ _)
              have hjK : j < k := by
                rw [List.length_take] at hjTake
                exact Nat.lt_of_lt_of_le hjTake (Nat.min_le_left _ _)
              refine ⟨⟨j, by simp [q']; omega⟩, ?_, ?_⟩
              · change j < min i.val (k + 1)
                have : k < i.val := by rw [hiEq]; exact inv.kLt
                omega
              · change q'[j]'(by simp [q']; omega) = x
                rw [List.getElem_append_left hjQ]; exact hqx
            · refine ⟨⟨k, kLtNext⟩, ?_, ?_⟩
              · change k < min i.val (k + 1)
                have : k < i.val := by rw [hiEq]; exact inv.kLt
                omega
              · change q'[k]'kLtNext = x
                rw [List.getElem_append_left inv.kLt, inv.qu]
      obtain ⟨t, stepsTail, tailLe, hTail, res⟩ := ih (c + 1) (by omega) stNext invNext
      have stepOne : Steps code input 17 st stNext :=
        .cons hs89 (hs911.append (.cons hs1112 (hs1214.append (hs1416.append (.cons hs1617
          (hs1719.append (.cons hs1920 (hs2022.append (.cons hs2223 (.cons hs2324
            (.cons hs24next (.zero stNext))))))))))))
      exact ⟨t, 17 + stepsTail, by omega, stepOne.append hTail, res⟩
    · have hge23 : ltb (reg s19 count) (reg s19 registers.one) = false :=
        branchLt_false (by rw [vCnt19, vOne19]; omega)
      let s23 : State L := { s19 with pc := 23 }
      have hs1923 : step code input s19 = some (.next s23) := by
        simpa only [s23, hge23, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf19 (by rw [hge23, hSize]; decide)
      have hf23 : code[s23.pc]? = some (.add registers.childBase registers.childBase registers.one) := rfl
      obtain ⟨s24, hs2324, p24, r24cb, fr24, d24⟩ := step_add15 (input := input) hf23
        (by rw [show s23.pc = 23 from rfl, hSize]; omega)
      have hf24 : code[s24.pc]? = some (.goto 8) := by rw [p24]; rfl
      let stNext : State L := { s24 with pc := 8 }
      have hs24next : step code input s24 = some (.next stNext) :=
        step_goto_at hf24 (by rw [hSize]; omega)
      have vCb23 : (reg s23 registers.childBase).val = lo + c :=
        (congrArg Fin.val (keepRegs19 _ (by decide) (by decide) (by decide))).trans inv.cur
      have vOne23 : (reg s23 registers.one).val = 1 := vOne19
      have cbFit : (reg s23 registers.childBase).val + (reg s23 registers.one).val < 2 ^ bits := by
        rw [vCb23, vOne23]; unfold rawWorkCap at hwRoom; omega
      have vCbNext : (reg stNext registers.childBase).val = lo + (c + 1) := by
        change (reg s24 registers.childBase).val = _
        rw [r24cb, add_no_wrap _ _ cbFit, vCb23, vOne23]; omega
      have keepNext (r : Fin 15) (hcb : r ≠ registers.childBase)
          (ht : r ≠ registers.tmp) (hv : r ≠ registers.value) (hcnt : r ≠ count) :
          reg stNext r = reg st r :=
        (fr24 r hcb).trans (keepRegs19 r ht hv hcnt)
      have keepValNext (r : Fin 15) (hcb : r ≠ registers.childBase)
          (ht : r ≠ registers.tmp) (hv : r ≠ registers.value) (hcnt : r ≠ count) :
          (reg stNext r).val = (reg st r).val := congrArg Fin.val (keepNext r hcb ht hv hcnt)
      have dataNext : stNext.data = s19.data := d24
      have invNext : KahnInnerInv H origData k processed u lo stop row (c + 1) stNext := by
        refine ⟨rfl, keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.ptr,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.sb,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.cmdV,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.tin,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.tout,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.off,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.cb,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.zeroV,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.oneV,
          vCbNext, keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.stopV,
          fun j hj => by rw [dataNext]; exact frame19 j hj,
          inv.q, inv.qnd, inv.kLt, inv.qtake, inv.qu,
          keepValNext _ (by decide) (by decide) (by decide) (by decide) |>.trans inv.clkV,
          fun i => by rw [dataNext]; exact qmem19 i,
          fun v => by rw [dataNext]; exact degAt19 v,
          ?_, inv.topo⟩
        intro v
        by_cases ev : v = w₀
        · subst v
          rw [inv.zeroMem w₀, hFlipW0]
          exact ⟨fun h => by omega, fun h => absurd h hZeroNext⟩
        · rw [inv.zeroMem v, hSameOther v ev]
      obtain ⟨t, stepsTail, tailLe, hTail, res⟩ := ih (c + 1) (by omega) stNext invNext
      have stepOne : Steps code input 14 st stNext :=
        .cons hs89 (hs911.append (.cons hs1112 (hs1214.append (hs1416.append (.cons hs1617
          (hs1719.append (.cons hs1923 (.cons hs2324 (.cons hs24next (.zero stNext))))))))))
      exact ⟨t, 14 + stepsTail, by omega, stepOne.append hTail, res⟩

private structure KahnOuterInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) (origData : Array (Word bits))
    (k : Nat) (st : State (layout bits inputCap workCap hi hw)) : Type where
  pc : st.pc = 0
  ptr : (reg st registers.ptr).val = k
  sb : (reg st registers.stackBase).val = 3 + H.arcCount
  cmdV : (reg st cmd).val = H.vertexCount + 1
  tin : (reg st tinBase).val = indegBase H.vertexCount H.arcCount
  tout : (reg st toutBase).val = 4 * (H.vertexCount + 1 + H.arcCount) + 1
  off : (reg st offsetBase).val = orderBase H.vertexCount H.arcCount
  cb : (reg st childrenBase).val = 5 * (H.vertexCount + 1 + H.arcCount) + 1
  zeroV : (reg st registers.zero).val = 0
  oneV : (reg st registers.one).val = 1
  csrSame : ∀ j < csrArenaWords H.vertexCount H.arcCount, st.data[j]? = origData[j]?
  frame : ∀ j, (j < indegBase H.vertexCount H.arcCount ∨
      (indegBase H.vertexCount H.arcCount + H.vertexCount ≤ j ∧
        j < orderBase H.vertexCount H.arcCount) ∨
      orderBase H.vertexCount H.arcCount + H.vertexCount ≤ j) → st.data[j]? = origData[j]?
  q : List (Fin H.vertexCount)
  qnd : q.Nodup
  kLe : k ≤ q.length
  clkV : (reg st clk).val = q.length
  qmem : ∀ i : Fin q.length,
    (st.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val = some (q[i.val]'i.isLt).val
  degAt : ∀ v : Fin H.vertexCount,
    (st.data[indegBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
      some (countWhere (fun e : Fin H.arcCount =>
        decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ q.take k)) H.arcCount)
  zeroMem : ∀ v : Fin H.vertexCount, v ∈ q ↔
    countWhere (fun e : Fin H.arcCount =>
      decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ q.take k)) H.arcCount = 0
  topo : ∀ i : Fin q.length, ∀ x : Fin H.vertexCount,
    H.HasQuotientArc x (q[i.val]'i.isLt) →
      ∃ j : Fin q.length, j.val < min i.val k ∧ q[j.val]'j.isLt = x

private def processedArcCount {m n : Nat} (src : Fin m → Fin n) (processed : List (Fin n)) : Nat :=
  countWhere (fun e => decide (src e ∈ processed)) m

private theorem processedArcCount_append {m n : Nat} (src : Fin m → Fin n)
    (processed : List (Fin n)) (u : Fin n) (hu : u ∉ processed) :
    processedArcCount src (processed ++ [u]) =
      processedArcCount src processed + (rowNodes src u).length := by
  let p1 : Fin m → Bool := fun e => decide (src e ∈ processed ++ [u])
  let p2 : Fin m → Bool := fun e => decide (src e ∈ processed)
  let p3 : Fin m → Bool := fun e => decide (src e = u)
  have hdisj : ∀ e : Fin m, ¬ (p2 e = true ∧ p3 e = true) := by
    intro e ⟨h2, h3⟩
    simp only [p2, p3, decide_eq_true_eq] at h2 h3
    exact hu (h3 ▸ h2)
  have hsum : ∀ k, countWhere p1 k = countWhere p2 k + countWhere p3 k := by
    intro k
    induction k with
    | zero => simp [countWhere]
    | succ k ih =>
      unfold countWhere
      rw [ih]
      by_cases hk : k < m
      · simp only [hk, dite_true]
        let e : Fin m := ⟨k, hk⟩
        have hiff : p1 e = true ↔ p2 e = true ∨ p3 e = true := by
          simp [p1, p2, p3, List.mem_append]
        by_cases hp2 : p2 e = true <;> by_cases hp3 : p3 e = true
        · exact (hdisj e ⟨hp2, hp3⟩).elim
        · have hp1 : p1 e = true := hiff.mpr (Or.inl hp2)
          simp [e, hp1, hp2, hp3]; omega
        · have hp1 : p1 e = true := hiff.mpr (Or.inr hp3)
          simp [e, hp1, hp2, hp3]; omega
        · have hp1 : p1 e = false := by
            cases hc : p1 e with
            | false => rfl
            | true => rcases hiff.mp hc with h | h <;> simp_all
          simp [e, hp1, hp2, hp3]
      · simp [hk]
  have hrowLen : countWhere p3 m = (rowNodes src u).length := by
    let pRow : Fin m → Bool := fun e => decide (arcNode n e ∈ rowNodes src u)
    have hext : ∀ e, p3 e = pRow e := by
      intro e
      apply Bool.eq_iff_iff.mpr
      simp only [p3, pRow, decide_eq_true_eq]
      exact (arcNode_in_row src u e).symm
    rw [countWhere_ext hext m]
    have hnodup := rowNodes_nodup src u
    have hm1 : ((List.finRange m).filter pRow).length = countWhere pRow m := by
      have hgen : ∀ k ≤ m, ((List.finRange m).take k |>.filter pRow).length = countWhere pRow k := by
        intro k hk
        induction k with
        | zero => simp [countWhere]
        | succ k ih =>
          have hget : (List.finRange m)[k]? = some ⟨k, hk⟩ := by
            rw [List.getElem?_eq_getElem (by simp; omega), List.getElem_finRange]
            rfl
          have htk : (List.finRange m).take (k + 1) =
              (List.finRange m).take k ++ [⟨k, hk⟩] := by
            rw [List.take_add_one, hget, Option.toList_some]
          rw [htk, List.filter_append, List.length_append, ih (Nat.le_of_lt hk)]
          have hlt : k < m := hk
          by_cases hp : pRow ⟨k, hlt⟩ = true
          · simp [countWhere, hlt, hp]
          · simp [countWhere, hlt, hp]
      have hfull : (List.finRange m).take m = List.finRange m :=
        List.take_of_length_le (by simp)
      simpa only [hfull] using hgen m (Nat.le_refl m)
    have hc1 : countWhere pRow m ≤ (rowNodes src u).length := by
      rw [← hm1]
      have hmapSub : ∀ x ∈ ((List.finRange m).filter pRow).map (arcNode n),
          x ∈ rowNodes src u := by
        intro x hx
        obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        have := (List.mem_filter.mp he).2
        simpa [pRow] using this
      have hmapNd : (((List.finRange m).filter pRow).map (arcNode n)).Nodup := by
        refine nodup_map_of_inj ?_ ((List.nodup_finRange m).filter pRow)
        intro a b hab
        apply Fin.ext
        have := congrArg Fin.val hab
        change n + 1 + a.val = n + 1 + b.val at this
        omega
      have hle := list_nodup_length_le_of_subset _ (rowNodes src u) hmapNd hmapSub
      simpa using hle
    have hc2 : (rowNodes src u).length ≤ countWhere pRow m := by
      rw [← hm1]
      let f : Fin (rowNodes src u).length → Fin m := fun j =>
        let node := (rowNodes src u)[j.val]'j.isLt
        have hm := List.getElem_mem j.isLt
        Classical.choose (rowNodes_are_arcs src u node hm)
      have hSub : ∀ x ∈ (List.finRange (rowNodes src u).length).map f,
          x ∈ (List.finRange m).filter pRow := by
        intro x hx
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
        rw [List.mem_filter]
        refine ⟨List.mem_finRange _, ?_⟩
        have hm := List.getElem_mem j.isLt
        have hsp := (Classical.choose_spec (rowNodes_are_arcs src u _ hm)).1
        simp only [pRow, decide_eq_true_eq]
        rw [← hsp]
        exact hm
      have hNd : ((List.finRange (rowNodes src u).length).map f).Nodup := by
        refine nodup_map_of_inj ?_ (List.nodup_finRange _)
        intro j1 j2 heq
        have hs1 := (Classical.choose_spec (rowNodes_are_arcs src u _ (List.getElem_mem j1.isLt))).1
        have hs2 := (Classical.choose_spec (rowNodes_are_arcs src u _ (List.getElem_mem j2.isLt))).1
        have hnode : (rowNodes src u)[j1.val]'j1.isLt = (rowNodes src u)[j2.val]'j2.isLt := by
          dsimp only [f] at heq
          rw [hs1, hs2, heq]
        exact Fin.ext (nodup_getElem_inj hnodup j1.val j2.val j1.isLt j2.isLt hnode)
      have hle := list_nodup_length_le_of_subset _ _ hNd hSub
      simpa using hle
    omega
  change countWhere p1 m = countWhere p2 m + (rowNodes src u).length
  rw [hsum m, hrowLen]

private theorem kahnBfs_outer (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (aOut : Arena bits workCap (H.vertexCount + 1 + H.arcCount))
    (haBase : aOut.base = 0) (haChildren : aOut.children = H.vertexCount + H.arcCount)
    (origData : Array (Word bits))
    (incOut : IncomingAt aOut (fun e => (rawOccurrence H e).1) origData) :
    ∀ rem k, rem + k = H.vertexCount →
    ∀ st : State L, ∀ inv : KahnOuterInv H origData k st,
    ∃ t : State L, ∃ stepsDone : Nat,
      stepsDone ≤ 11 * rem + 17 * (H.arcCount - processedArcCount (fun e => (rawOccurrence H e).1)
        (inv.q.take k)) + 2 ∧
      run (kahnBfsPhase (hi := hi) (hw := hw)).code input stepsDone st = some ⟨t, stepsDone⟩ ∧
      (reg t offsetBase).val = orderBase H.vertexCount H.arcCount ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (∀ j, (j < indegBase H.vertexCount H.arcCount ∨
          (indegBase H.vertexCount H.arcCount + H.vertexCount ≤ j ∧
            j < orderBase H.vertexCount H.arcCount) ∨
          orderBase H.vertexCount H.arcCount + H.vertexCount ≤ j) →
        t.data[j]? = origData[j]?) ∧
      ∃ q' : List (Fin H.vertexCount), q'.Nodup ∧ (reg t clk).val = q'.length ∧
        (∀ i : Fin q'.length, (t.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val =
          some (q'[i.val]'i.isLt).val) ∧
        (∀ v : Fin H.vertexCount, v ∈ q' ↔
          countWhere (fun e : Fin H.arcCount =>
            decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ q')) H.arcCount = 0) ∧
        (∀ i : Fin q'.length, ∀ x : Fin H.vertexCount,
          H.HasQuotientArc x (q'[i.val]'i.isLt) →
            ∃ j : Fin q'.length, j.val < i.val ∧ q'[j.val]'j.isLt = x) := by
  let n := H.vertexCount
  let m := H.arcCount
  let K := n + 1 + m
  let code := (kahnBfsPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 28 := rfl
  have hWorkFit : rawWorkCap n m ≤ 2 ^ bits := Nat.le_trans workRoom hw
  intro rem
  induction rem with
  | zero =>
    intro k hsum st inv
    have hkLe : inv.q.length ≤ n := list_fin_nodup_length_le inv.q inv.qnd
    have hkEq : k = inv.q.length := by have := inv.kLe; omega
    have hge : ltb (reg st registers.ptr) (reg st clk) = false :=
      branchLt_false (by rw [inv.ptr, inv.clkV]; exact Nat.le_of_eq hkEq.symm)
    have hf0 : code[st.pc]? = some (.branchLt registers.ptr clk 1 27) := by rw [inv.pc]; rfl
    let t : State L := { st with pc := 27 }
    have st_step : step code input st = some (.next t) := by
      simpa only [t, hge, Bool.false_eq_true, ite_false] using
        step_branchLt_at (input := input) hf0 (by rw [hge, hSize]; decide)
    have exec := (Steps.cons st_step (.zero t)).halts (step_halt_at rfl)
    refine ⟨t, 2, by omega, exec, inv.off, inv.zeroV, inv.oneV, inv.frame, inv.q, inv.qnd,
      inv.clkV, inv.qmem, ?_, ?_⟩
    · have htake : inv.q.take k = inv.q := List.take_of_length_le (Nat.le_of_eq hkEq.symm)
      simpa only [htake] using inv.zeroMem
    · intro i x hx
      obtain ⟨j, hj, hqx⟩ := inv.topo i x hx
      exact ⟨j, Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _), hqx⟩
  | succ rem ih =>
    intro k hsum st inv
    by_cases hDone : k = inv.q.length
    · have hge : ltb (reg st registers.ptr) (reg st clk) = false :=
        branchLt_false (by rw [inv.ptr, inv.clkV]; exact Nat.le_of_eq hDone.symm)
      have hf0 : code[st.pc]? = some (.branchLt registers.ptr clk 1 27) := by rw [inv.pc]; rfl
      let t : State L := { st with pc := 27 }
      have st_step : step code input st = some (.next t) := by
        simpa only [t, hge, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) hf0 (by rw [hge, hSize]; decide)
      have exec := (Steps.cons st_step (.zero t)).halts (step_halt_at rfl)
      refine ⟨t, 2, by omega, exec, inv.off, inv.zeroV, inv.oneV, inv.frame, inv.q, inv.qnd,
        inv.clkV, inv.qmem, ?_, ?_⟩
      · have htake : inv.q.take k = inv.q := List.take_of_length_le (Nat.le_of_eq hDone.symm)
        simpa only [htake] using inv.zeroMem
      · intro i x hx
        obtain ⟨j, hj, hqx⟩ := inv.topo i x hx
        exact ⟨j, Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _), hqx⟩
    · have hkLt : k < inv.q.length := Nat.lt_of_le_of_ne inv.kLe hDone
      have hlt : ltb (reg st registers.ptr) (reg st clk) = true :=
        branchLt_true (by rw [inv.ptr, inv.clkV]; exact hkLt)
      have hf0 : code[st.pc]? = some (.branchLt registers.ptr clk 1 27) := by rw [inv.pc]; rfl
      let s1 : State L := { st with pc := 1 }
      have hs01 : step code input st = some (.next s1) := by
        simpa only [s1, hlt, ite_true] using
          step_branchLt_at (input := input) hf0 (by rw [hlt, hSize]; decide)
      have pReadU : Placed code 1 (indexedDataRead registers.value offsetBase registers.ptr) :=
        kahnBfs_placed2 rfl rfl
      have bReadU : (reg s1 offsetBase).val + (reg s1 registers.ptr).val < workCap := by
        change (reg st offsetBase).val + (reg st registers.ptr).val < workCap
        rw [inv.off, inv.ptr]
        have := list_fin_nodup_length_le inv.q inv.qnd
        unfold rawWorkCap at workRoom
        unfold orderBase stampsBase indegBase csrArenaWords
        omega
      obtain ⟨s3, hs13, p3, r3u, fr3, d3⟩ := indexedDataRead15 (input := input) (s := s1)
        pReadU rfl (by rw [hSize]; omega) bReadU
      let u := inv.q[k]'hkLt
      have vU3 : (reg s3 registers.value).val = u.val := by
        change some (reg s3 registers.value) = st.data[(reg st offsetBase).val + (reg st registers.ptr).val]? at r3u
        rw [inv.off, inv.ptr] at r3u
        have hmap := congrArg (Option.map Fin.val) r3u.symm
        rw [inv.qmem ⟨k, hkLt⟩] at hmap
        exact Option.some.inj hmap.symm
      have pReadLo : Placed code 3 (indexedDataRead registers.childBase toutBase registers.value) :=
        kahnBfs_placed2 rfl rfl
      have vTout3 : (reg s3 toutBase).val = 4 * K + 1 :=
        (congrArg Fin.val (fr3 _ (by decide))).trans inv.tout
      have bReadLo : (reg s3 toutBase).val + (reg s3 registers.value).val < workCap := by
        have := u.isLt; rw [vTout3, vU3]; unfold rawWorkCap at workRoom; omega
      obtain ⟨s5, hs35, p5, r5lo, fr5, d5⟩ := indexedDataRead15 (input := input) (s := s3)
        pReadLo p3 (by rw [hSize]; omega) bReadLo
      have hf5 : code[s5.pc]? = some (.add registers.value registers.value registers.one) := by
        rw [p5]; rfl
      obtain ⟨s6, hs56, p6, r6u1, fr6, d6⟩ := step_add15 (input := input) hf5
        (by rw [p5, hSize]; omega)
      have vU5 : (reg s5 registers.value).val = u.val :=
        (congrArg Fin.val (fr5 _ (by decide))).trans vU3
      have vOne5 : (reg s5 registers.one).val = 1 :=
        (congrArg Fin.val ((fr5 _ (by decide)).trans (fr3 _ (by decide)))).trans inv.oneV
      have u1Fit : (reg s5 registers.value).val + (reg s5 registers.one).val < 2 ^ bits := by
        have := u.isLt; rw [vU5, vOne5]; unfold rawWorkCap at workRoom; omega
      have vU6 : (reg s6 registers.value).val = u.val + 1 := by
        rw [r6u1, add_no_wrap _ _ u1Fit, vU5, vOne5]
      have pReadStop : Placed code 6 (indexedDataRead registers.remain toutBase registers.value) :=
        kahnBfs_placed2 rfl rfl
      have vTout6 : (reg s6 toutBase).val = 4 * K + 1 :=
        (congrArg Fin.val ((fr6 _ (by decide)).trans (fr5 _ (by decide)))).trans vTout3
      have bReadStop : (reg s6 toutBase).val + (reg s6 registers.value).val < workCap := by
        have := u.isLt; rw [vTout6, vU6]; unfold rawWorkCap at workRoom; omega
      obtain ⟨s8, hs68, p8, r8stop, fr8, d8⟩ := indexedDataRead15 (input := input) (s := s6)
        pReadStop (by rw [p6, p5]) (by rw [hSize]; omega) bReadStop
      obtain ⟨loW, stopW, row, hLoW, hStopW, hStopWidth, hStopLe, hTokens, hRowSrc, hRowNode⟩ :=
        tokenView_of_incoming incOut u
      have haOff : aOut.offsets = 4 * K := by unfold Arena.offsets; omega
      have haPay : aOut.payload = 5 * K + 1 := by unfold Arena.payload; omega
      have hHeadNodeVal : (ArcParents.headNode m u).val = u.val + 1 := rfl
      have s5Data : s5.data = st.data := d5.trans d3
      have vLo8 : (reg s8 registers.childBase).val = loW.val := by
        have hkeep : reg s8 registers.childBase = reg s5 registers.childBase :=
          (fr8 _ (by decide)).trans (fr6 _ (by decide))
        rw [hkeep]
        have hSame : s3.data[(reg s3 toutBase).val + (reg s3 registers.value).val]? =
            origData[aOut.offsets + (ArcParents.headNode m u).val]? := by
          rw [d3, inv.csrSame _ (by rw [vTout3, vU3]; unfold csrArenaWords; omega)]
          rw [vTout3, vU3, haOff, hHeadNodeVal, Nat.add_assoc, Nat.add_comm 1 u.val]
        rw [hSame] at r5lo
        have hmap := congrArg (Option.map Fin.val) r5lo.symm
        rw [hLoW] at hmap
        exact Option.some.inj hmap.symm
      have vStop8 : (reg s8 registers.remain).val = stopW.val := by
        have hSame : s6.data[(reg s6 toutBase).val + (reg s6 registers.value).val]? =
            origData[aOut.offsets + (ArcParents.headNode m u).val + 1]? := by
          rw [d6, s5Data, inv.csrSame _ (by rw [vTout6, vU6]; unfold csrArenaWords; omega)]
          rw [vTout6, vU6, haOff, hHeadNodeVal,
            show 4 * K + 1 + (u.val + 1) = 4 * K + (u.val + 1) + 1 by omega]
        rw [hSame] at r8stop
        have hmap := congrArg (Option.map Fin.val) r8stop.symm
        rw [hStopW] at hmap
        exact Option.some.inj hmap.symm
      have huOut : u ∉ inv.q.take k := by
        intro hm
        obtain ⟨j, hj, hqj⟩ := List.mem_iff_getElem.mp hm
        rw [List.getElem_take] at hqj
        have hjQ : j < inv.q.length := by have := List.length_take_le k inv.q; omega
        have hjK : j < k := by rw [List.length_take] at hj; omega
        have hqeq : inv.q[j]'hjQ = inv.q[k]'hkLt := hqj
        have hjeq := nodup_getElem_inj inv.qnd j k hjQ hkLt hqeq
        omega
      have hRowInj : ∀ j₁ j₂, row j₁ = row j₂ → j₁ = j₂ := by
        intro j₁ j₂ heq
        have h1 := hRowNode j₁
        have h2 := hRowNode j₂
        have hnode : (rowNodes (fun e => (rawOccurrence H e).1) u)[j₁.val]'j₁.isLt =
            (rowNodes (fun e => (rawOccurrence H e).1) u)[j₂.val]'j₂.isLt := by
          rw [h1, h2, heq]
        exact Fin.ext (nodup_getElem_inj (rowNodes_nodup _ u) j₁.val j₂.val j₁.isLt j₂.isLt hnode)
      have keepS8 (r : Fin 15) (hv : r ≠ registers.value) (hcb : r ≠ registers.childBase)
          (hrem : r ≠ registers.remain) : reg s8 r = reg st r :=
        (fr8 r hrem).trans ((fr6 r hv).trans ((fr5 r hcb).trans (fr3 r hv)))
      have keepVal8 (r : Fin 15) (hv : r ≠ registers.value) (hcb : r ≠ registers.childBase)
          (hrem : r ≠ registers.remain) : (reg s8 r).val = (reg st r).val :=
        congrArg Fin.val (keepS8 r hv hcb hrem)
      have s8Data : s8.data = st.data := d8.trans (d6.trans s5Data)
      have hInnerInv : KahnInnerInv H origData k (inv.q.take k) u loW.val stopW.val row 0 s8 := by
        refine ⟨p8, keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.ptr,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.sb,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.cmdV,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.tin,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.tout,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.off,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.cb,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.zeroV,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.oneV,
          by simpa only [Nat.add_zero] using vLo8, vStop8,
          fun j hj => by rw [s8Data]; exact inv.frame j hj,
          inv.q, inv.qnd, hkLt, rfl, rfl,
          keepVal8 _ (by decide) (by decide) (by decide) |>.trans inv.clkV,
          fun i => by rw [s8Data]; exact inv.qmem i,
          fun v => ?_, fun v => ?_, fun i x hx => ?_⟩
        · rw [s8Data, inv.degAt v]
          simp only [Nat.not_lt_zero, false_implies, implies_true, and_true]
        · rw [inv.zeroMem v]
          simp only [Nat.not_lt_zero, false_implies, implies_true, and_true]
        · obtain ⟨j, hj, hqx⟩ := inv.topo i x hx
          have hmin : min i.val k ≤ min i.val (k + 1) := by omega
          exact ⟨j, Nat.lt_of_lt_of_le hj hmin, hqx⟩
      obtain ⟨s25, stepsInner, hInnerLe, hInnerSteps, s25pc, s25ptr, s25sb, s25cmd, s25tin, s25tout,
          s25off, s25cb, s25zero, s25one, s25frame, q', q'nd, hk1Le, q'take, hqu', s25clk, q'mem,
          s25degAt, q'zeroMem, q'topo⟩ :=
        kahnBfs_inner input raw workRoom origData k (inv.q.take k) u huOut loW.val stopW.val row
          hStopWidth (by rw [haChildren] at hStopLe; exact hStopLe)
          (by simpa only [haPay] using hTokens) hRowSrc hRowInj
          (rowNodes (fun e => (rawOccurrence H e).1) u).length 0 (by omega) s8 hInnerInv
      have hf25 : code[s25.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
        rw [s25pc]; rfl
      obtain ⟨s26, hs2526, p26, r26ptr, fr26, d26⟩ := step_add15 (input := input) hf25
        (by rw [s25pc, hSize]; omega)
      have hf26 : code[s26.pc]? = some (.goto 0) := by rw [p26, s25pc]; rfl
      let stNext : State L := { s26 with pc := 0 }
      have hs26next : step code input s26 = some (.next stNext) :=
        step_goto_at hf26 (by rw [hSize]; omega)
      have q'lenLe : q'.length ≤ n := list_fin_nodup_length_le q' q'nd
      have ptrFit : (reg s25 registers.ptr).val + (reg s25 registers.one).val < 2 ^ bits := by
        rw [s25ptr, s25one]; unfold rawWorkCap at workRoom; omega
      have vPtrNext : (reg stNext registers.ptr).val = k + 1 := by
        change (reg s26 registers.ptr).val = _
        rw [r26ptr, add_no_wrap _ _ ptrFit, s25ptr, s25one]
      have keepNext (r : Fin 15) (hp : r ≠ registers.ptr) : reg stNext r = reg s25 r := fr26 r hp
      have keepValNext (r : Fin 15) (hp : r ≠ registers.ptr) : (reg stNext r).val = (reg s25 r).val :=
        congrArg Fin.val (keepNext r hp)
      have q'takeNext : q'.take (k + 1) = inv.q.take k ++ [u] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk1Le, Option.toList_some, q'take, hqu' hk1Le]
      have hSrcRowIff : ∀ e : Fin m, (rawOccurrence H e).1 = u ↔
          ∃ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length, row j = e := by
        intro e
        constructor
        · intro heSrc
          have hm : arcNode n e ∈ rowNodes (fun e => (rawOccurrence H e).1) u :=
            (arcNode_in_row (fun e => (rawOccurrence H e).1) u e).mpr heSrc
          obtain ⟨j, hj, hnode⟩ := List.mem_iff_getElem.mp hm
          refine ⟨⟨j, hj⟩, ?_⟩
          have hn := hRowNode ⟨j, hj⟩
          rw [hnode] at hn
          apply Fin.ext
          have := congrArg Fin.val hn
          simp only [ArcParents.arcNode] at this
          omega
        · rintro ⟨j, rfl⟩
          exact hRowSrc j
      have hExt : ∀ v : Fin n,
          countWhere (fun e : Fin m =>
            decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ inv.q.take k ∧
              ∀ j : Fin (rowNodes (fun e => (rawOccurrence H e).1) u).length,
                j.val < (rowNodes (fun e => (rawOccurrence H e).1) u).length → row j ≠ e)) m =
          countWhere (fun e : Fin m =>
            decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ q'.take (k + 1))) m := by
        intro v
        apply countWhere_ext
        intro e
        apply Bool.eq_iff_iff.mpr
        have hmemIff : (rawOccurrence H e).1 ∈ q'.take (k + 1) ↔
            (rawOccurrence H e).1 ∈ inv.q.take k ∨ (rawOccurrence H e).1 = u := by
          rw [q'takeNext, List.mem_append, List.mem_singleton]
        simp only [decide_eq_true_eq, hmemIff, not_or]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun heq => ?_⟩
          obtain ⟨j, hj⟩ := (hSrcRowIff e).mp heq
          exact h3 j j.isLt hj
        · rintro ⟨h1, h2, h3⟩
          refine ⟨h1, h2, fun j _ hj => h3 (hj ▸ hRowSrc j)⟩
      let invNext : KahnOuterInv H origData (k + 1) stNext := by
        refine ⟨rfl, vPtrNext, keepValNext _ (by decide) |>.trans s25sb,
          keepValNext _ (by decide) |>.trans s25cmd,
          keepValNext _ (by decide) |>.trans s25tin,
          keepValNext _ (by decide) |>.trans s25tout,
          keepValNext _ (by decide) |>.trans s25off,
          keepValNext _ (by decide) |>.trans s25cb,
          keepValNext _ (by decide) |>.trans s25zero,
          keepValNext _ (by decide) |>.trans s25one,
          ?_, fun j hj => by rw [show stNext.data = s25.data from d26]; exact s25frame j hj,
          q', q'nd, hk1Le, keepValNext _ (by decide) |>.trans s25clk,
          fun i => by rw [show stNext.data = s25.data from d26]; exact q'mem i,
          fun v => ?_, fun v => ?_, q'topo⟩
        · intro j hj
          have hIn : j < indegBase n m := by unfold indegBase; exact hj
          rw [show stNext.data = s25.data from d26]
          exact s25frame j (Or.inl hIn)
        · rw [show stNext.data = s25.data from d26, s25degAt v, hExt v]
        · rw [q'zeroMem v, hExt v]
      have hArcAdd := processedArcCount_append (fun e => (rawOccurrence H e).1) (inv.q.take k) u huOut
      rw [← q'takeNext] at hArcAdd
      have hArcLe : processedArcCount (fun e => (rawOccurrence H e).1) (q'.take (k + 1)) ≤ m :=
        countWhere_le _ m
      obtain ⟨t, stepsTail, tailLe, hTail, res⟩ := ih (k + 1) (by omega) stNext invNext
      have stepPref : Steps code input 8 st s8 := by
        have h1 : Steps code input 3 s5 s8 := Steps.cons hs56 hs68
        have h2 : Steps code input 5 s3 s8 := hs35.append h1
        have h3 : Steps code input 7 s1 s8 := hs13.append h2
        exact Steps.cons hs01 h3
      have stepOne : Steps code input (8 + stepsInner + 2) st stNext :=
        (stepPref.append hInnerSteps).append (Steps.cons hs2526 (Steps.cons hs26next (Steps.zero stNext)))
      obtain ⟨k', last, route, halt, cost⟩ := run_has_steps_then_halt hTail
      have terminal : step code input last = some (.halted t) := by
        obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
        have ht : t = last := sameHalt
        rw [ht]
        exact step_halt_at atHalt
      have exec := (stepOne.append route).halts terminal
      change stepsTail = k' + 1 at cost
      rw [Nat.add_assoc, ← cost] at exec
      refine ⟨t, 8 + stepsInner + 2 + stepsTail, ?_, exec, res⟩
      change stepsTail ≤ 11 * rem + 17 * (m - processedArcCount (fun e => (rawOccurrence H e).1)
        (q'.take (k + 1))) + 2 at tailLe
      change processedArcCount (fun e => (rawOccurrence H e).1) (q'.take (k + 1)) =
        processedArcCount (fun e => (rawOccurrence H e).1) (inv.q.take k) +
          (rowNodes (fun e => (rawOccurrence H e).1) u).length at hArcAdd
      rw [hArcAdd] at hArcLe tailLe
      omega

/-- Run `kahnBfsPhase` from `kahnBfsSetupPhase` state through completion; by `H.IsAcyclic`,
the resulting order visits all `H.vertexCount` vertices in topological order. -/
theorem run_kahnBfs (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (acyc : H.IsAcyclic)
    (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (aOut : Arena bits workCap (H.vertexCount + 1 + H.arcCount))
    (haBase : aOut.base = 0) (haChildren : aOut.children = H.vertexCount + H.arcCount)
    (s : State L) (incOut : IncomingAt aOut (fun e => (rawOccurrence H e).1) s.data)
    (pc : s.pc = 0)
    (hPtr : (reg s registers.ptr).val = 0)
    (hSb : (reg s registers.stackBase).val = 3 + H.arcCount)
    (hCmd : (reg s cmd).val = H.vertexCount + 1)
    (hTin : (reg s tinBase).val = indegBase H.vertexCount H.arcCount)
    (hTout : (reg s toutBase).val = 4 * (H.vertexCount + 1 + H.arcCount) + 1)
    (hOff : (reg s offsetBase).val = orderBase H.vertexCount H.arcCount)
    (hCb : (reg s childrenBase).val = 5 * (H.vertexCount + 1 + H.arcCount) + 1)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1)
    (q0 : List (Fin H.vertexCount)) (q0nd : q0.Nodup) (q0clk : (reg s clk).val = q0.length)
    (q0mem : ∀ i : Fin q0.length,
      (s.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val = some (q0[i.val]'i.isLt).val)
    (hIndeg : ∀ v : Fin H.vertexCount,
      (s.data[indegBase H.vertexCount H.arcCount + v.val]?).map Fin.val =
        some (countOccPrefix (rawHead H) v H.arcCount))
    (q0zero : ∀ v : Fin H.vertexCount, v ∈ q0 ↔ countOccPrefix (rawHead H) v H.arcCount = 0) :
    ∃ t trace work, ∃ order : Array (Vertex H), ∃ size_order : order.size = H.vertexCount,
      work ≤ 11 * H.vertexCount + 17 * H.arcCount + 2 ∧
      run (kahnBfsPhase (hi := hi) (hw := hw)).code input work s = some ⟨t, work⟩ ∧
      order.toList.Nodup ∧
      (∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt order size_order i = v) ∧
      IsTopologicalOrder order size_order ∧
      (∀ i : Fin H.vertexCount,
        (t.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val =
          some (orderedVertexAt order size_order i).val) ∧
      (reg t clk).val = H.vertexCount ∧
      (reg t offsetBase).val = orderBase H.vertexCount H.arcCount ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (∀ j, (j < indegBase H.vertexCount H.arcCount ∨
          (indegBase H.vertexCount H.arcCount + H.vertexCount ≤ j ∧
            j < orderBase H.vertexCount H.arcCount) ∨
          orderBase H.vertexCount H.arcCount + H.vertexCount ≤ j) →
        t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (kahnBfsPhase (hi := hi) (hw := hw)).code input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let n := H.vertexCount
  let m := H.arcCount
  have startInv : KahnOuterInv H s.data 0 s := by
    refine ⟨pc, hPtr, hSb, hCmd, hTin, hTout, hOff, hCb, hZero, hOne,
      fun _ _ => rfl, fun _ _ => rfl, q0, q0nd, Nat.zero_le _, q0clk, q0mem, ?_, ?_, ?_⟩
    · intro v
      rw [hIndeg v, countOccPrefix_eq_countWhere]
      simp only [List.take_zero, List.not_mem_nil, not_false_eq_true, and_true]
    · intro v
      rw [q0zero v, countOccPrefix_eq_countWhere]
      simp only [List.take_zero, List.not_mem_nil, not_false_eq_true, and_true]
    · intro i x hx
      have hdeg0 : countOccPrefix (rawHead H) (q0[i.val]'i.isLt) m = 0 :=
        (q0zero _).mp (List.getElem_mem i.isLt)
      rw [countOccPrefix_eq_countWhere] at hdeg0
      obtain ⟨e, _, heHead⟩ := (rawOccurrence_membership H x _).mpr hx
      have hbad := countWhere_eq_zero hdeg0 e
      simp [heHead] at hbad
  obtain ⟨t, work, hWorkLe, exec, tOff, tZero, tOne, tFrame, q', q'nd, tClk, q'mem, q'zero, q'topo⟩ :=
    kahnBfs_outer input raw workRoom aOut haBase haChildren s.data incOut n 0 (by omega) s startInv
  have hProcLe : 0 ≤ H.arcCount - processedArcCount (fun e => (rawOccurrence H e).1) (q0.take 0) :=
    Nat.zero_le _
  have hMemAll : ∀ v : Fin n, v ∈ q' := by
    obtain ⟨rk, hrk⟩ := acyc
    have hStrong : ∀ bound : Nat, ∀ v : Fin n, rk v = bound → v ∈ q' := by
      intro bound
      induction bound using Nat.strongRecOn with
      | _ bound ih =>
        intro v hbv
        apply Classical.byContradiction
        intro hNot
        have hPos : 0 < countWhere (fun e : Fin m =>
            decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ q')) m := by
          cases hc : countWhere (fun e : Fin m =>
              decide (rawHead H e = v ∧ (rawOccurrence H e).1 ∉ q')) m with
          | zero => exact False.elim (hNot ((q'zero v).mpr hc))
          | succ _ => exact Nat.zero_lt_succ _
        obtain ⟨e, _, hpe⟩ := countWhere_pos_exists m hPos
        simp only [decide_eq_true_eq] at hpe
        have harc : H.HasQuotientArc (rawOccurrence H e).1 v :=
          (rawOccurrence_membership H _ v).mp ⟨e, rfl, hpe.1⟩
        have hlt : rk (rawOccurrence H e).1 < bound := hbv ▸ hrk _ _ harc
        exact hpe.2 (ih (rk (rawOccurrence H e).1) hlt (rawOccurrence H e).1 rfl)
    intro v
    exact hStrong (rk v) v rfl
  have hLenEq : q'.length = n := list_fin_nodup_eq_length_of_mem q' q'nd hMemAll
  let order : Array (Vertex H) := q'.toArray
  have size_order : order.size = n := by simpa [order] using hLenEq
  have hNodup : order.toList.Nodup := by simpa [order] using q'nd
  have hCovers : ∀ v : Vertex H, ∃ i : Fin n, orderedVertexAt order size_order i = v := by
    intro v
    obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp (hMemAll v)
    refine ⟨⟨idx, hLenEq ▸ hidx⟩, ?_⟩
    simpa [orderedVertexAt, order] using hget
  have hTopo : IsTopologicalOrder order size_order := by
    intro i j harc
    have hi : i.val < q'.length := hLenEq.symm ▸ i.isLt
    have hj : j.val < q'.length := hLenEq.symm ▸ j.isLt
    have h1 : orderedVertexAt order size_order i = q'[i.val]'hi := rfl
    have h2 : orderedVertexAt order size_order j = q'[j.val]'hj := rfl
    rw [h1, h2] at harc
    obtain ⟨r, hrLt, hqr⟩ := q'topo ⟨j.val, hj⟩ (q'[i.val]'hi) harc
    have heq := nodup_getElem_inj q'nd r.val i.val r.isLt hi hqr
    change r.val < j.val at hrLt
    change i.val < j.val
    omega
  have hOrderMem : ∀ i : Fin n,
      (t.data[orderBase n m + i.val]?).map Fin.val = some (orderedVertexAt order size_order i).val := by
    intro i
    have hi : i.val < q'.length := hLenEq.symm ▸ i.isLt
    simpa [orderedVertexAt, order] using q'mem ⟨i.val, hi⟩
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  refine ⟨t, trace, work, order, size_order, ?_, exec, hNodup, hCovers, hTopo, hOrderMem,
    tClk.trans hLenEq, tOff, tZero, tOne, tFrame, ok, ok.peak_eq⟩
  have hArcUpper : m - processedArcCount (fun e => (rawOccurrence H e).1) (q0.take 0) ≤ m :=
    Nat.sub_le _ _
  omega

private def rankScatterSetupList : List (Instr bits 15) :=
  [ .mov count clk,
    .mov childrenBase offsetBase,
    .add childrenBase childrenBase count,
    .add registers.ptr registers.zero registers.zero,
    .halt ]

/-- Setup for `rankScatterPhase`: sets `count = n`, `childrenBase = ranksBase n m`, `ptr = 0`. -/
def rankScatterSetupPhase : Phase L :=
  Phase.ofLast rankScatterSetupList.toArray 4 rfl rfl rfl

theorem run_rankScatterSetup (input : Input L) {n m : Nat}
    (hRankFit : ranksBase n m + n < workCap) (s : State L)
    (hClk : (reg s clk).val = n)
    (hOff : (reg s offsetBase).val = orderBase n m)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1) :
    ∃ t : State L,
      run (rankScatterSetupPhase (hi := hi) (hw := hw)).code input 5 (Phase.initial s) =
        some ⟨t, 5⟩ ∧
      (reg t registers.ptr).val = 0 ∧
      (reg t count).val = n ∧
      (reg t offsetBase).val = orderBase n m ∧
      (reg t childrenBase).val = ranksBase n m ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      t.data = s.data := by
  let code := (rankScatterSetupPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 5 := rfl
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1cnt, fr1, d1⟩ := step_mov15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2cb, fr2, d2⟩ := step_mov15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3cb, fr3, d3⟩ := step_add15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  obtain ⟨s4, hs34, p4, r4p, fr4, d4⟩ := step_add15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 4 (Phase.initial s) s4 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.zero s4))))
  have halt : step code input s4 = some (.halted s4) :=
    step_halt_at (by rw [p4, p3, p2, p1]; rfl)
  have vZero3 : (reg s3 registers.zero).val = 0 := by
    rw [fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hZero
  have vPtr : (reg s4 registers.ptr).val = 0 := by
    rw [r4p, add_no_wrap _ _ (by rw [vZero3]; exact Nat.two_pow_pos bits), vZero3]
  have vCnt2 : (reg s2 count).val = n := by
    rw [fr2 _ (by decide), r1cnt]; exact hClk
  have vCnt : (reg s4 count).val = n := by
    rw [fr4 _ (by decide), fr3 _ (by decide), vCnt2]
  have vOff : (reg s4 offsetBase).val = orderBase n m := by
    rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hOff
  have vCb2 : (reg s2 childrenBase).val = orderBase n m := by
    rw [r2cb, fr1 _ (by decide)]; exact hOff
  have vCb : (reg s4 childrenBase).val = ranksBase n m := by
    have hFit : orderBase n m + n < 2 ^ bits :=
      Nat.lt_of_lt_of_le (by unfold ranksBase at hRankFit; omega) hw
    rw [fr4 _ (by decide), r3cb, add_no_wrap _ _ (by rw [vCb2, vCnt2]; exact hFit), vCb2, vCnt2]
    rfl
  have vZero : (reg s4 registers.zero).val = 0 := by rw [fr4 _ (by decide), vZero3]
  have vOne : (reg s4 registers.one).val = 1 := by
    rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hOne
  exact ⟨s4, hSteps.halts halt, vPtr, vCnt, vOff, vCb, vZero, vOne,
    d4.trans (d3.trans (d2.trans d1))⟩

private def rankScatterList : List (Instr bits 15) :=
  [.branchLt registers.ptr count 1 7] ++
    indexedDataRead registers.value offsetBase registers.ptr ++
    indexedDataWrite registers.tmp childrenBase registers.value registers.ptr ++
    [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]

/-- Scatter inverse ranks from mutable `s.data[orderBase..orderBase+n)` into `s.data[ranksBase..ranksBase+n)`. -/
def rankScatterPhase : Phase L :=
  Phase.ofLast rankScatterList.toArray 7 rfl rfl rfl

theorem run_rankScatter (input : Input L) {H : LabelledQuotient}
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (nodup : order.toList.Nodup)
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt order size_order i = v)
    (topo : IsTopologicalOrder order size_order)
    (hRankFit : ranksBase H.vertexCount H.arcCount + H.vertexCount ≤ workCap)
    (s : State L) (pc : s.pc = 0)
    (hPtr : (reg s registers.ptr).val = 0)
    (hCnt : (reg s count).val = H.vertexCount)
    (hOff : (reg s offsetBase).val = orderBase H.vertexCount H.arcCount)
    (hCb : (reg s childrenBase).val = ranksBase H.vertexCount H.arcCount)
    (hOne : (reg s registers.one).val = 1)
    (hOrderMem : ∀ i : Fin H.vertexCount,
      (s.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val =
        some (orderedVertexAt order size_order i).val) :
    let n := H.vertexCount
    let m := H.arcCount
    let rank := readRank (orderRanks order nodup)
    ∃ t trace,
      run (rankScatterPhase (hi := hi) (hw := hw)).code input (7 * n + 2) s =
        some ⟨t, 7 * n + 2⟩ ∧
      (∀ i : Fin n, rank (orderedVertexAt order size_order i) = i.val) ∧
      (∀ i j : Fin n, i.val < j.val →
        rank (orderedVertexAt order size_order i) < rank (orderedVertexAt order size_order j)) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) ∧
      (∀ v : Vertex H, (t.data[ranksBase n m + v.val]?).map Fin.val = some (rank v)) ∧
      (∀ j, (j < ranksBase n m ∨ ranksBase n m + n ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (rankScatterPhase (hi := hi) (hw := hw)).code input s trace ⟨t, 7 * n + 2⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let n := H.vertexCount
  let m := H.arcCount
  let code := (rankScatterPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 8 := rfl
  let inv : Nat → State L → Prop := fun k q =>
    q.pc = 0 ∧ (reg q registers.ptr).val = k ∧ (reg q count).val = n ∧
    (reg q offsetBase).val = orderBase n m ∧ (reg q childrenBase).val = ranksBase n m ∧
    (reg q registers.one).val = 1 ∧
    (∀ i : Fin n, i.val < k →
      (q.data[ranksBase n m + (orderedVertexAt order size_order i).val]?).map Fin.val = some i.val) ∧
    (∀ j, (j < ranksBase n m ∨ ranksBase n m + n ≤ j) → q.data[j]? = s.data[j]?)
  have stepSpec : ∀ k, k < n → BlockSpec code input 7 (inv k) (inv (k + 1)) := by
    intro k hk st ⟨spc, sptr, scnt, soff, scb, sone, sranked, sfr⟩
    have hlt : ltb (reg st registers.ptr) (reg st count) = true :=
      branchLt_true (by rw [sptr, scnt]; exact hk)
    have hf0 : code[st.pc]? = some (.branchLt registers.ptr count 1 7) := by rw [spc]; rfl
    let u : State L := { st with pc := 1 }
    have su : step code input st = some (.next u) := by
      simpa only [u, hlt, ite_true] using
        step_branchLt_at (input := input) hf0 (by rw [hlt, hSize]; decide)
    have p1 : Placed code 1 (indexedDataRead registers.value offsetBase registers.ptr) := by
      have hp := @place_slice bits L
        [.branchLt registers.ptr count 1 7]
        (indexedDataRead registers.value offsetBase registers.ptr)
        (indexedDataWrite registers.tmp childrenBase registers.value registers.ptr ++
          [.add registers.ptr registers.ptr registers.one, .goto 0, .halt])
      rw [show ([Instr.branchLt registers.ptr count 1 7] : List (Instr bits 15)).length = 1 from rfl] at hp
      simpa only [code, rankScatterPhase, Phase.ofLast, rankScatterList, List.append_assoc] using hp
    have b1 : (reg u offsetBase).val + (reg u registers.ptr).val < workCap := by
      change (reg st offsetBase).val + (reg st registers.ptr).val < workCap
      rw [soff, sptr]
      change orderBase n m + k < workCap
      have hrf : ranksBase n m + n ≤ workCap := hRankFit
      unfold ranksBase at hrf
      omega
    obtain ⟨v, uv, vpc, vWord, vr, vm⟩ := indexedDataRead15 (input := input) (s := u)
      p1 rfl (by rw [hSize]; omega) b1
    let ik : Fin n := ⟨k, hk⟩
    let wk := orderedVertexAt order size_order ik
    have vVal : (reg v registers.value).val = wk.val := by
      change some (reg v registers.value) =
        st.data[(reg st offsetBase).val + (reg st registers.ptr).val]? at vWord
      rw [soff, sptr, sfr _ (Or.inl (by unfold ranksBase; omega))] at vWord
      have hmap := congrArg (Option.map Fin.val) vWord.symm
      rw [hOrderMem ik] at hmap
      exact Option.some.inj hmap.symm
    have p2 : Placed code 3 (indexedDataWrite registers.tmp childrenBase registers.value registers.ptr) := by
      have hp := @place_slice bits L
        ([.branchLt registers.ptr count 1 7] ++
          indexedDataRead registers.value offsetBase registers.ptr)
        (indexedDataWrite registers.tmp childrenBase registers.value registers.ptr)
        [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]
      rw [show ([Instr.branchLt registers.ptr count 1 7] ++
          indexedDataRead registers.value offsetBase registers.ptr : List (Instr bits 15)).length = 3 from rfl] at hp
      simpa only [code, rankScatterPhase, Phase.ofLast, rankScatterList, List.append_assoc] using hp
    have vCb : (reg v childrenBase).val = ranksBase n m :=
      (congrArg Fin.val (vr _ (by decide))).trans scb
    have vPtr : (reg v registers.ptr).val = k :=
      (congrArg Fin.val (vr _ (by decide))).trans sptr
    have b2 : (reg v childrenBase).val + (reg v registers.value).val < workCap := by
      have := wk.isLt
      rw [vCb, vVal]
      change ranksBase n m + wk.val < workCap
      have hrf : ranksBase n m + n ≤ workCap := hRankFit
      omega
    obtain ⟨w, vw, wpc, wMem, _, wr⟩ := indexedDataWrite15 (input := input) (s := v)
      p2 vpc (by rw [hSize]; omega) (by decide) b2
    have hf5 : code[w.pc]? = some (.add registers.ptr registers.ptr registers.one) := by rw [wpc]; rfl
    obtain ⟨x, wx, xpc, xPtr, xr, xm⟩ := step_add15 (input := input) hf5
      (by rw [wpc, hSize]; omega)
    have hf6 : code[x.pc]? = some (.goto 0) := by rw [xpc, wpc]; rfl
    let t : State L := { x with pc := 0 }
    have xt : step code input x = some (.next t) := step_goto_at hf6 (by rw [hSize]; omega)
    have wPtr : (reg w registers.ptr).val = k :=
      (congrArg Fin.val (wr _ (by decide))).trans vPtr
    have wOne : (reg w registers.one).val = 1 :=
      (congrArg Fin.val ((wr _ (by decide)).trans (vr _ (by decide)))).trans sone
    have nFit : n ≤ 2 ^ bits :=
      Nat.le_trans (by unfold ranksBase orderBase stampsBase indegBase csrArenaWords at hRankFit; omega) hw
    have ptrFit : (reg w registers.ptr).val + (reg w registers.one).val < 2 ^ bits := by
      rw [wPtr, wOne]; omega
    have tPtr : (reg t registers.ptr).val = k + 1 := by
      change (reg x registers.ptr).val = _
      rw [xPtr, add_no_wrap _ _ ptrFit, wPtr, wOne]
    have keep (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp) (hv : r ≠ registers.value) :
        reg t r = reg st r :=
      (xr r hp).trans ((wr r ht).trans (vr r hv))
    have keepVal (r : Fin 15) (hp : r ≠ registers.ptr) (ht : r ≠ registers.tmp) (hv : r ≠ registers.value) :
        (reg t r).val = (reg st r).val := congrArg Fin.val (keep r hp ht hv)
    have memEq : t.data = st.data.set (ranksBase n m + wk.val) (reg v registers.ptr)
        (by rw [st.data_size]; have := wk.isLt; change ranksBase n m + wk.val < workCap; omega) := by
      change x.data = _
      rw [xm]
      simpa only [vm, vCb, vVal] using wMem
    have keepCell (j : Nat) (hne : j ≠ ranksBase n m + wk.val) : t.data[j]? = st.data[j]? := by
      rw [memEq]; exact Array.getElem?_set_ne _ hne.symm
    refine ⟨t, (Steps.cons su uv).append (vw.append (.cons wx (.cons xt (.zero t)))), rfl, tPtr,
      keepVal count (by decide) (by decide) (by decide) |>.trans scnt,
      keepVal offsetBase (by decide) (by decide) (by decide) |>.trans soff,
      keepVal childrenBase (by decide) (by decide) (by decide) |>.trans scb,
      keepVal registers.one (by decide) (by decide) (by decide) |>.trans sone, ?_, ?_⟩
    · intro i hi
      by_cases ei : i.val = k
      · have hieq : i = ik := Fin.ext ei
        subst hieq
        rw [memEq, Array.getElem?_set_self, Option.map_some, vPtr]
      · have hiLt : i.val < k := by omega
        have hne : ranksBase n m + (orderedVertexAt order size_order i).val ≠
            ranksBase n m + wk.val := by
          intro he
          have hv : orderedVertexAt order size_order i = wk := Fin.ext (Nat.add_left_cancel he)
          have hl1 : i.val < order.toList.length := by simpa only [Array.length_toList, size_order] using i.isLt
          have hl2 : ik.val < order.toList.length := by simpa only [Array.length_toList, size_order] using ik.isLt
          have he2 : order.toList[i.val]'hl1 = order.toList[ik.val]'hl2 := hv
          exact ei (nodup_getElem_inj nodup i.val ik.val hl1 hl2 he2)
        rw [keepCell _ hne]
        exact sranked i hiLt
    · intro j hj
      have := wk.isLt
      rw [keepCell _ (by omega)]
      exact sfr j hj
  have h7 : ∀ m', iterationCost (fun _ => 7) m' = 7 * m' := by
    intro m'; induction m' with | zero => rfl | succ m' ih => simp [iterationCost, ih, Nat.mul_succ]
  have start : inv 0 s :=
    ⟨pc, hPtr, hCnt, hOff, hCb, hOne, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩
  obtain ⟨u, steps, upc, uptr, ucnt, _, _, _, uranked, ufr⟩ :=
    loop_steps (code := code) (input := input) n (fun _ => 7) inv stepSpec s start
  rw [h7] at steps
  have no : ltb (reg u registers.ptr) (reg u count) = false :=
    branchLt_false (by rw [uptr, ucnt]; exact Nat.le_refl _)
  let t : State L := { u with pc := 7 }
  have hf0 : code[u.pc]? = some (.branchLt registers.ptr count 1 7) := by rw [upc]; rfl
  have ut : step code input u = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) hf0 (by rw [no, hSize]; decide)
  have exec := (steps.append (.cons ut (.zero t))).halts (step_halt_at rfl)
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  let rank := readRank (orderRanks order nodup)
  refine ⟨t, trace, exec, orderRanks_at order size_order nodup,
    orderRanks_increasing order size_order nodup,
    orderRanks_rankArc order size_order nodup covers topo, ?_, ufr, ok, ok.peak_eq⟩
  intro v
  obtain ⟨i, rfl⟩ := covers v
  rw [orderRanks_at order size_order nodup i]
  exact uranked i i.isLt

private theorem incomingAt_of_agree {vertices arcs : Nat} {a : Arena bits workCap (vertices + 1 + arcs)}
    {heads : Fin arcs → Fin vertices} {d1 d2 : Array (Word bits)}
    (inc : IncomingAt a heads d1)
    (h : ∀ j < a.payload + a.children, d2[j]? = d1[j]?) : IncomingAt a heads d2 := by
  intro v
  obtain ⟨lo, stop, hLo, hStop, hW, hFit, hCells⟩ := inc v
  have h1 : a.offsets + (ArcParents.headNode arcs v).val < a.payload + a.children := by
    have := (ArcParents.headNode arcs v).isLt
    unfold Arena.offsets Arena.payload; omega
  have h2 : a.offsets + (ArcParents.headNode arcs v).val + 1 < a.payload + a.children := by
    have := (ArcParents.headNode arcs v).isLt
    unfold Arena.offsets Arena.payload; omega
  refine ⟨lo, stop, (h _ h1).trans hLo, (h _ h2).trans hStop, hW, hFit, ?_⟩
  intro j
  have hj : a.payload + (lo.val + j.val) < a.payload + a.children := by
    have := j.isLt; omega
  have hCellEq : d2[a.payload + lo.val + j.val]? = d1[a.payload + lo.val + j.val]? := by
    rw [Nat.add_assoc]; exact h _ hj
  simpa only [hCellEq] using hCells j

/-- Complete ordered phase list for Stage 1A: outgoing CSR -> indegree zero/count ->
Kahn queue seed -> Kahn BFS -> inverse rank scatter. -/
def kahnStagePhases (hbits : 4 ≤ 2 ^ bits) : List (Phase L) :=
  [ initOutgoingCsrRegsPhase hbits,
    rawIncomingPhase,
    initIndegSetupPhase (by omega),
    zeroBankPhase,
    countIndegSetupPhase hbits,
    countIndegPhase,
    seedQueueSetupPhase,
    seedQueuePhase,
    kahnBfsSetupPhase hbits,
    kahnBfsPhase,
    rankScatterSetupPhase,
    rankScatterPhase ]

/-- Single linked ROM phase for Stage 1A (outgoing CSR + Kahn topological order + inverse ranks). -/
def kahnStagePhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  pipelinePhase (kahnStagePhases hbits)

theorem kahnStagePhase_code (hbits : 4 ≤ 2 ^ bits) :
    (kahnStagePhase (hi := hi) (hw := hw) hbits).code =
      pipeline (kahnStagePhases (hi := hi) (hw := hw) hbits) :=
  pipelinePhase_code _

/-- Execute Stage 1A as a `PhasesRun` starting from arbitrary initial state `s₀`. -/
theorem run_kahn_stage_phases (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (acyc : H.IsAcyclic)
    (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s₀ : State L) :
    let n := H.vertexCount
    let m := H.arcCount
    let hbits := bits_ge_four_of_raw raw
    ∃ t work, ∃ order : Array (Vertex H), ∃ size_order : order.size = n, ∃ rank : Vertex H → Nat,
      work ≤ 84 * n + 79 * m + 150 ∧
      PhasesRun input (kahnStagePhases (hi := hi) (hw := hw) hbits) s₀ t work ∧
      order.toList.Nodup ∧
      (∀ v : Vertex H, ∃ i : Fin n, orderedVertexAt order size_order i = v) ∧
      IsTopologicalOrder order size_order ∧
      (∀ i : Fin n, rank (orderedVertexAt order size_order i) = i.val) ∧
      (∀ i j : Fin n, i.val < j.val →
        rank (orderedVertexAt order size_order i) <
          rank (orderedVertexAt order size_order j)) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) ∧
      (∀ i : Fin n,
        (t.data[orderBase n m + i.val]?).map Fin.val =
          some (orderedVertexAt order size_order i).val) ∧
      (∀ v : Vertex H, (t.data[ranksBase n m + v.val]?).map Fin.val = some (rank v)) := by
  intro n m hbits
  let K := n + 1 + m
  let aOut : Arena bits workCap K :=
    ⟨0, n + m, by unfold rawWorkCap at workRoom; omega,
      Nat.lt_of_lt_of_le (show 0 + 5 * K + 1 + (n + m) < rawWorkCap n m by unfold rawWorkCap; omega)
        (Nat.le_trans workRoom hw)⟩
  obtain ⟨s1, r1, cur1, clk1, cb1, d1⟩ := run_initOutgoingCsrRegs input raw workRoom s₀
  obtain ⟨s2, _, w2, w2Le, incOut, _, r2, _, _⟩ :=
    run_raw_incoming_framed input aOut (fun e => (rawOccurrence H e).1) 3
      (by have := raw.cap_ge; unfold rawInputCap at this; omega)
      raw.sources (by change n + 1 + m - 1 ≤ n + m; omega) s1 cur1 clk1 cb1
  obtain ⟨s3, r3, zp3, rem3, d3⟩ := run_initIndegSetup input raw workRoom s2
  have inc3 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s3.data := by
    simpa only [d3] using incOut
  have zp3' : ZeroBankParams (indegBase n m) n (Phase.initial s3) :=
    ⟨zp3.ptr, zp3.countVal, zp3.baseVal, zp3.zeroVal, zp3.oneVal, zp3.room⟩
  obtain ⟨s4, _, r4, zeroes4, frame4, regs4, _, _⟩ :=
    run_zeroBank input (indegBase n m) n (Phase.initial s3) rfl zp3'
  have inc4 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s4.data :=
    incomingAt_of_agree inc3 (fun j hj => frame4 j (Or.inl (by
      unfold indegBase csrArenaWords; unfold Arena.payload at hj; change j < 0 + 5 * K + 1 + (n + m) at hj; omega)))
  have rem4 : (reg s4 registers.remain).val = m :=
    (congrArg Fin.val (regs4 _ (by decide) (by decide))).trans rem3
  have tin4 : (reg s4 tinBase).val = indegBase n m :=
    (congrArg Fin.val (regs4 _ (by decide) (by decide))).trans zp3.baseVal
  have zero4 : (reg s4 registers.zero).val = 0 :=
    (congrArg Fin.val (regs4 _ (by decide) (by decide))).trans zp3.zeroVal
  have one4 : (reg s4 registers.one).val = 1 :=
    (congrArg Fin.val (regs4 _ (by decide) (by decide))).trans zp3.oneVal
  obtain ⟨s5, r5, ptr5, cnt5, head5, tin5, zero5, one5, d5⟩ :=
    run_countIndegSetup input hbits raw.cap_ge s4 rem4 tin4 zero4 one4
  have inc5 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s5.data := by
    simpa only [d5] using inc4
  have zeroes5 : ∀ v : Fin n, (s5.data[indegBase n m + v.val]?).map Fin.val = some 0 := by
    intro v; rw [d5]; exact zeroes4 v.val v.isLt
  obtain ⟨s6, _, r6, deg6, frame6, tin6, one6, zero6, _, _⟩ :=
    run_countIndeg input (rawHead H) raw.heads (by omega)
      (by have := raw.cap_ge; unfold rawInputCap at this; omega)
      (by unfold rawWorkCap at workRoom; unfold indegBase csrArenaWords; omega)
      (Phase.initial s5) rfl ptr5 cnt5 head5 tin5 one5 zeroes5
  have inc6 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s6.data :=
    incomingAt_of_agree inc5 (fun j hj => frame6 j (Or.inl (by
      unfold indegBase csrArenaWords; unfold Arena.payload at hj; change j < 0 + 5 * K + 1 + (n + m) at hj; omega)))
  have hOrderFit : orderBase n m + n ≤ workCap := by
    unfold rawWorkCap at workRoom
    unfold orderBase stampsBase indegBase csrArenaWords
    omega
  obtain ⟨s7, r7, ptr7, clk7, cnt7, tin7, off7, zero7, one7, d7⟩ :=
    run_seedQueueSetup input raw workRoom s6 tin6 (congrArg Fin.val zero6 |>.trans zero5) one6
  have inc7 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s7.data := by
    simpa only [d7] using inc6
  have deg7 : ∀ v : Fin n, (s7.data[indegBase n m + v.val]?).map Fin.val =
      some (countOccPrefix (rawHead H) v m) := by
    intro v; rw [d7]; exact deg6 v
  obtain ⟨s8, _, w8, q8, w8Le, r8, q8nd, q8len, clk8, q8mem, q8zero, frame8, tin8, off8, zero8, one8, _, _⟩ :=
    run_seedQueue input (fun v => countOccPrefix (rawHead H) v m) hOrderFit
      (Phase.initial s7) rfl ptr7 clk7 cnt7 tin7 off7 zero7 one7 deg7
  have inc8 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s8.data :=
    incomingAt_of_agree inc7 (fun j hj => frame8 j (Or.inl (by
      unfold orderBase stampsBase indegBase csrArenaWords; unfold Arena.payload at hj
      change j < 0 + 5 * K + 1 + (n + m) at hj; omega)))
  have deg8 : ∀ v : Fin n, (s8.data[indegBase n m + v.val]?).map Fin.val =
      some (countOccPrefix (rawHead H) v m) := by
    intro v
    have := v.isLt
    rw [frame8 _ (Or.inl (by change indegBase n m + v.val < orderBase n m; unfold orderBase stampsBase; omega))]
    exact deg7 v
  obtain ⟨s9, r9, ptr9, sb9, cmd9, clk9, tin9, tout9, off9, cb9, zero9, one9, d9⟩ :=
    run_kahnBfsSetup input raw workRoom hbits s8 zero8 one8 (clk8 ▸ q8len) tin8 off8
  have inc9 : IncomingAt aOut (fun e => (rawOccurrence H e).1) s9.data := by
    simpa only [d9] using inc8
  have q9mem : ∀ i : Fin q8.length, (s9.data[orderBase n m + i.val]?).map Fin.val =
      some (q8[i.val]'i.isLt).val := by
    intro i; rw [d9]; exact q8mem i
  have deg9 : ∀ v : Fin n, (s9.data[indegBase n m + v.val]?).map Fin.val =
      some (countOccPrefix (rawHead H) v m) := by
    intro v; rw [d9]; exact deg8 v
  obtain ⟨s10, _, w10, order, size_order, w10Le, r10, nodup10, covers10, topo10, orderMem10,
      clk10, off10, zero10, one10, _, _, _⟩ :=
    run_kahnBfs input raw acyc workRoom aOut rfl rfl (Phase.initial s9) inc9 rfl
      ptr9 sb9 cmd9 tin9 tout9 off9 cb9 zero9 one9 q8 q8nd (clk9.trans clk8) q9mem deg9 q8zero
  have hRankFitLt : ranksBase n m + n < workCap := by
    unfold rawWorkCap at workRoom
    unfold ranksBase orderBase stampsBase indegBase csrArenaWords
    omega
  obtain ⟨s11, r11, ptr11, cnt11, off11, cb11, _, one11, d11⟩ :=
    run_rankScatterSetup input hRankFitLt s10 clk10 off10 zero10 one10
  have orderMem11 : ∀ i : Fin n, (s11.data[orderBase n m + i.val]?).map Fin.val =
      some (orderedVertexAt order size_order i).val := by
    intro i; rw [d11]; exact orderMem10 i
  obtain ⟨s12, _, r12, rkAt, rkInc, rkArc, ranksMem12, frame12, _, _⟩ :=
    run_rankScatter input order size_order nodup10 covers10 topo10 (Nat.le_of_lt hRankFitLt)
      (Phase.initial s11) rfl ptr11 cnt11 off11 cb11 one11 orderMem11
  have orderMem12 : ∀ i : Fin n, (s12.data[orderBase n m + i.val]?).map Fin.val =
      some (orderedVertexAt order size_order i).val := by
    intro i
    have := i.isLt
    rw [frame12 _ (Or.inl (by change orderBase n m + i.val < ranksBase n m; unfold ranksBase; omega))]
    exact orderMem11 i
  have hPhases : PhasesRun input (kahnStagePhases (hi := hi) (hw := hw) hbits) s₀ (Phase.initial s12)
      (16 + (w2 + (12 + ((5 * n + 2) + (5 + ((10 * m + 2) + (6 + (w8 + (13 + (w10 + (5 + ((7 * n + 2) + 1)))))))))))) :=
    .cons r1 (.cons r2 (.cons r3 (.cons r4 (.cons r5 (.cons r6 (.cons r7 (.cons r8
      (.cons r9 (.cons r10 (.cons r11 (.cons r12 .nil)))))))))))
  refine ⟨Phase.initial s12, _, order, size_order, readRank (orderRanks order nodup10), ?_, hPhases,
    nodup10, covers10, topo10, rkAt, rkInc, rkArc, orderMem12, ranksMem12⟩
  omega

/-- Execute Stage 1A as a single linked ROM `Phase` (`kahnStagePhase`), returning the
topological order, inverse ranks, and execution trace with exact peak footprint. -/
theorem run_kahn_stage (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (acyc : H.IsAcyclic)
    (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s₀ : State L) :
    let n := H.vertexCount
    let m := H.arcCount
    let hbits := bits_ge_four_of_raw raw
    ∃ t trace work, ∃ order : Array (Vertex H), ∃ size_order : order.size = n,
      ∃ rank : Vertex H → Nat,
      work ≤ 84 * n + 79 * m + 150 ∧
      run (kahnStagePhase (hi := hi) (hw := hw) hbits).code input work (Phase.initial s₀) =
        some ⟨t, work⟩ ∧
      order.toList.Nodup ∧
      (∀ v : Vertex H, ∃ i : Fin n, orderedVertexAt order size_order i = v) ∧
      IsTopologicalOrder order size_order ∧
      (∀ i : Fin n, rank (orderedVertexAt order size_order i) = i.val) ∧
      (∀ i j : Fin n, i.val < j.val →
        rank (orderedVertexAt order size_order i) <
          rank (orderedVertexAt order size_order j)) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) ∧
      (∀ i : Fin n,
        (t.data[orderBase n m + i.val]?).map Fin.val =
          some (orderedVertexAt order size_order i).val) ∧
      (∀ v : Vertex H, (t.data[ranksBase n m + v.val]?).map Fin.val = some (rank v)) ∧
      SuccessfulTrace (kahnStagePhase (hi := hi) (hw := hw) hbits).code input
        (Phase.initial s₀) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  intro n m hbits
  obtain ⟨mState, work, order, size_order, rank, hWork, hPhases, nodup, covers, topo,
      rkAt, rkInc, rkArc, orderMem, ranksMem⟩ :=
    run_kahn_stage_phases input raw acyc workRoom s₀
  obtain ⟨t, trace, _, dataEq, exec, sTrace, peak⟩ := run_pipeline hPhases
  rw [← kahnStagePhase_code] at exec sTrace
  refine ⟨t, trace, work, order, size_order, rank, hWork, exec, nodup, covers, topo,
    rkAt, rkInc, rkArc, ?_, ?_, sTrace, peak⟩
  · intro i; rw [dataEq]; exact orderMem i
  · intro v; rw [dataEq]; exact ranksMem v

end KahnStage

theorem rawIncomingPhase_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) :
    (rawIncomingPhase (bits := bits) (hi := h₁) (hw := k₁)).code =
      (rawIncomingPhase (bits := bits) (hi := h₂) (hw := k₂)).code ∧
    (rawIncomingPhase (bits := bits) (hi := h₁) (hw := k₁)).haltPC =
      (rawIncomingPhase (bits := bits) (hi := h₂) (hw := k₂)).haltPC :=
  ⟨rfl, rfl⟩

private theorem kahnPhaseEq_link {bits c₁ d₁ c₂ d₂ : Nat}
    {h₁ : c₁ ≤ 2 ^ bits} {k₁ : d₁ ≤ 2 ^ bits}
    {h₂ : c₂ ≤ 2 ^ bits} {k₂ : d₂ ≤ 2 ^ bits}
    {p₁ q₁ : Phase (layout bits c₁ d₁ h₁ k₁)}
    {p₂ q₂ : Phase (layout bits c₂ d₂ h₂ k₂)}
    (hp : p₁.code = p₂.code ∧ p₁.haltPC = p₂.haltPC)
    (hq : q₁.code = q₂.code ∧ q₁.haltPC = q₂.haltPC) :
    (p₁.link q₁).code = (p₂.link q₂).code ∧
    (p₁.link q₁).haltPC = (p₂.link q₂).haltPC := by
  refine ⟨?_, ?_⟩
  · simp only [Phase.link, FixedROM.join, hp.1, hp.2, hq.1]
  · simp only [Phase.link, hp.1, hq.2]

theorem kahnStagePhase_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits)
    (hb₁ : 4 ≤ 2 ^ bits) (hb₂ : 4 ≤ 2 ^ bits) :
    (kahnStagePhase (bits := bits) (hi := h₁) (hw := k₁) hb₁).code =
      (kahnStagePhase (bits := bits) (hi := h₂) (hw := k₂) hb₂).code ∧
    (kahnStagePhase (bits := bits) (hi := h₁) (hw := k₁) hb₁).haltPC =
      (kahnStagePhase (bits := bits) (hi := h₂) (hw := k₂) hb₂).haltPC := by
  have hEq : hb₁ = hb₂ := Subsingleton.elim hb₁ hb₂
  subst hEq
  unfold kahnStagePhase kahnStagePhases pipelinePhase
  repeat' (refine kahnPhaseEq_link ?_ ?_)
  all_goals
    first
    | exact rawIncomingPhase_cap_indep h₁ k₁ h₂ k₂
    | exact ⟨rfl, rfl⟩

end PaperB.RamForestProgram.RawBuild
