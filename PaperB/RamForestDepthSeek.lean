module

public import PaperB.RamForestDepthRead
public import PaperB.RamForestPhaseLink

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.DepthSeek

open PaperB
open PaperB.RamProgram
open PaperB.WordOps (ltb)
open PaperB.Machine (Word)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

structure Records (base : Nat) (F : JumpForest) (data : Array (Word bits)) : Prop where
  valid : ValidJumpForest F
  fit : base + 3 * F.size ≤ data.size
  parent : ∀ u < F.size, (data[base + 3 * u]?).map Fin.val = some (F.parentOf u)
  depth : ∀ u < F.size, (data[base + 1 + 3 * u]?).map Fin.val = some (F.depthOf u)
  jump : ∀ u < F.size, (data[base + 2 + 3 * u]?).map Fin.val = some (F.jumpOf u)

structure Fixed (base target : Nat) (s : State L) : Prop where
  parent : (reg s tinBase).val = base
  depth : (reg s toutBase).val = base + 1
  jump : (reg s offsetBase).val = base + 2
  targetVal : (reg s cmd).val = target
  zero : (reg s registers.zero).val = 0

private theorem Fixed.keep {base target : Nat} {s t : State L} (f : Fixed base target s)
    (move : ∀ r : Fin 15, r ∈ ([tinBase, toutBase, offsetBase, cmd, registers.zero] : List (Fin 15)) →
      reg t r = reg s r) : Fixed base target t :=
  ⟨(congrArg Fin.val (move tinBase (by decide +revert))).trans f.parent,
    (congrArg Fin.val (move toutBase (by decide +revert))).trans f.depth,
    (congrArg Fin.val (move offsetBase (by decide +revert))).trans f.jump,
    (congrArg Fin.val (move cmd (by decide +revert))).trans f.targetVal,
    (congrArg Fin.val (move registers.zero (by decide +revert))).trans f.zero⟩

structure SeekAt (base : Nat) (F : JumpForest) (target u : Nat) (s : State L) : Prop where
  pc : s.pc = 0
  fixed : Fixed base target s
  mem : Records base F s.data
  uFit : u < F.size
  current : (reg s registers.ptr).val = u
  currentDepth : (reg s clk).val = F.depthOf u

private abbrev readParent : List (Instr bits 15) := recordField registers.remain tinBase registers.ptr
private abbrev readJump : List (Instr bits 15) := recordField registers.childBase offsetBase registers.ptr
private abbrev jumpDepth : List (Instr bits 15) :=
  recordField registers.value toutBase registers.childBase
private abbrev parentDepth : List (Instr bits 15) := recordField clk toutBase registers.ptr

/-- Follow the largest admissible jump. Cache the depth of the current
record, including on the parent fallback path. Work memory is read-only. -/
def seekProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  let guard : Instr bits 15 := .branchLt cmd clk 1 23
  let choose : List (Instr bits 15) :=
    [.branchLt registers.value cmd 17 14,
      .add registers.ptr registers.childBase registers.zero,
      .add clk registers.value registers.zero, .goto 0,
      .add registers.ptr registers.remain registers.zero]
  let tail : List (Instr bits 15) := [.goto 0, .halt]
  ([guard] ++ (readParent ++ (readJump ++ (jumpDepth ++ (choose ++ (parentDepth ++ tail)))))).toArray

private theorem placeFour {code : Program L} {pc : Nat} {dst base node : Fin 15}
    (a : code[pc]? = some (.add dst node node)) (b : code[pc + 1]? = some (.add dst dst node))
    (c : code[pc + 2]? = some (.add dst base dst)) (d : code[pc + 3]? = some (.loadData dst dst)) :
    Placed code pc (recordField dst base node) := by
  intro i op h
  cases i with
  | zero => rw [Nat.add_zero]; exact a.trans h
  | succ i =>
    cases i with
    | zero => exact b.trans h
    | succ i =>
      cases i with
      | zero => exact c.trans h
      | succ i =>
        cases i with
        | zero => exact d.trans h
        | succ i => simp [recordField] at h

private theorem copyZero {code : Program L} (input : Input L) {s : State L}
    {dst src : Fin 15}
    (fetch : code[s.pc]? = some (.add dst src registers.zero))
    (next : s.pc + 1 < code.size) (z : (reg s registers.zero).val = 0) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧ t.data = s.data ∧
      (reg t dst).val = (reg s src).val ∧ (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  obtain ⟨t, st, pc, val, keep, data⟩ := step_add_at (input := input) fetch next
  have fit : (reg s src).val + (reg s registers.zero).val < 2 ^ bits := by
    rw [z, Nat.add_zero]
    exact (reg s src).isLt
  exact ⟨t, st, pc, data, by rw [val, PaperB.WordOps.add_no_wrap _ _ fit, z, Nat.add_zero], keep⟩

private theorem rankRead (input : Input L) {code : Program L} {entry : Nat}
    {dst base node : Fin 15} {s : State L} {actual : Nat}
    (placed : Placed code entry (recordField dst base node)) (pc : s.pc = entry)
    (cont : entry + 4 < code.size) (kb : base ≠ dst) (kn : node ≠ dst)
    (fits : (reg s base).val + 3 * (reg s node).val < workCap)
    (cell : (s.data[(reg s base).val + 3 * (reg s node).val]?).map Fin.val = some actual) :
    ∃ t, Steps code input 4 s t ∧ t.pc = entry + 4 ∧ t.data = s.data ∧
      (reg t dst).val = actual ∧ (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  obtain ⟨t, step, pc, mem, read, regs⟩ := recordField_steps input placed pc cont kb kn fits
  rw [read, Option.map_some] at cell
  exact ⟨t, step, pc, mem, Option.some.inj cell, regs⟩

private theorem seek_step (input : Input L) {base target u : Nat}
    {F : JumpForest} {s : State L} (atGuard : SeekAt base F target u s)
    (need : target < F.depthOf u) :
    ∃ t cost, cost ≤ 20 ∧ Steps (seekProgram hi hw) input cost s t ∧
      SeekAt base F target (F.stepToDepth u target) t ∧ t.data = s.data := by
  let code : Program L := seekProgram hi hw
  have size : code.size = 24 := rfl
  have room := atGuard.mem.fit
  rw [s.data_size] at room
  change base + 3 * F.size ≤ workCap at room
  have uLt := atGuard.uFit
  let x : State L := {s with pc := 1}
  have gt : ltb (reg s cmd) (reg s clk) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr
      (by rw [atGuard.fixed.targetVal, atGuard.currentDepth]; exact need)
  have guard : code[s.pc]? = some (.branchLt cmd clk 1 23) := by rw [atGuard.pc]; rfl
  have sx : step code input s = some (.next x) := by
    simpa only [x, gt, ite_true] using
      step_branchLt_at (input := input) guard (by simp only [gt, ite_true]; omega)
  have fixx : Fixed base target x := atGuard.fixed.keep (fun _ _ => rfl)
  have xIdx : (reg x registers.ptr).val = u := atGuard.current
  have fitP : (reg x tinBase).val + 3 * (reg x registers.ptr).val < workCap := by
    rw [fixx.parent, xIdx]; omega
  have readP : (x.data[(reg x tinBase).val + 3 * (reg x registers.ptr).val]?).map Fin.val =
      some (F.parentOf u) := by rw [fixx.parent, xIdx]; exact atGuard.mem.parent u uLt
  have partP : Placed code 1 (readParent (bits := bits)) := placeFour rfl rfl rfl rfl
  obtain ⟨y, xy, ypc, ymem, yParent, yr⟩ := rankRead input partP rfl (by omega)
    (show tinBase ≠ registers.remain by decide) (show registers.ptr ≠ registers.remain by decide) fitP readP
  have yFix := fixx.keep (fun r hr => yr r (by intro e; subst r; exact (by decide : registers.remain ∉
    ([tinBase, toutBase, offsetBase, cmd, registers.zero] : List (Fin 15))) hr))
  have yIdx : (reg y registers.ptr).val = u :=
    (congrArg Fin.val (yr _ (show registers.ptr ≠ registers.remain by decide))).trans xIdx
  have fitJ : (reg y offsetBase).val + 3 * (reg y registers.ptr).val < workCap := by
    rw [yFix.jump, yIdx]; omega
  have readJ : (y.data[(reg y offsetBase).val + 3 * (reg y registers.ptr).val]?).map Fin.val =
      some (F.jumpOf u) := by rw [yFix.jump, yIdx, ymem]; exact atGuard.mem.jump u uLt
  have partJ : Placed code 5 (readJump (bits := bits)) := placeFour rfl rfl rfl rfl
  obtain ⟨z, yz, zpc, zmem, zJump, zr⟩ := rankRead input partJ ypc (by omega)
    (show offsetBase ≠ registers.childBase by decide)
    (show registers.ptr ≠ registers.childBase by decide) fitJ readJ
  have zFix := yFix.keep (fun r hr => zr r (by intro e; subst r; exact (by decide : registers.childBase ∉
    ([tinBase, toutBase, offsetBase, cmd, registers.zero] : List (Fin 15))) hr))
  have jumpLt := atGuard.mem.valid.jumpOf_lt_size uLt
  have fitD : (reg z toutBase).val + 3 * (reg z registers.childBase).val < workCap := by
    rw [zFix.depth, zJump]; omega
  have readD : (z.data[(reg z toutBase).val + 3 * (reg z registers.childBase).val]?).map Fin.val =
      some (F.depthOf (F.jumpOf u)) := by
    rw [zFix.depth, zJump, zmem, ymem]
    exact atGuard.mem.depth _ jumpLt
  have partD : Placed code 9 (jumpDepth (bits := bits)) := placeFour rfl rfl rfl rfl
  obtain ⟨w, zw, wpc, wmem, amount, wr⟩ := rankRead input partD zpc (by omega)
    (show toutBase ≠ registers.value by decide)
    (show registers.childBase ≠ registers.value by decide) fitD readD
  have wFix := zFix.keep (fun r hr => wr r (by intro e; subst r; exact (by decide : registers.value ∉
    ([tinBase, toutBase, offsetBase, cmd, registers.zero] : List (Fin 15))) hr))
  have wParent : (reg w registers.remain).val = F.parentOf u := by
    rw [wr _ (show registers.remain ≠ registers.value by decide),
      zr _ (show registers.remain ≠ registers.childBase by decide), yParent]
  have wJump : (reg w registers.childBase).val = F.jumpOf u := by
    rw [wr _ (show registers.childBase ≠ registers.value by decide), zJump]
  have same : w.data = s.data := wmem.trans (zmem.trans ymem)
  have atChoice : code[w.pc]? = some (.branchLt registers.value cmd 17 14) := by rw [wpc]; rfl
  have traveled := (Steps.cons sx xy).append (yz.append zw)
  have chooseLt :
      ltb (reg w registers.value) (reg w cmd) = true ↔ F.depthOf (F.jumpOf u) < target := by
    rw [PaperB.WordOps.ltb_eq_true, amount, wFix.targetVal]
  have parentLt := atGuard.mem.valid.parentOf_lt_size uLt
  have move (r : Fin 15) (hr : r ∈ ([tinBase, toutBase, offsetBase, cmd, registers.zero] : List (Fin 15))) :
      r ≠ registers.ptr ∧ r ≠ clk := by
    exact (by decide : ∀ q : Fin 15, q ∈ ([tinBase, toutBase, offsetBase, cmd, registers.zero] :
      List (Fin 15)) → q ≠ registers.ptr ∧ q ≠ clk) r hr
  by_cases allowed : target ≤ F.depthOf (F.jumpOf u)
  · have test : ltb (reg w registers.value) (reg w cmd) = false := by
      cases h : ltb (reg w registers.value) (reg w cmd) with
      | false => rfl
      | true => have bad := chooseLt.mp h; omega
    let p : State L := {w with pc := 14}
    have wp : step code input w = some (.next p) := by
      simpa only [p, test, Bool.false_eq_true, ite_false] using
        step_branchLt_at (input := input) atChoice (by simp only [test, Bool.false_eq_true, ite_false]; omega)
    have jumpFetch : code[p.pc]? = some (.add registers.ptr registers.childBase registers.zero) := rfl
    obtain ⟨q, pq, qpc, qmem, qNode, qr⟩ := copyZero input jumpFetch (by exact (show 15 < 24 by decide)) wFix.zero
    have depthFetch : code[q.pc]? = some (.add clk registers.value registers.zero) := by rw [qpc]; rfl
    have qZero : (reg q registers.zero).val = 0 :=
      (congrArg Fin.val (qr _ (show registers.zero ≠ registers.ptr by decide))).trans wFix.zero
    obtain ⟨r, qrStep, rpc, rmem, rDepth, rr⟩ := copyZero input depthFetch
      (by rw [qpc]; exact (show 16 < 24 by decide)) qZero
    have loop : code[r.pc]? = some (.goto 0) := by rw [rpc, qpc]; rfl
    let t : State L := {r with pc := 0}
    have rt : step code input r = some (.next t) := step_goto_at loop (by omega)
    have resultMem : t.data = s.data := rmem.trans (qmem.trans same)
    have path := traveled.append (Steps.cons wp (.cons pq (.cons qrStep (.cons rt (.zero t)))))
    have whereTo : F.stepToDepth u target = F.jumpOf u := ite_eq_left allowed
    rw [whereTo]
    refine ⟨t, 17, by decide, path, ⟨rfl,
      wFix.keep (fun reg h => (rr _ (move reg h).2).trans (qr _ (move reg h).1)),
      resultMem.symm ▸ atGuard.mem, jumpLt, ?_, ?_⟩, resultMem⟩
    · change (reg r registers.ptr).val = _
      rw [rr _ (show registers.ptr ≠ clk by decide), qNode]
      exact wJump
    · change (reg r clk).val = _
      rw [rDepth, qr _ (show registers.value ≠ registers.ptr by decide)]
      exact amount
  · have test : ltb (reg w registers.value) (reg w cmd) = true := chooseLt.mpr (by omega)
    let p : State L := {w with pc := 17}
    have wp : step code input w = some (.next p) := by
      simpa only [p, test, ite_true] using
        step_branchLt_at (input := input) atChoice (by simp only [test, ite_true]; omega)
    have parFetch : code[p.pc]? = some (.add registers.ptr registers.remain registers.zero) := rfl
    obtain ⟨q, pq, qpc, qmem, qNode, qr⟩ := copyZero input parFetch
      (by exact (show 18 < 24 by decide)) wFix.zero
    have qFix := wFix.keep (fun reg h => qr _ (move reg h).1)
    have cur : (reg q registers.ptr).val = F.parentOf u := qNode.trans wParent
    have fit : (reg q toutBase).val + 3 * (reg q registers.ptr).val < workCap := by
      rw [qFix.depth, cur]; omega
    have read : (q.data[(reg q toutBase).val + 3 * (reg q registers.ptr).val]?).map Fin.val =
        some (F.depthOf (F.parentOf u)) := by
      rw [qFix.depth, cur, qmem]
      change (w.data[base + 1 + 3 * F.parentOf u]?).map Fin.val = _
      rw [same]
      exact atGuard.mem.depth _ parentLt
    have part : Placed code 18 (parentDepth (bits := bits)) := placeFour rfl rfl rfl rfl
    obtain ⟨r, qrStep, rpc, rmem, rDepth, rr⟩ := rankRead input part qpc (by omega)
      (show toutBase ≠ clk by decide) (show registers.ptr ≠ clk by decide) fit read
    have loop : code[r.pc]? = some (.goto 0) := by rw [rpc]; rfl
    let t : State L := {r with pc := 0}
    have rt : step code input r = some (.next t) := step_goto_at loop (by omega)
    have resultMem : t.data = s.data := rmem.trans (qmem.trans same)
    have path := traveled.append ((Steps.cons wp (.cons pq (.zero q))).append
      (qrStep.append (.cons rt (.zero t))))
    have whereTo : F.stepToDepth u target = F.parentOf u := ite_eq_right allowed
    rw [whereTo]
    exact ⟨t, 20, by decide, path, ⟨rfl, qFix.keep (fun reg h => rr _ (move reg h).2),
      resultMem.symm ▸ atGuard.mem, parentLt,
      (congrArg Fin.val (rr _ (show registers.ptr ≠ clk by decide))).trans cur,
      rDepth⟩, resultMem⟩

/-- Execute exactly the abstract depth traversal with physical record
loads. The bound includes the guard on every iteration, the final
guard and the halt. No move trace is allocated by the program. -/
theorem run_depth_seek (input : Input L) {base target u : Nat}
    {F : JumpForest} (s : State L) (ready : SeekAt base F target u s) :
    ∃ t trace work, work ≤ 20 * (F.traceMoves u target).length + 2 ∧
      run (seekProgram hi hw) input work s = some ⟨t, work⟩ ∧
      (reg t registers.ptr).val = F.ancestorAtDepth u target ∧ t.data = s.data ∧
      SuccessfulTrace (seekProgram hi hw) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have simulate : ∀ depth v, F.depthOf v ≤ depth → ∀ start : State L,
      SeekAt base F target v start →
      ∃ t fuel, fuel ≤ 20 * (F.traceMoves v target).length ∧
        Steps (seekProgram hi hw) input fuel start t ∧
        SeekAt base F target (F.ancestorAtDepth v target) t ∧ t.data = start.data ∧
        F.depthOf (F.ancestorAtDepth v target) ≤ target := by
    intro height
    induction height with
    | zero =>
      intro v bound start h
      have le : F.depthOf v ≤ target := by omega
      rw [ancestorAtDepth_of_ge F le, traceMoves_of_ge F le]
      exact ⟨start, 0, Nat.zero_le _, .zero _, h, rfl, le⟩
    | succ height ih =>
      intro v bound start h
      by_cases need : target < F.depthOf v
      · have valid := h.mem.valid
        obtain ⟨a, work, limit, trace, next, mem⟩ := seek_step input h need
        have small := valid.depth_stepToDepth_lt h.uFit need
        obtain ⟨t, rest, rb, tail, final, state, reached⟩ :=
          ih (F.stepToDepth v target) (by omega) a next
        rw [valid.ancestorAtDepth_of_lt h.uFit need, valid.traceMoves_of_lt h.uFit need,
          List.length_cons]
        exact ⟨t, work + rest, by omega, trace.append tail, final, state.trans mem, reached⟩
      · have le : F.depthOf v ≤ target := by omega
        rw [ancestorAtDepth_of_ge F le, traceMoves_of_ge F le]
        exact ⟨start, 0, Nat.zero_le _, .zero _, h, rfl, le⟩
  obtain ⟨v, fuel, budget, trace, final, same, done⟩ :=
    simulate (F.depthOf u) u (Nat.le_refl _) s ready
  let t : State L := {v with pc := 23}
  have finished : ltb (reg v cmd) (reg v clk) = false := by
    cases h : ltb (reg v cmd) (reg v clk) with
    | false => rfl
    | true =>
      have lt := (PaperB.WordOps.ltb_eq_true _ _).mp h
      rw [final.fixed.targetVal, final.currentDepth] at lt
      omega
  have fetch : (seekProgram hi hw)[v.pc]? = some (.branchLt cmd clk 1 23) := by
    rw [final.pc]; rfl
  have vt : step (seekProgram hi hw) input v = some (.next t) := by
    simpa only [t, finished, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) fetch (by rw [finished]; exact (show 23 < 24 by decide))
  have run := (trace.append (.cons vt (.zero _))).halts (step_halt_at rfl)
  obtain ⟨checked, success⟩ := run_has_successfulTrace run
  exact ⟨t, checked, fuel + 2, by omega, run, final.current, same, success, success.peak_eq⟩

/-- Carry the existing abstract word-layout invariant into actual RAM
cells. The natural-valued view is proof-only. -/
theorem Records.of_jump_layout {R : JumpWordRegion} {F : JumpForest}
    {mem : Array Nat} {data : Array (Word bits)}
    (image : JumpWordLayout R F mem) (exactView : data.map Fin.val = mem) :
    Records (R.baseAddr + 1) F data := by
  have capacity := image.inserted_le
  change F.size - 1 ≤ R.maxNodes at capacity
  have memSize : mem.size = data.size := by
    rw [← exactView, Array.size_map]
  have across : R.endAddr ≤ data.size := by rw [← memSize]; exact image.region_inBounds
  have endBound : R.baseAddr + 1 + 3 * F.size ≤ data.size := by
    unfold JumpWordRegion.endAddr at across
    omega
  have view (i : Nat) (inside : i < data.size) :
      (data[i]?).map Fin.val = some (readWord mem i) := by
    have fit : i < mem.size := by rwa [memSize]
    rw [← Array.getElem?_map, exactView, getElem?_pos mem i fit, readWord_of_lt fit]
  refine ⟨image.valid, endBound, ?_, ?_, ?_⟩
  · intro u hu
    rw [view _ (by omega)]
    have eq := image.slot_parent u hu
    exact congrArg some eq
  · intro u hu
    rw [view _ (by omega)]
    have eq := image.slot_depth u hu
    unfold JumpWordRegion.depthAddr JumpWordRegion.slotAddr at eq
    rw [show R.baseAddr + 1 + 1 + 3 * u = R.baseAddr + 1 + 3 * u + 1 by omega]
    exact congrArg some eq
  · intro u hu
    rw [view _ (by omega)]
    have eq := image.slot_jump u hu
    unfold JumpWordRegion.jumpAddr JumpWordRegion.slotAddr at eq
    rw [show R.baseAddr + 1 + 2 + 3 * u = R.baseAddr + 1 + 3 * u + 2 by omega]
    exact congrArg some eq

/-- The skew-tree move bound transfers to all machine instructions,
including address arithmetic, branches, and the two exit instructions. -/
theorem run_depth_seek_logarithmic (input : Input L) {base target u : Nat}
    {F : JumpForest} (s : State L) (ready : SeekAt base F target u s)
    (nodes exponent : Nat) (fits : F.numInserted ≤ nodes)
    (power : nodes + 2 ≤ 2 ^ exponent) :
    ∃ t trace work, work ≤ 60 * exponent + 2 ∧
      run (seekProgram hi hw) input work s = some ⟨t, work⟩ ∧
      (reg t registers.ptr).val = F.ancestorAtDepth u target ∧ t.data = s.data ∧
      SuccessfulTrace (seekProgram hi hw) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨t, trace, work, small, run, result, state, replay, peak⟩ := run_depth_seek input s ready
  have count := traceMoves_length_le_of_bound ready.mem.valid ready.uFit fits power target
  exact ⟨t, trace, work, by omega, run, result, state, replay, peak⟩

section Standalone

open PaperB.RamProgram.FixedROM

private def preloadCode (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  (parentDepth ++ [Instr.halt]).toArray

private def preloadPhase : Phase L := Phase.ofLast (preloadCode hi hw) 4 rfl rfl rfl

/-- Include the initial depth load so the caller supplies only the starting
node, target depth and the fixed field bases. -/
def depthLookupProgram : Program L :=
  join (preloadPhase (hi := hi) (hw := hw)).code (seekProgram hi hw)
    preloadPhase.haltPC preloadPhase.haltFits

theorem run_depth_lookup (input : Input L) {base target u : Nat}
    {F : JumpForest} (s : State L) (parameters : Fixed base target s)
    (words : Records base F s.data) (uFit : u < F.size)
    (node : (reg s registers.ptr).val = u)
    (nodes exponent : Nat) (fits : F.numInserted ≤ nodes)
    (power : nodes + 2 ≤ 2 ^ exponent) :
    ∃ t trace work, work ≤ 60 * exponent + 7 ∧
      run depthLookupProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      (reg t registers.ptr).val = F.ancestorAtDepth u target ∧ t.data = s.data ∧
      SuccessfulTrace depthLookupProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let start := Phase.initial s
  have layoutBound := words.fit
  rw [s.data_size] at layoutBound
  change base + 3 * F.size ≤ workCap at layoutBound
  have sBase : (reg start toutBase).val = base + 1 := parameters.depth
  have sNode : (reg start registers.ptr).val = u := node
  have bound : (reg start toutBase).val + 3 * (reg start registers.ptr).val < workCap := by
    rw [sBase, sNode]; omega
  have field : (start.data[(reg start toutBase).val + 3 * (reg start registers.ptr).val]?).map
      Fin.val = some (F.depthOf u) := by
    rw [sBase, sNode]
    exact words.depth u uFit
  have placed : Placed (preloadCode hi hw) 0 (parentDepth (bits := bits)) := placeFour rfl rfl rfl rfl
  obtain ⟨v, init, vpc, vmem, depth, vr⟩ := rankRead input placed rfl (show 4 < 5 by decide)
    (show toutBase ≠ clk by decide) (show registers.ptr ≠ clk by decide) bound field
  have stop : step (preloadCode hi hw) input v = some (.halted v) := by
    apply step_halt_at
    rw [vpc]
    rfl
  let next := Phase.initial v
  have sameMem : v.data = s.data := vmem
  have nextMem : Records base F next.data := sameMem.symm ▸ words
  have fixed : Fixed base target next := by
    apply parameters.keep
    intro r hr
    have other : r ≠ clk := by
      intro eq
      subst r
      exact (by decide : clk ∉ ([tinBase, toutBase, offsetBase, cmd, registers.zero] : List (Fin 15))) hr
    exact vr r other
  have vNode : (reg next registers.ptr).val = u :=
    (congrArg Fin.val (vr _ (show registers.ptr ≠ clk by decide))).trans sNode
  have ready : SeekAt base F target u next := ⟨rfl, fixed, nextMem, uFit, vNode, depth⟩
  obtain ⟨w, _, count, cost, seek, result, same, _, _⟩ :=
    run_depth_seek_logarithmic input next ready nodes exponent fits power
  obtain ⟨t, trace, regs, memEq, run, replay, peak⟩ :=
    run_linked_pair preloadPhase (seekProgram hi hw) (show 0 < 24 by decide) (init.halts stop) seek
  have sameResult : (reg t registers.ptr).val = (reg w registers.ptr).val := by
    unfold reg
    cases t
    cases w
    simp only at regs
    subst_vars
    rfl
  exact ⟨t, trace, 5 + count, by omega, run, sameResult.trans result,
    memEq.trans (same.trans sameMem), replay, peak⟩

end Standalone

end PaperB.RamForestProgram.DepthSeek
