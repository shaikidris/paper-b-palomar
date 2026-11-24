module

public import PaperB.RamForestParentScan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram
open PaperB.Machine (Word)
open PaperB.WordOps (ltb)
open PaperB.RamForestStack (StackAt pushCode push_steps)

variable {bits n inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def zeroBody : List (Instr bits 15) :=
  pushCode registers.ptr tinBase registers.zero registers.one registers.tmp

/-- Clear the degree bank while retaining parent words in the stack bank. -/
def zeroDegreeProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  let first : List (Instr bits 15) := [.branchLt registers.ptr count 1 5]
  let last : List (Instr bits 15) := [.goto 0, .halt]
  (first ++ (zeroBody ++ last)).toArray

private theorem zeroAt {data : Array (Word bits)} {base i : Nat} {w : Word bits} :
    StackAt data base (List.replicate i w) ↔ ∀ j < i, data[base + j]? = some w := by
  induction i with
  | zero => simp [StackAt]
  | succ i ih =>
    simp only [List.replicate_succ, StackAt, List.length_replicate, ih]
    constructor
    · rintro ⟨atLast, before⟩ j hj
      by_cases eq : i = j
      · subst j; exact atLast
      · exact before j (by omega)
    · intro h
      exact ⟨h i (by omega), fun j hj => h j (by omega)⟩

private structure Clearing (a : Arena bits workCap n) (root : Fin n) (orig : State L)
    (i : Nat) (s : State L) : Prop where
  pc : s.pc = 0
  cursor : ParentCursor a root i s
  written : StackAt s.data a.tin (List.replicate i (reg s registers.zero))
  outside : ∀ j, (j < a.tin ∨ a.tin + i ≤ j) → s.data[j]? = orig.data[j]?

private theorem clearDegree (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {orig : State L} {i : Nat} (more : i < n) :
    BlockSpec (zeroDegreeProgram hi hw) input 5 (Clearing a root orig i)
      (Clearing a root orig (i + 1)) := by
  intro s h
  let code : Program L := zeroDegreeProgram hi hw
  let u : State L := {s with pc := 1}
  have at0 : code[s.pc]? = some (.branchLt registers.ptr count 1 5) := by rw [h.pc]; rfl
  have cmp : ltb (reg s registers.ptr) (reg s count) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [h.cursor.ptrVal, h.cursor.ctrl.count_eq]; exact more)
  have su : step code input s = some (.next u) := by
    simpa only [u, cmp, ite_true] using
      step_branchLt_at (input := input) at0 (by rw [cmp]; exact (show 1 < 6 by decide))
  have place : Placed code 1 (zeroBody (bits := bits)) :=
    @placed_link bits L [.branchLt registers.ptr count 1 5] zeroBody [.goto 0, .halt]
  have room := a.room
  have wide := a.wordFits
  have fit : (reg u tinBase).val + (List.replicate i (reg s registers.zero)).length < workCap := by
    change (reg s tinBase).val + _ < workCap
    rw [h.cursor.ctrl.tin_eq, List.length_replicate]
    unfold Arena.tin
    omega
  have stack : StackAt u.data (reg u tinBase).val (List.replicate i (reg s registers.zero)) := by
    change StackAt s.data (reg s tinBase).val _
    rw [h.cursor.ctrl.tin_eq]
    exact h.written
  obtain ⟨v, uv, vpc, vp, vs, vr, vm⟩ := push_steps (input := input) (s := u)
    place rfl (show 4 < 6 by decide)
    (by change (reg s registers.ptr).val = _; rw [h.cursor.ptrVal, List.length_replicate])
    h.cursor.ctrl.one fit (by rw [List.length_replicate]; omega)
    (show registers.zero ≠ registers.tmp by decide)
    (show registers.ptr ≠ registers.tmp by decide)
    (show registers.one ≠ registers.tmp by decide) stack
  have back : code[v.pc]? = some (.goto 0) := by rw [vpc]; rfl
  let t : State L := {v with pc := 0}
  have vt : step code input v = some (.next t) :=
    step_goto_at back (show 0 < 6 by decide)
  have keep (r : Fin 15) (notPtr : r ≠ registers.ptr) (notTmp : r ≠ registers.tmp) :
      reg t r = reg s r := vr r notPtr notTmp
  have ctrl : Control a t := by
    have move (r : Fin 15) (np : r ≠ registers.ptr) (nt : r ≠ registers.tmp) :=
      congrArg Fin.val (keep r np nt)
    exact ⟨(move count (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.count_eq,
      (move registers.one (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.one,
      (move registers.zero (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.zero,
      (move registers.stackBase (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.stackBase_eq,
      (move tinBase (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.tin_eq,
      (move toutBase (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.tout_eq,
      (move offsetBase (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.offset_eq,
      (move childrenBase (by decide +revert) (by decide +revert)).trans h.cursor.ctrl.child_eq⟩
  have rootEq := (congrArg Fin.val (keep cmd (by decide +revert) (by decide +revert))).trans
    h.cursor.rootVal
  have ptr : (reg t registers.ptr).val = i + 1 := by
    change (reg v registers.ptr).val = _
    simpa only [List.length_replicate] using vp
  have z : reg t registers.zero = reg s registers.zero :=
    keep _ (show registers.zero ≠ registers.ptr by decide) (show registers.zero ≠ registers.tmp by decide)
  have base : (reg u tinBase).val = a.tin := h.cursor.ctrl.tin_eq
  refine ⟨t, (Steps.cons su uv).append (.cons vt (.zero _)), rfl, ⟨ctrl, rootEq, ptr⟩, ?_, ?_⟩
  · have sameZero : reg u registers.zero = reg s registers.zero := rfl
    rw [base, sameZero, ← List.replicate_succ] at vs
    rw [z]
    exact vs
  · intro j hj
    rw [base, List.length_replicate] at vm
    exact (vm j (by omega)).trans (h.outside j (by omega))

private theorem fiveIterations (k : Nat) : iterationCost (fun _ => 5) k = 5 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterationCost, ih, Nat.mul_succ]

/-- No zero-filled scratch bank is assumed. The zero fill charges each
store and every guard, advance, back edge, and halt. -/
theorem run_zero_degrees (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} (s : State L) (pc : s.pc = 0) (cursor : ParentCursor a root 0 s) :
    ∃ t trace,
      run (zeroDegreeProgram hi hw) input (5 * n + 2) s = some ⟨t, 5 * n + 2⟩ ∧
      ParentCursor a root n t ∧
      (∀ p : Fin n, (t.data[a.tin + p.val]?).map Fin.val = some 0) ∧
      (∀ j, (j < a.tin ∨ a.tin + n ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (zeroDegreeProgram hi hw) input s trace ⟨t, 5 * n + 2⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have start : Clearing a root s 0 s := ⟨pc, cursor, trivial, fun _ _ => rfl⟩
  obtain ⟨u, trace, h⟩ := loop_steps (code := zeroDegreeProgram hi hw) (input := input)
    n (fun _ => 5) (Clearing a root s) (fun _ below => clearDegree input below) s start
  rw [fiveIterations] at trace
  have no : ltb (reg u registers.ptr) (reg u count) = false := by
    cases hx : ltb (reg u registers.ptr) (reg u count) with
    | false => rfl
    | true =>
      have conflict := (PaperB.WordOps.ltb_eq_true _ _).mp hx
      rw [h.cursor.ptrVal, h.cursor.ctrl.count_eq] at conflict
      omega
  let t : State L := {u with pc := 5}
  have fetch : (zeroDegreeProgram hi hw)[u.pc]? = some (.branchLt registers.ptr count 1 5) := by
    rw [h.pc]; rfl
  have next : step (zeroDegreeProgram hi hw) input u = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) fetch (by rw [no]; exact (show 5 < 6 by decide))
  have exec := (trace.append (.cons next (.zero t))).halts (step_halt_at rfl)
  obtain ⟨states, success⟩ := run_has_successfulTrace exec
  refine ⟨t, states, exec, h.cursor.unchanged (fun _ _ => rfl), ?_, h.outside,
    success, success.peak_eq⟩
  intro p
  change (u.data[a.tin + p.val]?).map Fin.val = some 0
  rw [zeroAt.mp h.written p.val p.isLt, Option.map_some, h.cursor.ctrl.zero]

/-- The preparation kernels share one calling convention. Reset the
cursor and accumulator and compute the seed's two-column length. -/
def prepareParentPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  #[.add registers.ptr registers.zero registers.zero,
    .add clk registers.zero registers.zero, .add registers.remain count count, .halt]

theorem run_prepare_parent_phase (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {i : Nat} (s : State L) (pc : s.pc = 0)
    (cursor : ParentCursor a root i s) :
    ∃ t, run (prepareParentPhase hi hw) input 4 s = some ⟨t, 4⟩ ∧
      ParentCursor a root 0 t ∧ (reg t clk).val = 0 ∧
      (reg t registers.remain).val = 2 * n ∧ t.data = s.data := by
  let code := prepareParentPhase hi hw
  have room := a.wordFits
  have fitZero : (reg s registers.zero).val + (reg s registers.zero).val < 2 ^ bits := by
    rw [cursor.ctrl.zero]; omega
  have at0 : code[s.pc]? = some (.add registers.ptr registers.zero registers.zero) := by rw [pc]; rfl
  obtain ⟨u, su, upc, uVal, uRegs, uData⟩ := step_add_at (input := input)
    at0 (by rw [pc]; exact (show 1 < 4 by decide))
  have at1 : code[u.pc]? = some (.add clk registers.zero registers.zero) := by rw [upc, pc]; rfl
  obtain ⟨v, uv, vpc, vVal, vRegs, vData⟩ := step_add_at (input := input)
    at1 (by rw [upc, pc]; exact (show 2 < 4 by decide))
  have at2 : code[v.pc]? = some (.add registers.remain count count) := by
    rw [vpc, upc, pc]; rfl
  obtain ⟨t, vt, tpc, tVal, tRegs, tData⟩ := step_add_at (input := input)
    at2 (by rw [vpc, upc, pc]; exact (show 3 < 4 by decide))
  have at3 : code[t.pc]? = some .halt := by rw [tpc, vpc, upc, pc]; rfl
  have trace : Steps code input 3 s t := .cons su (.cons uv (.cons vt (.zero t)))
  have common (r : Fin 15) (hp : r ≠ registers.ptr) (hc : r ≠ clk)
      (hr : r ≠ registers.remain) : reg t r = reg s r :=
    (tRegs r hr).trans ((vRegs r hc).trans (uRegs r hp))
  have inherits (r : Fin 15) (hp : r ≠ registers.ptr) (hc : r ≠ clk)
      (hr : r ≠ registers.remain) : (reg t r).val = (reg s r).val :=
    congrArg Fin.val (common r hp hc hr)
  have ctrl : Control a t :=
    ⟨(inherits count (by decide) (by decide) (by decide)).trans cursor.ctrl.count_eq,
      (inherits registers.one (by decide) (by decide) (by decide)).trans cursor.ctrl.one,
      (inherits registers.zero (by decide) (by decide) (by decide)).trans cursor.ctrl.zero,
      (inherits registers.stackBase (by decide) (by decide) (by decide)).trans cursor.ctrl.stackBase_eq,
      (inherits tinBase (by decide) (by decide) (by decide)).trans cursor.ctrl.tin_eq,
      (inherits toutBase (by decide) (by decide) (by decide)).trans cursor.ctrl.tout_eq,
      (inherits offsetBase (by decide) (by decide) (by decide)).trans cursor.ctrl.offset_eq,
      (inherits childrenBase (by decide) (by decide) (by decide)).trans cursor.ctrl.child_eq⟩
  have rootEq := (inherits cmd (by decide) (by decide) (by decide)).trans cursor.rootVal
  have ptr : (reg t registers.ptr).val = 0 := by
    rw [tRegs _ (show registers.ptr ≠ registers.remain by decide),
      vRegs _ (show registers.ptr ≠ clk by decide), uVal,
      PaperB.WordOps.add_no_wrap _ _ fitZero, cursor.ctrl.zero]
  have clockZero : (reg t clk).val = 0 := by
    rw [tRegs _ (show clk ≠ registers.remain by decide), vVal,
      uRegs _ (show registers.zero ≠ registers.ptr by decide),
      PaperB.WordOps.add_no_wrap _ _ fitZero, cursor.ctrl.zero]
  have countEq : (reg v count).val = n :=
    (congrArg Fin.val ((vRegs _ (show count ≠ clk by decide)).trans
      (uRegs _ (show count ≠ registers.ptr by decide)))).trans cursor.ctrl.count_eq
  have twoFit : (reg v count).val + (reg v count).val < 2 ^ bits := by rw [countEq]; omega
  refine ⟨t, trace.halts (step_halt_at at3), ⟨ctrl, rootEq, ptr⟩, clockZero, ?_,
    tData.trans (vData.trans uData)⟩
  rw [tVal, PaperB.WordOps.add_no_wrap _ _ twoFit, countEq]
  omega

end PaperB.RamForestProgram.Finish
