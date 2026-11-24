module

public import PaperB.RamForestParentRows

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram
open PaperB.Machine (Word)
open PaperB.WordOps (ltb)

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- Registers available to either parent scan body. The wrapper owns the
vertex cursor and carries the tree root and all bank bases. -/
def parentScratch : List (Fin 15) :=
  [registers.remain, registers.childBase, registers.value, registers.tmp, clk]

private def scanPrologue (after : Nat) : List (Instr bits 15) :=
  [.branchLt registers.ptr count 1 (after + 2),
    .branchLt registers.ptr cmd 2 3, .goto 4, .branchLt cmd registers.ptr 4 after]

private def scanEpilogue : List (Instr bits 15) :=
  [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]

def parentScanCode (body : List (Instr bits 15)) : Program L :=
  (scanPrologue (4 + body.length) ++ (body ++ scanEpilogue)).toArray

theorem parentBody_placed (body : List (Instr bits 15)) :
    Placed (parentScanCode (hi := hi) (hw := hw) body) 4 body :=
  @placed_link bits L (scanPrologue (4 + body.length)) body scanEpilogue

theorem parentScan_size (body : List (Instr bits 15)) :
    (parentScanCode (hi := hi) (hw := hw) body).size = 4 + body.length + 3 := by
  simp [parentScanCode, scanPrologue, scanEpilogue, Nat.add_assoc]
  omega

private theorem epilogueFetch (body : List (Instr bits 15)) (i : Nat) :
    (parentScanCode (hi := hi) (hw := hw) body)[4 + body.length + i]? =
      (scanEpilogue (bits := bits))[i]? := by
  unfold parentScanCode
  rw [List.getElem?_toArray, List.getElem?_append_right (by
    change 4 ≤ 4 + body.length + i
    omega)]
  change (body ++ scanEpilogue)[4 + body.length + i - 4]? = _
  rw [show 4 + body.length + i - 4 = body.length + i by omega,
    List.getElem?_append_right (by omega), show body.length + i - body.length = i by omega]

structure ParentCursor (a : Arena bits workCap n) (root : Fin n) (i : Nat)
    (s : State L) : Prop where
  ctrl : Control a s
  rootVal : (reg s cmd).val = root.val
  ptrVal : (reg s registers.ptr).val = i

private theorem control_unchanged {a : Arena bits workCap n} {s t : State L}
    (ctrl : Control a s)
    (keep : ∀ r : Fin 15, r ≠ registers.ptr → r ∉ parentScratch → reg t r = reg s r) :
    Control a t :=
  ⟨(congrArg Fin.val (keep count (by decide +revert) (by decide +revert))).trans ctrl.count_eq,
    (congrArg Fin.val (keep registers.one (by decide +revert) (by decide +revert))).trans ctrl.one,
    (congrArg Fin.val (keep registers.zero (by decide +revert) (by decide +revert))).trans ctrl.zero,
    (congrArg Fin.val (keep registers.stackBase (by decide +revert) (by decide +revert))).trans ctrl.stackBase_eq,
    (congrArg Fin.val (keep tinBase (by decide +revert) (by decide +revert))).trans ctrl.tin_eq,
    (congrArg Fin.val (keep toutBase (by decide +revert) (by decide +revert))).trans ctrl.tout_eq,
    (congrArg Fin.val (keep offsetBase (by decide +revert) (by decide +revert))).trans ctrl.offset_eq,
    (congrArg Fin.val (keep childrenBase (by decide +revert) (by decide +revert))).trans ctrl.child_eq⟩

theorem ParentCursor.unchanged {a : Arena bits workCap n} {root : Fin n} {i : Nat}
    {s t : State L} (h : ParentCursor a root i s)
    (frame : ∀ r : Fin 15, r ∉ parentScratch → reg t r = reg s r) :
    ParentCursor a root i t :=
  ⟨control_unchanged h.ctrl (fun r _ hr => frame r hr),
    (congrArg Fin.val (frame cmd (by decide +revert))).trans h.rootVal,
    (congrArg Fin.val (frame registers.ptr (by decide +revert))).trans h.ptrVal⟩

/-- Condition used to verify a histogram or scatter body. The root branch
has no memory effects; the nonroot body is the placed straight-line code. -/
def ParentBodySpec (input : Input L) (body : List (Instr bits 15))
    (a : Arena bits workCap n) (root : Fin n)
    (inv : Nat → Array (Word bits) → Prop) : Prop :=
  ∀ (u : Fin n), u ≠ root → ∀ s : State L,
    s.pc = 4 → ParentCursor a root u.val s → inv u.val s.data →
    ∃ t, Steps (parentScanCode body) input body.length s t ∧ t.pc = 4 + body.length ∧
      ParentCursor a root u.val t ∧ inv (u.val + 1) t.data

private def scanCost (root : Fin n) (bodyLength i : Nat) : Nat :=
  if i = root.val then 5 else 5 + bodyLength

private theorem scan_step (input : Input L) (body : List (Instr bits 15))
    {a : Arena bits workCap n} {root : Fin n} {inv : Nat → Array (Word bits) → Prop}
    (spec : ParentBodySpec input body a root inv)
    (skip : ∀ data, inv root.val data → inv (root.val + 1) data)
    (i : Nat) (below : i < n) :
    BlockSpec (parentScanCode body) input (scanCost root body.length i)
      (fun s => s.pc = 0 ∧ ParentCursor a root i s ∧ inv i s.data)
      (fun s => s.pc = 0 ∧ ParentCursor a root (i + 1) s ∧ inv (i + 1) s.data) := by
  intro s ⟨pc, cursor, old⟩
  let code : Program L := parentScanCode body
  let after := 4 + body.length
  have size : code.size = after + 3 := parentScan_size body
  have room := a.wordFits
  have cmp : ltb (reg s registers.ptr) (reg s count) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [cursor.ptrVal, cursor.ctrl.count_eq]; exact below)
  let x : State L := {s with pc := 1}
  have guardFetch : code[s.pc]? = some (.branchLt registers.ptr count 1 (after + 2)) := by
    rw [pc]; rfl
  have guard : step code input s = some (.next x) := by
    simpa only [x, cmp, ite_true] using
      step_branchLt_at (input := input) guardFetch (by simp only [cmp, ite_true]; omega)
  have xcursor : ParentCursor a root i x := cursor.unchanged (fun _ _ => rfl)
  let selected : Nat := if i = root.val then after else 4
  have select : Steps code input 2 x {s with pc := selected} := by
    by_cases lt : i < root.val
    · have left : ltb (reg x registers.ptr) (reg x cmd) = true :=
        (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [xcursor.ptrVal, xcursor.rootVal]; exact lt)
      have at1 : code[x.pc]? = some (.branchLt registers.ptr cmd 2 3) := rfl
      let y : State L := {s with pc := 2}
      have xy : step code input x = some (.next y) := by
        simpa only [x, y, left, ite_true] using
          step_branchLt_at (input := input) at1 (by simp only [left, ite_true]; omega)
      have at2 : code[y.pc]? = some (.goto 4) := rfl
      have endPC : selected = 4 := ite_eq_right (by omega)
      have ys := step_goto_at (input := input) at2 (by omega)
      rw [endPC]
      exact .cons xy (.cons ys (.zero _))
    · have left : ltb (reg x registers.ptr) (reg x cmd) = false := by
        cases h : ltb (reg x registers.ptr) (reg x cmd) with
        | false => rfl
        | true =>
          have e := (PaperB.WordOps.ltb_eq_true _ _).mp h
          rw [xcursor.ptrVal, xcursor.rootVal] at e
          exact (lt e).elim
      have at1 : code[x.pc]? = some (.branchLt registers.ptr cmd 2 3) := rfl
      let y : State L := {s with pc := 3}
      have xy : step code input x = some (.next y) := by
        simpa only [x, y, left, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) at1 (by simp only [left, Bool.false_eq_true, ite_false]; omega)
      have at3 : code[y.pc]? = some (.branchLt cmd registers.ptr 4 after) := rfl
      have ycursor : ParentCursor a root i y := cursor.unchanged (fun _ _ => rfl)
      have targetEq : (if ltb (reg y cmd) (reg y registers.ptr) then 4 else after) = selected := by
        by_cases eq : i = root.val
        · have no : ltb (reg y cmd) (reg y registers.ptr) = false := by
            cases h : ltb (reg y cmd) (reg y registers.ptr) with
            | false => rfl
            | true =>
              have e := (PaperB.WordOps.ltb_eq_true _ _).mp h
              rw [ycursor.rootVal, ycursor.ptrVal] at e
              omega
          simp [selected, eq, no]
        · have yes : ltb (reg y cmd) (reg y registers.ptr) = true :=
            (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [ycursor.rootVal, ycursor.ptrVal]; omega)
          simp [selected, eq, yes]
      have yz := step_branchLt_at (input := input) at3 (by rw [targetEq]; dsimp [selected]; split <;> omega)
      rw [targetEq] at yz
      exact .cons xy (.cons yz (.zero _))
  have work : ∃ t, Steps code input (if i = root.val then 0 else body.length)
      {s with pc := selected} t ∧ t.pc = after ∧ ParentCursor a root i t ∧ inv (i + 1) t.data := by
    by_cases eq : i = root.val
    · rw [ite_eq_left eq]
      exact ⟨_, .zero _, ite_eq_left eq, cursor.unchanged (fun _ _ => rfl), by
        rw [eq] at old ⊢
        exact skip _ old⟩
    · rw [ite_eq_right eq]
      have endPC : selected = 4 := ite_eq_right eq
      rw [endPC]
      let u : Fin n := ⟨i, below⟩
      have other : u ≠ root := fun e => eq (congrArg Fin.val e)
      exact spec u other _ rfl (cursor.unchanged (fun _ _ => rfl)) old
  obtain ⟨t, steps, tpc, atLoop, next⟩ := work
  have endFetch : code[t.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [tpc]
    exact epilogueFetch body 0
  obtain ⟨q, tq, qpc, qPtr, qRegs, qData⟩ :=
    step_add_at (input := input) endFetch (by omega)
  have qFetch : code[q.pc]? = some (.goto 0) := by
    rw [qpc, tpc]
    exact epilogueFetch body 1
  let output : State L := {q with pc := 0}
  have qs : step code input q = some (.next output) :=
    step_goto_at qFetch (by omega)
  have safe : (reg t registers.ptr).val + (reg t registers.one).val < 2 ^ bits := by
    rw [atLoop.ptrVal, atLoop.ctrl.one]; omega
  have finalPtr : (reg output registers.ptr).val = i + 1 := by
    change (reg q registers.ptr).val = _
    rw [qPtr, PaperB.WordOps.add_no_wrap _ _ safe, atLoop.ptrVal, atLoop.ctrl.one]
  have trace := (Steps.cons guard select).append (steps.append (.cons tq (.cons qs (.zero _))))
  have length : 3 + ((if i = root.val then 0 else body.length) + 2) = scanCost root body.length i := by
    unfold scanCost
    split <;> omega
  refine ⟨output, length ▸ trace, rfl,
    ⟨control_unchanged atLoop.ctrl (fun r hp _ => qRegs r hp), ?_, finalPtr⟩, ?_⟩
  · change (reg q cmd).val = root.val
    rw [qRegs cmd (show cmd ≠ registers.ptr by decide), atLoop.rootVal]
  · change inv (i + 1) q.data
    rwa [qData]

private theorem scanCost_bound (root : Fin n) (len m : Nat) :
    iterationCost (scanCost root len) m ≤ (5 + len) * m := by
  induction m with
  | zero => simp [iterationCost]
  | succ m ih =>
    simp only [iterationCost, Nat.mul_succ]
    have one : scanCost root len m ≤ 5 + len := by unfold scanCost; split <;> omega
    omega

/-- Scan every vertex, skipping the body only at the root. The budget
includes both comparison paths and the final guard and halt. -/
theorem run_parent_scan (input : Input L) (body : List (Instr bits 15))
    {a : Arena bits workCap n} {root : Fin n} {inv : Nat → Array (Word bits) → Prop}
    (spec : ParentBodySpec input body a root inv)
    (skip : ∀ data, inv root.val data → inv (root.val + 1) data)
    (s : State L) (pc : s.pc = 0) (cursor : ParentCursor a root 0 s) (initial : inv 0 s.data) :
    ∃ t trace work, work ≤ (5 + body.length) * n + 2 ∧
      run (parentScanCode body) input work s = some ⟨t, work⟩ ∧
      ParentCursor a root n t ∧ inv n t.data ∧
      SuccessfulTrace (parentScanCode body) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let code : Program L := parentScanCode body
  let after := 4 + body.length
  have size : code.size = after + 3 := parentScan_size body
  obtain ⟨t, steps, tpc, tc, done⟩ :=
    loop_steps (code := code) (input := input) n (scanCost root body.length)
      (fun i q => q.pc = 0 ∧ ParentCursor a root i q ∧ inv i q.data)
      (fun i below => scan_step input body spec skip i below) s ⟨pc, cursor, initial⟩
  have cmp : ltb (reg t registers.ptr) (reg t count) = false := by
    cases h : ltb (reg t registers.ptr) (reg t count) with
    | false => rfl
    | true =>
      have e := (PaperB.WordOps.ltb_eq_true _ _).mp h
      rw [tc.ptrVal, tc.ctrl.count_eq] at e
      omega
  have fetch : code[t.pc]? = some (.branchLt registers.ptr count 1 (after + 2)) := by
    rw [tpc]; rfl
  let u : State L := {t with pc := after + 2}
  have tu : step code input t = some (.next u) := by
    simpa only [u, cmp, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) fetch (by simp only [cmp, Bool.false_eq_true, ite_false]; omega)
  have last : code[u.pc]? = some .halt := epilogueFetch body 2
  have out := (steps.append (.cons tu (.zero _))).halts (step_halt_at last)
  obtain ⟨trace, success⟩ := run_has_successfulTrace out
  have bound := scanCost_bound root body.length n
  exact ⟨u, trace, _, by omega, out, tc.unchanged (fun _ _ => rfl), done, success,
    success.peak_eq⟩

end PaperB.RamForestProgram.Finish
