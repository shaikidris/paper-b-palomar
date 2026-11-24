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

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def readParent : List (Instr bits 15) :=
  indexedDataRead registers.remain registers.stackBase registers.ptr

private def readDegree : List (Instr bits 15) :=
  indexedDataRead registers.value tinBase registers.remain

private def storeDegree : List (Instr bits 15) :=
  indexedDataWrite registers.tmp tinBase registers.remain registers.value

/-- Read the parent and its counter, increment it, and store it. -/
def histogramBody : List (Instr bits 15) :=
  readParent ++ readDegree ++ [.add registers.value registers.value registers.one] ++ storeDegree

private def HistogramInv (a : Arena bits workCap n) (root : Fin n)
    (parent : Fin n → Fin n) (original : Array (Word bits)) (i : Nat)
    (data : Array (Word bits)) : Prop :=
  ParentAt a parent data ∧
    (∀ p : Fin n, (data[a.tin + p.val]?).map Fin.val = some (visitedRows root parent i p).length) ∧
    (∀ j, (j < a.tin ∨ a.tin + n ≤ j) → data[j]? = original[j]?)

private theorem histogram_skip {a : Arena bits workCap n} {root : Fin n}
    {parent : Fin n → Fin n} {original data : Array (Word bits)}
    (h : HistogramInv a root parent original root.val data) :
    HistogramInv a root parent original (root.val + 1) data := by
  refine ⟨h.1, ?_, h.2.2⟩
  intro p
  rw [visitedRows_succ root parent root p]
  simpa using h.2.1 p

private theorem hist_body (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n} {original : Array (Word bits)} :
    ParentBodySpec input histogramBody a root (HistogramInv a root parent original) := by
  intro u nonroot s pc cursor old
  let code : Program L := parentScanCode (histogramBody (bits := bits))
  have placed : Placed code 4 (histogramBody (bits := bits)) := parentBody_placed _
  have read : Placed code 4 (readParent (bits := bits)) := by
    intro i op h
    cases i with
    | zero => exact placed 0 _ h
    | succ i =>
      cases i with
      | zero => exact placed 1 _ h
      | succ i => simp [readParent, indexedDataRead] at h
  have size : code.size = 14 := parentScan_size histogramBody
  have width := a.wordFits
  have room := a.room
  have user := u.isLt
  have parentLt := (parent u).isLt
  have readFit : (reg s registers.stackBase).val + (reg s registers.ptr).val < workCap := by
    rw [cursor.ctrl.stackBase_eq, cursor.ptrVal]; omega
  obtain ⟨v, sv, vpc, raw, vr, vm⟩ :=
    indexedDataRead_steps (input := input) (s := s) read pc (by omega) readFit
  have pWord : (reg v registers.remain).val = (parent u).val := by
    rw [cursor.ctrl.stackBase_eq, cursor.ptrVal] at raw
    have val := congrArg (Option.map Fin.val) raw
    rw [old.1 u] at val
    exact Option.some.inj val
  have vc : ParentCursor a root u.val v :=
    cursor.unchanged (fun r h => vr r (by intro e; subst r; exact h (by decide +revert)))
  have get : Placed code 6 (readDegree (bits := bits)) := by
    intro i op h
    cases i with
    | zero => exact placed 2 _ h
    | succ i =>
      cases i with
      | zero => exact placed 3 _ h
      | succ i => simp [readDegree, indexedDataRead] at h
  have degreeFit : (reg v tinBase).val + (reg v registers.remain).val < workCap := by
    rw [vc.ctrl.tin_eq, pWord]
    unfold Arena.tin
    omega
  obtain ⟨w, vw, wpc, readOld, wr, wm⟩ :=
    indexedDataRead_steps (input := input) (s := v) get vpc (by omega) degreeFit
  have wVal : (reg w registers.value).val = (visitedRows root parent u.val (parent u)).length := by
    rw [vc.ctrl.tin_eq, pWord, vm] at readOld
    have val := congrArg (Option.map Fin.val) readOld
    rw [old.2.1 (parent u)] at val
    exact Option.some.inj val
  have keepW (r : Fin 15) (hr : r ∉ parentScratch) : reg w r = reg v r := by
    apply wr
    intro e; subst r; exact hr (by decide +revert)
  have wc := vc.unchanged keepW
  have bump : code[w.pc]? = some (.add registers.value registers.value registers.one) := by
    rw [wpc]; exact placed 4 _ rfl
  obtain ⟨x, wx, xpc, xVal, xr, xm⟩ := step_add_at (input := input) bump (by omega)
  have nextFits : (reg w registers.value).val + (reg w registers.one).val < 2 ^ bits := by
    rw [wVal, wc.ctrl.one]
    have length := visitedRows_length_le root parent (parent u) u.val (by omega)
    omega
  have xNext : (reg x registers.value).val = (visitedRows root parent u.val (parent u)).length + 1 := by
    rw [xVal, PaperB.WordOps.add_no_wrap _ _ nextFits, wVal, wc.ctrl.one]
  have keepX (r : Fin 15) (hr : r ∉ parentScratch) : reg x r = reg w r := by
    apply xr
    intro e; subst r; exact hr (by decide +revert)
  have xc := wc.unchanged keepX
  have xParent : (reg x registers.remain).val = (parent u).val := by
    rw [xr _ (show registers.remain ≠ registers.value by decide),
      wr _ (show registers.remain ≠ registers.value by decide), pWord]
  have put : Placed code 9 (storeDegree (bits := bits)) := by
    intro i op h
    cases i with
    | zero => exact placed 5 _ h
    | succ i =>
      cases i with
      | zero => exact placed 6 _ h
      | succ i => simp [storeDegree, indexedDataWrite] at h
  have storeFit : (reg x tinBase).val + (reg x registers.remain).val < workCap := by
    rw [xc.ctrl.tin_eq, xParent]
    unfold Arena.tin
    omega
  obtain ⟨t, xt, tpc, tm, _, tr⟩ := indexedDataWrite_steps (input := input) (s := x)
    put (by omega) (by omega) (show registers.value ≠ registers.tmp by decide) storeFit
  have tc := xc.unchanged (fun r hr => tr r (by intro e; subst r; exact hr (by decide +revert)))
  have wherePut : t.data = s.data.set (a.tin + (parent u).val) (reg x registers.value)
      (by rw [s.data_size]; change a.tin + (parent u).val < workCap
          unfold Arena.tin; omega) := by
    simpa only [xc.ctrl.tin_eq, xParent, xm, wm, vm] using tm
  have outside (j : Nat) (different : j ≠ a.tin + (parent u).val) : t.data[j]? = s.data[j]? := by
    rw [wherePut]
    exact Array.getElem?_set_ne _ different.symm
  refine ⟨t, sv.append (vw.append (.cons wx xt)), tpc, tc, ?_, ?_, ?_⟩
  · intro j
    rw [outside _ (by unfold Arena.tin; have := j.isLt; omega)]
    exact old.1 j
  · intro p
    rw [visitedRows_succ root parent u p]
    by_cases e : p = parent u
    · subst p
      rw [ite_eq_left ⟨nonroot, rfl⟩, wherePut, Array.getElem?_set_self, Option.map_some, xNext]
      rfl
    · rw [ite_eq_right (fun h => e h.2), outside _ (fun h => e (Fin.ext (Nat.add_left_cancel h)))]
      exact old.2.1 p
  · intro j h
    exact (outside j (by omega)).trans (old.2.2 j h)

/-- The root is skipped. The histogram produces exactly the lengths of
the descending child rows expected by the existing CSR prefix scan. -/
theorem run_parent_histogram (input : Input L) {a : Arena bits workCap n}
    (root : Fin n) (parent : Fin n → Fin n) (s : State L)
    (pc : s.pc = 0) (cursor : ParentCursor a root 0 s)
    (par : ParentAt a parent s.data)
    (zeroes : ∀ p : Fin n, (s.data[a.tin + p.val]?).map Fin.val = some 0) :
    ∃ t trace work, work ≤ 12 * n + 2 ∧
      run (parentScanCode (histogramBody (bits := bits))) input work s = some ⟨t, work⟩ ∧
      ParentCursor a root n t ∧ ParentAt a parent t.data ∧
      (∀ p : Fin n, (t.data[a.tin + p.val]?).map Fin.val = some (parentDegree root parent p.val)) ∧
      (∀ j, (j < a.tin ∨ a.tin + n ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (parentScanCode (histogramBody (bits := bits))) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have start : HistogramInv a root parent s.data 0 s.data :=
    ⟨par, by simpa using zeroes, fun _ _ => rfl⟩
  obtain ⟨t, trace, work, bound, exec, endRegs, result, success, peak⟩ :=
    run_parent_scan input histogramBody (hist_body input)
      (fun _ hc => histogram_skip hc) s pc cursor start
  refine ⟨t, trace, work, bound, exec, endRegs, result.1, ?_, result.2.2, success, peak⟩
  intro p
  simpa only [parentDegree_at, visitedRows_full] using result.2.1 p

end PaperB.RamForestProgram.Finish
