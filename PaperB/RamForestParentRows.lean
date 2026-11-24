module

public import PaperB.RamForestCsrOffsets

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.LabelledQuotient (finElems length_finElems bucketPassAux addChildToBuckets bucketChildren)
open PaperB.ForestLayout (bucketChildLists bucketChildLists_get ChildLists)
open PaperB.Machine (Word)
open PaperB.RamForestStack (commandWord)
open PaperB.RamProgram

variable {n bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

theorem finElems_index (k : Nat) (i : Fin k) :
    (finElems k)[i.val]'(by rw [length_finElems]; exact i.isLt) = i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    obtain ⟨j, bound⟩ := i
    cases j with
    | zero => rfl
    | succ j =>
      apply Fin.ext
      have h : j < k := Nat.lt_of_succ_lt_succ bound
      simp only [finElems, List.getElem_cons_succ, List.getElem_map]
      have e := ih ⟨j, h⟩
      simp only at e
      rw [e]
      rfl

private theorem bucket_append (root : Fin n) (parent : Fin n → Fin n)
    (xs ys : List (Fin n)) (start : Fin n → List (Fin n)) :
    bucketPassAux root parent (xs ++ ys) start =
      bucketPassAux root parent ys (bucketPassAux root parent xs start) := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append, bucketPassAux, ih]

/-- Specification of the rows after scanning vertices below the cursor.
The counted program accumulates their lengths; scatter writes their contents. -/
def visitedRows (root : Fin n) (parent : Fin n → Fin n) (i : Nat) (p : Fin n) :
    List (Fin n) :=
  bucketPassAux root parent ((finElems n).take i) (fun _ => []) p

@[simp] theorem visitedRows_zero (root : Fin n) (parent : Fin n → Fin n) (p : Fin n) :
    visitedRows root parent 0 p = [] := rfl

@[simp] theorem visitedRows_full (root : Fin n) (parent : Fin n → Fin n) (p : Fin n) :
    visitedRows root parent n p = (bucketChildLists root parent).get p := by
  unfold visitedRows
  have e : (finElems n).take n = finElems n := by
    apply List.take_of_length_le
    rw [length_finElems]
    exact Nat.le_refl _
  rw [e, bucketChildLists_get]
  rfl

theorem visitedRows_succ (root : Fin n) (parent : Fin n → Fin n)
    (u p : Fin n) :
    visitedRows root parent (u.val + 1) p =
      if u ≠ root ∧ p = parent u then u :: visitedRows root parent u.val p
      else visitedRows root parent u.val p := by
  have h : u.val < (finElems n).length := by rw [length_finElems]; exact u.isLt
  unfold visitedRows
  rw [List.take_succ_eq_append_getElem h, finElems_index n u, bucket_append]
  simp only [bucketPassAux, addChildToBuckets]
  by_cases e : u = root
  · simp [e]
  · simp [e]

theorem visitedRows_length_le (root : Fin n) (parent : Fin n → Fin n)
    (p : Fin n) (i : Nat) (bound : i ≤ n) :
    (visitedRows root parent i p).length ≤ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h : i < n := by omega
    have before := ih (by omega)
    rw [show visitedRows root parent (i + 1) p = _ from
      visitedRows_succ root parent (⟨i, h⟩ : Fin n) p]
    split <;> simp only [List.length_cons] <;> omega

theorem visitedRows_length_mono (root : Fin n) (parent : Fin n → Fin n) (p : Fin n)
    {i j : Nat} (hle : i ≤ j) (bound : j ≤ n) :
    (visitedRows root parent i p).length ≤ (visitedRows root parent j p).length := by
  induction j with
  | zero =>
    have e : i = 0 := by omega
    rw [e]
    exact Nat.le_refl _
  | succ j ih =>
    by_cases e : i = j + 1
    · rw [e]
      exact Nat.le_refl _
    · have before := ih (by omega) (by omega)
      have h : j < n := by omega
      rw [show visitedRows root parent (j + 1) p = _ from
        visitedRows_succ root parent (⟨j, h⟩ : Fin n) p]
      split <;> simp only [List.length_cons] <;> omega

/-- A parent column occupies the first half of the later DFS stack bank. -/
def ParentAt (a : Arena bits workCap n) (parent : Fin n → Fin n)
    (data : Array (Word bits)) : Prop :=
  ∀ v : Fin n, (data[a.base + v.val]?).map Fin.val = some (parent v).val

/-- The degree function expected by the CSR prefix scan. -/
def parentDegree (root : Fin n) (parent : Fin n → Fin n) (j : Nat) : Nat :=
  if h : j < n then (visitedRows root parent n ⟨j, h⟩).length else 0

@[simp] theorem parentDegree_at (root : Fin n) (parent : Fin n → Fin n) (p : Fin n) :
    parentDegree root parent p.val = ((bucketChildLists root parent).get p).length := by
  unfold parentDegree
  rw [dite_eq_left p.isLt, visitedRows_full]

theorem offsetInput_of_parent_degrees (input : State L) {a : Arena bits workCap n}
    (root : Fin n) (parent : Fin n → Fin n)
    (pc : input.pc = 0) (ptr : (reg input registers.ptr).val = 0)
    (clkZero : (reg input clk).val = 0) (ctrl : Control a input)
    (degreeBank : ∀ p : Fin n, (input.data[a.tin + p.val]?).map Fin.val =
      some (visitedRows root parent n p).length)
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) :
    OffsetInput a (parentDegree root parent) input := by
  refine ⟨pc, ptr, clkZero, ctrl, ?_, mass⟩
  intro j hj
  let p : Fin n := ⟨j, hj⟩
  change (input.data[a.tin + p.val]?).map Fin.val = some (parentDegree root parent p.val)
  rw [degreeBank p, parentDegree_at, visitedRows_full]

end PaperB.RamForestProgram.Finish
