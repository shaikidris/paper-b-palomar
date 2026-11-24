module

public import PaperB.ExitEmbeddingAncestry
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace AppendOrder

theorem le_index_after_append
    {size p position : Nat} {before after : Nat → Nat}
    (hPosition : position < size + 1)
    (hBefore : ∀ j < size, before j ≤ j)
    (hCopy : ∀ j < size, after j = before j)
    (hp : p ≤ size) (hAppend : after size = p) :
    after position ≤ position := by
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hPosition) with hOld | rfl
  · simpa only [hCopy position hOld] using hBefore position hOld
  · simpa only [hAppend] using hp

theorem lt_index_after_append
    {size p position : Nat} {before after : Nat → Nat}
    (hPosition : position < size + 1) (hPositive : 0 < position)
    (hBefore : ∀ j < size, 0 < j → before j < j)
    (hCopy : ∀ j < size, after j = before j)
    (hp : p < size) (hAppend : after size = p) :
    after position < position := by
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hPosition) with hOld | rfl
  · simpa only [hCopy position hOld] using hBefore position hOld hPositive
  · simpa only [hAppend] using hp

end AppendOrder

open PaperB PaperB.ForestHead PaperB.LabelledQuotient

namespace PaperB.FinalEmbeddingAncestry

/-- Parent reads from a valid growing forest never refer to later slots.
Positive slots refer strictly backward. -/
theorem valid_parent_slot_order {F : JumpForest} (valid : ValidJumpForest F) :
    (∀ u < F.size, F.parentOf u ≤ u) ∧
      (∀ u < F.size, 0 < u → F.parentOf u < u) := by
  induction valid with
  | init =>
    simp only [JumpForest.size_init]
    constructor
    · intro u hu
      have hu0 : u = 0 := by omega
      subst u
      decide
    · intro u hu hpos
      omega
  | @appendLeaf old p valid hp ih =>
    have written : (old.appendLeaf p).parentOf old.size = p := by
      unfold JumpForest.parentOf
      rw [recordAt_appendLeaf_new]
      rfl
    rw [JumpForest.size_appendLeaf]
    constructor
    · intro u hu
      exact AppendOrder.le_index_after_append
        hu ih.1 (fun j hj => parentOf_appendLeaf_old old p hj) (Nat.le_of_lt hp) written
    · intro u hu hpos
      exact AppendOrder.lt_index_after_append
        hu hpos ih.2 (fun j hj => parentOf_appendLeaf_old old p hj) hp written

theorem physical_le_of_valid_image {H : LabelledQuotient} {c : EX24.Config H}
    {s : EX24.State H} {F : JumpForest} {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size} {processed : Vertex H → Prop}
    (valid : ValidJumpForest F) (parentEq : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (E : EX24.PreStep.Embedding c s F rank up processed) {a z : Fin F.size}
    (path : IsForestAncestor (buildProperLossForest H rank).parent (E.image a) (E.image z)) :
    a.val ≤ z.val := by
  apply physical_le_of_image E path
  intro v
  rw [parentEq]
  exact (valid_parent_slot_order valid).1 v.val v.isLt

end PaperB.FinalEmbeddingAncestry
