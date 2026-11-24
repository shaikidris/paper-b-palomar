module

public import PaperB.DomBuildStep
public import PaperB.DomPredecessorFold

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace EX15

open JumpForestCommonAncestor

universe u

/-- The new slot is its own ancestor; every positive-length walk first visits `p`. -/
theorem isAncestor_appendLeaf_new_slot {F : JumpForest} (hF : ValidJumpForest F)
    {p a : Nat} (hp : p < F.size) :
    IsAncestor (F.appendLeaf p) a F.size ↔ a = F.size ∨ IsAncestor F a p := by
  have hParent : (F.appendLeaf p).parentOf F.size = p := by
    change ((F.appendLeaf p).recordAt F.size).parent = p
    rw [recordAt_appendLeaf_new F p] <;> rfl
  have hStep (j : Nat) :
      (F.appendLeaf p).iterParent (j + 1) F.size = F.iterParent j p := by
    change (F.appendLeaf p).iterParent j ((F.appendLeaf p).parentOf F.size) =
      F.iterParent j p
    rw [hParent]
    exact (JumpForest.Extends.step (JumpForest.Extends.refl F) hp).iterParent_eq
      hF hp j
  constructor
  · intro ⟨j, hj⟩
    cases j with
    | zero => exact Or.inl hj.symm
    | succ j => exact Or.inr ⟨j, (hStep j).symm.trans hj⟩
  · intro h
    rcases h with ha | ⟨j, hj⟩
    · exact ⟨0, ha.symm⟩
    · exact ⟨j + 1, (hStep j).trans hj⟩

/-- Every ancestor of an in-bounds slot in a valid forest is in bounds. -/
theorem isAncestor_lt_size_of_valid {F : JumpForest} (hF : ValidJumpForest F)
    {a x : Nat} (hx : x < F.size) (ha : IsAncestor F a x) :
    a < F.size := by
  obtain ⟨j, hj⟩ := ha
  rw [← hj]
  exact hF.iterParent_lt_size hx j

/-- The EX15 backend using the packed-word layout and the actual jump forest. -/
def packedJumpOps (α : Type u) (R : JumpWordRegion) :=
  ({ wordFold := JumpForestPredecessorFold.wordFold R
     appendLeafWords := appendLeafWords R
     occurrence := JumpForestPredecessorFold.Step.occurrence
     size := JumpForest.size
     appendLeaf := JumpForest.appendLeaf
     ancestor := IsAncestor
     layout := JumpWordLayout R
     maxNodes := R.maxNodes
     foldExact := by
       intro F mem n L hLay hn hL slot head tail hslots
       change F.numInserted ≤ n at hn
       exact JumpForestPredecessorFold.wordFold_exact hLay hn hL slot head tail hslots
     foldOccurrences := by
       intro mem slot head tail
       exact JumpForestPredecessorFold.wordFold_occurrences R mem slot head tail
     appendExact := by
       intro F mem p hLay hRoom hp
       change F.numInserted < R.maxNodes at hRoom
       have hAppend := appendLeafWords_spec hLay hRoom hp
       exact ⟨hAppend.1, hAppend.2.2.1⟩
     appendSize := by
       intro F mem p hLay hp
       exact JumpForest.size_appendLeaf F p
     ancestorOld := by
       intro F mem p k x hLay hp hx
       exact isAncestor_appendLeaf_old hLay.valid hp hx
     ancestorNew := by
       intro F mem p k hLay hp
       exact isAncestor_appendLeaf_new_slot hLay.valid hp
     ancestorBound := by
       intro F mem k x hLay hx ha
       exact isAncestor_lt_size_of_valid hLay.valid hx ha }
    : JumpOps α JumpForest (JumpForestPredecessorFold.Step α) _)

end EX15
end PaperB
