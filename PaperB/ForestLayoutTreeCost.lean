module

public import PaperB.ForestLayout
public import PaperB.ForestLayoutCost

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout

open PaperB.LabelledQuotient

variable {N : Nat}

/-- Use the existing buckets as layout rows, preserving their child order. -/
def bucketChildLists (root : Fin N) (parent : Fin N → Fin N) : ChildLists N where
  rows := bucketChildrenArray root parent
  rows_size := by simp only [bucketChildrenArray, Array.size_ofFn]

@[simp] theorem bucketChildLists_get (root : Fin N) (parent : Fin N → Fin N)
    (v : Fin N) :
    (bucketChildLists root parent).get v = bucketChildren root parent v := by
  simp only [ChildLists.get, bucketChildLists, bucketChildrenArray, Array.getElem_ofFn]

private theorem length_concatMapList_eq_sum {α β : Type} (f : α → List β)
    (xs : List α) :
    (concatMapList f xs).length = (xs.map (fun x => (f x).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [concatMapList, List.length_append, List.map_cons, List.sum_cons, ih]

private theorem sum_map_two_mul {α : Type} (f : α → Nat) (xs : List α) :
    (xs.map (fun x => 2 * f x)).sum = 2 * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private def dfsWeight (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) (v : Fin N) : Nat :=
  2 * (dfsSubtree root parent depth v).length

private theorem dfsWeight_eq {root : Fin N} {parent : Fin N → Fin N}
    {depth : Fin N → Nat} (hTree : ValidDepthTree root parent depth) (v : Fin N) :
    dfsWeight root parent depth v =
      2 + (((bucketChildLists root parent).get v).map
        (dfsWeight root parent depth)).sum := by
  rw [bucketChildLists_get]
  change 2 * (dfsSubtree root parent depth v).length =
    2 + ((bucketChildren root parent v).map
      (fun c => 2 * (dfsSubtree root parent depth c).length)).sum
  have hlen :
      (dfsSubtree root parent depth v).length =
        ((bucketChildren root parent v).map
          (fun c => (dfsSubtree root parent depth c).length)).sum + 1 := by
    have h := congrArg (fun xs : List (Fin N) => xs.length)
      (dfsSubtree_unfold hTree v)
    simpa only [List.length_cons, length_concatMapList_eq_sum] using h
  rw [sum_map_two_mul (fun c => (dfsSubtree root parent depth c).length)
    (bucketChildren root parent v), hlen, Nat.mul_add, Nat.mul_one]
  exact Nat.add_comm _ _

/-- At fuel `2 * N`, the actual layout has no pending commands and has
executed exactly `2 * N` enter and exit commands in total. -/
theorem layout_bucketChildren_exact {root : Fin N} {parent : Fin N → Fin N}
    {depth : Fin N → Nat} (hTree : ValidDepthTree root parent depth) :
    let s := layout (bucketChildLists root parent) root (2 * N)
    s.stack = [] ∧ s.processed = 2 * N := by
  have hroot : dfsWeight root parent depth root = 2 * N := by
    change 2 * (dfsPreorder root parent depth).length = 2 * N
    rw [length_dfsPreorder hTree]
  obtain ⟨hstack, hprocessed⟩ :=
    layout_exact_of_ge (bucketChildLists root parent) (dfsWeight root parent depth)
      (dfsWeight_eq hTree) root (2 * N) (Nat.le_of_eq hroot)
  exact ⟨hstack, hprocessed.trans hroot⟩

end PaperB.ForestLayout
