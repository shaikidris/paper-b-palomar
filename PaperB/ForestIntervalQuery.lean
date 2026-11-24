module

public import PaperB.ForestIntervals

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestIntervalQuery

open LabelledQuotient

/-- `N` is the forest-node index range, including the synthetic root.
`V` is the original quotient-vertex index range. Keeping the root slot
lets the label table use the forest's node IDs without translation. -/
structure Tables (N V : Nat) where
  entries : Array Nat
  ends : Array Nat
  labels : Array (Fin N)
  entries_size : entries.size = N
  ends_size : ends.size = N
  labels_size : labels.size = V

namespace Tables

@[inline] def readEntry {N V : Nat} (T : Tables N V) (i : Fin N) : Nat :=
  T.entries[i.val]'(by rw [T.entries_size]; exact i.isLt)

@[inline] def readEnd {N V : Nat} (T : Tables N V) (i : Fin N) : Nat :=
  T.ends[i.val]'(by rw [T.ends_size]; exact i.isLt)

@[inline] def readLabel {N V : Nat} (T : Tables N V) (y : Fin V) : Fin N :=
  T.labels[y.val]'(by rw [T.labels_size]; exact y.isLt)

end Tables

/-- Query with an already located node `a` and an original quotient vertex
ID `y`. The label read selects the second entry read. -/
def query {N V : Nat} (T : Tables N V) (a : Fin N) (y : Fin V) : Bool :=
  let v := T.readLabel y
  let lo := T.readEntry a
  let pos := T.readEntry v
  let hi := T.readEnd a
  decide (lo ≤ pos ∧ pos < hi)

/-- Per-index agreement with the computed DFS intervals and forest labels.
This is a proof-side relation, not part of the query data. -/
structure Layout {N V : Nat} (T : Tables N V)
    (root : Fin N) (parent : Fin N → Fin N) (depth : Fin N → Nat)
    (label : Fin V → Fin N) : Prop where
  entry_eq : ∀ i : Fin N, T.readEntry i = entry root parent depth i
  end_eq : ∀ i : Fin N, T.readEnd i =
    entry root parent depth i + (dfsSubtree root parent depth i).length
  label_eq : ∀ y : Fin V, T.readLabel y = label y

theorem query_eq_true_iff_interval {N V : Nat} {T : Tables N V}
    {root : Fin N} {parent : Fin N → Fin N} {depth : Fin N → Nat}
    {label : Fin V → Fin N} (hLayout : Layout T root parent depth label)
    (a : Fin N) (y : Fin V) :
    query T a y = true ↔ dfsIntervalContains root parent depth a (label y) := by
  simp only [query, decide_eq_true_eq, hLayout.label_eq, hLayout.entry_eq,
    hLayout.end_eq, dfsIntervalContains]

abbrev ProperLossLayout (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat)
    (T : Tables ((buildProperLossForest H rank).realNodeCount + 1)
      H.vertexCount) : Prop :=
  let F := buildProperLossForest H rank
  Layout T F.rootNode F.parent F.depth F.label

/-- With a correct layout and a known node for `P`, the Boolean query
recognizes exactly the proper-loss predicate. -/
theorem query_eq_true_iff_properLoss_of_node {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {T : Tables ((buildProperLossForest H rank).realNodeCount + 1)
      H.vertexCount}
    (hLayout : ProperLossLayout H rank T)
    {a : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P : CutPair H}
    (ha : (buildProperLossForest H rank).nodeKey? a = some P)
    (y : Fin H.vertexCount) :
    query T a y = true ↔ H.ProperLoss P y := by
  let F := buildProperLossForest H rank
  have hF : Layout T F.rootNode F.parent F.depth F.label := hLayout
  exact (query_eq_true_iff_interval hF a y).trans
    (buildProperLossForest_properLoss_iff_interval_of_node
      rankArc distinctRanks flat ha y).symm

end PaperB.ForestIntervalQuery
