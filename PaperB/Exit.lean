module

public import PaperB.Forest

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open LabelledQuotient

section RealEdge

variable {H : LabelledQuotient} {rank : Fin H.vertexCount → Nat}
variable (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)
variable {uP : Fin ((buildProperLossForest H rank).realNodeCount + 1)}
variable {P B : CutPair H}
variable (huP : (buildProperLossForest H rank).nodeKey? uP = some P)
variable (huB : (buildProperLossForest H rank).nodeKey?
  ((buildProperLossForest H rank).parent uP) = some B)

include rankArc flat huP huB

/-- EX3.3 on a real forest edge from parent cut `B` to child cut `P`.
Every term uses the same labelled quotient: physical-tail IDs are unchanged,
and no arcs are filtered or coalesced. -/
theorem buildProperLossForest_edge_exitTailMem_iff
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss P y) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) :=
  exitTailMem_iff_of_flat_rank rankArc flat
    (buildProperLossForest_edge_fresh_follows_parent rankArc flat huP huB)
    (buildProperLossForest_edge_distinct_cuts rankArc flat huP huB)
    hs proper

/-- The edge identity as equality of predicates on original vertices. -/
theorem buildProperLossForest_edge_exitTailMem_eq
    {s y : Fin H.vertexCount} (hs : B.Mem s) (proper : H.ProperLoss P y) :
    (fun x : Fin H.origVertexCount => H.ExitTailMem B s y x) =
      (fun x : Fin H.origVertexCount =>
        (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
        (P.Mem s ∧ H.ExitTailMem P s y x)) := by
  funext x
  exact propext
    (buildProperLossForest_edge_exitTailMem_iff rankArc flat huP huB (x := x) hs proper)


end RealEdge
end PaperB
