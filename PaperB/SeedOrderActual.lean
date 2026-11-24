module

public import PaperB.SeedOrder
public import PaperB.ForestIntervals
public import PaperB.ExitPaths

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX42

open PaperB PaperB.LabelledQuotient

/-- The seed-order witness for the actual proper-loss forest of `H`.
Its seed chronology lemmas use the original quotient arcs and the forest's
own keys, parent, and labels. -/
noncomputable def buildProperLossForestWitness
    (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat)
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) :
    ProperLossForestWitness H (fun K : LabelledQuotient => Fin K.vertexCount)
      (Fin ((buildProperLossForest H rank).realNodeCount + 1)) (CutPair H) where
  rank := rank
  distinctRanks := distinctRanks
  hasQuotientArc := H.HasQuotientArc
  mem := fun B y => B.Mem y
  lost := H.Lost
  nodeKey? := (buildProperLossForest H rank).nodeKey?
  parent := (buildProperLossForest H rank).parent
  label := (buildProperLossForest H rank).label
  ancestor := IsForestAncestor (buildProperLossForest H rank).parent
  ancestor_refl := fun _ => IsForestAncestor.refl
  real_has_properLoss := by
    intro u B hu
    exact ((buildProperLossForest_exists_node_iff rankArc flat B).mp ⟨u, hu⟩).2
  properLoss_iff_ancestor := by
    intro u B hu y
    exact buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat hu y
  edge_properLoss_subset := by
    intro u P B hu hparent y hy
    exact buildProperLossForest_edge_properLoss_subset
      rankArc distinctRanks flat hu hparent y hy
  edge_endpoints_lost := by
    intro u P B hu hparent p hp
    exact buildProperLossForest_edge_endpoints_lost rankArc flat hu hparent p hp
  edge_distinct_cuts := by
    intro u P B hu hparent
    exact buildProperLossForest_edge_distinct_cuts rankArc flat hu hparent
  properLoss_follows_endpoints := by
    intro B y b hy hb
    exact properLoss_follows_endpoints (B := B) rankArc flat hy hb
  predecessors_iff_endpoints_of_first_properLoss := by
    intro B y hy hfirst z
    exact predecessors_iff_endpoints_of_first_properLoss
      (B := B) rankArc flat hy hfirst z

end EX42
