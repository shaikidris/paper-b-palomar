module

public import PaperB.ForestReady
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

namespace EX24
namespace PreStep

noncomputable section

variable {H : LabelledQuotient} {rank : Vertex H → Nat}

private theorem take_snoc_prefix {α : Type} (xs : List α) (x : α) :
    (xs ++ [x]).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      change y :: (ys ++ [x]).take ys.length = y :: ys
      exact congrArg (List.cons y) ih

private theorem getElem?_snoc_last {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [ih]

private theorem iterParentFin_succ_outer {n : Nat}
    (parent : Fin n → Fin n) (k : Nat) (a : Fin n) :
    iterParentFin parent (k + 1) a =
      parent (iterParentFin parent k a) := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
      change iterParentFin parent (k + 1) (parent a) =
        parent (iterParentFin parent k (parent a))
      exact ih (parent a)

private theorem climb_eq_iterParentFin {n : Nat}
    (parent : Fin n → Fin n) (k : Nat) (a : Fin n) :
    climb parent k a = iterParentFin parent k a := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change parent (climb parent k a) = iterParentFin parent (k + 1) a
      rw [ih, iterParentFin_succ_outer]

-- Both the prefix and the final key come from this one-edge decomposition.
-- The parent-key theorem is essential: a stored parent must actually be
-- represented by the parent slot for the parentKeyChain equation to apply.
private theorem canonical_nodeChain_snoc
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {a : CanonNode H rank} {B : CutPair H}
    (ha : (buildProperLossForest H rank).nodeKey? a = some B) :
    (buildProperLossForest H rank).nodeChain a =
      (buildProperLossForest H rank).nodeChain
        ((buildProperLossForest H rank).parent a) ++ [B] := by
  rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat a,
    buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat
      ((buildProperLossForest H rank).parent a),
    ha, buildProperLossForest_nodeKey?_parent rankArc flat ha,
    parentKeyChain_some_eq rankArc flat B]

private theorem canonical_eq_root_of_no_key
    {a : CanonNode H rank}
    (ha : (buildProperLossForest H rank).nodeKey? a = none) :
    a = (buildProperLossForest H rank).rootNode :=
  buildProperLossForest_nodeKey?_inj H rank
    (ha.trans (buildProperLossForest_nodeKey?_root H rank).symm)

set_option maxHeartbeats 1000000 in
private theorem canonical_lost_cases (B : CutPair H) (u : Vertex H) :
    (B.Mem u ∨ H.ProperLoss B u) ↔ H.Lost B u := by
  classical
  constructor
  · rintro (hm | hp)
    · first
      | exact?
      | intro hPath
        have hAvoidsEnd : ¬ B.Mem u := by exact?
        exact hAvoidsEnd hm
    · first
      | exact hp.1
      | exact hp.2
      | exact?
  · intro hl
    by_cases hm : B.Mem u
    · exact Or.inl hm
    · apply Or.inr
      first
      | exact ⟨hl, hm⟩
      | exact ⟨hm, hl⟩
      | exact?

-- Look up the imported sweep correctness theorem by its result type.
-- In particular, the predecessor specification is proved for every vertex;
-- it is not an extra hypothesis of the CanonicalLaws construction.
set_option maxHeartbeats 1000000 in
private theorem canonical_sweep_spec
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (u : Vertex H) :
    SweepChainSpec H (sweepChain H rank u) u := by
  exact?

set_option maxHeartbeats 1000000 in
private theorem canonical_sweep_nested
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (m : Vertex H) :
    (sweepChain H rank m).Pairwise
      (fun B P => ∀ v, P.Mem v → H.Lost B v) := by
  have hs := canonical_sweep_spec rankArc flat m
  have fromEndpoints
      (h : (sweepChain H rank m).Pairwise
        (fun B P => H.Lost B P.fst ∧ H.Lost B P.snd)) :
      (sweepChain H rank m).Pairwise
        (fun B P => ∀ v, P.Mem v → H.Lost B v) := by
    refine List.Pairwise.imp ?_ h
    intro B P hBP v hv
    rcases hv with hv | hv
    · subst v
      exact hBP.1
    · subst v
      exact hBP.2
  first
  | exact?
  | apply fromEndpoints
    exact?
  | cases hs
    first
    | solve_by_elim [fromEndpoints, And.left, And.right]
    | exact?
    | apply fromEndpoints
      exact?
    | refine List.Pairwise.imp ?_ (by assumption)
      intro B P hBP v hv
      first
      | solve_by_elim [And.left, And.right]
      | rcases hv with hv | hv <;> subst v <;>
          solve_by_elim [And.left, And.right]

/-- The canonical EX2.4 pre-step contract, with no table or embedding assumptions. -/
theorem canonicalLaws_of_flat_forward
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) : CanonicalLaws H rank where
  root_nil := by
    rfl
  depth_length := by
    intro a
    change
      (parentKeyChain H rank ((buildProperLossForest H rank).nodeKey? a)).length =
        ((buildProperLossForest H rank).nodeChain a).length
    exact congrArg List.length
      (buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat a).symm
  parent_take := by
    intro a
    cases ha : (buildProperLossForest H rank).nodeKey? a with
    | none =>
        have har := canonical_eq_root_of_no_key ha
        subst a
        rfl
    | some B =>
        have hs := canonical_nodeChain_snoc rankArc flat ha
        have hlen :
            ((buildProperLossForest H rank).nodeChain a).length - 1 =
              ((buildProperLossForest H rank).nodeChain
                ((buildProperLossForest H rank).parent a)).length := by
          rw [hs] <;> simp
        rw [hlen, hs]
        exact (take_snoc_prefix _ B).symm
  last_key := by
    intro a k hk
    cases ha : (buildProperLossForest H rank).nodeKey? a with
    | none =>
        have har := canonical_eq_root_of_no_key ha
        subst a
        change 0 = k + 1 at hk
        omega
    | some B =>
        have hs := canonical_nodeChain_snoc rankArc flat ha
        have hlen :
            ((buildProperLossForest H rank).nodeChain
              ((buildProperLossForest H rank).parent a)).length = k := by
          rw [hs] at hk
          simpa using hk
        subst k
        simpa only [ha, hs] using
          (getElem?_snoc_last
            ((buildProperLossForest H rank).nodeChain
              ((buildProperLossForest H rank).parent a)) B).symm
  ancestor := by
    intro a b _
    simpa only [climb_eq_iterParentFin] using
      (isForestAncestor_iff_iterParentFin
        (buildProperLossForest H rank).parent a b)
  lost_cases := canonical_lost_cases
  nested := canonical_sweep_nested rankArc flat
  legacy := by
    intro y m k hk
    exact sweepPasses_correct_of_preds_spec (y := y)
      (fun u _ => canonical_sweep_spec rankArc flat u)
      ((sweepChain H rank m)[k]'hk)

end
end PreStep
end EX24
