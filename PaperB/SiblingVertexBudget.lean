module

public import PaperB.SiblingEncoding
public import PaperB.QuotientBudget

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.SiblingEncoding

open PaperB.Digraph

private noncomputable def budgetRootLabel
    (g : Digraph) (d v : Fin g.vertexCount) : Option (Fin g.vertexCount) := by
  classical
  exact if v = d then some v else none

private noncomputable def budgetChildLabel
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (v : Fin g.vertexCount) : Option (Fin g.vertexCount) := by
  classical
  exact if parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v then
    some v
  else
    none

private theorem budgetConditionOfSome
    {A : Type _} (p : Prop) [Decidable p] (v b : A)
    (h : (if p then some v else none) = some b) : p := by
  by_cases hp : p
  · exact hp
  · simp [hp] at h

private theorem budgetFilterMapLengthSplit
    (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (xs : List (Fin g.vertexCount)) :
    (show List (SiblingBlockKey g r d parent) from by
      classical
      exact xs.filterMap fun v =>
        if h : v = d ∨ (parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v) then
          some ⟨v, h⟩
        else
          none).length =
      (xs.filterMap (budgetRootLabel g d)).length +
        (xs.filterMap (budgetChildLabel g r d parent)).length := by
  classical
  delta SiblingBlockKey
  induction xs with
  | nil => rfl
  | cons v vs ih =>
      by_cases hr : v = d
      · have hc : ¬ (parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v) :=
          fun h => h.2.1 hr
        have hk : v = d ∨ (parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v) :=
          Or.inl hr
        simp only [List.filterMap, dite_eq_left hk, budgetRootLabel, ite_eq_left hr,
          budgetChildLabel, ite_eq_right hc, List.length_cons] at ih ⊢
        omega
      · by_cases hc : parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v
        · have hk : v = d ∨ (parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v) :=
            Or.inr hc
          simp only [List.filterMap, dite_eq_left hk, budgetRootLabel, ite_eq_right hr,
            budgetChildLabel, ite_eq_left hc, List.length_cons] at ih ⊢
          omega
        · have hk : ¬ (v = d ∨ (parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v)) :=
            fun h => h.elim hr hc
          simpa only [List.filterMap, dite_eq_right hk, budgetRootLabel, ite_eq_right hr,
            budgetChildLabel, ite_eq_right hc] using ih

private theorem budgetSumMapAdd
    {A : Type _} (xs : List A) (f h : A → Nat) :
    (xs.map (fun x : A => f x + h x)).sum =
      (xs.map f).sum + (xs.map h).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      omega

/-- The actual sibling block keys across distinct roots use at most two
    emissions per original vertex: one as a root and one as a child. -/
theorem _root_.PaperB.SiblingVertexBudget.sum_siblingBlockKeys_length_le_vertex_budget
    (g : Digraph) (r : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (roots : List (Fin g.vertexCount)) (hn : roots.Nodup) :
    (roots.map (fun d : Fin g.vertexCount =>
      (siblingBlockKeys g r d parent).length)).sum ≤ 2 * g.vertexCount := by
  classical
  let xs : List (Fin g.vertexCount) := List.ofFn (fun v : Fin g.vertexCount => v)
  let rootCount : Fin g.vertexCount → Nat :=
    fun d : Fin g.vertexCount => (xs.filterMap (budgetRootLabel g d)).length
  let childCount : Fin g.vertexCount → Nat :=
    fun d : Fin g.vertexCount => (xs.filterMap (budgetChildLabel g r d parent)).length
  have hroot : (roots.map rootCount).sum ≤ xs.length :=
    PaperB.QuotientBudget.sum_filterMap_length_le_length_of_nodup
      roots xs (budgetRootLabel g) hn (by
        intro d e v b c hd he
        have hvd : v = d := budgetConditionOfSome (v = d) v b hd
        have hve : v = e := budgetConditionOfSome (v = e) v c he
        exact hvd.symm.trans hve)
  have hchild : (roots.map childCount).sum ≤ xs.length :=
    PaperB.QuotientBudget.sum_filterMap_length_le_length_of_nodup
      roots xs (fun d : Fin g.vertexCount => budgetChildLabel g r d parent) hn (by
        intro d e v b c hd he
        have hvd : parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v :=
          budgetConditionOfSome (parent v = d ∧ v ≠ d ∧ g.InitiallyReachable r v)
            v b hd
        have hve : parent v = e ∧ v ≠ e ∧ g.InitiallyReachable r v :=
          budgetConditionOfSome (parent v = e ∧ v ≠ e ∧ g.InitiallyReachable r v)
            v c he
        exact hvd.1.symm.trans hve.1)
  have hper (d : Fin g.vertexCount) :
      (siblingBlockKeys g r d parent).length = rootCount d + childCount d := by
    simpa only [siblingBlockKeys, rootCount, childCount] using
      (budgetFilterMapLengthSplit g r d parent xs)
  have hmap :
      roots.map (fun d : Fin g.vertexCount => (siblingBlockKeys g r d parent).length) =
        roots.map (fun d : Fin g.vertexCount => rootCount d + childCount d) :=
    congrArg (fun f : Fin g.vertexCount → Nat => roots.map f) (funext hper)
  have hxs : xs.length = g.vertexCount := by
    simp [xs]
  calc
    (roots.map (fun d : Fin g.vertexCount => (siblingBlockKeys g r d parent).length)).sum =
        (roots.map rootCount).sum + (roots.map childCount).sum := by
          rw [hmap, budgetSumMapAdd roots rootCount childCount]
    _ ≤ xs.length + xs.length := Nat.add_le_add hroot hchild
    _ = 2 * g.vertexCount := by
      rw [hxs]
      omega

end PaperB.SiblingEncoding
