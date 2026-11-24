module

public import PaperB.ExitKernels

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.BuiltExit

section ForestRoutes

open PaperB.LabelledQuotient PaperB.ExitMap PaperB.ExitSummary

variable {H : LabelledQuotient} {m : Nat}

/-- The forest facts used by route existence. The raw `ProperLossForest`
structure does not assert them. -/
structure RouteForestFacts (F : ProperLossForest H) : Prop where
  root_fixed : F.parent F.rootNode = F.rootNode
  none_is_root : ∀ k, F.nodeKey? k = none → k = F.rootNode
  proper_of_ancestor :
    ∀ (y : Fin H.vertexCount) {k : Fin (F.realNodeCount + 1)} {C : CutPair H},
      F.nodeKey? k = some C →
      IsForestAncestor F.parent k (F.label y) →
      H.ProperLoss C y

/-- The reference forest builder supplies the root and loss facts. -/
theorem RouteForestFacts.of_build
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) :
    RouteForestFacts (buildProperLossForest H rank) := by
  refine ⟨buildProperLossForest_parent_root H rank, ?_, ?_⟩
  · intro k hk
    apply buildProperLossForest_nodeKey?_inj H rank
    rw [hk, buildProperLossForest_nodeKey?_root]
  intro y k C hk hAnc
  exact
    (buildProperLossForest_properLoss_iff_of_node
      rankArc distinctRanks flat hk y).mpr hAnc

/-- Installed coverage of the real edges on the path from `label z` to `a`.
The ancestry premises say that `a` is at or above `parent k` and that `k`
is at or above `label z`. The witness must drive this exact child node. -/
def RoutePathEdgeLive (W : Model H m) (S : Fin m → Prop)
    (a : Fin (W.forest.realNodeCount + 1)) (z : Fin H.vertexCount) : Prop :=
  ∀ (k : Fin (W.forest.realNodeCount + 1)) {C P : CutPair H},
    W.forest.nodeKey? k = some C →
    W.forest.nodeKey? (W.forest.parent k) = some P →
    IsForestAncestor W.forest.parent a (W.forest.parent k) →
    IsForestAncestor W.forest.parent k (W.forest.label z) →
    ∃ i : Fin m, W.edgeNode i = k ∧ S i

/-- Separate complete driver coverage from the installation proof. A
publication invariant can discharge `installed` at the query snapshot. -/
theorem RoutePathEdgeLive.of_driverCoverage
    {W : Model H m} {S : Fin m → Prop}
    {a : Fin (W.forest.realNodeCount + 1)} {z : Fin H.vertexCount}
    (cover : ∀ (k : Fin (W.forest.realNodeCount + 1)) {C P : CutPair H},
      W.forest.nodeKey? k = some C →
      W.forest.nodeKey? (W.forest.parent k) = some P →
      ∃ i : Fin m, W.edgeNode i = k)
    (installed : ∀ i : Fin m,
      IsForestAncestor W.forest.parent a
        (W.forest.parent (W.edgeNode i)) →
      IsForestAncestor W.forest.parent (W.edgeNode i)
        (W.forest.label z) →
      S i) :
    RoutePathEdgeLive W S a z := by
  intro k C P hk hp hAbove hBelow
  obtain ⟨i, hi⟩ := cover k hk hp
  exact ⟨i, hi, installed i
    (by simpa only [hi] using hAbove)
    (by simpa only [hi] using hBelow)⟩

private theorem routeAncestor_eq_of_fixed
    {n : Nat} {p : Fin n → Fin n} {a k : Fin n}
    (h : IsForestAncestor p a k) : p k = k → a = k := by
  induction h with
  | refl =>
    intro _
    rfl
  | step u _ ih =>
    intro hu
    exact (ih (congrArg p hu)).trans hu

private theorem routeKey_of_realAncestor
    {F : ProperLossForest H} (facts : RouteForestFacts F)
    {a k : Fin (F.realNodeCount + 1)} {B : CutPair H}
    (hB : F.nodeKey? a = some B)
    (hAnc : IsForestAncestor F.parent a k) :
    ∃ C : CutPair H, F.nodeKey? k = some C := by
  cases hk : F.nodeKey? k with
  | none =>
    have hFix : F.parent k = k := by
      rw [facts.none_is_root k hk]
      exact facts.root_fixed
    have hEq : a = k := routeAncestor_eq_of_fixed hAnc hFix
    have hSome : F.nodeKey? k = some B := by
      rw [← hEq]
      exact hB
    rw [hk] at hSome
    cases hSome
  | some C =>
    exact ⟨C, rfl⟩

namespace Route

variable {W : Model H m} {S : Fin m → Prop}
  {z : Fin H.vertexCount} {B : CutPair H}
  {a : Fin (W.forest.realNodeCount + 1)}

theorem nonempty_of_forestAncestor
    (facts : RouteForestFacts W.forest)
    (hOwner : W.owner z = W.forest.nodeKey? (W.forest.label z))
    (hB : W.forest.nodeKey? a = some B)
    (hAnc : IsForestAncestor W.forest.parent a (W.forest.label z))
    (hLive : RoutePathEdgeLive W S a z) :
    Nonempty (Route W S z B) := by
  have extendRoute :
      ∀ {k : Fin (W.forest.realNodeCount + 1)},
        IsForestAncestor W.forest.parent a k →
        IsForestAncestor W.forest.parent k (W.forest.label z) →
        ∀ {C : CutPair H}, W.forest.nodeKey? k = some C →
          Nonempty (Route W S z C) → Nonempty (Route W S z B) := by
    intro k h
    induction h with
    | refl =>
      intro _ C hk hr
      have hCB : C = B := Option.some.inj (hk.symm.trans hB)
      subst C
      exact hr
    | step k hPrev ih =>
      intro hBelow C hk hr
      obtain ⟨P, hp⟩ := routeKey_of_realAncestor facts hB hPrev
      obtain ⟨i, hi, hSi⟩ := hLive k hk hp hPrev hBelow
      have hc : W.child i = C := by
        apply Option.some.inj
        calc
          some (W.child i) = W.forest.nodeKey? (W.edgeNode i) :=
            (W.childKey i).symm
          _ = some C := by rw [hi, hk]
      have hpar : W.parent i = P := by
        apply Option.some.inj
        calc
          some (W.parent i) =
              W.forest.nodeKey? (W.forest.parent (W.edgeNode i)) :=
            (W.parentKey i).symm
          _ = some P := by rw [hi, hp]
      have hLoss : H.ProperLoss (W.child i) z := by
        rw [hc]
        exact facts.proper_of_ancestor z hk hBelow
      have hInner : Nonempty (Route W S z (W.child i)) := by
        rw [hc]
        exact hr
      obtain ⟨r⟩ := hInner
      have hUp : Nonempty (Route W S z P) := by
        rw [← hpar]
        exact ⟨Route.step i hSi hLoss r⟩
      have hEdge :
          IsForestAncestor W.forest.parent (W.forest.parent k) k :=
        IsForestAncestor.step k IsForestAncestor.refl
      exact ih (IsForestAncestor.trans hEdge hBelow) hp hUp
  obtain ⟨C, hC⟩ := routeKey_of_realAncestor facts hB hAnc
  have hSeed : Nonempty (Route W S z C) :=
    ⟨Route.seed (hOwner.trans hC)⟩
  exact extendRoute hAnc IsForestAncestor.refl hC hSeed

theorem exists_actual_exact_of_forestAncestor
    (facts : RouteForestFacts W.forest)
    (hOwner : W.owner z = W.forest.nodeKey? (W.forest.label z))
    (hB : W.forest.nodeKey? a = some B)
    (hAnc : IsForestAncestor W.forest.parent a (W.forest.label z))
    (hLive : RoutePathEdgeLive W S a z)
    (rm : MapReader S)
    (hm : ∀ i hi, rm i hi = some (W.wantMap i)) :
    ∃ r : Route W S z B,
      Map.eval (r.actual rm) (W.wantBase z) = W.ref B z := by
  obtain ⟨r⟩ := nonempty_of_forestAncestor facts hOwner hB hAnc hLive
  exact ⟨r, r.actual_exact rm hm⟩

end Route
end ForestRoutes
end PaperB.BuiltExit
