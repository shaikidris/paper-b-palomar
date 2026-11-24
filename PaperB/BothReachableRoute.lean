module

public import PaperB.RetainedRouteProof

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB.EX44

open PaperB
open PaperB.Digraph
open PaperB.Digraph.EX44
open PaperB.LabelledQuotient

variable {g : PaperB.Digraph} {n k B E : Nat}
variable {R : Runtime g.vertexCount n k B E} {W : World g n}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

variable (progress : ∀ i j, g.HasArc i j → rank i < rank j)
variable (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
variable (spec : ParentSpec g (W.vertex R.source) parent)

private abbrev BlockVertex
    (R : Runtime g.vertexCount n k B E) (W : World g n) (d : Fin n) :=
  SiblingVertex g (W.vertex R.source) (W.vertex d)

structure BothTables (R : Runtime g.vertexCount n k B E) (W : World g n)
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (spec : ParentSpec g (W.vertex R.source) parent) : Prop where
  intervals : Contracts R W
  vertexInj : Function.Injective W.vertex
  translateSome : ∀ z i,
    (R.fetch (.translate z)).value = some i ↔ W.vertex i = z
  translateNone : ∀ z,
    (R.fetch (.translate z)).value = none ↔
      ¬ g.InitiallyReachable (W.vertex R.source) z
  treeInterval : ∀ i j, W.Inside i j ↔
    Ancestor parent (W.vertex i) (W.vertex j)
  domInterval : ∀ i j, W.Inside i j ↔
    g.Dominates (W.vertex R.source) (W.vertex i) (W.vertex j)
  lca : ∀ a b d, (R.fetch (.lca a b)).value = d ↔
    ∀ c : Fin g.vertexCount,
      (g.Dominates (W.vertex R.source) c (W.vertex a) ∧
       g.Dominates (W.vertex R.source) c (W.vertex b)) ↔
      g.Dominates (W.vertex R.source) c (W.vertex d)
  childDomain : ∀ d x,
    (∃ u, (R.fetch (.child d x)).value = some u) ↔
      (W.vertex x ≠ W.vertex d ∧
        ∃ Z : BlockVertex R W d, Z.val = W.vertex x)
  childOutside : ∀ d x, (R.fetch (.child d x)).value = none ↔
    W.vertex x = W.vertex d ∨
      ¬ g.Dominates (W.vertex R.source) (W.vertex d) (W.vertex x)
  childLabel : ∀ d x u, (R.fetch (.child d x)).value = some u →
    u ≠ d ∧ parent (W.vertex u) = W.vertex d ∧
      Ancestor parent (W.vertex u) (W.vertex x)
  childFiber : ∀ (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    {x x' u u' : Fin n} {Z Z' : BlockVertex R W d},
    Z.val = W.vertex x → Z'.val = W.vertex x' →
    (R.fetch (.child d x)).value = some u →
    (R.fetch (.child d x')).value = some u' →
    let S := siblingBlockSystem progress injRank spec hd
    let ix := fun T : BlockVertex R W d =>
      encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d)
        parent (S.block T)
    (u = u' ↔ S.block Z = S.block Z') ∧ (u = u' ↔ ix Z = ix Z')

private abbrev PairFailure (a b z : Fin g.vertexCount) :=
  z = a ∨ z = b

private theorem fails_pair (a b : Fin g.vertexCount) :
    Fails (some a) (some b) = PairFailure a b := by
  funext z
  apply propext
  simp [Fails, PairFailure]

private theorem goal_pair (a b : Fin n) (t : Fin g.vertexCount) :
    Goal R W (some (W.vertex a)) (some (W.vertex b)) t ↔
      g.SurvivingPath (PairFailure (W.vertex a) (W.vertex b))
        (W.vertex R.source) t := by
  change g.SurvivingPath (Fails (some (W.vertex a)) (some (W.vertex b)))
    (W.vertex R.source) t ↔ _
  rw [fails_pair]

/-- `A,C` are in paper cut order; `a,b,u,v` are in query order. -/
structure BothThirdInput (d u v a b x y : Fin n) : Prop where
  firstChild : (R.fetch (.child d a)).value = some u
  secondChild : (R.fetch (.child d b)).value = some v
  targetChild : (R.fetch (.child d x)).value = some y
  distinct : u ≠ v
  otherFirst : y ≠ u
  otherSecond : y ≠ v
  targetReachable : g.InitiallyReachable (W.vertex R.source) (W.vertex x)
  targetAlive : ¬ PairFailure (W.vertex a) (W.vertex b) (W.vertex x)
  paper :
    ∃ hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d),
      let Q := finiteSiblingQuotient progress injRank spec hd
      let S := siblingBlockSystem progress injRank spec hd
      let ix := fun Z : BlockVertex R W d =>
        encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d)
          parent (S.block Z)
      ∃ (A C Z : BlockVertex R W d) (J : CutPair Q),
        ((A.val = W.vertex a ∧ C.val = W.vertex b) ∨
         (A.val = W.vertex b ∧ C.val = W.vertex a)) ∧
        Z.val = W.vertex x ∧
        J.fst = ix A ∧ J.snd = ix C ∧
        ix Z ≠ J.fst ∧ ix Z ≠ J.snd ∧
        LastExitTestBranches progress injRank spec hd J A C
          (PairFailure (W.vertex a) (W.vertex b))

/-- The branch witness lives in `Prop`, so its proof can unpack
the existential witnesses supplied by `last_exit_test`. -/
inductive BothRouteValue (a b : Fin n) (t : Fin g.vertexCount)
    (l : Leaf n k) : Prop where
  | no (tag : l = .failedSource ∨ l = .unreachableTarget ∨ l = .failedTarget)
      (dead : ¬ Goal R W (some (W.vertex a)) (some (W.vertex b)) t)
  | yes (tag : l = .outside)
      (live : Goal R W (some (W.vertex a)) (some (W.vertex b)) t)
  | withinFirst (x : Fin n) (target : W.vertex x = t)
      (tag : l = .withinLeft a x)
      (criterion : Goal R W (some (W.vertex a)) (some (W.vertex b)) t ↔
        ¬ W.Inside a x)
  | withinSecond (x : Fin n) (target : W.vertex x = t)
      (tag : l = .withinRight b x)
      (criterion : Goal R W (some (W.vertex a)) (some (W.vertex b)) t ↔
        ¬ W.Inside b x)
  | third (d u v x y : Fin n) (target : W.vertex x = t)
      (tag : l = ((routeThird d u v a b y).run R).value)
      (input : BothThirdInput (R := R) (W := W)
        progress injRank spec d u v a b x y)

/-- The third arm exposes the cut and the actual table results. It does
not assert that the third-block tables implement the exit test. -/
theorem bothReachable_split
    (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic) (a b : Fin n)
    (ab : ¬ Ancestor parent (W.vertex a) (W.vertex b))
    (ba : ¬ Ancestor parent (W.vertex b) (W.vertex a))
    (t : Fin g.vertexCount) :
    BothRouteValue (R := R) (W := W) progress injRank spec a b t
      ((route R.source (some (W.vertex a)) (some (W.vertex b)) t).run R).value := by
  classical
  let r := W.vertex R.source
  let F := PairFailure (W.vertex a) (W.vertex b)
  let l := ((route R.source (some (W.vertex a)) (some (W.vertex b)) t).run R).value
  change BothRouteValue (R := R) (W := W) progress injRank spec a b t l
  have ta := (T.translateSome (W.vertex a) a).2 rfl
  have tb := (T.translateSome (W.vertex b) b).2 rfl
  have retainedReach (i : Fin n) : g.InitiallyReachable r (W.vertex i) := by
    apply Classical.byContradiction
    intro h
    have hn := (T.translateNone (W.vertex i)).2 h
    rw [(T.translateSome (W.vertex i) i).2 rfl] at hn
    cases hn
  have mappedFailure (i : Fin n) :
      F (W.vertex i) ↔ Fails (some a) (some b) i := by
    change (W.vertex i = W.vertex a ∨ W.vertex i = W.vertex b) ↔ _
    simp only [Fails, Option.some.injEq]
    constructor
    · rintro (ha | hb)
      · exact Or.inl (T.vertexInj ha)
      · exact Or.inr (T.vertexInj hb)
    · rintro (ha | hb)
      · exact Or.inl (congrArg W.vertex ha)
      · exact Or.inr (congrArg W.vertex hb)
  have route0 : l =
      ((routeRetained R.source (some a) (some b)
        (R.fetch (.translate t)).value).run R).value := by
    simp only [l, route, withID, Plan.run, ta, tb]
  have goalF (z : Fin g.vertexCount) :
      Goal R W (some (W.vertex a)) (some (W.vertex b)) z ↔
        g.SurvivingPath F r z :=
    goal_pair (R := R) (W := W) a b z

  by_cases hs : Fails (some a) (some b) R.source
  · refine .no (Or.inl ?_) ?_
    · rw [route0]
      simp [routeRetained, Plan.run, hs]
    · intro p
      exact AvoidPath.source_alive ((goalF t).1 p) ((mappedFailure R.source).2 hs)

  have paper := last_exit_test (rank := rank) acyclic progress injRank spec ab ba
  dsimp only at paper
  obtain ⟨initial, _, _, _, both⟩ := paper
  cases tx : (R.fetch (.translate t)).value with
  | none =>
    refine .no (Or.inr (Or.inl ?_)) ?_
    · rw [route0, tx]
      simp [routeRetained, Plan.run, hs]
    · intro p
      exact (T.translateNone t).1 tx (initial t ((goalF t).1 p))
  | some x =>
    have xt := (T.translateSome t x).1 tx
    by_cases hx : Fails (some a) (some b) x
    · refine .no (Or.inr (Or.inr ?_)) ?_
      · rw [route0, tx]
        simp [routeRetained, Plan.run, hs, hx]
      · intro p
        have q := (goalF t).1 p
        have live : ¬ F t := by
          first
          | exact AvoidPath.target_alive q
          | exact AvoidPath.dest_alive q
          | change AvoidPath g.HasArc F r t at q
            induction q <;> first | assumption | solve_by_elim | grind
        exact live (xt ▸ (mappedFailure x).2 hx)

    have xlive : ¬ F (W.vertex x) := fun h => hx ((mappedFailure x).1 h)
    have routed : l = ((routePair a b x).run R).value := by
      rw [route0, tx]
      simp [routeRetained, hs, hx]

    obtain ⟨D, hD, common, A, C, J, order, keyA, keyC, branches⟩ :=
      both (retainedReach a) (retainedReach b)
    have dRet : ∃ d, W.vertex d = D := by
      cases td : (R.fetch (.translate D)).value with
      | none => exact False.elim ((T.translateNone D).1 td hD)
      | some d => exact ⟨d, (T.translateSome D d).1 td⟩
    obtain ⟨d, deq⟩ := dRet
    subst D
    have ld := (T.lca a b d).2 common
    have tableFalse (i j : Fin n)
        (h : ¬ Ancestor parent (W.vertex i) (W.vertex j)) :
        (R.fetch (.ancestor i j)).value = false := by
      change (R.ancestor i j).value = false
      cases e : (R.ancestor i j).value with
      | false => rfl
      | true =>
        exact False.elim (h ((T.treeInterval i j).1
          ((T.intervals.ancestor i j).1 e)))
    have blocks : l = ((routeBlocks d a b x).run R).value := by
      rw [routed]
      simp [routePair, Plan.run, tableFalse a b ab, tableFalse b a ba, ld]

    let S := siblingBlockSystem progress injRank spec hD
    let ix := fun Z : BlockVertex R W d =>
      encodeSiblingBlockKey g r (W.vertex d) parent (S.block Z)
    have ka : J.fst = ix A := keyA
    have kc : J.snd = ix C := keyC

    -- Keep the folded proof for the third arm and project from a copy.
    have clauses := branches
    unfold LastExitTestBranches at clauses
    have outside (z : Fin g.vertexCount)
        (hz : g.InitiallyReachable r z)
        (hout : ¬ Ancestor parent (W.vertex d) z) :
        g.SurvivingPath F r z :=
      clauses.1 z hz hout
    have atLca : g.SurvivingPath F r (W.vertex d) := clauses.2.1
    have own (Z K : BlockVertex R W d) (side : K = A ∨ K = C)
        (same : S.block Z = S.block K) :
        g.SurvivingPath F r Z.val ↔ ¬ g.Dominates r K.val Z.val := by
      rcases side with h | h
      · subst K
        exact clauses.2.2.1 Z same
      · subst K
        exact clauses.2.2.2.1 Z same

    obtain ⟨U, V, eqU, eqV, perm⟩ :
        ∃ U V : BlockVertex R W d,
          U.val = W.vertex a ∧ V.val = W.vertex b ∧
          ((U = A ∧ V = C) ∨ (U = C ∧ V = A)) := by
      rcases order with h | h
      · exact ⟨A, C, h.1, h.2, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨C, A, h.2, h.1, Or.inr ⟨rfl, rfl⟩⟩
    have commonAtD := (common (W.vertex d)).2
      (show g.Dominates r (W.vertex d) (W.vertex d) from dominates_refl)
    have aNeD : W.vertex a ≠ W.vertex d := by
      intro h
      apply ab
      apply (T.treeInterval a b).1
      apply (T.domInterval a b).2
      rw [h]
      exact commonAtD.2
    have bNeD : W.vertex b ≠ W.vertex d := by
      intro h
      apply ba
      apply (T.treeInterval b a).1
      apply (T.domInterval b a).2
      rw [h]
      exact commonAtD.1
    obtain ⟨u, cu⟩ := (T.childDomain d a).2 ⟨aNeD, ⟨U, eqU⟩⟩
    obtain ⟨v, cv⟩ := (T.childDomain d b).2 ⟨bNeD, ⟨V, eqV⟩⟩

    have differentKeys : J.fst ≠ J.snd := by
      first
      | exact J.ne
      | exact J.fst_ne_snd
      | exact J.distinct
      | cases J <;> first | assumption | omega | grind
    have diffUV : u ≠ v := by
      intro e
      have eqK : ix U = ix V :=
        (T.childFiber d hD (Z := U) (Z' := V) eqU eqV cu cv).2.1 e
      apply differentKeys
      rw [ka, kc]
      rcases perm with h | h
      · rwa [h.1, h.2] at eqK
      · rw [h.1, h.2] at eqK
        exact eqK.symm
    have diffVU : v ≠ u := Ne.symm diffUV

    cases cy : (R.fetch (.child d x)).value with
    | none =>
      have alive : g.SurvivingPath F r (W.vertex x) := by
        rcases (T.childOutside d x).1 cy with heq | hnd
        · rw [heq]
          exact atLca
        · apply outside (W.vertex x) (retainedReach x)
          intro ha
          exact hnd ((T.domInterval d x).1 ((T.treeInterval d x).2 ha))
      refine .yes ?_ ((goalF t).2 (xt ▸ alive))
      rw [blocks]
      simp [routeBlocks, Plan.run, *]
    | some y =>
      obtain ⟨Z, eqZ⟩ := ((T.childDomain d x).1 ⟨y, cy⟩).2
      have fiberU := T.childFiber d hD (Z := Z) (Z' := U) eqZ eqU cy cu
      have fiberV := T.childFiber d hD (Z := Z) (Z' := V) eqZ eqV cy cv
      have transport (i : Fin n) (K : BlockVertex R W d)
          (ki : K.val = W.vertex i)
          (h : g.SurvivingPath F r Z.val ↔ ¬ g.Dominates r K.val Z.val) :
          Goal R W (some (W.vertex a)) (some (W.vertex b)) t ↔
            ¬ W.Inside i x := by
        rw [eqZ, ki, ← (T.domInterval i x)] at h
        exact (goalF t).trans (xt ▸
          (show g.SurvivingPath F r (W.vertex x) ↔ ¬ W.Inside i x from h))
      by_cases yu : y = u
      · have side : U = A ∨ U = C :=
          perm.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
        refine .withinFirst x xt ?_
          (transport a U eqU (own Z U side (fiberU.1.1 yu)))
        rw [blocks]
        simp [routeBlocks, Plan.run, *]
      · have uy : u ≠ y := Ne.symm yu
        by_cases yv : y = v
        · have side : V = A ∨ V = C :=
            perm.elim (fun h => Or.inr h.2) (fun h => Or.inl h.2)
          refine .withinSecond x xt ?_
            (transport b V eqV (own Z V side (fiberV.1.1 yv)))
          rw [blocks]
          simp [routeBlocks, Plan.run, *]
        · have vy : v ≠ y := Ne.symm yv
          have noU : ix Z ≠ ix U := fun h => yu (fiberU.2.2 h)
          have noV : ix Z ≠ ix V := fun h => yv (fiberV.2.2 h)
          have noA : ix Z ≠ J.fst := by
            rw [ka]
            rcases perm with h | h
            · rwa [h.1] at noU
            · rwa [h.2] at noV
          have noC : ix Z ≠ J.snd := by
            rw [kc]
            rcases perm with h | h
            · rwa [h.2] at noV
            · rwa [h.1] at noU
          refine .third d u v x y xt ?_
            ⟨cu, cv, cy, diffUV, yu, yv, retainedReach x, xlive, ?_⟩
          · have hyu : y ≠ u := yu
            have hyv : y ≠ v := yv
            rw [blocks]
            simp only [routeBlocks, Plan.run, cu, cv, cy, if_neg hyu, if_neg hyv]
          · exact ⟨hD, A, C, Z, J, order, eqZ, ka, kc, noA, noC, branches⟩

end PaperB.EX44
