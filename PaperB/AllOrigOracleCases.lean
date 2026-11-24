module

public import PaperB.ThirdReachableRoute

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.EX44

open PaperB.Digraph PaperB.Digraph.EX44
open RetainedRouteProof

variable {g : PaperB.Digraph} {N n k B E : Nat}
variable {R : Runtime g.vertexCount n k B E} {W : World g n}

private theorem fails_eq_simple (p q : Option (Fin g.vertexCount)) :
    Fails p q = fails p q := by
  funext x
  apply propext
  change (some x = p ∨ some x = q) ↔ (hit p x ∨ hit q x)
  cases p <;> cases q <;> simp [hit]

private theorem translated_fails
    (I : NormalizedIDs R W) (p q : Option (Fin g.vertexCount)) (x : Fin n) :
    Fails (idAt R p) (idAt R q) x ↔ fails p q (W.vertex x) := by
  have coordinate (i : Option (Fin g.vertexCount)) :
      some x = idAt R i ↔ hit i (W.vertex x) := by
    cases i with
    | none =>
      change (some x = none) ↔ False
      simp
    | some z =>
      change (some x = idAt R (some z)) ↔ W.vertex x = z
      exact ⟨fun h => (I.present z x).mp h.symm,
        fun h => ((I.present z x).mpr h).symm⟩
  exact or_congr (coordinate p) (coordinate q)

private theorem translated_some_reachable
    (I : NormalizedIDs R W) {z : Fin g.vertexCount} {x : Fin n}
    (h : idAt R (some z) = some x) :
    g.InitiallyReachable (W.vertex R.source) z := by
  apply Classical.byContradiction
  intro dead
  have hn := (I.absent z).mpr dead
  rw [h] at hn
  cases hn

private theorem original_of_translated_some
    (I : NormalizedIDs R W) {p : Option (Fin g.vertexCount)} {x : Fin n}
    (h : idAt R p = some x) :
    p = some (W.vertex x) := by
  cases p with
  | none =>
    change none = some x at h
    cases h
  | some z =>
    exact congrArg some (((I.present z x).mp h).symm)

private theorem keep_eq_translated_map
    [∀ z, Decidable (g.InitiallyReachable (W.vertex R.source) z)]
    (I : NormalizedIDs R W) (p : Option (Fin g.vertexCount)) :
    keep g (W.vertex R.source) p = (idAt R p).map W.vertex := by
  cases p with
  | none => rfl
  | some z =>
    cases h : idAt R (some z) with
    | none =>
      simp only [keep, if_neg ((I.absent z).mp h), h, Option.map]
    | some x =>
      have hz := translated_some_reachable I h
      have hv := (I.present z x).mp h
      simp only [keep, if_pos hz, h, Option.map, hv]

private theorem original_goal_iff_simple
    (p q : Option (Fin g.vertexCount)) (t : Fin g.vertexCount) :
    Goal R W p q t ↔ g.SurvivingPath (fails p q) (W.vertex R.source) t := by
  change g.SurvivingPath (Fails p q) (W.vertex R.source) t ↔ _
  rw [fails_eq_simple p q]

private theorem original_goal_iff_kept
    (I : NormalizedIDs R W) (p q : Option (Fin g.vertexCount))
    (t : Fin g.vertexCount) :
    Goal R W p q t ↔
      g.SurvivingPath
        (fails ((idAt R p).map W.vertex) ((idAt R q).map W.vertex))
        (W.vertex R.source) t := by
  classical
  rw [← keep_eq_translated_map I p, ← keep_eq_translated_map I q]
  exact (original_goal_iff_simple (R := R) (W := W) p q t).trans
    (keep_path_iff g (W.vertex R.source) t p q).symm

private def liveRetainedLeaf (S : Runtime N n k B E)
    (a b : Option (Fin n)) (x : Fin n) : Leaf n k :=
  match a, b with
  | none, none => .zero
  | some u, none => .oneFirst u x
  | none, some v => .oneSecond v x
  | some u, some v => ((routePair u v x).run S).value

private theorem routeRetained_live_value
    (S : Runtime N n k B E) (r x : Fin n) (a b : Option (Fin n))
    (hs : ¬ Fails a b r) (ht : ¬ Fails a b x) :
    ((routeRetained r a b (some x)).run S).value =
      liveRetainedLeaf S a b x := by
  simp only [routeRetained, if_neg hs, if_neg ht] <;>
    cases a <;> cases b <;> rfl

private theorem routePair_left_value
    (S : Runtime N n k B E) (a b x : Fin n)
    (hab : (S.ancestor a b).value = true) :
    ((routePair a b x).run S).value = .comparableLeft a x := by
  have h : (S.fetch (.ancestor a b)).value = true := hab
  simp [routePair, Plan.run, h]

private theorem routePair_right_value
    (S : Runtime N n k B E) (a b x : Fin n)
    (hab : (S.ancestor a b).value = false)
    (hba : (S.ancestor b a).value = true) :
    ((routePair a b x).run S).value = .comparableRight b x := by
  have h₁ : (S.fetch (.ancestor a b)).value = false := hab
  have h₂ : (S.fetch (.ancestor b a)).value = true := hba
  simp [routePair, Plan.run, h₁, h₂]

/-- The executable answer agrees with the surviving-path query on the original
IDs. Only two translated failures with both ancestor bits false use the
quotient and direct third-table laws. -/
theorem original_routed_answer_correct_direct
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (spec : ParentSpec g (W.vertex R.source) parent)
    (D : DirectThirdTables (R := R) (W := W) progress injRank spec)
    (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic)
    (p q : Option (Fin g.vertexCount)) (t : Fin g.vertexCount) :
    ((answer ((route R.source p q t).run R).value).run R).value = true ↔
      Goal R W p q t := by
  have I : NormalizedIDs R W :=
    ⟨fun z x => T.translateSome z x, fun z => T.translateNone z⟩
  have original := original_goal_iff_simple (R := R) (W := W) p q t
  have kept {a b : Option (Fin n)}
      (ha : idAt R p = a) (hb : idAt R q = b) :
      Goal R W p q t ↔
        g.SurvivingPath (fails (a.map W.vertex) (b.map W.vertex))
          (W.vertex R.source) t := by
    simpa only [ha, hb] using original_goal_iff_kept I p q t
  have finish (l : Leaf n k)
      (hl : ((route R.source p q t).run R).value = l)
      (hc : LeafContract R W p q t l) :
      ((answer ((route R.source p q t).run R).value).run R).value = true ↔
        Goal R W p q t := by
    rw [hl]
    exact answer_correct T.intervals l hc
  by_cases hs : Fails (idAt R p) (idAt R q) R.source
  · refine finish .failedSource ?_ ?_
    · rw [route_value]
      simp only [routeRetained, if_pos hs, Plan.run, Plan.stop]
    · have hf := (translated_fails I p q R.source).mp hs
      exact fun path => failed_source (g := g) hf (original.mp path)
  · cases hx : idAt R (some t) with
    | none =>
      refine finish .unreachableTarget ?_ ?_
      · rw [route_value]
        simp only [routeRetained, if_neg hs, hx, Plan.run, Plan.stop]
      · exact fun path =>
          initially_unreachable_target (g := g) ((I.absent t).mp hx)
            (original.mp path)
    | some x =>
      have hxt := (I.present t x).mp hx
      by_cases ht : Fails (idAt R p) (idAt R q) x
      · refine finish .failedTarget ?_ ?_
        · rw [route_value, hx]
          simp only [routeRetained, if_neg hs, if_pos ht, Plan.run, Plan.stop]
        · have hf : fails p q t := by
            simpa only [hxt] using (translated_fails I p q x).mp ht
          exact fun path => failed_target (g := g) hf (original.mp path)
      · have liveRoute :
            ((route R.source p q t).run R).value =
              liveRetainedLeaf R (idAt R p) (idAt R q) x := by
          rw [route_value, hx]
          exact routeRetained_live_value R R.source x _ _ hs ht
        have notDom (u : Fin n) :
            (¬ g.Dominates (W.vertex R.source) (W.vertex u) t) ↔
              ¬ W.Inside u x := by
          simpa only [hxt] using not_congr (T.domInterval u x).symm
        have deleteOne (u : Fin n) :
            g.SurvivingPath (fun z => z = W.vertex u) (W.vertex R.source) t ↔
              ¬ W.Inside u x :=
          (delete_one_iff_not_dominates (g := g) (v := t)
            (W.vertex u)).trans (notDom u)
        cases ha : idAt R p with
        | none =>
          cases hb : idAt R q with
          | none =>
            refine finish .zero ?_ ?_
            · simpa only [ha, hb, liveRetainedLeaf] using liveRoute
            · exact (kept ha hb).mpr
                ((zero_failures (g := g)).mpr (translated_some_reachable I hx))
          | some b =>
            refine finish (.oneSecond b x) ?_ ?_
            · simpa only [ha, hb, liveRetainedLeaf] using liveRoute
            · exact (kept ha hb).trans
                ((one_failure_right (g := g) (v := t) (W.vertex b)).trans
                  (notDom b))
        | some a =>
          cases hb : idAt R q with
          | none =>
            refine finish (.oneFirst a x) ?_ ?_
            · simpa only [ha, hb, liveRetainedLeaf] using liveRoute
            · exact (kept ha hb).trans
                ((one_failure_left (g := g) (v := t) (W.vertex a)).trans
                  (notDom a))
          | some b =>
            have pairRoute :
                ((route R.source p q t).run R).value =
                  ((routePair a b x).run R).value := by
              simpa only [ha, hb, liveRetainedLeaf] using liveRoute
            have domBit (u v : Fin n) :
                (R.ancestor u v).value = true ↔
                  g.Dominates (W.vertex R.source) (W.vertex u) (W.vertex v) :=
              (T.intervals.ancestor u v).trans (T.domInterval u v)
            have treeBit (u v : Fin n) :
                (R.ancestor u v).value = true ↔
                  Ancestor parent (W.vertex u) (W.vertex v) :=
              (T.intervals.ancestor u v).trans (T.treeInterval u v)
            cases hab : (R.ancestor a b).value with
            | true =>
              -- This includes duplicate failures: reflexive dominance sets
              -- the first bit, so the code takes the left branch.
              refine finish (.comparableLeft a x)
                (pairRoute.trans (routePair_left_value R a b x hab)) ?_
              exact (kept ha hb).trans
                ((pair_iff_delete_left (g := g) (v := t)
                  ((domBit a b).mp hab)).trans (deleteOne a))
            | false =>
              cases hba : (R.ancestor b a).value with
              | true =>
                refine finish (.comparableRight b x)
                  (pairRoute.trans (routePair_right_value R a b x hab hba)) ?_
                exact (kept ha hb).trans
                  ((pair_iff_delete_right (g := g) (v := t)
                    ((domBit b a).mp hba)).trans (deleteOne b))
              | false =>
                have ab : ¬ Ancestor parent (W.vertex a) (W.vertex b) := by
                  intro h
                  have bad := hab.symm.trans ((treeBit a b).mpr h)
                  cases bad
                have ba : ¬ Ancestor parent (W.vertex b) (W.vertex a) := by
                  intro h
                  have bad := hba.symm.trans ((treeBit b a).mpr h)
                  cases bad
                rw [original_of_translated_some I ha, original_of_translated_some I hb]
                exact both_routed_answer_correct_direct progress injRank spec D T
                  acyclic a b ab ba t

/-- The all-case correctness theorem for legacy third-forest tables. -/
theorem original_routed_answer_correct
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (spec : ParentSpec g (W.vertex R.source) parent)
    {G : ThirdForestGeometry R W progress injRank spec}
    (D : ThirdForestTables progress injRank spec G)
    (T : BothTables R W progress injRank spec)
    (acyclic : g.IsAcyclic)
    (p q : Option (Fin g.vertexCount)) (t : Fin g.vertexCount) :
    ((answer ((route R.source p q t).run R).value).run R).value = true ↔
      Goal R W p q t :=
  original_routed_answer_correct_direct progress injRank spec
    (ThirdForestTables.toDirect (progress := progress) (injRank := injRank) (spec := spec) D)
    T acyclic p q t

end PaperB.EX44
