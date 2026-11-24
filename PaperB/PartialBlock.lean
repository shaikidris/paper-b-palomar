module

public import PaperB.SiblingBlocks
public import PaperB.DominatorBoundary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

private theorem lemma22_avoid_of_no_failed_prefix
    {V : Type} {arc : V → V → Prop} {oldFailed failed : V → Prop}
    {s t : V} (path : AvoidPath arc oldFailed s t) :
    (∀ x, failed x → ¬ AvoidPath arc oldFailed s x) →
      AvoidPath arc failed s t := by
  induction path with
  | refl x hx =>
      intro h
      exact AvoidPath.refl x (fun hf => h x hf (AvoidPath.refl x hx))
  | step x y z hx hxy _ ih =>
      intro h
      exact AvoidPath.step x y z
        (fun hf => h x hf (AvoidPath.refl x hx)) hxy
        (ih (fun w hf hp => h w hf (AvoidPath.step x y w hx hxy hp)))

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

private theorem lemma22_rank_le_of_path
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop} {s t : Fin g.vertexCount}
    (path : AvoidPath g.HasArc failed s t) :
    rank s ≤ rank t := by
  induction path with
  | refl x _ =>
      exact Nat.le_refl (rank x)
  | step x y _ _ hxy _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (progress x y hxy)) ih

/-- A DAG path already avoids every vertex ranked strictly after its target. -/
private theorem lemma22_avoid_of_rank
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {oldFailed failed : Fin g.vertexCount → Prop} {s t : Fin g.vertexCount}
    (path : AvoidPath g.HasArc oldFailed s t) :
    (∀ x, failed x → oldFailed x ∨ rank t < rank x) →
      AvoidPath g.HasArc failed s t := by
  induction path with
  | refl x hx =>
      intro h
      exact AvoidPath.refl x
        (fun hf => (h x hf).elim hx (Nat.lt_irrefl (rank x)))
  | step x y z hx hxy tail ih =>
      intro h
      have hxz : rank x < rank z :=
        Nat.lt_of_lt_of_le (progress x y hxy)
          (lemma22_rank_le_of_path progress tail)
      refine AvoidPath.step x y z ?_ hxy (ih h)
      intro hf
      rcases h x hf with ho | hz
      · exact hx ho
      · exact Nat.lt_irrefl (rank x) (Nat.lt_trans hxz hz)

/-- OUTSIDE: a retained target outside the subtree at `d` survives failures
in that subtree. This part does not require strict descent. -/
theorem lemma22_outside
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (spec : ParentSpec g r parent)
    {a b t : Fin g.vertexCount}
    (ha : g.InitiallyReachable r a) (hb : g.InitiallyReachable r b)
    (ht : g.InitiallyReachable r t)
    (hda : Ancestor parent d a) (hdb : Ancestor parent d b)
    (hout : ¬ Ancestor parent d t) :
    g.SurvivingPath (fun x => x = a ∨ x = b) r t := by
  have hDomA : g.Dominates r d a :=
    (ancestor_iff_dominates progress spec ha).1 hda
  have hDomB : g.Dominates r d b :=
    (ancestor_iff_dominates progress spec hb).1 hdb
  have hpath : g.SurvivingPath (fun x => x = d) r t := by
    apply Classical.byContradiction
    intro h
    exact hout ((ancestor_iff_dominates progress spec ht).2 h)
  change AvoidPath g.HasArc (fun x => x = a ∨ x = b) r t
  refine lemma22_avoid_of_no_failed_prefix hpath ?_
  intro x hx
  rcases hx with h | h
  · subst x
    exact hDomA
  · subst x
    exact hDomB

/-- OUTSIDE at the subtree root: both strict descendants follow `d` in
topological order, so neither can occur on a source-to-`d` path. -/
theorem lemma22_at_d
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (spec : ParentSpec g r parent)
    {a b : Fin g.vertexCount}
    (hd : g.InitiallyReachable r d)
    (ha : g.InitiallyReachable r a) (hb : g.InitiallyReachable r b)
    (hda : Ancestor parent d a) (hdb : Ancestor parent d b)
    (hdaNe : d ≠ a) (hdbNe : d ≠ b) :
    g.SurvivingPath (fun x => x = a ∨ x = b) r d := by
  have hRankA : rank d < rank a :=
    rank_lt_of_strict_dominator progress ha
      ((ancestor_iff_dominates progress spec ha).1 hda) hdaNe
  have hRankB : rank d < rank b :=
    rank_lt_of_strict_dominator progress hb
      ((ancestor_iff_dominates progress spec hb).1 hdb) hdbNe
  change AvoidPath g.HasArc (fun x => x = a ∨ x = b) r d
  refine lemma22_avoid_of_rank progress
    (oldFailed := fun _ => False) hd ?_
  intro x hx
  rcases hx with h | h
  · subst x
    exact Or.inr hRankA
  · subst x
    exact Or.inr hRankB

private theorem lemma22_own_subtree
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {u a b t : Fin g.vertexCount}
    (ha : g.InitiallyReachable r a) (ht : g.InitiallyReachable r t)
    (hua : g.Dominates r u a) (hut : g.Dominates r u t)
    (hub : ¬ g.Dominates r u b) (hbu : ¬ g.Dominates r b u) :
    g.SurvivingPath (fun x => x = a ∨ x = b) r t ↔
      ¬ g.Dominates r a t := by
  constructor
  · intro path hdom
    exact hdom (AvoidPath.mono path (fun _ hx => Or.inl hx))
  · intro hNotDom
    have hAvoidA : g.SurvivingPath (fun x => x = a) r t :=
      Classical.byContradiction hNotDom
    have huaNe : u ≠ a := by
      intro he
      apply hNotDom
      simpa only [he] using hut
    have hRankA : rank u < rank a :=
      rank_lt_of_strict_dominator progress ha hua huaNe
    have hAvoidB : g.SurvivingPath (fun x => x = b) r u :=
      Classical.byContradiction hbu
    have hPrefix : g.SurvivingPath (fun x => x = a ∨ x = b) r u := by
      change AvoidPath g.HasArc (fun x => x = a ∨ x = b) r u
      refine lemma22_avoid_of_rank progress
        (oldFailed := fun x => x = b) hAvoidB ?_
      intro x hx
      rcases hx with h | h
      · subst x
        exact Or.inr hRankA
      · exact Or.inl h
    have hSuffixA : g.SurvivingPath (fun x => x = a) u t :=
      survivingPath_suffix_of_dominates hAvoidA hut
    have hInternal := survivingPath_within_dominator_subtree
      (r := r) (d := u) (failed := fun x => x = a)
      progress ht hut hSuffixA
    have hSuffix : g.SurvivingPath (fun x => x = a ∨ x = b) u t := by
      refine AvoidPath.mono hInternal ?_
      intro x hx
      rcases hx with h | h
      · exact Or.inl h
      · subst x
        exact Or.inr (fun hm => hub hm.2)
    exact AvoidPath.trans hPrefix hSuffix

/-- OWN: for a target in `u`'s block, the failure in the distinct sibling
block `v` does not change the single-failure test for `a`. -/
theorem lemma22_own
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent)
    (hd : g.InitiallyReachable r d)
    (u v : SiblingBlockKey g r d parent)
    (hu : u.val ≠ d) (hv : v.val ≠ d) (huv : u ≠ v)
    (a b t : SiblingVertex g r d)
    (ha : siblingBlockOf progress injective spec a = u)
    (hb : siblingBlockOf progress injective spec b = v)
    (ht : siblingBlockOf progress injective spec t = u) :
    g.SurvivingPath (fun x => x = a.val ∨ x = b.val) r t.val ↔
      ¬ g.Dominates r a.val t.val := by
  have hua : g.Dominates r u.val a.val :=
    (siblingBlockOf_eq_child_iff progress injective spec a u hu).1 ha
  have hut : g.Dominates r u.val t.val :=
    (siblingBlockOf_eq_child_iff progress injective spec t u hu).1 ht
  have hub : ¬ g.Dominates r u.val b.val := by
    intro h
    have hOther := (siblingBlockOf_eq_child_iff progress injective spec b u hu).2 h
    exact huv (hOther.symm.trans hb)
  have hbu : ¬ g.Dominates r b.val u.val := by
    intro h
    have hvb : g.Dominates r v.val b.val :=
      (siblingBlockOf_eq_child_iff progress injective spec b v hv).1 hb
    have hvu : g.Dominates r v.val (siblingBlockLeader spec hd u).val :=
      dominates_trans hvb h
    have hOther := (siblingBlockOf_eq_child_iff progress injective spec
      (siblingBlockLeader spec hd u) v hv).2 hvu
    exact huv ((siblingBlockOf_leader progress injective spec hd u).symm.trans hOther)
  exact lemma22_own_subtree progress a.property.1 t.property.1 hua hut hub hbu

/-- OWN for the other sibling block, with the failure predicate unchanged. -/
theorem lemma22_own_right
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent)
    (hd : g.InitiallyReachable r d)
    (u v : SiblingBlockKey g r d parent)
    (hu : u.val ≠ d) (hv : v.val ≠ d) (huv : u ≠ v)
    (a b t : SiblingVertex g r d)
    (ha : siblingBlockOf progress injective spec a = u)
    (hb : siblingBlockOf progress injective spec b = v)
    (ht : siblingBlockOf progress injective spec t = v) :
    g.SurvivingPath (fun x => x = a.val ∨ x = b.val) r t.val ↔
      ¬ g.Dominates r b.val t.val := by
  have hSwap := lemma22_own progress injective spec hd v u hv hu
    (Ne.symm huv) b a t hb ha ht
  constructor
  · intro path
    apply hSwap.mp
    exact AvoidPath.mono path (fun _ hx => hx.elim Or.inr Or.inl)
  · intro h
    exact AvoidPath.mono (hSwap.mpr h) (fun _ hx => hx.elim Or.inr Or.inl)

end PaperB.Digraph
