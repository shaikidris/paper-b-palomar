module

public import PaperB.DominatorChain

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Paper B EX1.3: semantic entry and within-subtree paths. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

variable {g : Digraph} {r d u v : Fin g.vertexCount}

/-- A reachable predecessor of a dominated vertex is dominated unless the
target is `d` itself. Reachability of the target need not be assumed separately. -/
theorem dominates_reachable_predecessor_of_ne
    (arc : g.HasArc u v) (hu : g.InitiallyReachable r u)
    (hne : v ≠ d) (hdom : g.Dominates r d v) :
    g.Dominates r d u := by
  by_cases hvr : v = r
  · subst v
    have hdr : d = r := (dominates_source_iff (g := g)).mp hdom
    exact False.elim (hne hdr.symm)
  · have hdv : d ≠ v := fun he => hne he.symm
    exact ((dominates_iff_reachable_predecessors (g := g) hvr hdv).mp hdom)
      u arc hu

/-- An arc from a reachable vertex outside the dominator subtree to a
reachable vertex inside it can enter only at `d`. -/
theorem eq_dominator_of_entering_subtree
    (arc : g.HasArc u v)
    (hu : g.InitiallyReachable r u) (_hv : g.InitiallyReachable r v)
    (hdom : g.Dominates r d v) (hnot : ¬ g.Dominates r d u) :
    v = d := by
  by_cases h : v = d
  · exact h
  · exact False.elim (hnot (dominates_reachable_predecessor_of_ne arc hu h hdom))

variable {rank : Fin g.vertexCount → Nat}

/-- Starting at a reachable vertex of rank at least `rank d`, a path to a
dominated endpoint stays in the reachable dominator subtree. The proof
rebuilds the same path with the stronger failure predicate. -/
theorem dominates_and_stays_in_subtree_of_rank_le
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop}
    (path : AvoidPath g.HasArc failed u v) :
    g.InitiallyReachable r u → rank d ≤ rank u → g.Dominates r d v →
      g.Dominates r d u ∧
        g.SurvivingPath
          (fun x => failed x ∨ ¬ (g.InitiallyReachable r x ∧ g.Dominates r d x))
          u v := by
  induction path with
  | refl u alive =>
      intro hu _ hdom
      exact ⟨hdom, AvoidPath.refl u
        (fun h => h.elim alive (fun hnot => hnot ⟨hu, hdom⟩))⟩
  | step u w v alive arc _ ih =>
      intro hu hle hdom
      have hOne : g.InitiallyReachable u w :=
        AvoidPath.step (failed := fun _ => False) u w w (fun h => h) arc
          (AvoidPath.refl (failed := fun _ => False) w (fun h => h))
      have hw : g.InitiallyReachable r w := AvoidPath.trans hu hOne
      have hlt : rank d < rank w := Nat.lt_of_le_of_lt hle (progress u w arc)
      rcases ih hw (Nat.le_of_lt hlt) hdom with ⟨hdomw, hTail⟩
      have hwd : w ≠ d := fun he =>
        Nat.ne_of_lt hlt (congrArg rank he.symm)
      have hdomu : g.Dominates r d u :=
        dominates_reachable_predecessor_of_ne arc hu hwd hdomw
      exact ⟨hdomu, AvoidPath.step u w v
        (fun h => h.elim alive (fun hnot => hnot ⟨hu, hdomu⟩)) arc hTail⟩

/-- A surviving `d`-to-`v` path to a reachable dominated endpoint can also
avoid the complement of the dominator subtree, without dropping any of its
original failures. Strict increase along arcs suffices; ranks need not be
injective. -/
theorem survivingPath_within_dominator_subtree
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop}
    (hv : g.InitiallyReachable r v) (hdom : g.Dominates r d v)
    (path : g.SurvivingPath failed d v) :
    g.SurvivingPath
      (fun x => failed x ∨ ¬ (g.InitiallyReachable r x ∧ g.Dominates r d x))
      d v :=
  (dominates_and_stays_in_subtree_of_rank_le (r := r) (d := d) progress path
    (initiallyReachable_of_dominates hv hdom) (Nat.le_refl (rank d)) hdom).2

end PaperB.Digraph
