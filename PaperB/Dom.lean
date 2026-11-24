module

public import PaperB.Graph

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Paper B EX1.2: semantic dominance and predecessor recurrence. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

/-- No path from `r` to `v` avoids `d`. The intended targets are initially
reachable; on other targets this predicate holds vacuously. -/
def Dominates (g : Digraph) (r d v : Fin g.vertexCount) : Prop :=
  ¬ g.SurvivingPath (fun x => x = d) r v

theorem initiallyReachable_of_survivingPath {g : Digraph}
    {failed : Fin g.vertexCount → Prop} {r v : Fin g.vertexCount}
    (path : g.SurvivingPath failed r v) : g.InitiallyReachable r v := by
  show g.SurvivingPath (fun _ => False) r v
  exact AvoidPath.mono path (fun _ h => False.elim h)

private theorem avoid_of_no_path_to {V : Type} {edge : V → V → Prop}
    {failed : V → Prop} {u v d : V} (path : AvoidPath edge failed u v) :
    (¬ AvoidPath edge failed u d) → AvoidPath edge (fun x => x = d) u v := by
  induction path with
  | refl u alive =>
      intro hNo
      refine AvoidPath.refl u (fun he => hNo ?_)
      rw [← he]
      exact AvoidPath.refl u alive
  | step u w v alive arc _ ih =>
      intro hNo
      refine AvoidPath.step u w v ?_ arc (ih ?_)
      · intro he
        apply hNo
        rw [← he]
        exact AvoidPath.refl u alive
      · intro hpre
        exact hNo (AvoidPath.step u w d alive arc hpre)

/- These path laws do not require initial reachability. -/
theorem dominates_refl {g : Digraph} {r v : Fin g.vertexCount} :
    g.Dominates r v v :=
  fun path => AvoidPath.target_alive path rfl

theorem dominates_trans {g : Digraph} {r a b v : Fin g.vertexCount}
    (hab : g.Dominates r a b) (hbv : g.Dominates r b v) :
    g.Dominates r a v :=
  fun path => hbv (avoid_of_no_path_to path hab)

theorem source_dominates {g : Digraph} {r v : Fin g.vertexCount} :
    g.Dominates r r v :=
  fun path => AvoidPath.source_alive path rfl

theorem dominates_source_iff {g : Digraph} {r d : Fin g.vertexCount} :
    g.Dominates r d r ↔ d = r := by
  constructor
  · intro h
    by_cases he : r = d
    · exact he.symm
    · exact False.elim (h (AvoidPath.refl r he))
  · intro he
    subst d
    exact dominates_refl (g := g)

/-- Discarded predecessors cannot supply an avoiding prefix: any such prefix
would witness initial reachability. -/
theorem dominates_predecessors_iff_reachable {g : Digraph}
    {r d v : Fin g.vertexCount} :
    (∀ p, g.HasArc p v → g.Dominates r d p) ↔
      (∀ p, g.HasArc p v → g.InitiallyReachable r p → g.Dominates r d p) := by
  constructor
  · intro h p hp _
    exact h p hp
  · intro h p hp path
    exact h p hp (initiallyReachable_of_survivingPath (g := g) path) path

/-- Predecessor recurrence off the source and the failed endpoint.
The equivalence holds even without initial reachability of `v`. -/
theorem dominates_iff_reachable_predecessors {g : Digraph}
    {r d v : Fin g.vertexCount} (hvr : v ≠ r) (hdv : d ≠ v) :
    g.Dominates r d v ↔
      ∀ p, g.HasArc p v → g.InitiallyReachable r p → g.Dominates r d p := by
  constructor
  · intro hdom p hp _ path
    have hv : v ≠ d := fun he => hdv he.symm
    have hpAlive : p ≠ d := AvoidPath.target_alive (failed := fun x => x = d) path
    have hLast : g.SurvivingPath (fun x => x = d) p v :=
      AvoidPath.step (failed := fun x => x = d) p v v hpAlive hp
        (AvoidPath.refl (failed := fun x => x = d) v hv)
    exact hdom (AvoidPath.trans path hLast)
  · intro hdom path
    rcases AvoidPath.eq_or_exists_last_arc path with he | ⟨p, hpre, hp⟩
    · exact hvr he.symm
    · exact hdom p hp (initiallyReachable_of_survivingPath (g := g) hpre) hpre

end PaperB.Digraph
