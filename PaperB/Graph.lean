module

public import PaperB.Spec

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! The initially reachable induced graph, with original IDs and arc occurrences retained. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace AvoidPath

theorem endpoints_alive {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {u v : V} (h : AvoidPath edge failed u v) :
    (¬ failed u) ∧ (¬ failed v) := by
  induction h with
  | refl _ alive => exact ⟨alive, alive⟩
  | step _ _ _ alive _ _ ih => exact ⟨alive, ih.2⟩

/-- The length-zero constructor makes self-reachability equivalent to being alive. -/
theorem self_iff_alive {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    (u : V) : AvoidPath edge failed u u ↔ ¬ failed u :=
  ⟨fun h => (endpoints_alive h).1, AvoidPath.refl u⟩

end AvoidPath

namespace Digraph

/-- Ordinary reachability from `r`, before applying any query failures. -/
def InitiallyReachable (g : Digraph) (r v : Fin g.vertexCount) : Prop :=
  g.SurvivingPath (fun _ => False) r v

theorem initiallyReachable_source (g : Digraph) (r : Fin g.vertexCount) :
    g.InitiallyReachable r r :=
  AvoidPath.refl r (fun h => h)

theorem initiallyReachable_extend {g : Digraph} {r u v : Fin g.vertexCount}
    (hu : g.InitiallyReachable r u) (arc : g.HasArc u v) :
    g.InitiallyReachable r v := by
  change AvoidPath g.HasArc (fun _ => False) r u at hu
  change AvoidPath g.HasArc (fun _ => False) r v
  revert arc
  induction hu with
  | refl a alive =>
      intro arc
      exact AvoidPath.step a v v alive arc (AvoidPath.refl v (fun h => h))
  | step a b _ alive first _ ih =>
      intro arc
      exact AvoidPath.step a b v alive first (ih arc)

/-- Vertices of the induced graph carry their original IDs, not new indices. -/
abbrev ReachableVertex (g : Digraph) (r : Fin g.vertexCount) :=
  {v : Fin g.vertexCount // g.InitiallyReachable r v}

namespace ReachableVertex

/-- The original source is retained, regardless of the subsequent query. -/
def source (g : Digraph) (r : Fin g.vertexCount) : g.ReachableVertex r :=
  ⟨r, initiallyReachable_source g r⟩

@[simp] theorem source_val (g : Digraph) (r : Fin g.vertexCount) :
    (source g r).val = r :=
  rfl

variable {g : Digraph} {r : Fin g.vertexCount}

/-- Induced adjacency is original adjacency on the retained IDs. -/
def HasArc (u v : g.ReachableVertex r) : Prop :=
  g.HasArc u.val v.val

/-- Restrict a failed predicate without changing its meaning on retained IDs. -/
def restrictFailed (failed : Fin g.vertexCount → Prop)
    (u : g.ReachableVertex r) : Prop :=
  failed u.val

abbrev SurvivingPath (failed : Fin g.vertexCount → Prop)
    (u v : g.ReachableVertex r) : Prop :=
  AvoidPath (HasArc (g := g) (r := r)) (restrictFailed failed) u v

theorem outArcs_retained (u : g.ReachableVertex r)
    {v : Fin g.vertexCount} (hv : v ∈ g.outArcs u.val) :
    g.InitiallyReachable r v :=
  initiallyReachable_extend (g := g) (r := r) u.property hv

private def retainList (g : Digraph) (r : Fin g.vertexCount) :
    (xs : List (Fin g.vertexCount)) →
    (∀ v, v ∈ xs → g.InitiallyReachable r v) →
    List (g.ReachableVertex r)
  | [], _ => []
  | v :: vs, h =>
      ⟨v, h v (List.Mem.head vs)⟩ ::
        retainList g r vs (fun w hw => h w (List.Mem.tail v hw))

private theorem retainList_values (g : Digraph) (r : Fin g.vertexCount)
    (xs : List (Fin g.vertexCount))
    (h : ∀ v, v ∈ xs → g.InitiallyReachable r v) :
    (retainList g r xs h).map (fun v => v.val) = xs := by
  revert h
  induction xs with
  | nil =>
      intro h
      rfl
  | cons v vs ih =>
      intro h
      simpa only [retainList, List.map_cons] using
        congrArg (List.cons v) (ih (fun w hw => h w (List.Mem.tail v hw)))

/-- Label each original outgoing occurrence with its reachability proof. -/
def outArcs (u : g.ReachableVertex r) : List (g.ReachableVertex r) :=
  retainList g r (g.outArcs u.val) (fun _ hv => outArcs_retained u hv)

/-- Erasing the proof labels gives the exact original list, including duplicates. -/
theorem outArcs_values (u : g.ReachableVertex r) :
    (outArcs u).map (fun v => v.val) = g.outArcs u.val :=
  retainList_values g r (g.outArcs u.val) (fun _ hv => outArcs_retained u hv)

theorem hasArc_iff_mem_outArcs (u v : g.ReachableVertex r) :
    HasArc u v ↔ v ∈ outArcs u := by
  change (v.val ∈ g.outArcs u.val) ↔ v ∈ outArcs u
  rw [← outArcs_values u]
  constructor
  · intro h
    obtain ⟨w, hw, hval⟩ := List.mem_map.mp h
    have heq : w = v := Subtype.ext hval
    exact heq ▸ hw
  · intro h
    exact List.mem_map.mpr ⟨v, h, rfl⟩

/-- Lift a surviving path from a retained start, obtaining retention of its target. -/
theorem lift {failed : Fin g.vertexCount → Prop} {u v : Fin g.vertexCount}
    (h : g.SurvivingPath failed u v) (hu : g.InitiallyReachable r u) :
    ∃ hv : g.InitiallyReachable r v,
      SurvivingPath failed (⟨u, hu⟩ : g.ReachableVertex r) ⟨v, hv⟩ := by
  revert hu
  induction h with
  | refl a alive =>
      intro ha
      exact ⟨ha, AvoidPath.refl (⟨a, ha⟩ : g.ReachableVertex r) alive⟩
  | step a b c alive arc _ ih =>
      intro ha
      have hb : g.InitiallyReachable r b :=
        initiallyReachable_extend (g := g) (r := r) ha arc
      obtain ⟨hc, hrest⟩ := ih hb
      exact ⟨hc, AvoidPath.step (⟨a, ha⟩ : g.ReachableVertex r)
        (⟨b, hb⟩ : g.ReachableVertex r) (⟨c, hc⟩ : g.ReachableVertex r)
        alive arc hrest⟩

/-- Forget the retention proofs without changing any step or failure test. -/
theorem project {failed : Fin g.vertexCount → Prop} {u v : g.ReachableVertex r}
    (h : SurvivingPath failed u v) :
    g.SurvivingPath failed u.val v.val := by
  induction h with
  | refl a alive =>
      exact AvoidPath.refl a.val alive
  | step a b c alive arc _ ih =>
      exact AvoidPath.step a.val b.val c.val alive arc ih

theorem survivingPath_iff (failed : Fin g.vertexCount → Prop)
    (u v : g.ReachableVertex r) :
    SurvivingPath failed u v ↔ g.SurvivingPath failed u.val v.val := by
  constructor
  · intro h
    exact project (g := g) (r := r) (failed := failed) h
  · intro h
    obtain ⟨_, hLift⟩ := lift (g := g) (r := r) (failed := failed) h u.property
    exact hLift

end ReachableVertex

/-- A surviving path from the original source exists iff its target is retained
and the induced graph has a path from the retained source to that target.
The source is retained even if it fails; every failure test uses the original ID. -/
theorem survivingPath_iff_retained (g : Digraph) (r v : Fin g.vertexCount)
    (failed : Fin g.vertexCount → Prop) :
    g.SurvivingPath failed r v ↔
      ∃ hv : g.InitiallyReachable r v,
        AvoidPath (ReachableVertex.HasArc (g := g) (r := r))
          (ReachableVertex.restrictFailed failed)
          (ReachableVertex.source g r) (⟨v, hv⟩ : g.ReachableVertex r) := by
  constructor
  · intro h
    obtain ⟨hv, hLift⟩ := ReachableVertex.lift (g := g) (r := r)
      (failed := failed) h (initiallyReachable_source g r)
    exact ⟨hv, hLift⟩
  · rintro ⟨hv, h⟩
    exact ReachableVertex.project (g := g) (r := r) (failed := failed)
      (u := ReachableVertex.source g r) (v := (⟨v, hv⟩ : g.ReachableVertex r)) h

theorem not_survivingPath_of_not_initiallyReachable {g : Digraph}
    {r v : Fin g.vertexCount} {failed : Fin g.vertexCount → Prop}
    (hUnreachable : ¬ g.InitiallyReachable r v) : ¬ g.SurvivingPath failed r v := by
  intro h
  exact hUnreachable ((survivingPath_iff_retained g r v failed).mp h).1

theorem not_survivingPath_of_failed_endpoint {g : Digraph}
    {u v : Fin g.vertexCount} {failed : Fin g.vertexCount → Prop}
    (hFailed : failed u ∨ failed v) : ¬ g.SurvivingPath failed u v := by
  intro h
  have hAlive := AvoidPath.endpoints_alive (edge := g.HasArc) (failed := failed) h
  exact hFailed.elim hAlive.1 hAlive.2
end Digraph
end PaperB
