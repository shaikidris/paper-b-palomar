module

public import PaperB.BlockPaths

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.BlockSystem

variable {V C : Type} (S : BlockSystem V C)

def LeaderFailed (failed : C → Prop) (v : V) : Prop :=
  failed (S.block v) ∧ v = S.leader (S.block v)

variable (enter : ∀ v w : V, S.arc v w → S.block v ≠ S.block w →
  w = S.leader (S.block w))

include enter

theorem project {failed : C → Prop} {v t : V}
    (path : AvoidPath S.arc (S.VertexFailed failed) v t) :
    AvoidPath S.QuotientEdge failed (S.block v) (S.block t) := by
  classical
  induction path with
  | refl v hv =>
      exact AvoidPath.refl (S.block v) hv
  | step v w t hv edge _ ih =>
      by_cases h : S.block v = S.block w
      · simpa only [h] using ih
      · have hOut : S.arc v (S.leader (S.block w)) := by
          simpa only [← enter v w edge h] using edge
        exact AvoidPath.step (S.block v) (S.block w) (S.block t)
          hv ⟨v, ⟨h, rfl, hOut⟩⟩ ih

theorem avoid_failed_blocks {failed : C → Prop} {v t : V}
    (path : AvoidPath S.arc (S.LeaderFailed failed) v t) :
    (¬ failed (S.block v)) → AvoidPath S.arc (S.VertexFailed failed) v t := by
  classical
  induction path with
  | refl v _ =>
      intro hv
      exact AvoidPath.refl v hv
  | step v w t _ edge rest ih =>
      intro hv
      have hw : ¬ failed (S.block w) := by
        by_cases h : S.block v = S.block w
        · simpa only [h] using hv
        · intro hf
          exact rest.source_alive ⟨hf, enter v w edge h⟩
      exact AvoidPath.step v w t hv edge (ih hw)

theorem leader_path_iff {failed : C → Prop} {s t : C} :
    AvoidPath S.arc (S.LeaderFailed failed) (S.leader s) (S.leader t) ↔
      AvoidPath S.QuotientEdge failed s t := by
  constructor
  · intro path
    have hs : ¬ failed (S.block (S.leader s)) := by
      intro hf
      exact path.source_alive ⟨hf, by rw [S.leader_block]⟩
    simpa only [S.leader_block] using
      S.project enter (S.avoid_failed_blocks enter path hs)
  · intro path
    refine AvoidPath.mono (S.lift path) ?_
    intro v hv
    exact And.left hv

end PaperB.BlockSystem
