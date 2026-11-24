module

public import Challenge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Path operations, repeated failures, and direct labelled exits. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace AvoidPath

theorem source_alive {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {u v : V} (h : AvoidPath edge failed u v) : ¬ failed u := by
  cases h with
  | refl _ alive => exact alive
  | step _ _ _ alive _ _ => exact alive

theorem target_alive {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {u v : V} (h : AvoidPath edge failed u v) : ¬ failed v := by
  induction h with
  | refl _ alive => exact alive
  | step _ _ _ _ _ _ ih => exact ih

theorem mono {V : Type} {edge : V → V → Prop} {failed failed' : V → Prop}
    {u v : V} (h : AvoidPath edge failed u v)
    (weaken : ∀ x : V, failed' x → failed x) :
    AvoidPath edge failed' u v := by
  induction h with
  | refl u alive =>
      exact AvoidPath.refl u (fun hu => alive (weaken u hu))
  | step u w v alive arc _ ih =>
      exact AvoidPath.step u w v (fun hu => alive (weaken u hu)) arc ih

theorem trans {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {u w v : V}
    (h₁ : AvoidPath edge failed u w)
    (h₂ : AvoidPath edge failed w v) :
    AvoidPath edge failed u v := by
  revert h₂
  induction h₁ with
  | refl _ _ =>
      intro h₂
      exact h₂
  | step a b _ alive arc _ ih =>
      intro h₂
      exact AvoidPath.step a b v alive arc (ih h₂)

/-- A path is either from a vertex to itself or has a final arc after a surviving prefix. -/
theorem eq_or_exists_last_arc {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {u v : V} (path : AvoidPath edge failed u v) :
    u = v ∨ ∃ p, AvoidPath edge failed u p ∧ edge p v := by
  induction path with
  | refl _ _ =>
      exact Or.inl rfl
  | step a b c alive arc _ ih =>
      cases ih with
      | inl hEq =>
          refine Or.inr ⟨a, AvoidPath.refl a alive, ?_⟩
          rw [← hEq]
          exact arc
      | inr hLast =>
          let ⟨p, hPrefix, hLastArc⟩ := hLast
          exact Or.inr ⟨p, AvoidPath.step a b p alive arc hPrefix, hLastArc⟩

end AvoidPath

namespace Digraph

theorem survivingPath_source_alive {g : Digraph} {failed : Fin g.vertexCount → Prop}
    {u v : Fin g.vertexCount} (h : g.SurvivingPath failed u v) :
    ¬ failed u :=
  AvoidPath.source_alive h

theorem survivingPath_target_alive {g : Digraph} {failed : Fin g.vertexCount → Prop}
    {u v : Fin g.vertexCount} (h : g.SurvivingPath failed u v) :
    ¬ failed v :=
  AvoidPath.target_alive h

theorem survivingPath_mono {g : Digraph} {failed failed' : Fin g.vertexCount → Prop}
    {u v : Fin g.vertexCount}
    (h : g.SurvivingPath failed u v)
    (weaken : ∀ x : Fin g.vertexCount, failed' x → failed x) :
    g.SurvivingPath failed' u v :=
  AvoidPath.mono h weaken

theorem survivingPath_trans {g : Digraph} {failed : Fin g.vertexCount → Prop}
    {u w v : Fin g.vertexCount}
    (h₁ : g.SurvivingPath failed u w)
    (h₂ : g.SurvivingPath failed w v) :
    g.SurvivingPath failed u v :=
  AvoidPath.trans h₁ h₂

theorem reachableAvoiding_two_diag {g : Digraph} (a r t : Fin g.vertexCount) :
    g.ReachableAvoiding (.two a a) r t ↔ g.ReachableAvoiding (.one a) r t := by
  constructor
  · intro h
    exact AvoidPath.mono h (fun _ hx => Or.inl hx)
  · intro h
    exact AvoidPath.mono h (fun _ hx =>
      match hx with
      | Or.inl hEq => hEq
      | Or.inr hEq => hEq)

end Digraph

namespace LabelledQuotient

theorem mem_implies_lost (H : LabelledQuotient) (B : CutPair H)
    {v : Fin H.vertexCount} (hv : B.Mem v) : H.Lost B v :=
  fun path => AvoidPath.target_alive path hv

/-- A direct labelled arc `s → y` qualifies for `X^B_s(y)` whenever `y ∉ B`. -/
theorem direct_arc_exitTailMem {H : LabelledQuotient} {B : CutPair H}
    {s y : Fin H.vertexCount}
    (e : QuotientArc H.origVertexCount H.vertexCount)
    (he : e ∈ H.outArcs s)
    (hHead : e.head = y)
    (hy : ¬ B.Mem y) :
    H.ExitTailMem B s y e.origTail := by
  refine ⟨e, he, rfl, ?_⟩
  rw [hHead]
  exact AvoidPath.refl y hy

end LabelledQuotient

end PaperB
