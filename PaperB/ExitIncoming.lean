module

public import PaperB.Forest

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open LabelledQuotient

universe u

/--
The supplied excerpt does not expose the original arc fields, so the two
unfolding equations are explicit. `Occurrence` indexes original occurrences,
not quotient endpoint pairs: parallel arcs keep their own indices and labels.
-/
structure EX42OccurrenceView (H : LabelledQuotient) where
  Occurrence : Type u
  incoming : Fin H.vertexCount → Occurrence → Prop
  source : Occurrence → Fin H.vertexCount
  physicalTail : Occurrence → Fin H.origVertexCount
  quotientArc_iff : ∀ z y,
    H.HasQuotientArc z y ↔
      ∃ a, incoming y a ∧ source a = z
  exitTail_iff : ∀ (B : CutPair H) (s y : Fin H.vertexCount)
      (x : Fin H.origVertexCount), B.Mem s →
    (H.ExitTailMem B s y x ↔
      ∃ w a, incoming w a ∧ source a = s ∧ physicalTail a = x ∧
        H.SurvivingPath B.Mem w y)

/-- EX4.2: the exact union over original labelled occurrences entering `y`. -/
theorem ex42_exitTailMem_iff_incomingOccurrence
    {H : LabelledQuotient} (V : EX42OccurrenceView H)
    {B : CutPair H} {s y : Fin H.vertexCount}
    {x : Fin H.origVertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss B y) :
    H.ExitTailMem B s y x ↔
      ∃ a, V.incoming y a ∧
        ((V.source a = s ∧ V.physicalTail a = x) ∨
          (H.ProperLoss B (V.source a) ∧
            H.ExitTailMem B s (V.source a) x)) := by
  have lastStep : ∀ {z : Fin H.vertexCount}, ¬ B.Mem z →
      H.HasQuotientArc z y → H.SurvivingPath B.Mem z y := by
    intro z hz hzy
    exact AvoidPath.step z y y hz hzy (AvoidPath.refl y proper.2)
  constructor
  · intro hx
    obtain ⟨w, a, haw, has, hax, hwy⟩ :=
      (V.exitTail_iff B s y x hs).mp hx
    rcases AvoidPath.eq_or_exists_last_arc hwy with hEq | ⟨z, hwz, hzy⟩
    · subst w
      exact ⟨a, haw, Or.inl ⟨has, hax⟩⟩
    · obtain ⟨b, hby, hbz⟩ := (V.quotientArc_iff z y).mp hzy
      have hzAlive : ¬ B.Mem z := AvoidPath.target_alive hwz
      have hzLost : H.Lost B z := by
        intro hRootZ
        exact proper.1 (AvoidPath.trans hRootZ (lastStep hzAlive hzy))
      have hxz : H.ExitTailMem B s z x :=
        (V.exitTail_iff B s z x hs).mpr ⟨w, a, haw, has, hax, hwz⟩
      refine ⟨b, hby, Or.inr ?_⟩
      rw [hbz]
      exact ⟨⟨hzLost, hzAlive⟩, hxz⟩
  · rintro ⟨a, hay, hContribution⟩
    rcases hContribution with ⟨has, hax⟩ | ⟨haProper, hxa⟩
    · exact (V.exitTail_iff B s y x hs).mpr
        ⟨y, a, hay, has, hax, AvoidPath.refl y proper.2⟩
    · have hayArc : H.HasQuotientArc (V.source a) y :=
        (V.quotientArc_iff (V.source a) y).mpr ⟨a, hay, rfl⟩
      obtain ⟨w, b, hbw, hbs, hbx, hwa⟩ :=
        (V.exitTail_iff B s (V.source a) x hs).mp hxa
      exact (V.exitTail_iff B s y x hs).mpr
        ⟨w, b, hbw, hbs, hbx,
          AvoidPath.trans hwa (lastStep haProper.2 hayArc)⟩

theorem ex42_exitTailMem_eq_incomingOccurrence
    {H : LabelledQuotient} (V : EX42OccurrenceView H)
    {B : CutPair H} {s y : Fin H.vertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss B y) :
    (fun x : Fin H.origVertexCount => H.ExitTailMem B s y x) =
      (fun x : Fin H.origVertexCount =>
        ∃ a, V.incoming y a ∧
          ((V.source a = s ∧ V.physicalTail a = x) ∨
            (H.ProperLoss B (V.source a) ∧
              H.ExitTailMem B s (V.source a) x))) := by
  funext x
  exact propext (ex42_exitTailMem_iff_incomingOccurrence V (x := x) hs proper)

end PaperB
