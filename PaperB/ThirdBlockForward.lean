module

public import PaperB.BlockProjection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.BlockSystem

variable {V C : Type}

/-- Inspect the physical suffix first. If it already has a last exit, keep
that exit and extend only its prefix. Otherwise the current arc can be the
last exit, and only if its tail is in a forbidden block. -/
private theorem split_physical_last_exit (S : BlockSystem V C)
    (enter : ∀ v w : V, S.arc v w → S.block v ≠ S.block w →
      w = S.leader (S.block w))
    {failed : V → Prop} {bad : C → Prop} {u t : V}
    (path : AvoidPath S.arc failed u t) :
    ¬ bad (S.block t) →
      (AvoidPath S.arc (fun v => failed v ∨ bad (S.block v)) u t ∨
        ∃ x y : V,
          bad (S.block x) ∧
          AvoidPath S.arc failed u x ∧
          S.arc x y ∧
          y = S.leader (S.block y) ∧
          S.LabelledStep (S.block x) (S.block y) x ∧
          AvoidPath S.arc (fun v => failed v ∨ bad (S.block v)) y t) := by
  classical
  induction path with
  | refl v hv =>
      intro ht
      exact Or.inl (AvoidPath.refl v (fun h => h.elim hv ht))
  | step v w z hv edge _ ih =>
      intro ht
      rcases ih ht with hClean | ⟨x, y, hx, hPrefix, hArc, hy, hLabel, hSuffix⟩
      · have hw : ¬ bad (S.block w) :=
          fun h => hClean.source_alive (Or.inr h)
        have prependClean (h : ¬ bad (S.block v)) :
            AvoidPath S.arc (fun a => failed a ∨ bad (S.block a)) v z :=
          AvoidPath.step v w z (fun hf => hf.elim hv h) edge hClean
        by_cases hSame : S.block v = S.block w
        · have hvClean : ¬ bad (S.block v) := by
            simpa only [hSame] using hw
          exact Or.inl (prependClean hvClean)
        · by_cases hvBad : bad (S.block v)
          · have hHead : w = S.leader (S.block w) :=
              enter v w edge hSame
            have hOut : S.arc v (S.leader (S.block w)) := by
              rw [← hHead]
              exact edge
            exact Or.inr ⟨v, w, hvBad, AvoidPath.refl v hv, edge, hHead,
              ⟨hSame, rfl, hOut⟩, hClean⟩
          · exact Or.inl (prependClean hvBad)
      · exact Or.inr ⟨x, y, hx, AvoidPath.step v w x hv edge hPrefix,
          hArc, hy, hLabel, hSuffix⟩

/-- For a surviving physical path to a vertex outside both forbidden blocks,
either its projection avoids both blocks, or its last exit from their union
has an original surviving prefix and a clean quotient suffix. The exit
retains the physical tail and head, and the physical suffix ends at `t`. -/
theorem forward_last_exit (S : BlockSystem V C)
    (enter : ∀ v w : V, S.arc v w → S.block v ≠ S.block w →
      w = S.leader (S.block w))
    {failed : V → Prop} {root b₁ b₂ : C} {t : V}
    (path : AvoidPath S.arc failed (S.leader root) t)
    (ht₁ : S.block t ≠ b₁) (ht₂ : S.block t ≠ b₂) :
    AvoidPath S.QuotientEdge (fun c => c = b₁ ∨ c = b₂) root (S.block t) ∨
      ∃ x y : V,
        (S.block x = b₁ ∨ S.block x = b₂) ∧
        AvoidPath S.arc failed (S.leader root) x ∧
        S.arc x y ∧
        y = S.leader (S.block y) ∧
        S.LabelledStep (S.block x) (S.block y) x ∧
        AvoidPath S.arc (fun v => failed v ∨ (S.block v = b₁ ∨ S.block v = b₂))
          y t ∧
        AvoidPath S.QuotientEdge (fun c => c = b₁ ∨ c = b₂)
          (S.block y) (S.block t) := by
  let bad : C → Prop := fun c => c = b₁ ∨ c = b₂
  have ht : ¬ bad (S.block t) := fun h => Or.elim h ht₁ ht₂
  have projectClean {a b : V}
      (p : AvoidPath S.arc (fun v => failed v ∨ bad (S.block v)) a b) :
      AvoidPath S.QuotientEdge bad (S.block a) (S.block b) := by
    have p' : AvoidPath S.arc (S.VertexFailed bad) a b := by
      refine AvoidPath.mono p ?_
      intro v hv
      exact Or.inr hv
    exact S.project enter p'
  rcases split_physical_last_exit S enter (bad := bad) path ht with
    hClean | ⟨x, y, hx, hPrefix, hArc, hy, hLabel, hSuffix⟩
  · exact Or.inl (by simpa only [S.leader_block] using projectClean hClean)
  · exact Or.inr ⟨x, y, hx, hPrefix, hArc, hy, hLabel, hSuffix,
      projectClean hSuffix⟩

end PaperB.BlockSystem
