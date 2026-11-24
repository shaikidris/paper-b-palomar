module

public import Challenge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace LabelledQuotient
namespace Transport

variable {H K : LabelledQuotient}
variable (f : Fin H.vertexCount → Fin K.vertexCount)

/-- Exact adjacency at a fixed source, head, and physical tail. -/
def ExactAdj (hN : H.origVertexCount = K.origVertexCount) : Prop :=
  ∀ (u v : Fin H.vertexCount) (x : Fin H.origVertexCount),
    (⟨v, x⟩ : QuotientArc H.origVertexCount H.vertexCount) ∈ H.outArcs u ↔
    (⟨f v, Fin.cast hN x⟩ : QuotientArc K.origVertexCount K.vertexCount) ∈
      K.outArcs (f u)

theorem exactAdj_of_outArcs_eq
    (hi : ∀ ⦃u v⦄, f u = f v → u = v)
    (hN : H.origVertexCount = K.origVertexCount)
    (h : ∀ u, K.outArcs (f u) =
      (H.outArcs u).map (fun e => ⟨f e.head, Fin.cast hN e.origTail⟩)) :
    ExactAdj f hN := by
  intro u v x
  rw [h u]
  constructor
  · intro hm
    exact List.mem_map.mpr ⟨⟨v, x⟩, hm, rfl⟩
  · intro hm
    obtain ⟨⟨w, z⟩, hw, he⟩ := List.mem_map.mp hm
    have hv : w = v := hi (congrArg QuotientArc.head he)
    have hx : z = x :=
      Fin.ext (congrArg (fun e : QuotientArc K.origVertexCount K.vertexCount =>
        e.origTail.val) he)
    subst w
    subst z
    exact hw

private theorem tail_surj {m n : Nat} (h : m = n) (x : Fin n) :
    ∃ y : Fin m, Fin.cast h y = x := by
  cases h
  exact ⟨x, Fin.ext rfl⟩

theorem arc_iff (hN : H.origVertexCount = K.origVertexCount)
    (ha : ExactAdj f hN) (u v : Fin H.vertexCount) :
    H.HasQuotientArc u v ↔ K.HasQuotientArc (f u) (f v) := by
  constructor
  · rintro ⟨⟨w, x⟩, hm, he⟩
    change w = v at he
    subst w
    exact ⟨⟨f v, Fin.cast hN x⟩, (ha u v x).mp hm, rfl⟩
  · rintro ⟨⟨w, x⟩, hm, he⟩
    change w = f v at he
    subst w
    obtain ⟨z, hz⟩ := tail_surj hN x
    subst x
    exact ⟨⟨v, z⟩, (ha u v z).mpr hm, rfl⟩

theorem avoidPath_iff
    (hi : ∀ ⦃u v⦄, f u = f v → u = v)
    (hs : ∀ v, ∃ u, f u = v)
    (hN : H.origVertexCount = K.origVertexCount) (ha : ExactAdj f hN)
    {P : Fin H.vertexCount → Prop} {Q : Fin K.vertexCount → Prop}
    (hf : ∀ u, P u ↔ Q (f u)) (s t : Fin H.vertexCount) :
    H.SurvivingPath P s t ↔ K.SurvivingPath Q (f s) (f t) := by
  have forward {a b : Fin H.vertexCount} (p : H.SurvivingPath P a b) :
      K.SurvivingPath Q (f a) (f b) := by
    induction p with
    | refl a h =>
        exact .refl (f a) (fun hq => h ((hf a).mpr hq))
    | step a b c h he rest ih =>
        exact .step (f a) (f b) (f c) (fun hq => h ((hf a).mpr hq))
          ((arc_iff f hN ha a b).mp he) ih
  have backward {a b : Fin K.vertexCount} (p : K.SurvivingPath Q a b) :
      ∀ u v, f u = a → f v = b → H.SurvivingPath P u v := by
    induction p with
    | refl a h =>
        intro u v hu hv
        have huv : u = v := hi (hu.trans hv.symm)
        subst v
        refine .refl u ?_
        intro hp
        apply h
        rw [← hu]
        exact (hf u).mp hp
    | step a b c h he rest ih =>
        intro u v hu hv
        obtain ⟨w, hw⟩ := hs b
        refine .step u w v ?_ ?_ (ih w v hw hv)
        · intro hp
          apply h
          rw [← hu]
          exact (hf u).mp hp
        · apply (arc_iff f hN ha u w).mpr
          rw [hu, hw]
          exact he
  exact ⟨forward, fun p => backward p s t rfl rfl⟩

/-- Map the endpoints in place; do not canonicalize their order. -/
def cutPair (hi : ∀ ⦃u v⦄, f u = f v → u = v)
    (hr : f H.root = K.root) (B : CutPair H) : CutPair K where
  fst := f B.fst
  snd := f B.snd
  fst_ne_root := fun h => B.fst_ne_root (hi (h.trans hr.symm))
  snd_ne_root := fun h => B.snd_ne_root (hi (h.trans hr.symm))
  ne := fun h => B.ne (hi h)

variable (hi : ∀ ⦃u v⦄, f u = f v → u = v)
variable (hr : f H.root = K.root)

theorem mem_iff (B : CutPair H) (v : Fin H.vertexCount) :
    B.Mem v ↔ (cutPair f hi hr B).Mem (f v) := by
  change (v = B.fst ∨ v = B.snd) ↔
    (f v = f B.fst ∨ f v = f B.snd)
  exact ⟨fun h => h.elim (fun e => Or.inl (congrArg f e))
      (fun e => Or.inr (congrArg f e)),
    fun h => h.elim (fun e => Or.inl (hi e)) (fun e => Or.inr (hi e))⟩

theorem cutPath_iff (hs : ∀ v, ∃ u, f u = v)
    (hN : H.origVertexCount = K.origVertexCount) (ha : ExactAdj f hN)
    (B : CutPair H) (s t : Fin H.vertexCount) :
    H.SurvivingPath B.Mem s t ↔
      K.SurvivingPath (cutPair f hi hr B).Mem (f s) (f t) :=
  avoidPath_iff f hi hs hN ha (mem_iff f hi hr B) s t

theorem properLoss_iff (hs : ∀ v, ∃ u, f u = v)
    (hN : H.origVertexCount = K.origVertexCount) (ha : ExactAdj f hN)
    (B : CutPair H) (v : Fin H.vertexCount) :
    H.ProperLoss B v ↔ K.ProperLoss (cutPair f hi hr B) (f v) := by
  have hp := cutPath_iff f hi hr hs hN ha B H.root v
  rw [hr] at hp
  have hm := mem_iff f hi hr B v
  unfold ProperLoss Lost
  exact ⟨fun ⟨hl, hn⟩ => ⟨fun p => hl (hp.mpr p), fun m => hn (hm.mpr m)⟩,
    fun ⟨hl, hn⟩ => ⟨fun p => hl (hp.mp p), fun m => hn (hm.mp m)⟩⟩

theorem exitTailMem_iff (hs : ∀ v, ∃ u, f u = v)
    (hN : H.origVertexCount = K.origVertexCount) (ha : ExactAdj f hN)
    (B : CutPair H) (s y : Fin H.vertexCount) (x : Fin H.origVertexCount) :
    H.ExitTailMem B s y x ↔
      K.ExitTailMem (cutPair f hi hr B) (f s) (f y) (Fin.cast hN x) := by
  constructor
  · rintro ⟨⟨w, z⟩, hm, hz, hp⟩
    change z = x at hz
    subst z
    exact ⟨⟨f w, Fin.cast hN x⟩, (ha s w x).mp hm, rfl,
      (cutPath_iff f hi hr hs hN ha B w y).mp hp⟩
  · rintro ⟨⟨v, z⟩, hm, hz, hp⟩
    change z = Fin.cast hN x at hz
    subst z
    obtain ⟨w, hw⟩ := hs v
    subst v
    exact ⟨⟨w, x⟩, (ha s w x).mpr hm, rfl,
      (cutPath_iff f hi hr hs hN ha B w y).mpr hp⟩

theorem orderedExitTailMem_iff (hs : ∀ v, ∃ u, f u = v)
    (hN : H.origVertexCount = K.origVertexCount) (ha : ExactAdj f hN)
    (B P : CutPair H) (y : Fin H.vertexCount) (x : Fin H.origVertexCount) :
    (H.ExitTailMem B P.fst y x ↔ K.ExitTailMem (cutPair f hi hr B)
      (cutPair f hi hr P).fst (f y) (Fin.cast hN x)) ∧
    (H.ExitTailMem B P.snd y x ↔ K.ExitTailMem (cutPair f hi hr B)
      (cutPair f hi hr P).snd (f y) (Fin.cast hN x)) :=
  ⟨exitTailMem_iff f hi hr hs hN ha B P.fst y x,
    exitTailMem_iff f hi hr hs hN ha B P.snd y x⟩

end Transport
end LabelledQuotient
end PaperB
