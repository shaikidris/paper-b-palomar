module

public import PaperB.ForestReady
public import PaperB.ExitPublishedSlotChronology

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient

namespace PaperB.FinalEmbeddingAncestry

private theorem climb_succ_start {α : Type} (parent : α → α)
    (k : Nat) (x : α) :
    EX24.PreStep.climb parent k.succ x =
      EX24.PreStep.climb parent k (parent x) := by
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg parent ih

private theorem ancestor_iterate {n : Nat} {parent : Fin n → Fin n}
    {a source : Fin n} (h : IsForestAncestor parent a source) :
    ∃ k : Nat, EX24.PreStep.climb parent k source = a := by
  induction h
  all_goals
    try subst_vars
    first
    | exact ⟨0, rfl⟩
    | rename_i ih
      obtain ⟨k, hk⟩ := ih
      exact ⟨k.succ, (climb_succ_start parent k _).trans hk⟩

abbrev slotEdge {n : Nat} (up : Fin n → Fin n)
    (child parent : Nat) : Prop :=
  ∃ v : Fin n, v.val = child ∧ (up v).val = parent

private theorem iterate_physical {n : Nat} (up : Fin n → Fin n)
    (k : Nat) (source : Fin n) :
    PaperB.ExitPublishedSlotChronology.PhysicalAncestor
      (slotEdge up) source.val (EX24.PreStep.climb up k source).val := by
  induction k generalizing source with
  | zero =>
      exact PaperB.ExitPublishedSlotChronology.PhysicalAncestor.here source.val
  | succ k ih =>
      rw [climb_succ_start]
      have hedge : slotEdge up source.val (up source).val :=
        ⟨source, rfl, rfl⟩
      exact PaperB.ExitPublishedSlotChronology.PhysicalAncestor.up
        hedge (ih (up source))

variable {H : PaperB.LabelledQuotient}
variable {c : EX24.Config H} {s : EX24.State H} {F : JumpForest}
variable {rank : Vertex H → Nat} {up : Fin F.size → Fin F.size}
variable {processed : Vertex H → Prop}

theorem physical_ancestor_of_image
    (E : EX24.PreStep.Embedding c s F rank up processed)
    {a source : Fin F.size}
    (h : IsForestAncestor (buildProperLossForest H rank).parent
      (E.image a) (E.image source)) :
    PaperB.ExitPublishedSlotChronology.PhysicalAncestor
      (slotEdge up) source.val a.val := by
  obtain ⟨k, hk⟩ := ancestor_iterate h
  have he := (EX24.PreStep.path_iff E k a source).mpr hk
  simpa only [he] using iterate_physical up k source

theorem physical_le_of_image
    (E : EX24.PreStep.Embedding c s F rank up processed)
    {a source : Fin F.size}
    (h : IsForestAncestor (buildProperLossForest H rank).parent
      (E.image a) (E.image source))
    (hmon : ∀ v, (up v).val ≤ v.val) : a.val ≤ source.val := by
  have mono {x y : Nat}
      (p : PaperB.ExitPublishedSlotChronology.PhysicalAncestor
        (slotEdge up) x y) : y ≤ x := by
    induction p with
    | here x => exact Nat.le_refl x
    | up hedge _ ih =>
        obtain ⟨v, rfl, rfl⟩ := hedge
        exact Nat.le_trans ih (hmon v)
  exact mono (physical_ancestor_of_image E h)

end PaperB.FinalEmbeddingAncestry
