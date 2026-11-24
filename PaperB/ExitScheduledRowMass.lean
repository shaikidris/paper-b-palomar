module

public import PaperB.ExitLinearSchedule
public import PaperB.ForestInputPrepStorage

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.EX24.InputPrepCheckpoint

open PaperB.ForestIncomingRaw

universe u

private theorem sweep_mem_ofFn {α : Type u} (a : α) (n : Nat) :
    ∀ f : Fin n → α, a ∈ List.ofFn f ↔ ∃ i, f i = a := by
  induction n with
  | zero =>
    intro f
    constructor
    · intro h
      simp at h
    · rintro ⟨i, _⟩
      exact Fin.elim0 i
  | succ n ih =>
    intro f
    rw [List.ofFn_succ, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨i, hi⟩)
      · exact ⟨0, h.symm⟩
      · exact ⟨i.succ, hi⟩
    · rintro ⟨i, hi⟩
      exact Fin.cases
        (motive := fun j => f j = a →
          a = f 0 ∨ ∃ k : Fin n, f k.succ = a)
        (fun h => Or.inl h.symm) (fun k h => Or.inr ⟨k, h⟩) i hi

private theorem sweep_nodup_ofFn {α : Type u} (n : Nat) :
    ∀ f : Fin n → α, Function.Injective f → (List.ofFn f).Nodup := by
  induction n with
  | zero =>
    intro f _
    simp
  | succ n ih =>
    intro f hf
    rw [List.ofFn_succ, List.nodup_cons]
    constructor
    · intro hm
      obtain ⟨i, hi⟩ :=
        (sweep_mem_ofFn (f 0) n (fun j => f j.succ)).mp hm
      have h : i.succ = (0 : Fin (n + 1)) := hf hi
      have hv := congrArg Fin.val h
      change i.val + 1 = 0 at hv
      omega
    · apply ih
      intro i j hij
      have h : i.succ = j.succ := hf hij
      have hv := congrArg Fin.val h
      change i.val + 1 = j.val + 1 at hv
      apply Fin.ext
      omega

private theorem sweep_pull_front {α : Type u} (a : α) (ys : List α)
    (hy : ys.Nodup) (ha : a ∈ ys) :
    ∃ zs : List α, ys.Perm (a :: zs) ∧ zs.Nodup ∧
      ∀ b, b ∈ zs ↔ b ∈ ys ∧ b ≠ a := by
  induction ys with
  | nil => simp at ha
  | cons y ys ih =>
    obtain ⟨hny, hys⟩ := List.nodup_cons.mp hy
    rcases List.mem_cons.mp ha with h | ha'
    · subst y
      refine ⟨ys, List.Perm.refl _, hys, ?_⟩
      intro b
      constructor
      · intro hb
        refine ⟨List.mem_cons.mpr (Or.inr hb), ?_⟩
        intro e
        subst b
        exact hny hb
      · rintro ⟨hb, hne⟩
        exact (List.mem_cons.mp hb).resolve_left hne
    · have hya : y ≠ a := by
        intro e
        subst y
        exact hny ha'
      obtain ⟨zs, hp, hnz, hm⟩ := ih hys ha'
      have hs : (y :: a :: zs).Perm (a :: y :: zs) := by
        apply List.Perm.swap
      refine ⟨y :: zs, (List.Perm.cons y hp).trans hs,
        List.nodup_cons.mpr ⟨fun hb => hny ((hm y).mp hb).1, hnz⟩, ?_⟩
      intro b
      simp only [List.mem_cons, hm]
      constructor
      · rintro (rfl | ⟨hb, hne⟩)
        · exact ⟨Or.inl rfl, hya⟩
        · exact ⟨Or.inr hb, hne⟩
      · rintro ⟨hb, hne⟩
        rcases hb with hb | hb
        · exact Or.inl hb
        · exact Or.inr ⟨hb, hne⟩

private theorem sweep_perm_of_nodup_mem {α : Type u} (xs : List α) :
    ∀ ys : List α, xs.Nodup → ys.Nodup →
      (∀ a, a ∈ xs ↔ a ∈ ys) → xs.Perm ys := by
  induction xs with
  | nil =>
    intro ys _ _ hm
    cases ys with
    | nil => exact List.Perm.nil
    | cons y ys =>
      have h : y ∈ ([] : List α) :=
        (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
      simp at h
  | cons x xs ih =>
    intro ys hx hy hm
    obtain ⟨hnx, hxs⟩ := List.nodup_cons.mp hx
    have hxy : x ∈ ys := (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨zs, hp, hnz, hz⟩ := sweep_pull_front x ys hy hxy
    have htail : ∀ b, b ∈ xs ↔ b ∈ zs := by
      intro b
      rw [hz b, ← hm b, List.mem_cons]
      constructor
      · intro hb
        refine ⟨Or.inr hb, ?_⟩
        intro e
        subst b
        exact hnx hb
      · rintro ⟨hb, hne⟩
        exact hb.resolve_left hne
    exact (List.Perm.cons x (ih zs hxs hnz htail)).trans hp.symm

private theorem sweep_vertex_perm {n m : Nat} {P : _}
    (S : EX42.ArraySweep.Schedule (n := n) (m := m) P) :
    (List.ofFn S.vertex).Perm (List.ofFn (id : Fin n → Fin n)) := by
  apply sweep_perm_of_nodup_mem
  · exact sweep_nodup_ofFn n S.vertex (fun _ _ h => S.vertex_inj h)
  · exact sweep_nodup_ofFn n id (fun _ _ h => h)
  · intro v
    rw [sweep_mem_ofFn v n S.vertex, sweep_mem_ofFn v n id]
    exact ⟨fun _ => ⟨v, rfl⟩, fun _ => S.covers v⟩

private theorem sweep_perm_sum {α : Type u} (w : α → Nat)
    {xs ys : List α} (hp : xs.Perm ys) :
    (xs.map w).sum = (ys.map w).sum := by
  induction hp with
  | nil => rfl
  | cons a _ ih => simp only [List.map_cons, List.sum_cons, ih]
  | swap a b xs => simp only [List.map_cons, List.sum_cons] <;> omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

private theorem sweep_sum_eq_rowMass (H : LabelledQuotient)
    {m : Nat} {P : _}
    (S : EX42.ArraySweep.Schedule (n := H.vertexCount) (m := m) P) :
    ((List.ofFn S.vertex).map
      (fun v => ((prepare H).1.row v).length)).sum =
        EX51.Storage.rowMass (prepare H).1 := by
  let w : Fin H.vertexCount → Nat := fun v => ((prepare H).1.row v).length
  have hList :
      (List.ofFn (id : Fin H.vertexCount → Fin H.vertexCount)).map w =
        List.ofFn w := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      simp only [List.getElem_map, List.getElem_ofFn, id]
  calc
    ((List.ofFn S.vertex).map w).sum =
        ((List.ofFn (id : Fin H.vertexCount → Fin H.vertexCount)).map w).sum :=
      sweep_perm_sum w (sweep_vertex_perm S)
    _ = (List.ofFn w).sum := congrArg List.sum hList
    _ = EX51.Storage.rowMass (prepare H).1 :=
      (EX51.Storage.rowMass_eq_ofFn_sum (prepare H).1).symm

/-- The specification sum over the actual queue is exactly the raw arc budget.
This theorem adds no traversal to `prepare` or to the sweep. -/
theorem schedule_raw_row_sum_eq_arcCount (H : LabelledQuotient)
    {m : Nat} {P : _}
    (S : EX42.ArraySweep.Schedule (n := H.vertexCount) (m := m) P) :
    ((List.ofFn S.vertex).map
      (fun v => ((prepare H).1.row v).length)).sum = H.arcCount := by
  rw [sweep_sum_eq_rowMass H S, inputPreparePhases H,
    EX51.Storage.groupMap_rowMass]
  exact inputSuppliedCount H

private theorem sweep_filter_sum_le {α : Type u} (keep : α → Bool)
    (w : α → Nat) (xs : List α) :
    ((xs.filter keep).map w).sum ≤ (xs.map w).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    cases h : keep x <;> simp [List.filter, h] <;> omega

/-- Keeping only queued vertices assigned to `o` cannot increase the budget. -/
theorem schedule_owner_raw_row_sum_le_arcCount (H : LabelledQuotient)
    {m : Nat} {P : _}
    (S : EX42.ArraySweep.Schedule (n := H.vertexCount) (m := m) P)
    {Owner : Type u} [DecidableEq Owner]
    (owner : Fin H.vertexCount → Owner) (o : Owner) :
    ((((List.ofFn S.vertex).filter (fun v => decide (owner v = o))).map
      (fun v => ((prepare H).1.row v).length))).sum ≤ H.arcCount := by
  exact Nat.le_trans (sweep_filter_sum_le (fun v => decide (owner v = o))
    (fun v => ((prepare H).1.row v).length) (List.ofFn S.vertex))
    (Nat.le_of_eq (schedule_raw_row_sum_eq_arcCount H S))

end PaperB.EX24.InputPrepCheckpoint
