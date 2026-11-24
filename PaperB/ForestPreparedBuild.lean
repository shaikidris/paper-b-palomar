module

public import PaperB.ForestIncomingPrep
public import PaperB.ForestFastOrderedReader
public import PaperB.ForestOrderedReadBound
public import PaperB.ForestAllSizes

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestPreparedBuild

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.AggregateEX24
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open ForestIncomingRaw (arcTotal)

private theorem cover (H : LabelledQuotient) : ForestIncomingPrep.Cover H := by
  intro u y
  rfl

private theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
  first
  | exact List.nodup_finRange n
  | exact List.nodup_finRange
  | (simp; done)
  | exact?

private theorem ofFn_eq_map_finRange {α : Type} {n : Nat} (f : Fin n → α) :
    List.ofFn f = (List.finRange n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

private theorem array_toList_by_index {α : Type} (a : Array α) {n : Nat}
    (hn : a.size = n) :
    a.toList =
      (List.finRange n).map (fun i => a[i.val]'(by rw [hn]; exact i.isLt)) := by
  apply List.ext_getElem
  · simp [hn]
  · intro i hi hj
    first
    | (simp; done)
    | simp only [Array.getElem_toList, List.getElem_map, List.getElem_finRange]

private theorem foldl_mass {α : Type} (w : α → Nat) (xs : List α) (s : Nat) :
    xs.foldl (fun k x => k + w x) s = s + (xs.map w).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem array_foldl_mass {α : Type} (a : Array α) (w : α → Nat) :
    a.foldl (fun k x => k + w x) 0 = (a.toList.map w).sum := by
  have h : a.foldl (fun k x => k + w x) 0 =
      a.toList.foldl (fun k x => k + w x) 0 := by
    first
    | rfl
    | (rw [Array.foldl_toList]; done)
    | (rw [Array.foldl_eq_foldl_toList]; done)
    | (simp; done)
    | exact?
  rw [h, foldl_mass] <;> simp

private theorem finRange_mass_eq_toList_mass {α : Type}
    (a : Array α) {n : Nat} (hn : a.size = n) (w : α → Nat) :
    ((List.finRange n).map (fun i => w (a[i.val]'(by rw [hn]; exact i.isLt)))).sum =
      (a.toList.map w).sum := by
  rw [array_toList_by_index a hn, List.map_map] <;> rfl

private theorem finRange_mass_eq_array_foldl {α : Type}
    (a : Array α) {n : Nat} (hn : a.size = n) (w : α → Nat) :
    ((List.finRange n).map (fun i => w (a[i.val]'(by rw [hn]; exact i.isLt)))).sum =
      a.foldl (fun k x => k + w x) 0 :=
  (finRange_mass_eq_toList_mass a hn w).trans (array_foldl_mass a w).symm

private theorem finRange_mass_eq_mapped_foldl {α : Type}
    (a : Array α) {n : Nat} (hn : a.size = n) (w : α → Nat) :
    ((List.finRange n).map (fun i => w (a[i.val]'(by rw [hn]; exact i.isLt)))).sum =
      (a.map w).foldl (· + ·) 0 := by
  calc
    _ = (a.toList.map w).sum := finRange_mass_eq_toList_mass a hn w
    _ = ((a.map w).toList).sum := by simp
    _ = (a.map w).foldl (· + ·) 0 := by
      simpa using (array_foldl_mass (a.map w) id).symm

private theorem occurrenceRows_lengthSum {α : Type} (rows : List (List α)) :
    listLengthSum rows = (rows.map List.length).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [listLengthSum, ih]

theorem arcTotal_eq_arcCount (H : LabelledQuotient) :
    arcTotal H = H.arcCount := by
  unfold arcTotal LabelledQuotient.arcCount
  rw [occurrenceRows_lengthSum]
  exact finRange_mass_eq_toList_mass H.adj H.adj_size List.length

private theorem remove_mass {α : Type} (w : α → Nat) (a : α)
    (ys : List α) (ha : a ∈ ys) :
    ∃ zs : List α, (ys.map w).sum = w a + (zs.map w).sum ∧
      ∀ b, b ≠ a → b ∈ ys → b ∈ zs := by
  induction ys with
  | nil => cases ha
  | cons y ys ih =>
    rcases List.mem_cons.mp ha with h | h
    · subst y
      exact ⟨ys, rfl, fun b hn hb => (List.mem_cons.mp hb).resolve_left hn⟩
    · obtain ⟨zs, hz, hm⟩ := ih h
      refine ⟨y :: zs, ?_, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        omega
      · intro b hn hb
        rcases List.mem_cons.mp hb with e | hb
        · exact List.mem_cons.mpr (Or.inl e)
        · exact List.Mem.tail y (hm b hn hb)

private theorem sum_le_of_nodup_subset {α : Type} (w : α → Nat)
    (xs ys : List α) (hx : xs.Nodup) (hxy : ∀ x ∈ xs, x ∈ ys) :
    (xs.map w).sum ≤ (ys.map w).sum := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    have hn := List.nodup_cons.mp hx
    obtain ⟨zs, hz, hm⟩ := remove_mass w x ys (hxy x (List.Mem.head _))
    have ht := ih zs hn.2 (fun b hb =>
      hm b (fun e => hn.1 (e ▸ hb)) (hxy b (List.Mem.tail x hb)))
    rw [hz]
    exact Nat.add_le_add_left ht (w x)

private theorem nodup_map_of_injective {α β : Type} (f : α → β)
    (hf : ∀ {a b : α}, f a = f b → a = b)
    (xs : List α) (hx : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hn := List.nodup_cons.mp hx
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hn.2⟩
    intro hm
    obtain ⟨b, hb, he⟩ := List.mem_map.mp hm
    exact hn.1 ((hf he) ▸ hb)

private theorem entryTotal_eq_map_sum {H : LabelledQuotient} (rs : List (Row H)) :
    entryTotal rs = (rs.map fun r => r.tests.length).sum := by
  first
  | rfl
  | (simp [entryTotal, foldl_mass]; done)
  | (induction rs with
     | nil => rfl
     | cons r rs ih =>
       simp only [List.map_cons, List.sum_cons]
       change r.tests.length + entryTotal rs = _
       rw [ih])

private theorem ordered_entryTotal_indices {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount) :
    entryTotal (orderedRows p data size_data) =
      ((List.finRange H.vertexCount).map fun i =>
        (p.row (orderedVertexAt data size_data i)).length).sum := by
  rw [entryTotal_eq_map_sum, orderedRows, ofFn_eq_map_finRange, List.map_map]
  rfl

section

variable {H : LabelledQuotient}
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) <
    rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)

include rank increasing covers in
theorem ordered_entryTotal_eq (p : ForestDictionary.Rows H) :
    entryTotal (orderedRows p data size_data) =
      ((List.finRange H.vertexCount).map fun v => (p.row v).length).sum := by
  let atVertex := orderedVertexAt data size_data
  let ys := (List.finRange H.vertexCount).map atVertex
  let w := fun v : Vertex H => (p.row v).length
  have hinj : ∀ {i j : Fin H.vertexCount}, atVertex i = atVertex j → i = j := by
    intro i j h
    change orderedVertexAt data size_data i = orderedVertexAt data size_data j at h
    apply Fin.ext
    by_cases hij : i.val < j.val
    · have hh := increasing i j hij
      rw [h] at hh
      exact False.elim ((Nat.lt_irrefl _) hh)
    · by_cases hji : j.val < i.val
      · have hh := increasing j i hji
        rw [h] at hh
        exact False.elim ((Nat.lt_irrefl _) hh)
      · omega
  have hn : ys.Nodup :=
    nodup_map_of_injective atVertex hinj _ (finRange_nodup _)
  have hall : ∀ v : Vertex H, v ∈ ys := by
    intro v
    obtain ⟨i, hi⟩ := covers v
    exact List.mem_map.mpr ⟨i, by simp, hi⟩
  calc
    entryTotal (orderedRows p data size_data) = (ys.map w).sum := by
      simpa only [ys, atVertex, w, List.map_map, Function.comp_def] using
        ordered_entryTotal_indices p data size_data
    _ = ((List.finRange H.vertexCount).map w).sum := by
      apply Nat.le_antisymm
      · exact sum_le_of_nodup_subset w ys _ hn (fun v _ => by simp)
      · exact sum_le_of_nodup_subset w _ ys (finRange_nodup _) (fun v _ => hall v)

include rank increasing covers in
theorem entryTotal_le_arcTotal :
    entryTotal (orderedRows (ForestIncomingPrep.build H (cover H)).tests
      data size_data) ≤ arcTotal H := by
  rw [ordered_entryTotal_eq data size_data rank increasing covers]
  simpa only [ForestIncomingRaw.length_supplied] using
    ForestIncomingPrep.testLengths_le H (cover H)

end

theorem dedup_visits_eq_arcCount (H : LabelledQuotient) :
    (ForestIncomingPrep.build H (cover H)).visits = H.arcCount := by
  rw [ForestIncomingPrep.visits_supplied, ForestIncomingRaw.length_supplied,
    arcTotal_eq_arcCount]

abbrev Index (H : LabelledQuotient) := QuotientMembership.Index H

section

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) <
    rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

def build : Index H :=
  let prep := ForestIncomingPrep.build H (cover H)
  if large : 3 ≤ H.vertexCount then
    some (RetainedProperLoss.ofOrderedReader
      (runOrderedReaderFast prep.tests data size_data rank large
        increasing covers rankArc flat))
  else
    none

theorem build_of_small (small : H.vertexCount < 3) :
    build data size_data rank increasing covers rankArc flat = none := by
  have hn : ¬ 3 ≤ H.vertexCount := by omega
  simp only [build, dite_eq_right hn]

private theorem query_with_slot
    {p : ForestDictionary.Rows H} {large : 3 ≤ H.vertexCount}
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (v : Vertex H)
    (slot : {i : Nat // ∀ (p' : ForestDictionary.Rows H)
        (large' : 3 ≤ H.vertexCount), (orderedConfig p' large').vertexIndex v = i}) :
    (RetainedProperLoss.ofOrderedReader r).contains q slot.val =
      r.index.contains q v := by
  have h := RetainedProperLoss.contains_eq r q v
  rw [slot.property p large] at h
  exact h

private theorem query_columns
    {p : ForestDictionary.Rows H} {large : 3 ≤ H.vertexCount}
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (v : Vertex H) :
    QuotientMembership.Index.contains (some (RetainedProperLoss.ofOrderedReader r))
      q v = r.index.contains q v := by
  unfold QuotientMembership.Index.contains
  exact query_with_slot data size_data rank r q v _

theorem query_iff (q : CutPair H) (v : Vertex H) :
    QuotientMembership.Index.contains
        (build data size_data rank increasing covers rankArc flat) q v = true ↔
      q.fst < q.snd ∧ H.ProperLoss q v := by
  by_cases large : 3 ≤ H.vertexCount
  · rw [build, dite_eq_left large, query_columns]
    exact (runOrderedReaderFast (ForestIncomingPrep.build H (cover H)).tests
      data size_data rank large increasing covers rankArc flat).contains_true_iff q v
  · exact (PaperB.SmallQuotient.cutPair_impossible_of_small (by omega) q).elim

theorem arraySize_le :
    QuotientMembership.Index.arraySize
      (build data size_data rank increasing covers rankArc flat) ≤
      9 * H.vertexCount := by
  by_cases large : 3 ≤ H.vertexCount
  · simpa only [build, dite_eq_left large, QuotientMembership.Index.arraySize] using
      (RetainedProperLoss.arraySize_le
        (runOrderedReaderFast (ForestIncomingPrep.build H (cover H)).tests
          data size_data rank large increasing covers rankArc flat))
  · simpa only [build, dite_eq_right large, QuotientMembership.Index.arraySize] using
      (Nat.zero_le (9 * H.vertexCount))

end

end PaperB.ForestPreparedBuild
