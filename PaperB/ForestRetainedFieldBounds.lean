module

public import PaperB.ForestSlimIndex
public import PaperB.StaticLinearHead

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RetainedProperLoss

open _root_.EX24 _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

theorem dict_field_bounds (i : Fin (ofOrderedReader r).dict.size) :
    let k := (ofOrderedReader r).dict[i.val]'i.isLt
    k.1 < H.vertexCount ∧ k.2 < H.vertexCount := by
  let k := (ofOrderedReader r).dict[i.val]'i.isLt
  have hm : k ∈ (ofOrderedReader r).dict.toList := by
    apply List.mem_iff_getElem.mpr
    exact ⟨i.val, by simp, by simp [k]⟩
  change k ∈ (ForestDictionary.dictionary p orderedPairCode).toList at hm
  obtain ⟨_, q, _, hq⟩ := ((ForestDictionary.dictionary_spec p orderedPairCode).2.1 k).mp hm
  change k.1 < H.vertexCount ∧ k.2 < H.vertexCount
  rw [← hq]
  cases q
  exact ⟨Fin.isLt _, Fin.isLt _⟩

theorem slot_field_bound (i : Fin (ofOrderedReader r).slots.size) :
    (ofOrderedReader r).slots[i.val]'i.isLt ≤ H.vertexCount + 1 := by
  have hi : i.val < r.out.tables.slots.size := i.isLt
  have hr : r.out.tables.slotAt i.val = (ofOrderedReader r).slots[i.val]'i.isLt := by
    unfold Tables.slotAt
    rw [getElem?_pos r.out.tables.slots i.val hi]
    rfl
  rw [← hr]
  by_cases zero : r.out.tables.slotAt i.val = 0
  · simp [zero]
  · obtain ⟨_, _, hG, _, _⟩ := r.index.ok.2.2
    obtain ⟨q, _, hq⟩ := hG.forward i.val zero
    exact Nat.le_trans (Nat.le_of_lt (hG.backward _ q hq).1) r.index.ok.2.1

theorem label_field_bound (i : Fin (ofOrderedReader r).labels.size) :
    (ofOrderedReader r).labels[i.val]'i.isLt ≤ H.vertexCount + 1 := by
  have hi : i.val < r.out.labels.size := i.isLt
  let v : Vertex H := ⟨i.val, by simpa only [r.index.ok.1] using hi⟩
  have hr : (selectors (orderedConfig p large) r.out).label v =
      (ofOrderedReader r).labels[i.val]'i.isLt := by
    change (r.out.labels[i.val]?).getD 0 = _
    rw [getElem?_pos r.out.labels i.val hi]
    rfl
  obtain ⟨_, _, hG, _, ⟨E⟩⟩ := r.index.ok.2.2
  have hl := E.label_lt v True.intro
  rw [hr, hG.size_eq] at hl
  exact Nat.le_trans (Nat.le_of_lt hl) r.index.ok.2.1

theorem entry_field_bound (i : Fin (ofOrderedReader r).entry.size) :
    (ofOrderedReader r).entry[i.val]'i.isLt ≤ H.vertexCount + 1 := by
  let table := r.index.reader
  let v : Fin (nodeCount (orderedConfig p large) r.out) :=
    ⟨i.val, by
      have hs : i.val < table.layout.endpoints.entry.data.size := i.isLt
      exact table.layout.endpoints.entry.len ▸ hs⟩
  have ht : table.entry v < nodeCount (orderedConfig p large) r.out := by
    rw [table.entry_exact]
    exact Nat.lt_of_lt_of_le (entry_lt_length_dfsPreorder table.input_ok v)
      (Nat.le_of_eq (length_dfsPreorder table.input_ok))
  exact Nat.le_trans (Nat.le_of_lt ht) (nodeCount_le r.index.ok)

theorem stop_field_bound (i : Fin (ofOrderedReader r).stop.size) :
    (ofOrderedReader r).stop[i.val]'i.isLt ≤ H.vertexCount + 1 := by
  let table := r.index.reader
  let v : Fin (nodeCount (orderedConfig p large) r.out) :=
    ⟨i.val, by
      have hs : i.val < table.layout.endpoints.stop.data.size := i.isLt
      exact table.layout.endpoints.stop.len ▸ hs⟩
  obtain ⟨pre, post, hsplit⟩ := exists_split_dfsPreorder table.input_ok v
  have hlen := congrArg List.length hsplit
  rw [length_dfsPreorder table.input_ok] at hlen
  simp only [List.length_append] at hlen
  have ht : table.stop v ≤ nodeCount (orderedConfig p large) r.out := by
    rw [table.stop_exact, entry_eq_length_of_dfsPreorder_split table.input_ok hsplit]
    omega
  exact Nat.le_trans ht (nodeCount_le r.index.ok)

end PaperB.RetainedProperLoss
