module

public import PaperB.ForestOrderedReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

namespace RetainedProperLoss

private abbrev keyTypeOf {K : Type} (_ : Array K → Prop) : Type := K

abbrev EncodedKey : Type := keyTypeOf PairLookup.StrictSorted

private def encode {H : LabelledQuotient} (q : CutPair H) : EncodedKey := by
  first
  | exact orderedPairCode q
  | exact orderedPairCode H q
  | exact ForestDictionary.orderedPairCode q
  | exact ForestDictionary.orderedPairCode H q

/-- The retained index stores six arrays, with no reader, configuration,
    sweep state, or callback. -/
structure Columns (H : LabelledQuotient) where
  dict : Array EncodedKey
  slots : Array Nat
  back : Array (Option (CutPair H))
  labels : Array Nat
  entry : Array Nat
  stop : Array Nat

namespace Columns

def checked {H : LabelledQuotient} [DecidableEq (CutPair H)]
    (s : Columns H) (key : EncodedKey) (q : CutPair H) : Option Nat :=
  match (PairLookup.lookup s.dict key).1 with
  | none => none
  | some i =>
      let a := (s.slots[i]?).getD 0
      if a ≠ 0 ∧ s.back[a]? = some (some q) then some a else none

def labelAt {H : LabelledQuotient} (s : Columns H) (i : Nat) : Nat :=
  (s.labels[i]?).getD 0

/-- `i` is the scalar vertex slot; `a` is a checked node address. -/
def known {H : LabelledQuotient} (s : Columns H) (a i : Nat) : Bool :=
  let k := (s.entry[s.labelAt i]?).getD 0
  decide ((s.entry[a]?).getD 0 ≤ k) && decide (k < (s.stop[a]?).getD 0)

def contains {H : LabelledQuotient} [DecidableEq (CutPair H)]
    (s : Columns H) (q : CutPair H) (i : Nat) : Bool :=
  match s.checked (encode q) q with
  | none => false
  | some a => s.known a i

/-- Total number of retained array elements. -/
def arraySize {H : LabelledQuotient} (s : Columns H) : Nat :=
  s.dict.size + s.slots.size + s.back.size + s.labels.size +
    s.entry.size + s.stop.size

end Columns

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]

/-- Take the existing columns, including the reader's two DFS endpoint arrays. -/
def ofOrderedReader (r : OrderedReaderResult p data size_data rank large) :
    Columns H where
  dict := (orderedConfig p large).dict
  slots := r.out.tables.slots
  back := r.out.tables.back
  labels := r.out.labels
  entry := r.index.reader.layout.endpoints.entry.data
  stop := r.index.reader.layout.endpoints.stop.data

/-- The executable projection shares the dictionary constructed by the sweep. -/
def ofOrderedReaderShared (r : OrderedReaderResult p data size_data rank large) :
    Columns H where
  dict := r.dictionary
  slots := r.out.tables.slots
  back := r.out.tables.back
  labels := r.out.labels
  entry := r.index.reader.layout.endpoints.entry.data
  stop := r.index.reader.layout.endpoints.stop.data

@[csimp] theorem ofOrderedReader_csimp : @ofOrderedReader = @ofOrderedReaderShared := by
  funext H p data size_data rank large inst r
  unfold ofOrderedReader ofOrderedReaderShared
  rw [r.dictionary_eq]

theorem dict_sorted (r : OrderedReaderResult p data size_data rank large) :
    PairLookup.StrictSorted (ofOrderedReader r).dict :=
  (orderedConfig p large).sorted

theorem checked_eq (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) :
    (ofOrderedReader r).checked (encode q) q =
      checkedNode? (orderedConfig p large) r.out q :=
  rfl

theorem checked_iff_back (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (a : Nat) :
    (ofOrderedReader r).checked (encode q) q = some a ↔
      (ofOrderedReader r).back[a]? = some (some q) := by
  rw [checked_eq r q]
  exact checkedNode_iff_back r.index.ok

theorem labelAt_eq (r : OrderedReaderResult p data size_data rank large)
    (v : Vertex H) :
    (ofOrderedReader r).labelAt ((orderedConfig p large).vertexIndex v) =
      (r.index.label v).val :=
  rfl

theorem known_eq (r : OrderedReaderResult p data size_data rank large)
    (a : Fin (nodeCount (orderedConfig p large) r.out)) (v : Vertex H) :
    (ofOrderedReader r).known a.val ((orderedConfig p large).vertexIndex v) =
      r.index.known a v := by
  let e := r.index.reader.layout.endpoints.entry
  let t := r.index.reader.layout.endpoints.stop
  let l := r.index.label v
  have hl : l.val < e.data.size := by
    rw [e.len]
    exact l.isLt
  have he : a.val < e.data.size := by
    rw [e.len]
    exact a.isLt
  have ht : a.val < t.data.size := by
    rw [t.len]
    exact a.isLt
  change
    (let k := (e.data[l.val]?).getD 0
     decide ((e.data[a.val]?).getD 0 ≤ k) &&
       decide (k < (t.data[a.val]?).getD 0)) =
    (let k := e.read l
     decide (e.read a ≤ k) && decide (k < t.read a))
  simp [hl, he, ht, StaticHeadSweep.Slots.read] <;> rfl

/-- The retained Boolean agrees with the ordered reader on every query. -/
theorem contains_eq (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (v : Vertex H) :
    (ofOrderedReader r).contains q ((orderedConfig p large).vertexIndex v) =
      r.index.contains q v := by
  unfold Columns.contains
  rw [checked_eq r q]
  cases hit : checkedNode? (orderedConfig p large) r.out q with
  | none =>
      exact (r.index.contains_miss hit v).symm
  | some a =>
      exact (known_eq r ⟨a, (checkedNode_occupied r.index.ok hit).1⟩ v).trans
        (r.index.contains_hit hit v).symm

/-- A positive query requires both the exact reverse key and the DFS test at
    its retained address. This statement uses only retained reads. -/
theorem contains_iff_back_and_known
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (i : Nat) :
    (ofOrderedReader r).contains q i = true ↔
      ∃ a : Nat, (ofOrderedReader r).back[a]? = some (some q) ∧
        (ofOrderedReader r).known a i = true := by
  constructor
  · intro h
    cases hit : (ofOrderedReader r).checked (encode q) q with
    | none =>
        simp [Columns.contains, hit] at h
    | some a =>
        exact ⟨a, (checked_iff_back r q a).mp hit,
          by simpa only [Columns.contains, hit] using h⟩
  · rintro ⟨a, hb, hk⟩
    have hit := (checked_iff_back r q a).mpr hb
    simpa only [Columns.contains, hit] using hk

private theorem grounded_column_sizes
    (r : OrderedReaderResult p data size_data rank large) :
    r.out.tables.slots.size = (orderedConfig p large).dict.size ∧
      r.out.tables.back.size = (orderedConfig p large).region.maxNodes + 1 := by
  obtain ⟨_, _, G, _, _⟩ := r.index.ok.2.2
  exact ⟨G.slot_size, G.back_size⟩

/-- The checked dictionary address, using the same key as `Columns.contains`. -/
def checkedHit (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) : Option Nat :=
  (ofOrderedReader r).checked (encode q) q

private theorem exists_checkedHit_known_iff_properLoss
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (y : Vertex H) (hq : q.fst < q.snd) :
    (∃ a : Nat, checkedHit r q = some a ∧
      (ofOrderedReader r).known a ((orderedConfig p large).vertexIndex y) = true) ↔
      H.ProperLoss q y := by
  have hc :
      (ofOrderedReader r).contains q ((orderedConfig p large).vertexIndex y) =
        true ↔ H.ProperLoss q y := by
    rw [contains_eq r q y, r.contains_true_iff q y]
    exact ⟨fun h => h.2, fun h => ⟨hq, h⟩⟩
  have hb := contains_iff_back_and_known r q ((orderedConfig p large).vertexIndex y)
  simpa only [checkedHit, checked_iff_back r q] using (hb.symm.trans hc)

theorem not_properLoss_of_checkedHit_none
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (y : Vertex H) (hq : q.fst < q.snd)
    (miss : checkedHit r q = none) :
    ¬ H.ProperLoss q y := by
  intro hl
  obtain ⟨a, hit, _⟩ := (exists_checkedHit_known_iff_properLoss r q y hq).mpr hl
  have impossible : (none : Option Nat) = some a := miss.symm.trans hit
  cases impossible

theorem known_true_iff_properLoss_of_checkedHit_some
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (y : Vertex H) (hq : q.fst < q.snd)
    (a : Nat) (hit : checkedHit r q = some a) :
    (ofOrderedReader r).known a ((orderedConfig p large).vertexIndex y) = true ↔
      H.ProperLoss q y := by
  have h := exists_checkedHit_known_iff_properLoss r q y hq
  constructor
  · intro hk
    exact h.mp ⟨a, hit, hk⟩
  · intro hl
    obtain ⟨b, hit', hk⟩ := h.mpr hl
    have hab : a = b := Option.some.inj (hit.symm.trans hit')
    subst b
    exact hk

/-- A proper-loss target exists exactly when the checked lookup returns an
    address whose retained `known` read is true at some vertex. -/
theorem exists_properLoss_iff_checkedHit_known
    (r : OrderedReaderResult p data size_data rank large)
    (q : CutPair H) (hq : q.fst < q.snd) :
    (∃ y : Vertex H, H.ProperLoss q y) ↔
      ∃ (a : Nat) (y : Vertex H), checkedHit r q = some a ∧
        (ofOrderedReader r).known a ((orderedConfig p large).vertexIndex y) = true := by
  constructor
  · rintro ⟨y, hl⟩
    obtain ⟨a, hit, hk⟩ := (exists_checkedHit_known_iff_properLoss r q y hq).mpr hl
    exact ⟨a, y, hit, hk⟩
  · rintro ⟨a, y, hit, hk⟩
    exact ⟨y, (known_true_iff_properLoss_of_checkedHit_some r q y hq a hit).mp hk⟩

/-- The six arrays use at most `9 * H.vertexCount` elements in total. -/
theorem arraySize_le (r : OrderedReaderResult p data size_data rank large) :
    (ofOrderedReader r).arraySize ≤ 9 * H.vertexCount := by
  have hd : (orderedConfig p large).dict.size ≤ H.vertexCount := by
    change (ForestDictionary.dictionary p (encode (H := H))).size ≤ H.vertexCount
    exact (ForestDictionary.dictionary_spec p (encode (H := H))).2.2
  obtain ⟨hs, hb⟩ := grounded_column_sizes r
  have hm : (orderedConfig p large).region.maxNodes ≤ H.vertexCount + 1 := by
    first
    | change H.vertexCount + 1 ≤ H.vertexCount + 1
      exact Nat.le_refl _
    | change H.vertexCount ≤ H.vertexCount + 1
      omega
    | simp [orderedConfig] <;> omega
  have hl : r.out.labels.size ≤ H.vertexCount + 1 := by
    have h := r.index.ok.1
    omega
  have hn : nodeCount (orderedConfig p large) r.out ≤ H.vertexCount + 2 := by
    have hok := r.index.ok
    first
    | have h : nodeCount (orderedConfig p large) r.out ≤ H.vertexCount + 1 := by
        apply nodeCount_le <;> first | exact hok | exact r.index | exact large
      omega
    | have h : nodeCount (orderedConfig p large) r.out ≤ H.vertexCount := by
        apply nodeCount_le <;> first | exact hok | exact r.index | exact large
      omega
    | have h : nodeCount (orderedConfig p large) r.out ≤
          (orderedConfig p large).region.maxNodes + 1 := by
        apply nodeCount_le <;> first | exact hok | exact r.index | exact large
      omega
    | have h : nodeCount (orderedConfig p large) r.out ≤
          (orderedConfig p large).region.maxNodes := by
        apply nodeCount_le <;> first | exact hok | exact r.index | exact large
      omega
  have he : (ofOrderedReader r).entry.size =
      nodeCount (orderedConfig p large) r.out :=
    r.index.reader.layout.endpoints.entry.len
  have ht : (ofOrderedReader r).stop.size =
      nodeCount (orderedConfig p large) r.out :=
    r.index.reader.layout.endpoints.stop.len
  unfold Columns.arraySize
  rw [he, ht]
  change (orderedConfig p large).dict.size + r.out.tables.slots.size +
      r.out.tables.back.size + r.out.labels.size +
      nodeCount (orderedConfig p large) r.out +
      nodeCount (orderedConfig p large) r.out ≤ 9 * H.vertexCount
  omega

end RetainedProperLoss
end PaperB

-- Append this section to ForestSlimIndex.lean, where the private `encode`
-- used by Columns.contains is in scope.

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

namespace RetainedProperLoss

namespace Columns

variable {H : LabelledQuotient}

/-- Use the actual lookup result and probe count. A hit reads `slots`;
    only a nonzero address proceeds to the `back` read. -/
def checkedCounted [DecidableEq (CutPair H)]
    (s : Columns H) (key : EncodedKey) (q : CutPair H) : Option Nat × Nat :=
  let r := PairLookup.lookup s.dict key
  match r.1 with
  | none => (none, r.2)
  | some i =>
      let a := (s.slots[i]?).getD 0
      if a ≠ 0 then
        (if s.back[a]? = some (some q) then some a else none, r.2 + 2)
      else
        (none, r.2 + 1)

theorem checkedCounted_value [DecidableEq (CutPair H)]
    (s : Columns H) (key : EncodedKey) (q : CutPair H) :
    (s.checkedCounted key q).1 = s.checked key q := by
  cases h : (PairLookup.lookup s.dict key).1 with
  | none => simp [checkedCounted, checked, h]
  | some i =>
      by_cases ha : (s.slots[i]?).getD 0 ≠ 0 <;>
        simp [checkedCounted, checked, h, ha]

theorem checkedCounted_count_le [DecidableEq (CutPair H)]
    (s : Columns H) (key : EncodedKey) (q : CutPair H) :
    (s.checkedCounted key q).2 ≤ (PairLookup.lookup s.dict key).2 + 2 := by
  cases h : (PairLookup.lookup s.dict key).1 with
  | none => simp [checkedCounted, h]
  | some i =>
      by_cases ha : (s.slots[i]?).getD 0 ≠ 0 <;>
        simp [checkedCounted, h, ha] <;> omega

/-- Four array accesses in the charged interval test: `labels[i]`,
    `entry[label]`, `entry[a]`, and `stop[a]`. Bind both endpoints before
    combining the comparison results. -/
def knownCounted (s : Columns H) (a i : Nat) : Bool × Nat :=
  let label := s.labelAt i
  let k := (s.entry[label]?).getD 0
  let lo := (s.entry[a]?).getD 0
  let hi := (s.stop[a]?).getD 0
  (decide (lo ≤ k) && decide (k < hi), 4)

theorem knownCounted_value (s : Columns H) (a i : Nat) :
    (s.knownCounted a i).1 = s.known a i := rfl

theorem knownCounted_count (s : Columns H) (a i : Nat) :
    (s.knownCounted a i).2 = 4 := rfl

def containsCounted [DecidableEq (CutPair H)]
    (s : Columns H) (q : CutPair H) (i : Nat) : Bool × Nat :=
  let r := s.checkedCounted (encode q) q
  match r.1 with
  | none => (false, r.2)
  | some a =>
      let t := s.knownCounted a i
      (t.1, r.2 + t.2)

theorem containsCounted_value [DecidableEq (CutPair H)]
    (s : Columns H) (q : CutPair H) (i : Nat) :
    (s.containsCounted q i).1 = s.contains q i := by
  simp only [containsCounted, contains, checkedCounted_value]
  cases s.checked (encode q) q <;> rfl

theorem containsCounted_count_le [DecidableEq (CutPair H)]
    (s : Columns H) (q : CutPair H) (i : Nat) :
    (s.containsCounted q i).2 ≤ Nat.log2 (s.dict.size + 1) + 8 := by
  have hc := checkedCounted_count_le s (encode q) q
  have hl := PairLookup.lookup_count_le s.dict (encode q)
  have hi :
      (s.containsCounted q i).2 ≤ (s.checkedCounted (encode q) q).2 + 4 := by
    cases h : (s.checkedCounted (encode q) q).1 with
    | none => simp [containsCounted, h]
    | some a => simp [containsCounted, h, knownCounted_count]
  omega

end Columns

/-- The dictionary bound is for the actual retained dictionary and encoder. -/
theorem ofOrderedReader_dict_size_le
    {H : LabelledQuotient} {p : ForestDictionary.Rows H}
    {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    [DecidableEq (CutPair H)]
    (r : OrderedReaderResult p data size_data rank large) :
    (ofOrderedReader r).dict.size ≤ H.vertexCount := by
  change (ForestDictionary.dictionary p (encode (H := H))).size ≤ H.vertexCount
  exact (ForestDictionary.dictionary_spec p (encode (H := H))).2.2

end RetainedProperLoss
end PaperB
