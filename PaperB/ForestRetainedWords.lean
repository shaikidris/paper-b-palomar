module

public import PaperB.ForestRetainedFieldBounds
public import PaperB.ForestBackWords
public import PaperB.FlatPairDictionary
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace BoundedScalarArray

def pack (xs : Array Nat) (lim : Nat)
    (fits : ∀ i : Fin xs.size, xs[i.val]'(i.isLt) < lim) : Array (Fin lim) :=
  Array.ofFn fun i : Fin xs.size => ⟨xs[i.val]'(i.isLt), fits i⟩

theorem size_pack (xs : Array Nat) (lim : Nat)
    (fits : ∀ i : Fin xs.size, xs[i.val]'(i.isLt) < lim) :
    (pack xs lim fits).size = xs.size := by
  simp only [pack, Array.size_ofFn]

theorem getElem_pack_val (xs : Array Nat) (lim : Nat)
    (fits : ∀ i : Fin xs.size, xs[i.val]'(i.isLt) < lim)
    (i : Fin xs.size) (hi : i.val < (pack xs lim fits).size) :
    ((pack xs lim fits)[i.val]'hi).val = xs[i.val]'(i.isLt) := by
  simp only [pack, Array.getElem_ofFn]

theorem getElem?_pack_map_val (xs : Array Nat) (lim : Nat)
    (fits : ∀ i : Fin xs.size, xs[i.val]'(i.isLt) < lim) (j : Nat) :
    ((pack xs lim fits)[j]?).map Fin.val = xs[j]? := by
  by_cases hj : j < xs.size
  · have hp : j < (pack xs lim fits).size := by
      simpa only [size_pack xs lim fits] using hj
    rw [getElem?_pos (pack xs lim fits) j hp, getElem?_pos xs j hj]
    exact congrArg some (getElem_pack_val xs lim fits ⟨j, hj⟩ hp)
  · have hp : ¬ j < (pack xs lim fits).size := by
      simpa only [size_pack xs lim fits] using hj
    rw [getElem?_neg (pack xs lim fits) j hp, getElem?_neg xs j hj] <;> rfl

end BoundedScalarArray

namespace PaperB.RetainedProperLoss

open _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead
open PaperB.ForestSlimIndex

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

structure WordColumns (bits : Nat) where
  dictionary : Array (Fin (2 ^ bits))
  back : BackWords bits
  labels : Array (Fin (2 ^ bits))
  entry : Array (Fin (2 ^ bits))
  stop : Array (Fin (2 ^ bits))

def WordColumns.wordCount {bits : Nat} (w : WordColumns bits) : Nat :=
  w.dictionary.size + w.back.tagAndFirst.size + w.back.second.size +
    w.labels.size + w.entry.size + w.stop.size

theorem dictionary_fits {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits) :
    FlatPairDictionary.Fits bits (ofOrderedReader r) := by
  have fields : H.vertexCount + 1 < 2 ^ bits := by omega
  apply FlatPairDictionary.Fits.ofDenseIds (ofOrderedReader r) (by omega)
  · intro i hi
    exact (dict_field_bounds r ⟨i, hi⟩).1
  · intro i hi
    exact (dict_field_bounds r ⟨i, hi⟩).2
  · intro i hi
    rw [getElem?_pos (ofOrderedReader r).slots i hi]
    exact Nat.lt_of_le_of_lt (slot_field_bound r ⟨i, hi⟩) fields
  · have sz := arraySize_le r
    unfold FlatPairDictionary.packedSize FlatPairDictionary.slotBase FlatPairDictionary.secondBase
    unfold Columns.arraySize at sz
    omega

def packWordColumns {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits) : WordColumns bits :=
  let s := ofOrderedReader r
  have fit : H.vertexCount + 1 < 2 ^ bits := by omega
  { dictionary := FlatPairDictionary.serialize s (dictionary_fits r cap)
    back := packBackWords s (by omega)
    labels := BoundedScalarArray.pack s.labels _ (fun i =>
      Nat.lt_of_le_of_lt (label_field_bound r i) fit)
    entry := BoundedScalarArray.pack s.entry _ (fun i =>
      Nat.lt_of_le_of_lt (entry_field_bound r i) fit)
    stop := BoundedScalarArray.pack s.stop _ (fun i =>
      Nat.lt_of_le_of_lt (stop_field_bound r i) fit) }

theorem packWordColumns_count_le {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits) :
    (packWordColumns r cap).wordCount ≤ 1 + 18 * H.vertexCount := by
  have sz := arraySize_le r
  unfold Columns.arraySize at sz
  simp only [WordColumns.wordCount, packWordColumns, FlatPairDictionary.retained_words,
    (packBackWords_size (ofOrderedReader r) (by omega : H.vertexCount < 2 ^ bits)).1,
    (packBackWords_size (ofOrderedReader r) (by omega : H.vertexCount < 2 ^ bits)).2,
    BoundedScalarArray.size_pack]
  omega

def WordColumns.labelAt {bits : Nat} (w : WordColumns bits) (v : Nat) : Nat :=
  ((w.labels[v]?).map Fin.val).getD 0

def WordColumns.known {bits : Nat} (w : WordColumns bits) (a v : Nat) : Bool :=
  let k := ((w.entry[w.labelAt v]?).map Fin.val).getD 0
  decide (((w.entry[a]?).map Fin.val).getD 0 ≤ k) &&
    decide (k < ((w.stop[a]?).map Fin.val).getD 0)

theorem packWordColumns_known {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits)
    (a v : Nat) :
    (packWordColumns r cap).known a v = (ofOrderedReader r).known a v := by
  simp only [WordColumns.known, WordColumns.labelAt, packWordColumns, Columns.known,
    Columns.labelAt, BoundedScalarArray.getElem?_pack_map_val] <;> rfl

end PaperB.RetainedProperLoss
