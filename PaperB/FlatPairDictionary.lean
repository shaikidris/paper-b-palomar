module

public import PaperB.ForestSlimIndex
public import PaperB.RamLexPairCuts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestSlimIndex.FlatPairDictionary

open PaperB.PairLookup.ColumnReduction (Slice)

abbrev Word (bits : Nat) := PaperB.PairLookup.ColumnReduction.ScalarWord bits

variable {bits : Nat} {H : PaperB.LabelledQuotient}

/- Layout: [dict length | first keys | second keys | slots].
   The slot region has its own length, recovered from the buffer size.
   In particular, serialization does not assume slots.size = dict.size. -/

def secondBase (n : Nat) : Nat := 1 + n

def slotBase (n : Nat) : Nat := secondBase n + n

def packedSize (s : PaperB.RetainedProperLoss.Columns H) : Nat :=
  slotBase s.dict.size + s.slots.size

/-- The first two obligations concern key values, not row numbers.
    Slot addresses have a separate fit obligation. Strict capacity
    makes the final one-past address representable as a word. -/
structure Fits (bits : Nat) (s : PaperB.RetainedProperLoss.Columns H) : Prop where
  first : ∀ (i : Nat) (hi : i < s.dict.size), (s.dict[i]'hi).1 < 2 ^ bits
  second : ∀ (i : Nat) (hi : i < s.dict.size), (s.dict[i]'hi).2 < 2 ^ bits
  slot : ∀ i : Nat, i < s.slots.size → (s.slots[i]?).getD 0 < 2 ^ bits
  capacity : packedSize s < 2 ^ bits

/-- For a dictionary certified to store dense vertex IDs, one vertex-count
    bound discharges both key-field obligations. It does not bound slots. -/
theorem Fits.ofDenseIds (s : PaperB.RetainedProperLoss.Columns H)
    (verticesFit : H.vertexCount ≤ 2 ^ bits)
    (firstDense : ∀ (i : Nat) (hi : i < s.dict.size),
      (s.dict[i]'hi).1 < H.vertexCount)
    (secondDense : ∀ (i : Nat) (hi : i < s.dict.size),
      (s.dict[i]'hi).2 < H.vertexCount)
    (slotsFit : ∀ i : Nat, i < s.slots.size →
      (s.slots[i]?).getD 0 < 2 ^ bits)
    (capacity : packedSize s < 2 ^ bits) : Fits bits s where
  first i hi := Nat.lt_of_lt_of_le (firstDense i hi) verticesFit
  second i hi := Nat.lt_of_lt_of_le (secondDense i hi) verticesFit
  slot := slotsFit
  capacity := capacity

private def cell (s : PaperB.RetainedProperLoss.Columns H) (f : Fits bits s)
    (j : Fin (packedSize s)) : Word bits :=
  if h0 : j.val = 0 then
    ⟨s.dict.size, by
      have hc := f.capacity
      unfold packedSize slotBase secondBase at hc
      omega⟩
  else if h1 : j.val < secondBase s.dict.size then
    have hi : j.val - 1 < s.dict.size := by
      unfold secondBase at h1
      omega
    ⟨(s.dict[j.val - 1]'hi).1, f.first (j.val - 1) hi⟩
  else if h2 : j.val < slotBase s.dict.size then
    have hi : j.val - secondBase s.dict.size < s.dict.size := by
      unfold slotBase at h2
      omega
    ⟨(s.dict[j.val - secondBase s.dict.size]'hi).2,
      f.second (j.val - secondBase s.dict.size) hi⟩
  else
    ⟨(s.slots[j.val - slotBase s.dict.size]?).getD 0,
      f.slot (j.val - slotBase s.dict.size) (by
        have hj := j.isLt
        unfold packedSize at hj
        omega)⟩

/-- The only retained data is this buffer. No back keys are serialized. -/
def serialize (s : PaperB.RetainedProperLoss.Columns H) (f : Fits bits s) :
    Array (Word bits) :=
  Array.ofFn (cell s f)

@[simp] theorem serialize_size (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) : (serialize s f).size = packedSize s := by
  simp [serialize]

theorem retained_words (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) :
    (serialize s f).size = 1 + s.dict.size + s.dict.size + s.slots.size := by
  simpa only [packedSize, slotBase, secondBase] using serialize_size s f

def rowCount (xs : Array (Word bits)) : Nat :=
  ((xs[0]?).map Fin.val).getD 0

/-- Layout validity is erased. The first inequality also excludes an empty
    buffer, so a valid buffer always has an actual header word. -/
structure Valid (xs : Array (Word bits)) : Prop where
  keysWithin : slotBase (rowCount xs) ≤ xs.size
  capacity : xs.size < 2 ^ bits

private def sliceAt (xs : Array (Word bits)) (v : Valid xs)
    (base len : Nat) (h : base + len ≤ xs.size) : Slice xs where
  base := ⟨base, by have hc := v.capacity; omega⟩
  len := len
  fits := Nat.lt_of_le_of_lt h v.capacity
  within := h

def firstSlice (xs : Array (Word bits)) (v : Valid xs) : Slice xs :=
  sliceAt xs v 1 (rowCount xs) (by
    have h := v.keysWithin
    unfold slotBase secondBase at h
    omega)

def secondSlice (xs : Array (Word bits)) (v : Valid xs) : Slice xs :=
  sliceAt xs v (secondBase (rowCount xs)) (rowCount xs) v.keysWithin

def slotSlice (xs : Array (Word bits)) (v : Valid xs) : Slice xs :=
  sliceAt xs v (slotBase (rowCount xs)) (xs.size - slotBase (rowCount xs)) (by
    have h := v.keysWithin
    omega)

@[simp] theorem firstSlice_len (xs : Array (Word bits)) (v : Valid xs) :
    (firstSlice xs v).len = rowCount xs := rfl

@[simp] theorem secondSlice_len (xs : Array (Word bits)) (v : Valid xs) :
    (secondSlice xs v).len = rowCount xs := rfl

private theorem serialize_get (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) (j : Nat) (hj : j < packedSize s) :
    (serialize s f)[j]'(by simpa only [serialize_size] using hj) =
      cell s f ⟨j, hj⟩ := by
  simp [serialize]

@[simp] theorem rowCount_serialize (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) : rowCount (serialize s f) = s.dict.size := by
  have h0 : 0 < packedSize s := by
    unfold packedSize slotBase secondBase
    omega
  have hb : 0 < (serialize s f).size := by
    simpa only [serialize_size] using h0
  simp only [rowCount, getElem?_def, hb, dite_eq_left,
    serialize_get s f 0 h0, Option.map_some] <;> simp [cell]

theorem serialize_valid (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) : Valid (serialize s f) := by
  constructor
  · rw [rowCount_serialize, serialize_size]
    unfold packedSize
    omega
  · simpa only [serialize_size] using f.capacity

@[simp] theorem slotSlice_serialize_len (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) :
    (slotSlice (serialize s f) (serialize_valid s f)).len = s.slots.size := by
  change (serialize s f).size - slotBase (rowCount (serialize s f)) =
    s.slots.size
  rw [serialize_size, rowCount_serialize]
  unfold packedSize
  omega

private theorem slice_serialize_get (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) (p : Slice (serialize s f)) (i : Nat) (hi : i < p.len)
    (j : Nat) (hj : j < packedSize s) (e : p.base.val + i = j) :
    p.get i hi = cell s f ⟨j, hj⟩ := by
  subst j
  exact serialize_get s f (p.base.val + i) hj

private theorem get_same {α : Type} (a : Array α) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (e : i = j) :
    (a[i]'hi) = (a[j]'hj) := by
  subst j
  rfl

private theorem first_serialize (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) (i : Nat) (hi : i < s.dict.size)
    (h : i < (firstSlice (serialize s f) (serialize_valid s f)).len) :
    ((firstSlice (serialize s f) (serialize_valid s f)).get i h).val =
      (s.dict[i]'hi).1 := by
  have h1 : 1 + i < secondBase s.dict.size := by
    unfold secondBase
    omega
  have hj : 1 + i < packedSize s := by
    unfold packedSize slotBase
    omega
  have h0 : 1 + i ≠ 0 := by omega
  have he : 1 + i - 1 = i := by omega
  rw [slice_serialize_get s f
    (firstSlice (serialize s f) (serialize_valid s f)) i h (1 + i) hj rfl]
  simp only [cell, dif_neg h0, if_neg h0, dif_pos h1, if_pos h1] <;>
    exact congrArg Prod.fst (get_same s.dict (by omega) hi he)

private theorem second_serialize (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) (i : Nat) (hi : i < s.dict.size)
    (h : i < (secondSlice (serialize s f) (serialize_valid s f)).len) :
    ((secondSlice (serialize s f) (serialize_valid s f)).get i h).val =
      (s.dict[i]'hi).2 := by
  have h0 : secondBase s.dict.size + i ≠ 0 := by
    unfold secondBase
    omega
  have h1 : ¬ (secondBase s.dict.size + i < secondBase s.dict.size) := by omega
  have h2 : secondBase s.dict.size + i < slotBase s.dict.size := by
    unfold slotBase
    omega
  have hj : secondBase s.dict.size + i < packedSize s := by
    unfold packedSize
    omega
  have he : secondBase s.dict.size + i - secondBase s.dict.size = i := by omega
  have e : (secondSlice (serialize s f) (serialize_valid s f)).base.val + i =
      secondBase s.dict.size + i := by
    change secondBase (rowCount (serialize s f)) + i = secondBase s.dict.size + i
    rw [rowCount_serialize]
  rw [slice_serialize_get s f
    (secondSlice (serialize s f) (serialize_valid s f)) i h
    (secondBase s.dict.size + i) hj e]
  simp only [cell, dif_neg h0, if_neg h0, dif_neg h1, if_neg h1,
    dif_pos h2, if_pos h2] <;>
    exact congrArg Prod.snd (get_same s.dict (by omega) hi he)

private theorem slot_serialize (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) (i : Nat) (hi : i < s.slots.size)
    (h : i < (slotSlice (serialize s f) (serialize_valid s f)).len) :
    ((slotSlice (serialize s f) (serialize_valid s f)).get i h).val =
      (s.slots[i]?).getD 0 := by
  have h0 : slotBase s.dict.size + i ≠ 0 := by
    unfold slotBase secondBase
    omega
  have h1 : ¬ (slotBase s.dict.size + i < secondBase s.dict.size) := by
    unfold slotBase
    omega
  have h2 : ¬ (slotBase s.dict.size + i < slotBase s.dict.size) := by omega
  have hj : slotBase s.dict.size + i < packedSize s := by
    unfold packedSize
    omega
  have he : slotBase s.dict.size + i - slotBase s.dict.size = i := by omega
  have e : (slotSlice (serialize s f) (serialize_valid s f)).base.val + i =
      slotBase s.dict.size + i := by
    change slotBase (rowCount (serialize s f)) + i = slotBase s.dict.size + i
    rw [rowCount_serialize]
  rw [slice_serialize_get s f
    (slotSlice (serialize s f) (serialize_valid s f)) i h
    (slotBase s.dict.size + i) hj e]
  simp only [cell, dif_neg h0, if_neg h0, dif_neg h1, if_neg h1,
    dif_neg h2, if_neg h2, he]

/-- A proof-only link to the source. The source arrays are not fields of
    the buffer or of its runtime views. -/
structure Represents (xs : Array (Word bits))
    (s : PaperB.RetainedProperLoss.Columns H) : Prop where
  valid : Valid xs
  rows : rowCount xs = s.dict.size
  slot_len : (slotSlice xs valid).len = s.slots.size
  first_eq : ∀ (i : Nat) (h : i < (firstSlice xs valid).len) (hi : i < s.dict.size),
    ((firstSlice xs valid).get i h).val = (s.dict[i]'hi).1
  second_eq : ∀ (i : Nat) (h : i < (secondSlice xs valid).len) (hi : i < s.dict.size),
    ((secondSlice xs valid).get i h).val = (s.dict[i]'hi).2
  slot_eq : ∀ (i : Nat) (h : i < (slotSlice xs valid).len) (hi : i < s.slots.size),
    ((slotSlice xs valid).get i h).val = (s.slots[i]?).getD 0

theorem serialize_represents (s : PaperB.RetainedProperLoss.Columns H)
    (f : Fits bits s) : Represents (serialize s f) s where
  valid := serialize_valid s f
  rows := rowCount_serialize s f
  slot_len := slotSlice_serialize_len s f
  first_eq i h hi := first_serialize s f i hi h
  second_eq i h hi := second_serialize s f i hi h
  slot_eq i h hi := slot_serialize s f i hi h

/-- Adapter for the fixed RAM worker. Both slices are views into `xs`.
    This constructs only constant-size metadata and never calls `serialize`. -/
def workerColumns (xs : Array (Word bits)) {s : PaperB.RetainedProperLoss.Columns H}
    (r : Represents xs s) : PaperB.PairLookup.ColumnReduction.Columns xs s.dict where
  first := firstSlice xs r.valid
  second := secondSlice xs r.valid
  first_len := r.rows
  second_len := r.rows
  first_word i hi := r.first_eq i (by simpa only [firstSlice_len, r.rows] using hi) hi
  second_word i hi := r.second_eq i (by simpa only [secondSlice_len, r.rows] using hi) hi

/-- One payload read when the slot index is in range. The zero fallback
    agrees with the source even when the slot column is shorter than the dict. -/
def slotAt (xs : Array (Word bits)) (v : Valid xs) (i : Nat) : Nat :=
  let p := slotSlice xs v
  if hi : i < p.len then (p.get i hi).val else 0

theorem Represents.slotAt_eq {xs : Array (Word bits)}
    {s : PaperB.RetainedProperLoss.Columns H} (r : Represents xs s) (i : Nat) :
    slotAt xs r.valid i = (s.slots[i]?).getD 0 := by
  by_cases hi : i < (slotSlice xs r.valid).len
  · have hs : i < s.slots.size := by simpa only [r.slot_len] using hi
    simpa only [slotAt, dif_pos hi] using r.slot_eq i hi hs
  · have hs : ¬ (i < s.slots.size) := by simpa only [r.slot_len] using hi
    simp only [slotAt, dif_neg hi, getElem?_def, dif_neg hs, Option.getD_none]

/-- At any in-range row selected by the worker, both key fields and the
    defaulted slot read agree with the source. -/
theorem worker_row_eq {xs : Array (Word bits)}
    {s : PaperB.RetainedProperLoss.Columns H} (r : Represents xs s)
    (i : Nat) (hi : i < s.dict.size) :
    (((workerColumns xs r).first.get i
        (by rw [(workerColumns xs r).first_len]; exact hi)).val,
      ((workerColumns xs r).second.get i
        (by rw [(workerColumns xs r).second_len]; exact hi)).val,
      slotAt xs r.valid i) =
    ((s.dict[i]'hi).1, (s.dict[i]'hi).2, (s.slots[i]?).getD 0) := by
  rw [(workerColumns xs r).first_word i hi, (workerColumns xs r).second_word i hi,
    r.slotAt_eq i]

/-- Consume the worker's hit without rebuilding a key array. `some 0`
    is a raw slot result, not a checked pair hit. -/
def readHitSlot (xs : Array (Word bits)) (v : Valid xs) (hit : Option Nat) :
    Option Nat :=
  hit.map (slotAt xs v)

theorem readHitSlot_eq {xs : Array (Word bits)}
    {s : PaperB.RetainedProperLoss.Columns H} (r : Represents xs s) (hit : Option Nat) :
    readHitSlot xs r.valid hit = hit.map (fun i => (s.slots[i]?).getD 0) := by
  cases hit with
  | none => rfl
  | some i => exact congrArg some (r.slotAt_eq i)

/-- Compose slot decoding with the worker's row-correctness result.
    This does not claim agreement with `Columns.checked`. -/
theorem worker_hit_slot_eq {xs : Array (Word bits)}
    {s : PaperB.RetainedProperLoss.Columns H} (r : Represents xs s)
    (key : PaperB.PairLookup.Key) (hit : Option Nat)
    (hit_eq : hit = (PaperB.PairLookup.lookup s.dict key).1) :
    readHitSlot xs r.valid hit =
      ((PaperB.PairLookup.lookup s.dict key).1).map
        (fun i => (s.slots[i]?).getD 0) := by
  rw [← hit_eq]
  exact readHitSlot_eq r hit

end PaperB.ForestSlimIndex.FlatPairDictionary
