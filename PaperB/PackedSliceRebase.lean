module

public import PaperB.RamLexPairCuts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PairLookup.ColumnReduction

variable {bits : Nat}

/-- Bounds for the relocated window, independent of any source array. The
strict bound is the endpoint convention used by `Slice.fits`. -/
structure RelocationFits (dst : Array (ScalarWord bits))
    (oldBase oldLen shift : ScalarWord bits) : Prop where
  fits : oldBase.val + shift.val + oldLen.val < 2 ^ bits
  within : oldBase.val + shift.val + oldLen.val ≤ dst.size

/-- On a word RAM, with the scalar arguments already available, this uses
exactly one word addition for the new base and zero payload loads or stores.
The length is reused. This count excludes metadata moves and is not a claim
about the compiled implementation of Lean's `Nat.add`. -/
@[inline] def relocateSlice {dst : Array (ScalarWord bits)}
    (oldBase oldLen shift : ScalarWord bits)
    (h : RelocationFits dst oldBase oldLen shift) : Slice dst where
  base := ⟨oldBase.val + shift.val, by have hf := h.fits; omega⟩
  len := oldLen.val
  fits := h.fits
  within := h.within

/-- A subsequent `get` uses one address addition and one load from `dst`
in the same RAM model. It neither recomputes the relocation nor reads a
source buffer. -/
theorem relocateSlice_get_address {dst : Array (ScalarWord bits)}
    (oldBase oldLen shift : ScalarWord bits)
    (h : RelocationFits dst oldBase oldLen shift)
    (i : Nat) (hi : i < oldLen.val) :
    (relocateSlice oldBase oldLen shift h).get i hi =
      dst[oldBase.val + shift.val + i]'(by have hw := h.within; omega) :=
  rfl

/-- Proof-only evidence that `xs` occupies a contiguous window of an
already-sealed input. Constructing the sealed input is not part of rebasing. -/
structure SlicePlacement (xs dst : Array (ScalarWord bits))
    (shift : Nat) : Prop where
  capacity : shift + xs.size < 2 ^ bits
  within : shift + xs.size ≤ dst.size
  word_eq : ∀ (i : Nat) (hi : i < xs.size),
    xs[i]'hi = dst[shift + i]'(by have hw := within; omega)

private def sliceLengthWord {xs : Array (ScalarWord bits)}
    (p : Slice xs) : ScalarWord bits :=
  ⟨p.len, by have hf := p.fits; omega⟩

/-- Rebase an existing slice. The source array is used only in types and
proofs; the constructor takes its data from the old slice's metadata. -/
@[inline] def rebaseSlice {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift) :
    Slice dst :=
  relocateSlice (dst := dst) p.base (sliceLengthWord p)
    ⟨shift, by have hc := h.capacity; omega⟩
    (by
      have hc := h.capacity
      have hw := h.within
      have hp := p.within
      constructor
      · change p.base.val + shift + p.len < 2 ^ bits
        omega
      · change p.base.val + shift + p.len ≤ dst.size
        omega)

@[simp] theorem rebaseSlice_base {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift) :
    (rebaseSlice p h).base.val = p.base.val + shift :=
  rfl

@[simp] theorem rebaseSlice_len {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift) :
    (rebaseSlice p h).len = p.len :=
  rfl

private theorem arrayGetCongr {α : Type} (a : Array α) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (e : i = j) :
    a[i]'hi = a[j]'hj := by
  subst j
  rfl

theorem rebaseSlice_get {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift)
    (i : Nat) (hi : i < p.len) :
    (rebaseSlice p h).get i hi = p.get i hi := by
  have hj : p.base.val + i < xs.size := by
    have hp := p.within
    omega
  unfold Slice.get
  calc
    dst[(rebaseSlice p h).base.val + i]'(by
        have hw := (rebaseSlice p h).within
        have hi' : i < (rebaseSlice p h).len := hi
        omega) =
        dst[shift + (p.base.val + i)]'(by have hw := h.within; omega) := by
      apply arrayGetCongr
      rw [rebaseSlice_base]
      omega
    _ = xs[p.base.val + i]'hj := (h.word_eq (p.base.val + i) hj).symm

private theorem rebaseSlice_order_iff {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift)
    (R : Nat → Nat → Prop) :
    (∀ (i j : Nat) (hi : i < (rebaseSlice p h).len)
        (hj : j < (rebaseSlice p h).len),
      i < j → R ((rebaseSlice p h).get i hi).val
                ((rebaseSlice p h).get j hj).val) ↔
    (∀ (i j : Nat) (hi : i < p.len) (hj : j < p.len),
      i < j → R (p.get i hi).val (p.get j hj).val) := by
  constructor
  · intro hs i j hi hj hij
    simpa only [rebaseSlice_get p h i hi, rebaseSlice_get p h j hj] using
      hs i j hi hj hij
  · intro hs i j hi hj hij
    have hi' : i < p.len := hi
    have hj' : j < p.len := hj
    rw [rebaseSlice_get p h i hi', rebaseSlice_get p h j hj']
    exact hs i j hi' hj' hij

theorem rebaseSlice_sorted_iff {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift) :
    (rebaseSlice p h).Sorted ↔ p.Sorted :=
  rebaseSlice_order_iff p h (fun x y => x ≤ y)

theorem rebaseSlice_increasing_iff {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift) :
    (rebaseSlice p h).Increasing ↔ p.Increasing :=
  rebaseSlice_order_iff p h (fun x y => x < y)

/-- The second-column sub-slice searched within a first-column band also
agrees word for word. No global sort assumption on the second column is needed. -/
theorem rebaseSlice_sub_get {xs dst : Array (ScalarWord bits)}
    (p : Slice xs) {shift : Nat} (h : SlicePlacement xs dst shift)
    (lo hi : Nat) (hlo : lo ≤ hi) (hhi : hi ≤ p.len)
    (i : Nat) (ii : i < hi - lo) :
    ((rebaseSlice p h).sub lo hi hlo hhi).get i ii =
      (p.sub lo hi hlo hhi).get i ii := by
  have hj : lo + i < p.len := by omega
  calc
    ((rebaseSlice p h).sub lo hi hlo hhi).get i ii =
        (rebaseSlice p h).get (lo + i) hj :=
      Slice.sub_get (rebaseSlice p h) lo hi hlo hhi i ii
    _ = p.get (lo + i) hj := rebaseSlice_get p h (lo + i) hj
    _ = (p.sub lo hi hlo hhi).get i ii :=
      (Slice.sub_get p lo hi hlo hhi i ii).symm

/-- The slices may come from different buffers. Each must agree with its own
coordinate of the same key array at the same row indices. Given the old
metadata, this performs two base additions and no payload reads or copies.
The key array is a specification index; the worker reads `dst`. -/
def rebaseColumns {xs ys dst : Array (ScalarWord bits)} {a : Array Key}
    (p : Slice xs) (q : Slice ys) {bp bq : Nat}
    (hp : SlicePlacement xs dst bp) (hq : SlicePlacement ys dst bq)
    (pn : p.len = a.size) (qn : q.len = a.size)
    (pw : ∀ (i : Nat) (hi : i < a.size),
      (p.get i (by rw [pn]; exact hi)).val = (a[i]'hi).1)
    (qw : ∀ (i : Nat) (hi : i < a.size),
      (q.get i (by rw [qn]; exact hi)).val = (a[i]'hi).2) :
    Columns dst a where
  first := rebaseSlice p hp
  second := rebaseSlice q hq
  first_len := pn
  second_len := qn
  first_word i hi := by
    have hip : i < p.len := by simpa only [pn] using hi
    exact (congrArg (fun w : ScalarWord bits => w.val)
      (rebaseSlice_get p hp i hip)).trans (pw i hi)
  second_word i hi := by
    have hiq : i < q.len := by simpa only [qn] using hi
    exact (congrArg (fun w : ScalarWord bits => w.val)
      (rebaseSlice_get q hq i hiq)).trans (qw i hi)

/-- Specialization for an existing worker adapter whose two slices share
one local buffer. The pair worker keeps its original key-array contract. -/
def rebaseWorkerColumns {xs dst : Array (ScalarWord bits)} {a : Array Key}
    (c : Columns xs a) {shift : Nat} (h : SlicePlacement xs dst shift) :
    Columns dst a :=
  rebaseColumns c.first c.second h h c.first_len c.second_len
    c.first_word c.second_word

end PaperB.PairLookup.ColumnReduction
