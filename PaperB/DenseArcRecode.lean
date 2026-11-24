module

public import PaperB.DenseQuotientRows

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.DenseArcRecode

open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open DenseQuotientRows

/- Translate the emitter’s two contiguous code ranges to dense local slots. -/

structure Wire (N : Nat) where
  pack : Key N → Fin (2 * N)
  unpack : Fin (2 * N) → Key N
  unpack_pack : ∀ k, unpack (pack k) = k
  pack_unpack : ∀ b, pack (unpack b) = b

variable {N : Nat}

private def packHalves : Key N → Fin (2 * N)
  | .inl x => ⟨x.val, by have hx := x.isLt; omega⟩
  | .inr x => ⟨N + x.val, by have hx := x.isLt; omega⟩

private def unpackHalves (b : Fin (2 * N)) : Key N :=
  if h : b.val < N then
    .inl ⟨b.val, h⟩
  else
    .inr ⟨b.val - N, by have hb := b.isLt; omega⟩

def halves (N : Nat) : Wire N where
  pack := packHalves
  unpack := unpackHalves
  unpack_pack k := by
    cases k with
    | inl x =>
        simp [unpackHalves, packHalves, x.isLt]
    | inr x =>
        have hn : ¬ N + x.val < N := by omega
        have hd : N + x.val - N = x.val := by omega
        simp [unpackHalves, packHalves, hn, hd]
  pack_unpack b := by
    by_cases h : b.val < N
    · simp only [unpackHalves, dif_pos h, packHalves] <;> exact Fin.ext rfl
    · apply Fin.ext
      simp only [unpackHalves, dif_neg h, packHalves]
      omega

variable {g : ChildLists N}

/-- The membership certificate is erased. `Layout.encode` reads at most one
inverse-position cell and does not inspect the child bucket. -/
def slot (w : Wire N) (rows : DenseQuotientRows.Layout g) (u : Fin N)
    (b : Fin (2 * N)) (h : Occurs g u (w.unpack b)) :
    Fin (rows.length u) :=
  rows.encode u ⟨w.unpack b, h⟩

def codeAt (w : Wire N) (rows : DenseQuotientRows.Layout g) (u : Fin N)
    (i : Fin (rows.length u)) : Fin (2 * N) :=
  w.pack (rows.key u i)

theorem codeAt_occurs (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u : Fin N) (i : Fin (rows.length u)) :
    Occurs g u (w.unpack (codeAt w rows u i)) := by
  rw [codeAt, w.unpack_pack]
  exact (rows.decode u i).property

@[simp] theorem codeAt_slot (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u : Fin N) (b : Fin (2 * N)) (h : Occurs g u (w.unpack b)) :
    codeAt w rows u (slot w rows u b h) = b := by
  have hk : rows.key u (slot w rows u b h) = w.unpack b :=
    congrArg (fun k : Occurrence g u => k.val)
      (rows.decode_encode u ⟨w.unpack b, h⟩)
  rw [codeAt, hk, w.pack_unpack]

@[simp] theorem slot_codeAt (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u : Fin N) (i : Fin (rows.length u)) :
    slot w rows u (codeAt w rows u i) (codeAt_occurs w rows u i) = i := by
  have hk :
      (⟨w.unpack (codeAt w rows u i), codeAt_occurs w rows u i⟩ :
        Occurrence g u) = rows.decode u i := by
    apply Subtype.ext
    exact w.unpack_pack (rows.key u i)
  unfold slot
  rw [hk, rows.encode_decode]

/-- The unchecked candidate is needed only when no occurrence certificate
is available. It uses the existing scattered inverse-position column. -/
private def candidate (rows : DenseQuotientRows.Layout g) (k : Key N) : Nat :=
  k.elim (fun _ => 0) (fun c => rows.localPos.read c)

private theorem encode_val (rows : DenseQuotientRows.Layout g) (u : Fin N)
    (k : Occurrence g u) :
    (rows.encode u k).val = candidate rows k.val := by
  rcases k with ⟨k, hk⟩
  cases k <;> rfl

theorem slot_root_val (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u : Fin N) (h : Occurs g u (w.unpack (w.pack (.inl u)))) :
    (slot w rows u (w.pack (.inl u)) h).val = 0 := by
  simp only [slot, encode_val, w.unpack_pack] <;> rfl

theorem slot_child_val (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u c : Fin N) (h : Occurs g u (w.unpack (w.pack (.inr c)))) :
    (slot w rows u (w.pack (.inr c)) h).val = rows.localPos.read c := by
  simp only [slot, encode_val, w.unpack_pack] <;> rfl

/-- For a raw code, check the one candidate against the forward cell in
this row. A code from another row cannot pass just because its candidate
is in bounds. -/
def checkedSlot (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u : Fin N) (b : Fin (2 * N)) : Option (Fin (rows.length u)) :=
  let j := candidate rows (w.unpack b)
  if hj : j < rows.length u then
    let i : Fin (rows.length u) := ⟨j, hj⟩
    if codeAt w rows u i = b then some i else none
  else
    none

theorem checkedSlot_valid (w : Wire N) (rows : DenseQuotientRows.Layout g)
    (u : Fin N) (b : Fin (2 * N)) (h : Occurs g u (w.unpack b)) :
    checkedSlot w rows u b = some (slot w rows u b h) := by
  have hj : candidate rows (w.unpack b) = (slot w rows u b h).val :=
    (encode_val rows u ⟨w.unpack b, h⟩).symm
  unfold checkedSlot
  rw [hj, dif_pos (slot w rows u b h).isLt]
  change (if codeAt w rows u (slot w rows u b h) = b then
    some (slot w rows u b h) else none) = some (slot w rows u b h)
  rw [if_pos (codeAt_slot w rows u b h)]

@[simp] theorem checkedSlot_codeAt (w : Wire N)
    (rows : DenseQuotientRows.Layout g) (u : Fin N) (i : Fin (rows.length u)) :
    checkedSlot w rows u (codeAt w rows u i) = some i := by
  rw [checkedSlot_valid w rows u _ (codeAt_occurs w rows u i), slot_codeAt]

/-- Exact round trip, including soundness on arbitrary raw codes. -/
theorem checkedSlot_eq_some_iff (w : Wire N)
    (rows : DenseQuotientRows.Layout g) (u : Fin N) (b : Fin (2 * N))
    (i : Fin (rows.length u)) :
    checkedSlot w rows u b = some i ↔ codeAt w rows u i = b := by
  constructor
  · intro h
    by_cases hj : candidate rows (w.unpack b) < rows.length u
    · let j : Fin (rows.length u) := ⟨candidate rows (w.unpack b), hj⟩
      have hh : (if codeAt w rows u j = b then some j else none) = some i := by
        simpa only [checkedSlot, dif_pos hj] using h
      split at hh
      · rename_i he
        have hji : j = i := Option.some.inj hh
        simpa only [hji] using he
      · cases hh
    · have hn : (none : Option (Fin (rows.length u))) = some i := by
        simpa only [checkedSlot, dif_neg hj] using h
      cases hn
  · intro h
    rw [← h, checkedSlot_codeAt]

end PaperB.DenseArcRecode
