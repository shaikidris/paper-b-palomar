module

public import PaperB.ForestBackPairCodec
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PairColumns

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Write the first output directly into a fresh array. The second pass
can then consume the original backing array. -/
def left (a : Array α) (f : α → β × γ) : Array β :=
  Array.ofFn fun i : Fin a.size => (f (a[i.val]'i.isLt)).1

def right (a : Array α) (f : α → β × γ) : Array γ :=
  a.map (fun x => (f x).2)

theorem size_left (a : Array α) (f : α → β × γ) :
    (left a f).size = a.size := by
  simp only [left, Array.size_ofFn]

theorem size_right (a : Array α) (f : α → β × γ) :
    (right a f).size = a.size := by
  simp only [right, Array.size_map]

theorem getElem_left (a : Array α) (f : α → β × γ) (i : Fin a.size) :
    (left a f)[i.val]'(by simpa only [size_left] using i.isLt) =
      (f (a[i.val]'(i.isLt))).1 := by
  simp only [left, Array.getElem_ofFn]

theorem getElem_right (a : Array α) (f : α → β × γ) (i : Fin a.size) :
    (right a f)[i.val]'(by simpa only [size_right] using i.isLt) =
      (f (a[i.val]'(i.isLt))).2 := by
  simp only [right, Array.getElem_map]

end PairColumns

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient

variable {H : LabelledQuotient} {bits : Nat}

private def backWordPair (h : H.vertexCount < 2 ^ bits) (q : Option (CutPair H)) :
    Fin (2 ^ bits) × Fin (2 ^ bits) :=
  let p := encodeBackPair q
  let fit := encodeBackPair_fits h q
  (⟨p.1, fit.1⟩, ⟨p.2, fit.2⟩)

structure BackWords (bits : Nat) where
  tagAndFirst : Array (Fin (2 ^ bits))
  second : Array (Fin (2 ^ bits))

/-- Store the reverse-key column as two bounded-word arrays. -/
def packBackWords (s : Columns H) (h : H.vertexCount < 2 ^ bits) : BackWords bits :=
  ⟨PairColumns.left s.back (backWordPair h), PairColumns.right s.back (backWordPair h)⟩

theorem packBackWords_size (s : Columns H) (h : H.vertexCount < 2 ^ bits) :
    (packBackWords s h).tagAndFirst.size = s.back.size ∧
      (packBackWords s h).second.size = s.back.size :=
  ⟨PairColumns.size_left s.back _, PairColumns.size_right s.back _⟩

theorem packBackWords_read (s : Columns H) (h : H.vertexCount < 2 ^ bits)
    (i : Fin s.back.size) :
    let w := packBackWords s h
    let hb := packBackWords_size s h
    ((w.tagAndFirst[i.val]'(by rw [hb.1]; exact i.isLt)).val,
      (w.second[i.val]'(by rw [hb.2]; exact i.isLt)).val) =
        encodeBackPair (s.back[i.val]'i.isLt) := by
  dsimp only
  exact Prod.ext
    (congrArg Fin.val (PairColumns.getElem_left s.back (backWordPair h) i))
    (congrArg Fin.val (PairColumns.getElem_right s.back (backWordPair h) i))

/-- The two stored words preserve the actual back-key equality test. -/
theorem packBackWords_check (s : Columns H) (h : H.vertexCount < 2 ^ bits)
    (i : Fin s.back.size) (q : CutPair H) :
    let w := packBackWords s h
    let hb := packBackWords_size s h
    ((w.tagAndFirst[i.val]'(by rw [hb.1]; exact i.isLt)).val,
      (w.second[i.val]'(by rw [hb.2]; exact i.isLt)).val) =
        encodeBackPair (some q) ↔ s.back[i.val]'i.isLt = some q := by
  dsimp only
  rw [packBackWords_read]
  exact encodeBackPair_eq_iff _ _

end PaperB.RetainedProperLoss
