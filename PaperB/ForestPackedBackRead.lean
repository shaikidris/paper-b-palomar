module

public import PaperB.ForestBackWords

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient

variable {H : LabelledQuotient} {bits : Nat}

def BackWords.read (w : BackWords bits) (i : Nat) : Option (Nat × Nat) :=
  (w.tagAndFirst[i]?).bind fun a => (w.second[i]?).map fun b => (a.val, b.val)

theorem packBackWords_read_option (s : Columns H) (h : H.vertexCount < 2 ^ bits)
    (j : Nat) :
    (packBackWords s h).read j = (s.back[j]?).map encodeBackPair := by
  have hs := packBackWords_size s h
  by_cases hj : j < s.back.size
  · have h₁ : j < (packBackWords s h).tagAndFirst.size := hs.1.symm ▸ hj
    have h₂ : j < (packBackWords s h).second.size := hs.2.symm ▸ hj
    unfold BackWords.read
    rw [getElem?_pos (packBackWords s h).tagAndFirst j h₁,
      getElem?_pos (packBackWords s h).second j h₂, getElem?_pos s.back j hj]
    exact congrArg some (packBackWords_read s h ⟨j, hj⟩)
  · have h₁ : ¬ j < (packBackWords s h).tagAndFirst.size := hs.1.symm ▸ hj
    unfold BackWords.read
    rw [getElem?_neg (packBackWords s h).tagAndFirst j h₁, getElem?_neg s.back j hj]
    rfl

theorem packBackWords_matches (s : Columns H) (h : H.vertexCount < 2 ^ bits)
    (j : Nat) (q : CutPair H) :
    (packBackWords s h).read j = some (encodeBackPair (some q)) ↔
      s.back[j]? = some (some q) := by
  rw [packBackWords_read_option]
  cases hj : s.back[j]? with
  | none => simp
  | some found =>
    simp only [Option.map_some, Option.some.injEq, encodeBackPair_eq_iff]

end PaperB.RetainedProperLoss
