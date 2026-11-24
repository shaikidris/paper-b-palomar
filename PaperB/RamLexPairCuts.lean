module

public import PaperB.PairLookup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PairLookup.ColumnReduction

abbrev ScalarWord (bits : Nat) := Fin (2 ^ bits)

/-- A read-only view into the shared input. The end address must fit in a word,
even for an empty slice. -/
structure Slice {bits : Nat} (input : Array (ScalarWord bits)) where
  base : ScalarWord bits
  len : Nat
  fits : base.val + len < 2 ^ bits
  within : base.val + len ≤ input.size

variable {bits : Nat} {input : Array (ScalarWord bits)}

def Slice.get (p : Slice input) (i : Nat) (h : i < p.len) : ScalarWord bits :=
  input[p.base.val + i]'(by have hp := p.within; omega)

def Slice.sub (p : Slice input) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ p.len) : Slice input where
  base := ⟨p.base.val + lo, by have hp := p.fits; omega⟩
  len := hi - lo
  fits := by
    change p.base.val + lo + (hi - lo) < 2 ^ bits
    have hp := p.fits
    omega
  within := by
    change p.base.val + lo + (hi - lo) ≤ input.size
    have hp := p.within
    omega

private theorem getElem_same {α : Type} (a : Array α) {i j : Nat}
    (hi : i < a.size) (hj : j < a.size) (e : i = j) :
    (a[i]'hi) = (a[j]'hj) := by
  subst j
  rfl

theorem Slice.sub_get (p : Slice input) (lo hi : Nat)
    (hlo : lo ≤ hi) (hhi : hi ≤ p.len)
    (i : Nat) (h : i < (p.sub lo hi hlo hhi).len) :
    (p.sub lo hi hlo hhi).get i h =
      p.get (lo + i) (by change i < hi - lo at h; omega) := by
  unfold Slice.get
  apply getElem_same
  exact Nat.add_assoc _ _ _

def Slice.Sorted (p : Slice input) : Prop :=
  ∀ (i j : Nat) (hi : i < p.len) (hj : j < p.len),
    i < j → (p.get i hi).val ≤ (p.get j hj).val

def Slice.Increasing (p : Slice input) : Prop :=
  ∀ (i j : Nat) (hi : i < p.len) (hj : j < p.len),
    i < j → (p.get i hi).val < (p.get j hj).val

/-- Value-level contract of a scalar `upper_bound` call. -/
def Answer (p : Slice input) (key : ScalarWord bits) (k : Nat) : Prop :=
  k ≤ p.len ∧
  (∀ (i : Nat) (h : i < p.len), i < k → (p.get i h).val ≤ key.val) ∧
  (∀ (i : Nat) (h : i < p.len), k ≤ i → key.val < (p.get i h).val)

private theorem le_key_iff_lt_cut {p : Slice input} {key : ScalarWord bits}
    {k : Nat} (ans : Answer p key k) (i : Nat) (h : i < p.len) :
    (p.get i h).val ≤ key.val ↔ i < k := by
  refine ⟨?_, ans.2.1 i h⟩
  intro hv
  by_cases hk : i < k
  · exact hk
  · have hg := ans.2.2 i h (by omega)
    omega

/-- Both columns use the same row index; neither column is copied. -/
structure Columns (input : Array (ScalarWord bits)) (a : Array Key) where
  first : Slice input
  second : Slice input
  first_len : first.len = a.size
  second_len : second.len = a.size
  first_word : ∀ (i : Nat) (h : i < a.size),
    (first.get i (by rw [first_len]; exact h)).val = (a[i]'h).1
  second_word : ∀ (i : Nat) (h : i < a.size),
    (second.get i (by rw [second_len]; exact h)).val = (a[i]'h).2

private theorem first_sorted {a : Array Key} (c : Columns input a)
    (hs : StrictSorted a) : c.first.Sorted := by
  intro i j hi hj hij
  have ia : i < a.size := by simpa only [c.first_len] using hi
  have ja : j < a.size := by simpa only [c.first_len] using hj
  rw [c.first_word i ia, c.first_word j ja]
  have hp := hs i j ia ja hij
  unfold lexLess at hp
  rcases hp with h | ⟨h, _⟩
  · exact Nat.le_of_lt h
  · omega

def predecessor (x : ScalarWord bits) : ScalarWord bits :=
  ⟨x.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt⟩

def LowerCut (p : Slice input) (x : ScalarWord bits) (lo : Nat) : Prop :=
  if x.val = 0 then lo = 0 else Answer p (predecessor x) lo

private theorem lower_spec {p : Slice input} {x : ScalarWord bits} {lo : Nat}
    (hl : LowerCut p x lo) :
    lo ≤ p.len ∧
      ∀ (i : Nat) (h : i < p.len), i < lo ↔ (p.get i h).val < x.val := by
  by_cases hz : x.val = 0
  · have hlo : lo = 0 := by simpa only [LowerCut, if_pos hz] using hl
    refine ⟨by omega, ?_⟩
    intro i h
    constructor <;> intro hh <;> omega
  · have ans : Answer p (predecessor x) lo := by
      simpa only [LowerCut, if_neg hz] using hl
    refine ⟨ans.1, ?_⟩
    intro i h
    have hc := le_key_iff_lt_cut ans i h
    change ((p.get i h).val ≤ x.val - 1 ↔ i < lo) at hc
    constructor
    · intro hi
      have hv := hc.mpr hi
      omega
    · intro hv
      exact hc.mp (by omega)

def IsBand (p : Slice input) (x : ScalarWord bits) (lo hi : Nat) : Prop :=
  ∀ (i : Nat) (h : i < p.len),
    (lo ≤ i ∧ i < hi) ↔ (p.get i h).val = x.val

theorem band_spec {p : Slice input} {x : ScalarWord bits} {lo hi : Nat}
    (hl : LowerCut p x lo) (hh : Answer p x hi) :
    lo ≤ hi ∧ hi ≤ p.len ∧ IsBand p x lo hi := by
  obtain ⟨hlen, hs⟩ := lower_spec hl
  have hlo : lo ≤ hi := by
    by_cases h : lo ≤ hi
    · exact h
    · have hb : hi < p.len := by omega
      have hlt := (hs hi hb).mp (by omega)
      have hgt := hh.2.2 hi hb (Nat.le_refl hi)
      omega
  refine ⟨hlo, hh.1, ?_⟩
  intro i h
  have hc := le_key_iff_lt_cut hh i h
  constructor
  · rintro ⟨hil, hih⟩
    have hv := hc.mpr hih
    by_cases hlt : (p.get i h).val < x.val
    · have := (hs i h).mpr hlt
      omega
    · omega
  · intro he
    refine ⟨?_, hc.mp (by omega)⟩
    by_cases hil : i < lo
    · have := (hs i h).mp hil
      omega
    · omega

/-- Only the second-coordinate sub-slice is increasing. -/
private theorem band_increasing {a : Array Key} (c : Columns input a)
    (hs : StrictSorted a) {x : ScalarWord bits} {lo hi : Nat}
    (hlo : lo ≤ hi) (hhi : hi ≤ c.second.len)
    (hb : IsBand c.first x lo hi) :
    (c.second.sub lo hi hlo hhi).Increasing := by
  intro i j ii jj hij
  have iiBound : i < hi - lo := ii
  have jjBound : j < hi - lo := jj
  have hsize := c.second_len
  have ia : lo + i < a.size := by omega
  have ja : lo + j < a.size := by omega
  have fi : lo + i < c.first.len := by simpa only [c.first_len] using ia
  have fj : lo + j < c.first.len := by simpa only [c.first_len] using ja
  have ei := (hb (lo + i) fi).mp ⟨by omega, by omega⟩
  have ej := (hb (lo + j) fj).mp ⟨by omega, by omega⟩
  rw [c.first_word (lo + i) ia] at ei
  rw [c.first_word (lo + j) ja] at ej
  have hp := hs (lo + i) (lo + j) ia ja (by omega)
  unfold lexLess at hp
  simp only [Slice.sub_get]
  rw [c.second_word (lo + i) ia, c.second_word (lo + j) ja]
  rcases hp with h | ⟨_, h⟩
  · omega
  · exact h

/-- The predecessor of the third cut is only a candidate. Check both words. -/
def finish (first second : Slice input) (x y : ScalarWord bits)
    (lo k : Nat) : Option Nat :=
  if 0 < k then
    let i := lo + (k - 1)
    if h : i < first.len ∧ i < second.len then
      if (first.get i h.1).val = x.val ∧ (second.get i h.2).val = y.val then
        some i
      else none
    else none
  else none

theorem finish_empty_band (first second : Slice input)
    (x y : ScalarWord bits) (lo k : Nat) (h : lo ≤ second.len)
    (ans : Answer (second.sub lo lo (Nat.le_refl lo) h) y k) :
    finish first second x y lo k = none := by
  have hk : k ≤ lo - lo := ans.1
  have hz : ¬ 0 < k := by omega
  simp only [finish, if_neg hz]

private theorem finish_at {a : Array Key} (c : Columns input a)
    (x y : ScalarWord bits) (lo k : Nat) (hk : 0 < k)
    (hj : lo + (k - 1) < a.size) :
    finish c.first c.second x y lo k =
      (if (a[lo + (k - 1)]'hj) = (x.val, y.val) then some (lo + (k - 1))
       else none) := by
  have hb : lo + (k - 1) < c.first.len ∧ lo + (k - 1) < c.second.len := by
    rw [c.first_len, c.second_len]
    exact ⟨hj, hj⟩
  have heq :
      ((a[lo + (k - 1)]'hj).1 = x.val ∧ (a[lo + (k - 1)]'hj).2 = y.val) ↔
        (a[lo + (k - 1)]'hj) = (x.val, y.val) :=
    ⟨fun h => Prod.ext h.1 h.2,
      fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩
  unfold finish
  rw [if_pos hk, dif_pos hb, c.first_word _ hj, c.second_word _ hj]
  by_cases he : (a[lo + (k - 1)]'hj) = (x.val, y.val)
  · rw [if_pos (heq.mpr he), if_pos he]
  · rw [if_neg (fun h => he (heq.mp h)), if_neg he]

/-- Any cuts satisfying the three scalar contracts give exactly `lookup`. -/
theorem cuts_correct {a : Array Key} (c : Columns input a) (hs : StrictSorted a)
    (x y : ScalarWord bits) {lo hi k : Nat}
    (hl : LowerCut c.first x lo) (hh : Answer c.first x hi)
    (hlo : lo ≤ hi) (hhi : hi ≤ c.second.len)
    (hk : Answer (c.second.sub lo hi hlo hhi) y k) :
    finish c.first c.second x y lo k =
      (PairLookup.lookup a (x.val, y.val)).1 := by
  have hb := (band_spec hl hh).2.2
  let p := c.second.sub lo hi hlo hhi
  change Answer p y k at hk
  have inc : p.Increasing := band_increasing c hs hlo hhi hb
  have hklen : k ≤ hi - lo := hk.1
  have hia : hi ≤ a.size := by simpa only [c.second_len] using hhi
  have hit : ∀ (i : Nat) (ia : i < a.size),
      (a[i]'ia) = (x.val, y.val) → 0 < k ∧ i = lo + (k - 1) := by
    intro i ia he
    have fi : i < c.first.len := by simpa only [c.first_len] using ia
    have fx : (c.first.get i fi).val = x.val :=
      (c.first_word i ia).trans (congrArg Prod.fst he)
    obtain ⟨hil, hih⟩ := (hb i fi).mpr fx
    let t := i - lo
    have ht : t < p.len := by
      change t < hi - lo
      dsimp [t]
      omega
    have hti : lo + t = i := by dsimp [t]; omega
    have ta : lo + t < a.size := by omega
    have ty : (p.get t ht).val = y.val := by
      change ((c.second.sub lo hi hlo hhi).get t ht).val = y.val
      rw [Slice.sub_get, c.second_word (lo + t) ta]
      exact (congrArg Prod.snd (getElem_same a ta ia hti)).trans
        (congrArg Prod.snd he)
    have htk : t < k := (le_key_iff_lt_cut hk t ht).mp (by omega)
    have hnext : ¬ t + 1 < k := by
      intro hn
      have ht' : t + 1 < p.len := by
        change t + 1 < hi - lo
        omega
      have hg := inc t (t + 1) ht ht' (by omega)
      have hv := hk.2.1 (t + 1) ht' hn
      omega
    exact ⟨by omega, by omega⟩
  have missing :
      (∀ (i : Nat) (ia : i < a.size), (a[i]'ia) ≠ (x.val, y.val)) →
        (PairLookup.lookup a (x.val, y.val)).1 = none := by
    intro hn
    cases e : (PairLookup.lookup a (x.val, y.val)).1 with
    | none => rfl
    | some i =>
      obtain ⟨ia, he⟩ := (PairLookup.lookup_eq_some_iff a (x.val, y.val) hs i).mp e
      exact False.elim (hn i ia he)
  by_cases hpos : 0 < k
  · have hj : lo + (k - 1) < a.size := by omega
    rw [finish_at c x y lo k hpos hj]
    by_cases he : (a[lo + (k - 1)]'hj) = (x.val, y.val)
    · rw [if_pos he]
      exact ((PairLookup.lookup_eq_some_iff a (x.val, y.val) hs _).mpr
        ⟨hj, he⟩).symm
    · rw [if_neg he]
      symm
      apply missing
      intro i ia eq
      have hidx := (hit i ia eq).2
      exact he ((getElem_same a hj ia hidx.symm).trans eq)
  · simp only [finish, if_neg hpos]
    symm
    apply missing
    intro i ia he
    exact hpos (hit i ia he).1


end PaperB.PairLookup.ColumnReduction
