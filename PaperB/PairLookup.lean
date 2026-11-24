module

public import PaperB.PrefixProbe

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PairLookup

abbrev Key := Nat × Nat

def lexLess (a b : Key) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

instance (a b : Key) : Decidable (lexLess a b) := by
  unfold lexLess
  infer_instance

theorem lexLess_trans {a b c : Key}
    (hab : lexLess a b) (hbc : lexLess b c) : lexLess a c := by
  unfold lexLess at hab hbc ⊢
  rcases hab with h₁ | ⟨h₁, h₂⟩
  · rcases hbc with h₃ | ⟨h₃, h₄⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
  · rcases hbc with h₃ | ⟨h₃, h₄⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩

theorem lexLess_irrefl (a : Key) : ¬ lexLess a a := by
  unfold lexLess
  intro h
  rcases h with h | ⟨_, h⟩ <;> omega

def StrictSorted (a : Array Key) : Prop :=
  ∀ (i j : Nat) (hi : i < a.size) (hj : j < a.size),
    i < j → lexLess (a[i]'hi) (a[j]'hj)

/-- Slot zero is the true sentinel. Slot `i + 1` tests array index `i`
when it exists, so `a.size + 1` is the false sentinel. -/
def lessPrefix (a : Array Key) (q : Key) : Nat → Bool
  | 0 => true
  | i + 1 =>
    if hi : i < a.size then decide (lexLess (a[i]'hi) q) else false

theorem prefix_upper (a : Array Key) (q : Key) :
    lessPrefix a q (a.size + 1) = false := by
  simp [lessPrefix]

theorem prefix_real_true (a : Array Key) (q : Key)
    (i : Nat) (hi : i < a.size) :
    lessPrefix a q (i + 1) = true ↔ lexLess (a[i]'hi) q := by
  simp [lessPrefix, hi]

private theorem prefix_mono (a : Array Key) (q : Key) (hs : StrictSorted a) :
    ∀ x y : Nat, 0 ≤ x → x ≤ y → y ≤ a.size + 1 →
      lessPrefix a q y = true → lessPrefix a q x = true := by
  intro x y _hx hxy _hy ht
  cases x with
  | zero => rfl
  | succ i =>
    cases y with
    | zero => omega
    | succ j =>
      by_cases hj : j < a.size
      · have hi : i < a.size := by omega
        have hq : lexLess (a[j]'hj) q :=
          (prefix_real_true a q j hj).mp ht
        apply (prefix_real_true a q i hi).mpr
        by_cases hij : i = j
        · subst j
          exact hq
        · exact lexLess_trans (hs i j hi hj (by omega)) hq
      · simp [lessPrefix, hj] at ht

/-- Returns the zero-based lower-bound cut and the search probe count.
A cut equal to `a.size` means every key is strictly less than `q`. -/
def lowerBound (a : Array Key) (q : Key) : Nat × Nat :=
  PrefixProbe.searchLog (lessPrefix a q) 0 (a.size + 1)

theorem lowerBound_spec (a : Array Key) (q : Key) (hs : StrictSorted a) :
    let cut := (lowerBound a q).1
    cut ≤ a.size ∧
      ∀ (i : Nat) (hi : i < a.size),
        (lexLess (a[i]'hi) q ↔ i < cut) ∧
        (¬ lexLess (a[i]'hi) q ↔ cut ≤ i) := by
  intro cut
  obtain ⟨_, hcut, _, _, hclass⟩ :=
    PrefixProbe.searchLog_spec (lessPrefix a q) 0 (a.size + 1)
      (by omega) (by rfl) (prefix_upper a q) (prefix_mono a q hs)
  have hc : cut < a.size + 1 := hcut
  constructor
  · omega
  · intro i hi
    have hp := (hclass (i + 1) (by omega) (by omega)).1
    have hiff : lexLess (a[i]'hi) q ↔ i + 1 ≤ cut :=
      (prefix_real_true a q i hi).symm.trans hp
    constructor
    · exact hiff.trans (by omega)
    · rw [hiff]
      omega

theorem lowerBound_count_le (a : Array Key) (q : Key) :
    (lowerBound a q).2 ≤ Nat.log2 (a.size + 1) + 1 := by
  simpa [lowerBound] using
    (PrefixProbe.searchLog_count_le (lessPrefix a q) 0 (a.size + 1))

/-- Charge one additional probe for the final bounded check.
When the cut is at `a.size`, this check does not read the array. -/
def lookup (a : Array Key) (q : Key) : Option Nat × Nat :=
  let r := lowerBound a q
  let cut := r.1
  let found :=
    if hc : cut < a.size then
      if (a[cut]'hc) = q then some cut else none
    else none
  (found, r.2 + 1)

theorem lookup_count_eq (a : Array Key) (q : Key) :
    (lookup a q).2 = (lowerBound a q).2 + 1 := rfl

theorem lookup_count_le (a : Array Key) (q : Key) :
    (lookup a q).2 ≤ Nat.log2 (a.size + 1) + 2 := by
  rw [lookup_count_eq]
  have h := lowerBound_count_le a q
  omega

theorem lookup_eq_some_iff (a : Array Key) (q : Key)
    (hs : StrictSorted a) (i : Nat) :
    (lookup a q).1 = some i ↔ ∃ hi : i < a.size, (a[i]'hi) = q := by
  let cut := (lowerBound a q).1
  change
    (if hc : cut < a.size then
      if (a[cut]'hc) = q then some cut else none
    else none) = some i ↔ ∃ hi : i < a.size, (a[i]'hi) = q
  constructor
  · intro h
    by_cases hc : cut < a.size
    · rw [dite_eq_left hc] at h
      by_cases he : (a[cut]'hc) = q
      · rw [ite_eq_left he] at h
        have hci : cut = i := Option.some.inj h
        subst i
        exact ⟨hc, he⟩
      · simp [he] at h
    · simp [hc] at h
  · intro h
    obtain ⟨hi, he⟩ := h
    have hclass :
        ∀ (j : Nat) (hj : j < a.size),
          (lexLess (a[j]'hj) q ↔ j < cut) ∧
          (¬ lexLess (a[j]'hj) q ↔ cut ≤ j) :=
      (lowerBound_spec a q hs).2
    have hnot : ¬ lexLess (a[i]'hi) q := by
      rw [he]
      exact lexLess_irrefl q
    have hle : cut ≤ i := (hclass i hi).2.mp hnot
    have hc : cut < a.size := by omega
    have hci : cut = i := by
      by_cases hlt : cut < i
      · have hless := hs cut i hc hi hlt
        rw [he] at hless
        have hn : ¬ lexLess (a[cut]'hc) q :=
          (hclass cut hc).2.mpr (Nat.le_refl cut)
        exact False.elim (hn hless)
      · omega
    subst i
    rw [dite_eq_left hc, ite_eq_left he]

theorem lookup_member_iff (a : Array Key) (q : Key) (hs : StrictSorted a) :
    (∃ i : Nat, (lookup a q).1 = some i) ↔
      ∃ (i : Nat) (hi : i < a.size), (a[i]'hi) = q := by
  constructor
  · intro h
    obtain ⟨i, h⟩ := h
    obtain ⟨hi, he⟩ := (lookup_eq_some_iff a q hs i).mp h
    exact ⟨i, hi, he⟩
  · intro h
    obtain ⟨i, hi, he⟩ := h
    exact ⟨i, (lookup_eq_some_iff a q hs i).mpr ⟨hi, he⟩⟩

end PaperB.PairLookup
