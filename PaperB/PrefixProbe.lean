module

public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PrefixProbe

def search (p : Nat → Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, lo, _ => (lo, 0)
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then (lo, 0)
      else
        let mid := lo + (hi - lo) / 2
        if p mid then
          let r := search p fuel mid hi
          (r.1, r.2 + 1)
        else
          let r := search p fuel lo mid
          (r.1, r.2 + 1)

theorem search_count_le (p : Nat → Bool) (fuel lo hi : Nat) :
    (search p fuel lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero =>
      simp [search]
  | succ fuel ih =>
      simp only [search]
      split
      · exact Nat.zero_le _
      · split
        · exact Nat.succ_le_succ (ih _ _)
        · exact Nat.succ_le_succ (ih _ _)

theorem search_cutoff (p : Nat → Bool) (fuel lo hi : Nat)
    (hWidth : hi - lo ≤ 2 ^ fuel) (hLT : lo < hi)
    (hLo : p lo = true) (hHi : p hi = false) :
    let k := (search p fuel lo hi).1
    lo ≤ k ∧ k < hi ∧ p k = true ∧ p (k + 1) = false := by
  induction fuel generalizing lo hi with
  | zero =>
      simp only [Nat.pow_zero] at hWidth
      have hEq : hi = lo + 1 := by omega
      change lo ≤ lo ∧ lo < hi ∧ p lo = true ∧ p (lo + 1) = false
      exact ⟨Nat.le_refl lo, hLT, hLo, by simpa only [hEq] using hHi⟩
  | succ fuel ih =>
      by_cases hStop : hi ≤ lo + 1
      · have hEq : hi = lo + 1 := by omega
        simp only [search, ite_eq_left hStop]
        exact ⟨Nat.le_refl lo, hLT, hLo, by simpa only [hEq] using hHi⟩
      · rw [Nat.pow_succ] at hWidth
        let mid := lo + (hi - lo) / 2
        have hLoMid : lo < mid := by
          dsimp only [mid]
          omega
        have hMidHi : mid < hi := by
          dsimp only [mid]
          omega
        have hLeft : mid - lo ≤ 2 ^ fuel := by
          dsimp only [mid]
          omega
        have hRight : hi - mid ≤ 2 ^ fuel := by
          dsimp only [mid]
          omega
        cases hMid : p mid with
        | false =>
            have hm : p (lo + (hi - lo) / 2) = false := hMid
            have hn : ¬ (p (lo + (hi - lo) / 2) = true) := by simp [hm]
            simp only [search, ite_eq_right hStop, ite_eq_right hn]
            obtain ⟨hkLo, hkMid, hkTrue, hkFalse⟩ :=
              ih lo mid hLeft hLoMid hLo hMid
            exact ⟨hkLo, Nat.lt_trans hkMid hMidHi, hkTrue, hkFalse⟩
        | true =>
            have hm : p (lo + (hi - lo) / 2) = true := hMid
            simp only [search, ite_eq_right hStop, ite_eq_left hm]
            obtain ⟨hkMid, hkHi, hkTrue, hkFalse⟩ :=
              ih mid hi hRight hMidHi hMid hHi
            exact ⟨Nat.le_trans (Nat.le_of_lt hLoMid) hkMid, hkHi, hkTrue, hkFalse⟩

def searchLog (p : Nat → Bool) (lo hi : Nat) : Nat × Nat :=
  search p (Nat.log2 (hi - lo) + 1) lo hi

theorem searchLog_count_le (p : Nat → Bool) (lo hi : Nat) :
    (searchLog p lo hi).2 ≤ Nat.log2 (hi - lo) + 1 :=
  search_count_le p (Nat.log2 (hi - lo) + 1) lo hi

theorem searchLog_spec (p : Nat → Bool) (lo hi : Nat)
    (hLT : lo < hi) (hLo : p lo = true) (hHi : p hi = false)
    (hMono : ∀ a b : Nat, lo ≤ a → a ≤ b → b ≤ hi →
      p b = true → p a = true) :
    let cut := (searchLog p lo hi).1
    lo ≤ cut ∧ cut < hi ∧ p cut = true ∧ p (cut + 1) = false ∧
      ∀ j : Nat, lo ≤ j → j ≤ hi →
        (p j = true ↔ j ≤ cut) ∧ (p j = false ↔ cut < j) := by
  intro cut
  have hPow : hi - lo < 2 ^ (Nat.log2 (hi - lo) + 1) := by
    have hne : hi - lo ≠ 0 := by omega
    exact (Nat.log2_lt hne).mp (Nat.lt_succ_self (Nat.log2 (hi - lo)))
  have hCut : lo ≤ cut ∧ cut < hi ∧ p cut = true ∧ p (cut + 1) = false :=
    search_cutoff p (Nat.log2 (hi - lo) + 1) lo hi
      (Nat.le_of_lt hPow) hLT hLo hHi
  obtain ⟨hCutLo, hCutHi, hCutTrue, hNextFalse⟩ := hCut
  refine ⟨hCutLo, hCutHi, hCutTrue, hNextFalse, ?_⟩
  intro j hjLo hjHi
  have hTrue : p j = true ↔ j ≤ cut := by
    constructor
    · intro hjTrue
      by_cases hjCut : j ≤ cut
      · exact hjCut
      · have hNextTrue : p (cut + 1) = true :=
          hMono (cut + 1) j (by omega) (by omega) hjHi hjTrue
        simp [hNextFalse] at hNextTrue
    · intro hjCut
      exact hMono j cut hjLo hjCut (Nat.le_of_lt hCutHi) hCutTrue
  refine ⟨hTrue, ?_⟩
  have hBool : p j = false ↔ ¬ (p j = true) := by
    cases p j <;> simp
  rw [hBool, hTrue]
  omega

end PrefixProbe
