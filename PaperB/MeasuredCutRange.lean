module

public import PaperB.ForestHead

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestHead

theorem measuredSearch_cut_lt_hi (p : Nat → Probe) (fuel lo hi : Nat)
    (hlt : lo < hi) : (measuredSearch p fuel lo hi).cut < hi := by
  induction fuel generalizing lo hi with
  | zero =>
    simpa only [measuredSearch] using hlt
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simpa only [measuredSearch, if_pos hs] using hlt
    · let mid := lo + (hi - lo) / 2
      have hlo : lo < mid := by
        dsimp [mid]
        omega
      have hhi : mid < hi := by
        dsimp [mid]
        omega
      simp only [measuredSearch, if_neg hs]
      change
        (if (p mid).ok then measuredSearch p fuel mid hi
         else measuredSearch p fuel lo mid).cut < hi
      by_cases hq : (p mid).ok = true
      · rw [if_pos hq]
        exact ih mid hi hhi
      · rw [if_neg hq]
        exact Nat.lt_trans (ih lo mid hlo) hhi

end PaperB.ForestHead
