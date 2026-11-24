module

public import PaperB.RamPairSliceBinding

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamPairWorkerCalls

open Machine RamProgram PairLookup ColumnReduction RamPairSliceBinding

/-- The scalar worker runs separately on the two first-column queries
    (omitting the predecessor query at zero) and on the second-column band.
    The step counts are those of the individual runs, not of a linked program. -/
theorem worker_calls_correct {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    {input : RamProgram.Input (Predecessor.layout bits cap hcap)}
    {a : Array Key}
    (c : Columns (bits := bits)
      input.words a)
    (hs : StrictSorted a) (x y : Machine.Word bits) :
    let call (p : Slice (bits := bits) input.words)
        (key : Machine.Word bits) (cut steps : Nat) : Prop :=
      Answer p key cut ∧
      steps ≤ 11 * (Nat.log2 (p.len + 1) + 1) ∧
      ∃ r, run (Predecessor.worker hcap) input
            (11 * (Nat.log2 (p.len + 1) + 1))
            (Predecessor.init (toPredecessor (input := input) p) key) = some r ∧
        Predecessor.lower r.finalState = cut ∧
        r.finalState.data = #[] ∧
        r.executed = steps
    ∃ (lo hi k predSteps xSteps ySteps : Nat)
        (hlo : lo ≤ hi) (hhi : hi ≤ c.second.len),
      (if x.val = 0 then lo = 0 ∧ predSteps = 0
       else call c.first (ColumnReduction.predecessor x) lo predSteps) ∧
      call c.first x hi xSteps ∧
      IsBand c.first x lo hi ∧
      call (c.second.sub lo hi hlo hhi) y k ySteps ∧
      finish c.first c.second x y lo k =
        (PairLookup.lookup a (x.val, y.val)).1 ∧
      predSteps + xSteps + ySteps ≤ 33 * (Nat.log2 (a.size + 1) + 1) := by
  intro call
  have execute (p : Slice (bits := bits) input.words)
      (key : Machine.Word bits) (sorted : p.Sorted) :
      ∃ cut steps, call p key cut steps := by
    obtain ⟨r, hrun, hanswer, hdata, hsteps⟩ :=
      worker_correct_on_column (input := input) (hcap := hcap) p key sorted
    exact ⟨Predecessor.lower r.finalState, r.executed,
      hanswer, hsteps, r, hrun, rfl, hdata, rfl⟩

  have firstSorted : c.first.Sorted := by
    intro i j hi hj hij
    have ia : i < a.size := by simpa only [c.first_len] using hi
    have ja : j < a.size := by simpa only [c.first_len] using hj
    rw [c.first_word i ia, c.first_word j ja]
    have hlex := hs i j ia ja hij
    unfold lexLess at hlex
    rcases hlex with h | ⟨h, _⟩
    · exact Nat.le_of_lt h
    · exact Nat.le_of_eq h

  obtain ⟨lo, predSteps, hl, hpred, hpredSteps⟩ :
      ∃ lo predSteps, LowerCut c.first x lo ∧
        (if x.val = 0 then lo = 0 ∧ predSteps = 0
         else call c.first (ColumnReduction.predecessor x) lo predSteps) ∧
        predSteps ≤ 11 * (Nat.log2 (a.size + 1) + 1) := by
    by_cases hz : x.val = 0
    · exact ⟨0, 0, by simp [LowerCut, hz], by simp [hz], Nat.zero_le _⟩
    · obtain ⟨lo, steps, hcall⟩ :=
        execute c.first (ColumnReduction.predecessor x) firstSorted
      exact ⟨lo, steps,
        by simpa only [LowerCut, if_neg hz] using hcall.1,
        by simpa only [if_neg hz] using hcall,
        by simpa only [c.first_len] using hcall.2.1⟩

  obtain ⟨hi, xSteps, hx⟩ := execute c.first x firstSorted
  obtain ⟨hlo, hhiFirst, hband⟩ := ColumnReduction.band_spec hl hx.1
  have hhiSize : hi ≤ a.size := by simpa only [c.first_len] using hhiFirst
  have hhi : hi ≤ c.second.len := by simpa only [c.second_len] using hhiSize
  let p := c.second.sub lo hi hlo hhi

  have bandSorted : p.Sorted := by
    intro i j ii jj hij
    have ib : i < hi - lo := ii
    have jb : j < hi - lo := jj
    have ia : lo + i < a.size := by omega
    have ja : lo + j < a.size := by omega
    have fi : lo + i < c.first.len := by simpa only [c.first_len] using ia
    have fj : lo + j < c.first.len := by simpa only [c.first_len] using ja
    have ei := (hband (lo + i) fi).mp ⟨by omega, by omega⟩
    have ej := (hband (lo + j) fj).mp ⟨by omega, by omega⟩
    rw [c.first_word (lo + i) ia] at ei
    rw [c.first_word (lo + j) ja] at ej
    have hlex := hs (lo + i) (lo + j) ia ja (by omega)
    unfold lexLess at hlex
    simp only [p, Slice.sub_get]
    rw [c.second_word (lo + i) ia, c.second_word (lo + j) ja]
    rcases hlex with h | ⟨_, h⟩
    · omega
    · exact Nat.le_of_lt h

  obtain ⟨k, ySteps, hy⟩ := execute p y bandSorted
  have hlookup := ColumnReduction.cuts_correct c hs x y hl hx.1 hlo hhi hy.1
  have hpLen : p.len ≤ a.size := by
    change hi - lo ≤ a.size
    exact Nat.le_trans (Nat.sub_le hi lo) hhiSize
  have hlog : Nat.log2 (p.len + 1) ≤ Nat.log2 (a.size + 1) := by
    have hlen : p.len + 1 ≤ a.size + 1 := Nat.succ_le_succ hpLen
    exact (Nat.le_log2 (by omega : a.size + 1 ≠ 0)).mpr
      (Nat.le_trans (Nat.log2_self_le (by omega : p.len + 1 ≠ 0)) hlen)
  have hxSteps : xSteps ≤ 11 * (Nat.log2 (a.size + 1) + 1) := by
    simpa only [c.first_len] using hx.2.1
  have hySteps := hy.2.1
  have htotal :
      predSteps + xSteps + ySteps ≤ 33 * (Nat.log2 (a.size + 1) + 1) := by
    omega
  exact ⟨lo, hi, k, predSteps, xSteps, ySteps, hlo, hhi,
    hpred, hx, hband, hy, hlookup, htotal⟩

end PaperB.RamPairWorkerCalls
