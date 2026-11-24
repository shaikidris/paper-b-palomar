module

public import PaperB.RamPredecessorWorker

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram.Predecessor

open PaperB.Machine (Word)

private abbrev inputLayout {bits : Nat} {L : Layout bits} (_ : Input L) := L

/-- The entries outside the live interval are already on the correct
side of the upper-bound partition. -/
def Partition {bits cap : Nat} {hcap} {input}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    (key : Word bits) (s : State (inputLayout input)) : Prop :=
  (∀ (i : Nat) (hi : i < p.len), i < lower s → (p.get i hi).val ≤ key.val) ∧
  (∀ (i : Nat) (hi : i < p.len), upper s ≤ i → key.val < (p.get i hi).val)

/-- `k` is the upper-bound index: entries to its left are at most the
key, and entries at or to its right are strictly greater. -/
def Answer {bits cap : Nat} {hcap} {input}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    (key : Word bits) (k : Nat) : Prop :=
  k ≤ p.len ∧
  (∀ (i : Nat) (hi : i < p.len), i < k → (p.get i hi).val ≤ key.val) ∧
  (∀ (i : Nat) (hi : i < p.len), k ≤ i → key.val < (p.get i hi).val)

theorem Answer.unique {bits cap : Nat} {hcap} {input}
    {p : Slice (bits := bits) (cap := cap) (hcap := hcap) input}
    {key : Word bits} {a b : Nat} (ha : Answer p key a) (hb : Answer p key b) :
    a = b := by
  rcases Nat.lt_trichotomy a b with hab | heq | hba
  · have hi : a < p.len := Nat.lt_of_lt_of_le hab hb.1
    exact False.elim
      (Nat.not_lt_of_ge (hb.2.1 a hi hab) (ha.2.2 a hi (Nat.le_refl a)))
  · exact heq
  · have hi : b < p.len := Nat.lt_of_lt_of_le hba ha.1
    exact False.elim
      (Nat.not_lt_of_ge (ha.2.1 b hi hba) (hb.2.2 b hi (Nat.le_refl b)))

/-- A live iteration preserves the partition and the arena, and leaves
at most half the previous interval length. -/
theorem worker_partition_step {bits cap : Nat} {hcap} {input}
    {p : Slice (bits := bits) (cap := cap) (hcap := hcap) input}
    {key : Word bits} {s : State (inputLayout input)}
    (sorted : p.Sorted) (H : Head p key s) (P : Partition p key s)
    (live : lower s < upper s) :
    ∃ t, Steps (worker hcap) input 9 s t ∧ Head p key t ∧
      Partition p key t ∧ t.data = s.data ∧
      upper t - lower t ≤ (upper s - lower s) / 2 := by
  obtain ⟨t, trace, Ht, dt, split⟩ := worker_iteration H live
  have hm : midpoint s < p.len :=
    Nat.lt_of_lt_of_le (midpoint_lt_upper live) H.inSlice
  change
    (key.val < (p.get (midpoint s) hm).val ∧
      lower t = lower s ∧ upper t = midpoint s) ∨
    ((p.get (midpoint s) hm).val ≤ key.val ∧
      lower t = midpoint s + 1 ∧ upper t = upper s) at split
  refine ⟨t, trace, Ht, ?_, dt, ?_⟩
  · rcases split with ⟨cmp, hlo, hhi⟩ | ⟨cmp, hlo, hhi⟩
    · constructor
      · intro i hi h
        rw [hlo] at h
        exact P.1 i hi h
      · intro i hi h
        rw [hhi] at h
        exact Nat.lt_of_lt_of_le cmp (sorted (midpoint s) i hm hi h)
    · constructor
      · intro i hi h
        rw [hlo] at h
        exact Nat.le_trans (sorted i (midpoint s) hi hm (by omega)) cmp
      · intro i hi h
        rw [hhi] at h
        exact P.2 i hi h
  · rcases split with ⟨_, hlo, hhi⟩ | ⟨_, hlo, hhi⟩
    · rw [hlo, hhi]
      unfold midpoint
      omega
    · rw [hlo, hhi]
      unfold midpoint
      omega

private theorem stop_with_fuel {bits cap : Nat} {hcap} {input}
    {p : Slice (bits := bits) (cap := cap) (hcap := hcap) input}
    {key : Word bits} {s : State (inputLayout input)}
    {fuel : Nat} (H : Head p key s) (P : Partition p key s)
    (cross : upper s ≤ lower s) (hfuel : 2 ≤ fuel) :
    ∃ r, run (worker hcap) input fuel s = some r ∧
      Answer p key (lower r.finalState) ∧ r.finalState.data = s.data ∧
      r.executed ≤ fuel := by
  let t : State (inputLayout input) := { s with pc := 11 }
  have hr : run (worker hcap) input 2 s = some ⟨t, 2⟩ :=
    worker_crossed H.pc_zero cross
  have heq : upper s = lower s := Nat.le_antisymm cross H.ordered
  refine ⟨⟨t, 2⟩, run_stable_of_le hfuel hr, ?_, rfl, hfuel⟩
  change Answer p key (lower s)
  refine ⟨Nat.le_trans H.ordered H.inSlice, P.1, ?_⟩
  intro i hi h
  exact P.2 i hi (heq.symm ▸ h)

/-- An interval shorter than `2^k` needs at most `k` live iterations
followed by the two-instruction exit, including the halt. -/
theorem worker_power_budget {bits cap : Nat} {hcap} {input}
    {p : Slice (bits := bits) (cap := cap) (hcap := hcap) input}
    {key : Word bits} (sorted : p.Sorted) (k : Nat)
    {s : State (inputLayout input)}
    (H : Head p key s) (P : Partition p key s)
    (width : upper s - lower s < 2 ^ k) :
    ∃ r, run (worker hcap) input (9 * k + 2) s = some r ∧
      Answer p key (lower r.finalState) ∧ r.finalState.data = s.data ∧
      r.executed ≤ 9 * k + 2 := by
  induction k generalizing s with
  | zero =>
    have cross : upper s ≤ lower s := by
      change upper s - lower s < 1 at width
      omega
    exact stop_with_fuel H P cross (by decide)
  | succ k ih =>
    by_cases live : lower s < upper s
    · obtain ⟨t, trace, Ht, Pt, dt, half⟩ :=
        worker_partition_step sorted H P live
      have smaller : upper t - lower t < 2 ^ k := by
        rw [Nat.pow_succ] at width
        omega
      obtain ⟨r, hr, ans, dr, count⟩ := ih Ht Pt smaller
      refine ⟨⟨r.finalState, 9 + r.executed⟩, ?_, ans, dr.trans dt, ?_⟩
      · have fuel_eq : 9 * (k + 1) + 2 = 9 + (9 * k + 2) := by omega
        rw [fuel_eq]
        exact trace.thenRun hr
      · change 9 + r.executed ≤ 9 * (k + 1) + 2
        omega
    · exact stop_with_fuel H P (Nat.le_of_not_gt live) (by omega)

/-- Starting with an empty writable arena, the worker returns the unique
upper-bound index within the stated logarithmic instruction budget. -/
theorem worker_correct {bits cap : Nat} {hcap} {input}
    (p : Slice (bits := bits) (cap := cap) (hcap := hcap) input)
    (key : Word bits) (sorted : p.Sorted) :
    let budget := 11 * (Nat.log2 (p.len + 1) + 1)
    ∃ r, run (worker hcap) input budget (init p key) = some r ∧
      Answer p key (lower r.finalState) ∧ r.finalState.data = #[] ∧
      r.executed ≤ budget := by
  let k := Nat.log2 (p.len + 1) + 1
  have H : Head p key (init p key) :=
    ⟨rfl, rfl, rfl, rfl, Nat.zero_le _, Nat.le_refl _⟩
  have P : Partition p key (init p key) := by
    constructor
    · intro i hi h
      change i < 0 at h
      omega
    · intro i hi h
      change p.len ≤ i at h
      omega
  have hp : p.len + 1 < 2 ^ k := by
    change p.len + 1 < 2 ^ (Nat.log2 (p.len + 1) + 1)
    first
    | exact (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _)
    | exact Nat.lt_pow_succ_log2 (by omega)
    | exact Nat.lt_pow_succ_log2 (p.len + 1)
    | exact (Nat.log2_lt_iff_lt_pow (by omega)).mp (Nat.lt_succ_self _)
  have hw : upper (init p key) - lower (init p key) < 2 ^ k := by
    change p.len - 0 < 2 ^ k
    omega
  obtain ⟨r, hr, ans, hd, count⟩ := worker_power_budget sorted k H P hw
  have hk : 0 < k := Nat.succ_pos _
  have hle : 9 * k + 2 ≤ 11 * k := by omega
  exact ⟨r, run_stable_of_le hle hr, ans, hd, Nat.le_trans count hle⟩

end PaperB.RamProgram.Predecessor
