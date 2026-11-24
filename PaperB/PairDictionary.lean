module

public import PaperB.PairKeyMerge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Append after the supplied PaperB.PairLookup.KeyMerge namespace.
namespace PaperB.PairLookup.KeyMerge


def halves (xs : List Key) : List Key × List Key :=
  xs.splitAt (xs.length / 2)

private theorem halves_append (xs : List Key) :
    (halves xs).1 ++ (halves xs).2 = xs := by
  simp [halves, List.splitAt_eq, List.take_append_drop]

private theorem halves_lengths (xs : List Key) :
    (halves xs).1.length = xs.length / 2 ∧
    (halves xs).2.length = xs.length - xs.length / 2 := by
  have h : xs.length / 2 ≤ xs.length := by omega
  simp [halves, List.splitAt_eq, List.length_take, List.length_drop,
    Nat.min_eq_left h]

private theorem halves_decrease (xs : List Key) (h : ¬ xs.length ≤ 1) :
    (halves xs).1.length < xs.length ∧
    (halves xs).2.length < xs.length := by
  obtain ⟨hl, hr⟩ := halves_lengths xs
  constructor <;> omega

private theorem pow_halves {n d : Nat} (h : n ≤ 2 ^ (d + 1)) :
    n / 2 ≤ 2 ^ d ∧ n - n / 2 ≤ 2 ^ d := by
  rw [Nat.pow_succ] at h
  constructor <;> omega

private theorem short_increasing (xs : List Key) (h : xs.length ≤ 1) :
    Increasing xs := by
  cases xs with
  | nil => exact Increasing.nil
  | cons x ys =>
    cases ys with
    | nil => exact Increasing.cons (by simp) Increasing.nil
    | cons y zs =>
      simp only [List.length_cons] at h
      omega

structure BuildResult where
  keys : List Key
  /-- Sum of the actual `lexLess` tests at all internal nodes. -/
  comparisons : Nat

private def joinResults (a b : BuildResult) : BuildResult :=
  let m := merge a.keys b.keys
  ⟨m.keys, a.comparisons + b.comparisons + m.comparisons⟩

/-- Functional list implementation. Only the root result is converted to an
array. The comparison counter is not an allocation or live-storage counter. -/
def build (xs : List Key) : BuildResult :=
  if h : xs.length ≤ 1 then
    ⟨xs, 0⟩
  else
    joinResults (build (halves xs).1) (build (halves xs).2)
termination_by xs.length
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | exact (halves_decrease xs (by assumption)).1
    | exact (halves_decrease xs (by assumption)).2

private theorem build_leaf (xs : List Key) (h : xs.length ≤ 1) :
    build xs = ⟨xs, 0⟩ := by
  rw [build] <;> simp only [dif_pos h, if_pos h]

private theorem build_node (xs : List Key) (h : ¬ xs.length ≤ 1) :
    build xs = joinResults (build (halves xs).1) (build (halves xs).2) := by
  rw [build] <;> simp only [dif_neg h, if_neg h]

structure BuildSpec (xs : List Key) (r : BuildResult) : Prop where
  mem_iff : ∀ k : Key, k ∈ r.keys ↔ k ∈ xs
  increasing : Increasing r.keys
  length_le : r.keys.length ≤ xs.length
  /-- A budget of `d` binary levels suffices whenever `K ≤ 2^d`. -/
  comparisons_le : ∀ d : Nat, xs.length ≤ 2 ^ d →
    r.comparisons ≤ 2 * xs.length * d

theorem build_spec (xs : List Key) : BuildSpec xs (build xs) := by
  by_cases h : xs.length ≤ 1
  · rw [build_leaf xs h]
    exact ⟨fun _ => Iff.rfl, short_increasing xs h, Nat.le_refl _,
      fun _ _ => Nat.zero_le _⟩
  · let a := (halves xs).1
    let b := (halves xs).2
    have ha : BuildSpec a (build a) := build_spec a
    have hb : BuildSpec b (build b) := build_spec b
    have happ : a ++ b = xs := halves_append xs
    have hsum : a.length + b.length = xs.length := by
      have hh := congrArg List.length happ
      simpa only [List.length_append] using hh
    have hm := merge_spec ha.increasing hb.increasing
    have hlocal : (merge (build a).keys (build b).keys).comparisons ≤
        2 * xs.length := by
      have hc := (merge_comparison_bounds ha.increasing hb.increasing).1
      have hla := ha.length_le
      have hlb := hb.length_le
      omega
    rw [build_node xs h]
    change BuildSpec xs (joinResults (build a) (build b))
    refine ⟨?_, hm.increasing, ?_, ?_⟩
    · intro k
      change k ∈ (merge (build a).keys (build b).keys).keys ↔ k ∈ xs
      rw [hm.mem_iff k, ha.mem_iff k, hb.mem_iff k]
      have hk : k ∈ a ++ b ↔ k ∈ a ∨ k ∈ b := List.mem_append
      rw [happ] at hk
      exact hk.symm
    · change (merge (build a).keys (build b).keys).keys.length ≤ xs.length
      have ht := hm.length_charge
      have hla := ha.length_le
      have hlb := hb.length_le
      omega
    · intro d hd
      cases d with
      | zero =>
        simp only [Nat.pow_zero] at hd
        exact False.elim (h hd)
      | succ d =>
        obtain ⟨hla, hlb⟩ := halves_lengths xs
        have hp := pow_halves hd
        have hpa : a.length ≤ 2 ^ d := by
          change (halves xs).1.length ≤ 2 ^ d
          rw [hla]
          exact hp.1
        have hpb : b.length ≤ 2 ^ d := by
          change (halves xs).2.length ≤ 2 ^ d
          rw [hlb]
          exact hp.2
        have hscale : 2 * a.length + 2 * b.length = 2 * xs.length := by
          omega
        have hchildren : (build a).comparisons + (build b).comparisons ≤
            2 * xs.length * d := by
          calc
            _ ≤ 2 * a.length * d + 2 * b.length * d :=
              Nat.add_le_add (ha.comparisons_le d hpa) (hb.comparisons_le d hpb)
            _ = _ := by rw [← Nat.add_mul, hscale]
        -- The node charge is at most 2K; the two child lengths sum to K.
        change (build a).comparisons + (build b).comparisons +
          (merge (build a).keys (build b).keys).comparisons ≤
          2 * xs.length * (d + 1)
        rw [Nat.mul_succ]
        exact Nat.add_le_add hchildren hlocal
termination_by xs.length
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | exact (halves_decrease xs (by assumption)).1
    | exact (halves_decrease xs (by assumption)).2

/-- The least `d` with `n ≤ 2^d`, including value zero at `n = 0`.
This is used for bounds, not by `build`. -/
def ceilBinaryLog (n : Nat) : Nat :=
  if h : n ≤ 1 then 0 else ceilBinaryLog (n - n / 2) + 1
termination_by n
decreasing_by simp_wf <;> omega

private theorem log_leaf (n : Nat) (h : n ≤ 1) :
    ceilBinaryLog n = 0 := by
  rw [ceilBinaryLog] <;> simp only [dif_pos h, if_pos h]

private theorem log_node (n : Nat) (h : ¬ n ≤ 1) :
    ceilBinaryLog n = ceilBinaryLog (n - n / 2) + 1 := by
  rw [ceilBinaryLog] <;> simp only [dif_neg h, if_neg h]

theorem ceilBinaryLog_le_iff (n d : Nat) :
    ceilBinaryLog n ≤ d ↔ n ≤ 2 ^ d := by
  induction d generalizing n with
  | zero =>
    rw [Nat.pow_zero]
    by_cases h : n ≤ 1
    · rw [log_leaf n h]
      simp [h]
    · rw [log_node n h]
      omega
  | succ d ih =>
    by_cases h : n ≤ 1
    · have hn : n ≤ 2 ^ d :=
        (ih n).mp (by rw [log_leaf n h]; exact Nat.zero_le d)
      rw [log_leaf n h, Nat.pow_succ]
      omega
    · rw [log_node n h, Nat.pow_succ]
      constructor
      · intro hd
        have hr : ceilBinaryLog (n - n / 2) ≤ d := by omega
        have hn := (ih (n - n / 2)).mp hr
        omega
      · intro hn
        have hr : n - n / 2 ≤ 2 ^ d := by omega
        have hd := (ih (n - n / 2)).mpr hr
        omega

/-- For `K = xs.length`, at most `2K * ceil(log₂ K)` head tests
(with the empty-input convention above). -/
theorem build_comparisons_log (xs : List Key) :
    (build xs).comparisons ≤ 2 * xs.length * ceilBinaryLog xs.length :=
  (build_spec xs).comparisons_le _
    ((ceilBinaryLog_le_iff xs.length _).mp (Nat.le_refl _))

def dictionary (xs : List Key) : Array Key :=
  (build xs).keys.toArray

theorem dictionary_spec (xs : List Key) :
    StrictSorted (dictionary xs) ∧
      ∀ k : Key, k ∈ (dictionary xs).toList ↔ k ∈ xs := by
  have h := build_spec xs
  refine ⟨increasing_toArray h.increasing, ?_⟩
  intro k
  first
  | exact h.mem_iff k
  | simpa [dictionary] using h.mem_iff k

private theorem not_lexLess_self (x : Key) : ¬ lexLess x x := by
  rcases x with ⟨a, b⟩
  change ¬ (a < a ∨ (a = a ∧ b < b))
  omega

private theorem increasing_ext {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys)
    (hm : ∀ k : Key, k ∈ xs ↔ k ∈ ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hn := (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
      simp at hn
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hn := (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
      simp at hn
    | cons y ys =>
      have hxy : x ∈ y :: ys :=
        (hm x).mp (List.mem_cons.mpr (Or.inl rfl))
      have hyx : y ∈ x :: xs :=
        (hm y).mpr (List.mem_cons.mpr (Or.inl rfl))
      have he : x = y := by
        by_cases h : x = y
        · exact h
        · have hxr : x ∈ ys := (List.mem_cons.mp hxy).resolve_left h
          have hyr : y ∈ xs :=
            (List.mem_cons.mp hyx).resolve_left (fun e => h e.symm)
          exact False.elim (not_lexLess_self x
            (lexLess_trans (hx.head y hyr) (hy.head x hxr)))
      subst y
      have ht : ∀ k : Key, k ∈ xs ↔ k ∈ ys := by
        intro k
        by_cases hk : k = x
        · subst k
          have hnx : x ∉ xs := fun hk => not_lexLess_self x (hx.head x hk)
          have hny : x ∉ ys := fun hk => not_lexLess_self x (hy.head x hk)
          simp [hnx, hny]
        · simpa only [List.mem_cons, hk, false_or] using hm k
      have e : xs = ys := by
        apply ih
        all_goals first | exact hx.tail | exact hy.tail | exact ht
      exact congrArg (List.cons x) e

/-- Input order and repeated occurrences do not change the dictionary. -/
theorem dictionary_eq_of_mem_iff (xs ys : List Key)
    (h : ∀ k : Key, k ∈ xs ↔ k ∈ ys) : dictionary xs = dictionary ys := by
  have hx := build_spec xs
  have hy := build_spec ys
  have e := increasing_ext hx.increasing hy.increasing
    (fun k => (hx.mem_iff k).trans ((h k).trans (hy.mem_iff k).symm))
  exact congrArg (fun ks : List Key => ks.toArray) e

namespace Workspace

/-!
Separate fixed-buffer layout for a depth-first implementation:

* Use two banks of `K` key slots. Start with input in bank zero. A job owns
  a span and is told which bank receives its result. Visit its children
  sequentially, asking each to write to the opposite bank. A leaf reads
  its original slot before writing; no ancestor has merged yet, and jobs
  already completed outside that leaf's span cannot overwrite it.
* A child returns the length of its occupied prefix. Merge the two prefixes
  with cursors, reading one bank and writing the other. Keep the count in
  the job's frame; unused suffix slots do not need to be cleared. The prefix
  bound below includes ties and the untouched suffix.
* One frame slot per depth suffices for this schedule: only ancestors and
  the current job are live. A frame needs a fixed number of fields for
  span, phase, bank, prefix lengths, and cursors. The parent may retain the
  left prefix length while the right child reuses the next frame slot.

The definitions below certify addresses for that layout: `2K` key slots and
`ceilBinaryLog K + 1` frame slots. If a separately owned compact output is
required, copying the final prefix needs at most `K` more key slots. These
are slot capacities for the stated layout, not a byte bound or a physical
peak claim about the compiled list recursion above. `dictionary` does not
execute this buffer schedule.
-/

structure Span (capacity : Nat) where
  base : Nat
  width : Nat
  fits : base + width ≤ capacity

def Span.root (k : Nat) : Span k :=
  ⟨0, k, by omega⟩

def Span.left {k : Nat} (s : Span k) : Span k :=
  ⟨s.base, s.width / 2, by have h := s.fits; omega⟩

def Span.right {k : Nat} (s : Span k) : Span k :=
  ⟨s.base + s.width / 2, s.width - s.width / 2,
    by have h := s.fits; omega⟩

def Span.addr {k : Nat} (s : Span k) (i : Fin s.width) : Fin k :=
  ⟨s.base + i.val, by
    have hi := i.isLt
    have hs := s.fits
    omega⟩

theorem child_addresses_ordered {k : Nat} (s : Span k)
    (i : Fin s.left.width) (j : Fin s.right.width) :
    (s.left.addr i).val < (s.right.addr j).val := by
  have hi := i.isLt
  change i.val < s.width / 2 at hi
  change s.base + i.val < (s.base + s.width / 2) + j.val
  omega

def Span.keySlot {k : Nat} (s : Span k) (bank : Bool)
    (i : Fin s.width) : Fin (2 * k) :=
  match bank with
  | false => ⟨(s.addr i).val, by have h := (s.addr i).isLt; omega⟩
  | true => ⟨k + (s.addr i).val, by have h := (s.addr i).isLt; omega⟩

theorem bank_addresses_ordered {k : Nat} (s t : Span k)
    (i : Fin s.width) (j : Fin t.width) :
    (s.keySlot false i).val < (t.keySlot true j).val := by
  change (s.addr i).val < k + (t.addr j).val
  have hi := (s.addr i).isLt
  omega

def Span.prefixSlot {k n : Nat} (s : Span k) (bank : Bool)
    (h : n ≤ s.width) (i : Fin n) : Fin (2 * k) :=
  s.keySlot bank ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

theorem merged_prefix_fits {k : Nat} (s : Span k) {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys)
    (hl : xs.length ≤ s.left.width) (hr : ys.length ≤ s.right.width) :
    (merge xs ys).keys.length ≤ s.width := by
  change xs.length ≤ s.width / 2 at hl
  change ys.length ≤ s.width - s.width / 2 at hr
  have h := (merge_spec hx hy).length_charge
  omega

structure Frame (capacity : Nat) where
  span : Span capacity
  depth : Nat
  remaining : Nat
  depth_budget : depth + remaining = ceilBinaryLog capacity
  width_budget : span.width ≤ 2 ^ remaining

def Frame.root (k : Nat) : Frame k :=
  ⟨Span.root k, 0, ceilBinaryLog k, Nat.zero_add _,
    (ceilBinaryLog_le_iff k _).mp (Nat.le_refl _)⟩

def Frame.slot {k : Nat} (f : Frame k) : Fin (ceilBinaryLog k + 1) :=
  ⟨f.depth, by have h := f.depth_budget; omega⟩

theorem Frame.remaining_positive {k : Nat} (f : Frame k)
    (h : 1 < f.span.width) : 0 < f.remaining := by
  cases hr : f.remaining with
  | zero =>
    have hw := f.width_budget
    rw [hr, Nat.pow_zero] at hw
    omega
  | succ d => omega

/-- Both children use depth `f.depth + 1` and therefore share a frame
slot when visited sequentially. The parent keeps its own slot. -/
def Frame.children {k : Nat} (f : Frame k) (d : Nat)
    (h : f.remaining = d + 1) : Frame k × Frame k := by
  have hw : f.span.width ≤ 2 ^ (d + 1) := by
    simpa only [h] using f.width_budget
  have hc := pow_halves hw
  have hd : f.depth + 1 + d = ceilBinaryLog k := by
    have he := f.depth_budget
    omega
  exact (⟨f.span.left, f.depth + 1, d, hd, hc.1⟩,
    ⟨f.span.right, f.depth + 1, d, hd, hc.2⟩)

end Workspace
end PaperB.PairLookup.KeyMerge
