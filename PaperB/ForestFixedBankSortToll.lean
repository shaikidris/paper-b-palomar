module

public import PaperB.ForestFixedBankSort

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open PaperB.PairLookup.KeyMerge.Workspace (Span)

namespace PaperB.PairDictionary.FixedBank

/-- One toll per checked physical step: its head reads, its key comparisons,
and one output key write. This is a proposition, not a second merge loop. -/
inductive MergeCharge {k : Nat} {p : ArrayMerge.Plan k} {orig : Array Key} :
    {a : Array Key} → {i j w : Nat} → {xs : List Key} → {r c : Nat} →
    ArrayMerge.Trace p orig a i j w xs r c → Nat → Prop where
  | nil : MergeCharge (ArrayMerge.Trace.nil (p := p) (orig := orig)) 0
  | snoc {a b : Array Key} {i j w i' j' w' : Nat}
      {xs : List Key} {r c dr dc cost : Nat} {x : Key}
      {t : ArrayMerge.Trace p orig a i j w xs r c}
      (step : ArrayMerge.Step p a i j w b i' j' w' x dr dc) :
      MergeCharge t cost →
      MergeCharge (ArrayMerge.Trace.snoc t step) (cost + (dr + dc + 1))

theorem MergeCharge.ofTrace {k : Nat} {p : ArrayMerge.Plan k}
    {orig a : Array Key} {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : ArrayMerge.Trace p orig a i j w xs r c) :
    MergeCharge t (r + c + w) := by
  induction t with
  | nil => exact MergeCharge.nil
  | @snoc a b i j w i' j' w' xs r c dr dc x t step ih =>
    have hadv := step.advance
    have he : (r + dr) + (c + dc) + w' =
        (r + c + w) + (dr + dc + 1) := by omega
    rw [he]
    exact MergeCharge.snoc step ih

/-- The indices record the input bank, returned bank, returned count, and cost.
Each sort frame costs one unit. At a leaf, `runSpan_leaf` selects `runLeaf`,
whose positive-width branch performs one input read and one output write;
its zero-width branch performs neither. A fork uses the left output as the
right input and the right output as the physical merge input.

Address arithmetic (including bank selection and offsets), cursor tests
and increments, and fuel/count bookkeeping have no separate toll here.
The frame unit is fixed; this trace does not price merge control operations
or array implementation costs such as backing-store copies. -/
inductive SpanCostTrace {k : Nat} :
    Nat → Span k → Bool → Array Key → Array Key → Nat → Nat → Prop where
  | leaf {fuel : Nat} {s : Span k} {dst : Bool} {a : Array Key}
      (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ fuel) (hs : s.width ≤ 1) :
      SpanCostTrace fuel s dst a (runSpan fuel s dst a ha hw).bank
        (runSpan fuel s dst a ha hw).count (1 + if 0 < s.width then 2 else 0)
  | fork {n : Nat} {s : Span k} {dst : Bool} {a lb rb b : Array Key}
      {lc rc w cl cr rd cp : Nat} {xs : List Key}
      (hs : 1 < s.width) (hl : lc ≤ s.left.width) (hr : rc ≤ s.right.width)
      (hrb : rb.size = 2 * k)
      (left : SpanCostTrace n s.left (!dst) a lb lc cl)
      (right : SpanCostTrace n s.right (!dst) lb rb rc cr)
      (t : ArrayMerge.Trace (forkPlan s dst lc rc hl hr) rb b lc rc w xs rd cp)
      (charge : MergeCharge t (rd + cp + w))
      (actual : let m := ArrayMerge.runPacked (forkPlan s dst lc rc hl hr) rb hrb;
        (b, w) = (m.bank, m.count)) :
      SpanCostTrace (n + 1) s dst a b w (1 + cl + cr + (rd + cp + w))

theorem runSpan_costTrace {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ fuel) :
    let out := runSpan fuel s dst a ha hw
    ∃ cost, SpanCostTrace fuel s dst a out.bank out.count cost := by
  induction fuel generalizing s dst a with
  | zero =>
    exact ⟨_, SpanCostTrace.leaf ha hw (by simpa using hw)⟩
  | succ n ih =>
    by_cases hs : s.width ≤ 1
    · exact ⟨_, SpanCostTrace.leaf ha hw hs⟩
    · have hsplit : 1 < s.width := by omega
      let l := runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw)
      let r := runSpan n s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
      let p := forkPlan s dst l.count r.count l.count_le r.count_le
      let m := ArrayMerge.runPacked p r.bank r.size_eq
      obtain ⟨cl, tl⟩ := ih s.left (!dst) a ha (leftBudget (n := n) s hw)
      obtain ⟨cr, tr⟩ := ih s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
      obtain ⟨xs, rd, cp, t, _⟩ := m.certified
      let cost := 1 + cl + cr + (rd + cp + m.count)
      have hm : SpanCostTrace (n + 1) s dst a m.bank m.count cost :=
        SpanCostTrace.fork hsplit l.count_le r.count_le r.size_eq tl tr t
          (MergeCharge.ofTrace t) rfl
      refine ⟨cost, ?_⟩
      exact Eq.mpr (runSpan_fork_observe n s dst a ha hw hsplit
        (fun b _ c _ => SpanCostTrace (n + 1) s dst a b c cost)) hm

/-- The additive term pays for the single frame when the width is zero. -/
theorem SpanCostTrace.bound {k fuel : Nat} {s : Span k} {dst : Bool}
    {a b : Array Key} {w cost : Nat}
    (t : SpanCostTrace fuel s dst a b w cost) :
    cost ≤ 6 * s.width * (fuel + 1) + (if s.width = 0 then 1 else 0) := by
  induction t with
  | @leaf fuel s dst a ha hw hs =>
    by_cases hz : s.width = 0
    · simp [hz]
    · have hp : 0 < s.width := by omega
      simp only [if_neg hz, if_pos hp, Nat.add_zero]
      rw [Nat.mul_add (6 * s.width) fuel 1, Nat.mul_one]
      omega
  | @fork n s dst a lb rb b lc rc w cl cr rd cp xs hs hl hr hrb
      left right t _charge _actual ihl ihr =>
    have hL : s.left.width ≠ 0 := by
      change s.width / 2 ≠ 0
      omega
    have hR : s.right.width ≠ 0 := by
      change s.width - s.width / 2 ≠ 0
      omega
    have hsum : s.left.width + s.right.width = s.width := by
      change s.width / 2 + (s.width - s.width / 2) = s.width
      omega
    simp only [if_neg hL, if_neg hR, Nat.add_zero] at ihl ihr
    have hadd :
        6 * s.left.width * (n + 1) + 6 * s.right.width * (n + 1) =
          6 * s.width * (n + 1) := by
      rw [← Nat.add_mul, ← Nat.mul_add, hsum]
    have hchildren : cl + cr ≤ 6 * s.width * (n + 1) := by
      rw [← hadd]
      exact Nat.add_le_add ihl ihr
    obtain ⟨_, hrd, hcp, _, _⟩ := t.accounting
    have hw : w ≤ s.width := t.fits
    have hmerge : rd + cp + w ≤ 5 * s.width := by omega
    simp only [if_neg (show s.width ≠ 0 by omega), Nat.add_zero]
    rw [Nat.mul_add (6 * s.width) (n + 1) 1, Nat.mul_one]
    omega

theorem runSpan_cost_bound {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ fuel)
    (hp : 0 < s.width) :
    let out := runSpan fuel s dst a ha hw
    ∃ cost, SpanCostTrace fuel s dst a out.bank out.count cost ∧
      cost ≤ 6 * s.width * (fuel + 1) := by
  obtain ⟨cost, t⟩ := runSpan_costTrace fuel s dst a ha hw
  exact ⟨cost, t, by simpa only [if_neg (Nat.ne_of_gt hp), Nat.add_zero] using t.bound⟩

end PaperB.PairDictionary.FixedBank
