module

public import PaperB.ForestFixedBankSort
public import PaperB.ForestArrayMergeExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open PaperB.PairLookup.KeyMerge.Workspace (Span Frame)

namespace PaperB.PairDictionary.FixedBank

private theorem viewBound {k base len i : Nat} (b : Bool)
    (hf : base + len ≤ k) (hi : i < len) :
    bankBase k b + (base + i) < 2 * k := by
  cases b <;> simp [bankBase] <;> omega

private theorem slot_congr_addr {k : Nat} (a : Array Key)
    (ha : a.size = 2 * k) {i j : Nat} (e : i = j)
    (hi : i < 2 * k) (hj : j < 2 * k) :
    ArrayMerge.slot a ha i hi = ArrayMerge.slot a ha j hj := by
  subst j
  rfl

private theorem keysAt_length {k : Nat} (a : Array Key)
    (ha : a.size = 2 * k) (b : Bool) (base len : Nat)
    (hf : base + len ≤ k) :
    (keysAt a ha b base len hf).length = len := by
  simp only [keysAt, List.length_ofFn]

private theorem keysAt_nth {k : Nat} (a : Array Key)
    (ha : a.size = 2 * k) (b : Bool) (base len : Nat)
    (hf : base + len ≤ k) (i : Nat) (hi : i < len) :
    (keysAt a ha b base len hf)[i]'(by simpa only [keysAt_length] using hi) =
      ArrayMerge.slot a ha (bankBase k b + (base + i)) (viewBound b hf hi) := by
  simp only [keysAt, List.getElem_ofFn]

/-- The trace's list describes the physical destination prefix, in write order. -/
theorem trace_output_keysAt {k : Nat} {p : ArrayMerge.Plan k}
    {orig a : Array Key} {i j w : Nat} {xs : List Key} {nr nc : Nat}
    (t : ArrayMerge.Trace p orig a i j w xs nr nc)
    (ho : orig.size = 2 * k) (ha : a.size = 2 * k)
    (dst : Bool) (hsrc : p.source = !dst) (hf : p.outBase + w ≤ k) :
    keysAt a ha dst p.outBase w hf = xs := by
  apply List.ext_getElem
  · rw [keysAt_length]
    exact t.accounting.1.symm
  · intro q hq hxs
    have hqw : q < w := by simpa only [keysAt_length] using hq
    obtain ⟨hw, he⟩ := t.output ho q hxs
    have haddr : bankBase k dst + (p.outBase + q) = p.dstAddr q := by
      cases dst <;> simp [bankBase, ArrayMerge.Plan.dstAddr, hsrc]
    calc
      _ = ArrayMerge.slot a ha (bankBase k dst + (p.outBase + q))
          (viewBound dst hf hqw) :=
        keysAt_nth a ha dst p.outBase w hf q hqw
      _ = ArrayMerge.slot a ha (p.dstAddr q) (p.dstBound hw) :=
        slot_congr_addr a ha haddr (viewBound dst hf hqw) (p.dstBound hw)
      _ = xs[q]'hxs := he

/-- Specification view of the original physical bank-zero span. -/
noncomputable def inputKeys {k : Nat} (a : Array Key) (ha : a.size = 2 * k)
    (s : Span k) : List Key :=
  keysAt a ha false s.base s.width s.fits

private theorem inputKeys_length {k : Nat} (a : Array Key)
    (ha : a.size = 2 * k) (s : Span k) :
    (inputKeys a ha s).length = s.width :=
  keysAt_length a ha false s.base s.width s.fits

private theorem inputIndexBound {k : Nat} (s : Span k) {i : Nat}
    (hi : i < s.width) : s.base + i < 2 * k := by
  have hf := s.fits
  omega

private theorem inputKeys_nth {k : Nat} (a : Array Key)
    (ha : a.size = 2 * k) (s : Span k) (i : Nat) (hi : i < s.width) :
    (inputKeys a ha s)[i]'(by simpa only [inputKeys_length] using hi) =
      ArrayMerge.slot a ha (s.base + i) (inputIndexBound s hi) := by
  calc
    _ = ArrayMerge.slot a ha (bankBase k false + (s.base + i))
        (viewBound false s.fits hi) :=
      keysAt_nth a ha false s.base s.width s.fits i hi
    _ = _ := by
      apply slot_congr_addr
      simp [bankBase]

theorem inputKeys_split {k : Nat} (a : Array Key)
    (ha : a.size = 2 * k) (s : Span k) :
    inputKeys a ha s.left ++ inputKeys a ha s.right = inputKeys a ha s := by
  have hw : s.left.width + s.right.width = s.width := by
    change s.width / 2 + (s.width - s.width / 2) = s.width
    omega
  apply List.ext_getElem
  · simpa only [List.length_append, inputKeys_length] using hw
  · intro i hi hj
    have his : i < s.width := by simpa only [inputKeys_length] using hj
    by_cases hil : i < s.left.width
    · have hidx : i < (inputKeys a ha s.left).length := by
        simpa only [inputKeys_length] using hil
      calc
        _ = (inputKeys a ha s.left)[i]'hidx := by
          simp [List.getElem_append, hidx]
        _ = _ :=
          (inputKeys_nth a ha s.left i hil).trans (inputKeys_nth a ha s i his).symm
    · have hir : i - s.left.width < s.right.width := by omega
      have hidx : i - s.left.width < (inputKeys a ha s.right).length := by
        simpa only [inputKeys_length] using hir
      calc
        _ = (inputKeys a ha s.right)[i - s.left.width]'hidx := by
          simp [List.getElem_append, inputKeys_length, hil]
        _ = ArrayMerge.slot a ha (s.right.base + (i - s.left.width))
            (inputIndexBound s.right hir) :=
          inputKeys_nth a ha s.right (i - s.left.width) hir
        _ = ArrayMerge.slot a ha (s.base + i) (inputIndexBound s his) := by
          apply slot_congr_addr
          change s.base + s.width / 2 + (i - s.width / 2) = s.base + i
          change ¬ i < s.width / 2 at hil
          omega
        _ = _ := (inputKeys_nth a ha s i his).symm

private theorem short_result_keys {k fuel : Nat} {s : Span k} {dst : Bool}
    {a : Array Key} {ha : a.size = 2 * k}
    (r : SortResult fuel s dst a ha) (hs : s.width ≤ 1) :
    r.keys = inputKeys a ha s := by
  have hle := r.count_le
  have hcount : r.count = s.width := by
    by_cases hz : s.width = 0
    · omega
    · have hp := r.count_pos (show 0 < s.width by omega)
      omega
  apply List.ext_getElem
  · simpa only [SortResult.keys, keysAt_length, inputKeys_length] using hcount
  · intro i hi hj
    have his : i < s.width := by simpa only [inputKeys_length] using hj
    have hone : s.width = 1 := by omega
    have hiz : i = 0 := by omega
    subst i
    have hc : 0 < r.count := by omega
    have hf := s.fits
    have hp : s.base + r.count ≤ k := by omega
    have hb : bankBase k dst + s.base < 2 * k := by
      cases dst <;> simp [bankBase] <;> omega
    have ha₀ : s.base < 2 * k := by omega
    calc
      _ = ArrayMerge.slot r.bank r.size_eq (bankBase k dst + (s.base + 0))
          (viewBound dst hp hc) :=
        keysAt_nth r.bank r.size_eq dst s.base r.count hp 0 hc
      _ = ArrayMerge.slot r.bank r.size_eq (bankBase k dst + s.base) hb := by
        apply slot_congr_addr
        simp only [Nat.add_zero]
      _ = ArrayMerge.slot a ha s.base ha₀ := r.leafCopy hone
      _ = ArrayMerge.slot a ha (s.base + 0) (inputIndexBound s his) := by
        apply slot_congr_addr
        simp only [Nat.add_zero]
      _ = _ := (inputKeys_nth a ha s 0 his).symm

private theorem increasing_of_length_le_one (xs : List Key)
    (h : xs.length ≤ 1) : Increasing xs := by
  cases xs with
  | nil => exact Increasing.nil
  | cons x ys =>
    cases ys with
    | nil => exact Increasing.cons (by simp) Increasing.nil
    | cons y zs =>
      simp only [List.length_cons] at h
      omega

private theorem short_result_spec {k fuel : Nat} {s : Span k} {dst : Bool}
    {a : Array Key} {ha : a.size = 2 * k}
    (r : SortResult fuel s dst a ha) (hs : s.width ≤ 1) :
    Increasing r.keys ∧ ∀ z : Key, z ∈ r.keys ↔ z ∈ inputKeys a ha s := by
  rw [short_result_keys r hs]
  exact ⟨increasing_of_length_le_one _
    (by simpa only [inputKeys_length] using hs), fun _ => Iff.rfl⟩

private theorem runSpan_leaf_spec {k : Nat} (fuel : Nat) (s : Span k)
    (dst : Bool) (a : Array Key) (ha : a.size = 2 * k)
    (hw : s.width ≤ 2 ^ fuel) (hs : s.width ≤ 1) :
    Increasing (runSpan fuel s dst a ha hw).keys ∧
      ∀ z : Key, z ∈ (runSpan fuel s dst a ha hw).keys ↔
        z ∈ inputKeys a ha s := by
  rw [runSpan_leaf fuel s dst a ha hw hs]
  exact short_result_spec _ hs

/-- The actual returned prefix is strictly increasing and has exactly the
support of the bank-zero span at entry to this call. -/
theorem runSpan_spec {k : Nat} (fuel : Nat) :
    ∀ (s : Span k) (dst : Bool) (a : Array Key) (ha : a.size = 2 * k)
      (hw : s.width ≤ 2 ^ fuel),
      Increasing (runSpan fuel s dst a ha hw).keys ∧
        ∀ z : Key, z ∈ (runSpan fuel s dst a ha hw).keys ↔
          z ∈ inputKeys a ha s := by
  induction fuel with
  | zero =>
    intro s dst a ha hw
    exact runSpan_leaf_spec 0 s dst a ha hw
      (by simpa only [Nat.pow_zero] using hw)
  | succ n ih =>
    intro s dst a ha hw
    by_cases hs : s.width ≤ 1
    · exact runSpan_leaf_spec (n + 1) s dst a ha hw hs
    · have hsplit : 1 < s.width := by omega
      let l := runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw)
      let r := runSpan n s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
      let p := forkPlan s dst l.count r.count l.count_le r.count_le
      let m := ArrayMerge.runPacked p r.bank r.size_eq
      have hl : Increasing l.keys ∧
          ∀ z : Key, z ∈ l.keys ↔ z ∈ inputKeys a ha s.left :=
        ih s.left (!dst) a ha (leftBudget (n := n) s hw)
      have hr : Increasing r.keys ∧
          ∀ z : Key, z ∈ r.keys ↔ z ∈ inputKeys l.bank l.size_eq s.right :=
        ih s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
      -- The frame equations preserve the left output and the pending right input.
      have hreads :
          ArrayMergeExact.leftSlice p r.bank r.size_eq = l.keys ∧
          ArrayMergeExact.rightSlice p r.bank r.size_eq = r.keys ∧
          inputKeys l.bank l.size_eq s.right = inputKeys a ha s.right :=
        runSpan_fork_reads n s dst a ha hw
      obtain ⟨hreadL, hreadR, hpending⟩ := hreads
      have hil : Increasing (ArrayMergeExact.leftSlice p r.bank r.size_eq) := by
        simpa only [hreadL] using hl.1
      have hir : Increasing (ArrayMergeExact.rightSlice p r.bank r.size_eq) := by
        simpa only [hreadR] using hr.1
      obtain ⟨_, _, t⟩ := ArrayMergeExact.runPacked_exact p r.bank r.size_eq hil hir
      have hc : m.count ≤ s.width := t.fits
      have hf : s.base + m.count ≤ k := by
        have hfit := s.fits
        omega
      have hout : (runSpan (n + 1) s dst a ha hw).keys =
          keysAt m.bank m.size_eq dst s.base m.count hf :=
        runSpan_fork_keys n s dst a ha hw hsplit
      have hmerge : keysAt m.bank m.size_eq dst s.base m.count hf =
          (merge (ArrayMergeExact.leftSlice p r.bank r.size_eq)
            (ArrayMergeExact.rightSlice p r.bank r.size_eq)).keys :=
        trace_output_keysAt t r.size_eq m.size_eq dst rfl hf
      rw [hout, hmerge, hreadL, hreadR]
      have hm := merge_spec hl.1 hr.1
      refine ⟨hm.increasing, ?_⟩
      intro z
      rw [hm.mem_iff z, hl.2 z, hr.2 z, hpending, ← inputKeys_split a ha s]
      exact List.mem_append.symm

/-- At the root the input span comprises all `k` physical slots of bank zero. -/
theorem runPacked_spec (k : Nat) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) :
    Increasing (runPacked k dst a ha).keys ∧
      ∀ z : Key, z ∈ (runPacked k dst a ha).keys ↔
        z ∈ keysAt a ha false 0 k (by simp) :=
  runSpan_spec (ceilBinaryLog k) (Span.root k) dst a ha (Frame.root k).width_budget

end PaperB.PairDictionary.FixedBank
