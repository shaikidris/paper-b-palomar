module

public import PaperB.ForestArrayMerge
public import PaperB.PairDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open PaperB.PairLookup.KeyMerge.Workspace (Span Frame)

namespace PaperB.PairDictionary.FixedBank

@[inline] def bankBase (k : Nat) (bank : Bool) : Nat :=
  if bank then k else 0

def InBank {k : Nat} (s : Span k) (bank : Bool) (q : Nat) : Prop :=
  bankBase k bank + s.base ≤ q ∧
    q < bankBase k bank + s.base + s.width

def InSpan {k : Nat} (s : Span k) (q : Nat) : Prop :=
  InBank s false q ∨ InBank s true q

private theorem inSpan_of_inBank {k : Nat} {s : Span k} {b : Bool}
    {q : Nat} (h : InBank s b q) : InSpan s q := by
  cases b
  · exact Or.inl h
  · exact Or.inr h

private theorem inSpan_mono {k : Nat} {s t : Span k} {q : Nat}
    (hbase : s.base ≤ t.base)
    (hend : t.base + t.width ≤ s.base + s.width)
    (h : InSpan t q) : InSpan s q := by
  have lift : ∀ b : Bool, InBank t b q → InBank s b q := by
    intro b hb
    unfold InBank at hb ⊢
    omega
  rcases h with h | h
  · exact Or.inl (lift false h)
  · exact Or.inr (lift true h)

private theorem left_inSpan {k : Nat} (s : Span k) {q : Nat}
    (h : InSpan s.left q) : InSpan s q :=
  inSpan_mono (s := s) (t := s.left) (Nat.le_refl s.base)
    (by
      change s.base + s.width / 2 ≤ s.base + s.width
      omega) h

private theorem right_inSpan {k : Nat} (s : Span k) {q : Nat}
    (h : InSpan s.right q) : InSpan s q :=
  inSpan_mono (s := s) (t := s.right)
    (by
      change s.base ≤ s.base + s.width / 2
      omega)
    (by
      change s.base + s.width / 2 + (s.width - s.width / 2) ≤
        s.base + s.width
      omega) h

theorem right_input_outside_left {k : Nat} (s : Span k) {q : Nat}
    (h : InBank s.right false q) : ¬ InSpan s.left q := by
  have hf := s.fits
  simp [InBank, bankBase] at h
  change s.base + s.width / 2 ≤ q ∧
    q < s.base + s.width / 2 + (s.width - s.width / 2) at h
  intro hleft
  rcases hleft with hleft | hleft
  · simp [InBank, bankBase] at hleft
    change s.base ≤ q ∧ q < s.base + s.width / 2 at hleft
    omega
  · simp [InBank, bankBase] at hleft
    change k + s.base ≤ q ∧ q < k + s.base + s.width / 2 at hleft
    omega

theorem left_output_outside_right {k : Nat} (s : Span k) {b : Bool}
    {q : Nat} (h : InBank s.left b q) : ¬ InSpan s.right q := by
  have hf := s.fits
  change bankBase k b + s.base ≤ q ∧
    q < bankBase k b + s.base + s.width / 2 at h
  have rightBounds (d : Bool) (hd : InBank s.right d q) :
      bankBase k d + (s.base + s.width / 2) ≤ q ∧
        q < bankBase k d + (s.base + s.width / 2) +
          (s.width - s.width / 2) := hd
  intro hr
  rcases hr with hr | hr
  · have hq := rightBounds false hr
    cases b <;> simp [bankBase] at h hq <;> omega
  · have hq := rightBounds true hr
    cases b <;> simp [bankBase] at h hq <;> omega

private theorem inputBound {k : Nat} (s : Span k) (h : 0 < s.width) :
    s.base < 2 * k := by
  have hf := s.fits
  omega

private theorem outputBound {k : Nat} (s : Span k) (dst : Bool)
    (h : 0 < s.width) : bankBase k dst + s.base < 2 * k := by
  have hf := s.fits
  cases dst <;> simp [bankBase] <;> omega

private theorem dstAddr_eq {k : Nat} (p : ArrayMerge.Plan k)
    (dst : Bool) (h : p.source = !dst) (v : Nat) :
    p.dstAddr v = bankBase k dst + (p.outBase + v) := by
  cases dst <;> simp [ArrayMerge.Plan.dstAddr, bankBase, h]

/-- Peak live frames; sibling calls execute sequentially. -/
inductive Calls {k : Nat} : Nat → Span k → Nat → Prop where
  | leaf {fuel : Nat} {s : Span k} (h : s.width ≤ 1) :
      Calls fuel s 1
  | fork {fuel : Nat} {s : Span k} {l r : Nat} (h : 1 < s.width) :
      Calls fuel s.left l → Calls fuel s.right r →
      Calls (fuel + 1) s (max l r + 1)

theorem Calls.peak_le {k fuel peak : Nat} {s : Span k}
    (h : Calls fuel s peak) : peak ≤ fuel + 1 := by
  induction h with
  | leaf _ => omega
  | fork _ _ _ ihl ihr =>
    simp only [Nat.max_def] <;> split <;> omega

structure SortResult {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (orig : Array Key) (hOrig : orig.size = 2 * k) where
  bank : Array Key
  count : Nat
  size_eq : bank.size = 2 * k
  count_le : count ≤ s.width
  count_pos : 0 < s.width → 0 < count
  leafCopy : ∀ h : s.width = 1,
    ArrayMerge.slot bank size_eq (bankBase k dst + s.base)
        (outputBound s dst (by omega)) =
      ArrayMerge.slot orig hOrig s.base (inputBound s (by omega))
  frame : ∀ (q : Nat) (hq : q < 2 * k), ¬ InSpan s q →
    ArrayMerge.slot bank size_eq q hq = ArrayMerge.slot orig hOrig q hq
  calls : ∃ peak : Nat, Calls fuel s peak

theorem SortResult.count_eq_zero_iff {k fuel : Nat} {s : Span k}
    {dst : Bool} {a : Array Key} {ha : a.size = 2 * k}
    (r : SortResult fuel s dst a ha) : r.count = 0 ↔ s.width = 0 := by
  constructor
  · intro hc
    by_cases hw : s.width = 0
    · exact hw
    · have hp := r.count_pos (by omega)
      omega
  · intro hw
    have hc := r.count_le
    omega

theorem SortResult.pendingRight {k fuel : Nat} {s : Span k} {dst : Bool}
    {a : Array Key} {ha : a.size = 2 * k}
    (l : SortResult fuel s.left dst a ha)
    (q : Nat) (hq : q < 2 * k) (h : InBank s.right false q) :
    ArrayMerge.slot l.bank l.size_eq q hq = ArrayMerge.slot a ha q hq :=
  l.frame q hq (right_input_outside_left s h)

private def runLeaf {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 1) :
    SortResult fuel s dst a ha :=
  if hp : 0 < s.width then
    let j : Nat := bankBase k dst + s.base
    have hj : j < 2 * k := outputBound s dst hp
    have hjA : j < a.size := by omega
    let x : Key := ArrayMerge.slot a ha s.base (inputBound s hp)
    let b : Array Key := a.set j x hjA
    have hb : b.size = 2 * k := by simpa [b] using ha
    { bank := b
      count := 1
      size_eq := hb
      count_le := by omega
      count_pos := fun _ => Nat.zero_lt_succ 0
      leafCopy := by
        intro _
        change b[j]'(by omega) = x
        first
        | simpa [b]
        | simp [b, Array.getElem_set]
      frame := by
        intro q hq avoid
        have hin : InBank s dst j := by
          change j ≤ j ∧ j < j + s.width
          omega
        have hne : j ≠ q := by
          intro e
          exact avoid (inSpan_of_inBank (e ▸ hin))
        change b[q]'(by omega) = a[q]'(by omega)
        first
        | simpa [b, hne, Ne.symm hne]
        | simp [b, Array.getElem_set, hne, Ne.symm hne]
      calls := ⟨1, Calls.leaf hw⟩ }
  else
    { bank := a
      count := 0
      size_eq := ha
      count_le := Nat.zero_le _
      count_pos := by intro h; exact False.elim (hp h)
      leafCopy := by intro h; omega
      frame := by intro _ _ _; rfl
      calls := ⟨1, Calls.leaf hw⟩ }

theorem leftBudget {k n : Nat} (s : Span k)
    (hw : s.width ≤ 2 ^ (n + 1)) : s.left.width ≤ 2 ^ n := by
  have hp : s.width ≤ 2 ^ n * 2 := by
    simpa only [Nat.pow_succ] using hw
  change s.width / 2 ≤ 2 ^ n
  omega

theorem rightBudget {k n : Nat} (s : Span k)
    (hw : s.width ≤ 2 ^ (n + 1)) : s.right.width ≤ 2 ^ n := by
  have hp : s.width ≤ 2 ^ n * 2 := by
    simpa only [Nat.pow_succ] using hw
  change s.width - s.width / 2 ≤ 2 ^ n
  omega

@[inline] def forkPlan {k : Nat} (s : Span k) (dst : Bool)
    (lc rc : Nat) (hl : lc ≤ s.left.width) (hr : rc ≤ s.right.width) :
    ArrayMerge.Plan k :=
  have hL : lc ≤ s.width / 2 := hl
  have hR : rc ≤ s.width - s.width / 2 := hr
  { source := !dst
    leftBase := s.base
    leftLen := lc
    rightBase := s.base + s.width / 2
    rightLen := rc
    outBase := s.base
    outWidth := s.width
    separated := by omega
    rightFits := by
      have hf := s.fits
      omega
    outFits := s.fits
    room := by omega }

private theorem packedCountLe {k : Nat} (p : ArrayMerge.Plan k)
    (a : Array Key) (ha : a.size = 2 * k) :
    (ArrayMerge.runPacked p a ha).count ≤ p.outWidth := by
  obtain ⟨_, _, _, _, _, hfit, _⟩ := (ArrayMerge.runPacked p a ha).certified
  exact hfit

private theorem packedFrame {k : Nat} (p : ArrayMerge.Plan k)
    (a : Array Key) (ha : a.size = 2 * k)
    (q : Nat) (hq : q < 2 * k)
    (avoid : ∀ v : Nat, v < (ArrayMerge.runPacked p a ha).count →
      p.dstAddr v ≠ q) :
    let m := ArrayMerge.runPacked p a ha
    ArrayMerge.slot m.bank m.size_eq q hq = ArrayMerge.slot a ha q hq := by
  obtain ⟨_, _, _, t, _⟩ := (ArrayMerge.runPacked p a ha).certified
  exact t.frame ha q hq avoid

/-- The left result is destructured before running the right child.
The logical slice views below are not part of this recursion. -/
def runSpan {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ fuel) :
    SortResult fuel s dst a ha :=
  match fuel with
  | 0 =>
    runLeaf 0 s dst a ha (by simpa using hw)
  | n + 1 =>
    if hs : s.width ≤ 1 then
      runLeaf (n + 1) s dst a ha hs
    else
      have hsplit : 1 < s.width := by omega
      let ⟨lb, lc, hlb, hlc, hlpos, _, hlframe, hlcalls⟩ :=
        runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw)
      let ⟨rb, rc, hrb, hrc, _, _, hrframe, hrcalls⟩ :=
        runSpan n s.right (!dst) lb hlb (rightBudget (n := n) s hw)
      let p := forkPlan s dst lc rc hlc hrc
      let m := ArrayMerge.runPacked p rb hrb
      { bank := m.bank
        count := m.count
        size_eq := m.size_eq
        count_le := packedCountLe p rb hrb
        count_pos := by
          intro _
          have hwLpos : 0 < s.left.width := by
            change 0 < s.width / 2
            omega
          have hl : 0 < lc := hlpos hwLpos
          obtain ⟨_, _, _, _, _, _, _, hcharge, _⟩ := m.certified
          change lc + rc ≤ 2 * m.count at hcharge
          omega
        leafCopy := by intro h; omega
        frame := by
          intro q hq avoid
          have hm : ArrayMerge.slot m.bank m.size_eq q hq =
              ArrayMerge.slot rb hrb q hq := by
            apply packedFrame p rb hrb q hq
            intro v hv he
            change v < m.count at hv
            have hc : m.count ≤ s.width := packedCountLe p rb hrb
            have hd : p.dstAddr v = bankBase k dst + (s.base + v) :=
              dstAddr_eq p dst rfl v
            apply avoid
            apply inSpan_of_inBank (b := dst)
            unfold InBank
            omega
          exact hm.trans
            ((hrframe q hq (fun h => avoid (right_inSpan s h))).trans
              (hlframe q hq (fun h => avoid (left_inSpan s h))))
        calls := by
          obtain ⟨lp, hLcalls⟩ := hlcalls
          obtain ⟨rp, hRcalls⟩ := hrcalls
          exact ⟨max lp rp + 1, Calls.fork hsplit hLcalls hRcalls⟩ }
termination_by structural fuel

def runPacked (k : Nat) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) :
    SortResult (ceilBinaryLog k) (Span.root k) dst a ha :=
  runSpan (ceilBinaryLog k) (Span.root k) dst a ha (Frame.root k).width_budget

theorem runPacked_live_frames (k : Nat) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) :
    ∃ peak : Nat, Calls (ceilBinaryLog k) (Span.root k) peak ∧
      peak ≤ ceilBinaryLog k + 1 := by
  obtain ⟨peak, h⟩ := (runPacked k dst a ha).calls
  exact ⟨peak, h, h.peak_le⟩

theorem runSpan_leaf {k : Nat} (fuel : Nat) (s : Span k) (dst : Bool)
    (a : Array Key) (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ fuel)
    (hs : s.width ≤ 1) :
    runSpan fuel s dst a ha hw = runLeaf fuel s dst a ha hs := by
  cases fuel <;> simp [runSpan, hs]

universe u

/-- Proof-only fork equation for the actual recursion. The observer may
depend on both the backing array and the exact returned count. -/
theorem runSpan_fork_observe {k : Nat} {α : Sort u}
    (n : Nat) (s : Span k) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ (n + 1))
    (hs : 1 < s.width)
    (observe : (b : Array Key) → b.size = 2 * k →
      (c : Nat) → c ≤ s.width → α) :
    let l := runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw)
    let r := runSpan n s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
    let p := forkPlan s dst l.count r.count l.count_le r.count_le
    let m := ArrayMerge.runPacked p r.bank r.size_eq
    let out := runSpan (n + 1) s dst a ha hw
    observe out.bank out.size_eq out.count out.count_le =
      observe m.bank m.size_eq m.count (packedCountLe p r.bank r.size_eq) := by
  have hn : ¬ s.width ≤ 1 := by omega
  dsimp only
  simp only [runSpan, dif_neg hn] <;>
    (first
    | rfl
    | generalize runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw) = l
      cases l with
      | mk lb lc hlb hlc hlpos hlleaf hlframe hlcalls =>
        try dsimp only
        first
        | rfl
        | generalize
            runSpan n s.right (!dst) lb hlb (rightBudget (n := n) s hw) = r
          cases r <;> rfl)

private theorem prefixFits {k : Nat} (s : Span k) {c : Nat}
    (hc : c ≤ s.width) : s.base + c ≤ k := by
  have hf := s.fits
  omega

private theorem prefixBound {k base len i : Nat} (b : Bool)
    (hf : base + len ≤ k) (hi : i < len) :
    bankBase k b + (base + i) < 2 * k := by
  cases b <;> simp [bankBase] <;> omega

/-- A specification view, used only to state and prove read equations. -/
noncomputable def keysAt {k : Nat} (a : Array Key) (ha : a.size = 2 * k)
    (b : Bool) (base len : Nat) (hf : base + len ≤ k) : List Key :=
  List.ofFn fun i : Fin len =>
    ArrayMerge.slot a ha (bankBase k b + (base + i.val)) (prefixBound b hf i.isLt)

noncomputable def SortResult.keys {k fuel : Nat} {s : Span k} {dst : Bool}
    {a : Array Key} {ha : a.size = 2 * k}
    (r : SortResult fuel s dst a ha) : List Key :=
  keysAt r.bank r.size_eq dst s.base r.count (prefixFits s r.count_le)

theorem SortResult.keysAt_eq_of_frame {k fuel : Nat} {s : Span k}
    {dst : Bool} {a : Array Key} {ha : a.size = 2 * k}
    (r : SortResult fuel s dst a ha) (b : Bool) (base len : Nat)
    (hf : base + len ≤ k)
    (avoid : ∀ i : Nat, i < len → ¬ InSpan s (bankBase k b + (base + i))) :
    keysAt r.bank r.size_eq b base len hf = keysAt a ha b base len hf := by
  unfold keysAt
  apply congrArg (fun f : Fin len → Key => List.ofFn f)
  funext i
  exact r.frame _ (prefixBound b hf i.isLt) (avoid i.val i.isLt)

theorem SortResult.leftKeysPreserved {k fuel : Nat} {s : Span k} {b : Bool}
    {a : Array Key} {ha : a.size = 2 * k}
    (l : SortResult fuel s.left b a ha)
    (r : SortResult fuel s.right b l.bank l.size_eq) :
    keysAt r.bank r.size_eq b s.left.base l.count (prefixFits s.left l.count_le) =
      l.keys := by
  unfold SortResult.keys
  apply r.keysAt_eq_of_frame
  intro i hi
  apply left_output_outside_right s (b := b)
  have hc := l.count_le
  change l.count ≤ s.width / 2 at hc
  change bankBase k b + s.base ≤ bankBase k b + (s.base + i) ∧
    bankBase k b + (s.base + i) < bankBase k b + s.base + s.width / 2
  omega

/-- Both source prefixes in the fork plan are exactly the child outputs.
The third equation preserves the pending bank-zero input before the right call. -/
theorem runSpan_fork_reads {k : Nat}
    (n : Nat) (s : Span k) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ (n + 1)) :
    let l := runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw)
    let r := runSpan n s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
    let p := forkPlan s dst l.count r.count l.count_le r.count_le
    keysAt r.bank r.size_eq p.source p.leftBase p.leftLen
        (by
          have hsep := p.separated
          have hfit := p.rightFits
          omega) = l.keys ∧
      keysAt r.bank r.size_eq p.source p.rightBase p.rightLen p.rightFits = r.keys ∧
      keysAt l.bank l.size_eq false s.right.base s.right.width s.right.fits =
        keysAt a ha false s.right.base s.right.width s.right.fits := by
  dsimp only
  refine ⟨?_, rfl, ?_⟩
  · exact SortResult.leftKeysPreserved (s := s) _ _
  · apply SortResult.keysAt_eq_of_frame
    intro i hi
    apply right_input_outside_left s
    simp [InBank, bankBase] <;> omega

/-- The actual sort's key-prefix recurrence, stopping at the packed-merge
boundary. `runSpan_fork_reads` identifies the two input views at that boundary. -/
theorem runSpan_fork_keys {k : Nat}
    (n : Nat) (s : Span k) (dst : Bool) (a : Array Key)
    (ha : a.size = 2 * k) (hw : s.width ≤ 2 ^ (n + 1))
    (hs : 1 < s.width) :
    let l := runSpan n s.left (!dst) a ha (leftBudget (n := n) s hw)
    let r := runSpan n s.right (!dst) l.bank l.size_eq (rightBudget (n := n) s hw)
    let p := forkPlan s dst l.count r.count l.count_le r.count_le
    let m := ArrayMerge.runPacked p r.bank r.size_eq
    (runSpan (n + 1) s dst a ha hw).keys =
      keysAt m.bank m.size_eq dst s.base m.count
        (prefixFits s (packedCountLe p r.bank r.size_eq)) :=
  runSpan_fork_observe n s dst a ha hw hs
    (fun b hb c hc => keysAt b hb dst s.base c (prefixFits s hc))


end PaperB.PairDictionary.FixedBank
