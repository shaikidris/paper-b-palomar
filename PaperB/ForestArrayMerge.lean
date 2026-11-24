module

public import PaperB.PairDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
The reusable first module: an executable two-bank cursor merge and an exact
trace of its reads, comparisons, cursor advances, and writes. The trace
certifies the destination prefix and preservation of the input bank. This
module does not prove the separate refinement to `KeyMerge.merge`.

The executable loop never constructs the trace or its list of emitted keys.
Pass the backing array with exclusive ownership to get in-place `Array.set`;
retaining an alias can cause Lean's copy-on-write implementation to copy the
backing array. The cost theorem counts key operations, not that copy or the
bit complexity of comparing `Nat` keys.
-/

namespace PaperB.PairDictionary.ArrayMerge

open PaperB.PairLookup PaperB.PairLookup.KeyMerge

structure Plan (k : Nat) where
  source : Bool
  leftBase : Nat
  leftLen : Nat
  rightBase : Nat
  rightLen : Nat
  outBase : Nat
  outWidth : Nat
  separated : leftBase + leftLen ≤ rightBase
  rightFits : rightBase + rightLen ≤ k
  outFits : outBase + outWidth ≤ k
  room : leftLen + rightLen ≤ outWidth

@[inline] def Plan.srcAddr {k : Nat} (p : Plan k) (q : Nat) : Nat :=
  (if p.source then k else 0) + q

@[inline] def Plan.dstAddr {k : Nat} (p : Plan k) (w : Nat) : Nat :=
  (if p.source then 0 else k) + (p.outBase + w)

theorem Plan.srcBound {k : Nat} (p : Plan k) {q : Nat} (h : q < k) :
    p.srcAddr q < 2 * k := by
  cases e : p.source <;> simp [Plan.srcAddr, e] <;> omega

theorem Plan.dstBound {k : Nat} (p : Plan k) {w : Nat}
    (h : w < p.outWidth) : p.dstAddr w < 2 * k := by
  have hf := p.outFits
  cases e : p.source <;> simp [Plan.dstAddr, e] <;> omega

theorem Plan.banksDisjoint {k : Nat} (p : Plan k) {w q : Nat}
    (hw : w < p.outWidth) (hq : q < k) :
    p.dstAddr w ≠ p.srcAddr q := by
  have hf := p.outFits
  cases e : p.source <;> simp [Plan.dstAddr, Plan.srcAddr, e] <;> omega

@[inline] def slot {k : Nat} (a : Array Key) (ha : a.size = 2 * k)
    (q : Nat) (hq : q < 2 * k) : Key :=
  a[q]'(by omega)

@[inline] def readLeft {k : Nat} (p : Plan k) (a : Array Key)
    (ha : a.size = 2 * k) (i : Nat) (hi : i < p.leftLen) : Key :=
  slot a ha (p.srcAddr (p.leftBase + i)) (p.srcBound (by
    have hs := p.separated
    have hf := p.rightFits
    omega))

@[inline] def readRight {k : Nat} (p : Plan k) (a : Array Key)
    (ha : a.size = 2 * k) (j : Nat) (hj : j < p.rightLen) : Key :=
  slot a ha (p.srcAddr (p.rightBase + j)) (p.srcBound (by
    have hf := p.rightFits
    omega))

@[inline] def put {k : Nat} (p : Plan k) (a : Array Key)
    (ha : a.size = 2 * k) (w : Nat) (hw : w < p.outWidth)
    (x : Key) : Array Key :=
  a.set (p.dstAddr w) x (by
    have h := p.dstBound hw
    omega)

/-- Next cursors, emitted key, number of head reads, and number of
`lexLess` calls. The one-sided cases copy without comparing. -/
inductive Choice {k : Nat} (p : Plan k) (a : Array Key)
    (ha : a.size = 2 * k) (i j : Nat) :
    Nat → Nat → Key → Nat → Nat → Prop where
  | leftOnly (hi : i < p.leftLen) (hj : j = p.rightLen) :
      Choice p a ha i j (i + 1) j (readLeft p a ha i hi) 1 0
  | rightOnly (hi : i = p.leftLen) (hj : j < p.rightLen) :
      Choice p a ha i j i (j + 1) (readRight p a ha j hj) 1 0
  | leftFirst (hi : i < p.leftLen) (hj : j < p.rightLen)
      (h : lexLess (readLeft p a ha i hi) (readRight p a ha j hj)) :
      Choice p a ha i j (i + 1) j (readLeft p a ha i hi) 2 1
  | rightFirst (hi : i < p.leftLen) (hj : j < p.rightLen)
      (h₁ : ¬ lexLess (readLeft p a ha i hi) (readRight p a ha j hj))
      (h₂ : lexLess (readRight p a ha j hj) (readLeft p a ha i hi)) :
      Choice p a ha i j i (j + 1) (readRight p a ha j hj) 2 2
  | tie (hi : i < p.leftLen) (hj : j < p.rightLen)
      (h₁ : ¬ lexLess (readLeft p a ha i hi) (readRight p a ha j hj))
      (h₂ : ¬ lexLess (readRight p a ha j hj) (readLeft p a ha i hi)) :
      Choice p a ha i j (i + 1) (j + 1) (readLeft p a ha i hi) 2 2

theorem eq_of_neither_less {x y : Key}
    (hxy : ¬ lexLess x y) (hyx : ¬ lexLess y x) : x = y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  simp only [lexLess, Prod.fst, Prod.snd] at hxy hyx
  have h₁ : a = c := by omega
  have h₂ : b = d := by omega
  exact Prod.ext h₁ h₂

theorem Choice.bounds {k : Nat} {p : Plan k} {a : Array Key}
    {ha : a.size = 2 * k} {i j i' j' : Nat} {x : Key} {r c : Nat}
    (s : Choice p a ha i j i' j' x r c) :
    i' ≤ p.leftLen ∧ j' ≤ p.rightLen ∧
      i + j + 1 ≤ i' + j' ∧ i' + j' ≤ i + j + 2 ∧
      r ≤ 2 ∧ c ≤ 2 := by
  cases s <;> exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

structure Step {k : Nat} (p : Plan k)
    (a : Array Key) (i j w : Nat) (b : Array Key) (i' j' w' : Nat)
    (x : Key) (r c : Nat) : Prop where
  size_eq : a.size = 2 * k
  room : w < p.outWidth
  choice : Choice p a size_eq i j i' j' x r c
  store : b = put p a size_eq w room x
  advance : w' = w + 1

theorem Step.afterSize {k : Nat} {p : Plan k} {a b : Array Key}
    {i j w i' j' w' : Nat} {x : Key} {r c : Nat}
    (s : Step p a i j w b i' j' w' x r c) : b.size = 2 * k := by
  rw [s.store]
  simp [put, s.size_eq]

theorem Step.getWritten {k : Nat} {p : Plan k} {a b : Array Key}
    {i j w i' j' w' : Nat} {x : Key} {r c : Nat}
    (s : Step p a i j w b i' j' w' x r c) :
    slot b s.afterSize (p.dstAddr w) (p.dstBound s.room) = x := by
  rcases s with ⟨ha, hw, _, rfl, _⟩
  simp [slot, put, Array.getElem_set]

theorem Step.getOther {k : Nat} {p : Plan k} {a b : Array Key}
    {i j w i' j' w' : Nat} {x : Key} {r c : Nat}
    (s : Step p a i j w b i' j' w' x r c)
    (q : Nat) (hq : q < 2 * k) (hne : p.dstAddr w ≠ q) :
    slot b s.afterSize q hq = slot a s.size_eq q hq := by
  rcases s with ⟨ha, hw, _, rfl, _⟩
  simp [slot, put, Array.getElem_set, hne, Ne.symm hne]

/-- `xs` lists the writes in destination order. `r` and `c` count reads
and comparisons respectively; the write count is the destination cursor. -/
inductive Trace {k : Nat} (p : Plan k) (orig : Array Key) :
    Array Key → Nat → Nat → Nat → List Key → Nat → Nat → Prop where
  | nil : Trace p orig orig 0 0 0 [] 0 0
  | snoc {a b : Array Key} {i j w i' j' w' : Nat}
      {xs : List Key} {r c dr dc : Nat} {x : Key} :
      Trace p orig a i j w xs r c →
      Step p a i j w b i' j' w' x dr dc →
      Trace p orig b i' j' w' (xs ++ [x]) (r + dr) (c + dc)

theorem Trace.capacity {k : Nat} {p : Plan k} {orig a : Array Key}
    {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : Trace p orig a i j w xs r c) (h : orig.size = 2 * k) :
    a.size = 2 * k := by
  cases t with
  | nil => exact h
  | snoc _ s => exact s.afterSize

theorem Trace.fits {k : Nat} {p : Plan k} {orig a : Array Key}
    {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : Trace p orig a i j w xs r c) : w ≤ p.outWidth := by
  cases t with
  | nil => exact Nat.zero_le _
  | snoc _ s =>
    have h₁ := s.room
    have h₂ := s.advance
    omega

theorem Trace.accounting {k : Nat} {p : Plan k} {orig a : Array Key}
    {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : Trace p orig a i j w xs r c) :
    xs.length = w ∧ r ≤ 2 * w ∧ c ≤ 2 * w ∧
      w ≤ i + j ∧ i + j ≤ 2 * w := by
  induction t with
  | nil => simp
  | snoc _ s ih =>
    obtain ⟨hlen, hr, hc, hlow, hhigh⟩ := ih
    obtain ⟨_, _, hlo, hhi, hdr, hdc⟩ := s.choice.bounds
    have hw := s.advance
    simp only [List.length_append, List.length_cons, List.length_nil]
    exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- No slot outside the written destination prefix has changed. -/
theorem Trace.frame {k : Nat} {p : Plan k} {orig a : Array Key}
    {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : Trace p orig a i j w xs r c) (h : orig.size = 2 * k)
    (q : Nat) (hq : q < 2 * k) :
    (∀ v, v < w → p.dstAddr v ≠ q) →
      slot a (t.capacity h) q hq = slot orig h q hq := by
  induction t with
  | nil =>
    intro _
    rfl
  | snoc _ s ih =>
    intro avoid
    have hw := s.advance
    exact (s.getOther q hq (avoid _ (by omega))).trans
      (ih (fun v hv => avoid v (by omega)))

/-- This applies to every intermediate trace as well as to the final one,
so every head read is from the original input bank. -/
theorem Trace.sourceUnchanged {k : Nat} {p : Plan k} {orig a : Array Key}
    {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : Trace p orig a i j w xs r c) (h : orig.size = 2 * k)
    (q : Nat) (hq : q < k) :
    slot a (t.capacity h) (p.srcAddr q) (p.srcBound hq) =
      slot orig h (p.srcAddr q) (p.srcBound hq) := by
  have hw := t.fits
  exact t.frame h _ _ (fun v hv => p.banksDisjoint (by omega) hq)

/-- Exact contents of the destination prefix, indexed in write order. -/
theorem Trace.output {k : Nat} {p : Plan k} {orig a : Array Key}
    {i j w : Nat} {xs : List Key} {r c : Nat}
    (t : Trace p orig a i j w xs r c) (h : orig.size = 2 * k) :
    ∀ (q : Nat) (hq : q < xs.length), ∃ hw : q < p.outWidth,
      slot a (t.capacity h) (p.dstAddr q) (p.dstBound hw) = xs[q]'hq := by
  induction t with
  | nil =>
    intro q hq
    simp at hq
  | @snoc a b i j w i' j' w' xs r c dr dc x prev s ih =>
    intro q hq
    have hlen := prev.accounting.1
    by_cases lt : q < xs.length
    · obtain ⟨hw, he⟩ := ih q lt
      have hne : p.dstAddr w ≠ p.dstAddr q := by
        unfold Plan.dstAddr
        omega
      refine ⟨hw, (s.getOther _ _ hne).trans (he.trans ?_)⟩
      simp [List.getElem_append, lt]
    · have hq' : q = xs.length := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hq
        omega
      subst q
      subst w
      refine ⟨s.room, s.getWritten.trans ?_⟩
      simp [List.getElem_append]

private structure Good {k : Nat} (p : Plan k) (a : Array Key)
    (i j w fuel : Nat) : Prop where
  size_eq : a.size = 2 * k
  left_le : i ≤ p.leftLen
  right_le : j ≤ p.rightLen
  count_le : w ≤ i + j
  fuel_le : p.leftLen + p.rightLen ≤ i + j + fuel

private theorem Good.next {k : Nat} {p : Plan k} {a b : Array Key}
    {i j w i' j' w' f : Nat} {x : Key} {r c : Nat}
    (g : Good p a i j w (f + 1))
    (s : Step p a i j w b i' j' w' x r c) :
    Good p b i' j' w' f := by
  obtain ⟨hi, hj, hlo, _, _, _⟩ := s.choice.bounds
  have hw := s.advance
  have hg := g.count_le
  have hf := g.fuel_le
  exact ⟨s.afterSize, hi, hj, by omega, by omega⟩

private theorem Good.canWrite {k : Nat} {p : Plan k} {a : Array Key}
    {i j w f : Nat} (g : Good p a i j w f)
    (h : i < p.leftLen ∨ j < p.rightLen) : w < p.outWidth := by
  have hi := g.left_le
  have hj := g.right_le
  have hw := g.count_le
  have hr := p.room
  omega

private structure End {k : Nat} (p : Plan k)
    (P : Array Key → Nat → Nat → Nat → Prop) where
  bank : Array Key
  count : Nat
  size_eq : bank.size = 2 * k
  invariant : P bank p.leftLen p.rightLen count

private def finish {k : Nat} {p : Plan k}
    {P : Array Key → Nat → Nat → Nat → Prop}
    (a : Array Key) (i j w : Nat) (ha : a.size = 2 * k)
    (hi : i = p.leftLen) (hj : j = p.rightLen) (hp : P a i j w) :
    End p P :=
  ⟨a, w, ha, by simpa only [hi, hj] using hp⟩

private def loop {k : Nat} (p : Plan k)
    (P : Array Key → Nat → Nat → Nat → Prop)
    (extend : ∀ {a i j w b i' j' w' x r c},
      P a i j w → Step p a i j w b i' j' w' x r c → P b i' j' w') :
    (fuel : Nat) → (a : Array Key) → (i j w : Nat) →
      Good p a i j w fuel → P a i j w → End p P
  | 0, a, i, j, w, g, hp =>
    have hi := g.left_le
    have hj := g.right_le
    have hf := g.fuel_le
    finish a i j w g.size_eq (by omega) (by omega) hp
  | f + 1, a, i, j, w, g, hp =>
    if hi : i < p.leftLen then
      let x := readLeft p a g.size_eq i hi
      have hw := g.canWrite (Or.inl hi)
      if hj : j < p.rightLen then
        let y := readRight p a g.size_eq j hj
        if hxy : lexLess x y then
          let b := put p a g.size_eq w hw x
          have s : Step p a i j w b (i + 1) j (w + 1) x 2 1 :=
            ⟨g.size_eq, hw, .leftFirst hi hj hxy, rfl, rfl⟩
          loop p P extend f b (i + 1) j (w + 1) (g.next s) (extend hp s)
        else if hyx : lexLess y x then
          let b := put p a g.size_eq w hw y
          have s : Step p a i j w b i (j + 1) (w + 1) y 2 2 :=
            ⟨g.size_eq, hw, .rightFirst hi hj hxy hyx, rfl, rfl⟩
          loop p P extend f b i (j + 1) (w + 1) (g.next s) (extend hp s)
        else
          let b := put p a g.size_eq w hw x
          have s : Step p a i j w b (i + 1) (j + 1) (w + 1) x 2 2 :=
            ⟨g.size_eq, hw, .tie hi hj hxy hyx, rfl, rfl⟩
          loop p P extend f b (i + 1) (j + 1) (w + 1) (g.next s) (extend hp s)
      else
        have ej : j = p.rightLen := by have h := g.right_le; omega
        let b := put p a g.size_eq w hw x
        have s : Step p a i j w b (i + 1) j (w + 1) x 1 0 :=
          ⟨g.size_eq, hw, .leftOnly hi ej, rfl, rfl⟩
        loop p P extend f b (i + 1) j (w + 1) (g.next s) (extend hp s)
    else
      have ei : i = p.leftLen := by have h := g.left_le; omega
      if hj : j < p.rightLen then
        let y := readRight p a g.size_eq j hj
        have hw := g.canWrite (Or.inr hj)
        let b := put p a g.size_eq w hw y
        have s : Step p a i j w b i (j + 1) (w + 1) y 1 0 :=
          ⟨g.size_eq, hw, .rightOnly ei hj, rfl, rfl⟩
        loop p P extend f b i (j + 1) (w + 1) (g.next s) (extend hp s)
      else
        have ej : j = p.rightLen := by have h := g.right_le; omega
        finish a i j w g.size_eq ei ej hp
termination_by structural fuel => fuel


structure Result {k : Nat} (p : Plan k) (orig : Array Key)
    (h : orig.size = 2 * k) where
  bank : Array Key
  count : Nat
  size_eq : bank.size = 2 * k
  sourceUnchanged : ∀ (q : Nat) (hq : q < k),
    slot bank size_eq (p.srcAddr q) (p.srcBound hq) =
      slot orig h (p.srcAddr q) (p.srcBound hq)
  certified : ∃ (xs : List Key) (r c : Nat),
    Trace p orig bank p.leftLen p.rightLen count xs r c ∧
    xs.length = count ∧ count ≤ p.outWidth ∧
    count ≤ p.leftLen + p.rightLen ∧ p.leftLen + p.rightLen ≤ 2 * count ∧
    r ≤ 2 * count ∧ c ≤ 2 * count ∧
    (∀ (q : Nat) (hq : q < xs.length), ∃ hw : q < p.outWidth,
      slot bank size_eq (p.dstAddr q) (p.dstBound hw) = xs[q]'hq)

/-- Run on two banks already packed into one backing array. -/
def runPacked {k : Nat} (p : Plan k) (orig : Array Key)
    (h : orig.size = 2 * k) : Result p orig h :=
  let P : Array Key → Nat → Nat → Nat → Prop := fun a i j w =>
    ∃ (xs : List Key) (r c : Nat), Trace p orig a i j w xs r c
  have extend : ∀ {a i j w b i' j' w' x r c},
      P a i j w → Step p a i j w b i' j' w' x r c → P b i' j' w' := by
    intro a i j w b i' j' w' x r c hp s
    obtain ⟨xs, nr, nc, t⟩ := hp
    exact ⟨xs ++ [x], nr + r, nc + c, Trace.snoc t s⟩
  have g : Good p orig 0 0 0 (p.leftLen + p.rightLen) :=
    ⟨h, Nat.zero_le _, Nat.zero_le _, by simp, by simp⟩
  have hp : P orig 0 0 0 := ⟨[], 0, 0, Trace.nil⟩
  let e := loop p P extend (p.leftLen + p.rightLen) orig 0 0 0 g hp
  have ht : ∃ (xs : List Key) (r c : Nat),
      Trace p orig e.bank p.leftLen p.rightLen e.count xs r c := e.invariant
  { bank := e.bank
    count := e.count
    size_eq := e.size_eq
    sourceUnchanged := by
      obtain ⟨_, _, _, t⟩ := ht
      exact t.sourceUnchanged h
    certified := by
      obtain ⟨xs, r, c, t⟩ := ht
      obtain ⟨hlen, hr, hc, hlo, hhi⟩ := t.accounting
      exact ⟨xs, r, c, t, hlen, t.fits, hlo, hhi, hr, hc, t.output h⟩ }


end PaperB.PairDictionary.ArrayMerge
