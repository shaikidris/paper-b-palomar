module

public import PaperB.Forest
public import PaperB.PrefixProbe

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestHead

open LabelledQuotient PrefixProbe

abbrev Vertex (H : LabelledQuotient) := Fin H.vertexCount

/-- The read-only interface to the forest before processing this head.

For a `JumpForest`, pass `depthOf`, `ancestorAtDepth`, and
`decideAncestor` for the three forest selectors. `key` reads the ordered
pair record of a positive node. Its value at the artificial root is unused.
No selector returns an ancestor list. -/
structure Selectors (H : LabelledQuotient) where
  label : Vertex H → Nat
  depth : Nat → Nat
  atDepth : Nat → Nat → Nat
  ancestor : Nat → Nat → Bool
  key : Nat → CutPair H

/-- Deduplication is by predecessor vertex, not by label or pair key.
In particular, the root is retained if it is a predecessor.
This list is used only for the repeated tests. -/
structure TestSpec {H : LabelledQuotient} (y : Vertex H)
    (xs : List (Vertex H)) : Prop where
  nodup : xs.Nodup
  cover : ∀ u, u ∈ xs ↔ H.HasQuotientArc u y

inductive LabelSelector where
  | existing (node : Nat)
  | fresh
  deriving DecidableEq, Repr

structure Step (H : LabelledQuotient) where
  newPair : Option (CutPair H)
  parent : Nat
  assigned : LabelSelector

def finish {H : LabelledQuotient} (parent : Nat) (key : Option (CutPair H)) :
    Step H :=
  ⟨key, parent, match key with
    | none => .existing parent
    | some _ => .fresh⟩

/-- Depth zero is the artificial root, and needs no jump query. -/
def nodeAt {H : LabelledQuotient} (S : Selectors H) (u d : Nat) : Nat :=
  if d = 0 then 0 else S.atDepth u d

structure Probe where
  ok : Bool
  tests : Nat
  depthCalls : Nat
  ancestryCalls : Nat

/-- An endpoint hit does not read the predecessor label or query ancestry. -/
def raw {H : LabelledQuotient} (S : Selectors H) (a : Nat)
    (B : CutPair H) (u : Vertex H) : Bool × Nat :=
  if B.Mem u then (true, 0) else (S.ancestor a (S.label u), 1)

theorem raw_ok {H : LabelledQuotient} (S : Selectors H) (a : Nat)
    (B : CutPair H) (u : Vertex H) :
    (raw S a B u).1 = true ↔ B.Mem u ∨ S.ancestor a (S.label u) = true := by
  by_cases h : B.Mem u <;> simp [raw, h]

private theorem raw_calls_le {H : LabelledQuotient} (S : Selectors H)
    (a : Nat) (B : CutPair H) (u : Vertex H) :
    (raw S a B u).2 ≤ 1 := by
  by_cases h : B.Mem u <;> simp [raw, h]

/-- Count the failing test, but do not test the tail after it. -/
def scan {α : Type} (test : α → Bool × Nat) : List α → Probe
  | [] => ⟨true, 0, 0, 0⟩
  | x :: xs =>
    let q := test x
    if q.1 then
      let r := scan test xs
      ⟨r.ok, r.tests + 1, 0, r.ancestryCalls + q.2⟩
    else
      ⟨false, 1, 0, q.2⟩

theorem scan_ok {α : Type} (test : α → Bool × Nat) (xs : List α) :
    (scan test xs).ok = true ↔ ∀ x, x ∈ xs → (test x).1 = true := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    by_cases hx : (test x).1 = true
    · simp only [scan, if_pos hx]
      rw [ih]
      constructor
      · intro h u hu
        rcases List.mem_cons.mp hu with he | ht
        · subst u
          exact hx
        · exact h u ht
      · intro h u hu
        exact h u (List.mem_cons.mpr (Or.inr hu))
    · simp only [scan, if_neg hx]
      constructor
      · intro h
        cases h
      · intro h
        exact False.elim (hx (h x (by simp)))

theorem scan_bounds {α : Type} (test : α → Bool × Nat)
    (ht : ∀ x, (test x).2 ≤ 1) (xs : List α) :
    (scan test xs).tests ≤ xs.length ∧
      (scan test xs).ancestryCalls ≤ (scan test xs).tests := by
  induction xs with
  | nil => simp [scan]
  | cons x xs ih =>
    obtain ⟨hLen, hCalls⟩ := ih
    have hOne := ht x
    by_cases hx : (test x).1 = true
    · simp only [scan, if_pos hx, List.length_cons]
      constructor <;> omega
    · simp only [scan, if_neg hx, List.length_cons]
      constructor <;> omega

/-- Depth zero is true; depths past the latest label are false.
A real probe reads one pair record, then scans the unique predecessors. -/
def probe {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (d : Nat) : Probe :=
  if d = 0 then ⟨true, 0, 0, 0⟩
  else if d ≤ S.depth (S.label m) then
    let a := S.atDepth (S.label m) d
    let r := scan (raw S a (S.key a)) xs
    { r with depthCalls := 1 }
  else ⟨false, 0, 0, 0⟩

private theorem probe_bounds {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (d : Nat) :
    (probe S xs m d).tests ≤ xs.length ∧
      (probe S xs m d).depthCalls ≤ 1 ∧
      (probe S xs m d).ancestryCalls ≤ (probe S xs m d).tests := by
  by_cases hz : d = 0
  · simp [probe, hz]
  by_cases hd : d ≤ S.depth (S.label m)
  · let a := S.atDepth (S.label m) d
    have h := scan_bounds (raw S a (S.key a))
      (raw_calls_le S a (S.key a)) xs
    simp only [probe, if_neg hz, if_pos hd]
    exact ⟨h.1, Nat.le_refl 1, h.2⟩
  · simp [probe, hz, hd]

structure SearchResult where
  cut : Nat
  comparisons : Nat
  tests : Nat
  depthCalls : Nat
  ancestryCalls : Nat

def addProbe (q : Probe) (r : SearchResult) : SearchResult :=
  ⟨r.cut, r.comparisons + 1, r.tests + q.tests,
    r.depthCalls + q.depthCalls, r.ancestryCalls + q.ancestryCalls⟩

/-- `PrefixProbe.search` with the work of each *evaluated* probe retained.
A comparison here means one midpoint predicate evaluation, as in
`PrefixProbe.search`; it does not count the search's arithmetic guards. -/
def measuredSearch (p : Nat → Probe) : Nat → Nat → Nat → SearchResult
  | 0, lo, _ => ⟨lo, 0, 0, 0, 0⟩
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then ⟨lo, 0, 0, 0, 0⟩
    else
      let mid := lo + (hi - lo) / 2
      let q := p mid
      let r := if q.ok then measuredSearch p fuel mid hi
               else measuredSearch p fuel lo mid
      addProbe q r

theorem measuredSearch_project (p : Nat → Probe) (fuel lo hi : Nat) :
    ((measuredSearch p fuel lo hi).cut,
      (measuredSearch p fuel lo hi).comparisons) =
      PrefixProbe.search (fun d => (p d).ok) fuel lo hi := by
  induction fuel generalizing lo hi with
  | zero => rfl
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simp [measuredSearch, PrefixProbe.search, hs]
    · by_cases hp : (p (lo + (hi - lo) / 2)).ok = true
      · simp only [measuredSearch, PrefixProbe.search, if_neg hs, if_pos hp, addProbe]
        rw [← ih (lo + (hi - lo) / 2) hi]
      · simp only [measuredSearch, PrefixProbe.search, if_neg hs, if_neg hp, addProbe]
        rw [← ih lo (lo + (hi - lo) / 2)]

def Within (n : Nat) (r : SearchResult) : Prop :=
  r.tests ≤ r.comparisons * n ∧ r.depthCalls ≤ r.comparisons ∧
    r.ancestryCalls ≤ r.tests

private theorem addProbe_within (n : Nat) (q : Probe) (r : SearchResult)
    (hq : q.tests ≤ n ∧ q.depthCalls ≤ 1 ∧ q.ancestryCalls ≤ q.tests)
    (hr : Within n r) : Within n (addProbe q r) := by
  obtain ⟨hqT, hqD, hqA⟩ := hq
  obtain ⟨hrT, hrD, hrA⟩ := hr
  simp only [Within, addProbe, Nat.add_mul, Nat.one_mul]
  refine ⟨?_, ?_, ?_⟩ <;> omega

theorem measuredSearch_within (p : Nat → Probe) (n : Nat)
    (hp : ∀ d, (p d).tests ≤ n ∧ (p d).depthCalls ≤ 1 ∧
      (p d).ancestryCalls ≤ (p d).tests)
    (fuel lo hi : Nat) : Within n (measuredSearch p fuel lo hi) := by
  induction fuel generalizing lo hi with
  | zero => simp [measuredSearch, Within]
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simp [measuredSearch, hs, Within]
    · by_cases hq : (p (lo + (hi - lo) / 2)).ok = true
      · simpa only [measuredSearch, if_neg hs, if_pos hq] using
          addProbe_within n _ _ (hp (lo + (hi - lo) / 2))
            (ih (lo + (hi - lo) / 2) hi)
      · simpa only [measuredSearch, if_neg hs, if_neg hq] using
          addProbe_within n _ _ (hp (lo + (hi - lo) / 2))
            (ih lo (lo + (hi - lo) / 2))

def measuredLog (p : Nat → Probe) (hi : Nat) : SearchResult :=
  measuredSearch p (Nat.log2 hi + 1) 0 hi

theorem measuredLog_project (p : Nat → Probe) (hi : Nat) :
    ((measuredLog p hi).cut, (measuredLog p hi).comparisons) =
      searchLog (fun d => (p d).ok) 0 hi := by
  simpa only [measuredLog, searchLog, Nat.sub_zero] using
    measuredSearch_project p (Nat.log2 hi + 1) 0 hi

structure Measured (H : LabelledQuotient) where
  step : Step H
  search : SearchResult

/-- Include the final parent selection, not just the midpoint selections. -/
def Measured.depthCalls {H : LabelledQuotient} (r : Measured H) : Nat :=
  r.search.depthCalls + (if r.search.cut = 0 then 0 else 1)

/-- Bounded per-head kernel. `m` and `key` are selected from the original
predecessors; only `xs`, the repeated-test list, is deduplicated.
`.fresh` requests assignment to the node for `newPair`; this kernel does
not allocate or intern that node. -/
def active {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H)) :
    Measured H :=
  let r := measuredLog (probe S xs m) (S.depth (S.label m) + 1)
  ⟨finish (nodeAt S (S.label m) r.cut) key, r⟩

def stopped {H : LabelledQuotient} : Measured H :=
  ⟨finish 0 none, ⟨0, 0, 0, 0, 0⟩⟩

theorem stopped_work {H : LabelledQuotient} :
    (stopped (H := H)).search.comparisons = 0 ∧
      (stopped (H := H)).search.tests = 0 ∧
      (stopped (H := H)).depthCalls = 0 ∧
      (stopped (H := H)).search.ancestryCalls = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem active_work {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H)) :
    let r := active S xs m key
    r.search.comparisons ≤ Nat.log2 (S.depth (S.label m) + 1) + 1 ∧
      r.search.tests ≤ r.search.comparisons * xs.length ∧
      r.depthCalls ≤ r.search.comparisons + 1 ∧
      r.search.ancestryCalls ≤ r.search.tests := by
  let p := probe S xs m
  let hi := S.depth (S.label m) + 1
  let r := measuredLog p hi
  have hc : r.comparisons = (searchLog (fun d => (p d).ok) 0 hi).2 :=
    congrArg Prod.snd (measuredLog_project p hi)
  have hLog : r.comparisons ≤ Nat.log2 hi + 1 := by
    rw [hc]
    simpa only [Nat.sub_zero] using
      searchLog_count_le (fun d => (p d).ok) 0 hi
  have hWithin : Within xs.length r :=
    measuredSearch_within p xs.length (probe_bounds S xs m)
      (Nat.log2 hi + 1) 0 hi
  obtain ⟨ht, hd, ha⟩ := hWithin
  change r.comparisons ≤ Nat.log2 hi + 1 ∧
    r.tests ≤ r.comparisons * xs.length ∧
    r.depthCalls + (if r.cut = 0 then 0 else 1) ≤ r.comparisons + 1 ∧
    r.ancestryCalls ≤ r.tests
  refine ⟨hLog, ht, ?_, ha⟩
  by_cases hz : r.cut = 0 <;> simp only [hz, if_true, if_false] <;> omega

/-- Separate charges for the two jump operations. For the word-layout
adapter, `ancestorAtDepthWords_spec` supplies `depthCost` and
`decideAncestorWords_spec` supplies `ancestryCost`. Under their layout,
valid-node and size hypotheses, each can be `1 + 3 * (6 * L + 1)`.
This charge does not include label, pair record, list, or head-plan access. -/
theorem active_jump_charge {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) (key : Option (CutPair H))
    (depthCost ancestryCost : Nat) :
    let r := active S xs m key
    r.depthCalls * depthCost + r.search.ancestryCalls * ancestryCost ≤
      (r.search.comparisons + 1) * depthCost +
        (r.search.comparisons * xs.length) * ancestryCost := by
  obtain ⟨_, ht, hd, ha⟩ := active_work S xs m key
  exact Nat.add_le_add (Nat.mul_le_mul_right depthCost hd)
    (Nat.mul_le_mul_right ancestryCost (Nat.le_trans ha ht))

/-- Ghost view of an assigned selector; never used by the kernel. -/
def decode {H : LabelledQuotient} (view : Nat → List (CutPair H))
    (step : Step H) : List (CutPair H) :=
  match step.assigned with
  | .existing node => view node
  | .fresh => view step.parent ++ step.newPair.toList

theorem decode_finish {H : LabelledQuotient} (view : Nat → List (CutPair H))
    (parent : Nat) (key : Option (CutPair H)) :
    decode view (finish parent key) = view parent ++ key.toList := by
  cases key <;> simp [decode, finish]

/-- Contracts on the passed selectors at a ready head. All the chains in
these contracts are for *previous* nodes. `legacy_pass` is the
predecessor-loss characterization of the existing semantic predicate;
it does not assert any result about the new label or its cutoff.

`view_at` says which prefix a selected node represents. `key_at` and
`raw_loss` say what a real probe reads and what a predecessor test means. -/
structure Ready {H : LabelledQuotient} (S : Selectors H)
    (view : Nat → List (CutPair H)) (rank : Vertex H → Nat)
    (y m : Vertex H) (xs : List (Vertex H)) : Prop where
  depth_eq : S.depth (S.label m) = (sweepChain H rank m).length
  view_at : ∀ d, d ≤ S.depth (S.label m) →
    view (nodeAt S (S.label m) d) = (sweepChain H rank m).take d
  key_at : ∀ (k : Nat) (hk : k < (sweepChain H rank m).length),
    S.key (S.atDepth (S.label m) (k + 1)) = (sweepChain H rank m)[k]
  raw_loss : ∀ (k : Nat) (hk : k < (sweepChain H rank m).length)
      (u : Vertex H), u ∈ xs →
    (((sweepChain H rank m)[k].Mem u ∨
        S.ancestor (S.atDepth (S.label m) (k + 1)) (S.label u) = true) ↔
      H.Lost (sweepChain H rank m)[k] u)
  nested : (sweepChain H rank m).Pairwise
    (fun B P => ∀ v, P.Mem v → H.Lost B v)
  legacy_pass : ∀ (k : Nat) (hk : k < (sweepChain H rank m).length),
    sweepPasses H rank y (sweepChain H rank m)[k] = true ↔
      ∀ u, H.HasQuotientArc u y → H.Lost (sweepChain H rank m)[k] u

private theorem probe_real {H : LabelledQuotient} {S : Selectors H}
    {view : Nat → List (CutPair H)} {rank : Vertex H → Nat}
    {y m : Vertex H} {xs : List (Vertex H)}
    (T : TestSpec y xs) (R : Ready S view rank y m xs)
    (k : Nat) (hk : k < (sweepChain H rank m).length) :
    (probe S xs m (k + 1)).ok = true ↔
      ∀ u, H.HasQuotientArc u y → H.Lost (sweepChain H rank m)[k] u := by
  have hz : k + 1 ≠ 0 := by omega
  have hd : k + 1 ≤ S.depth (S.label m) := by
    rw [R.depth_eq]
    omega
  simp only [probe, if_neg hz, if_pos hd]
  rw [R.key_at k hk, scan_ok]
  constructor
  · intro h u hu
    have hm := (T.cover u).2 hu
    exact (R.raw_loss k hk u hm).1 ((raw_ok _ _ _ _).1 (h u hm))
  · intro h u hu
    exact (raw_ok _ _ _ _).2 ((R.raw_loss k hk u hu).2 (h u ((T.cover u).1 hu)))

private theorem probe_end {H : LabelledQuotient} (S : Selectors H)
    (xs : List (Vertex H)) (m : Vertex H) :
    (probe S xs m (S.depth (S.label m) + 1)).ok = false := by
  have h : ¬ S.depth (S.label m) + 1 ≤ S.depth (S.label m) := by omega
  simp [probe, h]

private theorem probe_mono {H : LabelledQuotient} {S : Selectors H}
    {view : Nat → List (CutPair H)} {rank : Vertex H → Nat}
    {y m : Vertex H} {xs : List (Vertex H)}
    (T : TestSpec y xs) (R : Ready S view rank y m xs) :
    ∀ a b : Nat, 0 ≤ a → a ≤ b → b ≤ S.depth (S.label m) + 1 →
      (probe S xs m b).ok = true → (probe S xs m a).ok = true := by
  intro a b _ hab hb hpass
  cases a with
  | zero => rfl
  | succ a =>
    cases b with
    | zero => omega
    | succ b =>
      by_cases hReal : b < (sweepChain H rank m).length
      · have ha : a < (sweepChain H rank m).length := by omega
        by_cases he : a = b
        · subst a
          exact hpass
        · have hlt : a < b := by omega
          have hInc := (List.pairwise_iff_getElem.mp R.nested) a b ha hReal hlt
          apply (probe_real T R a ha).2
          intro u hu
          exact lost_of_nested_endpoints hInc ((probe_real T R b hReal).1 hpass u hu)
      · have he : b + 1 = S.depth (S.label m) + 1 := by
          rw [R.depth_eq] at hb ⊢
          omega
        rw [he, probe_end S xs m] at hpass
        cases hpass

/-- Real depths are classified by the selected cutoff. The upper sentinel
is not a forest node and is never selected. -/
theorem active_cut {H : LabelledQuotient} {S : Selectors H}
    {view : Nat → List (CutPair H)} {rank : Vertex H → Nat}
    {y m : Vertex H} {xs : List (Vertex H)}
    (T : TestSpec y xs) (R : Ready S view rank y m xs)
    (key : Option (CutPair H)) :
    let cut := (active S xs m key).search.cut
    cut ≤ (sweepChain H rank m).length ∧
      ∀ (k : Nat) (hk : k < (sweepChain H rank m).length),
        (∀ u, H.HasQuotientArc u y → H.Lost (sweepChain H rank m)[k] u) ↔
          k + 1 ≤ cut := by
  let hi := S.depth (S.label m) + 1
  let p : Nat → Bool := fun d => (probe S xs m d).ok
  have hp : (measuredLog (probe S xs m) hi).cut = (searchLog p 0 hi).1 :=
    congrArg Prod.fst (measuredLog_project (probe S xs m) hi)
  dsimp only [active]
  rw [hp]
  have hHi : 0 < hi := by dsimp [hi]; omega
  obtain ⟨_, hlt, _, _, hClass⟩ :=
    searchLog_spec p 0 hi hHi rfl (probe_end S xs m) (probe_mono T R)
  have he : hi = (sweepChain H rank m).length + 1 :=
    congrArg (fun n : Nat => n + 1) R.depth_eq
  have hRank : (searchLog p 0 hi).1 ≤ (sweepChain H rank m).length :=
    Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hlt (Nat.le_of_eq he))
  refine ⟨hRank, ?_⟩
  intro k hk
  have hd : k + 1 ≤ hi := by rw [he]; omega
  exact (probe_real T R k hk).symm.trans (hClass (k + 1) (Nat.zero_le _) hd).1

private theorem takeWhile_eq_take_index {α : Type} (p : α → Bool)
    (xs : List α) (cut : Nat)
    (h : ∀ (k : Nat) (hk : k < xs.length), p xs[k] = true ↔ k + 1 ≤ cut) :
    xs.takeWhile p = xs.take cut := by
  induction xs generalizing cut with
  | nil => cases cut <;> rfl
  | cons x xs ih =>
    have hx : p x = true ↔ 1 ≤ cut := h 0 (by simp)
    cases cut with
    | zero =>
      cases hp : p x with
      | false => simp [List.takeWhile, hp]
      | true =>
        have hBad := hx.mp hp
        omega
    | succ cut =>
      have hxTrue : p x = true := hx.mpr (by omega)
      have ht : ∀ (k : Nat) (hk : k < xs.length),
          p xs[k] = true ↔ k + 1 ≤ cut := by
        intro k hk
        have hs : k + 1 < (x :: xs).length := by
          simp only [List.length_cons]
          omega
        have hi : p xs[k] = true ↔ (k + 1) + 1 ≤ cut + 1 := h (k + 1) hs
        exact hi.trans (by omega)
      simp [List.takeWhile, hxTrue, ih cut ht]

/-- The forest update, interpreted by the ghost view, is the existing
semantic step. In particular the proof identifies the prefix retained
before the optional pair is appended. -/
theorem active_semantics {H : LabelledQuotient} {S : Selectors H}
    {view : Nat → List (CutPair H)} {rank : Vertex H → Nat}
    {y m : Vertex H} {xs : List (Vertex H)}
    (T : TestSpec y xs) (R : Ready S view rank y m xs)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (hy : y ≠ H.root) (hNoRoot : H.hasQuotientArcBool H.root y = false)
    (hMax : maxByRank rank (preds H y) = some m)
    (hEntering : H.HasQuotientArc m y) :
    decode view (active S xs m (candidatePairOfPreds H (preds H y))).step =
      sweepChain H rank y := by
  let key := candidatePairOfPreds H (preds H y)
  let cut := (active S xs m key).search.cut
  obtain ⟨hc, hClass⟩ := active_cut T R key
  have hd : cut ≤ S.depth (S.label m) := by
    rw [R.depth_eq]
    exact hc
  have ht : (sweepChain H rank m).takeWhile (sweepPasses H rank y) =
      (sweepChain H rank m).take cut :=
    takeWhile_eq_take_index _ _ cut
      (fun k hk => (R.legacy_pass k hk).trans (hClass k hk))
  change decode view (finish (nodeAt S (S.label m) cut) key) = _
  calc
    decode view (finish (nodeAt S (S.label m) cut) key) =
        view (nodeAt S (S.label m) cut) ++ key.toList :=
      decode_finish view _ _
    _ = (sweepChain H rank m).take cut ++ key.toList := by
      rw [R.view_at cut hd]
    _ = sweepChain H rank y := by
      rw [← ht]
      exact (sweepChain_eq_step rankArc hy hNoRoot hMax hEntering).symm

/-- Optional adapter using the existing head-plan selectors. In particular,
neither the latest-predecessor selection nor the candidate-key selection
uses the repeated-test list. All three stop cases do no forest probes. -/
def runHead {H : LabelledQuotient} (S : Selectors H)
    (rank : Vertex H → Nat) (y : Vertex H) (xs : List (Vertex H)) :
    Measured H :=
  if y = H.root then stopped
  else if H.hasQuotientArcBool H.root y then stopped
  else
    let ps := preds H y
    match maxByRank rank ps with
    | none => stopped
    | some m => active S xs m (candidatePairOfPreds H ps)

theorem runHead_semantics {H : LabelledQuotient} (S : Selectors H)
    (view : Nat → List (CutPair H)) (rank : Vertex H → Nat)
    (y : Vertex H) (xs : List (Vertex H)) (T : TestSpec y xs)
    (rootView : view 0 = [])
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (ready : ∀ m, y ≠ H.root → H.hasQuotientArcBool H.root y = false →
      maxByRank rank (preds H y) = some m →
        H.HasQuotientArc m y ∧ Ready S view rank y m xs) :
    decode view (runHead S rank y xs).step = sweepChain H rank y := by
  by_cases hy : y = H.root
  · simp [runHead, hy, stopped, decode, finish, rootView, sweepChain, sweepChainAux]
  · cases hr : H.hasQuotientArcBool H.root y with
    | true =>
      simp [runHead, hy, hr, stopped, decode, finish, rootView, sweepChain, sweepChainAux]
    | false =>
      cases hm : maxByRank rank (preds H y) with
      | none =>
        simp [runHead, hy, hr, hm, stopped, decode, finish, rootView,
          sweepChain, sweepChainAux]
      | some m =>
        obtain ⟨hEntering, R⟩ := ready m hy hr hm
        simpa [runHead, hy, hr, hm] using
          active_semantics T R rankArc hy hr hm hEntering

end PaperB.ForestHead
