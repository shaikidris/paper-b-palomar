module

public import PaperB.ExitPaths

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Finite topological sweep and proper-loss forest construction (Lemma 3.1) for Paper B. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace LabelledQuotient

private theorem fin_eq_of_val_eq {n : Nat} {a b : Fin n} (h : a.val = b.val) : a = b := by
  cases a with
  | mk va _ =>
    cases b with
    | mk vb _ =>
      change va = vb at h
      subst h
      rfl

private theorem nat_lt_of_not_lt_of_ne :
    ∀ {a b : Nat}, ¬ a < b → a ≠ b → b < a
  | 0, 0, _, hne => False.elim (hne rfl)
  | 0, _ + 1, hlt, _ => False.elim (hlt (Nat.zero_lt_succ _))
  | _ + 1, 0, _, _ => Nat.zero_lt_succ _
  | _ + 1, _ + 1, hlt, hne =>
      Nat.succ_lt_succ
        (nat_lt_of_not_lt_of_ne
          (fun h => hlt (Nat.succ_lt_succ h))
          (fun h => hne (congrArg Nat.succ h)))

private theorem nat_le_of_not_le : ∀ {a b : Nat}, ¬ a ≤ b → b ≤ a
  | 0, b, hle => False.elim (hle (Nat.zero_le b))
  | _ + 1, 0, _ => Nat.zero_le _
  | _ + 1, _ + 1, hle =>
      Nat.succ_le_succ (nat_le_of_not_le (fun h => hle (Nat.succ_le_succ h)))

theorem CutPair.ext {H : LabelledQuotient} {A B : CutPair H}
    (hFst : A.fst = B.fst) (hSnd : A.snd = B.snd) : A = B := by
  cases A with
  | mk a₁ a₂ _ _ _ =>
    cases B with
    | mk b₁ b₂ _ _ _ =>
      change a₁ = b₁ at hFst
      change a₂ = b₂ at hSnd
      subst hFst
      subst hSnd
      rfl

instance CutPair.instDecidableEq {H : LabelledQuotient} : DecidableEq (CutPair H) :=
  fun A B =>
    if h₁ : A.fst = B.fst then
      if h₂ : A.snd = B.snd then
        isTrue (CutPair.ext h₁ h₂)
      else
        isFalse (fun hEq => h₂ (congrArg CutPair.snd hEq))
    else
      isFalse (fun hEq => h₁ (congrArg CutPair.fst hEq))

/-- Canonically ordered representative (`fst < snd`) with identical endpoint set. -/
def CutPair.canonical {H : LabelledQuotient} (B : CutPair H) : CutPair H :=
  if B.fst < B.snd then
    B
  else
    ⟨B.snd, B.fst, B.snd_ne_root, B.fst_ne_root, B.ne.symm⟩

theorem CutPair.canonical_lt {H : LabelledQuotient} (B : CutPair H) :
    B.canonical.fst < B.canonical.snd := by
  unfold CutPair.canonical
  by_cases h : B.fst < B.snd
  · rw [ite_eq_left h]
    exact h
  · rw [ite_eq_right h]
    exact nat_lt_of_not_lt_of_ne h (fun hVal => B.ne (fin_eq_of_val_eq hVal))

theorem CutPair.canonical_eq_self {H : LabelledQuotient} {B : CutPair H}
    (h : B.fst < B.snd) : B.canonical = B := by
  unfold CutPair.canonical
  exact ite_eq_left h

theorem CutPair.canonical_mem_iff {H : LabelledQuotient} (B : CutPair H)
    (u : Fin H.vertexCount) : B.canonical.Mem u ↔ B.Mem u := by
  unfold CutPair.canonical
  by_cases h : B.fst < B.snd
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact ⟨fun hm => hm.elim Or.inr Or.inl, fun hm => hm.elim Or.inr Or.inl⟩

theorem lost_canonical_iff (H : LabelledQuotient) (B : CutPair H)
    (v : Fin H.vertexCount) : H.Lost B.canonical v ↔ H.Lost B v := by
  constructor
  · exact fun hLost hPath =>
      hLost (AvoidPath.mono hPath (fun z hz => (B.canonical_mem_iff z).mp hz))
  · exact fun hLost hPath =>
      hLost (AvoidPath.mono hPath (fun z hz => (B.canonical_mem_iff z).mpr hz))

theorem properLoss_canonical_iff (H : LabelledQuotient) (B : CutPair H)
    (v : Fin H.vertexCount) : H.ProperLoss B.canonical v ↔ H.ProperLoss B v := by
  constructor
  · intro h
    exact ⟨(lost_canonical_iff H B v).mp h.1, fun hm => h.2 ((B.canonical_mem_iff v).mpr hm)⟩
  · intro h
    exact ⟨(lost_canonical_iff H B v).mpr h.1, fun hm => h.2 ((B.canonical_mem_iff v).mp hm)⟩

theorem CutPair.eq_of_canonical_mem_iff {H : LabelledQuotient}
    {A B : CutPair H} (hA : A.fst < A.snd) (hB : B.fst < B.snd)
    (hMem : ∀ u : Fin H.vertexCount, A.Mem u ↔ B.Mem u) : A = B := by
  have hFst : A.fst = B.fst := by
    cases (hMem A.fst).mp (Or.inl rfl) with
    | inl hEq => exact hEq
    | inr hA1B2 =>
        cases (hMem B.fst).mpr (Or.inl rfl) with
        | inl hB1A1 => exact hB1A1.symm
        | inr hB1A2 =>
            have h1 : B.snd < A.snd := by rw [← hA1B2]; exact hA
            have h2 : B.snd < B.fst := by rw [hB1A2]; exact h1
            exact False.elim (Nat.lt_irrefl B.fst.val (Nat.lt_trans hB h2))
  have hSnd : A.snd = B.snd := by
    cases (hMem A.snd).mp (Or.inr rfl) with
    | inr hEq => exact hEq
    | inl hA2B1 =>
        cases (hMem B.snd).mpr (Or.inr rfl) with
        | inr hB2A2 => exact hB2A2.symm
        | inl hB2A1 =>
            have h1 : A.snd < B.snd := by rw [hA2B1]; exact hB
            have h2 : A.snd < A.fst := by rw [← hB2A1]; exact h1
            exact False.elim (Nat.lt_irrefl A.fst.val (Nat.lt_trans hA h2))
  exact CutPair.ext hFst hSnd

/-! ### Self-contained computable list combinators -/

def anyBool {α : Type} (p : α → Bool) : List α → Bool
  | [] => false
  | x :: xs => if p x then true else anyBool p xs

theorem anyBool_eq_true_iff {α : Type} (p : α → Bool) (l : List α) :
    anyBool p l = true ↔ ∃ x : α, x ∈ l ∧ p x = true := by
  induction l with
  | nil =>
      constructor
      · intro h; nomatch h
      · intro ⟨_, hMem, _⟩; nomatch hMem
  | cons x xs ih =>
      dsimp [anyBool]
      cases hpx : p x with
      | true =>
          simp only [ ↓reduceIte, true_iff]
          exact ⟨x, List.mem_cons.mpr (Or.inl rfl), hpx⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          constructor
          · intro hRest
            let ⟨z, hzMem, hpz⟩ := ih.mp hRest
            exact ⟨z, List.mem_cons.mpr (Or.inr hzMem), hpz⟩
          · intro ⟨z, hzMem, hpz⟩
            cases List.mem_cons.mp hzMem with
            | inl hEq =>
                rw [hEq] at hpz
                exact False.elim (by rw [hpx] at hpz; nomatch hpz)
            | inr hzTail =>
                exact ih.mpr ⟨z, hzTail, hpz⟩

def allBool {α : Type} (p : α → Bool) : List α → Bool
  | [] => true
  | x :: xs => if p x then allBool p xs else false

theorem allBool_eq_true_iff {α : Type} (p : α → Bool) (l : List α) :
    allBool p l = true ↔ ∀ x : α, x ∈ l → p x = true := by
  induction l with
  | nil =>
      constructor
      · intro _ _ hMem; nomatch hMem
      · intro _; rfl
  | cons x xs ih =>
      dsimp [allBool]
      cases hpx : p x with
      | true =>
          simp only [↓reduceIte]
          constructor
          · intro hRest z hzMem
            cases List.mem_cons.mp hzMem with
            | inl hEq => rw [hEq]; exact hpx
            | inr hzTail => exact ih.mp hRest z hzTail
          · intro hAll
            exact ih.mpr (fun z hzTail => hAll z (List.mem_cons.mpr (Or.inr hzTail)))
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, false_iff]
          intro hAll
          have hTrue : p x = true := hAll x (List.mem_cons.mpr (Or.inl rfl))
          rw [hpx] at hTrue
          nomatch hTrue

theorem allBool_congr {α : Type} {p q : α → Bool} {l : List α}
    (hEq : ∀ x : α, x ∈ l → p x = q x) : allBool p l = allBool q l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      dsimp [allBool]
      rw [hEq x (List.mem_cons.mpr (Or.inl rfl))]
      rw [ih (fun z hz => hEq z (List.mem_cons.mpr (Or.inr hz)))]

def keepBool {α : Type} (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs => if p x then x :: keepBool p xs else keepBool p xs

theorem mem_keepBool_iff {α : Type} (p : α → Bool) (l : List α) (x : α) :
    x ∈ keepBool p l ↔ x ∈ l ∧ p x = true := by
  induction l with
  | nil =>
      constructor
      · intro h; nomatch h
      · intro ⟨h, _⟩; nomatch h
  | cons y ys ih =>
      dsimp [keepBool]
      cases hpy : p y with
      | true =>
          simp only [↓reduceIte]
          constructor
          · intro hMem
            cases List.mem_cons.mp hMem with
            | inl hEq => rw [hEq]; exact ⟨List.mem_cons.mpr (Or.inl rfl), hpy⟩
            | inr hTail =>
                let ⟨hInYs, hpx⟩ := ih.mp hTail
                exact ⟨List.mem_cons.mpr (Or.inr hInYs), hpx⟩
          · intro ⟨hInCons, hpx⟩
            cases List.mem_cons.mp hInCons with
            | inl hEq => exact List.mem_cons.mpr (Or.inl hEq)
            | inr hInYs => exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨hInYs, hpx⟩))
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          constructor
          · intro hTail
            let ⟨hInYs, hpx⟩ := ih.mp hTail
            exact ⟨List.mem_cons.mpr (Or.inr hInYs), hpx⟩
          · intro ⟨hInCons, hpx⟩
            cases List.mem_cons.mp hInCons with
            | inl hEq =>
                rw [hEq, hpy] at hpx
                nomatch hpx
            | inr hInYs => exact ih.mpr ⟨hInYs, hpx⟩

theorem pairwise_keepBool {α : Type} {R : α → α → Prop} (p : α → Bool)
    {l : List α} (hl : l.Pairwise R) : (keepBool p l).Pairwise R := by
  revert hl
  induction l with
  | nil =>
      intro _
      exact List.Pairwise.nil
  | cons x xs ih =>
      intro hl
      let ⟨hxRel, hxsRel⟩ := List.pairwise_cons.mp hl
      dsimp [keepBool]
      cases p x with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact ih hxsRel
      | true =>
          simp only [↓reduceIte]
          refine List.pairwise_cons.mpr ⟨?_, ih hxsRel⟩
          intro z hz
          exact hxRel z ((mem_keepBool_iff p xs z).mp hz).1

/-! ### Strictly sorted `Fin` enumeration, decidable arcs, and predecessor lists -/

private def finSucc {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def finElems : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.zero_lt_succ n⟩ :: (finElems n).map finSucc

theorem length_finElems (n : Nat) : (finElems n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      dsimp [finElems]
      rw [List.length_map, ih]

/-! ### Linear executable enumeration

The loop visits `k - 1, …, 0`. Prepending each visited index produces
`0, …, k - 1` in front of the original accumulator.
-/

@[specialize] private def finElems_loop {σ : Type} (n : Nat)
    (push : Fin n → σ → σ) : (k : Nat) → k ≤ n → σ → σ
  | 0, _, acc => acc
  | k + 1, hk, acc =>
      finElems_loop n push k (Nat.le_trans (Nat.le_succ k) hk)
        (push ⟨k, hk⟩ acc)

/-- Enumerate `Fin n` in increasing order with one cons per iteration. -/
def finElems_linear (n : Nat) : List (Fin n) :=
  finElems_loop n List.cons n (Nat.le_refl n) []

private def finElems_widen {k n : Nat} (h : k ≤ n) (i : Fin k) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

private theorem finElems_snoc (k : Nat) :
    finElems (k + 1) =
      (finElems k).map (finElems_widen (Nat.le_succ k)) ++
        [⟨k, Nat.lt_succ_self k⟩] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change
        (⟨0, Nat.zero_lt_succ (k + 1)⟩ : Fin (k + 1 + 1)) ::
            (finElems (k + 1)).map finSucc =
          List.map (finElems_widen (Nat.le_succ (k + 1)))
            ((⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)) ::
              (finElems k).map finSucc) ++
            [⟨k + 1, Nat.lt_succ_self (k + 1)⟩]
      simp only [ih, List.map_append, List.map_cons, List.map_nil,
        List.cons_append, List.map_map] <;> rfl

private theorem finElems_loop_prefix (n k : Nat) (hk : k ≤ n)
    (acc : List (Fin n)) :
    finElems_loop n List.cons k hk acc =
      (finElems k).map (finElems_widen hk) ++ acc := by
  induction k generalizing acc with
  | zero =>
      simp only [finElems_loop, finElems, List.map_nil, List.nil_append]
  | succ k ih =>
      rw [finElems_loop, ih, finElems_snoc k]
      simp only [List.map_append, List.map_map, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append] <;> rfl

theorem finElems_linear_eq (n : Nat) : finElems_linear n = finElems n := by
  rw [finElems_linear, finElems_loop_prefix, List.append_nil]
  have hw : finElems_widen (Nat.le_refl n) = (id : Fin n → Fin n) := by
    funext i
    exact Fin.ext rfl
  rw [hw, List.map_id]

@[csimp] theorem finElems_csimp : finElems = finElems_linear := by
  funext n
  exact (finElems_linear_eq n).symm

/-- The same loop with one counter increment per cons. The initial empty
list and the terminating branch are not charged. -/
def finElems_linear_counted (n : Nat) : List (Fin n) × Nat :=
  finElems_loop n
    (fun i (s : List (Fin n) × Nat) => (i :: s.1, s.2 + 1))
    n (Nat.le_refl n) ([], 0)

private theorem finElems_loop_counted (n k : Nat) (hk : k ≤ n)
    (acc : List (Fin n)) (c : Nat) :
    finElems_loop n
        (fun i (s : List (Fin n) × Nat) => (i :: s.1, s.2 + 1))
        k hk (acc, c) =
      (finElems_loop n List.cons k hk acc, c + k) := by
  induction k generalizing acc c with
  | zero =>
      simp only [finElems_loop, Nat.add_zero]
  | succ k ih =>
      simp only [finElems_loop]
      rw [ih, Nat.add_right_comm c 1 k] <;> rfl

/-- Exactly `n` nonterminal iterations and `n` list cons constructions,
with the same output as the uninstrumented executable loop. -/
theorem finElems_linear_budget (n : Nat) :
    finElems_linear_counted n = (finElems_linear n, n) := by
  unfold finElems_linear_counted finElems_linear
  rw [finElems_loop_counted, Nat.zero_add]

/-- Explicit source-level substitution under a list consumer. -/
theorem finElems_linear_under.{u} {n : Nat} {α : Sort u}
    (use : List (Fin n) → α) :
    use (finElems_linear n) = use (finElems n) :=
  congrArg use (finElems_linear_eq n)

/-- Predecessor selection can call `keepBool p (finElems_linear n)` directly. -/
theorem keepBool_finElems_linear_eq (n : Nat) (p : Fin n → Bool) :
    keepBool p (finElems_linear n) = keepBool p (finElems n) :=
  finElems_linear_under (keepBool p)

theorem mem_finElems {n : Nat} (x : Fin n) : x ∈ finElems n := by
  induction n with
  | zero =>
      cases x with
      | mk _ isLt => nomatch isLt
  | succ k ih =>
      cases x with
      | mk val isLt =>
          cases val with
          | zero =>
              exact List.mem_cons.mpr (Or.inl (fin_eq_of_val_eq rfl))
          | succ v =>
              let x' : Fin k := ⟨v, Nat.le_of_succ_le_succ isLt⟩
              exact List.mem_cons.mpr
                (Or.inr (List.mem_map.mpr ⟨x', ih x', fin_eq_of_val_eq rfl⟩))

private theorem pairwise_map_imp {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hImp : ∀ a b : α, R a b → S (f a) (f b))
    {l : List α} (hl : l.Pairwise R) : (l.map f).Pairwise S := by
  revert hl
  induction l with
  | nil =>
      intro _
      exact List.Pairwise.nil
  | cons x xs ih =>
      intro hl
      let ⟨hxRel, hxsRel⟩ := List.pairwise_cons.mp hl
      refine List.pairwise_cons.mpr ⟨?_, ih hxsRel⟩
      intro b hb
      let ⟨a', ha', hfa⟩ := List.mem_map.mp hb
      rw [← hfa]
      exact hImp x a' (hxRel a' ha')

theorem pairwise_lt_finElems (n : Nat) : (finElems n).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ k ih =>
      dsimp [finElems]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro y hy
        let ⟨x, _, hfx⟩ := List.mem_map.mp hy
        rw [← hfx]
        exact Nat.zero_lt_succ x.val
      · exact pairwise_map_imp finSucc (fun _ _ hlt => Nat.succ_lt_succ hlt) ih

def hasQuotientArcBool (H : LabelledQuotient) (u w : Fin H.vertexCount) : Bool :=
  anyBool (fun e => decide (e.head = w)) (H.outArcs u)

theorem hasQuotientArcBool_eq_true_iff (H : LabelledQuotient)
    (u w : Fin H.vertexCount) :
    H.hasQuotientArcBool u w = true ↔ H.HasQuotientArc u w := by
  unfold hasQuotientArcBool HasQuotientArc
  rw [anyBool_eq_true_iff]
  constructor
  · intro ⟨e, he, hDec⟩
    exact ⟨e, he, of_decide_eq_true hDec⟩
  · intro ⟨e, he, hHead⟩
    exact ⟨e, he, decide_eq_true hHead⟩

/-- Distinct incoming predecessors of `y` in strictly increasing `Fin` order. -/
def preds (H : LabelledQuotient) (y : Fin H.vertexCount) : List (Fin H.vertexCount) :=
  keepBool (fun u => H.hasQuotientArcBool u y) (finElems H.vertexCount)

theorem mem_preds_iff (H : LabelledQuotient) (y u : Fin H.vertexCount) :
    u ∈ preds H y ↔ H.HasQuotientArc u y := by
  unfold preds
  rw [mem_keepBool_iff, hasQuotientArcBool_eq_true_iff]
  exact ⟨fun h => h.2, fun h => ⟨mem_finElems u, h⟩⟩

theorem pairwise_lt_preds (H : LabelledQuotient) (y : Fin H.vertexCount) :
    (preds H y).Pairwise (· < ·) :=
  pairwise_keepBool _ (pairwise_lt_finElems H.vertexCount)

/-! ### Latest predecessor by rank and exact canonical two-predecessor candidate -/

def maxByRankAux {n : Nat} (rank : Fin n → Nat) (best : Fin n) : List (Fin n) → Fin n
  | [] => best
  | x :: xs => maxByRankAux rank (if rank best ≤ rank x then x else best) xs

def maxByRank {n : Nat} (rank : Fin n → Nat) : List (Fin n) → Option (Fin n)
  | [] => none
  | x :: xs => some (maxByRankAux rank x xs)

private theorem maxByRankAux_mem {n : Nat} (rank : Fin n → Nat)
    (best : Fin n) (xs : List (Fin n)) :
    maxByRankAux rank best xs = best ∨ maxByRankAux rank best xs ∈ xs := by
  revert best
  induction xs with
  | nil =>
      intro best
      exact Or.inl rfl
  | cons x xs ih =>
      intro best
      dsimp [maxByRankAux]
      by_cases hle : rank best ≤ rank x
      · rw [ite_eq_left hle]
        cases ih x with
        | inl hEq => exact Or.inr (List.mem_cons.mpr (Or.inl hEq))
        | inr hMem => exact Or.inr (List.mem_cons.mpr (Or.inr hMem))
      · rw [ite_eq_right hle]
        cases ih best with
        | inl hEq => exact Or.inl hEq
        | inr hMem => exact Or.inr (List.mem_cons.mpr (Or.inr hMem))

private theorem maxByRankAux_ge {n : Nat} (rank : Fin n → Nat)
    (best : Fin n) (xs : List (Fin n)) :
    rank best ≤ rank (maxByRankAux rank best xs) ∧
      ∀ u : Fin n, u ∈ xs → rank u ≤ rank (maxByRankAux rank best xs) := by
  revert best
  induction xs with
  | nil =>
      intro best
      exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x xs ih =>
      intro best
      dsimp [maxByRankAux]
      by_cases hle : rank best ≤ rank x
      · rw [ite_eq_left hle]
        let ⟨hBestX, hRest⟩ := ih x
        refine ⟨Nat.le_trans hle hBestX, fun u hu => ?_⟩
        cases List.mem_cons.mp hu with
        | inl hEq => rw [hEq]; exact hBestX
        | inr hTail => exact hRest u hTail
      · rw [ite_eq_right hle]
        let ⟨hBest, hRest⟩ := ih best
        refine ⟨hBest, fun u hu => ?_⟩
        cases List.mem_cons.mp hu with
        | inl hEq =>
            rw [hEq]
            exact Nat.le_trans (nat_le_of_not_le hle) hBest
        | inr hTail => exact hRest u hTail

theorem maxByRank_preds_of_flat {H : LabelledQuotient}
    (rank : Fin H.vertexCount → Nat) (flat : H.IsFlat)
    {y : Fin H.vertexCount} (notRoot : H.root ≠ y) :
    ∃ m : Fin H.vertexCount,
      maxByRank rank (preds H y) = some m ∧
      H.HasQuotientArc m y ∧
      ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → rank u ≤ rank m := by
  have hExistsPred : ∃ p : Fin H.vertexCount, H.HasQuotientArc p y := by
    cases AvoidPath.eq_or_exists_last_arc (flat.1 y) with
    | inl hEq => exact False.elim (notRoot hEq)
    | inr hLast =>
        let ⟨p, _, hArc⟩ := hLast
        exact ⟨p, hArc⟩
  cases hps : preds H y with
  | nil =>
      let ⟨p, hpArc⟩ := hExistsPred
      have hpMem : p ∈ preds H y := (mem_preds_iff H y p).mpr hpArc
      rw [hps] at hpMem
      nomatch hpMem
  | cons x xs =>
      let m := maxByRankAux rank x xs
      refine ⟨m, rfl, ?_, ?_⟩
      · have hmInCons : m ∈ x :: xs := by
          cases maxByRankAux_mem rank x xs with
          | inl hEq => exact List.mem_cons.mpr (Or.inl hEq)
          | inr hTail => exact List.mem_cons.mpr (Or.inr hTail)
        have hmInPreds : m ∈ preds H y := by rw [hps]; exact hmInCons
        exact (mem_preds_iff H y m).mp hmInPreds
      · intro u huArc
        have huInCons : u ∈ x :: xs := by
          rw [← hps]
          exact (mem_preds_iff H y u).mpr huArc
        let ⟨hGeX, hGeXs⟩ := maxByRankAux_ge rank x xs
        cases List.mem_cons.mp huInCons with
        | inl hEq => rw [hEq]; exact hGeX
        | inr hTail => exact hGeXs u hTail

private theorem eq_pair_of_pairwise_lt_mem_iff {n : Nat}
    {l : List (Fin n)} (hSort : l.Pairwise (· < ·))
    {a b : Fin n} (hab : a < b)
    (hMem : ∀ u : Fin n, u ∈ l ↔ u = a ∨ u = b) :
    l = [a, b] := by
  have haMem : a ∈ l := (hMem a).mpr (Or.inl rfl)
  have hbMem : b ∈ l := (hMem b).mpr (Or.inr rfl)
  have habNe : a ≠ b := fun hEq => Nat.lt_irrefl b.val (by rw [hEq] at hab; exact hab)
  cases l with
  | nil => nomatch haMem
  | cons x xs =>
      let ⟨hxLt, hxsSort⟩ := List.pairwise_cons.mp hSort
      have hxEq : x = a := by
        cases (hMem x).mp (List.mem_cons.mpr (Or.inl rfl)) with
        | inl hxa => exact hxa
        | inr hxb =>
            cases List.mem_cons.mp haMem with
            | inl hax => exact False.elim (habNe (hax.trans hxb))
            | inr haInXs =>
                have hba : b < a := by
                  rw [← hxb]
                  exact hxLt a haInXs
                exact False.elim (Nat.lt_irrefl a.val (Nat.lt_trans hab hba))
      cases xs with
      | nil =>
          cases List.mem_cons.mp hbMem with
          | inl hbx => exact False.elim (habNe (hxEq.symm.trans hbx.symm))
          | inr hbNil => nomatch hbNil
      | cons y ys =>
          let ⟨hyLt, _⟩ := List.pairwise_cons.mp hxsSort
          have hyEq : y = b := by
            cases (hMem y).mp
                (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))) with
            | inl hya =>
                have hxy : x < y := hxLt y (List.mem_cons.mpr (Or.inl rfl))
                rw [hxEq, hya] at hxy
                exact False.elim (Nat.lt_irrefl a.val hxy)
            | inr hyb => exact hyb
          cases ys with
          | nil => rw [hxEq, hyEq]
          | cons z zs =>
              have hzInL : z ∈ x :: y :: z :: zs :=
                List.mem_cons.mpr
                  (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
              have hyz : y < z := hyLt z (List.mem_cons.mpr (Or.inl rfl))
              rw [hyEq] at hyz
              have haz : a < z := Nat.lt_trans hab hyz
              cases (hMem z).mp hzInL with
              | inl hza =>
                  rw [hza] at haz
                  exact False.elim (Nat.lt_irrefl a.val haz)
              | inr hzb =>
                  rw [hzb] at hyz
                  exact False.elim (Nat.lt_irrefl b.val hyz)

def candidatePairOfPreds (H : LabelledQuotient) (ps : List (Fin H.vertexCount)) :
    Option (CutPair H) :=
  match ps with
  | [u, v] =>
      if hu : u ≠ H.root then
        if hv : v ≠ H.root then
          if hlt : u < v then
            some ⟨u, v, hu, hv, fun hEq => Nat.lt_irrefl v.val (by rw [hEq] at hlt; exact hlt)⟩
          else
            none
        else
          none
      else
        none
  | _ => none

theorem candidatePairOfPreds_preds_iff (H : LabelledQuotient)
    (y : Fin H.vertexCount) (B : CutPair H) :
    candidatePairOfPreds H (preds H y) = some B ↔
      B.fst < B.snd ∧ ∀ u : Fin H.vertexCount, H.HasQuotientArc u y ↔ B.Mem u := by
  constructor
  · cases hps : preds H y with
    | nil => intro h; nomatch h
    | cons u rest =>
        cases rest with
        | nil => intro h; nomatch h
        | cons v rest₂ =>
            cases rest₂ with
            | cons _ _ => intro h; nomatch h
            | nil =>
                intro h
                dsimp [candidatePairOfPreds] at h
                by_cases hu : u ≠ H.root
                · rw [dite_eq_left hu] at h
                  by_cases hv : v ≠ H.root
                  · rw [dite_eq_left hv] at h
                    by_cases hlt : u < v
                    · rw [dite_eq_left hlt] at h
                      have hEq :
                          (⟨u, v, hu, hv,
                            fun hEq' => Nat.lt_irrefl v.val (by rw [hEq'] at hlt; exact hlt)⟩ :
                              CutPair H) = B :=
                        Option.some.inj h
                      refine ⟨?_, ?_⟩
                      · rw [← hEq]; exact hlt
                      · intro w
                        rw [← mem_preds_iff, hps, ← hEq]
                        constructor
                        · intro hw
                          cases List.mem_cons.mp hw with
                          | inl h₁ => exact Or.inl h₁
                          | inr h₂ =>
                              cases List.mem_cons.mp h₂ with
                              | inl h₃ => exact Or.inr h₃
                              | inr h₄ => nomatch h₄
                        · intro hw
                          cases hw with
                          | inl h₁ => exact List.mem_cons.mpr (Or.inl h₁)
                          | inr h₂ =>
                              exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl h₂)))
                    · rw [dite_eq_right hlt] at h; nomatch h
                  · rw [dite_eq_right hv] at h; nomatch h
                · rw [dite_eq_right hu] at h; nomatch h
  · intro ⟨hOrder, hArcIff⟩
    have hMemPreds : ∀ u : Fin H.vertexCount, u ∈ preds H y ↔ u = B.fst ∨ u = B.snd := by
      intro u
      rw [mem_preds_iff]
      exact hArcIff u
    have hPsEq : preds H y = [B.fst, B.snd] :=
      eq_pair_of_pairwise_lt_mem_iff (pairwise_lt_preds H y) hOrder hMemPreds
    rw [hPsEq]
    dsimp [candidatePairOfPreds]
    rw [dite_eq_left B.fst_ne_root, dite_eq_left B.snd_ne_root, dite_eq_left hOrder]

/-- Candidate canonical two-predecessor key emitted at `y` during the sweep. -/
def sweepCandidate (H : LabelledQuotient) (y : Fin H.vertexCount) : Option (CutPair H) :=
  if y = H.root then
    none
  else if H.hasQuotientArcBool H.root y then
    none
  else
    candidatePairOfPreds H (preds H y)

/-! ### Fuel-invariant topological `sweepChain` and global `sweepChain_spec` -/

def memCutPairBool {H : LabelledQuotient} (B : CutPair H) (l : List (CutPair H)) : Bool :=
  anyBool (fun X => decide (B = X)) l

theorem memCutPairBool_eq_true_iff {H : LabelledQuotient}
    (B : CutPair H) (l : List (CutPair H)) :
    memCutPairBool B l = true ↔ B ∈ l := by
  unfold memCutPairBool
  rw [anyBool_eq_true_iff]
  constructor
  · intro ⟨X, hMem, hDec⟩
    rw [of_decide_eq_true hDec]
    exact hMem
  · intro hMem
    exact ⟨B, hMem, decide_eq_true rfl⟩

def sweepChainAux (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    Nat → Fin H.vertexCount → List (CutPair H)
  | 0, _ => []
  | fuel + 1, y =>
      if y = H.root then
        []
      else if H.hasQuotientArcBool H.root y then
        []
      else
        match maxByRank rank (preds H y) with
        | none => []
        | some m =>
            let passes : CutPair H → Bool := fun B =>
              allBool
                (fun u =>
                  if decide (B.Mem u) then
                    true
                  else
                    memCutPairBool B.canonical (sweepChainAux H rank fuel u))
                (preds H y)
            (sweepChainAux H rank fuel m).takeWhile passes ++
              (candidatePairOfPreds H (preds H y)).toList

def sweepChain (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (y : Fin H.vertexCount) : List (CutPair H) :=
  sweepChainAux H rank (rank y + 1) y

def sweepPasses (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (y : Fin H.vertexCount) (B : CutPair H) : Bool :=
  allBool
    (fun u =>
      if decide (B.Mem u) then
        true
      else
        memCutPairBool B.canonical (sweepChain H rank u))
    (preds H y)

theorem sweepChainAux_eq_of_gt_rank {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v) :
    ∀ {f₁ f₂ : Nat} {y : Fin H.vertexCount},
      rank y < f₁ → rank y < f₂ →
      sweepChainAux H rank f₁ y = sweepChainAux H rank f₂ y
  | 0, _, _, h₁, _ => False.elim (by nomatch h₁)
  | _ + 1, 0, _, _, h₂ => False.elim (by nomatch h₂)
  | f₁ + 1, f₂ + 1, y, h₁, h₂ => by
      dsimp [sweepChainAux]
      by_cases hy : y = H.root
      · rw [ite_eq_left hy, ite_eq_left hy]
      · rw [ite_eq_right hy, ite_eq_right hy]
        cases hArc : H.hasQuotientArcBool H.root y with
        | true => simp only [↓reduceIte]
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte]
            cases hMax : maxByRank rank (preds H y) with
            | none => rfl
            | some m =>
                dsimp only
                have hmMem : m ∈ preds H y := by
                  cases hps : preds H y with
                  | nil =>
                      rw [hps] at hMax
                      nomatch hMax
                  | cons x xs =>
                      rw [hps] at hMax
                      have hEqM : maxByRankAux rank x xs = m := Option.some.inj hMax
                      rw [← hEqM]
                      cases maxByRankAux_mem rank x xs with
                      | inl hEq => exact List.mem_cons.mpr (Or.inl hEq)
                      | inr hTail => exact List.mem_cons.mpr (Or.inr hTail)
                have hmRankLt : rank m < rank y :=
                  rankArc m y ((mem_preds_iff H y m).mp hmMem)
                have hm₁ : rank m < f₁ :=
                  Nat.lt_of_lt_of_le hmRankLt (Nat.le_of_succ_le_succ h₁)
                have hm₂ : rank m < f₂ :=
                  Nat.lt_of_lt_of_le hmRankLt (Nat.le_of_succ_le_succ h₂)
                have hChainM :
                    sweepChainAux H rank f₁ m = sweepChainAux H rank f₂ m :=
                  sweepChainAux_eq_of_gt_rank rankArc hm₁ hm₂
                have hPassesEq :
                    (fun B : CutPair H =>
                      allBool
                        (fun u =>
                          if decide (B.Mem u) then true
                          else memCutPairBool B.canonical (sweepChainAux H rank f₁ u))
                        (preds H y)) =
                    (fun B : CutPair H =>
                      allBool
                        (fun u =>
                          if decide (B.Mem u) then true
                          else memCutPairBool B.canonical (sweepChainAux H rank f₂ u))
                        (preds H y)) := by
                  funext B
                  refine allBool_congr (fun u huPred => ?_)
                  have huRankLt : rank u < rank y :=
                    rankArc u y ((mem_preds_iff H y u).mp huPred)
                  have hu₁ : rank u < f₁ :=
                    Nat.lt_of_lt_of_le huRankLt (Nat.le_of_succ_le_succ h₁)
                  have hu₂ : rank u < f₂ :=
                    Nat.lt_of_lt_of_le huRankLt (Nat.le_of_succ_le_succ h₂)
                  rw [sweepChainAux_eq_of_gt_rank rankArc hu₁ hu₂]
                rw [hChainM, hPassesEq]

theorem sweepChain_eq_of_eq_root (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) {y : Fin H.vertexCount}
    (hy : y = H.root) : sweepChain H rank y = [] := by
  unfold sweepChain sweepChainAux
  exact ite_eq_left hy

theorem sweepChain_eq_of_root_arc (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) {y : Fin H.vertexCount}
    (hArc : H.HasQuotientArc H.root y) : sweepChain H rank y = [] := by
  unfold sweepChain sweepChainAux
  by_cases hy : y = H.root
  · exact ite_eq_left hy
  · rw [ite_eq_right hy]
    rw [(hasQuotientArcBool_eq_true_iff H H.root y).mpr hArc]
    rfl

theorem sweepChain_eq_step {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    {y m : Fin H.vertexCount}
    (hy : y ≠ H.root) (hNoRootArc : H.hasQuotientArcBool H.root y = false)
    (hMax : maxByRank rank (preds H y) = some m)
    (hEntering : H.HasQuotientArc m y) :
    sweepChain H rank y =
      (sweepChain H rank m).takeWhile (sweepPasses H rank y) ++
        (candidatePairOfPreds H (preds H y)).toList := by
  unfold sweepChain
  conv => lhs; unfold sweepChainAux
  rw [ite_eq_right hy, hNoRootArc]
  simp only [Bool.false_eq_true, ↓reduceIte, hMax]
  have hmLtY : rank m < rank y := rankArc m y hEntering
  have hChainM :
      sweepChainAux H rank (rank y) m = sweepChainAux H rank (rank m + 1) m :=
    sweepChainAux_eq_of_gt_rank rankArc hmLtY (Nat.lt_succ_self (rank m))
  have hPasses :
      (fun B : CutPair H =>
        allBool
          (fun u =>
            if decide (B.Mem u) then true
            else memCutPairBool B.canonical (sweepChainAux H rank (rank y) u))
          (preds H y)) =
      sweepPasses H rank y := by
    funext B
    unfold sweepPasses sweepChain
    refine allBool_congr (fun u huPred => ?_)
    have huLtY : rank u < rank y := rankArc u y ((mem_preds_iff H y u).mp huPred)
    rw [sweepChainAux_eq_of_gt_rank rankArc huLtY (Nat.lt_succ_self (rank u))]
  rw [hChainM, hPasses]

theorem not_properLoss_root (H : LabelledQuotient) (B : CutPair H) :
    ¬ H.ProperLoss B H.root := by
  intro hProper
  have hRootNotB : ¬ B.Mem H.root := fun hMem =>
    match hMem with
    | Or.inl h₁ => B.fst_ne_root h₁.symm
    | Or.inr h₂ => B.snd_ne_root h₂.symm
  exact hProper.1 (AvoidPath.refl H.root hRootNotB)

theorem not_properLoss_of_root_arc {H : LabelledQuotient} {B : CutPair H}
    {y : Fin H.vertexCount} (hArc : H.HasQuotientArc H.root y) :
    ¬ H.ProperLoss B y := by
  intro hProper
  have hRootNotB : ¬ B.Mem H.root := fun hMem =>
    match hMem with
    | Or.inl h₁ => B.fst_ne_root h₁.symm
    | Or.inr h₂ => B.snd_ne_root h₂.symm
  exact hProper.1
    (AvoidPath.step H.root y y hRootNotB hArc (AvoidPath.refl y hProper.2))

/-- Bundle of invariant properties maintained by `sweepChain H rank y` at every vertex `y`. -/
structure SweepChainSpec (H : LabelledQuotient)
    (chain : List (CutPair H)) (y : Fin H.vertexCount) : Prop where
  canonical : ∀ B : CutPair H, B ∈ chain → B.fst < B.snd
  nested : chain.Pairwise
    (fun ancestor child => ∀ p : Fin H.vertexCount, child.Mem p → H.Lost ancestor p)
  nodup : chain.Pairwise (· ≠ ·)
  sound : ∀ B : CutPair H, B ∈ chain → H.ProperLoss B y
  complete_iff : ∀ B : CutPair H, B.fst < B.snd → (B ∈ chain ↔ H.ProperLoss B y)

theorem sweepPasses_correct_of_preds_spec {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat} {y : Fin H.vertexCount}
    (hPredSpec : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y →
      SweepChainSpec H (sweepChain H rank u) u) :
    ∀ B : CutPair H, sweepPasses H rank y B = true ↔
      ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost B u := by
  intro B
  unfold sweepPasses
  rw [allBool_eq_true_iff]
  constructor
  · intro hAll u hArc
    have hTest :
        (if decide (B.Mem u) then true
          else memCutPairBool B.canonical (sweepChain H rank u)) = true :=
      hAll u ((mem_preds_iff H y u).mpr hArc)
    by_cases hMemU : B.Mem u
    · exact mem_implies_lost H B hMemU
    · rw [ite_eq_right (fun hDec => hMemU (of_decide_eq_true hDec))] at hTest
      have hInChain : B.canonical ∈ sweepChain H rank u :=
        (memCutPairBool_eq_true_iff B.canonical (sweepChain H rank u)).mp hTest
      have hProperCan : H.ProperLoss B.canonical u :=
        (hPredSpec u hArc).sound B.canonical hInChain
      exact ((properLoss_canonical_iff H B u).mp hProperCan).1
  · intro hLostAll u huPred
    have hArc : H.HasQuotientArc u y := (mem_preds_iff H y u).mp huPred
    have hLostU : H.Lost B u := hLostAll u hArc
    by_cases hMemU : B.Mem u
    · exact ite_eq_left (decide_eq_true hMemU)
    · rw [ite_eq_right (fun hDec => hMemU (of_decide_eq_true hDec))]
      have hProperCan : H.ProperLoss B.canonical u :=
        (properLoss_canonical_iff H B u).mpr ⟨hLostU, hMemU⟩
      have hInChain : B.canonical ∈ sweepChain H rank u :=
        ((hPredSpec u hArc).complete_iff B.canonical (CutPair.canonical_lt B)).mpr hProperCan
      exact (memCutPairBool_eq_true_iff B.canonical (sweepChain H rank u)).mpr hInChain

private theorem sweepChain_spec_bounded {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    ∀ (bound : Nat) (y : Fin H.vertexCount),
      rank y < bound → SweepChainSpec H (sweepChain H rank y) y
  | 0, _, hLt => False.elim (by nomatch hLt)
  | bound + 1, y, hLt => by
      by_cases hy : y = H.root
      · rw [sweepChain_eq_of_eq_root H rank hy]
        refine ⟨(fun _ h => by nomatch h), List.Pairwise.nil, List.Pairwise.nil,
          (fun _ h => by nomatch h), ?_⟩
        intro B _
        constructor
        · intro h; nomatch h
        · intro hProp
          rw [hy] at hProp
          exact False.elim (not_properLoss_root H B hProp)
      · cases hRootArc : H.hasQuotientArcBool H.root y with
        | true =>
            have hArc : H.HasQuotientArc H.root y :=
              (hasQuotientArcBool_eq_true_iff H H.root y).mp hRootArc
            rw [sweepChain_eq_of_root_arc H rank hArc]
            refine ⟨(fun _ h => by nomatch h), List.Pairwise.nil, List.Pairwise.nil,
              (fun _ h => by nomatch h), ?_⟩
            intro B _
            constructor
            · intro h; nomatch h
            · intro hProp
              exact False.elim (not_properLoss_of_root_arc hArc hProp)
        | false =>
            have notRoot : H.root ≠ y := fun hEq => hy hEq.symm
            let ⟨m, hMax, hEntering, hLatest⟩ :=
              maxByRank_preds_of_flat rank flat notRoot
            have hPredSpec : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y →
                SweepChainSpec H (sweepChain H rank u) u := by
              intro u hArcUY
              have huLt : rank u < bound :=
                Nat.lt_of_lt_of_le (rankArc u y hArcUY) (Nat.le_of_succ_le_succ hLt)
              exact sweepChain_spec_bounded rankArc flat bound u huLt
            have specM : SweepChainSpec H (sweepChain H rank m) m :=
              hPredSpec m hEntering
            have hPassesCorrect : ∀ B : CutPair H, sweepPasses H rank y B = true ↔
                ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost B u :=
              sweepPasses_correct_of_preds_spec hPredSpec
            have hCandExact : ∀ B : CutPair H,
                candidatePairOfPreds H (preds H y) = some B ↔
                  B.fst < B.snd ∧ ∀ u : Fin H.vertexCount, H.HasQuotientArc u y ↔ B.Mem u :=
              candidatePairOfPreds_preds_iff H y
            have ⟨hNextNested, hNextIff⟩ :=
              sweep_step_preserves_proper_loss_labels rankArc flat notRoot hEntering hLatest
                (sweepChain H rank m) specM.nested specM.sound
                (fun B hOrd hProp => (specM.complete_iff B hOrd).mpr hProp)
                (sweepPasses H rank y) hPassesCorrect
                (candidatePairOfPreds H (preds H y)) hCandExact
            rw [sweepChain_eq_step rankArc hy hRootArc hMax hEntering]
            have hNextCan : ∀ B : CutPair H,
                B ∈ (sweepChain H rank m).takeWhile (sweepPasses H rank y) ++
                  (candidatePairOfPreds H (preds H y)).toList → B.fst < B.snd := by
              intro B hMem
              cases List.mem_append.mp hMem with
              | inl hPref =>
                  have hInM : B ∈ sweepChain H rank m :=
                    ((takeWhile_predecessor_losses_iff (sweepChain H rank m) specM.nested
                      (sweepPasses H rank y) hPassesCorrect B).mp hPref).1
                  exact specM.canonical B hInM
              | inr hCand =>
                  rw [Option.mem_toList] at hCand
                  exact ((hCandExact B).mp hCand).1
            have hNextSound : ∀ B : CutPair H,
                B ∈ (sweepChain H rank m).takeWhile (sweepPasses H rank y) ++
                  (candidatePairOfPreds H (preds H y)).toList → H.ProperLoss B y :=
              fun B hMem => (hNextIff B (hNextCan B hMem)).mp hMem
            have hNextNodup :
                ((sweepChain H rank m).takeWhile (sweepPasses H rank y) ++
                  (candidatePairOfPreds H (preds H y)).toList).Pairwise (· ≠ ·) := by
              refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
              · exact specM.nodup.sublist (by apply List.takeWhile_sublist)
              · cases candidatePairOfPreds H (preds H y) <;> simp
              · intro A hA B hB hEq
                have hAInM : A ∈ sweepChain H rank m :=
                  ((takeWhile_predecessor_losses_iff (sweepChain H rank m) specM.nested
                    (sweepPasses H rank y) hPassesCorrect A).mp hA).1
                have hmNotA : ¬ A.Mem m := (specM.sound A hAInM).2
                rw [Option.mem_toList, ← hEq] at hB
                have hmInA : A.Mem m := (((hCandExact A).mp hB).2 m).mp hEntering
                exact hmNotA hmInA
            exact ⟨hNextCan, hNextNested, hNextNodup, hNextSound, hNextIff⟩

/-- Global sweep chain theorem across all vertices of a flat acyclic quotient. -/
theorem sweepChain_spec {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (y : Fin H.vertexCount) :
    SweepChainSpec H (sweepChain H rank y) y :=
  sweepChain_spec_bounded rankArc flat (rank y + 1) y (Nat.lt_succ_self (rank y))

/-! ### Part 2a: Deduplicated effective keys, single stored parent key, and chain consistency -/

theorem length_keepBool_le {α : Type} (p : α → Bool) (l : List α) :
    (keepBool p l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      dsimp [keepBool]
      cases p x with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact Nat.le_trans ih (Nat.le_succ xs.length)
      | true =>
          simp only [↓reduceIte]
          exact Nat.succ_le_succ ih

theorem getLast?_concat {α : Type} :
    ∀ (l : List α) (x : α), (l ++ [x]).getLast? = some x
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: b :: cs, x => getLast?_concat (b :: cs) x

theorem mem_of_getLast?_eq_some {α : Type} :
    ∀ {l : List α} {x : α}, l.getLast? = some x → x ∈ l
  | [], _, h => False.elim (by nomatch h)
  | [_], _, h => List.mem_cons.mpr (Or.inl (Option.some.inj h).symm)
  | _ :: b :: cs, x, h => by
      have hSub : (b :: cs).getLast? = some x := h
      exact List.mem_cons.mpr (Or.inr (mem_of_getLast?_eq_some hSub))

theorem mem_of_mem_takeWhile {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : x ∈ l.takeWhile p) : x ∈ l := by
  induction l with
  | nil => nomatch h
  | cons a _ ih =>
      by_cases ha : p a = true
      · rw [List.takeWhile_cons_of_pos ha] at h
        cases List.mem_cons.mp h with
        | inl hEq => exact List.mem_cons.mpr (Or.inl hEq)
        | inr hTail => exact List.mem_cons.mpr (Or.inr (ih hTail))
      · rw [List.takeWhile_cons_of_neg ha] at h
        nomatch h

theorem takeWhile_append_singleton {α : Type} (p : α → Bool) (l : List α) (x : α) :
    (l ++ [x]).takeWhile p = l.takeWhile p ∨
      (l ++ [x]).takeWhile p = l ++ [x] := by
  induction l with
  | nil =>
      change ([x]).takeWhile p = [].takeWhile p ∨ ([x]).takeWhile p = [x]
      by_cases hx : p x = true
      · rw [List.takeWhile_cons_of_pos hx]
        exact Or.inr rfl
      · rw [List.takeWhile_cons_of_neg hx]
        exact Or.inl rfl
  | cons a as ih =>
      change (a :: (as ++ [x])).takeWhile p = (a :: as).takeWhile p ∨
        (a :: (as ++ [x])).takeWhile p = a :: (as ++ [x])
      by_cases ha : p a = true
      · rw [List.takeWhile_cons_of_pos ha, List.takeWhile_cons_of_pos ha]
        cases ih with
        | inl h₁ => exact Or.inl (congrArg (List.cons a) h₁)
        | inr h₂ => exact Or.inr (congrArg (List.cons a) h₂)
      · rw [List.takeWhile_cons_of_neg ha, List.takeWhile_cons_of_neg ha]
        exact Or.inl rfl

def findOpt {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs => if p x then some x else findOpt p xs

theorem findOpt_some_spec {α : Type} {p : α → Bool} {l : List α} {x : α}
    (h : findOpt p l = some x) : x ∈ l ∧ p x = true := by
  induction l with
  | nil => nomatch h
  | cons y _ ih =>
      dsimp [findOpt] at h
      cases hpy : p y with
      | true =>
          rw [hpy] at h
          simp only [↓reduceIte] at h
          have hEq : y = x := Option.some.inj h
          rw [← hEq]
          exact ⟨List.mem_cons.mpr (Or.inl rfl), hpy⟩
      | false =>
          rw [hpy] at h
          simp only [Bool.false_eq_true, ↓reduceIte] at h
          let ⟨hMem, hpx⟩ := ih h
          exact ⟨List.mem_cons.mpr (Or.inr hMem), hpx⟩

theorem findOpt_is_some_of_mem {α : Type} {p : α → Bool} {l : List α} {y : α}
    (hyMem : y ∈ l) (hpy : p y = true) : ∃ x : α, findOpt p l = some x := by
  induction l with
  | nil => nomatch hyMem
  | cons z _ ih =>
      dsimp [findOpt]
      cases hpz : p z with
      | true =>
          simp only [↓reduceIte]
          exact ⟨z, rfl⟩
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases List.mem_cons.mp hyMem with
          | inl hEq =>
              rw [hEq, hpz] at hpy
              nomatch hpy
          | inr hTail =>
              exact ih hTail

def filterMapOpt {α β : Type} (f : α → Option β) : List α → List β
  | [] => []
  | x :: xs =>
      match f x with
      | none => filterMapOpt f xs
      | some b => b :: filterMapOpt f xs

theorem mem_filterMapOpt_iff {α β : Type} (f : α → Option β) (l : List α) (b : β) :
    b ∈ filterMapOpt f l ↔ ∃ x : α, x ∈ l ∧ f x = some b := by
  induction l with
  | nil =>
      constructor
      · intro h; nomatch h
      · intro ⟨_, hMem, _⟩; nomatch hMem
  | cons x _ ih =>
      dsimp [filterMapOpt]
      cases hfx : f x with
      | none =>
          constructor
          · intro hTail
            let ⟨z, hzMem, hfz⟩ := ih.mp hTail
            exact ⟨z, List.mem_cons.mpr (Or.inr hzMem), hfz⟩
          · intro ⟨z, hzMem, hfz⟩
            cases List.mem_cons.mp hzMem with
            | inl hEq =>
                rw [hEq, hfx] at hfz
                nomatch hfz
            | inr hzTail =>
                exact ih.mpr ⟨z, hzTail, hfz⟩
      | some _ =>
          constructor
          · intro hMem
            cases List.mem_cons.mp hMem with
            | inl hEq =>
                rw [hEq]
                exact ⟨x, List.mem_cons.mpr (Or.inl rfl), hfx⟩
            | inr hTail =>
                let ⟨z, hzMem, hfz⟩ := ih.mp hTail
                exact ⟨z, List.mem_cons.mpr (Or.inr hzMem), hfz⟩
          · intro ⟨z, hzMem, hfz⟩
            cases List.mem_cons.mp hzMem with
            | inl hEq =>
                rw [hEq, hfx] at hfz
                exact List.mem_cons.mpr (Or.inl (Option.some.inj hfz).symm)
            | inr hzTail =>
                exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨z, hzTail, hfz⟩))

theorem length_filterMapOpt_le {α β : Type} (f : α → Option β) (l : List α) :
    (filterMapOpt f l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      dsimp [filterMapOpt]
      cases f x with
      | none => exact Nat.le_trans ih (Nat.le_succ xs.length)
      | some _ => exact Nat.succ_le_succ ih

def dedupFirst {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: keepBool (fun y => decide (y ≠ x)) (dedupFirst xs)

theorem mem_dedupFirst_iff {α : Type} [DecidableEq α] (l : List α) (a : α) :
    a ∈ dedupFirst l ↔ a ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons x xs ih =>
      dsimp [dedupFirst]
      constructor
      · intro hMem
        cases List.mem_cons.mp hMem with
        | inl hEq => exact List.mem_cons.mpr (Or.inl hEq)
        | inr hKeep =>
            have hInDedup : a ∈ dedupFirst xs :=
              ((mem_keepBool_iff (fun y => decide (y ≠ x)) (dedupFirst xs) a).mp hKeep).1
            exact List.mem_cons.mpr (Or.inr (ih.mp hInDedup))
      · intro hMem
        by_cases hax : a = x
        · exact List.mem_cons.mpr (Or.inl hax)
        · cases List.mem_cons.mp hMem with
          | inl hEq => exact False.elim (hax hEq)
          | inr hTail =>
              have hKeep : a ∈ keepBool (fun y => decide (y ≠ x)) (dedupFirst xs) :=
                (mem_keepBool_iff (fun y => decide (y ≠ x)) (dedupFirst xs) a).mpr
                  ⟨ih.mpr hTail, decide_eq_true hax⟩
              exact List.mem_cons.mpr (Or.inr hKeep)

theorem nodup_dedupFirst {α : Type} [DecidableEq α] (l : List α) :
    (dedupFirst l).Pairwise (· ≠ ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
      dsimp [dedupFirst]
      refine List.pairwise_cons.mpr ⟨?_, pairwise_keepBool _ ih⟩
      intro y hy
      have hDec : decide (y ≠ x) = true :=
        ((mem_keepBool_iff (fun z => decide (z ≠ x)) (dedupFirst xs) y).mp hy).2
      exact (of_decide_eq_true hDec).symm

theorem length_dedupFirst_le {α : Type} [DecidableEq α] (l : List α) :
    (dedupFirst l).length ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
      dsimp [dedupFirst]
      have hKeep :
          (keepBool (fun y => decide (y ≠ x)) (dedupFirst xs)).length ≤
            (dedupFirst xs).length :=
        length_keepBool_le _ (dedupFirst xs)
      exact Nat.succ_le_succ (Nat.le_trans hKeep ih)

/-! ### Topological vertex ordering and deduplicated effective keys -/

def insertByRank {n : Nat} (rank : Fin n → Nat) (x : Fin n) :
    List (Fin n) → List (Fin n)
  | [] => [x]
  | y :: ys =>
      if rank x ≤ rank y then
        x :: y :: ys
      else
        y :: insertByRank rank x ys

def sortByRank {n : Nat} (rank : Fin n → Nat) : List (Fin n) → List (Fin n)
  | [] => []
  | x :: xs => insertByRank rank x (sortByRank rank xs)

theorem length_insertByRank {n : Nat} (rank : Fin n → Nat) (x : Fin n)
    (l : List (Fin n)) :
    (insertByRank rank x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons y _ ih =>
      dsimp [insertByRank]
      by_cases hle : rank x ≤ rank y
      · rw [ite_eq_left hle]
        rfl
      · rw [ite_eq_right hle]
        exact congrArg Nat.succ ih

theorem length_sortByRank {n : Nat} (rank : Fin n → Nat) (l : List (Fin n)) :
    (sortByRank rank l).length = l.length := by
  induction l with
  | nil => rfl
  | cons _ _ ih =>
      dsimp [sortByRank]
      rw [length_insertByRank, ih]

theorem mem_insertByRank_iff {n : Nat} (rank : Fin n → Nat) (x : Fin n)
    (l : List (Fin n)) (u : Fin n) :
    u ∈ insertByRank rank x l ↔ u = x ∨ u ∈ l := by
  induction l with
  | nil =>
      dsimp [insertByRank]
      exact List.mem_cons
  | cons y _ ih =>
      dsimp [insertByRank]
      by_cases hle : rank x ≤ rank y
      · rw [ite_eq_left hle]
        exact List.mem_cons
      · rw [ite_eq_right hle]
        constructor
        · intro hMem
          cases List.mem_cons.mp hMem with
          | inl hEq => exact Or.inr (List.mem_cons.mpr (Or.inl hEq))
          | inr hTail =>
              cases ih.mp hTail with
              | inl hux => exact Or.inl hux
              | inr hInYs => exact Or.inr (List.mem_cons.mpr (Or.inr hInYs))
        · intro hOr
          cases hOr with
          | inl hux =>
              exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inl hux)))
          | inr hInCons =>
              cases List.mem_cons.mp hInCons with
              | inl huy => exact List.mem_cons.mpr (Or.inl huy)
              | inr hInYs =>
                  exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inr hInYs)))

theorem mem_sortByRank_iff {n : Nat} (rank : Fin n → Nat) (l : List (Fin n))
    (u : Fin n) : u ∈ sortByRank rank l ↔ u ∈ l := by
  induction l with
  | nil => exact Iff.rfl
  | cons _ _ ih =>
      dsimp [sortByRank]
      rw [mem_insertByRank_iff, ih]
      exact List.mem_cons.symm

theorem pairwise_le_insertByRank {n : Nat} (rank : Fin n → Nat) (x : Fin n)
    {l : List (Fin n)} (hl : l.Pairwise (fun a b => rank a ≤ rank b)) :
    (insertByRank rank x l).Pairwise (fun a b => rank a ≤ rank b) := by
  revert hl
  induction l with
  | nil =>
      intro _
      exact List.pairwise_cons.mpr ⟨(fun _ h => by nomatch h), List.Pairwise.nil⟩
  | cons y ys ih =>
      intro hl
      let ⟨hyLe, hysSort⟩ := List.pairwise_cons.mp hl
      dsimp [insertByRank]
      by_cases hle : rank x ≤ rank y
      · rw [ite_eq_left hle]
        refine List.pairwise_cons.mpr ⟨?_, hl⟩
        intro z hz
        cases List.mem_cons.mp hz with
        | inl hzy => rw [hzy]; exact hle
        | inr hzYs => exact Nat.le_trans hle (hyLe z hzYs)
      · rw [ite_eq_right hle]
        have hyx : rank y ≤ rank x := nat_le_of_not_le hle
        refine List.pairwise_cons.mpr ⟨?_, ih hysSort⟩
        intro z hz
        cases (mem_insertByRank_iff rank x ys z).mp hz with
        | inl hzx => rw [hzx]; exact hyx
        | inr hzYs => exact hyLe z hzYs

theorem pairwise_le_sortByRank {n : Nat} (rank : Fin n → Nat) (l : List (Fin n)) :
    (sortByRank rank l).Pairwise (fun a b => rank a ≤ rank b) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x _ ih => exact pairwise_le_insertByRank rank x ih

/-- Vertices of `H` sorted in nondecreasing `rank` order. -/
def topoVertices (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    List (Fin H.vertexCount) :=
  sortByRank rank (finElems H.vertexCount)

theorem mem_topoVertices (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (v : Fin H.vertexCount) : v ∈ topoVertices H rank :=
  (mem_sortByRank_iff rank (finElems H.vertexCount) v).mpr (mem_finElems v)

theorem length_topoVertices (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    (topoVertices H rank).length = H.vertexCount := by
  unfold topoVertices
  rw [length_sortByRank, length_finElems]

theorem pairwise_le_topoVertices (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    (topoVertices H rank).Pairwise (fun a b => rank a ≤ rank b) :=
  pairwise_le_sortByRank rank (finElems H.vertexCount)

/-- Raw candidate canonical two-predecessor keys emitted across `topoVertices`. -/
def rawCandidatePairs (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    List (CutPair H) :=
  filterMapOpt (sweepCandidate H) (topoVertices H rank)

/-- Deduplicated canonical real forest keys in topological encounter order. -/
def realKeys (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    List (CutPair H) :=
  dedupFirst (rawCandidatePairs H rank)

theorem nodup_realKeys (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    (realKeys H rank).Pairwise (· ≠ ·) :=
  nodup_dedupFirst (rawCandidatePairs H rank)

theorem length_realKeys_le (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    (realKeys H rank).length ≤ H.vertexCount := by
  have h₁ : (realKeys H rank).length ≤ (rawCandidatePairs H rank).length :=
    length_dedupFirst_le (rawCandidatePairs H rank)
  have h₂ : (rawCandidatePairs H rank).length ≤ (topoVertices H rank).length :=
    length_filterMapOpt_le (sweepCandidate H) (topoVertices H rank)
  rw [length_topoVertices H rank] at h₂
  exact Nat.le_trans h₁ h₂

theorem sweepCandidate_some_elim {H : LabelledQuotient} {y : Fin H.vertexCount}
    {B : CutPair H} (h : sweepCandidate H y = some B) :
    y ≠ H.root ∧
      H.hasQuotientArcBool H.root y = false ∧
      candidatePairOfPreds H (preds H y) = some B := by
  unfold sweepCandidate at h
  by_cases hy : y = H.root
  · rw [ite_eq_left hy] at h
    nomatch h
  · rw [ite_eq_right hy] at h
    cases hArc : H.hasQuotientArcBool H.root y with
    | true =>
        rw [hArc] at h
        simp only [↓reduceIte] at h
        nomatch h
    | false =>
        rw [hArc] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        exact ⟨hy, rfl, h⟩

theorem sweepCandidate_eq_some_of_endpoints {H : LabelledQuotient}
    {y : Fin H.vertexCount} {B : CutPair H}
    (hy : y ≠ H.root) (hOrder : B.fst < B.snd)
    (hArcIff : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y ↔ B.Mem u) :
    sweepCandidate H y = some B := by
  have hNoRootArc : H.hasQuotientArcBool H.root y = false := by
    cases hBool : H.hasQuotientArcBool H.root y with
    | false => rfl
    | true =>
        have hRootMem : B.Mem H.root :=
          (hArcIff H.root).mp ((hasQuotientArcBool_eq_true_iff H H.root y).mp hBool)
        cases hRootMem with
        | inl h₁ => exact False.elim (B.fst_ne_root h₁.symm)
        | inr h₂ => exact False.elim (B.snd_ne_root h₂.symm)
  unfold sweepCandidate
  rw [ite_eq_right hy, hNoRootArc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact (candidatePairOfPreds_preds_iff H y B).mpr ⟨hOrder, hArcIff⟩

theorem canonical_of_mem_realKeys {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat} {B : CutPair H}
    (hMem : B ∈ realKeys H rank) : B.fst < B.snd := by
  have hRaw : B ∈ rawCandidatePairs H rank :=
    (mem_dedupFirst_iff (rawCandidatePairs H rank) B).mp hMem
  let ⟨y, _, hCandY⟩ :=
    (mem_filterMapOpt_iff (sweepCandidate H) (topoVertices H rank) B).mp hRaw
  let ⟨_, _, hPredCand⟩ := sweepCandidate_some_elim hCandY
  exact ((candidatePairOfPreds_preds_iff H y B).mp hPredCand).1

/-- Exact correspondence between `realKeys` and canonical pairs `B` with `J(B) ≠ ∅`. -/
theorem mem_realKeys_iff {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (B : CutPair H) :
    B ∈ realKeys H rank ↔
      B.fst < B.snd ∧ ∃ y : Fin H.vertexCount, H.ProperLoss B y := by
  constructor
  · intro hMem
    have hRaw : B ∈ rawCandidatePairs H rank :=
      (mem_dedupFirst_iff (rawCandidatePairs H rank) B).mp hMem
    let ⟨y, _, hCandY⟩ :=
      (mem_filterMapOpt_iff (sweepCandidate H) (topoVertices H rank) B).mp hRaw
    let ⟨hy, hNoRootArc, hPredCand⟩ := sweepCandidate_some_elim hCandY
    have hOrder : B.fst < B.snd :=
      ((candidatePairOfPreds_preds_iff H y B).mp hPredCand).1
    let ⟨m, hMax, hEntering, _⟩ :=
      maxByRank_preds_of_flat rank flat (fun hEq => hy hEq.symm)
    have hStep := sweepChain_eq_step rankArc hy hNoRootArc hMax hEntering
    have hInChain : B ∈ sweepChain H rank y := by
      rw [hStep, hPredCand]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    exact ⟨hOrder, ⟨y, (sweepChain_spec rankArc flat y).sound B hInChain⟩⟩
  · intro ⟨hOrder, ⟨y₀, hProper₀⟩⟩
    have hy₀InLosses :
        y₀ ∈ keepBool (fun v => memCutPairBool B (sweepChain H rank v))
          (topoVertices H rank) := by
      refine (mem_keepBool_iff _ (topoVertices H rank) y₀).mpr ⟨mem_topoVertices H rank y₀, ?_⟩
      exact (memCutPairBool_eq_true_iff B (sweepChain H rank y₀)).mpr
        (((sweepChain_spec rankArc flat y₀).complete_iff B hOrder).mpr hProper₀)
    have hLossesSort :
        (keepBool (fun v => memCutPairBool B (sweepChain H rank v))
          (topoVertices H rank)).Pairwise (fun a b => rank a ≤ rank b) :=
      pairwise_keepBool _ (pairwise_le_topoVertices H rank)
    cases hEqLosses :
        keepBool (fun v => memCutPairBool B (sweepChain H rank v)) (topoVertices H rank) with
    | nil =>
        rw [hEqLosses] at hy₀InLosses
        nomatch hy₀InLosses
    | cons yStar rest =>
        rw [hEqLosses] at hLossesSort
        let ⟨hStarLeRest, _⟩ := List.pairwise_cons.mp hLossesSort
        have hyStarMem :
            yStar ∈ keepBool (fun v => memCutPairBool B (sweepChain H rank v))
              (topoVertices H rank) := by
          rw [hEqLosses]
          exact List.mem_cons.mpr (Or.inl rfl)
        have hBInStar : B ∈ sweepChain H rank yStar :=
          (memCutPairBool_eq_true_iff B (sweepChain H rank yStar)).mp
            ((mem_keepBool_iff _ (topoVertices H rank) yStar).mp hyStarMem).2
        have hProperStar : H.ProperLoss B yStar :=
          (sweepChain_spec rankArc flat yStar).sound B hBInStar
        have hFirst : ∀ v : Fin H.vertexCount, H.ProperLoss B v → rank yStar ≤ rank v := by
          intro v hProperV
          have hvInLosses :
              v ∈ keepBool (fun w => memCutPairBool B (sweepChain H rank w))
                (topoVertices H rank) := by
            refine (mem_keepBool_iff _ (topoVertices H rank) v).mpr ⟨mem_topoVertices H rank v, ?_⟩
            exact (memCutPairBool_eq_true_iff B (sweepChain H rank v)).mpr
              (((sweepChain_spec rankArc flat v).complete_iff B hOrder).mpr hProperV)
          rw [hEqLosses] at hvInLosses
          cases List.mem_cons.mp hvInLosses with
          | inl hvEq => rw [hvEq]; exact Nat.le_refl _
          | inr hvRest => exact hStarLeRest v hvRest
        have hArcIff : ∀ u : Fin H.vertexCount, H.HasQuotientArc u yStar ↔ B.Mem u :=
          predecessors_iff_endpoints_of_first_properLoss rankArc flat hProperStar hFirst
        have hyStarNeRoot : yStar ≠ H.root := fun hEq => by
          rw [hEq] at hProperStar
          exact not_properLoss_root H B hProperStar
        have hCandStar : sweepCandidate H yStar = some B :=
          sweepCandidate_eq_some_of_endpoints hyStarNeRoot hOrder hArcIff
        have hRaw : B ∈ rawCandidatePairs H rank :=
          (mem_filterMapOpt_iff (sweepCandidate H) (topoVertices H rank) B).mpr
            ⟨yStar, mem_topoVertices H rank yStar, hCandStar⟩
        exact (mem_dedupFirst_iff (rawCandidatePairs H rank) B).mpr hRaw

/-! ### Single stored parent on pair keys and pair-key reuse consistency -/

def witnessVertex? (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (P : CutPair H) : Option (Fin H.vertexCount) :=
  findOpt (fun y => decide (sweepCandidate H y = some P)) (topoVertices H rank)

def parentOfWitness (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (z : Fin H.vertexCount) : Option (CutPair H) :=
  match maxByRank rank (preds H z) with
  | none => none
  | some m => ((sweepChain H rank m).takeWhile (sweepPasses H rank z)).getLast?

def storedParentKey? (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (P : CutPair H) : Option (CutPair H) :=
  match witnessVertex? H rank P with
  | none => none
  | some z => parentOfWitness H rank z

def pairMaxRank {H : LabelledQuotient} (rank : Fin H.vertexCount → Nat)
    (B : CutPair H) : Nat :=
  if rank B.fst ≤ rank B.snd then rank B.snd else rank B.fst

theorem rank_le_pairMaxRank_of_mem {H : LabelledQuotient}
    (rank : Fin H.vertexCount → Nat) {B : CutPair H} {u : Fin H.vertexCount}
    (hu : B.Mem u) : rank u ≤ pairMaxRank rank B := by
  unfold pairMaxRank
  by_cases hle : rank B.fst ≤ rank B.snd
  · rw [ite_eq_left hle]
    cases hu with
    | inl h₁ => rw [h₁]; exact hle
    | inr h₂ => rw [h₂]; exact Nat.le_refl _
  · rw [ite_eq_right hle]
    cases hu with
    | inl h₁ => rw [h₁]; exact Nat.le_refl _
    | inr h₂ => rw [h₂]; exact nat_le_of_not_le hle

theorem pairMaxRank_lt_of_endpoints_lt {H : LabelledQuotient}
    (rank : Fin H.vertexCount → Nat) {B : CutPair H} {r : Nat}
    (h₁ : rank B.fst < r) (h₂ : rank B.snd < r) :
    pairMaxRank rank B < r := by
  unfold pairMaxRank
  by_cases hle : rank B.fst ≤ rank B.snd
  · rw [ite_eq_left hle]; exact h₂
  · rw [ite_eq_right hle]; exact h₁

theorem storedParentKey?_some_props {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {P B : CutPair H}
    (hPar : storedParentKey? H rank P = some B) :
    B ∈ realKeys H rank ∧
      pairMaxRank rank B < pairMaxRank rank P ∧
      (∀ p : Fin H.vertexCount, P.Mem p → H.Lost B p) := by
  unfold storedParentKey? at hPar
  cases hw : witnessVertex? H rank P with
  | none =>
      rw [hw] at hPar
      nomatch hPar
  | some z =>
      rw [hw] at hPar
      have hCandZ : sweepCandidate H z = some P :=
        of_decide_eq_true (findOpt_some_spec hw).2
      let ⟨hzNeRoot, hNoRootArcZ, hPredCandZ⟩ := sweepCandidate_some_elim hCandZ
      have hKeyZ : ∀ u : Fin H.vertexCount, H.HasQuotientArc u z ↔ P.Mem u :=
        ((candidatePairOfPreds_preds_iff H z P).mp hPredCandZ).2
      unfold parentOfWitness at hPar
      dsimp only at hPar
      cases hMaxZ : maxByRank rank (preds H z) with
      | none =>
          rw [hMaxZ] at hPar
          nomatch hPar
      | some m =>
          rw [hMaxZ] at hPar
          let ⟨m', hMaxZ', hEnteringZ', _⟩ :=
            maxByRank_preds_of_flat rank flat (fun hEq => hzNeRoot hEq.symm)
          have hmEq : m = m' := Option.some.inj (hMaxZ.symm.trans hMaxZ')
          have hEnteringZ : H.HasQuotientArc m z := by rw [hmEq]; exact hEnteringZ'
          have hBInPref : B ∈ (sweepChain H rank m).takeWhile (sweepPasses H rank z) :=
            mem_of_getLast?_eq_some hPar
          have hBInM : B ∈ sweepChain H rank m := mem_of_mem_takeWhile hBInPref
          have specM := sweepChain_spec rankArc flat m
          have hBCan : B.fst < B.snd := specM.canonical B hBInM
          have hProperBM : H.ProperLoss B m := specM.sound B hBInM
          have hBReal : B ∈ realKeys H rank :=
            (mem_realKeys_iff rankArc flat B).mpr ⟨hBCan, ⟨m, hProperBM⟩⟩
          have hRankFst : rank B.fst < rank m :=
            properLoss_follows_endpoints rankArc flat hProperBM (Or.inl rfl)
          have hRankSnd : rank B.snd < rank m :=
            properLoss_follows_endpoints rankArc flat hProperBM (Or.inr rfl)
          have hmMemP : P.Mem m := (hKeyZ m).mp hEnteringZ
          have hMaxLt : pairMaxRank rank B < pairMaxRank rank P :=
            Nat.lt_of_lt_of_le
              (pairMaxRank_lt_of_endpoints_lt rank hRankFst hRankSnd)
              (rank_le_pairMaxRank_of_mem rank hmMemP)
          have hStepZ := sweepChain_eq_step rankArc hzNeRoot hNoRootArcZ hMaxZ hEnteringZ
          have hNestedZ := (sweepChain_spec rankArc flat z).nested
          rw [hStepZ, hPredCandZ] at hNestedZ
          have hCross := (List.pairwise_append.mp hNestedZ).2.2
          have hEndpointsLost : ∀ p : Fin H.vertexCount, P.Mem p → H.Lost B p :=
            hCross B hBInPref P (List.mem_cons.mpr (Or.inl rfl))
          exact ⟨hBReal, hMaxLt, hEndpointsLost⟩

/-- Reused-key parent agreement: every vertex emitting `some P` computes the same immediate parent. -/
theorem storedParentKey?_eq_at_candidate {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) {y mY : Fin H.vertexCount} {P : CutPair H}
    (hCandY : sweepCandidate H y = some P)
    (hMaxY : maxByRank rank (preds H y) = some mY) :
    ((sweepChain H rank mY).takeWhile (sweepPasses H rank y)).getLast? =
      storedParentKey? H rank P := by
  let ⟨z, hzFind⟩ :=
    findOpt_is_some_of_mem (p := fun w => decide (sweepCandidate H w = some P))
      (mem_topoVertices H rank y) (decide_eq_true hCandY)
  have hCandZ : sweepCandidate H z = some P :=
    of_decide_eq_true (findOpt_some_spec hzFind).2
  let ⟨hyNeRoot, _, hPredCandY⟩ := sweepCandidate_some_elim hCandY
  let ⟨hzNeRoot, _, hPredCandZ⟩ := sweepCandidate_some_elim hCandZ
  have keyY : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y ↔ P.Mem u :=
    ((candidatePairOfPreds_preds_iff H y P).mp hPredCandY).2
  have keyZ : ∀ u : Fin H.vertexCount, H.HasQuotientArc u z ↔ P.Mem u :=
    ((candidatePairOfPreds_preds_iff H z P).mp hPredCandZ).2
  let ⟨mY', hMaxY', hEdgeY', hLatestY'⟩ :=
    maxByRank_preds_of_flat rank flat (fun hEq => hyNeRoot hEq.symm)
  have hmYEq : mY = mY' := Option.some.inj (hMaxY.symm.trans hMaxY')
  have hEdgeY : H.HasQuotientArc mY y := by rw [hmYEq]; exact hEdgeY'
  have hLatestY : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → rank u ≤ rank mY := by
    rw [hmYEq]; exact hLatestY'
  let ⟨mZ, hMaxZ, hEdgeZ, hLatestZ⟩ :=
    maxByRank_preds_of_flat rank flat (fun hEq => hzNeRoot hEq.symm)
  have correctY : ∀ B : CutPair H, sweepPasses H rank y B = true ↔
      ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost B u :=
    sweepPasses_correct_of_preds_spec (fun u _ => sweepChain_spec rankArc flat u)
  have correctZ : ∀ B : CutPair H, sweepPasses H rank z B = true ↔
      ∀ u : Fin H.vertexCount, H.HasQuotientArc u z → H.Lost B u :=
    sweepPasses_correct_of_preds_spec (fun u _ => sweepChain_spec rankArc flat u)
  change witnessVertex? H rank P = some z at hzFind
  unfold storedParentKey?
  rw [hzFind]
  unfold parentOfWitness
  dsimp only
  rw [hMaxZ]
  exact sweep_parent_eq_for_reused_pair_key distinctRanks (sweepChain H rank)
    keyY keyZ hEdgeY hEdgeZ hLatestY hLatestZ
    (sweepPasses H rank y) (sweepPasses H rank z) correctY correctZ

/-! ### Root-to-node key chains under `storedParentKey?` -/

def parentKeyChainAux (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    Nat → Option (CutPair H) → List (CutPair H)
  | _, none => []
  | 0, some _ => []
  | fuel + 1, some P =>
      parentKeyChainAux H rank fuel (storedParentKey? H rank P) ++ [P]

def parentKeyChain (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat) :
    Option (CutPair H) → List (CutPair H)
  | none => []
  | some P => parentKeyChainAux H rank (pairMaxRank rank P + 1) (some P)

theorem parentKeyChainAux_eq_of_gt {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    ∀ {f₁ f₂ : Nat} {P : CutPair H},
      pairMaxRank rank P < f₁ → pairMaxRank rank P < f₂ →
      parentKeyChainAux H rank f₁ (some P) = parentKeyChainAux H rank f₂ (some P)
  | 0, _, _, h₁, _ => False.elim (by nomatch h₁)
  | _ + 1, 0, _, _, h₂ => False.elim (by nomatch h₂)
  | f₁ + 1, f₂ + 1, P, h₁, h₂ => by
      dsimp [parentKeyChainAux]
      cases hPar : storedParentKey? H rank P with
      | none => cases f₁ <;> cases f₂ <;> rfl
      | some B =>
          have hBLt : pairMaxRank rank B < pairMaxRank rank P :=
            (storedParentKey?_some_props rankArc flat hPar).2.1
          have hB₁ : pairMaxRank rank B < f₁ :=
            Nat.lt_of_lt_of_le hBLt (Nat.le_of_succ_le_succ h₁)
          have hB₂ : pairMaxRank rank B < f₂ :=
            Nat.lt_of_lt_of_le hBLt (Nat.le_of_succ_le_succ h₂)
          rw [parentKeyChainAux_eq_of_gt rankArc flat hB₁ hB₂]

theorem parentKeyChain_some_eq {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (P : CutPair H) :
    parentKeyChain H rank (some P) =
      parentKeyChain H rank (storedParentKey? H rank P) ++ [P] := by
  change parentKeyChainAux H rank (pairMaxRank rank P + 1) (some P) = _
  dsimp [parentKeyChainAux]
  cases hPar : storedParentKey? H rank P with
  | none => cases pairMaxRank rank P <;> rfl
  | some B =>
      dsimp [parentKeyChain]
      have hBLt : pairMaxRank rank B < pairMaxRank rank P :=
        (storedParentKey?_some_props rankArc flat hPar).2.1
      rw [parentKeyChainAux_eq_of_gt rankArc flat hBLt (Nat.lt_succ_self (pairMaxRank rank B))]

theorem getLast?_parentKeyChain {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (opt : Option (CutPair H)) :
    (parentKeyChain H rank opt).getLast? = opt := by
  cases opt with
  | none => rfl
  | some P =>
      rw [parentKeyChain_some_eq rankArc flat P, getLast?_concat]

private theorem takeWhile_parentKeyChain_bounded {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (p : CutPair H → Bool) :
    ∀ (bound : Nat) (P : CutPair H),
      pairMaxRank rank P < bound →
      (parentKeyChain H rank (some P)).takeWhile p =
        parentKeyChain H rank ((parentKeyChain H rank (some P)).takeWhile p).getLast?
  | 0, _, hLt => False.elim (by nomatch hLt)
  | bound + 1, P, hLt => by
      have hUnfold := parentKeyChain_some_eq rankArc flat P
      cases takeWhile_append_singleton p
          (parentKeyChain H rank (storedParentKey? H rank P)) P with
      | inl hPref =>
          rw [hUnfold, hPref]
          cases hPar : storedParentKey? H rank P with
          | none =>
              rfl
          | some B =>
              have hBLt : pairMaxRank rank B < bound :=
                Nat.lt_of_lt_of_le
                  (storedParentKey?_some_props rankArc flat hPar).2.1
                  (Nat.le_of_succ_le_succ hLt)
              exact takeWhile_parentKeyChain_bounded rankArc flat p bound B hBLt
      | inr hFull =>
          have hTwEq : (parentKeyChain H rank (some P)).takeWhile p =
              parentKeyChain H rank (some P) := by
            rw [hUnfold]
            exact hFull
          rw [hTwEq, getLast?_parentKeyChain rankArc flat (some P)]

theorem takeWhile_parentKeyChain {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (p : CutPair H → Bool) (opt : Option (CutPair H)) :
    (parentKeyChain H rank opt).takeWhile p =
      parentKeyChain H rank ((parentKeyChain H rank opt).takeWhile p).getLast? := by
  cases opt with
  | none => rfl
  | some P =>
      exact takeWhile_parentKeyChain_bounded rankArc flat p
        (pairMaxRank rank P + 1) P (Nat.lt_succ_self (pairMaxRank rank P))

def vertexLabelKey? (H : LabelledQuotient) (rank : Fin H.vertexCount → Nat)
    (y : Fin H.vertexCount) : Option (CutPair H) :=
  (sweepChain H rank y).getLast?

private theorem sweepChain_eq_parentKeyChain_bounded {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) :
    ∀ (bound : Nat) (y : Fin H.vertexCount),
      rank y < bound →
      sweepChain H rank y = parentKeyChain H rank (vertexLabelKey? H rank y)
  | 0, _, hLt => False.elim (by nomatch hLt)
  | bound + 1, y, hLt => by
      by_cases hy : y = H.root
      · unfold vertexLabelKey?
        rw [sweepChain_eq_of_eq_root H rank hy]
        rfl
      · cases hRootArc : H.hasQuotientArcBool H.root y with
        | true =>
            have hArc : H.HasQuotientArc H.root y :=
              (hasQuotientArcBool_eq_true_iff H H.root y).mp hRootArc
            unfold vertexLabelKey?
            rw [sweepChain_eq_of_root_arc H rank hArc]
            rfl
        | false =>
            let ⟨m, hMax, hEntering, _⟩ :=
              maxByRank_preds_of_flat rank flat (fun hEq => hy hEq.symm)
            have hmLt : rank m < bound :=
              Nat.lt_of_lt_of_le (rankArc m y hEntering) (Nat.le_of_succ_le_succ hLt)
            have ihM : sweepChain H rank m = parentKeyChain H rank (vertexLabelKey? H rank m) :=
              sweepChain_eq_parentKeyChain_bounded rankArc distinctRanks flat bound m hmLt
            have hStep := sweepChain_eq_step rankArc hy hRootArc hMax hEntering
            have hCandEq : candidatePairOfPreds H (preds H y) = sweepCandidate H y := by
              unfold sweepCandidate
              rw [ite_eq_right hy, hRootArc]
              simp only [Bool.false_eq_true, ↓reduceIte]
            rw [hCandEq] at hStep
            cases hCand : sweepCandidate H y with
            | none =>
                rw [hCand] at hStep
                have hStepNil :
                    sweepChain H rank y =
                      (sweepChain H rank m).takeWhile (sweepPasses H rank y) := by
                  rw [hStep]
                  exact List.append_nil _
                unfold vertexLabelKey?
                rw [hStepNil, ihM]
                exact takeWhile_parentKeyChain rankArc flat
                  (sweepPasses H rank y) (vertexLabelKey? H rank m)
            | some P =>
                have hParEq :
                    ((sweepChain H rank m).takeWhile (sweepPasses H rank y)).getLast? =
                      storedParentKey? H rank P :=
                  storedParentKey?_eq_at_candidate rankArc distinctRanks flat hCand hMax
                have hPrefChain :
                    (sweepChain H rank m).takeWhile (sweepPasses H rank y) =
                      parentKeyChain H rank (storedParentKey? H rank P) := by
                  rw [← hParEq, ihM]
                  exact takeWhile_parentKeyChain rankArc flat
                    (sweepPasses H rank y) (vertexLabelKey? H rank m)
                rw [hCand] at hStep
                have hLabelP : vertexLabelKey? H rank y = some P := by
                  unfold vertexLabelKey?
                  rw [hStep]
                  exact getLast?_concat _ P
                rw [hLabelP, hStep, hPrefChain, parentKeyChain_some_eq rankArc flat P]
                rfl

theorem sweepChain_eq_parentKeyChain {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) (y : Fin H.vertexCount) :
    sweepChain H rank y = parentKeyChain H rank (vertexLabelKey? H rank y) :=
  sweepChain_eq_parentKeyChain_bounded rankArc distinctRanks flat
    (rank y + 1) y (Nat.lt_succ_self (rank y))

/-! ### Part 2b: Indexed `ProperLossForest`, `IsForestAncestor`, and Lemma 3.1 theorem suite -/

def listGetFin {α : Type} : (l : List α) → Fin l.length → α
  | x :: _, ⟨0, _⟩ => x
  | _ :: xs, ⟨k + 1, hk⟩ => listGetFin xs ⟨k, Nat.le_of_succ_le_succ hk⟩

theorem listGetFin_mem {α : Type} :
    ∀ (l : List α) (i : Fin l.length), listGetFin l i ∈ l
  | _ :: _, ⟨0, _⟩ => List.mem_cons.mpr (Or.inl rfl)
  | _ :: xs, ⟨k + 1, hk⟩ =>
      List.mem_cons.mpr (Or.inr (listGetFin_mem xs ⟨k, Nat.le_of_succ_le_succ hk⟩))

def findFinIdx {α : Type} [DecidableEq α] (target : α) :
    (l : List α) → Option (Fin l.length)
  | [] => none
  | x :: xs =>
      if target = x then
        some ⟨0, Nat.zero_lt_succ xs.length⟩
      else
        match findFinIdx target xs with
        | none => none
        | some i => some ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

theorem findFinIdx_of_mem {α : Type} [DecidableEq α] {target : α} :
    ∀ {l : List α}, target ∈ l →
      ∃ i : Fin l.length, findFinIdx target l = some i ∧ listGetFin l i = target
  | [], hMem => False.elim (by nomatch hMem)
  | x :: xs, hMem => by
      dsimp [findFinIdx]
      by_cases htx : target = x
      · rw [ite_eq_left htx]
        exact ⟨⟨0, Nat.zero_lt_succ xs.length⟩, rfl, htx.symm⟩
      · rw [ite_eq_right htx]
        cases List.mem_cons.mp hMem with
        | inl hEq => exact False.elim (htx hEq)
        | inr hTail =>
            let ⟨i, hiFind, hiGet⟩ := findFinIdx_of_mem hTail
            rw [hiFind]
            refine ⟨⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩, rfl, ?_⟩
            dsimp [listGetFin]
            exact hiGet

theorem findFinIdx_listGetFin {α : Type} [DecidableEq α] :
    ∀ {l : List α}, l.Pairwise (· ≠ ·) →
      ∀ (i : Fin l.length), findFinIdx (listGetFin l i) l = some i
  | [], _, ⟨_, isLt⟩ => False.elim (by nomatch isLt)
  | x :: xs, _, ⟨0, h0⟩ => by
      have hGet : listGetFin (x :: xs) ⟨0, h0⟩ = x := rfl
      rw [hGet]
      dsimp [findFinIdx]
      rw [ite_eq_left rfl]
  | x :: xs, hl, ⟨k + 1, hk⟩ => by
      let ⟨hxNe, hxsNodup⟩ := List.pairwise_cons.mp hl
      let i' : Fin xs.length := ⟨k, Nat.le_of_succ_le_succ hk⟩
      have hTargetMem : listGetFin xs i' ∈ xs := listGetFin_mem xs i'
      have hNeX : listGetFin xs i' ≠ x :=
        (hxNe (listGetFin xs i') hTargetMem).symm
      dsimp [listGetFin, findFinIdx]
      rw [ite_eq_right hNeX, findFinIdx_listGetFin hxsNodup i']

def nodeKeyOfList? {H : LabelledQuotient} (keys : List (CutPair H)) :
    Fin (keys.length + 1) → Option (CutPair H)
  | ⟨0, _⟩ => none
  | ⟨k + 1, hk⟩ => some (listGetFin keys ⟨k, Nat.le_of_succ_le_succ hk⟩)

def nodeOfOptKeyList {H : LabelledQuotient} (keys : List (CutPair H)) :
    Option (CutPair H) → Fin (keys.length + 1)
  | none => ⟨0, Nat.zero_lt_succ keys.length⟩
  | some B =>
      match findFinIdx B keys with
      | none => ⟨0, Nat.zero_lt_succ keys.length⟩
      | some i => ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

theorem nodeKeyOfList?_mem {H : LabelledQuotient} {keys : List (CutPair H)} :
    ∀ {u : Fin (keys.length + 1)} {B : CutPair H},
      nodeKeyOfList? keys u = some B → B ∈ keys
  | ⟨0, _⟩, _, h => False.elim (by nomatch h)
  | ⟨k + 1, hk⟩, _, h => by
      have hEq := Option.some.inj h
      rw [← hEq]
      exact listGetFin_mem keys ⟨k, Nat.le_of_succ_le_succ hk⟩

theorem nodeOfOptKeyList_nodeKeyOfList? {H : LabelledQuotient}
    {keys : List (CutPair H)} (hNodup : keys.Pairwise (· ≠ ·)) :
    ∀ (u : Fin (keys.length + 1)),
      nodeOfOptKeyList keys (nodeKeyOfList? keys u) = u
  | ⟨0, _⟩ => fin_eq_of_val_eq rfl
  | ⟨k + 1, hk⟩ => by
      let i : Fin keys.length := ⟨k, Nat.le_of_succ_le_succ hk⟩
      dsimp [nodeKeyOfList?, nodeOfOptKeyList]
      rw [findFinIdx_listGetFin hNodup i]

theorem nodeKeyOfList?_inj {H : LabelledQuotient}
    {keys : List (CutPair H)} (hNodup : keys.Pairwise (· ≠ ·))
    {u v : Fin (keys.length + 1)}
    (hEq : nodeKeyOfList? keys u = nodeKeyOfList? keys v) : u = v := by
  have hNode := congrArg (nodeOfOptKeyList keys) hEq
  rw [nodeOfOptKeyList_nodeKeyOfList? hNodup u,
    nodeOfOptKeyList_nodeKeyOfList? hNodup v] at hNode
  exact hNode

theorem nodeKeyOfList?_nodeOfOptKeyList_some {H : LabelledQuotient}
    {keys : List (CutPair H)} {B : CutPair H} (hMem : B ∈ keys) :
    nodeKeyOfList? keys (nodeOfOptKeyList keys (some B)) = some B := by
  let ⟨i, hiFind, hiGet⟩ := findFinIdx_of_mem hMem
  dsimp [nodeOfOptKeyList]
  rw [hiFind]
  dsimp [nodeKeyOfList?]
  exact congrArg some hiGet

/-- Inclusive ancestry in a finite parent-pointer forest (`IsForestAncestor parent a u`
    means `a` lies on the upward `parent` chain from `u`, including `a = u`). -/
inductive IsForestAncestor {n : Nat} (parent : Fin n → Fin n) (a : Fin n) :
    Fin n → Prop where
  | refl : IsForestAncestor parent a a
  | step (u : Fin n) (prev : IsForestAncestor parent a (parent u)) :
      IsForestAncestor parent a u

theorem IsForestAncestor.trans {n : Nat} {parent : Fin n → Fin n}
    {a b c : Fin n} (h₁ : IsForestAncestor parent a b)
    (h₂ : IsForestAncestor parent b c) : IsForestAncestor parent a c := by
  induction h₂ with
  | refl => exact h₁
  | step u _ ih => exact IsForestAncestor.step u ih

def iterParentFin {n : Nat} (parent : Fin n → Fin n) : Nat → Fin n → Fin n
  | 0, u => u
  | k + 1, u => iterParentFin parent k (parent u)

theorem isForestAncestor_iff_iterParentFin {n : Nat} (parent : Fin n → Fin n)
    (a u : Fin n) :
    IsForestAncestor parent a u ↔ ∃ k : Nat, iterParentFin parent k u = a := by
  constructor
  · intro hAnc
    induction hAnc with
    | refl => exact ⟨0, rfl⟩
    | step _ _ ih =>
        let ⟨k, hk⟩ := ih
        exact ⟨k + 1, hk⟩
  · intro ⟨k, hk⟩
    revert u
    induction k with
    | zero =>
        intro u hk
        change u = a at hk
        rw [hk]
        exact IsForestAncestor.refl
    | succ _ ih =>
        intro u hk
        exact IsForestAncestor.step u (ih (parent u) hk)

/-- Concrete proper-loss forest data structure of Lemma 3.1 on `H`:
    node `0` (`rootNode`) is the artificial root, `1 .. realNodeCount` carry the
    deduplicated canonical real `CutPair H` keys, `parent` stores the single parent
    pointer per node, `depth` stores tree depth, and `label` is `c(y)`. -/
structure ProperLossForest (H : LabelledQuotient) where
  realKeys : List (CutPair H)
  parent : Fin (realKeys.length + 1) → Fin (realKeys.length + 1)
  depth : Fin (realKeys.length + 1) → Nat
  label : Fin H.vertexCount → Fin (realKeys.length + 1)

namespace ProperLossForest

abbrev realNodeCount {H : LabelledQuotient} (F : ProperLossForest H) : Nat :=
  F.realKeys.length

def rootNode {H : LabelledQuotient} (F : ProperLossForest H) :
    Fin (F.realNodeCount + 1) :=
  ⟨0, Nat.zero_lt_succ F.realKeys.length⟩

def nodeKey? {H : LabelledQuotient} (F : ProperLossForest H)
    (u : Fin (F.realNodeCount + 1)) : Option (CutPair H) :=
  nodeKeyOfList? F.realKeys u

def keyOfReal {H : LabelledQuotient} (F : ProperLossForest H)
    (i : Fin F.realNodeCount) : CutPair H :=
  listGetFin F.realKeys i

def lookupNode? {H : LabelledQuotient} (F : ProperLossForest H)
    (B : CutPair H) : Option (Fin (F.realNodeCount + 1)) :=
  match findFinIdx B F.realKeys with
  | none => none
  | some i => some ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

def nodeChainAux {H : LabelledQuotient} (F : ProperLossForest H) :
    Nat → Fin (F.realNodeCount + 1) → List (CutPair H)
  | 0, _ => []
  | fuel + 1, u =>
      match F.nodeKey? u with
      | none => []
      | some P => F.nodeChainAux fuel (F.parent u) ++ [P]

def nodeChain {H : LabelledQuotient} (F : ProperLossForest H)
    (u : Fin (F.realNodeCount + 1)) : List (CutPair H) :=
  F.nodeChainAux (F.depth u + 1) u

end ProperLossForest

/-- Construct the finite proper-loss forest of Lemma 3.1 from `(H, rank)`. -/
def buildProperLossForest (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) : ProperLossForest H :=
  let keys := realKeys H rank
  { realKeys := keys
    parent := fun u =>
      match nodeKeyOfList? keys u with
      | none => ⟨0, Nat.zero_lt_succ keys.length⟩
      | some P => nodeOfOptKeyList keys (storedParentKey? H rank P)
    depth := fun u => (parentKeyChain H rank (nodeKeyOfList? keys u)).length
    label := fun y => nodeOfOptKeyList keys (vertexLabelKey? H rank y) }

/-! ### Complete Lemma 3.1 theorem suite for `buildProperLossForest` -/

theorem buildProperLossForest_realKeys_canonical (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    ∀ B : CutPair H, B ∈ (buildProperLossForest H rank).realKeys → B.fst < B.snd :=
  fun _ hMem => canonical_of_mem_realKeys hMem

theorem buildProperLossForest_realKeys_nodup (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    (buildProperLossForest H rank).realKeys.Pairwise (· ≠ ·) :=
  nodup_realKeys H rank

theorem buildProperLossForest_realNodeCount_le (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    (buildProperLossForest H rank).realNodeCount ≤ H.vertexCount :=
  length_realKeys_le H rank

theorem buildProperLossForest_nodeKey?_root (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    (buildProperLossForest H rank).nodeKey?
      (buildProperLossForest H rank).rootNode = none :=
  rfl

theorem buildProperLossForest_nodeKey?_inj (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat)
    {u v : Fin ((buildProperLossForest H rank).realNodeCount + 1)}
    (hEq : (buildProperLossForest H rank).nodeKey? u =
      (buildProperLossForest H rank).nodeKey? v) : u = v :=
  nodeKeyOfList?_inj (nodup_realKeys H rank) hEq

theorem buildProperLossForest_parent_root (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    (buildProperLossForest H rank).parent
      (buildProperLossForest H rank).rootNode =
      (buildProperLossForest H rank).rootNode :=
  rfl

theorem buildProperLossForest_depth_root (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    (buildProperLossForest H rank).depth
      (buildProperLossForest H rank).rootNode = 0 :=
  rfl

theorem buildProperLossForest_label_root (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    (buildProperLossForest H rank).label H.root =
      (buildProperLossForest H rank).rootNode := by
  dsimp [buildProperLossForest, ProperLossForest.rootNode]
  unfold vertexLabelKey?
  rw [sweepChain_eq_of_eq_root H rank rfl]
  rfl

theorem buildProperLossForest_label_of_root_arc (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) {y : Fin H.vertexCount}
    (hArc : H.HasQuotientArc H.root y) :
    (buildProperLossForest H rank).label y =
      (buildProperLossForest H rank).rootNode := by
  dsimp [buildProperLossForest, ProperLossForest.rootNode]
  unfold vertexLabelKey?
  rw [sweepChain_eq_of_root_arc H rank hArc]
  rfl

theorem buildProperLossForest_mem_realKeys_iff {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (B : CutPair H) :
    B ∈ (buildProperLossForest H rank).realKeys ↔
      B.fst < B.snd ∧ ∃ y : Fin H.vertexCount, H.ProperLoss B y :=
  mem_realKeys_iff rankArc flat B

theorem buildProperLossForest_exists_node_iff {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (B : CutPair H) :
    (∃ u : Fin ((buildProperLossForest H rank).realNodeCount + 1),
      (buildProperLossForest H rank).nodeKey? u = some B) ↔
      B.fst < B.snd ∧ ∃ y : Fin H.vertexCount, H.ProperLoss B y := by
  rw [← buildProperLossForest_mem_realKeys_iff rankArc flat B]
  constructor
  · intro ⟨_, hu⟩
    exact nodeKeyOfList?_mem hu
  · intro hMem
    exact ⟨nodeOfOptKeyList (realKeys H rank) (some B),
      nodeKeyOfList?_nodeOfOptKeyList_some hMem⟩

theorem buildProperLossForest_nodeKey?_parent {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {u : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P : CutPair H}
    (hu : (buildProperLossForest H rank).nodeKey? u = some P) :
    (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent u) = storedParentKey? H rank P := by
  have hParDef :
      (buildProperLossForest H rank).parent u =
        nodeOfOptKeyList (realKeys H rank) (storedParentKey? H rank P) := by
    change (match (buildProperLossForest H rank).nodeKey? u with
      | none => (⟨0, Nat.zero_lt_succ (realKeys H rank).length⟩ : Fin ((realKeys H rank).length + 1))
      | some P' => nodeOfOptKeyList (realKeys H rank) (storedParentKey? H rank P')) = _
    rw [hu]
  change nodeKeyOfList? (realKeys H rank)
    ((buildProperLossForest H rank).parent u) = _
  rw [hParDef]
  cases hPar : storedParentKey? H rank P with
  | none => rfl
  | some B =>
      have hBMem : B ∈ realKeys H rank :=
        (storedParentKey?_some_props rankArc flat hPar).1
      exact nodeKeyOfList?_nodeOfOptKeyList_some hBMem

theorem buildProperLossForest_depth_real {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {u : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P : CutPair H}
    (hu : (buildProperLossForest H rank).nodeKey? u = some P) :
    (buildProperLossForest H rank).depth u =
      (buildProperLossForest H rank).depth
        ((buildProperLossForest H rank).parent u) + 1 := by
  have hParKey := buildProperLossForest_nodeKey?_parent rankArc flat hu
  change (parentKeyChain H rank ((buildProperLossForest H rank).nodeKey? u)).length =
    (parentKeyChain H rank
      ((buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent u))).length + 1
  rw [hu, hParKey, parentKeyChain_some_eq rankArc flat P, List.length_append]
  rfl

private theorem nodeChainAux_eq_parentKeyChain {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    ∀ (fuel : Nat) (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)),
      (buildProperLossForest H rank).depth u < fuel →
      (buildProperLossForest H rank).nodeChainAux fuel u =
        parentKeyChain H rank ((buildProperLossForest H rank).nodeKey? u)
  | 0, _, hLt => False.elim (by nomatch hLt)
  | fuel + 1, u, hLt => by
      dsimp [ProperLossForest.nodeChainAux]
      cases hu : (buildProperLossForest H rank).nodeKey? u with
      | none => rfl
      | some P =>
          have hDepthEq := buildProperLossForest_depth_real rankArc flat hu
          have hParDepthLt :
              (buildProperLossForest H rank).depth
                ((buildProperLossForest H rank).parent u) < fuel := by
            rw [hDepthEq] at hLt
            exact Nat.le_of_succ_le_succ hLt
          have ihPar :=
            nodeChainAux_eq_parentKeyChain rankArc flat fuel
              ((buildProperLossForest H rank).parent u) hParDepthLt
          rw [ihPar, buildProperLossForest_nodeKey?_parent rankArc flat hu,
            parentKeyChain_some_eq rankArc flat P]

theorem buildProperLossForest_nodeChain_eq_parentKeyChain {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)) :
    (buildProperLossForest H rank).nodeChain u =
      parentKeyChain H rank ((buildProperLossForest H rank).nodeKey? u) :=
  nodeChainAux_eq_parentKeyChain rankArc flat
    ((buildProperLossForest H rank).depth u + 1) u
    (Nat.lt_succ_self ((buildProperLossForest H rank).depth u))

theorem buildProperLossForest_nodeKey?_label {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) (y : Fin H.vertexCount) :
    (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).label y) = vertexLabelKey? H rank y := by
  dsimp [buildProperLossForest, ProperLossForest.nodeKey?]
  cases hLab : vertexLabelKey? H rank y with
  | none => rfl
  | some B =>
      have hBInChain : B ∈ sweepChain H rank y := mem_of_getLast?_eq_some hLab
      have specY := sweepChain_spec rankArc flat y
      have hBMem : B ∈ realKeys H rank :=
        (mem_realKeys_iff rankArc flat B).mpr
          ⟨specY.canonical B hBInChain, ⟨y, specY.sound B hBInChain⟩⟩
      exact nodeKeyOfList?_nodeOfOptKeyList_some hBMem

/-- Single stored `parent` consistency: every vertex's `sweepChain` equals its root-to-`label` `nodeChain`. -/
theorem buildProperLossForest_sweepChain_eq_nodeChain {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) (y : Fin H.vertexCount) :
    sweepChain H rank y =
      (buildProperLossForest H rank).nodeChain
        ((buildProperLossForest H rank).label y) := by
  rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat,
    buildProperLossForest_nodeKey?_label rankArc flat y]
  exact sweepChain_eq_parentKeyChain rankArc distinctRanks flat y

private theorem mem_nodeChain_imp_isForestAncestor_bounded {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {uB : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {B : CutPair H}
    (huB : (buildProperLossForest H rank).nodeKey? uB = some B) :
    ∀ (bound : Nat) (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)),
      (buildProperLossForest H rank).depth u < bound →
      B ∈ (buildProperLossForest H rank).nodeChain u →
      IsForestAncestor (buildProperLossForest H rank).parent uB u
  | 0, _, hLt, _ => False.elim (by nomatch hLt)
  | bound + 1, u, hLt, hMem => by
      rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat u] at hMem
      cases hu : (buildProperLossForest H rank).nodeKey? u with
      | none =>
          rw [hu] at hMem
          nomatch hMem
      | some P =>
          rw [hu, parentKeyChain_some_eq rankArc flat P] at hMem
          cases List.mem_append.mp hMem with
          | inr hTail =>
              cases List.mem_cons.mp hTail with
              | inr hNil => nomatch hNil
              | inl hBPEq =>
                  have hKeyEq :
                      (buildProperLossForest H rank).nodeKey? uB =
                        (buildProperLossForest H rank).nodeKey? u := by
                    rw [huB, hu, hBPEq]
                  have huEq : uB = u :=
                    buildProperLossForest_nodeKey?_inj H rank hKeyEq
                  rw [huEq]
                  exact IsForestAncestor.refl
          | inl hPref =>
              have hDepthEq := buildProperLossForest_depth_real rankArc flat hu
              have hParLt :
                  (buildProperLossForest H rank).depth
                    ((buildProperLossForest H rank).parent u) < bound := by
                rw [hDepthEq] at hLt
                exact Nat.le_of_succ_le_succ hLt
              have hMemPar :
                  B ∈ (buildProperLossForest H rank).nodeChain
                    ((buildProperLossForest H rank).parent u) := by
                rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat
                    ((buildProperLossForest H rank).parent u),
                  buildProperLossForest_nodeKey?_parent rankArc flat hu]
                exact hPref
              exact IsForestAncestor.step u
                (mem_nodeChain_imp_isForestAncestor_bounded rankArc flat huB
                  bound ((buildProperLossForest H rank).parent u) hParLt hMemPar)

theorem mem_nodeChain_iff_isForestAncestor {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {uB : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {B : CutPair H}
    (huB : (buildProperLossForest H rank).nodeKey? uB = some B)
    (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)) :
    B ∈ (buildProperLossForest H rank).nodeChain u ↔
      IsForestAncestor (buildProperLossForest H rank).parent uB u := by
  constructor
  · intro hMem
    exact mem_nodeChain_imp_isForestAncestor_bounded rankArc flat huB
      ((buildProperLossForest H rank).depth u + 1) u
      (Nat.lt_succ_self ((buildProperLossForest H rank).depth u)) hMem
  · intro hAnc
    induction hAnc with
    | refl =>
        rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat uB, huB,
          parentKeyChain_some_eq rankArc flat B]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    | step w _ ih =>
        rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat w]
        cases hw : (buildProperLossForest H rank).nodeKey? w with
        | none =>
            have hwRoot : w = (buildProperLossForest H rank).rootNode :=
              buildProperLossForest_nodeKey?_inj H rank
                (hw.trans (buildProperLossForest_nodeKey?_root H rank).symm)
            rw [hwRoot, buildProperLossForest_parent_root H rank,
              buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat,
              buildProperLossForest_nodeKey?_root H rank] at ih
            nomatch ih
        | some P =>
            rw [buildProperLossForest_nodeChain_eq_parentKeyChain rankArc flat
                ((buildProperLossForest H rank).parent w),
              buildProperLossForest_nodeKey?_parent rankArc flat hw] at ih
            rw [parentKeyChain_some_eq rankArc flat P]
            exact List.mem_append.mpr (Or.inl ih)

theorem buildProperLossForest_properLoss_iff_of_node {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {uB : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {B : CutPair H}
    (huB : (buildProperLossForest H rank).nodeKey? uB = some B)
    (y : Fin H.vertexCount) :
    H.ProperLoss B y ↔
      IsForestAncestor (buildProperLossForest H rank).parent uB
        ((buildProperLossForest H rank).label y) := by
  have hCan : B.fst < B.snd :=
    canonical_of_mem_realKeys (nodeKeyOfList?_mem huB)
  rw [← (sweepChain_spec rankArc flat y).complete_iff B hCan,
    buildProperLossForest_sweepChain_eq_nodeChain rankArc distinctRanks flat y]
  exact mem_nodeChain_iff_isForestAncestor rankArc flat huB
    ((buildProperLossForest H rank).label y)

/-- Inclusive ancestor correctness (Lemma 3.1): for every canonical `B` (`B.fst < B.snd`) and `y`,
    `H.ProperLoss B y` iff `B` is a real forest node and an inclusive ancestor of `c(y)`. -/
theorem buildProperLossForest_properLoss_iff_ancestor {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) {B : CutPair H} (hOrder : B.fst < B.snd)
    (y : Fin H.vertexCount) :
    H.ProperLoss B y ↔
      ∃ uB : Fin ((buildProperLossForest H rank).realNodeCount + 1),
        (buildProperLossForest H rank).nodeKey? uB = some B ∧
        IsForestAncestor (buildProperLossForest H rank).parent uB
          ((buildProperLossForest H rank).label y) := by
  constructor
  · intro hProper
    let ⟨uB, huB⟩ :=
      (buildProperLossForest_exists_node_iff rankArc flat B).mpr ⟨hOrder, ⟨y, hProper⟩⟩
    exact ⟨uB, huB,
      (buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat huB y).mp hProper⟩
  · intro ⟨uB, huB, hAnc⟩
    exact (buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat huB y).mpr hAnc

/-- Edge invariant 1 (`P ⊆ Z(B)`): both endpoints of a real child `P` are lost under its real parent `B`. -/
theorem buildProperLossForest_edge_endpoints_lost {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {uP : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P B : CutPair H}
    (huP : (buildProperLossForest H rank).nodeKey? uP = some P)
    (huB : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent uP) = some B) :
    ∀ p : Fin H.vertexCount, P.Mem p → H.Lost B p := by
  have hPar : storedParentKey? H rank P = some B := by
    rw [← buildProperLossForest_nodeKey?_parent rankArc flat huP]
    exact huB
  exact (storedParentKey?_some_props rankArc flat hPar).2.2

/-- Edge invariant 2 (`J(P) ⊆ J(B)`): proper losses of a real child `P` are proper losses of its real parent `B`. -/
theorem buildProperLossForest_edge_properLoss_subset {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {uP : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P B : CutPair H}
    (huP : (buildProperLossForest H rank).nodeKey? uP = some P)
    (huB : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent uP) = some B) :
    ∀ y : Fin H.vertexCount, H.ProperLoss P y → H.ProperLoss B y := by
  intro y hProperP
  have hAncP : IsForestAncestor (buildProperLossForest H rank).parent uP
      ((buildProperLossForest H rank).label y) :=
    (buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat huP y).mp hProperP
  have hEdgeAnc : IsForestAncestor (buildProperLossForest H rank).parent
      ((buildProperLossForest H rank).parent uP) uP :=
    IsForestAncestor.step uP IsForestAncestor.refl
  have hAncB := IsForestAncestor.trans hEdgeAnc hAncP
  exact (buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat huB y).mpr hAncB

/-- Edge invariant 3 (`P \ B` follows `B`): every fresh child endpoint strictly follows both parent endpoints. -/
theorem buildProperLossForest_edge_fresh_follows_parent {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {uP : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P B : CutPair H}
    (huP : (buildProperLossForest H rank).nodeKey? uP = some P)
    (huB : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent uP) = some B) :
    ∀ p : Fin H.vertexCount, IsFreshEndpoint B P p →
      ∀ b : Fin H.vertexCount, B.Mem b → rank b < rank p := by
  have hLost := buildProperLossForest_edge_endpoints_lost rankArc flat huP huB
  intro p hFresh b hb
  exact properLoss_follows_endpoints rankArc flat ⟨hLost p hFresh.1, hFresh.2⟩ hb

/-- Real parent and real child cuts are distinct as unordered pairs (`¬ ∀ z, B.Mem z ↔ P.Mem z`). -/
theorem buildProperLossForest_edge_distinct_cuts {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {uP : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P B : CutPair H}
    (huP : (buildProperLossForest H rank).nodeKey? uP = some P)
    (huB : (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).parent uP) = some B) :
    ¬ ∀ z : Fin H.vertexCount, B.Mem z ↔ P.Mem z := by
  intro hSame
  have hBCan : B.fst < B.snd := canonical_of_mem_realKeys (nodeKeyOfList?_mem huB)
  have hPCan : P.fst < P.snd := canonical_of_mem_realKeys (nodeKeyOfList?_mem huP)
  have hEqBP : B = P := CutPair.eq_of_canonical_mem_iff hBCan hPCan hSame
  have hKeyEq :
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent uP) =
        (buildProperLossForest H rank).nodeKey? uP := by
    rw [huB, huP, hEqBP]
  have hNodeEq : (buildProperLossForest H rank).parent uP = uP :=
    buildProperLossForest_nodeKey?_inj H rank hKeyEq
  have hDepth := buildProperLossForest_depth_real rankArc flat huP
  rw [hNodeEq] at hDepth
  exact Nat.ne_of_lt (Nat.lt_succ_self _) hDepth

/-- Topological-list rank adapter: index of a vertex in an enumerated `topo` list. -/
def indexInList {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else indexInList x ys + 1

theorem indexInList_inj_of_mem {α : Type} [DecidableEq α] {l : List α} {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (hEq : indexInList a l = indexInList b l) : a = b := by
  induction l with
  | nil => nomatch ha
  | cons y ys ih =>
      dsimp [indexInList] at hEq
      by_cases hay : a = y
      · rw [ite_eq_left hay] at hEq
        by_cases hby : b = y
        · exact hay.trans hby.symm
        · rw [ite_eq_right hby] at hEq
          nomatch hEq
      · rw [ite_eq_right hay] at hEq
        by_cases hby : b = y
        · rw [ite_eq_left hby] at hEq
          nomatch hEq
        · rw [ite_eq_right hby] at hEq
          have haYs : a ∈ ys :=
            match List.mem_cons.mp ha with
            | Or.inl h => False.elim (hay h)
            | Or.inr h => h
          have hbYs : b ∈ ys :=
            match List.mem_cons.mp hb with
            | Or.inl h => False.elim (hby h)
            | Or.inr h => h
          exact ih haYs hbYs (Nat.succ.inj hEq)

/-- Complete Lemma 3.1 theorem bundle for a flat quotient DAG with injective topological rank. -/
theorem exists_properLossForest_lemma_3_1 {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) :
    ∃ F : ProperLossForest H,
      (∀ B : CutPair H, B ∈ F.realKeys → B.fst < B.snd) ∧
      F.realKeys.Pairwise (· ≠ ·) ∧
      F.realNodeCount ≤ H.vertexCount ∧
      F.nodeKey? F.rootNode = none ∧
      F.parent F.rootNode = F.rootNode ∧
      F.label H.root = F.rootNode ∧
      (∀ y : Fin H.vertexCount, H.HasQuotientArc H.root y → F.label y = F.rootNode) ∧
      (∀ B : CutPair H,
        (∃ u, F.nodeKey? u = some B) ↔
          B.fst < B.snd ∧ ∃ y : Fin H.vertexCount, H.ProperLoss B y) ∧
      (∀ y : Fin H.vertexCount, sweepChain H rank y = F.nodeChain (F.label y)) ∧
      (∀ B : CutPair H, B.fst < B.snd → ∀ y : Fin H.vertexCount,
        H.ProperLoss B y ↔
          ∃ u, F.nodeKey? u = some B ∧ IsForestAncestor F.parent u (F.label y)) ∧
      (∀ uP : Fin (F.realNodeCount + 1), ∀ P B : CutPair H,
        F.nodeKey? uP = some P → F.nodeKey? (F.parent uP) = some B →
          (∀ p : Fin H.vertexCount, P.Mem p → H.Lost B p) ∧
          (∀ y : Fin H.vertexCount, H.ProperLoss P y → H.ProperLoss B y) ∧
          (∀ p : Fin H.vertexCount, IsFreshEndpoint B P p →
            ∀ b : Fin H.vertexCount, B.Mem b → rank b < rank p)) :=
  ⟨buildProperLossForest H rank,
    buildProperLossForest_realKeys_canonical H rank,
    buildProperLossForest_realKeys_nodup H rank,
    buildProperLossForest_realNodeCount_le H rank,
    buildProperLossForest_nodeKey?_root H rank,
    buildProperLossForest_parent_root H rank,
    buildProperLossForest_label_root H rank,
    fun _ hArc => buildProperLossForest_label_of_root_arc H rank hArc,
    buildProperLossForest_exists_node_iff rankArc flat,
    buildProperLossForest_sweepChain_eq_nodeChain rankArc distinctRanks flat,
    fun _ hOrd y =>
      buildProperLossForest_properLoss_iff_ancestor rankArc distinctRanks flat hOrd y,
    fun _ _ _ huP huB =>
      ⟨buildProperLossForest_edge_endpoints_lost rankArc flat huP huB,
        buildProperLossForest_edge_properLoss_subset rankArc distinctRanks flat huP huB,
        buildProperLossForest_edge_fresh_follows_parent rankArc flat huP huB⟩⟩

set_option autoImplicit false

/-- An injective rank makes the maximum independent of row order.
No `Nodup` hypothesis is needed for this result. -/
theorem maxByRank_eq_of_mem_iff {n : Nat} (rank : Fin n → Nat)
    (inj : ∀ {a b : Fin n}, rank a = rank b → a = b)
    {xs ys : List (Fin n)}
    (mem : ∀ u : Fin n, u ∈ xs ↔ u ∈ ys) :
    maxByRank rank xs = maxByRank rank ys := by
  have best (a : Fin n) (tl : List (Fin n)) :
      maxByRankAux rank a tl ∈ a :: tl ∧
        ∀ u : Fin n, u ∈ a :: tl →
          rank u ≤ rank (maxByRankAux rank a tl) := by
    refine ⟨List.mem_cons.mpr (maxByRankAux_mem rank a tl), ?_⟩
    intro u hu
    obtain ⟨ha, ht⟩ := maxByRankAux_ge rank a tl
    rcases List.mem_cons.mp hu with he | hu
    · subst u
      exact ha
    · exact ht u hu
  cases xs with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b bs =>
      have h : b ∈ ([] : List (Fin n)) :=
        (mem b).mpr (List.mem_cons.mpr (Or.inl rfl))
      simp at h
  | cons a ats =>
    cases ys with
    | nil =>
      have h : a ∈ ([] : List (Fin n)) :=
        (mem a).mp (List.mem_cons.mpr (Or.inl rfl))
      simp at h
    | cons b bs =>
      obtain ⟨ha, hga⟩ := best a ats
      obtain ⟨hb, hgb⟩ := best b bs
      have hEq : maxByRankAux rank a ats = maxByRankAux rank b bs :=
        inj (Nat.le_antisymm
          (hgb _ ((mem _).mp ha))
          (hga _ ((mem _).mpr hb)))
      exact congrArg some hEq

/-- A two-element predecessor set determines the reference row in `Fin` order. -/
theorem preds_eq_pair_of_mem_iff (H : LabelledQuotient)
    (y : Fin H.vertexCount) {a b : Fin H.vertexCount} (hab : a < b)
    (mem : ∀ u : Fin H.vertexCount, u ∈ preds H y ↔ u = a ∨ u = b) :
    preds H y = [a, b] :=
  eq_pair_of_pairwise_lt_mem_iff (pairwise_lt_preds H y) hab mem

end LabelledQuotient

end PaperB
