module

public import PaperB.ForestKeyInstall

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.ForestHead

open PaperB.LabelledQuotient

private def rowHasRoot {n : Nat} (root : Fin n) : List (Fin n) → Bool
  | [] => false
  | x :: xs => if x = root then true else rowHasRoot root xs

private theorem rowHasRoot_eq_true_iff {n : Nat}
    (root : Fin n) (xs : List (Fin n)) :
    rowHasRoot root xs = true ↔ root ∈ xs := by
  induction xs with
  | nil => simp [rowHasRoot]
  | cons x xs ih =>
    by_cases h : x = root
    · subst x
      simp [rowHasRoot]
    · simp [rowHasRoot, h, Ne.symm h, ih, List.mem_cons]

/-- Inspect at most three list constructors. Only a two-entry row needs
an order comparison or a call to `candidatePairOfPreds`. -/
def preparedKey (H : LabelledQuotient) :
    List (Vertex H) → Option (CutPair H)
  | [a, b] =>
    candidatePairOfPreds H (if a < b then [a, b] else [b, a])
  | _ => none

private theorem nodup_cons_parts {α : Type} {a : α} {xs : List α}
    (h : (a :: xs).Nodup) :
    (∀ b : α, b ∈ xs → a ≠ b) ∧ xs.Nodup :=
  List.pairwise_cons.mp
    (show (a :: xs).Pairwise (fun u v => u ≠ v) from h)

private theorem two_of_nodup_mem_pair {α : Type} {xs : List α} {a b : α}
    (hne : a ≠ b) (nd : xs.Nodup)
    (mem : ∀ u : α, u ∈ xs ↔ u = a ∨ u = b) :
    ∃ p q : α, xs = [p, q] := by
  cases xs with
  | nil =>
    have ha : a ∈ ([] : List α) := (mem a).mpr (Or.inl rfl)
    simp at ha
  | cons p xs =>
    cases xs with
    | nil =>
      have ha : a = p := by simpa using (mem a).mpr (Or.inl rfl)
      have hb : b = p := by simpa using (mem b).mpr (Or.inr rfl)
      exact (hne (ha.trans hb.symm)).elim
    | cons q xs =>
      cases xs with
      | nil => exact ⟨p, q, rfl⟩
      | cons r xs =>
        obtain ⟨hp, nd'⟩ := nodup_cons_parts nd
        obtain ⟨hq, _⟩ := nodup_cons_parts nd'
        have hpq : p ≠ q := hp q (by simp)
        have hpr : p ≠ r := hp r (by simp)
        have hqr : q ≠ r := hq r (by simp)
        rcases (mem p).mp (by simp) with ep | ep <;>
          rcases (mem q).mp (by simp) with eq | eq <;>
          rcases (mem r).mp (by simp) with er | er <;>
          first
          | exact (hpq (ep.trans eq.symm)).elim
          | exact (hpr (ep.trans er.symm)).elim
          | exact (hqr (eq.trans er.symm)).elim

private theorem keys_none_of_not_two (H : LabelledQuotient)
    (xs : List (Vertex H))
    (h : ¬ ∃ a b : Vertex H, xs = [a, b]) :
    preparedKey H xs = none ∧ candidatePairOfPreds H xs = none := by
  cases xs with
  | nil => exact ⟨rfl, rfl⟩
  | cons a xs =>
    cases xs with
    | nil => exact ⟨rfl, rfl⟩
    | cons b xs =>
      cases xs with
      | nil => exact (h ⟨a, b, rfl⟩).elim
      | cons c xs => exact ⟨rfl, rfl⟩

theorem preparedKey_eq_candidate {H : LabelledQuotient}
    (y : Vertex H) (xs : List (Vertex H)) (T : TestSpec y xs) :
    preparedKey H xs = candidatePairOfPreds H (preds H y) := by
  have mem (u : Vertex H) : u ∈ xs ↔ u ∈ preds H y :=
    (T.cover u).trans (mem_preds_iff H y u).symm
  by_cases ht : ∃ a b : Vertex H, xs = [a, b]
  · obtain ⟨a, b, rfl⟩ := ht
    have hne : a ≠ b := (nodup_cons_parts T.nodup).1 b (by simp)
    have hm (u : Vertex H) : u ∈ preds H y ↔ u = a ∨ u = b := by
      simpa using (mem u).symm
    by_cases hab : a < b
    · have hp := preds_eq_pair_of_mem_iff H y hab hm
      simp [preparedKey, hab, hp]
    · have hba : b < a := by
        change b.val < a.val
        rcases Nat.lt_trichotomy a.val b.val with hlt | he | hgt
        · exact (hab hlt).elim
        · exact (hne (Fin.ext he)).elim
        · exact hgt
      have hp := preds_eq_pair_of_mem_iff H y hba
        (fun u => by simpa [or_comm] using hm u)
      simp [preparedKey, hab, hp]
  · have hp : ¬ ∃ a b : Vertex H, preds H y = [a, b] := by
      intro hex
      obtain ⟨a, b, he⟩ := hex
      have hs := pairwise_lt_preds H y
      rw [he] at hs
      have hab : a < b := (List.pairwise_cons.mp hs).1 b (by simp)
      have hne : a ≠ b := by
        intro h
        subst b
        exact Nat.lt_irrefl a.val hab
      exact ht (two_of_nodup_mem_pair hne T.nodup
        (fun u => by simpa [he] using mem u))
    exact (keys_none_of_not_two H xs ht).1.trans
      (keys_none_of_not_two H (preds H y) hp).2.symm

/-- `none` is a stopped head; `some (m, key)` is an active head. -/
def planPrepared {H : LabelledQuotient} (rank : Vertex H → Nat)
    (y : Vertex H) (xs : List (Vertex H)) :
    Option (Vertex H × Option (CutPair H)) :=
  if y = H.root then none
  else if rowHasRoot H.root xs then none
  else (maxByRank rank xs).map fun m => (m, preparedKey H xs)

/-- Execute on the prepared row, with no access to graph adjacency. -/
def runPrepared {H : LabelledQuotient} (S : Selectors H)
    (rank : Vertex H → Nat) (y : Vertex H) (xs : List (Vertex H)) :
    Measured H :=
  match planPrepared rank y xs with
  | none => stopped
  | some (m, key) => active S xs m key

theorem runPrepared_eq_runHead {H : LabelledQuotient} (S : Selectors H)
    (rank : Vertex H → Nat) (y : Vertex H) (xs : List (Vertex H))
    (T : TestSpec y xs)
    (inj : ∀ {a b : Vertex H}, rank a = rank b → a = b) :
    runPrepared S rank y xs = runHead S rank y xs := by
  have hr : rowHasRoot H.root xs = H.hasQuotientArcBool H.root y := by
    have hiff :
        rowHasRoot H.root xs = true ↔ H.hasQuotientArcBool H.root y = true :=
      (rowHasRoot_eq_true_iff H.root xs).trans
        ((T.cover H.root).trans (hasQuotientArcBool_eq_true_iff H H.root y).symm)
    cases h₁ : rowHasRoot H.root xs <;>
      cases h₂ : H.hasQuotientArcBool H.root y <;>
      simp_all
  have hm : maxByRank rank xs = maxByRank rank (preds H y) :=
    maxByRank_eq_of_mem_iff rank inj
      (fun u => (T.cover u).trans (mem_preds_iff H y u).symm)
  have hk := preparedKey_eq_candidate y xs T
  by_cases hy : y = H.root
  · simp [runPrepared, planPrepared, runHead, hy]
  · cases hb : H.hasQuotientArcBool H.root y <;>
      cases hm' : maxByRank rank (preds H y) <;>
      simp [runPrepared, planPrepared, runHead, hy, hr, hb, hm, hm', hk]

/- Source-level planning meter. Charge one unit per visited row entry
   in either scan, plus a fixed allowance for non-loop work. These
   definitions are not called by `runPrepared`. -/

private def rowRootMeter {n : Nat} (root : Fin n) :
    List (Fin n) → Bool × Nat
  | [] => (false, 0)
  | x :: xs =>
    if x = root then (true, 1)
    else
      let r := rowRootMeter root xs
      (r.1, r.2 + 1)

private theorem rowRootMeter_spec {n : Nat} (root : Fin n)
    (xs : List (Fin n)) :
    (rowRootMeter root xs).1 = rowHasRoot root xs ∧
      (rowRootMeter root xs).2 ≤ xs.length := by
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    by_cases h : x = root
    · refine ⟨by simp [rowRootMeter, rowHasRoot, h], ?_⟩
      simpa [rowRootMeter, h] using Nat.succ_le_succ (Nat.zero_le xs.length)
    · refine ⟨by simpa [rowRootMeter, rowHasRoot, h] using ih.1, ?_⟩
      simpa [rowRootMeter, h] using Nat.succ_le_succ ih.2

private def rowMaxAuxMeter {n : Nat} (rank : Fin n → Nat) :
    Fin n → List (Fin n) → Fin n × Nat
  | best, [] => (best, 0)
  | best, x :: xs =>
    let r := rowMaxAuxMeter rank (if rank best ≤ rank x then x else best) xs
    (r.1, r.2 + 1)

private theorem rowMaxAuxMeter_eq {n : Nat} (rank : Fin n → Nat)
    (best : Fin n) (xs : List (Fin n)) :
    rowMaxAuxMeter rank best xs = (maxByRankAux rank best xs, xs.length) := by
  induction xs generalizing best with
  | nil => rfl
  | cons x xs ih =>
    simp only [rowMaxAuxMeter, maxByRankAux, ih, List.length_cons]

private def rowMaxMeter {n : Nat} (rank : Fin n → Nat) :
    List (Fin n) → Option (Fin n) × Nat
  | [] => (none, 0)
  | x :: xs =>
    let r := rowMaxAuxMeter rank x xs
    (some r.1, r.2 + 1)

private theorem rowMaxMeter_eq {n : Nat} (rank : Fin n → Nat)
    (xs : List (Fin n)) :
    rowMaxMeter rank xs = (maxByRank rank xs, xs.length) := by
  cases xs with
  | nil => rfl
  | cons x xs => simp [rowMaxMeter, rowMaxAuxMeter_eq, maxByRank]

/-- `16` is a fixed allowance, not an exact instruction count: it covers
the head/branch checks, scan setup and exit, and the constant-size key
and plan construction. Neither the search nor installation is metered here. -/
def planPreparedMetered {H : LabelledQuotient} (rank : Vertex H → Nat)
    (y : Vertex H) (xs : List (Vertex H)) :
    Option (Vertex H × Option (CutPair H)) × Nat :=
  if y = H.root then (none, 16)
  else
    let r := rowRootMeter H.root xs
    if r.1 then (none, r.2 + 16)
    else
      let m := rowMaxMeter rank xs
      (m.1.map (fun u => (u, preparedKey H xs)), r.2 + m.2 + 16)

/-- The meter projects to the actual planner and charges at most two
visits per row entry in total, plus the fixed allowance. -/
theorem planPrepared_work {H : LabelledQuotient} (rank : Vertex H → Nat)
    (y : Vertex H) (xs : List (Vertex H)) :
    (planPreparedMetered rank y xs).1 = planPrepared rank y xs ∧
      (planPreparedMetered rank y xs).2 ≤ xs.length + xs.length + 16 := by
  by_cases hy : y = H.root
  · refine ⟨by simp [planPreparedMetered, planPrepared, hy], ?_⟩
    simpa [planPreparedMetered, hy] using
      Nat.add_le_add_right (Nat.zero_le (xs.length + xs.length)) 16
  · obtain ⟨hr, hcost⟩ := rowRootMeter_spec H.root xs
    have hm := rowMaxMeter_eq rank xs
    cases hb : (rowRootMeter H.root xs).1 with
    | false =>
      refine ⟨by simp [planPreparedMetered, planPrepared, hy, ← hr, hb, hm], ?_⟩
      simpa [planPreparedMetered, hy, hb, hm] using
        Nat.add_le_add_right (Nat.add_le_add hcost (Nat.le_refl xs.length)) 16
    | true =>
      refine ⟨by simp [planPreparedMetered, planPrepared, hy, ← hr, hb], ?_⟩
      simpa [planPreparedMetered, hy, hb] using
        Nat.add_le_add_right (Nat.add_le_add hcost (Nat.zero_le xs.length)) 16

end PaperB.ForestHead

namespace EX24
open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient
set_option autoImplicit false

/-- Plan on the prepared row, install against the old tables, and write
the head label once, only if installation succeeds. -/
def stepPrepared {H : LabelledQuotient} (c : Config H) (s : State H)
    (rank : Vertex H → Nat) (y : Vertex H) (xs : List (Vertex H)) :
    Option (HeadResult H) :=
  if hy : c.vertexIndex y < s.labels.size then
    let m := ForestHead.runPrepared (selectors c s) rank y xs
    (install c s.tables m.step).map fun r =>
      ⟨m, r, s.labels.set (c.vertexIndex y) r.node hy⟩
  else none

theorem stepPrepared_eq_step {H : LabelledQuotient} (c : Config H) (s : State H)
    (rank : Vertex H → Nat) (y : Vertex H) (xs : List (Vertex H))
    (T : ForestHead.TestSpec y xs)
    (inj : ∀ {a b : Vertex H}, rank a = rank b → a = b) :
    stepPrepared c s rank y xs = step c s rank y xs := by
  unfold stepPrepared step
  rw [ForestHead.runPrepared_eq_runHead (selectors c s) rank y xs T inj]

end EX24
