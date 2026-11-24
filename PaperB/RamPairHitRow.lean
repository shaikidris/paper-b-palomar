module

public import PaperB.RamCheckedPairLookup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine PaperB.WordOps PaperB.PairLookup
open PaperB.PairLookup.ColumnReduction
open PaperB.RamProgram.ThreeCalls.EqualityTail

private theorem first_column_covers_cut_with_index
    {bits : Nat} {input : Array (Word bits)} {a : Array Key}
    (c : Columns (bits := bits) input a) {hi : Nat}
    (hhi : hi ≤ c.second.len) : hi ≤ c.first.len := by
  cases c
  first
  | omega
  | dsimp at * <;> omega

private theorem pair_run_widen_with_index
    {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    {code : RamProgram.Program (layout bits cap hcap)}
    {input : RamProgram.Input (layout bits cap hcap)}
    {s : RamProgram.State (layout bits cap hcap)}
    {r : RamProgram.Result (layout bits cap hcap)}
    {fuel fuel' : Nat} (hle : fuel ≤ fuel')
    (hr : run code input fuel s = some r) :
    run code input fuel' s = some r := by
  induction fuel generalizing fuel' s r with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases fuel' with
    | zero => omega
    | succ fuel' =>
      have hle' : fuel ≤ fuel' := Nat.le_of_succ_le_succ hle
      cases he : step code input s with
      | none => simp [run, he] at hr
      | some e =>
        cases e with
        | halted t => simpa only [run, he] using hr
        | next t =>
          cases ht : run code input fuel t with
          | none => simp [run, he, ht] at hr
          | some rt =>
            have hw := ih (fuel' := fuel') (s := t) (r := rt) hle' ht
            simpa only [run, he, ht, hw] using hr

/-- In the same checked run and fuel budget as `pair_search_correct_from_pc0`,
register 0 gates the exact lookup row in register 3. The optional output is
`none` on a miss, regardless of the final contents of register 3. -/
theorem pair_search_correct_from_pc0_with_index
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits) (hone : 1 < 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    {j : RamProgram.Input (layout bits cap hcap)}
    {a : Array Key} (c : Columns (bits := bits) i.words a)
    (hs : StrictSorted a) (x y : Word bits) (hwords : i.words = j.words)
    (s : RamProgram.State (layout bits cap hcap)) (hpc : s.pc = 0)
    (h7 : setupReg s 7 = c.first.base)
    (h8 : (setupReg s 8).val = c.first.len)
    (h9 : setupReg s 9 = c.second.base)
    (h11 : setupReg s 11 = x) (h12 : setupReg s 12 = y)
    (h4 : setupReg s 4 = zero bits) (h5 : setupReg s 5 = zero bits) :
    ∃ r : RamProgram.Result (layout bits cap hcap),
      run (checkedProgram hcap hone (concreteSetup bits hone)) j
        (33 * (Nat.log2 (a.size + 1) + 1) + 39) s = some r ∧
      (setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits) ↔
        (PairLookup.lookup a (x.val, y.val)).1.isSome = true) ∧
      (∀ row : Nat, (PairLookup.lookup a (x.val, y.val)).1 = some row →
        setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits) ∧
        (setupReg r.finalState 3).val = row) ∧
      (let success : Bool :=
        decide (setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits))
       (if success then some (setupReg r.finalState 3).val else none) =
        (PairLookup.lookup a (x.val, y.val)).1) := by
  obtain ⟨lo, hi, k, predSteps, xSteps, ySteps, n, s20, s40, s60,
    hlo, hhi₂, ht20, hp20, hlo20, ht40, hp40, hhi40, hwlo40,
    ht60, hp60, hk0, hwlo60, hwhi60, hlo60, hhi60,
    h607, h609, h6011, h6012, hband, hk, hfinish, hn, hprefix, hbudget⟩ :=
    pair_search_prefix_from_pc0 hcap hone c hs x y hwords s hpc
      h7 h8 h9 h11 h12 h4 h5
  have hhi₁ : hi ≤ c.first.len := first_column_covers_cut_with_index c hhi₂
  have hsize : i.words.size ≤ cap := by
    rw [hwords, j.size_eq] <;> exact Nat.le_refl _
  have hcol₁ : (setupReg s60 7).val + (setupReg s60 14).val ≤ cap := by
    rw [h607, hhi60]
    have hw := c.first.within
    omega
  have hcol₂ : (setupReg s60 9).val + (setupReg s60 14).val ≤ cap := by
    rw [h609, hhi60]
    have hw := c.second.within
    omega
  have hk60 :
      (setupReg s60 0).val ≤ (setupReg s60 14).val - (setupReg s60 13).val := by
    simpa only [hk0, hlo60, hhi60] using hk
  have hmatch :=
    selectedPairMatches_iff_finish_isSome c x y hwords s60 hp60
      hk hhi₁ hhi₂ hk0 hlo60 h607 h609 h6011 h6012
  obtain ⟨r, htail, hout, hindex⟩ :=
    EqualityTail.validation_correct_with_index hcap hone (concreteSetup bits hone)
      j s60 hp60 hk60 hcol₁ hcol₂
  have hchecked :
      Steps (checkedProgram hcap hone (concreteSetup bits hone)) j n s s60 :=
    PaperB.RamEqualityTailTransfer.steps_checkedProgram hprefix
  have hrun := hchecked.thenRun htail

  have hfinishIndex {row : Nat}
      (hrow : ColumnReduction.finish c.first c.second x y lo k = some row) :
      chosenIndex s60 = row := by
    by_cases hpos : 0 < k
    · let d := lo + (k - 1)
      have hdhi : d < hi := by dsimp [d]; omega
      have hd₁ : d < c.first.len := by omega
      have hd₂ : d < c.second.len := by omega
      have hboth :
          lo + (k - 1) < c.first.len ∧ lo + (k - 1) < c.second.len :=
        ⟨hd₁, hd₂⟩
      have hf : ColumnReduction.finish c.first c.second x y lo k =
          (if (c.first.get d hd₁).val = x.val ∧
              (c.second.get d hd₂).val = y.val then some d else none) := by
        simp only [ColumnReduction.finish, if_pos hpos, dif_pos hboth] <;> rfl
      have hdrow : d = row := by
        rw [hf] at hrow
        split at hrow
        · exact Option.some.inj hrow
        · simp at hrow
      change (setupReg s60 13).val + (setupReg s60 0).val - 1 = row
      rw [hlo60, hk0]
      dsimp [d] at hdrow
      omega
    · simp [ColumnReduction.finish, hpos] at hrow

  have hflagMatches : setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits) ↔
      selectedPairMatches j s60 := hout
  have hflag : setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits) ↔
      (PairLookup.lookup a (x.val, y.val)).1.isSome = true :=
    hflagMatches.trans (hmatch.trans (by rw [hfinish]))
  have hhit (row : Nat) (hrow : (PairLookup.lookup a (x.val, y.val)).1 = some row) :
      setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits) ∧
      (setupReg r.finalState 3).val = row := by
    have hb : setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits) :=
      hflag.mpr (by simp [hrow])
    have hf : ColumnReduction.finish c.first c.second x y lo k = some row := by
      simpa only [hfinish] using hrow
    have hr3 : (setupReg r.finalState 3).val = chosenIndex s60 := hindex hb
    exact ⟨hb, hr3.trans (hfinishIndex hf)⟩

  refine ⟨⟨r.finalState, n + r.executed⟩, pair_run_widen_with_index hbudget hrun,
    hflag, hhit, ?_⟩
  change
    (if (decide (setupReg r.finalState 0 = (⟨1, hone⟩ : Word bits)) : Bool)
      then some (setupReg r.finalState 3).val else none) =
      (PairLookup.lookup a (x.val, y.val)).1
  cases hlookup : (PairLookup.lookup a (x.val, y.val)).1 with
  | none =>
    have hmiss : setupReg r.finalState 0 ≠ (⟨1, hone⟩ : Word bits) := by
      intro hb
      have hs' := hflag.mp hb
      simp [hlookup] at hs'
    simp [hmiss]
  | some row =>
    obtain ⟨hb, hrow⟩ := hhit row hlookup
    simp [hb, hrow]

end PaperB.RamProgram.ThreeCalls
