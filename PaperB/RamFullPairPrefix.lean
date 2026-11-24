module

public import PaperB.RamFirstSetupAgreement
public import PaperB.RamPlacedCalls

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine PaperB.WordOps PaperB.PairLookup
open PaperB.PairLookup.ColumnReduction
open PaperB.RamPairSliceBinding (toPredecessor)

private abbrev PairPrefixDescriptorReg (q : Fin 16) : Prop :=
  q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 11 ∨ q = 12

/-- The fixed PC0–PC60 prefix. All three cuts and worker costs come from
one scalar specification witness. The fuel bound reserves fifteen steps
for validation; this theorem stops at the validation entry. -/
theorem pair_search_prefix_from_pc0
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
    let firstCost : Nat := if x.val = 0 then 5 else 8
    ∃ (lo hi k predSteps xSteps ySteps n : Nat)
      (s20 s40 s60 : RamProgram.State (layout bits cap hcap))
      (hlo : lo ≤ hi) (hhi : hi ≤ c.second.len),
      Steps (program hcap (concreteSetup bits hone)) j
        (firstCost + predSteps) s s20 ∧
      s20.pc = 20 ∧ (setupReg s20 0).val = lo ∧
      Steps (program hcap (concreteSetup bits hone)) j
        (8 + xSteps) s20 s40 ∧
      s40.pc = 40 ∧ (setupReg s40 0).val = hi ∧
      setupReg s40 13 = setupReg s20 0 ∧
      Steps (program hcap (concreteSetup bits hone)) j
        (8 + ySteps) s40 s60 ∧
      s60.pc = 60 ∧ (setupReg s60 0).val = k ∧
      setupReg s60 13 = setupReg s20 0 ∧
      setupReg s60 14 = setupReg s40 0 ∧
      (setupReg s60 13).val = lo ∧ (setupReg s60 14).val = hi ∧
      setupReg s60 7 = c.first.base ∧ setupReg s60 9 = c.second.base ∧
      setupReg s60 11 = x ∧ setupReg s60 12 = y ∧
      IsBand c.first x lo hi ∧ k ≤ hi - lo ∧
      ColumnReduction.finish c.first c.second x y lo k =
        (PairLookup.lookup a (x.val, y.val)).1 ∧
      n = firstCost + predSteps + (8 + xSteps) + (8 + ySteps) ∧
      Steps (program hcap (concreteSetup bits hone)) j n s s60 ∧
      n + 15 ≤ 33 * (Nat.log2 (a.size + 1) + 1) + 39 := by
  intro firstCost
  obtain ⟨lo, hi, k, predSteps, xSteps, ySteps, hlo, hhi,
      hpred, hxCall, hband, hyCall, hfinish, hworkerCost⟩ :=
    PaperB.RamPairWorkerCalls.worker_calls_correct c hs x y

  have hsetupSaved (q : Fin 16) (hq : PairPrefixDescriptorReg q) :
      setupReg (firstSetupState hone s) q = setupReg s q := by
    rcases hq with rfl | rfl | rfl | rfl | rfl <;>
      by_cases hz : (setupReg s 11).val = 0 <;>
      simp (disch := decide) only [firstSetupState_regs, hz, if_pos, if_neg]

  have firstTrace :
      ∃ u, Steps (program hcap (concreteSetup bits hone)) j
          (firstCost + predSteps) s u ∧
        u.pc = 20 ∧ (setupReg u 0).val = lo ∧
        ∀ q, PairPrefixDescriptorReg q → setupReg u q = setupReg s q := by
    by_cases hz : x.val = 0
    · rw [if_pos hz] at hpred
      obtain ⟨hlo0, hcost0⟩ := hpred
      have hzr : (setupReg s 11).val = 0 := by
        simpa only [h11] using hz
      obtain ⟨ht, hp, hr⟩ := run_first_setup_zero_entry hcap hone j s hpc hzr
      refine ⟨firstSetupState hone s, ?_, hp, ?_, hsetupSaved⟩
      · simpa only [firstCost, if_pos hz, hcost0, Nat.add_zero] using ht
      · simpa only [hr, hlo0] using (show (zero bits).val = 0 from rfl)
    · rw [if_neg hz] at hpred
      obtain ⟨_, _, r, hr, hcut, _, hcost⟩ := hpred
      have hzr : (setupReg s 11).val ≠ 0 := by
        simpa only [h11] using hz
      obtain ⟨ht, _, ha⟩ :=
        run_first_setup_nonzero_entry hcap c.first hone j s hpc
          hzr h7 h8 h4 h5
      have hkey : firstSetupKey (setupReg s 11) =
          ColumnReduction.predecessor x := by
        rw [h11] <;> first
        | rfl
        | apply Fin.ext
          have hlt : x.val - 1 < 2 ^ bits :=
            Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt
          simp [firstSetupKey, ColumnReduction.predecessor, hz,
            Nat.mod_eq_of_lt hlt]
      rw [hkey] at ha
      obtain ⟨u, hw, hp, hout, hsave⟩ :=
        placed_worker_saved_frame hcap (concreteSetup bits hone) 0
          hr hwords ha
      refine ⟨u, ?_, hp, hout.trans hcut, ?_⟩
      · simpa only [firstCost, if_neg hz, hcost] using Steps.append ht hw
      · intro q hq
        have hq7 : 7 ≤ q.val := by
          rcases hq with rfl | rfl | rfl | rfl | rfl <;> decide
        exact (hsave q hq7).trans (hsetupSaved q hq)

  obtain ⟨s20, ht20, hp20, hlo20, hsave20⟩ := firstTrace
  have h207 : setupReg s20 7 = c.first.base :=
    (hsave20 7 (by decide)).trans h7
  have h208 : (setupReg s20 8).val = c.first.len :=
    (congrArg Fin.val (hsave20 8 (by decide))).trans h8
  have h2011 : setupReg s20 11 = x :=
    (hsave20 11 (by decide)).trans h11

  obtain ⟨_, _, rx, hrx, hcutx, _, hcostx⟩ := hxCall
  obtain ⟨s40, ht40, hp40, hout40, hframe40⟩ :=
    second_scalar_placed hcap hone c.first x s20
      hwords hp20 h207 h208 h2011 hrx
  have hhi40 : (setupReg s40 0).val = hi := hout40.trans hcutx
  have hwlo40 : setupReg s40 13 = setupReg s20 0 := by
    simpa [if_pos (rfl : (13 : Fin 16) = 13)] using
      hframe40 13 (by decide)
  have hlo40 : (setupReg s40 13).val = lo :=
    (congrArg Fin.val hwlo40).trans hlo20
  have hsave40 (q : Fin 16) (hq : PairPrefixDescriptorReg q)
      (hq7 : 7 ≤ q.val) (hne : q ≠ 13) :
      setupReg s40 q = setupReg s q := by
    calc
      setupReg s40 q = setupReg s20 q := by
        simpa only [if_neg hne] using hframe40 q hq7
      _ = setupReg s q := hsave20 q hq

  let band := c.second.sub lo hi hlo hhi
  have hbandBase : band.base.val = c.second.base.val + lo := by
    first
    | rfl
    | simp [band, Slice.sub]
  have hbandLen : band.len = hi - lo := by rfl
  have h409 : setupReg s40 9 = c.second.base :=
    (hsave40 9 (by decide) (by decide) (by decide)).trans h9
  have h4012 : setupReg s40 12 = y :=
    (hsave40 12 (by decide) (by decide) (by decide)).trans h12
  have haddr : (setupReg s40 9).val + (setupReg s40 13).val =
      band.base.val := by
    simpa only [h409, hlo40] using hbandBase.symm
  have horder : (setupReg s40 13).val ≤ (setupReg s40 0).val := by
    simpa only [hlo40, hhi40] using hlo
  have hlen : (setupReg s40 0).val - (setupReg s40 13).val = band.len := by
    simpa only [hhi40, hlo40] using hbandLen.symm

  obtain ⟨hyAnswer, _, ry, hry, hcuty, _, hcosty⟩ := hyCall
  have hk : k ≤ hi - lo := by
    have hk' : k ≤ band.len := hyAnswer.1
    simpa only [hbandLen] using hk'
  obtain ⟨s60, ht60, hp60, hout60, hframe60⟩ :=
    third_scalar_placed hcap hone band y s40
      hwords hp40 haddr horder hlen h4012 hry
  have hwlo60 : setupReg s60 13 = setupReg s20 0 := by
    calc
      setupReg s60 13 = setupReg s40 13 := by
        simpa only [if_neg (by decide : (13 : Fin 16) ≠ 14)] using
          hframe60 13 (by decide)
      _ = setupReg s20 0 := hwlo40
  have hwhi60 : setupReg s60 14 = setupReg s40 0 := by
    simpa [if_pos (rfl : (14 : Fin 16) = 14)] using
      hframe60 14 (by decide)
  have hsave60 (q : Fin 16) (hq : PairPrefixDescriptorReg q)
      (hq7 : 7 ≤ q.val) (hn13 : q ≠ 13) (hn14 : q ≠ 14) :
      setupReg s60 q = setupReg s q := by
    calc
      setupReg s60 q = setupReg s40 q := by
        simpa only [if_neg hn14] using hframe60 q hq7
      _ = setupReg s q := hsave40 q hq hq7 hn13
  have ht40' : Steps (program hcap (concreteSetup bits hone)) j
      (8 + xSteps) s20 s40 := by
    rw [← hcostx]
    exact ht40
  have ht60' : Steps (program hcap (concreteSetup bits hone)) j
      (8 + ySteps) s40 s60 := by
    rw [← hcosty]
    exact ht60
  have hfirstCost : firstCost ≤ 8 := by
    by_cases hz : x.val = 0
    · simp only [firstCost, if_pos hz]
      decide
    · simp only [firstCost, if_neg hz]
      exact Nat.le_refl 8
  refine ⟨lo, hi, k, predSteps, xSteps, ySteps,
    firstCost + predSteps + (8 + xSteps) + (8 + ySteps),
    s20, s40, s60, hlo, hhi,
    ht20, hp20, hlo20, ht40', hp40, hhi40, hwlo40,
    ht60', hp60, hout60.trans hcuty, hwlo60, hwhi60,
    (congrArg Fin.val hwlo60).trans hlo20,
    (congrArg Fin.val hwhi60).trans hhi40,
    (hsave60 7 (by decide) (by decide) (by decide) (by decide)).trans h7,
    (hsave60 9 (by decide) (by decide) (by decide) (by decide)).trans h9,
    (hsave60 11 (by decide) (by decide) (by decide) (by decide)).trans h11,
    (hsave60 12 (by decide) (by decide) (by decide) (by decide)).trans h12,
    hband, hk, hfinish, rfl,
    Steps.append (Steps.append ht20 ht40') ht60', ?_⟩
  omega

end PaperB.RamProgram.ThreeCalls
