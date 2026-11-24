module

public import PaperB.RamExitSummaryEvalROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.ArcParents
open PaperB.ForestHead (Vertex)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open PaperB.RetainedProperLoss (encodeBackPair encodeBackPair_eq_iff ofOrderedReader)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalDepthColumn
open PaperB.Exit.OrderedReaderResult
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)

/-! Apply the selected map, copy the result back, and loop. -/

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_eval15Apply {code : Program DomL} {input : Input DomL}
    {basePc : Nat} {h100 : 100 ≤ 2 ^ bits}
    (hPl : Placed code basePc (eval15Instrs basePc h100))
    (hSz : basePc + 161 < code.size)
    {base mapAddr : Nat} (hFit : base + 48 ≤ workCap)
    (hMapBound : mapAddr + 8 ≤ base + mIdxEval0)
    {map : Map} {xs : Values}
    {s21 : State DomL} (hpc21 : s21.pc = basePc + 33)
    (h0_21 : (reg s21 reg0).val = 0) (h1_21 : (reg s21 reg1).val = 1)
    (hM_21 : (reg s21 rMeta).val = base) (h2_21 : (reg s21 reg2).val = mapAddr)
    (hMap : MapWordsAt s21.data mapAddr map)
    (hVals : ValuesWordsAt s21.data (base + mIdxEval0) xs) :
    ∃ k : Nat, ∃ t : State DomL, k ≤ 106 ∧ Steps code input k s21 t ∧
      t.pc = basePc ∧ (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = base ∧ ValuesWordsAt t.data (base + mIdxEval0) (Map.eval map xs) ∧
      (∀ j, (j < base + mIdxEval0 ∨ base + 48 ≤ j) → t.data[j]? = s21.data[j]?) := by
  have hMapEvalPl := placed_eval15_mapEval hPl
  have hCopy6Pl := placed_eval15_copy6 hPl
  have hMapFit : mapAddr + 7 < 2 ^ bits := by
    dsimp only [mIdxEval0] at hMapBound
    omega
  -- PCs 33..36 (4 steps) -> PC basePc + 37
  obtain ⟨s22, hs22, hpc22, h5_22, ho22, hd22⟩ := step_imm_at (input := input)
    (by rw [hpc21]; exact hPl 33 _ rfl) (by omega)
  have h5V22 : (reg s22 reg5).val = mIdxEval0 := by rw [h5_22]
  have hM_22 : (reg s22 rMeta).val = base := by rw [ho22 rMeta (by intro h; cases h), hM_21]
  obtain ⟨s23, hs23, hpc23, h3_23, ho23, hd23⟩ := step_add_at (input := input)
    (by rw [hpc22, hpc21]; exact hPl 34 _ rfl) (by omega)
  have h3V23 : (reg s23 reg3).val = base + mIdxEval0 := by
    rw [h3_23, add_no_wrap _ _ (by rw [hM_22, h5V22]; dsimp only [mIdxEval0]; omega), hM_22, h5V22]
  obtain ⟨s24, hs24, hpc24, h5_24, ho24, hd24⟩ := step_imm_at (input := input)
    (by rw [hpc23, hpc22, hpc21]; exact hPl 35 _ rfl) (by omega)
  have h5V24 : (reg s24 reg5).val = mIdxTmp0 := by rw [h5_24]
  have hM_24 : (reg s24 rMeta).val = base := by
    rw [ho24 rMeta (by intro h; cases h), ho23 rMeta (by intro h; cases h), hM_22]
  obtain ⟨s25, hs25, hpc25, h4_25, ho25, hd25⟩ := step_add_at (input := input)
    (by rw [hpc24, hpc23, hpc22, hpc21]; exact hPl 36 _ rfl) (by omega)
  have h4V25 : (reg s25 reg4).val = base + mIdxTmp0 := by
    rw [h4_25, add_no_wrap _ _ (by rw [hM_24, h5V24]; dsimp only [mIdxTmp0]; omega), hM_24, h5V24]
  have hPres25 : ∀ r : Fin 15, r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → reg s25 r = reg s21 r :=
    fun r hr3 hr4 hr5 => by rw [ho25 r hr4, ho24 r hr5, ho23 r hr3, ho22 r hr5]
  have hd25' : s25.data = s21.data := by rw [hd25, hd24, hd23, hd22]
  have hMapWords25 : MapWordsAt s25.data mapAddr map := by
    rw [hd25']; exact hMap
  have hVals25 : ValuesWordsAt s25.data (base + mIdxEval0) xs := by
    rw [hd25']; exact hVals
  have hDisjMap : base + mIdxTmp0 + 6 ≤ mapAddr ∨
      mapAddr + 8 ≤ base + mIdxTmp0 := by
    right
    dsimp only [mIdxTmp0, mIdxEval0] at *
    omega
  have hDisjVal : base + mIdxTmp0 + 6 ≤ base + mIdxEval0 ∨
      base + mIdxEval0 + 6 ≤ base + mIdxTmp0 := by
    right; dsimp only [mIdxEval0, mIdxTmp0]; omega
  obtain ⟨kEv, s26, hkEv, hStepsEv, hpc26, hVals26, hPresEv, hFrEv⟩ :=
    run_mapEval (input := input) (basePc + 37) hMapEvalPl (by omega) mapAddr
      (base + mIdxEval0) (base + mIdxTmp0) map xs
      hMapFit
      (by dsimp only [mIdxEval0]; omega)
      (by dsimp only [mIdxTmp0]; omega)
      (by dsimp only [mIdxTmp0]; omega)
      hDisjMap hDisjVal s25 (by omega)
      (by rw [hPres25 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_21])
      (by rw [hPres25 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_21])
      (by rw [hPres25 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2_21])
      (by rw [ho25 reg3 (by intro h; cases h), ho24 reg3 (by intro h; cases h), h3V23])
      h4V25 hMapWords25 hVals25
  -- PCs 136..137: imm r5 mIdxTmp0; add r4 rMeta r5
  obtain ⟨s27, hs27, hpc27, h5_27, ho27, hd27⟩ := step_imm_at (input := input)
    (by rw [hpc26]; exact hPl 136 _ rfl) (by omega)
  have hM_27 : (reg s27 rMeta).val = base := by
    rw [ho27 rMeta (by intro h; cases h), hPresEv rMeta (Or.inr (Or.inr (Or.inr (Or.inr rfl)))),
      hPres25 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM_21]
  obtain ⟨s28, hs28, hpc28, h4_28, ho28, hd28⟩ := step_add_at (input := input)
    (by rw [hpc27, hpc26]; exact hPl 137 _ rfl) (by omega)
  have h4V28 : (reg s28 reg4).val = base + mIdxTmp0 := by
    rw [h4_28, add_no_wrap _ _ (by rw [hM_27, h5_27]; dsimp only [mIdxTmp0]; omega), hM_27, h5_27]
  have h3V28 : (reg s28 reg3).val = base + mIdxEval0 := by
    rw [ho28 reg3 (by intro h; cases h), ho27 reg3 (by intro h; cases h),
      hPresEv reg3 (Or.inr (Or.inr (Or.inl rfl))),
      ho25 reg3 (by intro h; cases h), ho24 reg3 (by intro h; cases h), h3V23]
  have h1_28 : (reg s28 reg1).val = 1 := by
    rw [ho28 reg1 (by intro h; cases h), ho27 reg1 (by intro h; cases h),
      hPresEv reg1 (Or.inr (Or.inl rfl)),
      hPres25 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_21]
  have hVals28 : ValuesWordsAt s28.data (base + mIdxTmp0) (Map.eval map xs) := by
    rw [hd28, hd27]; exact hVals26
  -- PCs 138..159: run_copy6 (src = r4 = Tmp0, dst = r3 = Eval0)
  obtain ⟨s29, hStepsCopy, hpc29, hVals29, hPresCopy, hFrCopy⟩ :=
    run_copy6 (input := input) (basePc + 138) reg3 reg4 reg5
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      hCopy6Pl (by omega)
      (base + mIdxTmp0) (base + mIdxEval0) (Map.eval map xs)
      (by dsimp only [mIdxTmp0]; omega) (by dsimp only [mIdxEval0]; omega)
      (by dsimp only [mIdxEval0]; omega)
      (Or.inl (by dsimp only [mIdxEval0, mIdxTmp0]; omega))
      s28 (by omega) h1_28 h4V28 h3V28 hVals28
  -- PC 160: goto basePc
  obtain ⟨sEnd, hsEnd, hpcEnd, hrEnd, hdEnd⟩ := step_goto_at (input := input)
    (by rw [hpc29]; exact hPl 160 _ rfl) (by omega)
  have hrEndF := reg_of_regs_eq hrEnd
  have hPrep : Steps code input 4 s21 s25 :=
    Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24 (steps_1_of_step hs25)))
  have hReload : Steps code input 2 s26 s28 := Steps.cons hs27 (steps_1_of_step hs28)
  refine ⟨4 + kEv + 2 + 22 + 1, sEnd, by omega,
    ((((hPrep.append hStepsEv).append hReload).append hStepsCopy).append (steps_1_of_step hsEnd)),
    hpcEnd, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrEndF, hPresCopy reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
      ho28 reg0 (by intro h; cases h), ho27 reg0 (by intro h; cases h),
      hPresEv reg0 (Or.inl rfl),
      hPres25 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_21]
  · rw [hrEndF, hPresCopy reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_28]
  · rw [hrEndF, hPresCopy rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
      ho28 rMeta (by intro h; cases h), hM_27]
  · rw [hdEnd]; exact hVals29
  · intro j hj
    rw [hdEnd, hFrCopy j (by dsimp only [mIdxEval0] at *; rcases hj with h | h <;> omega),
      hd28, hd27, hFrEv j (by dsimp only [mIdxEval0, mIdxTmp0] at *; rcases hj with h | h <;> omega),
      hd25']

end PaperB.RamProgram.ExitSummaryBuild
