module

public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! Load the source’s six prior-base words and write the inputs to the jump-map evaluator. -/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.BuiltExit (vjoin zero Test get_vjoin test_zero)
open PaperB.ExitSummary (endpointsInside_span_iff)
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

/-! Execution of one incoming-arc update in the prior-base sweep. -/

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4A_prepareLift_spec {code : Program DomL} {input : Input DomL}
    (loopPc N metaBase u v ownerDepth : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hBoundMeta : metaBase + 64 ≤ workCap)
    (hPriorBound : priorBase N + 6 * u + 6 ≤ metaBase)
    (hAncestry : Placed code (loopPc + 118) (step4A_ancestry loopPc h100))
    (hSz : loopPc + 406 < code.size)
    (s31 : State DomL) (hpc31 : s31.pc = loopPc + 137)
    (h0_31 : (reg s31 reg0).val = 0) (h1_31 : (reg s31 reg1).val = 1)
    (hM_31 : (reg s31 rMeta).val = metaBase)
    (h5_31 : (reg s31 reg5).val = u) (h6_31 : (reg s31 reg6).val = v)
    (hOwnDep : (s31.data[metaBase + 52]?).map Fin.val = some ownerDepth)
    (hPrior : (s31.data[metaBase + mIdxPriorBase]?).map Fin.val = some (priorBase N))
    (xs : Values) (hValues : ValuesWordsAt s31.data (priorBase N + 6 * u) xs) :
    ∃ t, Steps code input 40 s31 t ∧ t.pc = loopPc + 177 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      (t.data[metaBase + mIdxEvalU]?).map Fin.val = some v ∧
      (t.data[metaBase + mIdxEvalD]?).map Fin.val = some ownerDepth ∧
      ValuesWordsAt t.data (metaBase + mIdxEval0) xs ∧
      (∀ j, j ≠ metaBase + mIdxEvalU → j ≠ metaBase + mIdxEvalD →
        (j < metaBase + mIdxEval0 ∨ metaBase + mIdxEval0 + 6 ≤ j) →
        t.data[j]? = s31.data[j]?) := by
  have placed := step4A_liftPreparation_placed hAncestry
  -- Store `mIdxEvalU := v`, load `ownerDepth`, store `mIdxEvalD`:
  have hPlEU : Placed code (loopPc + 137) (metaStoreInstrs (bits := bits) reg6 reg8 mIdxEvalU (by dsimp only [mIdxEvalU]; omega)) :=
    Placed_window placed 0 rfl
  obtain ⟨s32, hs32, hpc32, hAt32, hFr32, hPres32⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlEU (by omega) hpc31 hM_31 (by dsimp only [mIdxEvalU]; omega)
    (lt_data_size (by dsimp only [mIdxEvalU]; omega))
  have hM_32 : (reg s32 rMeta).val = metaBase := by rw [hPres32 rMeta (by intro h; cases h), hM_31]
  have hPlOD : Placed code (loopPc + 140) (metaLoadInstrs (bits := bits) reg7 reg8 52 (by omega)) :=
    Placed_window placed 3 rfl
  obtain ⟨s33, hs33, hpc33, hd33, h7_33, hPres33⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlOD (by omega) hpc32 hM_32 (by omega)
    (by rw [hFr32 (metaBase + 52) (by dsimp only [mIdxEvalU]; omega)]; exact hOwnDep)
  have hM_33 : (reg s33 rMeta).val = metaBase := by rw [hPres33 rMeta (by intro h; cases h) (by intro h; cases h), hM_32]
  have hPlED : Placed code (loopPc + 143) (metaStoreInstrs (bits := bits) reg7 reg8 mIdxEvalD (by dsimp only [mIdxEvalD]; omega)) :=
    Placed_window placed 6 rfl
  obtain ⟨s34, hs34, hpc34, hAt34, hFr34, hPres34⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlED (by omega) hpc33 hM_33 (by dsimp only [mIdxEvalD]; omega)
    (lt_data_size (by dsimp only [mIdxEvalD]; omega))
  have hM_34 : (reg s34 rMeta).val = metaBase := by rw [hPres34 rMeta (by intro h; cases h), hM_33]
  have h5_34 : (reg s34 reg5).val = u := by
    rw [hPres34 reg5 (by intro h; cases h), hPres33 reg5 (by intro h; cases h) (by intro h; cases h),
      hPres32 reg5 (by intro h; cases h), h5_31]
  -- Load `mIdxPriorBase`, mul6 `u`, add, set `reg2 = metaBase + 36`, `copy6`:
  have hPlPB : Placed code (loopPc + 146) (metaLoadInstrs (bits := bits) reg3 reg8 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega)) :=
    Placed_window placed 9 rfl
  obtain ⟨s35, hs35, hpc35, hd35, h3_35, hPres35⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlPB (by omega) hpc34 hM_34 (by dsimp only [mIdxPriorBase]; omega)
    (by
      rw [hFr34 _ (by dsimp only [mIdxPriorBase, mIdxEvalD]; omega), hd33,
        hFr32 _ (by dsimp only [mIdxPriorBase, mIdxEvalU]; omega)]
      exact hPrior)
  have h5_35 : (reg s35 reg5).val = u := by rw [hPres35 reg5 (by intro h; cases h) (by intro h; cases h), h5_34]
  have haM1 : code[s35.pc]? = some (.add reg4 reg5 reg5) := by rw [hpc35]; exact placed 12 _ rfl
  obtain ⟨s36, hs36Raw, hpc36, h4_36, ho36, hd36⟩ := step_add_at (input := input) haM1 (by omega)
  have hs36 := steps_1_of_step hs36Raw
  have h4Val36 : (reg s36 reg4).val = 2 * u := by
    rw [h4_36, add_no_wrap _ _ (by rw [h5_35]; omega), h5_35]; omega
  have haM2 : code[s36.pc]? = some (.add reg4 reg4 reg5) := by rw [hpc36, hpc35]; exact placed 13 _ rfl
  obtain ⟨s37, hs37Raw, hpc37, h4_37, ho37, hd37⟩ := step_add_at (input := input) haM2 (by omega)
  have hs37 := steps_1_of_step hs37Raw
  have h4Val37 : (reg s37 reg4).val = 3 * u := by
    rw [h4_37, add_no_wrap _ _ (by rw [h4Val36, ho36 reg5 (by intro h; cases h), h5_35]; omega),
      h4Val36, ho36 reg5 (by intro h; cases h), h5_35]; omega
  have haM3 : code[s37.pc]? = some (.add reg4 reg4 reg4) := by rw [hpc37, hpc36, hpc35]; exact placed 14 _ rfl
  obtain ⟨s38, hs38Raw, hpc38, h4_38, ho38, hd38⟩ := step_add_at (input := input) haM3 (by omega)
  have hs38 := steps_1_of_step hs38Raw
  have h4Val38 : (reg s38 reg4).val = 6 * u := by
    rw [h4_38, add_no_wrap _ _ (by rw [h4Val37]; omega), h4Val37]; omega
  have h3_38 : (reg s38 reg3).val = priorBase N := by
    rw [ho38 reg3 (by intro h; cases h), ho37 reg3 (by intro h; cases h),
      ho36 reg3 (by intro h; cases h), h3_35]
  have haAP : code[s38.pc]? = some (.add reg3 reg3 reg4) := by rw [hpc38, hpc37, hpc36, hpc35]; exact placed 15 _ rfl
  obtain ⟨s39, hs39Raw, hpc39, h3_39, ho39, hd39⟩ := step_add_at (input := input) haAP (by omega)
  have hs39 := steps_1_of_step hs39Raw
  have h3Val39 : (reg s39 reg3).val = priorBase N + 6 * u := by
    rw [h3_39, add_no_wrap _ _ (by rw [h3_38, h4Val38]; exact Nat.lt_of_lt_of_le (by omega) hw), h3_38, h4Val38]
  have haI3 : code[s39.pc]? = some (.imm reg2 ⟨36, by omega⟩) := by rw [hpc39, hpc38, hpc37, hpc36, hpc35]; exact placed 16 _ rfl
  obtain ⟨s40, hs40Raw, hpc40, h2_40, ho40, hd40⟩ := step_imm_at (input := input) haI3 (by omega)
  have hs40 := steps_1_of_step hs40Raw
  have hRM40 : (reg s40 rMeta).val = metaBase := by
    rw [ho40 rMeta (by intro h; cases h), ho39 rMeta (by intro h; cases h),
      ho38 rMeta (by intro h; cases h), ho37 rMeta (by intro h; cases h),
      ho36 rMeta (by intro h; cases h), hPres35 rMeta (by intro h; cases h) (by intro h; cases h), hM_34]
  have haAE0 : code[s40.pc]? = some (.add reg2 rMeta reg2) := by rw [hpc40, hpc39, hpc38, hpc37, hpc36, hpc35]; exact placed 17 _ rfl
  obtain ⟨s41, hs41Raw, hpc41, h2_41, ho41, hd41⟩ := step_add_at (input := input) haAE0 (by omega)
  have hs41 := steps_1_of_step hs41Raw
  have h2Val41 : (reg s41 reg2).val = metaBase + mIdxEval0 := by
    rw [h2_41, add_no_wrap _ _ (by rw [hRM40, h2_40]; change metaBase + 36 < 2 ^ bits; omega), hRM40, h2_40]
  have h3Val41 : (reg s41 reg3).val = priorBase N + 6 * u := by
    rw [ho41 reg3 (by intro h; cases h), ho40 reg3 (by intro h; cases h), h3Val39]
  have h0_41 : (reg s41 reg0).val = 0 := by
    rw [ho41 reg0 (by intro h; cases h), ho40 reg0 (by intro h; cases h),
      ho39 reg0 (by intro h; cases h), ho38 reg0 (by intro h; cases h),
      ho37 reg0 (by intro h; cases h), ho36 reg0 (by intro h; cases h),
      hPres35 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres34 reg0 (by intro h; cases h), hPres33 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres32 reg0 (by intro h; cases h), h0_31]
  have h1_41 : (reg s41 reg1).val = 1 := by
    rw [ho41 reg1 (by intro h; cases h), ho40 reg1 (by intro h; cases h),
      ho39 reg1 (by intro h; cases h), ho38 reg1 (by intro h; cases h),
      ho37 reg1 (by intro h; cases h), ho36 reg1 (by intro h; cases h),
      hPres35 reg1 (by intro h; cases h) (by intro h; cases h),
      hPres34 reg1 (by intro h; cases h), hPres33 reg1 (by intro h; cases h) (by intro h; cases h),
      hPres32 reg1 (by intro h; cases h), h1_31]
  have hRM41 : (reg s41 rMeta).val = metaBase := by rw [ho41 rMeta (by intro h; cases h), hRM40]
  have hData41 : ∀ j, j ≠ metaBase + mIdxEvalU → j ≠ metaBase + mIdxEvalD →
      s41.data[j]? = s31.data[j]? := by
    intro j hj1 hj2
    rw [hd41, hd40, hd39, hd38, hd37, hd36, hd35, hFr34 j hj2, hd33, hFr32 j hj1]
  have hBaseU41 : ValuesWordsAt s41.data (priorBase N + 6 * u) xs :=
    valuesWordsAt_frame (fun i hi => hData41 (priorBase N + 6 * u + i)
      (by dsimp only [mIdxEvalU]; omega) (by dsimp only [mIdxEvalD]; omega)) hValues
  have hPlC6 : Placed code (loopPc + 155) (copy6Instrs (bits := bits) reg2 reg3 reg4) :=
    Placed_window placed 18 rfl
  obtain ⟨s42, hs42, hpc42, hVals42, hPres42, hFr42⟩ := run_copy6 (input := input)
    (loopPc + 155) reg2 reg3 reg4
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPlC6 (by omega) (priorBase N + 6 * u) (metaBase + mIdxEval0) xs
    (Nat.lt_of_lt_of_le (by omega) hw) (by dsimp only [mIdxEval0]; omega) (by dsimp only [mIdxEval0]; omega)
    (Or.inr (by dsimp only [mIdxEval0]; omega))
    s41 (by rw [hpc41, hpc40, hpc39, hpc38, hpc37, hpc36, hpc35])
    h1_41 h3Val41 h2Val41 hBaseU41
  have hTrace : Steps code input 40 s31 s42 :=
    hs32.append (hs33.append (hs34.append (hs35.append
      (hs36.append (hs37.append (hs38.append (hs39.append
        (hs40.append (hs41.append hs42)))))))))
  refine ⟨s42, hTrace, hpc42, ?_, ?_, ?_, ?_, ?_, hVals42, ?_⟩
  · rw [hPres42 reg0 (by decide) (by decide) (by decide), h0_41]
  · rw [hPres42 reg1 (by decide) (by decide) (by decide), h1_41]
  · rw [hPres42 rMeta (by decide) (by decide) (by decide), hRM41]
  · rw [hFr42 (metaBase + mIdxEvalU) (Or.inl (by dsimp only [mIdxEvalU, mIdxEval0]; omega)),
      hd41, hd40, hd39, hd38, hd37, hd36, hd35,
      hFr34 _ (by dsimp only [mIdxEvalU, mIdxEvalD]; omega), hd33,
      hAt32, Option.map_some, h6_31]
  · rw [hFr42 (metaBase + mIdxEvalD) (Or.inl (by dsimp only [mIdxEvalD, mIdxEval0]; omega)),
      hd41, hd40, hd39, hd38, hd37, hd36, hd35, hAt34, Option.map_some, h7_33]
  · intro j hU hD hX
    rw [hFr42 j hX, hData41 j hU hD]

end PaperB.RamProgram.ExitSummaryBuild
