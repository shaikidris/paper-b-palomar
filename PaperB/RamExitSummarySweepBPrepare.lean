module

public import PaperB.RamExitSummarySweepBROM
public import PaperB.RamExitSummarySweepAROM
public import PaperB.RamExitSummarySweepZero

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000

/-! Prepare the endpoint’s prior-base record and inputs for the jump-map evaluator. -/

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

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4BFresh_prepare_spec {code : Program DomL} {input : Input DomL}
    (basePc N metaBase z v dp : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hInCap : 4 + z < inputCap)
    (hPriorBound : priorBase N + 6 * z + 6 ≤ metaBase)
    (hBoundMeta : metaBase + 64 ≤ workCap)
    (hPrep : Placed code (basePc + 13) (step4BFresh_prepare h100))
    (hLoad : Placed code (basePc + 36) (copy6Instrs reg2 reg3 reg4))
    (hSz : basePc + 238 < code.size)
    (s7 : State DomL) (hpc7 : s7.pc = basePc + 13)
    (h0_7 : (reg s7 reg0).val = 0) (h1_7 : (reg s7 reg1).val = 1)
    (hM_7 : (reg s7 rMeta).val = metaBase) (h2_7 : (reg s7 reg2).val = z)
    (hMetaLabels : (s7.data[metaBase + mIdxLabelsInBase]?).map Fin.val = some 4)
    (hLabel : (input.words[4 + z]?).map Fin.val = some v)
    (hdpMem : (s7.data[metaBase + 54]?).map Fin.val = some dp)
    (hMetaPrior : (s7.data[metaBase + mIdxPriorBase]?).map Fin.val = some (priorBase N))
    (baseZ : Values) (hValues : ValuesWordsAt s7.data (priorBase N + 6 * z) baseZ) :
    ∃ t, Steps code input 45 s7 t ∧ t.pc = basePc + 58 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      (t.data[metaBase + mIdxEvalU]?).map Fin.val = some v ∧
      (t.data[metaBase + mIdxEvalD]?).map Fin.val = some dp ∧
      ValuesWordsAt t.data (metaBase + mIdxEval0) baseZ ∧
      (∀ j, j ≠ metaBase + mIdxEvalU → j ≠ metaBase + mIdxEvalD →
        (j < metaBase + mIdxEval0 ∨ metaBase + mIdxEval0 + 6 ≤ j) →
        t.data[j]? = s7.data[j]?) := by
  have hOffsetLt (off : Nat) (hOff : off < 64) : metaBase + off < workCap := by omega
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (hOffsetLt off hOff) hw
  -- Load `v = input[4 + z]`, store `mIdxEvalU`, load `dp`, store `mIdxEvalD`, load `priorBase`, mul6, add, copy6, `eval15`, goto:
  have hPlLab : Placed code (basePc + 13) (metaLoadInstrs (bits := bits) reg4 reg7 mIdxLabelsInBase (by dsimp only [mIdxLabelsInBase]; omega)) :=
    Placed_window hPrep 0 rfl
  obtain ⟨s8, hs8, hpc8, hd8, h4_8, hPres8⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlLab (by omega) hpc7 hM_7 (hOffsetFit mIdxLabelsInBase (by decide))
    hMetaLabels
  have h2_8 : (reg s8 reg2).val = z := by rw [hPres8 reg2 (by intro h; cases h) (by intro h; cases h), h2_7]
  have haAL : code[s8.pc]? = some (.add reg4 reg4 reg2) := by rw [hpc8]; exact hPrep 3 _ rfl
  obtain ⟨s9, hs9Raw, hpc9, h4_9, ho9, hd9⟩ := step_add_at (input := input) haAL (by omega)
  have hs9 := steps_1_of_step hs9Raw
  have h4Val9 : (reg s9 reg4).val = 4 + z := by rw [h4_9, add_no_wrap _ _ (by rw [h4_8, h2_8]; omega), h4_8, h2_8]
  obtain ⟨wv, hwv, hwvV⟩ := Option.map_eq_some_iff.mp hLabel
  have haLL : code[s9.pc]? = some (.loadInput reg4 reg4) := by rw [hpc9, hpc8]; exact hPrep 4 _ rfl
  obtain ⟨s10, hs10Raw, hpc10, h4_10, ho10, hd10⟩ := step_loadInput_at (input := input) haLL (by omega) (by rw [h4Val9]; exact hwv)
  have hs10 := steps_1_of_step hs10Raw
  have hvVal : (reg s10 reg4).val = v := by rw [h4_10, hwvV]
  have hM_10 : (reg s10 rMeta).val = metaBase := by
    rw [ho10 rMeta (by intro h; cases h), ho9 rMeta (by intro h; cases h),
      hPres8 rMeta (by intro h; cases h) (by intro h; cases h), hM_7]
  have hPlSU : Placed code (basePc + 18) (metaStoreInstrs (bits := bits) reg4 reg7 mIdxEvalU (by dsimp only [mIdxEvalU]; omega)) :=
    Placed_window hPrep 5 rfl
  obtain ⟨s11, hs11, hpc11, hAt11, hFr11, hPres11⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSU (by omega) (by rw [hpc10, hpc9, hpc8]) hM_10 (hOffsetFit mIdxEvalU (by decide))
    (lt_data_size (hOffsetLt mIdxEvalU (by decide)))
  have hM_11 : (reg s11 rMeta).val = metaBase := by rw [hPres11 rMeta (by intro h; cases h), hM_10]
  have hPlLD : Placed code (basePc + 21) (metaLoadInstrs (bits := bits) reg4 reg7 54 (by omega)) :=
    Placed_window hPrep 8 rfl
  obtain ⟨s12, hs12, hpc12, hd12, h4_12, hPres12⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlLD (by omega) hpc11 hM_11 (by omega)
    (by rw [hFr11 _ (by dsimp only [mIdxEvalU]; omega), hd10, hd9, hd8]; exact hdpMem)
  have hM_12 : (reg s12 rMeta).val = metaBase := by rw [hPres12 rMeta (by intro h; cases h) (by intro h; cases h), hM_11]
  have hPlSD : Placed code (basePc + 24) (metaStoreInstrs (bits := bits) reg4 reg7 mIdxEvalD (by dsimp only [mIdxEvalD]; omega)) :=
    Placed_window hPrep 11 rfl
  obtain ⟨s13, hs13, hpc13, hAt13, hFr13, hPres13⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSD (by omega) hpc12 hM_12 (hOffsetFit mIdxEvalD (by decide))
    (lt_data_size (hOffsetLt mIdxEvalD (by decide)))
  have hM_13 : (reg s13 rMeta).val = metaBase := by rw [hPres13 rMeta (by intro h; cases h), hM_12]
  have h2_13 : (reg s13 reg2).val = z := by
    rw [hPres13 reg2 (by intro h; cases h), hPres12 reg2 (by intro h; cases h) (by intro h; cases h),
      hPres11 reg2 (by intro h; cases h), ho10 reg2 (by intro h; cases h), ho9 reg2 (by intro h; cases h), h2_8]
  have hPlPB : Placed code (basePc + 27) (metaLoadInstrs (bits := bits) reg3 reg7 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega)) :=
    Placed_window hPrep 14 rfl
  obtain ⟨s14, hs14, hpc14, hd14, h3_14, hPres14⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlPB (by omega) hpc13 hM_13 (hOffsetFit mIdxPriorBase (by decide))
    (by rw [hFr13 _ (by dsimp only [mIdxPriorBase, mIdxEvalD]; omega), hd12,
        hFr11 _ (by dsimp only [mIdxPriorBase, mIdxEvalU]; omega), hd10, hd9, hd8]; exact hMetaPrior)
  have h2_14 : (reg s14 reg2).val = z := by rw [hPres14 reg2 (by intro h; cases h) (by intro h; cases h), h2_13]
  have hPlMul : Placed code (basePc + 30) (mul6Instrs (bits := bits) reg4 reg2) :=
    Placed_window hPrep 17 rfl
  obtain ⟨s17, hs17, hpc17, hd17, h4Val17, hMulRegs⟩ := steps_add_mul6 (input := input)
    (by decide : reg4 ≠ reg2) hPlMul (by omega) s14 hpc14 (by rw [h2_14]; omega)
  rw [h2_14] at h4Val17
  have h3_17 : (reg s17 reg3).val = priorBase N := by
    rw [hMulRegs reg3 (by intro h; cases h), h3_14]
  have haAP : code[s17.pc]? = some (.add reg3 reg3 reg4) := by rw [hpc17]; exact hPrep 20 _ rfl
  obtain ⟨s18, hs18Raw, hpc18, h3_18, ho18, hd18⟩ := step_add_at (input := input) haAP (by omega)
  have hs18 := steps_1_of_step hs18Raw
  have h3Val18 : (reg s18 reg3).val = priorBase N + 6 * z := by
    rw [h3_18, add_no_wrap _ _ (by rw [h3_17, h4Val17]; omega), h3_17, h4Val17]
  have haIE : code[s18.pc]? = some (.imm reg2 ⟨36, by omega⟩) := by rw [hpc18, hpc17]; exact hPrep 21 _ rfl
  obtain ⟨s19, hs19Raw, hpc19, h2_19, ho19, hd19⟩ := step_imm_at (input := input) haIE (by omega)
  have hs19 := steps_1_of_step hs19Raw
  have hM_19 : (reg s19 rMeta).val = metaBase := by
    rw [ho19 rMeta (by intro h; cases h), ho18 rMeta (by intro h; cases h),
      hMulRegs rMeta (by intro h; cases h), hPres14 rMeta (by intro h; cases h) (by intro h; cases h), hM_13]
  have haAE : code[s19.pc]? = some (.add reg2 rMeta reg2) := by rw [hpc19, hpc18, hpc17]; exact hPrep 22 _ rfl
  obtain ⟨s20, hs20Raw, hpc20, h2_20, ho20, hd20⟩ := step_add_at (input := input) haAE (by omega)
  have hs20 := steps_1_of_step hs20Raw
  have h2Val20 : (reg s20 reg2).val = metaBase + mIdxEval0 := by
    rw [h2_20, add_no_wrap _ _ (by rw [hM_19, h2_19]; change metaBase + 36 < 2 ^ bits; omega), hM_19, h2_19]
  have h3Val20 : (reg s20 reg3).val = priorBase N + 6 * z := by
    rw [ho20 reg3 (by intro h; cases h), ho19 reg3 (by intro h; cases h), h3Val18]
  have h1_20 : (reg s20 reg1).val = 1 := by
    rw [ho20 reg1 (by intro h; cases h), ho19 reg1 (by intro h; cases h), ho18 reg1 (by intro h; cases h),
      hMulRegs reg1 (by intro h; cases h),
      hPres14 reg1 (by intro h; cases h) (by intro h; cases h), hPres13 reg1 (by intro h; cases h),
      hPres12 reg1 (by intro h; cases h) (by intro h; cases h), hPres11 reg1 (by intro h; cases h),
      ho10 reg1 (by intro h; cases h), ho9 reg1 (by intro h; cases h),
      hPres8 reg1 (by intro h; cases h) (by intro h; cases h), h1_7]
  have h0_20 : (reg s20 reg0).val = 0 := by
    rw [ho20 reg0 (by intro h; cases h), ho19 reg0 (by intro h; cases h), ho18 reg0 (by intro h; cases h),
      hMulRegs reg0 (by intro h; cases h),
      hPres14 reg0 (by intro h; cases h) (by intro h; cases h), hPres13 reg0 (by intro h; cases h),
      hPres12 reg0 (by intro h; cases h) (by intro h; cases h), hPres11 reg0 (by intro h; cases h),
      ho10 reg0 (by intro h; cases h), ho9 reg0 (by intro h; cases h),
      hPres8 reg0 (by intro h; cases h) (by intro h; cases h), h0_7]
  have hM_20 : (reg s20 rMeta).val = metaBase := by rw [ho20 rMeta (by intro h; cases h), hM_19]
  have hData20 : ∀ j, j ≠ metaBase + mIdxEvalU → j ≠ metaBase + mIdxEvalD → s20.data[j]? = s7.data[j]? := fun j h1 h2 => by
    rw [hd20, hd19, hd18, hd17, hd14, hFr13 j h2, hd12, hFr11 j h1, hd10, hd9, hd8]
  have hDataLow : ∀ j, j < metaBase → s20.data[j]? = s7.data[j]? := by
    intro j hj
    exact hData20 j (by dsimp only [mIdxEvalU]; omega) (by dsimp only [mIdxEvalD]; omega)
  have hValues20 : ValuesWordsAt s20.data (priorBase N + 6 * z) baseZ :=
    valuesWordsAt_frame (fun i hi => hDataLow _ (by omega)) hValues
  have hPlC6 : Placed code (basePc + 36) (copy6Instrs (bits := bits) reg2 reg3 reg4) :=
    hLoad
  obtain ⟨s21, hs21, hpc21, hVals21, hPres21, hFr21⟩ := run_copy6 (input := input) (basePc + 36) reg2 reg3 reg4
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPlC6 (by omega) (priorBase N + 6 * z) (metaBase + mIdxEval0) baseZ
    (by omega) (by dsimp only [mIdxEval0]; omega) (by dsimp only [mIdxEval0]; omega)
    (Or.inr (by dsimp only [mIdxEval0]; omega))
    s20 (by rw [hpc20, hpc19, hpc18, hpc17]) h1_20 h3Val20 h2Val20 hValues20
  have hTracePrep : Steps code input 23 s7 s20 :=
    hs8.append (hs9.append (hs10.append (hs11.append (hs12.append (hs13.append
      (hs14.append (hs17.append (hs18.append (hs19.append hs20)))))))))
  refine ⟨s21, hTracePrep.append hs21, hpc21, ?_, ?_, ?_, ?_, ?_, hVals21, ?_⟩
  · rw [hPres21 reg0 (by decide) (by decide) (by decide), h0_20]
  · rw [hPres21 reg1 (by decide) (by decide) (by decide), h1_20]
  · rw [hPres21 rMeta (by decide) (by decide) (by decide), hM_20]
  · rw [hFr21 (metaBase + mIdxEvalU) (Or.inl (by dsimp only [mIdxEvalU, mIdxEval0]; omega)),
      hd20, hd19, hd18, hd17, hd14, hFr13 _ (by dsimp only [mIdxEvalU, mIdxEvalD]; omega),
      hd12, hAt11, Option.map_some, hvVal]
  · rw [hFr21 (metaBase + mIdxEvalD) (Or.inl (by dsimp only [mIdxEvalD, mIdxEval0]; omega)),
      hd20, hd19, hd18, hd17, hd14, hAt13, Option.map_some, h4_12]
  · intro j hU hD hX
    rw [hFr21 j hX, hData20 j hU hD]

end PaperB.RamProgram.ExitSummaryBuild
