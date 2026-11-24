module

public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

/-! Copy the completed pair of intervals into the current vertex’s prior-base record. -/

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

theorem step4A_writePrior_spec {code : Program DomL} {input : Input DomL}
    (basePc n m N nGlobal y : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPlWrite : Placed code basePc (step4AWritePriorInstrs h100))
    (hSz : basePc + 34 < code.size)
    (hBound : metaArrBase n m N + 64 ≤ workCap)
    (hPrior : priorBase N + 6 * y + 6 ≤ metaArrBase n m N)
    (s39 : State DomL) (hpc39 : s39.pc = basePc)
    (hMeta39 : MetaReady s39 n m N nGlobal)
    (hCurY : (s39.data[metaArrBase n m N + mIdxCurY]?).map Fin.val = some y)
    (values : Values)
    (hAcc39 : ValuesWordsAt s39.data (metaArrBase n m N + mIdxAcc0) values) :
    let metaBase := metaArrBase n m N
    let dst := priorBase N + 6 * y
    ∃ t, Steps code input 34 s39 t ∧ t.pc = basePc + 34 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      ValuesWordsAt t.data dst values ∧
      (∀ j, (j < dst ∨ dst + 6 ≤ j) → t.data[j]? = s39.data[j]?) := by
  let metaBase := metaArrBase n m N
  have hBoundMeta : metaBase + 64 ≤ workCap := hBound
  have hPriorY : priorBase N + 6 * y + 6 ≤ metaBase := hPrior
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits := by omega
  have hMulFit : 6 * y < 2 ^ bits := by omega
  -- Write 6 words from `metaBase + 30` (`mIdxAcc0`) to `priorBase N + 6 * y`:
  have hRM39 := hMeta39.rMeta_eq
  have hPlCY : Placed code (basePc) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxCurY (by dsimp only [mIdxCurY]; omega)) :=
    Placed_window hPlWrite 0 rfl
  obtain ⟨s40, hs40, hpc40, hd40, h4_40, hPres40⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlCY (by omega) hpc39 hRM39 (hOffsetFit mIdxCurY (by decide))
    hCurY
  have hPlMul : Placed code (basePc + 3) (mul6Instrs (bits := bits) reg2 reg4) :=
    Placed_window hPlWrite 3 rfl
  obtain ⟨s43, hs43, hpc43, hd43, h2Val43, hMulRegs⟩ := steps_add_mul6 (input := input)
    (by decide : reg2 ≠ reg4) hPlMul (by omega) s40 hpc40 (by rw [h4_40]; exact hMulFit)
  have hM_43 : (reg s43 rMeta).val = metaBase := by
    rw [hMulRegs rMeta (by intro h; cases h),
      hPres40 rMeta (by decide) (by decide), hRM39]
  have hPlWPB : Placed code (basePc + 6) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega)) :=
    Placed_window hPlWrite 6 rfl
  obtain ⟨s44, hs44, hpc44, hd44, h4_44, hPres44⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlWPB (by omega) hpc43
    hM_43 (hOffsetFit mIdxPriorBase (by decide)) (by rw [hd43, hd40]; exact hMeta39.meta_priorBase)
  have h2_44 : (reg s44 reg2).val = 6 * y := by rw [hPres44 reg2 (by intro h; cases h) (by intro h; cases h), h2Val43, h4_40]
  have haWAdd : code[s44.pc]? = some (.add reg2 reg4 reg2) := by rw [hpc44]; exact hPlWrite 9 _ rfl
  obtain ⟨s45, hs45Raw, hpc45, h2_45, ho45, hd45⟩ := step_add_at (input := input) haWAdd (by omega)
  have hs45 := steps_1_of_step hs45Raw
  have hDstLt : priorBase N + 6 * y + 5 < workCap := by omega
  have hDstFit : priorBase N + 6 * y + 5 < 2 ^ bits := Nat.lt_of_lt_of_le hDstLt hWorkFit
  have h2Val45 : (reg s45 reg2).val = priorBase N + 6 * y := by
    rw [h2_45, add_no_wrap _ _ (by rw [h4_44, h2_44]; unfold priorBase at hPriorY; omega), h4_44, h2_44]
    rfl
  have h30Fit : 30 < 2 ^ bits := Nat.lt_of_lt_of_le (by decide : 30 < 100) h100
  have haWI : code[s45.pc]? = some (.imm reg3 ⟨30, h30Fit⟩) := by rw [hpc45, hpc44]; exact hPlWrite 10 _ rfl
  obtain ⟨s46, hs46Raw, hpc46, h3_46, ho46, hd46⟩ := step_imm_at (input := input) haWI (by omega)
  have hs46 := steps_1_of_step hs46Raw
  have hM_46 : (reg s46 rMeta).val = metaBase := by
    rw [ho46 rMeta (by intro h; cases h), ho45 rMeta (by intro h; cases h),
      hPres44 rMeta (by intro h; cases h) (by intro h; cases h), hM_43]
  have haWAM : code[s46.pc]? = some (.add reg3 rMeta reg3) := by rw [hpc46, hpc45, hpc44]; exact hPlWrite 11 _ rfl
  obtain ⟨s47, hs47Raw, hpc47, h3_47, ho47, hd47⟩ := step_add_at (input := input) haWAM (by omega)
  have hs47 := steps_1_of_step hs47Raw
  have h3Val47 : (reg s47 reg3).val = metaBase + mIdxAcc0 := by
    rw [h3_47, add_no_wrap _ _ (by rw [hM_46, h3_46]; change metaBase + 30 < 2 ^ bits; omega), hM_46, h3_46]
  have h2Val47 : (reg s47 reg2).val = priorBase N + 6 * y := by
    rw [ho47 reg2 (by intro h; cases h), ho46 reg2 (by intro h; cases h), h2Val45]
  have h1_47 : (reg s47 reg1).val = 1 := by
    rw [ho47 reg1 (by intro h; cases h), ho46 reg1 (by intro h; cases h), ho45 reg1 (by intro h; cases h),
      hPres44 reg1 (by intro h; cases h) (by intro h; cases h), hMulRegs reg1 (by intro h; cases h),
      hPres40 reg1 (by intro h; cases h) (by intro h; cases h), hMeta39.r1_one]
  have h0_47 : (reg s47 reg0).val = 0 := by
    rw [ho47 reg0 (by intro h; cases h), ho46 reg0 (by intro h; cases h), ho45 reg0 (by intro h; cases h),
      hPres44 reg0 (by intro h; cases h) (by intro h; cases h), hMulRegs reg0 (by intro h; cases h),
      hPres40 reg0 (by intro h; cases h) (by intro h; cases h), hMeta39.r0_zero]
  have hM_47 : (reg s47 rMeta).val = metaBase := by rw [ho47 rMeta (by intro h; cases h), hM_46]
  have hd47' : s47.data = s39.data := by rw [hd47, hd46, hd45, hd44, hd43, hd40]
  have hPlWCopy : Placed code (basePc + 12) (copy6Instrs (bits := bits) reg2 reg3 reg4) :=
    Placed_window hPlWrite 12 rfl
  obtain ⟨t, ht, hpct, hValsT, hPresT, hFrT⟩ := run_copy6 (input := input) (basePc + 12) reg2 reg3 reg4
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPlWCopy (by omega) (metaBase + mIdxAcc0) (priorBase N + 6 * y) values
    (hOffsetFit 35 (by decide)) hDstFit hDstLt
    (Or.inl (by dsimp only [mIdxAcc0]; omega))
    s47 (by rw [hpc47, hpc46, hpc45, hpc44]) h1_47 h3Val47 h2Val47 (by rw [hd47']; exact hAcc39)
  have hTrace : Steps code input 34 s39 t :=
    hs40.append (hs43.append (hs44.append (hs45.append (hs46.append (hs47.append ht)))))
  refine ⟨t, hTrace, hpct, ?_, ?_, ?_, hValsT, ?_⟩
  · rw [hPresT reg0 (by decide) (by decide) (by decide), h0_47]
  · rw [hPresT reg1 (by decide) (by decide) (by decide), h1_47]
  · rw [hPresT rMeta (by decide) (by decide) (by decide), hM_47]
  · intro j hj
    rw [hFrT j hj, hd47']

end PaperB.RamProgram.ExitSummaryBuild
