module

public import PaperB.RamExitSummaryCsrCountLoop

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
The exit-summary CSR count phase and its execution proof.
-/

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

section Stage2CsrKahn

section CsrCountPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_csrCount {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hInZ : ∀ i ≤ H.vertexCount,
      (s0.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some 0)
    (hTempZ : ∀ i < 2 * H.vertexCount + 1,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + i]?).map Fin.val = some 0) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 19 * H.arcCount + 25 ∧
      run (csrCountPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ u < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
          some (degOut H u)) ∧
      (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
        some 0 ∧
      (∀ v < H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
          some (degIn H v)) ∧
      (t.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
        some 0 ∧
      (∀ v < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (degIn H v)) ∧
      (∀ j, j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≤ j →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB1 : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) =
      inArcIdArrBase H.vertexCount r.out.tables.next := rfl
  have hB2 : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
  have hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ 2 ^ bits := by omega
  let ph := csrCountPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (csrCountInstrs (bits := bits) h100).length = 40 := by
    simp [csrCountInstrs, csrCountSetupInstrs, csrCountLoopInstrs, metaLoadInstrs]
  have hCodeSize : ph.code.size = 41 := by
    dsimp [ph, csrCountPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (csrCountInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold csrCountInstrs at hPlFull; exact hPlFull)
  have hPlLoop := Placed_append_right (by unfold csrCountInstrs at hPlFull; exact hPlFull)
  rw [show (csrCountSetupInstrs (bits := bits) h100).length = 21 by
    simp [csrCountSetupInstrs, metaLoadInstrs]] at hPlLoop
  have hPlM := Placed_append_left (by unfold csrCountSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold csrCountSetupInstrs at hPlSetup; exact hPlSetup)
  rw [hLml] at hPlS1
  have hPlBr := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1
  rw [show ([Instr.branchLt reg0 reg2 4 40] : List (Instr bits 15)).length = 1 by rfl] at hPlS2
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlM (by omega)
    rfl hMeta.rMeta_eq (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) hMeta.meta_m
  have h0_1 : (reg s1 reg0).val = 0 := by rw [ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_1 : (reg s1 reg1).val = 1 := by rw [ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  have hBr : ph.code[s1.pc]? = some (.branchLt reg0 reg2 4 40) := by rw [hpc1]; exact hPlBr 0 _ rfl
  by_cases hmZero : H.arcCount = 0
  · have hFalse : ¬ ((reg s1 reg0).val < (reg s1 reg2).val) := by rw [h0_1, h2_1, hmZero]; exact Nat.lt_irrefl _
    obtain ⟨s2, hs2, hpc2, hreg2, hd2⟩ := step_branchLt_at (input := input) hBr (by rw [ite_eq_right hFalse]; omega)
    rw [ite_eq_right hFalse] at hpc2
    have hr2 : ∀ r : Fin 15, reg s2 r = reg s1 r := reg_of_regs_eq hreg2
    have hAllSteps : Steps ph.code input 4 (Phase.initial s0) s2 := hs1.append (steps_1_of_step hs2)
    have hHalt : step ph.code input s2 = some (.halted s2) :=
      haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrCountInstrs (bits := bits) h100) _
        (by rw [hpc2, hCodeLen]) (input := input)
    have hDegOut0 : ∀ u, degOut H u = 0 := fun u => by simp [degOut, hmZero, outCountPrefix]
    have hDegIn0 : ∀ v, degIn H v = 0 := fun v => by simp [degIn, hmZero, inCountPrefix]
    refine ⟨4 + 1, s2, by omega, hAllSteps.halts hHalt, ?_,
      fun u hu => by rw [hd2, hd1, data_initial, hDegOut0 u, Nat.add_assoc]; exact hTempZ (H.vertexCount + u) (by omega),
      by rw [hd2, hd1, data_initial]; exact hTempZ (2 * H.vertexCount) (by omega),
      fun v hv => by rw [hd2, hd1, data_initial, hDegIn0 v]; exact hInZ v (by omega),
      by rw [hd2, hd1, data_initial]; exact hInZ H.vertexCount (by omega),
      fun v hv => by rw [hd2, hd1, data_initial, hDegIn0 v]; exact hTempZ v (by omega),
      fun j _ => by rw [hd2, hd1, data_initial]⟩
    · apply hMeta.preserve
      · rw [hr2, hMeta1]
      · rw [hr2, h0_1]
      · rw [hr2, h1_1]
      · intro i _; rw [hd2, hd1, data_initial]
  · have hmPos : 0 < H.arcCount := Nat.pos_of_ne_zero hmZero
    have hTrue : (reg s1 reg0).val < (reg s1 reg2).val := by rw [h0_1, h2_1]; exact hmPos
    obtain ⟨s2, hs2, hpc2, hreg2, hd2⟩ := step_branchLt_at (input := input) hBr (by rw [ite_eq_left hTrue]; omega)
    rw [ite_eq_left hTrue] at hpc2
    have hr2 : ∀ r : Fin 15, reg s2 r = reg s1 r := reg_of_regs_eq hreg2
    have hPlTemp := Placed_append_left hPlS2
    have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
    have hPlN := Placed_append_left hPlS3
    have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
    have hPlAdd := Placed_append_left hPlS4
    have hPlS5 := Placed_append_right hPlS4
    rw [show ([Instr.add reg4 reg3 reg4] : List (Instr bits 15)).length = 1 by rfl] at hPlS5
    have hPlInS := Placed_append_left hPlS5
    have hPlS6 := Placed_append_right hPlS5; rw [hLml] at hPlS6
    have hPlQSrc := Placed_append_left hPlS6
    have hPlS7 := Placed_append_right hPlS6; rw [hLml] at hPlS7
    have hPlQHead := Placed_append_left hPlS7
    have hPlMov := Placed_append_right hPlS7; rw [hLml] at hPlMov
    have hMeta2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by rw [hr2, hMeta1]
    have hd2' : s2.data = s0.data := by rw [hd2, hd1, data_initial]
    obtain ⟨s3, hs3, hpc3, hd3, h3_3, ho3⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlTemp (by omega)
      (by omega) hMeta2 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd2']; exact hMeta.meta_tempBase)
    have hMeta3 : (reg s3 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho3 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta2
    obtain ⟨s4, hs4, hpc4, hd4, h4_4, ho4⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlN (by omega)
      hpc3 hMeta3 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd3, hd2']; exact hMeta.meta_n)
    have h3_4 : (reg s4 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho4 reg3 (by intro h; cases h) (by intro h; cases h), h3_3]
    have hAdd : ph.code[s4.pc]? = some (.add reg4 reg3 reg4) := by rw [hpc4]; exact hPlAdd 0 _ rfl
    obtain ⟨s5, hs5, hpc5, h4_5, ho5, hd5⟩ := step_add_at (input := input) hAdd (by omega)
    have hOutS5 : (reg s5 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      rw [h4_5, add_no_wrap _ _ (by rw [h3_4, h4_4]; exact Nat.lt_of_lt_of_le (by omega) hw), h3_4, h4_4]
    have hMeta5 : (reg s5 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho5 rMeta (by intro h; cases h), ho4 rMeta (by intro h; cases h) (by intro h; cases h), hMeta3]
    have hd5' : s5.data = s0.data := by rw [hd5, hd4, hd3, hd2']
    obtain ⟨s6, hs6, hpc6, hd6, h5_6, ho6⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlInS (by omega)
      (by omega) hMeta5 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd5']; exact hMeta.meta_inStartBase)
    have hMeta6 : (reg s6 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho6 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta5
    obtain ⟨s7, hs7, hpc7, hd7, h6_7, ho7⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlQSrc (by omega)
      hpc6 hMeta6 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd6, hd5']; exact hMeta.meta_qSrcIn hmPos)
    have hMeta7 : (reg s7 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho7 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta6
    obtain ⟨s8, hs8, hpc8, hd8, h7_8, ho8⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlQHead (by omega)
      hpc7 hMeta7 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd7, hd6, hd5']; exact hMeta.meta_qHeadIn hmPos)
    have hMov : ph.code[s8.pc]? = some (.mov reg8 reg0) := by rw [hpc8]; exact hPlMov 0 _ rfl
    obtain ⟨s9, hs9, hpc9, h8_9, ho9, hd9⟩ := step_mov_at (input := input) hMov (by omega)
    have hd9' : s9.data = s0.data := by rw [hd9, hd8, hd7, hd6, hd5']
    have h0_9 : (reg s9 reg0).val = 0 := by
      rw [ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h) (by intro h; cases h),
        ho7 reg0 (by intro h; cases h) (by intro h; cases h), ho6 reg0 (by intro h; cases h) (by intro h; cases h),
        ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h) (by intro h; cases h),
        ho3 reg0 (by intro h; cases h) (by intro h; cases h), hr2, h0_1]
    have h1_9 : (reg s9 reg1).val = 1 := by
      rw [ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h) (by intro h; cases h),
        ho7 reg1 (by intro h; cases h) (by intro h; cases h), ho6 reg1 (by intro h; cases h) (by intro h; cases h),
        ho5 reg1 (by intro h; cases h), ho4 reg1 (by intro h; cases h) (by intro h; cases h),
        ho3 reg1 (by intro h; cases h) (by intro h; cases h), hr2, h1_1]
    have hMeta9 : (reg s9 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h) (by intro h; cases h), hMeta7]
    have h2_9 : (reg s9 reg2).val = H.arcCount := by
      rw [ho9 reg2 (by intro h; cases h), ho8 reg2 (by intro h; cases h) (by intro h; cases h),
        ho7 reg2 (by intro h; cases h) (by intro h; cases h), ho6 reg2 (by intro h; cases h) (by intro h; cases h),
        ho5 reg2 (by intro h; cases h), ho4 reg2 (by intro h; cases h) (by intro h; cases h),
        ho3 reg2 (by intro h; cases h) (by intro h; cases h), hr2, h2_1]
    have h3_9 : (reg s9 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho9 reg3 (by intro h; cases h), ho8 reg3 (by intro h; cases h) (by intro h; cases h),
        ho7 reg3 (by intro h; cases h) (by intro h; cases h), ho6 reg3 (by intro h; cases h) (by intro h; cases h),
        ho5 reg3 (by intro h; cases h), h3_4]
    have h4_9 : (reg s9 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      rw [ho9 reg4 (by intro h; cases h), ho8 reg4 (by intro h; cases h) (by intro h; cases h),
        ho7 reg4 (by intro h; cases h) (by intro h; cases h), ho6 reg4 (by intro h; cases h) (by intro h; cases h),
        hOutS5]
    have h5_9 : (reg s9 reg5).val = inStartArrBase H.vertexCount r.out.tables.next := by
      rw [ho9 reg5 (by intro h; cases h), ho8 reg5 (by intro h; cases h) (by intro h; cases h),
        ho7 reg5 (by intro h; cases h) (by intro h; cases h), h5_6]
    have h6_9 : (reg s9 reg6).val = 4 + H.vertexCount + 4 * r.out.tables.next := by
      rw [ho9 reg6 (by intro h; cases h), ho8 reg6 (by intro h; cases h) (by intro h; cases h), h6_7]
    have h7_9 : (reg s9 reg7).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount := by
      rw [ho9 reg7 (by intro h; cases h), h7_8]
    have h8_9' : (reg s9 reg8).val = 0 := by rw [h8_9, ← ho9 reg0 (by intro h; cases h), h0_9]
    obtain ⟨kLoop, t, hkLoop, hStepsLoop, hpcT, h0T, h1T, hMetaT, hOutT, hInT, hIndT, hFrT⟩ :=
      csrCountLoop_spec hIn hWork hPlLoop (by omega) 0 (Nat.zero_le _) s9 (by omega)
        h0_9 h1_9 hMeta9 h2_9 h3_9 h4_9 h5_9 h6_9 h7_9 h8_9'
        (fun u hu => by
          change (s9.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val = some 0
          rw [hd9', Nat.add_assoc]; exact hTempZ (H.vertexCount + u) (by omega))
        (fun v hv => by
          change (s9.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val = some 0
          rw [hd9']; exact hInZ v (by omega))
        (fun v hv => by
          change (s9.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val = some 0
          rw [hd9']; exact hTempZ v (by omega))
    have hSetupSteps : Steps ph.code input 21 (Phase.initial s0) s9 :=
      hs1.append ((steps_1_of_step hs2).append (hs3.append (hs4.append
        ((steps_1_of_step hs5).append (hs6.append (hs7.append (hs8.append (steps_1_of_step hs9))))))))
    have hHalt : step ph.code input t = some (.halted t) :=
      haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrCountInstrs (bits := bits) h100) _
        (by rw [hpcT, hCodeLen]) (input := input)
    have hMetaFrame : ∀ i < 22,
        inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + i ∧
        metaArrBase H.vertexCount H.arcCount r.out.tables.next + i <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := fun i hi22 => by omega
    have hInNFrame :
        inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
          inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ∧
        inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
    have hTemp2NGe :
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≤
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount := Nat.le_refl _
    have h2NLe : 2 * H.vertexCount < 2 * H.vertexCount + 1 := Nat.lt_succ_self _
    have hNLeN : H.vertexCount ≤ H.vertexCount := Nat.le_refl _
    have hkRes : 21 + kLoop + 1 ≤ 19 * H.arcCount + 25 := by
      simp only [Nat.sub_zero] at hkLoop; omega
    refine ⟨21 + kLoop + 1, t, hkRes, (hSetupSteps.append hStepsLoop).halts hHalt, ?_,
      hOutT,
      by
        rw [hFrT (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount)
          (Or.inr (Or.inr hTemp2NGe)), hd9']
        exact hTempZ (2 * H.vertexCount) h2NLe,
      hInT,
      by
        rw [hFrT (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount)
          (Or.inr (Or.inl hInNFrame)), hd9']
        exact hInZ H.vertexCount hNLeN,
      hIndT,
      fun j hj => by rw [hFrT j hj, hd9']⟩
    · apply hMeta.preserve hMetaT h0T h1T
      intro i hi22
      rw [hFrT (metaArrBase H.vertexCount H.arcCount r.out.tables.next + i)
        (Or.inr (Or.inl (hMetaFrame i hi22))), hd9']

end CsrCountPhase


end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
