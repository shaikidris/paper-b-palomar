module

public import PaperB.RamExitSummarySweepBROM
public import PaperB.RamExitSummarySweepAROM
public import PaperB.RamExitSummarySweepZero
public import PaperB.RamExitSummarySweepBPrepare

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

/-! Word-RAM correctness and cost for fresh endpoint contributions. -/

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

private theorem fresh_frame {b j : Nat}
    (h : j < b + mIdxEvalU ∨ (b + (mIdxEvalD + 1) ≤ j ∧ j < b + mIdxEval0) ∨ b + 48 ≤ j) :
    (j < b + 36 ∨ b + 42 ≤ j) ∧ j ≠ b + mIdxEvalU ∧ j ≠ b + mIdxEvalD ∧
      (j < b + mIdxEvalU ∨ (b + (mIdxEvalU + 1) ≤ j ∧ j < b + mIdxEval0) ∨ b + 48 ≤ j) := by
  dsimp only [mIdxEvalU, mIdxEvalD, mIdxEval0] at h ⊢
  omega

private theorem step4BFresh_placements {code : Program DomL} {pc zOff : Nat}
    {hz : zOff < 2 ^ bits} {h100 : 100 ≤ 2 ^ bits}
    (h : Placed code pc (step4BFreshInstrs pc zOff hz h100)) :
    Placed code pc (step4BFresh_endpointCheck pc zOff hz h100) ∧
    Placed code (pc + 13) (step4BFresh_prepare h100) ∧
    Placed code (pc + 36) (copy6Instrs reg2 reg3 reg4) ∧
    Placed code (pc + 58) (eval15Instrs (pc + 58) h100 ++ [.goto (pc + 238)]) ∧
    Placed code (pc + 220) (step4BFresh_clear h100) := by
  unfold step4BFreshInstrs at h
  have hUntilEval := Placed_append_left h
  have hUntilPrep := Placed_append_left hUntilEval
  have hEndpoint := Placed_append_left hUntilPrep
  have hLen0 : (step4BFresh_endpointCheck pc zOff hz h100).length = 13 := by
    simp [step4BFresh_endpointCheck, metaLoadInstrs]
  have hLen1 : (step4BFresh_prepare h100).length = 23 := by
    simp [step4BFresh_prepare, metaLoadInstrs, metaStoreInstrs, mul6Instrs]
  have hLen2 : (step4BFresh_evaluate pc h100).length = 184 := by
    simp [step4BFresh_evaluate, copy6Instrs_length, eval15Instrs_length]
  have hEval : Placed code (pc + 36) (step4BFresh_evaluate pc h100) := by
    simpa only [List.length_append, hLen0, hLen1, Nat.reduceAdd]
      using Placed_append_right hUntilEval
  refine ⟨hEndpoint, ?_, ?_, ?_, ?_⟩
  · simpa only [hLen0] using Placed_append_right hUntilPrep
  · exact Placed_append_left (Placed_append_left hEval)
  · have hEval' : Placed code (pc + 36)
        (copy6Instrs reg2 reg3 reg4 ++ (eval15Instrs (pc + 58) h100 ++ [.goto (pc + 238)])) := by
      simpa only [step4BFresh_evaluate, List.append_assoc] using hEval
    simpa only [copy6Instrs_length, Nat.add_assoc, Nat.reduceAdd] using Placed_append_right hEval'
  · simpa only [List.length_append, hLen0, hLen1, hLen2, Nat.reduceAdd]
      using Placed_append_right h

theorem run_step4BFresh {code : Program DomL} {input : Input DomL}
    (basePc zOff : Nat) (hzOff : zOff < 2 ^ bits) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4BFreshInstrs (bits := bits) basePc zOff hzOff h100))
    (hSz : basePc + 238 < code.size)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F ref live)
    (hFSize : F.size = r.out.tables.next)
    (B := buildActualSweepBundle H flat increasing covers rankArc r)
    (hFEq : F = B.F)
    (z : Vertex H) (pFst pSnd : Vertex H) (dp : Nat)
    (baseZ : Values)
    (st : State DomL) (hpc : st.pc = basePc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hzMem : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + zOff]?).map Fin.val = some z.val)
    (hpFstMem : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 52]?).map Fin.val = some pFst.val)
    (hpSndMem : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 53]?).map Fin.val = some pSnd.val)
    (hdpMem : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 54]?).map Fin.val = some dp)
    (hDepth : ∀ w : Fin r.out.tables.next, (st.data[w.val]?).map Fin.val = some (F.depthOf w.val))
    (hStored : ∀ w : Fin r.out.tables.next, live w.val →
      (st.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
      (st.data[storedBase r.out.tables.next + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 2) (ref w.val).parentMap ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 10) (ref w.val).jumpMap)
    (hzPrior : z.val ≠ pFst.val → z.val ≠ pSnd.val →
      ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * z.val) baseZ ∧
      live ((selectors (orderedConfig p large) r.out).label z)) :
    let vz := (selectors (orderedConfig p large) r.out).label z
    let resVal := if z.val = pFst.val ∨ z.val = pSnd.val then zero
      else Map.eval (foldFused F ref vz dp).composed baseZ
    ∃ k t, k ≤ 560 * OracleContract.L H.vertexCount ∧
      Steps code input k st t ∧ t.pc = basePc + 238 ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      ValuesWordsAt t.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEval0) resVal ∧
      (∀ j, (j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEvalU ∨
          (metaArrBase H.vertexCount H.arcCount r.out.tables.next + (mIdxEvalD + 1) ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEval0) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ j) →
        t.data[j]? = st.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let metaBase := metaArrBase n m N
  have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hBoundMeta : metaBase + 64 ≤ workCap := by
    dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
  have hInCap : 4 + n + 4 * N + 3 * m ≤ inputCap := hIn.cap_ge
  have hInFit : inputCap ≤ 2 ^ bits := hi
  have hRM := hMeta.rMeta_eq
  have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
  have hZFit : metaBase + zOff < 2 ^ bits := by
    obtain ⟨w, hwAt, _⟩ := Option.map_eq_some_iff.mp hzMem
    have hAddr := (Array.getElem?_eq_some_iff.mp hwAt).1
    rw [st.data_size] at hAddr
    exact Nat.lt_of_lt_of_le hAddr hWorkFit
  have valid : ValidJumpForest F := by rw [hFEq]; exact B.G.layout.valid
  have hPriorBound : priorBase N + 6 * z.val + 6 ≤ metaBase := by
    have := z.isLt
    unfold priorBase
    omega
  obtain ⟨hTest, hPrep, hLoad, hEval, hClear⟩ := step4BFresh_placements hPl
  have hLGe2 : 2 ≤ OracleContract.L H.vertexCount := by
    unfold OracleContract.L
    by_cases hLog : Nat.log2 (H.vertexCount + 1) < 1
    · have hSmall := (Nat.log2_lt (Nat.succ_ne_zero H.vertexCount)).mp hLog
      omega
    · omega
  -- Load `z` (`zOff`) and `pFst` (`52`):
  have hPl0 : Placed code basePc (metaLoadInstrs (bits := bits) reg2 reg7 zOff hzOff) :=
    Placed_window hTest 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) hpc hRM hZFit hzMem
  have hRM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hRM]
  have hPl1 : Placed code (basePc + 3) (metaLoadInstrs (bits := bits) reg3 reg7 52 (by omega)) :=
    Placed_window hTest 3 rfl
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc1 hRM1 (by omega) (by rw [hd1]; exact hpFstMem)
  have h2_2 : (reg s2 reg2).val = z.val := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h0_2 : (reg s2 reg0).val = 0 := by
    rw [hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero]
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one]
  have hRM2 : (reg s2 rMeta).val = metaBase := by rw [hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hRM1]
  have hd2' : s2.data = st.data := by rw [hd2, hd1]
  have haBr1 : code[s2.pc]? = some (.branchLt reg2 reg3 (basePc + 8) (basePc + 7)) := by
    rw [hpc2]; exact hTest 6 _ rfl
  obtain ⟨s3, hs3Raw, hpc3, hr3, hd3⟩ := step_branchLt_at (input := input) haBr1 (by split <;> omega)
  have hs3 := steps_1_of_step hs3Raw
  have hr3F := reg_of_regs_eq hr3
  have writeZero : ∀ (k0 : Nat) (sZ : State DomL), k0 ≤ 13 → Steps code input k0 st sZ → sZ.pc = basePc + 220 →
      (reg sZ reg0).val = 0 → (reg sZ reg1).val = 1 → (reg sZ rMeta).val = metaBase → sZ.data = st.data →
      z.val = pFst.val ∨ z.val = pSnd.val →
      ∃ k t, k ≤ 560 * OracleContract.L H.vertexCount ∧ Steps code input k st t ∧ t.pc = basePc + 238 ∧
        MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
        ValuesWordsAt t.data (metaBase + mIdxEval0)
          (if z.val = pFst.val ∨ z.val = pSnd.val then zero
           else Map.eval (foldFused F ref ((selectors (orderedConfig p large) r.out).label z) dp).composed baseZ) ∧
        (∀ j, (j < metaBase + mIdxEvalU ∨
            (metaBase + (mIdxEvalD + 1) ≤ j ∧ j < metaBase + mIdxEval0) ∨
            metaBase + 48 ≤ j) → t.data[j]? = st.data[j]?) := by
    intro k0 sZ hk0 hsZ hpcZ h0Z h1Z hMZ hdZ hMatch
    have hPlZero : Placed code (basePc + 220)
        (clearWordsInstrs (bits := bits) reg7 36 6 (by omega)) := hClear
    obtain ⟨t, ht, hpct, hValsT, htFr, htRegs⟩ :=
      clearValues_run (input := input) (tmp := reg7) (by decide) (by decide)
        (basePc + 220) 36 metaBase (by omega) hPlZero (by omega) sZ hpcZ hMZ h0Z
    have hFrAll : ∀ j, (j < metaBase + mIdxEvalU ∨
        (metaBase + (mIdxEvalD + 1) ≤ j ∧ j < metaBase + mIdxEval0) ∨ metaBase + 48 ≤ j) →
        t.data[j]? = st.data[j]? := by
      intro j hj
      rw [htFr j (fresh_frame hj).1, hdZ]
    rw [ite_eq_left hMatch]
    refine ⟨k0 + 18, t, by omega, hsZ.append ht, hpct, ?_, hValsT, hFrAll⟩
    refine hMeta.preserve (by rw [htRegs rMeta (by decide), hMZ])
      (by rw [htRegs reg0 (by decide), h0Z]) (by rw [htRegs reg1 (by decide), h1Z]) ?_
    intro i hi
    exact hFrAll (metaBase + i) (Or.inl (by dsimp only [mIdxEvalU]; omega))
  by_cases hEqF : z.val = pFst.val
  · rw [ite_eq_right (by rw [h2_2, h3_2, hEqF]; exact Nat.lt_irrefl _)] at hpc3
    have haBr2 : code[s3.pc]? = some (.branchLt reg3 reg2 (basePc + 8) (basePc + 220)) := by
      rw [hpc3]; exact hTest 7 _ rfl
    obtain ⟨s4, hs4Raw, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
    have hs4 := steps_1_of_step hs4Raw
    rw [ite_eq_right (by rw [hr3F reg2, hr3F reg3, h2_2, h3_2, hEqF]; exact Nat.lt_irrefl _)] at hpc4
    have hr4F := reg_of_regs_eq hr4
    exact writeZero 8 s4 (by omega) ((hs1.append hs2).append (hs3.append hs4)) hpc4
      (by rw [hr4F, hr3F, h0_2]) (by rw [hr4F, hr3F, h1_2]) (by rw [hr4F, hr3F, hRM2])
      (by rw [hd4, hd3, hd2']) (Or.inl hEqF)
  · have hToSnd : ∃ k1 s4, (k1 = 7 ∨ k1 = 8) ∧ Steps code input k1 st s4 ∧ s4.pc = basePc + 8 ∧
        (reg s4 reg0).val = 0 ∧ (reg s4 reg1).val = 1 ∧ (reg s4 rMeta).val = metaBase ∧
        (reg s4 reg2).val = z.val ∧ s4.data = st.data := by
      by_cases hLt1 : z.val < pFst.val
      · rw [ite_eq_left (by rw [h2_2, h3_2]; exact hLt1)] at hpc3
        exact ⟨7, s3, Or.inl rfl, (hs1.append hs2).append hs3, hpc3,
          by rw [hr3F, h0_2], by rw [hr3F, h1_2], by rw [hr3F, hRM2], by rw [hr3F, h2_2], by rw [hd3, hd2']⟩
      · have hGt1 : pFst.val < z.val := by omega
        rw [ite_eq_right (by rw [h2_2, h3_2]; exact hLt1)] at hpc3
        have haBr2 : code[s3.pc]? = some (.branchLt reg3 reg2 (basePc + 8) (basePc + 220)) := by
          rw [hpc3]; exact hTest 7 _ rfl
        obtain ⟨s4, hs4Raw, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
        have hs4 := steps_1_of_step hs4Raw
        rw [ite_eq_left (by rw [hr3F reg2, hr3F reg3, h2_2, h3_2]; exact hGt1)] at hpc4
        have hr4F := reg_of_regs_eq hr4
        exact ⟨8, s4, Or.inr rfl, (hs1.append hs2).append (hs3.append hs4), hpc4,
          by rw [hr4F, hr3F, h0_2], by rw [hr4F, hr3F, h1_2], by rw [hr4F, hr3F, hRM2],
          by rw [hr4F, hr3F, h2_2], by rw [hd4, hd3, hd2']⟩
    obtain ⟨k1, s4, hk1, hs4, hpc4, h0_4, h1_4, hM_4, h2_4, hd4⟩ := hToSnd
    have hPlS : Placed code (basePc + 8) (metaLoadInstrs (bits := bits) reg3 reg7 53 (by omega)) :=
      Placed_window hTest 8 rfl
    obtain ⟨s5, hs5, hpc5, hd5, h3_5, hPres5⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlS (by omega) hpc4 hM_4 (by omega) (by rw [hd4]; exact hpSndMem)
    have h2_5 : (reg s5 reg2).val = z.val := by rw [hPres5 reg2 (by intro h; cases h) (by intro h; cases h), h2_4]
    have h0_5 : (reg s5 reg0).val = 0 := by rw [hPres5 reg0 (by intro h; cases h) (by intro h; cases h), h0_4]
    have h1_5 : (reg s5 reg1).val = 1 := by rw [hPres5 reg1 (by intro h; cases h) (by intro h; cases h), h1_4]
    have hM_5 : (reg s5 rMeta).val = metaBase := by rw [hPres5 rMeta (by intro h; cases h) (by intro h; cases h), hM_4]
    have haBr3 : code[s5.pc]? = some (.branchLt reg2 reg3 (basePc + 13) (basePc + 12)) := by
      rw [hpc5]; exact hTest 11 _ rfl
    obtain ⟨s6, hs6Raw, hpc6, hr6, hd6⟩ := step_branchLt_at (input := input) haBr3 (by split <;> omega)
    have hs6 := steps_1_of_step hs6Raw
    have hr6F := reg_of_regs_eq hr6
    by_cases hEqS : z.val = pSnd.val
    · rw [ite_eq_right (by rw [h2_5, h3_5, hEqS]; exact Nat.lt_irrefl _)] at hpc6
      have haBr4 : code[s6.pc]? = some (.branchLt reg3 reg2 (basePc + 13) (basePc + 220)) := by
        rw [hpc6]; exact hTest 12 _ rfl
      obtain ⟨s7, hs7Raw, hpc7, hr7, hd7⟩ := step_branchLt_at (input := input) haBr4 (by split <;> omega)
      have hs7 := steps_1_of_step hs7Raw
      rw [ite_eq_right (by rw [hr6F reg2, hr6F reg3, h2_5, h3_5, hEqS]; exact Nat.lt_irrefl _)] at hpc7
      have hr7F := reg_of_regs_eq hr7
      exact writeZero (k1 + 5) s7 (by rcases hk1 with rfl | rfl <;> omega)
        (hs4.append (hs5.append (hs6.append hs7))) hpc7
        (by rw [hr7F, hr6F, h0_5]) (by rw [hr7F, hr6F, h1_5]) (by rw [hr7F, hr6F, hM_5])
        (by rw [hd7, hd6, hd5, hd4]) (Or.inr hEqS)
    · -- Lift case (`z ≠ pFst ∧ z ≠ pSnd`):
      have hToLift : ∃ k2 s7, (k2 = 1 ∨ k2 = 2) ∧ Steps code input k2 s5 s7 ∧ s7.pc = basePc + 13 ∧
          (reg s7 reg0).val = 0 ∧ (reg s7 reg1).val = 1 ∧ (reg s7 rMeta).val = metaBase ∧
          (reg s7 reg2).val = z.val ∧ s7.data = st.data := by
        by_cases hLt2 : z.val < pSnd.val
        · rw [ite_eq_left (by rw [h2_5, h3_5]; exact hLt2)] at hpc6
          exact ⟨1, s6, Or.inl rfl, hs6, hpc6,
            by rw [hr6F, h0_5], by rw [hr6F, h1_5], by rw [hr6F, hM_5], by rw [hr6F, h2_5], by rw [hd6, hd5, hd4]⟩
        · have hGt2 : pSnd.val < z.val := by omega
          rw [ite_eq_right (by rw [h2_5, h3_5]; exact hLt2)] at hpc6
          have haBr4 : code[s6.pc]? = some (.branchLt reg3 reg2 (basePc + 13) (basePc + 220)) := by
            rw [hpc6]; exact hTest 12 _ rfl
          obtain ⟨s7, hs7Raw, hpc7, hr7, hd7⟩ := step_branchLt_at (input := input) haBr4 (by split <;> omega)
          have hs7 := steps_1_of_step hs7Raw
          rw [ite_eq_left (by rw [hr6F reg2, hr6F reg3, h2_5, h3_5]; exact hGt2)] at hpc7
          have hr7F := reg_of_regs_eq hr7
          exact ⟨2, s7, Or.inr rfl, hs6.append hs7, hpc7,
            by rw [hr7F, hr6F, h0_5], by rw [hr7F, hr6F, h1_5], by rw [hr7F, hr6F, hM_5],
            by rw [hr7F, hr6F, h2_5], by rw [hd7, hd6, hd5, hd4]⟩
      obtain ⟨k2, s7, hk2, hs7, hpc7, h0_7, h1_7, hM_7, h2_7, hd7⟩ := hToLift
      obtain ⟨hBaseZ, hLiveV⟩ := hzPrior hEqF hEqS
      let v := (selectors (orderedConfig p large) r.out).label z
      have hvLt : v < r.out.tables.next := by
        rw [← B.G.size_eq]
        exact B.E.label_lt z True.intro
      have hCapZ : 4 + z.val < inputCap := by have := z.isLt; omega
      obtain ⟨s21, hs21, hpc21, h0_21, h1_21, hM_21, hEU21, hED21, hVals21, hFr21⟩ :=
        step4BFresh_prepare_spec (input := input) basePc N metaBase z.val v dp h100
          hCapZ hPriorBound hBoundMeta hPrep hLoad hSz s7 hpc7 h0_7 h1_7 hM_7 h2_7
          (by rw [hd7]; exact hMeta.meta_labelsIn) (hIn.labels_at z)
          (by rw [hd7]; exact hdpMem) (by rw [hd7]; exact hMeta.meta_priorBase)
          baseZ (by rw [hd7]; exact hBaseZ)
      have hData21 : ∀ j, j ≠ metaBase + mIdxEvalU → j ≠ metaBase + mIdxEvalD →
          (j < metaBase + mIdxEval0 ∨ metaBase + mIdxEval0 + 6 ≤ j) →
          s21.data[j]? = st.data[j]? := by
        intro j hU hD hX
        rw [hFr21 j hU hD hX, hd7]
      have hDataLow : ∀ j, j < metaBase → s21.data[j]? = st.data[j]? := by
        intro j hj
        exact hData21 j (by dsimp only [mIdxEvalU]; omega) (by dsimp only [mIdxEvalD]; omega)
          (Or.inl (by dsimp only [mIdxEval0]; omega))
      have hPlEv : Placed code (basePc + 58) (eval15Instrs (bits := bits) (basePc + 58) h100) :=
        Placed_append_left hEval
      obtain ⟨kEv, s22, hkEv, hs22, hpc22, h0_22, h1_22, hM_22, hVals22, hFr22⟩ :=
        run_eval15 (input := input) (basePc + 58) h100 hPlEv (by omega) valid ok hNLe
          (by omega) hWorkFit hFSize (F.depthOf v - dp) v hLiveV hvLt baseZ s21 rfl hpc21
          h0_21 h1_21 hM_21
          (by rw [hData21 (metaBase + mIdxStoredBase)
                (by dsimp only [mIdxStoredBase, mIdxEvalU]; omega)
                (by dsimp only [mIdxStoredBase, mIdxEvalD]; omega)
                (Or.inl (by dsimp only [mIdxStoredBase, mIdxEval0]; omega))]
              exact hMeta.meta_storedBase)
          hEU21 hED21 hVals21
          (fun w => by rw [hDataLow w.val (by have := w.isLt; omega)]; exact hDepth w)
          (fun w hwL => by
            have hSeg : ∀ i < 18, s21.data[storedBase N + 18 * w.val + i]? =
                st.data[storedBase N + 18 * w.val + i]? := fun i hi =>
              hDataLow _ (by have := w.isLt; unfold storedBase; omega)
            have ho := hStored w hwL
            have hp := hSeg 0 (by decide)
            rw [Nat.add_zero] at hp
            refine ⟨by rw [hp]; exact ho.1, by rw [hSeg 1 (by decide)]; exact ho.2.1,
              mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (2 + i) (by omega)) ho.2.2.1,
              mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (10 + i) (by omega)) ho.2.2.2⟩)
      have hEndGoto : Placed code (basePc + 219) [.goto (basePc + 238)] := by
        simpa only [eval15Instrs_length, Nat.add_assoc, Nat.reduceAdd] using Placed_append_right hEval
      have haGoEnd : code[s22.pc]? = some (.goto (basePc + 238)) := by
        rw [hpc22]
        exact hEndGoto 0 _ rfl
      obtain ⟨t, htRaw, hpct, hrt, hdt⟩ := step_goto_at (input := input) haGoEnd (by omega)
      have ht := steps_1_of_step htRaw
      have hrTF := reg_of_regs_eq hrt
      have hFrAll : ∀ j, (j < metaBase + mIdxEvalU ∨
          (metaBase + (mIdxEvalD + 1) ≤ j ∧ j < metaBase + mIdxEval0) ∨
          metaBase + 48 ≤ j) → t.data[j]? = st.data[j]? := by
        intro j hj
        obtain ⟨hX, hU, hD, hK⟩ := fresh_frame hj
        rw [hdt, hFr22 j hK, hData21 j hU hD hX]
      have hStepsCost : (foldFused F ref v dp).steps ≤ 3 * OracleContract.L H.vertexCount := by
        have hInserted : F.numInserted ≤ H.vertexCount := by rw [hFEq]; exact bundle_numInserted_le B
        have hvSize : v < F.size := hFSize.symm ▸ hvLt
        have hCost := foldTrace_cost ref valid hvSize hInserted dp
        rw [live_foldFused_eq_foldTrace ok hLiveV, hCost.1]
        exact Nat.le_trans hCost.2.1 (Nat.mul_le_mul_left 3 (ceilLog2_add_two_le_L H.vertexCount))
      have hTot := hs4.append (hs5.append (hs7.append (hs21.append (hs22.append ht))))
      have hOrFalse : ¬ (z.val = pFst.val ∨ z.val = pSnd.val) := fun h => h.elim hEqF hEqS
      dsimp only
      rw [ite_eq_right hOrFalse]
      have hMulEv : 165 * (foldFused F ref v dp).steps ≤ 495 * OracleContract.L H.vertexCount := by
        have hM := Nat.mul_le_mul_left 165 hStepsCost
        omega
      exact ⟨_, t,
        by rcases hk1 with rfl | rfl <;> rcases hk2 with rfl | rfl <;> omega,
        hTot, hpct,
        hMeta.preserve (by rw [hrTF, hM_22]) (by rw [hrTF, h0_22]) (by rw [hrTF, h1_22])
          (fun i hi => hFrAll (metaBase + i) (Or.inl (by dsimp only [mIdxEvalU]; omega))),
        by rw [hdt]; exact hVals22, hFrAll⟩

end PaperB.RamProgram.ExitSummaryBuild
