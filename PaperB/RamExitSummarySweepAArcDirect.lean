module

public import PaperB.RamExitSummarySweepADecode
public import PaperB.RamExitSummarySweepADirect

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! The prior-base arc fold when the source matches either endpoint of the cut pair. -/

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

private theorem arcFrameDirect {b j a : Nat} (hA : a = 30 ∨ a = 33)
    (h : j < b + 25 ∨ (b + 26 ≤ j ∧ j < b + 28) ∨
      (b + 48 ≤ j ∧ j < b + 53) ∨ b + 55 ≤ j) :
    j ≠ b + 25 ∧ (j < b + a ∨ b + a + 3 ≤ j) ∧
      (j < b + 42 ∨ b + 45 ≤ j) ∧ j ≠ b + 53 ∧ j ≠ b + 54 := by
  rcases hA with rfl | rfl <;> omega

theorem step4A_arc_direct_spec {code : Program DomL} {input : Input DomL}
    (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code loopPc (step4ALoopInstrs (bits := bits) loopPc h100))
    (hSz : loopPc + 406 < code.size)
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
    {F : JumpForest} {ref : Store} (ownerSlot : Nat)
    (Bcut : CutPair H) (baseFn : Vertex H → Values)
    (arcPtr arcEnd e : Nat) (heLt : e < H.arcCount)
    (hPtrLt : arcPtr < arcEnd) (hEndLe : arcEnd ≤ H.arcCount)
    (st : State DomL) (hpc : st.pc = loopPc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hPtr : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr]?).map Fin.val = some arcPtr)
    (hEnd : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcEnd]?).map Fin.val = some arcEnd)
    (hArcId : (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + arcPtr]?).map Fin.val = some e)
    (hBFst : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48]?).map Fin.val = some Bcut.fst.val)
    (hBSnd : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 49]?).map Fin.val = some Bcut.snd.val)
    (acc : Values)
    (hAcc : ValuesWordsAt st.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0) acc)
    (hEndpoint : let u := (rawOccurrence H ⟨e, heLt⟩).1
      u.val = Bcut.fst.val ∨ u.val = Bcut.snd.val) :
    ∃ k t, k ≤ 700 * OracleContract.L H.vertexCount ∧
      Steps code input k st t ∧ t.pc = loopPc ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr]?).map Fin.val =
        some (arcPtr + 1) ∧
      ValuesWordsAt t.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0)
        (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) ∧
      (∀ j, (j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr ∨
          (metaArrBase H.vertexCount H.arcCount r.out.tables.next + (mIdxArcPtr + 1) ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEvalU) ∨
          (metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + 53) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 55 ≤ j) →
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
  let occ := rawOccurrence H ⟨e, heLt⟩
  let u := occ.1
  let rTail := entryRank occ.2.origTail
  obtain ⟨s15, hSteps15, hpc15, h0_15, h1_15, hRM15, h5_15, h6_15, h7_15, hData15⟩ :=
    step4A_decode_spec (input := input) loopPc h100 hPl hSz flat increasing covers rankArc
      hIn hWork Bcut arcPtr arcEnd e heLt hPtrLt hEndLe st hpc hMeta hPtr hEnd hArcId hBFst
  have hDecode := step4A_decode_placed hPl
  have hSecond := step4A_secondEndpoint_placed hPl
  -- Compare `u` (`reg5`) with `Bcut.fst` (`reg7`):
  have haBrFst1 : code[s15.pc]? = some (.branchLt reg5 reg7 (loopPc + 73) (loopPc + 32)) := by
    rw [hpc15]; exact hDecode 31 _ rfl
  obtain ⟨s16, hs16Raw, hpc16, hr16, hd16⟩ := step_branchLt_at (input := input) haBrFst1 (by split <;> omega)
  have hs16 := steps_1_of_step hs16Raw
  have hr16F := reg_of_regs_eq hr16
  by_cases hEqFst : u.val = Bcut.fst.val
  · rw [ite_eq_right (by rw [h5_15, h7_15, hEqFst]; exact Nat.lt_irrefl _)] at hpc16
    have haBrFst2 : code[s16.pc]? = some (.branchLt reg7 reg5 (loopPc + 73) (loopPc + 33)) := by
      rw [hpc16]; exact hDecode 32 _ rfl
    obtain ⟨s17, hs17Raw, hpc17, hr17, hd17⟩ := step_branchLt_at (input := input) haBrFst2 (by split <;> omega)
    have hs17 := steps_1_of_step hs17Raw
    rw [ite_eq_right (by rw [hr16F reg5, hr16F reg7, h5_15, h7_15, hEqFst]; exact Nat.lt_irrefl _)] at hpc17
    have hr17F := reg_of_regs_eq hr17
    have hRM17 : (reg s17 rMeta).val = metaBase := by rw [hr17F, hr16F, hRM15]
    have h1_17 : (reg s17 reg1).val = 1 := by rw [hr17F, hr16F, h1_15]
    have h0_17 : (reg s17 reg0).val = 0 := by rw [hr17F, hr16F, h0_15]
    have h6_17 : (reg s17 reg6).val = rTail := by rw [hr17F, hr16F, h6_15]
    have hData17 : ∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → s17.data[j]? = st.data[j]? := fun j h1 h2 => by
      rw [hd17, hd16, hData15 j h1 h2]
    have hLocal : IntervalWordsAt s17.data (metaBase + 30) acc.x0 :=
      intervalWordsAt_frame (fun i hi => hData17 _ (by omega) (by omega)) hAcc.1
    obtain ⟨kD, sD, hkD, hsD, hpcD, h0D, h1D, hMD, hJoinD, hFrameD⟩ :=
      step4A_direct_spec (input := input) (loopPc + 33) (loopPc + 398) 30 metaBase rTail h100
        (by decide) hBoundMeta (step4A_firstEndpoint_placed hPl) (by omega) (by omega)
        s17 hpc17 h0_17 h1_17 hRM17 h6_17 acc.x0 hLocal
    have hPtrD : (sD.data[metaBase + mIdxArcPtr]?).map Fin.val = some arcPtr := by
      change (sD.data[metaBase + 25]?).map Fin.val = some arcPtr
      rw [hFrameD _ (Or.inl (by omega)) (Or.inl (by omega)), hData17 _ (by omega) (by omega)]
      exact hPtr
    obtain ⟨t, ht, hpct, h0T, h1T, hMT, hPtrT, hFrT⟩ := step4A_nextArc_spec (input := input)
      loopPc n m N arcPtr h100 hPl hSz hNLe large hWork hWorkFit
      (Nat.lt_of_lt_of_le hPtrLt hEndLe) sD hpcD h0D h1D hMD hPtrD
    have hFrAll : ∀ j, (j < metaBase + 25 ∨
        (metaBase + 26 ≤ j ∧ j < metaBase + 28) ∨
        (metaBase + 48 ≤ j ∧ j < metaBase + 53) ∨ metaBase + 55 ≤ j) →
        t.data[j]? = st.data[j]? := by
      intro j hj
      obtain ⟨hNe, hAccFr, hTmpFr, h53, h54⟩ := arcFrameDirect (a := 30) (by decide) hj
      rw [hFrT j hNe, hFrameD j hAccFr hTmpFr, hData17 j h53 h54]
    have hRamEq : ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e =
        ⟨Interval.join acc.x0 (.span rTail rTail), acc.x1⟩ := by
      unfold ramArcStep
      rw [dite_eq_left heLt]
      dsimp only
      rw [ite_eq_left hEqFst]
    have hNew : IntervalWordsAt t.data (metaBase + 30) (Interval.join acc.x0 (.span rTail rTail)) :=
      intervalWordsAt_frame (fun i hi => hFrT _ (by dsimp only [mIdxArcPtr]; omega)) hJoinD
    have hOther : IntervalWordsAt t.data (metaBase + 33) acc.x1 := by
      apply intervalWordsAt_frame ?_ hAcc.2
      intro i hi
      rw [hFrT (metaBase + 33 + i) (by dsimp only [mIdxArcPtr]; omega),
        hFrameD _ (by omega) (Or.inl (by omega)), hData17 _ (by omega) (by omega)]
    have hAccT : ValuesWordsAt t.data (metaBase + mIdxAcc0)
        (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) := by
      rw [hRamEq]
      exact ⟨hNew, hOther⟩
    have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
    have hPre : Steps code input 33 st s17 := hSteps15.append (hs16.append hs17)
    have hTot := hPre.append (hsD.append ht)
    refine ⟨_, t, ?_, hTot, hpct, hMeta.preserve hMT h0T h1T ?_, hPtrT, hAccT, hFrAll⟩
    · omega
    · intro i hi
      exact hFrAll (metaBase + i) (Or.inl (by omega))
  · -- `u.val ≠ Bcut.fst.val`: jump to `loopPc + 73`:
    have hToChkSnd : ∃ k1 sC, (k1 = 1 ∨ k1 = 2) ∧ Steps code input k1 s15 sC ∧ sC.pc = loopPc + 73 ∧
        (reg sC reg0).val = 0 ∧ (reg sC reg1).val = 1 ∧ (reg sC rMeta).val = metaBase ∧
        (reg sC reg5).val = u.val ∧ (reg sC reg6).val = rTail ∧
        (∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → sC.data[j]? = st.data[j]?) := by
      by_cases hLt1 : u.val < Bcut.fst.val
      · rw [ite_eq_left (by rw [h5_15, h7_15]; exact hLt1)] at hpc16
        exact ⟨1, s16, Or.inl rfl, hs16, hpc16,
          by rw [hr16F, h0_15], by rw [hr16F, h1_15], by rw [hr16F, hRM15],
          by rw [hr16F, h5_15], by rw [hr16F, h6_15],
          fun j h1 h2 => by rw [hd16, hData15 j h1 h2]⟩
      · have hGt1 : Bcut.fst.val < u.val := by omega
        rw [ite_eq_right (by rw [h5_15, h7_15]; exact hLt1)] at hpc16
        have haBr2 : code[s16.pc]? = some (.branchLt reg7 reg5 (loopPc + 73) (loopPc + 33)) := by
          rw [hpc16]; exact hDecode 32 _ rfl
        obtain ⟨s17, hs17Raw, hpc17, hr17, hd17⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
        have hs17 := steps_1_of_step hs17Raw
        rw [ite_eq_left (by rw [hr16F reg5, hr16F reg7, h5_15, h7_15]; exact hGt1)] at hpc17
        have hr17F := reg_of_regs_eq hr17
        exact ⟨2, s17, Or.inr rfl, hs16.append hs17, hpc17,
          by rw [hr17F, hr16F, h0_15], by rw [hr17F, hr16F, h1_15], by rw [hr17F, hr16F, hRM15],
          by rw [hr17F, hr16F, h5_15], by rw [hr17F, hr16F, h6_15],
          fun j h1 h2 => by rw [hd17, hd16, hData15 j h1 h2]⟩
    obtain ⟨k1, sC, hk1, hsC, hpcC, h0C, h1C, hMC, h5C, h6C, hDataC⟩ := hToChkSnd
    -- Load `Bcut.snd` (`49`):
    have hPlSnd : Placed code (loopPc + 73) (metaLoadInstrs (bits := bits) reg7 reg8 49 (by omega)) :=
      Placed_window hSecond 0 rfl
    obtain ⟨s18, hs18, hpc18, hd18, h7_18, hPres18⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlSnd (by omega) hpcC hMC (by omega)
      (by rw [hDataC _ (by omega) (by omega)]; exact hBSnd)
    have h0_18 : (reg s18 reg0).val = 0 := by rw [hPres18 reg0 (by intro h; cases h) (by intro h; cases h), h0C]
    have h1_18 : (reg s18 reg1).val = 1 := by rw [hPres18 reg1 (by intro h; cases h) (by intro h; cases h), h1C]
    have hM_18 : (reg s18 rMeta).val = metaBase := by rw [hPres18 rMeta (by intro h; cases h) (by intro h; cases h), hMC]
    have h5_18 : (reg s18 reg5).val = u.val := by rw [hPres18 reg5 (by intro h; cases h) (by intro h; cases h), h5C]
    have h6_18 : (reg s18 reg6).val = rTail := by rw [hPres18 reg6 (by intro h; cases h) (by intro h; cases h), h6C]
    have hData18 : ∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → s18.data[j]? = st.data[j]? := fun j h1 h2 => by
      rw [hd18, hDataC j h1 h2]
    have haBrSnd1 : code[s18.pc]? = some (.branchLt reg5 reg7 (loopPc + 118) (loopPc + 77)) := by
      rw [hpc18]; exact hSecond 3 _ rfl
    obtain ⟨s19, hs19Raw, hpc19, hr19, hd19⟩ := step_branchLt_at (input := input) haBrSnd1 (by split <;> omega)
    have hs19 := steps_1_of_step hs19Raw
    have hr19F := reg_of_regs_eq hr19
    by_cases hEqSnd : u.val = Bcut.snd.val
    · rw [ite_eq_right (by rw [h5_18, h7_18, hEqSnd]; exact Nat.lt_irrefl _)] at hpc19
      have haBrSnd2 : code[s19.pc]? = some (.branchLt reg7 reg5 (loopPc + 118) (loopPc + 78)) := by
        rw [hpc19]; exact hSecond 4 _ rfl
      obtain ⟨s20, hs20Raw, hpc20, hr20, hd20⟩ := step_branchLt_at (input := input) haBrSnd2 (by split <;> omega)
      have hs20 := steps_1_of_step hs20Raw
      rw [ite_eq_right (by rw [hr19F reg5, hr19F reg7, h5_18, h7_18, hEqSnd]; exact Nat.lt_irrefl _)] at hpc20
      have hr20F := reg_of_regs_eq hr20
      have hRM20 : (reg s20 rMeta).val = metaBase := by rw [hr20F, hr19F, hM_18]
      have h0_20 : (reg s20 reg0).val = 0 := by rw [hr20F, hr19F, h0_18]
      have h1_20 : (reg s20 reg1).val = 1 := by rw [hr20F, hr19F, h1_18]
      have h6_20 : (reg s20 reg6).val = rTail := by rw [hr20F, hr19F, h6_18]
      have hData20 : ∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → s20.data[j]? = st.data[j]? := fun j h1 h2 => by
        rw [hd20, hd19, hData18 j h1 h2]
      have hLocal : IntervalWordsAt s20.data (metaBase + 33) acc.x1 :=
        intervalWordsAt_frame (fun i hi => hData20 _ (by omega) (by omega)) hAcc.2
      obtain ⟨kD, sD, hkD, hsD, hpcD, h0D, h1D, hMD, hJoinD, hFrameD⟩ :=
        step4A_direct_spec (input := input) (loopPc + 78) (loopPc + 398) 33 metaBase rTail h100
          (by decide) hBoundMeta (step4A_secondDirect_placed hPl) (by omega) (by omega)
          s20 hpc20 h0_20 h1_20 hRM20 h6_20 acc.x1 hLocal
      have hPtrD : (sD.data[metaBase + mIdxArcPtr]?).map Fin.val = some arcPtr := by
        change (sD.data[metaBase + 25]?).map Fin.val = some arcPtr
        rw [hFrameD _ (Or.inl (by omega)) (Or.inl (by omega)), hData20 _ (by omega) (by omega)]
        exact hPtr
      obtain ⟨t, ht, hpct, h0T, h1T, hMT, hPtrT, hFrT⟩ := step4A_nextArc_spec (input := input)
        loopPc n m N arcPtr h100 hPl hSz hNLe large hWork hWorkFit
        (Nat.lt_of_lt_of_le hPtrLt hEndLe) sD hpcD h0D h1D hMD hPtrD
      have hFrAll : ∀ j, (j < metaBase + 25 ∨
          (metaBase + 26 ≤ j ∧ j < metaBase + 28) ∨
          (metaBase + 48 ≤ j ∧ j < metaBase + 53) ∨ metaBase + 55 ≤ j) →
          t.data[j]? = st.data[j]? := by
        intro j hj
        obtain ⟨hNe, hAccFr, hTmpFr, h53, h54⟩ := arcFrameDirect (a := 33) (by decide) hj
        rw [hFrT j hNe, hFrameD j hAccFr hTmpFr, hData20 j h53 h54]
      have hRamEq : ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e =
          ⟨acc.x0, Interval.join acc.x1 (.span rTail rTail)⟩ := by
        unfold ramArcStep
        rw [dite_eq_left heLt]
        dsimp only
        rw [ite_eq_right hEqFst, ite_eq_left hEqSnd]
      have hNew : IntervalWordsAt t.data (metaBase + 33) (Interval.join acc.x1 (.span rTail rTail)) :=
        intervalWordsAt_frame (fun i hi => hFrT _ (by dsimp only [mIdxArcPtr]; omega)) hJoinD
      have hOther : IntervalWordsAt t.data (metaBase + 30) acc.x0 := by
        apply intervalWordsAt_frame ?_ hAcc.1
        intro i hi
        rw [hFrT (metaBase + 30 + i) (by dsimp only [mIdxArcPtr]; omega),
          hFrameD _ (by omega) (Or.inl (by omega)), hData20 _ (by omega) (by omega)]
      have hAccT : ValuesWordsAt t.data (metaBase + mIdxAcc0)
          (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) := by
        rw [hRamEq]
        exact ⟨hOther, hNew⟩
      have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
      have hPre : Steps code input (31 + (k1 + (3 + (1 + 1)))) st s20 := hSteps15.append (hsC.append (hs18.append (hs19.append hs20)))
      have hTot := hPre.append (hsD.append ht)
      refine ⟨_, t, ?_, hTot, hpct, hMeta.preserve hMT h0T h1T ?_, hPtrT, hAccT, hFrAll⟩
      · rcases hk1 with rfl | rfl <;> omega
      · intro i hi
        exact hFrAll (metaBase + i) (Or.inl (by omega))
    · exact False.elim (hEndpoint.elim hEqFst hEqSnd)

end PaperB.RamProgram.ExitSummaryBuild
