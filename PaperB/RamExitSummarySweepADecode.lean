module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepANext

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 / EX5.2 Word-RAM exit-summary builder (`PaperB/RamExitSummaryBuild.lean`).

Contains:
1. Mathematical bridges connecting the Word-RAM Stage 4 computations (`Step 4A` incoming-arc
   base fold, `Step 4B` endpoint-lift + `Stored.parentOnly`/`Stored.skew`) to
   `ActualSealedContract`, `DecodedOccupied`, `LiveStoreOK`, `BaseBound`, and
   `SealedPriorBase.Placed`.
2. `stage4Phase` (`run_stage4`), composed via `PhaseChain` & `run_linkNonEmpty` with
   `setupPhases` into the single fixed 15-register Word-RAM program `exitSummaryBuildProgram`,
   proving `run_exitSummaryBuild`.
-/

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

theorem step4A_decode_spec {code : Program DomL} {input : Input DomL}
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
    (Bcut : CutPair H) (arcPtr arcEnd e : Nat) (heLt : e < H.arcCount)
    (hPtrLt : arcPtr < arcEnd) (hEndLe : arcEnd ≤ H.arcCount)
    (st : State DomL) (hpc : st.pc = loopPc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hPtr : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr]?).map Fin.val = some arcPtr)
    (hEnd : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcEnd]?).map Fin.val = some arcEnd)
    (hArcId : (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + arcPtr]?).map Fin.val = some e)
    (hBFst : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48]?).map Fin.val = some Bcut.fst.val)
    :
    let metaBase := metaArrBase H.vertexCount H.arcCount r.out.tables.next
    let occ := rawOccurrence H ⟨e, heLt⟩
    ∃ t, Steps code input 31 st t ∧ t.pc = loopPc + 31 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      (reg t reg5).val = occ.1.val ∧ (reg t reg6).val = entryRank occ.2.origTail ∧
      (reg t reg7).val = Bcut.fst.val ∧
      (∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → t.data[j]? = st.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let metaBase := metaArrBase n m N
  have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hBoundMeta : metaBase + 64 ≤ workCap := by
    dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
  have hFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (by omega) hWorkFit
  have hArcFit : inArcIdArrBase n N + arcPtr < 2 ^ bits := by
    have hBase : inArcIdArrBase n N + m = metaBase := rfl
    exact Nat.lt_of_lt_of_le (by omega) hWorkFit
  have hInCap : 4 + n + 4 * N + 3 * m ≤ inputCap := hIn.cap_ge
  have hInFit : inputCap ≤ 2 ^ bits := hi
  have hmPos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) heLt
  have hR0 := hMeta.r0_zero
  have hR1 := hMeta.r1_one
  have hRM := hMeta.rMeta_eq
  have hDecode := step4A_decode_placed hPl
  -- Step 0..27: load arcPtr, arcEnd, branch, decode e, u, rTail, store 53, 54, load Bcut.fst!
  have hPl0 : Placed code loopPc (metaLoadInstrs (bits := bits) reg2 reg4 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega)) :=
    Placed_window hDecode 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) hpc hRM (hFit mIdxArcPtr (by decide)) hPtr
  have hRM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hRM]
  have hPl1 : Placed code (loopPc + 3) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxArcEnd (by dsimp only [mIdxArcEnd]; omega)) :=
    Placed_window hDecode 3 rfl
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc1 hRM1 (hFit mIdxArcEnd (by decide)) (by rw [hd1]; exact hEnd)
  have h2_2 : (reg s2 reg2).val = arcPtr := by
    rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have haBr0 : code[s2.pc]? = some (.branchLt reg2 reg3 (loopPc + 7) (loopPc + 406)) := by
    rw [hpc2]; exact hDecode 6 _ rfl
  obtain ⟨s3, hs3, hpc3, hr3, hd3⟩ := step_branchLt_at (input := input) haBr0 (by split <;> omega)
  rw [ite_eq_left (by rw [h2_2, h3_2]; exact hPtrLt)] at hpc3
  have hr3F := reg_of_regs_eq hr3
  have hRM3 : (reg s3 rMeta).val = metaBase := by
    rw [hr3F, hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hRM1]
  have hd3' : s3.data = st.data := by rw [hd3, hd2, hd1]
  -- Load `mIdxInArcIdBase`, add `reg2` (`arcPtr`), loadData -> `e`:
  have hPl2 : Placed code (loopPc + 7) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxInArcIdBase (by dsimp only [mIdxInArcIdBase]; omega)) :=
    Placed_window hDecode 7 rfl
  obtain ⟨s4, hs4, hpc4, hd4, h4_4, hPres4⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl2 (by omega) hpc3 hRM3 (hFit mIdxInArcIdBase (by decide))
    (by rw [hd3']; exact hMeta.meta_inArcIdBase)
  have h2_4 : (reg s4 reg2).val = arcPtr := by
    rw [hPres4 reg2 (by intro h; cases h) (by intro h; cases h), hr3F, h2_2]
  have haAddE : code[s4.pc]? = some (.add reg4 reg4 reg2) := by rw [hpc4]; exact hDecode 10 _ rfl
  obtain ⟨s5, hs5, hpc5, h4_5, ho5, hd5⟩ := step_add_at (input := input) haAddE (by omega)
  have h4Val5 : (reg s5 reg4).val = inArcIdArrBase n N + arcPtr := by
    have hBase : (reg s4 reg4).val = inArcIdArrBase n N := h4_4
    rw [h4_5, add_no_wrap _ _ (by rw [hBase, h2_4]; exact hArcFit), hBase, h2_4]
  obtain ⟨we, hwe, hweV⟩ := Option.map_eq_some_iff.mp hArcId
  have haLoadE : code[s5.pc]? = some (.loadData reg4 reg4) := by rw [hpc5, hpc4]; exact hDecode 11 _ rfl
  obtain ⟨s6, hs6, hpc6, h4_6, ho6, hd6⟩ := step_loadData_at (input := input) haLoadE (by omega)
    (by rw [h4Val5, hd5, hd4, hd3']; exact hwe)
  have heVal6 : (reg s6 reg4).val = e := by rw [h4_6, hweV]
  have hRM6 : (reg s6 rMeta).val = metaBase := by
    rw [ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h),
      hPres4 rMeta (by intro h; cases h) (by intro h; cases h), hRM3]
  have hd6' : s6.data = st.data := by rw [hd6, hd5, hd4, hd3']
  -- Load `mIdxQSrcInBase`, add `e`, loadInput -> `u`, store at 53:
  have hPl3 : Placed code (loopPc + 12) (metaLoadInstrs (bits := bits) reg5 reg6 mIdxQSrcInBase (by dsimp only [mIdxQSrcInBase]; omega)) :=
    Placed_window hDecode 12 rfl
  obtain ⟨s7, hs7, hpc7, hd7, h5_7, hPres7⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl3 (by omega) (by rw [hpc6, hpc5, hpc4]) hRM6 (hFit mIdxQSrcInBase (by decide))
    (by rw [hd6']; exact hMeta.meta_qSrcIn hmPos)
  have h4_7 : (reg s7 reg4).val = e := by
    rw [hPres7 reg4 (by intro h; cases h) (by intro h; cases h), heVal6]
  have haAddU : code[s7.pc]? = some (.add reg5 reg5 reg4) := by rw [hpc7]; exact hDecode 15 _ rfl
  obtain ⟨s8, hs8, hpc8, h5_8, ho8, hd8⟩ := step_add_at (input := input) haAddU (by omega)
  have h5Val8 : (reg s8 reg5).val = 4 + n + 4 * N + e := by
    rw [h5_8, add_no_wrap _ _ (by rw [h5_7, h4_7]; omega), h5_7, h4_7]
  let occ := rawOccurrence H ⟨e, heLt⟩
  let u := occ.1
  let rTail := entryRank occ.2.origTail
  obtain ⟨wu, hwu, hwuV⟩ := Option.map_eq_some_iff.mp (hIn.qSrc_at ⟨e, heLt⟩)
  have haLoadU : code[s8.pc]? = some (.loadInput reg5 reg5) := by rw [hpc8, hpc7]; exact hDecode 16 _ rfl
  obtain ⟨s9, hs9, hpc9, h5_9, ho9, hd9⟩ := step_loadInput_at (input := input) haLoadU (by omega)
    (by rw [h5Val8]; exact hwu)
  have huVal9 : (reg s9 reg5).val = u.val := by rw [h5_9, hwuV]
  have hRM9 : (reg s9 rMeta).val = metaBase := by
    rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h),
      hPres7 rMeta (by intro h; cases h) (by intro h; cases h), hRM6]
  have hd9' : s9.data = st.data := by rw [hd9, hd8, hd7, hd6']
  have hPl4 : Placed code (loopPc + 17) (metaStoreInstrs (bits := bits) reg5 reg6 53 (by omega)) :=
    Placed_window hDecode 17 rfl
  obtain ⟨s10, hs10, hpc10, _, hFr10, hPres10⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl4 (by omega) (by rw [hpc9, hpc8, hpc7]) hRM9 (by omega)
    (by rw [hd9']; exact lt_data_size (by omega))
  have hRM10 : (reg s10 rMeta).val = metaBase := by rw [hPres10 rMeta (by intro h; cases h), hRM9]
  have h4_10 : (reg s10 reg4).val = e := by
    rw [hPres10 reg4 (by intro h; cases h), ho9 reg4 (by intro h; cases h), ho8 reg4 (by intro h; cases h), h4_7]
  have h5_10 : (reg s10 reg5).val = u.val := by rw [hPres10 reg5 (by intro h; cases h), huVal9]
  -- Load `mIdxQTailRankInBase`, add `e`, loadInput -> `rTail`, store at 54, load Bcut.fst:
  have hPl5 : Placed code (loopPc + 20) (metaLoadInstrs (bits := bits) reg6 reg7 mIdxQTailRankInBase (by dsimp only [mIdxQTailRankInBase]; omega)) :=
    Placed_window hDecode 20 rfl
  obtain ⟨s11, hs11, hpc11, hd11, h6_11, hPres11⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl5 (by omega) hpc10 hRM10 (hFit mIdxQTailRankInBase (by decide))
    (by rw [hFr10 _ (by dsimp only [mIdxQTailRankInBase]; omega), hd9']; exact hMeta.meta_qTailRankIn hmPos)
  have h4_11 : (reg s11 reg4).val = e := by rw [hPres11 reg4 (by intro h; cases h) (by intro h; cases h), h4_10]
  have haAddT : code[s11.pc]? = some (.add reg6 reg6 reg4) := by rw [hpc11]; exact hDecode 23 _ rfl
  obtain ⟨s12, hs12, hpc12, h6_12, ho12, hd12⟩ := step_add_at (input := input) haAddT (by omega)
  have h6Val12 : (reg s12 reg6).val = 4 + n + 4 * N + 2 * m + e := by
    rw [h6_12, add_no_wrap _ _ (by rw [h6_11, h4_11]; omega), h6_11, h4_11]
  obtain ⟨wt, hwt, hwtV⟩ := Option.map_eq_some_iff.mp (hIn.qTailRank_at ⟨e, heLt⟩)
  have haLoadT : code[s12.pc]? = some (.loadInput reg6 reg6) := by rw [hpc12, hpc11]; exact hDecode 24 _ rfl
  obtain ⟨s13, hs13, hpc13, h6_13, ho13, hd13⟩ := step_loadInput_at (input := input) haLoadT (by omega)
    (by rw [h6Val12]; exact hwt)
  have htVal13 : (reg s13 reg6).val = rTail := by rw [h6_13, hwtV]
  have hRM13 : (reg s13 rMeta).val = metaBase := by
    rw [ho13 rMeta (by intro h; cases h), ho12 rMeta (by intro h; cases h),
      hPres11 rMeta (by intro h; cases h) (by intro h; cases h), hRM10]
  have hPl6 : Placed code (loopPc + 25) (metaStoreInstrs (bits := bits) reg6 reg7 54 (by omega)) :=
    Placed_window hDecode 25 rfl
  obtain ⟨s14, hs14, hpc14, _, hFr14, hPres14⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl6 (by omega) (by rw [hpc13, hpc12, hpc11]) hRM13 (by omega)
    (by rw [hd13, hd12, hd11]; exact lt_data_size (by omega))
  have hRM14 : (reg s14 rMeta).val = metaBase := by rw [hPres14 rMeta (by intro h; cases h), hRM13]
  have hFr14_9 : ∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → s14.data[j]? = st.data[j]? := by
    intro j hj1 hj2
    rw [hFr14 j hj2, hd13, hd12, hd11, hFr10 j hj1, hd9']
  have hPl7 : Placed code (loopPc + 28) (metaLoadInstrs (bits := bits) reg7 reg8 48 (by omega)) :=
    Placed_window hDecode 28 rfl
  obtain ⟨s15, hs15, hpc15, hd15, h7_15, hPres15⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl7 (by omega) hpc14 hRM14 (by omega)
    (by rw [hFr14_9 _ (by omega) (by omega)]; exact hBFst)
  -- Common registers preserved up to `s15`:
  have h5_15 : (reg s15 reg5).val = u.val := by
    rw [hPres15 reg5 (by intro h; cases h) (by intro h; cases h), hPres14 reg5 (by intro h; cases h),
      ho13 reg5 (by intro h; cases h), ho12 reg5 (by intro h; cases h),
      hPres11 reg5 (by intro h; cases h) (by intro h; cases h), h5_10]
  have h6_15 : (reg s15 reg6).val = rTail := by
    rw [hPres15 reg6 (by intro h; cases h) (by intro h; cases h), hPres14 reg6 (by intro h; cases h), htVal13]
  have h0_15 : (reg s15 reg0).val = 0 := by
    rw [hPres15 reg0 (by intro h; cases h) (by intro h; cases h), hPres14 reg0 (by intro h; cases h),
      ho13 reg0 (by intro h; cases h), ho12 reg0 (by intro h; cases h),
      hPres11 reg0 (by intro h; cases h) (by intro h; cases h), hPres10 reg0 (by intro h; cases h),
      ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h),
      hPres7 reg0 (by intro h; cases h) (by intro h; cases h), ho6 reg0 (by intro h; cases h),
      ho5 reg0 (by intro h; cases h), hPres4 reg0 (by intro h; cases h) (by intro h; cases h),
      hr3F, hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hR0]
  have h1_15 : (reg s15 reg1).val = 1 := by
    rw [hPres15 reg1 (by intro h; cases h) (by intro h; cases h), hPres14 reg1 (by intro h; cases h),
      ho13 reg1 (by intro h; cases h), ho12 reg1 (by intro h; cases h),
      hPres11 reg1 (by intro h; cases h) (by intro h; cases h), hPres10 reg1 (by intro h; cases h),
      ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h),
      hPres7 reg1 (by intro h; cases h) (by intro h; cases h), ho6 reg1 (by intro h; cases h),
      ho5 reg1 (by intro h; cases h), hPres4 reg1 (by intro h; cases h) (by intro h; cases h),
      hr3F, hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hR1]
  have hRM15 : (reg s15 rMeta).val = metaBase := by
    rw [hPres15 rMeta (by intro h; cases h) (by intro h; cases h), hRM14]
  have hData15 : ∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → s15.data[j]? = st.data[j]? := fun j hj1 hj2 => by
    rw [hd15]; exact hFr14_9 j hj1 hj2
  have hReadPair : Steps code input 7 st s3 :=
    hs1.append (hs2.append (steps_1_of_step hs3))
  have hReadArc : Steps code input 5 s3 s6 :=
    hs4.append (Steps.cons hs5 (steps_1_of_step hs6))
  have hReadSource : Steps code input 8 s6 s10 :=
    hs7.append (Steps.cons hs8 (Steps.cons hs9 hs10))
  have hReadTail : Steps code input 8 s10 s14 :=
    hs11.append (Steps.cons hs12 (Steps.cons hs13 hs14))
  exact ⟨s15, (((hReadPair.append hReadArc).append hReadSource).append hReadTail).append hs15,
    hpc15, h0_15, h1_15, hRM15, h5_15, h6_15, h7_15, hData15⟩

end PaperB.RamProgram.ExitSummaryBuild
