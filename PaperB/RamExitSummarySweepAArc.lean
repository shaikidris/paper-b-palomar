module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepADecode
public import PaperB.RamExitSummarySweepAArcDirect
public import PaperB.RamExitSummarySweepAJoin
public import PaperB.RamExitSummarySweepAAncestry
public import PaperB.RamExitSummarySweepAPrepare

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

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

private theorem arcFrameNonendpoint {b j : Nat}
    (h : j < b + 25 ∨ (b + 26 ≤ j ∧ j < b + 28) ∨
      (b + 48 ≤ j ∧ j < b + 53) ∨ b + 55 ≤ j) :
    j ≠ b + 25 ∧ (j < b + 30 ∨ b + 33 ≤ j) ∧
      (j < b + 33 ∨ b + 36 ≤ j) ∧
      (j < b + 28 ∨ (b + 30 ≤ j ∧ j < b + 36) ∨
        (b + 48 ≤ j ∧ j < b + 53) ∨ b + 55 ≤ j) ∧ j ≠ b + 53 ∧ j ≠ b + 54 := by
  omega

private theorem arcFrameEval {b j : Nat}
    (h : j < b + 28 ∨ (b + 30 ≤ j ∧ j < b + 36) ∨
      (b + 48 ≤ j ∧ j < b + 53) ∨ b + 55 ≤ j) :
    (j < b + 28 ∨ (b + 29 ≤ j ∧ j < b + 36) ∨ b + 48 ≤ j) ∧
      j ≠ b + 28 ∧ j ≠ b + 29 ∧ (j < b + 36 ∨ b + 42 ≤ j) ∧
      j ≠ b + 53 ∧ j ≠ b + 54 := by
  omega

theorem step4A_arc_nonendpoint_spec {code : Program DomL} {input : Input DomL}
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
    (_hFitRank : ∀ x : Fin H.origVertexCount, entryRank x < 2 ^ bits)
    {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F ref live)
    (hFSize : F.size = r.out.tables.next)
    (B := buildActualSweepBundle H flat increasing covers rankArc r)
    (hFEq : F = B.F)
    (ownerSlot : Nat) (_hOwnPos : 0 < ownerSlot) (hOwnLt : ownerSlot < r.out.tables.next)
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
    (hOwnEn : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 50]?).map Fin.val =
      some (r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)))
    (hOwnSt : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 51]?).map Fin.val =
      some (r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)))
    (hOwnDep : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 52]?).map Fin.val =
      some (F.depthOf ownerSlot))
    (acc : Values)
    (hAcc : ValuesWordsAt st.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0) acc)
    (hDepth : ∀ w : Fin r.out.tables.next, (st.data[w.val]?).map Fin.val = some (F.depthOf w.val))
    (hStored : ∀ w : Fin r.out.tables.next, live w.val →
      (st.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
      (st.data[storedBase r.out.tables.next + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 2) (ref w.val).parentMap ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 10) (ref w.val).jumpMap)
    (hBaseAtU : let u := (rawOccurrence H ⟨e, heLt⟩).1
      ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * u.val) (baseFn u))
    (hLiveAtV : let u := (rawOccurrence H ⟨e, heLt⟩).1
      let v := (selectors (orderedConfig p large) r.out).label u
      let hvLt : v < r.out.tables.next := B.G.size_eq ▸ B.E.label_lt u True.intro
      u.val ≠ Bcut.fst.val → u.val ≠ Bcut.snd.val → 0 < v →
      r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) ≤
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) →
      r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) <
        r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) →
      live v)
    (hNonendpoint : let u := (rawOccurrence H ⟨e, heLt⟩).1
      u.val ≠ Bcut.fst.val ∧ u.val ≠ Bcut.snd.val) :
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
  have hInCap : 4 + n + 4 * N + 3 * m ≤ inputCap := hIn.cap_ge
  have hInFit : inputCap ≤ 2 ^ bits := hi
  have hmPos : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) heLt
  have hR0 := hMeta.r0_zero
  have hR1 := hMeta.r1_one
  have hRM := hMeta.rMeta_eq
  let occ := rawOccurrence H ⟨e, heLt⟩
  let u := occ.1
  let rTail := entryRank occ.2.origTail
  obtain ⟨s15, hSteps15, hpc15, h0_15, h1_15, hRM15, h5_15, h6_15, h7_15, hData15⟩ :=
    step4A_decode_spec (input := input) loopPc h100 hPl hSz flat increasing covers rankArc
      hIn hWork Bcut arcPtr arcEnd e heLt hPtrLt hEndLe st hpc hMeta hPtr hEnd hArcId hBFst
  have hDecode := step4A_decode_placed hPl
  have hSecond := step4A_secondEndpoint_placed hPl
  have hAncestry := step4A_ancestry_placed hPl
  have hJoinFirst := step4A_joinFirst_placed hPl
  have hJoinSecond := step4A_joinSecond_placed hPl
  -- Compare `u` (`reg5`) with `Bcut.fst` (`reg7`):
  have haBrFst1 : code[s15.pc]? = some (.branchLt reg5 reg7 (loopPc + 73) (loopPc + 32)) := by
    rw [hpc15]; exact hDecode 31 _ rfl
  obtain ⟨s16, hs16Raw, hpc16, hr16, hd16⟩ := step_branchLt_at (input := input) haBrFst1 (by split <;> omega)
  have hs16 := steps_1_of_step hs16Raw
  have hr16F := reg_of_regs_eq hr16
  have hEqFst : u.val ≠ Bcut.fst.val := hNonendpoint.1
  have hEqSnd : u.val ≠ Bcut.snd.val := hNonendpoint.2
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
  have hToChkLift : ∃ k2 sL, (k2 = 1 ∨ k2 = 2) ∧ Steps code input k2 s18 sL ∧ sL.pc = loopPc + 118 ∧
      (reg sL reg0).val = 0 ∧ (reg sL reg1).val = 1 ∧ (reg sL rMeta).val = metaBase ∧
      (reg sL reg5).val = u.val ∧
      (∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → sL.data[j]? = st.data[j]?) := by
    by_cases hLt2 : u.val < Bcut.snd.val
    · rw [ite_eq_left (by rw [h5_18, h7_18]; exact hLt2)] at hpc19
      exact ⟨1, s19, Or.inl rfl, hs19, hpc19,
        by rw [hr19F, h0_18], by rw [hr19F, h1_18], by rw [hr19F, hM_18],
        by rw [hr19F, h5_18], fun j h1 h2 => by rw [hd19, hData18 j h1 h2]⟩
    · have hGt2 : Bcut.snd.val < u.val := by omega
      rw [ite_eq_right (by rw [h5_18, h7_18]; exact hLt2)] at hpc19
      have haBr2 : code[s19.pc]? = some (.branchLt reg7 reg5 (loopPc + 118) (loopPc + 78)) := by
        rw [hpc19]; exact hSecond 4 _ rfl
      obtain ⟨s20, hs20Raw, hpc20, hr20, hd20⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
      have hs20 := steps_1_of_step hs20Raw
      rw [ite_eq_left (by rw [hr19F reg5, hr19F reg7, h5_18, h7_18]; exact hGt2)] at hpc20
      have hr20F := reg_of_regs_eq hr20
      exact ⟨2, s20, Or.inr rfl, hs19.append hs20, hpc20,
        by rw [hr20F, hr19F, h0_18], by rw [hr20F, hr19F, h1_18], by rw [hr20F, hr19F, hM_18],
        by rw [hr20F, hr19F, h5_18], fun j h1 h2 => by rw [hd20, hd19, hData18 j h1 h2]⟩
  obtain ⟨k2, sL, hk2, hsL, hpcL, h0L, h1L, hML, h5L, hDataL⟩ := hToChkLift
  let v := (selectors (orderedConfig p large) r.out).label u
  have hvLt : v < r.out.tables.next := by
    rw [← B.G.size_eq]
    exact B.E.label_lt u True.intro
  let vEntry := r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩)
  let ownerEntry := r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)
  let ownerStop := r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)
  have hAtL := hIn.labels_at u
  have hAtE := hIn.fEntry_at ⟨v, hvLt⟩
  obtain ⟨kAn, sAn, hkAn, hsAn, hpcAn, hdAn, h0An, h1An, hMAn, h5An, h6An⟩ :=
    step4A_ancestry_spec (input := input) loopPc n N metaBase u.val v vEntry ownerEntry ownerStop
      h100 u.isLt hvLt hBoundMeta (by omega) hAncestry hSz sL hpcL h0L h1L hML h5L
      (by rw [hDataL (metaBase + mIdxLabelsInBase)
            (by dsimp only [mIdxLabelsInBase]; omega) (by dsimp only [mIdxLabelsInBase]; omega)]
          exact hMeta.meta_labelsIn)
      (by rw [hDataL (metaBase + mIdxFEntryInBase)
            (by dsimp only [mIdxFEntryInBase]; omega) (by dsimp only [mIdxFEntryInBase]; omega)]
          exact hMeta.meta_fEntryIn)
      hAtL hAtE
      (by rw [hDataL (metaBase + 50) (by omega) (by omega)]; exact hOwnEn)
      (by rw [hDataL (metaBase + 51) (by omega) (by omega)]; exact hOwnSt)
  have hDataAn : ∀ j, j ≠ metaBase + 53 → j ≠ metaBase + 54 → sAn.data[j]? = st.data[j]? := by
    intro j h53 h54
    rw [hdAn, hDataL j h53 h54]
  have hPre := hSteps15.append (hsC.append (hs18.append (hsL.append hsAn)))
  by_cases hTest : 0 < v ∧ ownerEntry ≤ vEntry ∧ vEntry < ownerStop
  · rw [ite_eq_left hTest] at hpcAn
    have hLiveV : live v := hLiveAtV hEqFst hEqSnd hTest.1 hTest.2.1 hTest.2.2
    have hPriorBound : priorBase N + 6 * u.val + 6 ≤ metaBase := by
      have := u.isLt
      unfold priorBase
      omega
    have hValuesAn : ValuesWordsAt sAn.data (priorBase N + 6 * u.val) (baseFn u) :=
      valuesWordsAt_frame (fun i hi => hDataAn _ (by omega) (by omega)) hBaseAtU
    obtain ⟨s42, hs42, hpc42, h0_42, h1_42, hM_42, hEU42, hED42, hVals42, hFr42⟩ :=
      step4A_prepareLift_spec (input := input) loopPc N metaBase u.val v (F.depthOf ownerSlot)
        h100 hBoundMeta hPriorBound hAncestry hSz sAn hpcAn h0An h1An hMAn h5An h6An
        (by rw [hDataAn (metaBase + 52) (by omega) (by omega)]; exact hOwnDep)
        (by rw [hDataAn (metaBase + mIdxPriorBase)
              (by dsimp only [mIdxPriorBase]; omega) (by dsimp only [mIdxPriorBase]; omega)]
            exact hMeta.meta_priorBase)
        (baseFn u) hValuesAn
    have hData42 : ∀ j, j ≠ metaBase + mIdxEvalU → j ≠ metaBase + mIdxEvalD →
        (j < metaBase + mIdxEval0 ∨ metaBase + 42 ≤ j) →
        j ≠ metaBase + 53 → j ≠ metaBase + 54 →
        s42.data[j]? = st.data[j]? := by
      intro j hU hD hX h53 h54
      rw [hFr42 j hU hD hX, hDataAn j h53 h54]
    have hBelow42 : ∀ j, j < metaBase → s42.data[j]? = st.data[j]? := by
      intro j hj
      exact hData42 j (by dsimp only [mIdxEvalU]; omega) (by dsimp only [mIdxEvalD]; omega)
        (Or.inl (by dsimp only [mIdxEval0]; omega)) (by omega) (by omega)
    have valid : ValidJumpForest F := by rw [hFEq]; exact B.G.layout.valid
    have hPlEv := step4A_eval15_placed hPl
    obtain ⟨kEv, s43, hkEv, hs43, hpc43, h0_43, h1_43, hM_43, hVals43, hFr43⟩ :=
      run_eval15 (input := input) (loopPc + 177) h100 hPlEv (by omega) valid ok hNLe (by omega)
        hWorkFit hFSize (F.depthOf v - F.depthOf ownerSlot) v hLiveV hvLt (baseFn u)
        s42 rfl hpc42 h0_42 h1_42 hM_42
        (by rw [hData42 (metaBase + mIdxStoredBase)
              (by dsimp only [mIdxStoredBase, mIdxEvalU]; omega)
              (by dsimp only [mIdxStoredBase, mIdxEvalD]; omega)
              (Or.inl (by dsimp only [mIdxStoredBase, mIdxEval0]; omega))
              (by dsimp only [mIdxStoredBase]; omega) (by dsimp only [mIdxStoredBase]; omega)]
            exact hMeta.meta_storedBase)
        hEU42 hED42 hVals42
        (fun w => by rw [hBelow42 _ (by have := w.isLt; omega)]; exact hDepth w)
        (fun w hwL => by
          have hSeg : ∀ i < 18, s42.data[storedBase N + 18 * w.val + i]? =
              st.data[storedBase N + 18 * w.val + i]? := fun i hi =>
            hBelow42 _ (by have := w.isLt; unfold storedBase; omega)
          have ho := hStored w hwL
          refine ⟨by rw [hBelow42 _ (by have := w.isLt; unfold storedBase; omega)]; exact ho.1, by rw [hSeg 1 (by decide)]; exact ho.2.1,
            mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (2 + i) (by omega)) ho.2.2.1,
            mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (10 + i) (by omega)) ho.2.2.2⟩)
    have hFrameEval : ∀ j, (j < metaBase + 28 ∨
        (metaBase + 30 ≤ j ∧ j < metaBase + 36) ∨
        (metaBase + 48 ≤ j ∧ j < metaBase + 53) ∨ metaBase + 55 ≤ j) →
        s43.data[j]? = st.data[j]? := by
      intro j hj
      obtain ⟨hK, hU, hD, hTemp, h53, h54⟩ := arcFrameEval hj
      rw [hFr43 j hK, hData42 j hU hD hTemp h53 h54]
    let lifted := Map.eval (foldFused F ref v (F.depthOf ownerSlot)).composed (baseFn u)
    have hAtFirst : IntervalWordsAt s43.data (metaBase + 30) acc.x0 :=
      intervalWordsAt_frame (fun i hi => hFrameEval (metaBase + 30 + i)
        (Or.inr (Or.inl ⟨by omega, by omega⟩))) hAcc.1
    obtain ⟨kJ0, s49, hkJ0, hs49, hpc49, h0_49, h1_49, hM_49, hJoin49, hFr49⟩ :=
      step4A_joinAt_spec (input := input) (loopPc + 338) metaBase 30 36 h100
        (by decide) (by decide) hBoundMeta hJoinFirst (by omega)
        s43 hpc43 h0_43 h1_43 hM_43 acc.x0 lifted.x0 hAtFirst hVals43.1
    have hAtSecond : IntervalWordsAt s49.data (metaBase + 33) acc.x1 := by
      apply intervalWordsAt_frame ?_ hAcc.2
      intro i hi
      rw [hFr49 (metaBase + 33 + i) (Or.inr (by omega))]
      exact hFrameEval (metaBase + 33 + i) (Or.inr (Or.inl ⟨by omega, by omega⟩))
    have hEvSecond : IntervalWordsAt s49.data (metaBase + 39) lifted.x1 :=
      intervalWordsAt_frame (fun i hi => hFr49 (metaBase + 39 + i) (Or.inr (by omega))) hVals43.2
    obtain ⟨kJ1, s55, hkJ1, hs55, hpc55, h0_55, h1_55, hM_55, hJoin55, hFr55⟩ :=
      step4A_joinAt_spec (input := input) (loopPc + 368) metaBase 33 39 h100
        (by decide) (by decide) hBoundMeta hJoinSecond (by omega)
        s49 hpc49 h0_49 h1_49 hM_49 acc.x1 lifted.x1 hAtSecond hEvSecond
    have hPtr55 : (s55.data[metaBase + mIdxArcPtr]?).map Fin.val = some arcPtr := by
      change (s55.data[metaBase + 25]?).map Fin.val = some arcPtr
      rw [hFr55 (metaBase + 25) (Or.inl (by omega)),
        hFr49 (metaBase + 25) (Or.inl (by omega)),
        hFrameEval (metaBase + 25) (Or.inl (by omega))]
      exact hPtr
    obtain ⟨t, ht, hpct, h0T, h1T, hMT, hPtrT, hFrT⟩ := step4A_nextArc_spec (input := input)
      loopPc n m N arcPtr h100 hPl hSz hNLe large hWork hWorkFit
      (Nat.lt_of_lt_of_le hPtrLt hEndLe) s55 hpc55 h0_55 h1_55 hM_55 hPtr55
    have hFrAll : ∀ j, (j < metaBase + 25 ∨
        (metaBase + 26 ≤ j ∧ j < metaBase + 28) ∨
        (metaBase + 48 ≤ j ∧ j < metaBase + 53) ∨ metaBase + 55 ≤ j) →
        t.data[j]? = st.data[j]? := by
      intro j hj
      obtain ⟨hNe, hJ0, hJ1, hK, _, _⟩ := arcFrameNonendpoint hj
      rw [hFrT j hNe, hFr55 j hJ1, hFr49 j hJ0, hFrameEval j hK]
    have hRamEq : ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e =
        vjoin acc (Map.eval (foldFused F ref v (F.depthOf ownerSlot)).composed (baseFn u)) := by
      unfold ramArcStep
      rw [dite_eq_left heLt]
      dsimp only
      rw [ite_eq_right hEqFst, ite_eq_right hEqSnd, dite_eq_left hvLt, dite_eq_left hOwnLt,
        ite_eq_left hTest]
    have hAccT : ValuesWordsAt t.data (metaBase + mIdxAcc0)
        (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) := by
      rw [hRamEq]
      refine ⟨?_, ?_⟩
      · exact intervalWordsAt_frame (fun i hi => by
          rw [hFrT (metaBase + 30 + i) (by dsimp only [mIdxArcPtr]; omega),
            hFr55 (metaBase + 30 + i) (Or.inl (by omega))]) hJoin49
      · exact intervalWordsAt_frame (fun i hi =>
          hFrT (metaBase + 33 + i) (by dsimp only [mIdxArcPtr]; omega)) hJoin55
    have hStepsCost : (foldFused F ref v (F.depthOf ownerSlot)).steps ≤ 3 * OracleContract.L H.vertexCount := by
      have hInserted : F.numInserted ≤ H.vertexCount := by
        rw [hFEq]
        exact bundle_numInserted_le B
      have hvSize : v < F.size := hFSize.symm ▸ (show v < r.out.tables.next from hvLt)
      have hCost := foldTrace_cost ref valid hvSize hInserted (F.depthOf ownerSlot)
      rw [live_foldFused_eq_foldTrace ok hLiveV, hCost.1]
      exact Nat.le_trans hCost.2.1 (Nat.mul_le_mul_left 3 (ceilLog2_add_two_le_L H.vertexCount))
    have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
    have hTot := hPre.append (hs42.append (hs43.append (hs49.append (hs55.append ht))))
    refine ⟨_, t, ?_, hTot, hpct, hMeta.preserve hMT h0T h1T ?_, hPtrT, hAccT, hFrAll⟩
    · rcases hk1 with rfl | rfl <;> rcases hk2 with rfl | rfl <;> omega
    · intro i hi
      exact hFrAll (metaBase + i) (Or.inl (by omega))
  · rw [ite_eq_right hTest] at hpcAn
    obtain ⟨t, ht, hpct, h0T, h1T, hMT, hPtrT, hFrT⟩ := step4A_nextArc_spec (input := input) loopPc n m N arcPtr h100
      hPl hSz hNLe large hWork hWorkFit (Nat.lt_of_lt_of_le hPtrLt hEndLe) sAn hpcAn h0An h1An hMAn
      (by rw [hDataAn (metaBase + mIdxArcPtr)
        (by dsimp only [mIdxArcPtr]; omega) (by dsimp only [mIdxArcPtr]; omega)]; exact hPtr)
    have hFrAll : ∀ j, (j < metaBase + 25 ∨
        (metaBase + 26 ≤ j ∧ j < metaBase + 28) ∨
        (metaBase + 48 ≤ j ∧ j < metaBase + 53) ∨
        metaBase + 55 ≤ j) → t.data[j]? = st.data[j]? := by
      intro j hj
      obtain ⟨hNe, _, _, _, h53, h54⟩ := arcFrameNonendpoint hj
      rw [hFrT j hNe, hDataAn j h53 h54]
    have hRamEq : ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e = acc := by
      unfold ramArcStep
      rw [dite_eq_left heLt]
      dsimp only
      rw [ite_eq_right hEqFst, ite_eq_right hEqSnd, dite_eq_left hvLt, dite_eq_left hOwnLt,
        ite_eq_right hTest]
    have hAccT : ValuesWordsAt t.data (metaBase + mIdxAcc0)
        (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) := by
      rw [hRamEq]
      apply valuesWordsAt_frame ?_ hAcc
      intro i hi
      let addr := metaBase + 30 + i
      change t.data[addr]? = st.data[addr]?
      have hPtrNe : addr ≠ metaBase + mIdxArcPtr := by dsimp [addr, mIdxArcPtr]; omega
      rw [hFrT addr hPtrNe, hDataAn addr (by dsimp [addr]; omega) (by dsimp [addr]; omega)]
    have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
    have hTot := hPre.append ht
    refine ⟨_, t, ?_, hTot, hpct, hMeta.preserve hMT h0T h1T ?_, hPtrT, hAccT, hFrAll⟩
    · rcases hk1 with rfl | rfl <;> rcases hk2 with rfl | rfl <;> omega
    · intro i hi
      exact hFrAll (metaBase + i) (Or.inl (by omega))

end PaperB.RamProgram.ExitSummaryBuild
