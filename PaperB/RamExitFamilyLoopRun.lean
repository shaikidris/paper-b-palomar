module

public import PaperB.RamExitFamilyStaged
public import PaperB.RamExitFamilyLift
public import PaperB.RamExitFamilyEmitStage
public import PaperB.RamExitFamilyForestStage
public import PaperB.RamExitFamilyKernels
public import PaperB.RamExitFamilyCopies
public import PaperB.RamExitFamilyRegisters
public import PaperB.RamExitFamilyProgram
public import PaperB.RamExitFamilyLoop

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
set_option maxErrors 160

/-!
EX5.1 Exit-Summary Family Loop Program and End-to-End Proof (`PaperB.RamExitFamilyLoop`):
Sections 3–5 constructing `exitFamilyLoopProgram` and proving `run_exit_family_loop`,
chaining from `prefixAndForestLoopProgram` into `sealedPackAndShiftProgram`.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter prefixTreeBase)
open PaperB.ForestHead (Vertex)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex rawInputCap)
open PaperB.ForestSlimIndex
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
open PaperB.RamStaticReaderBridge (denseRank)
open PaperB.RamFamilyForestLoop
open PaperB.RamQuotientEmitter
open PaperB.RamDataSliceAdapter
open PaperB.RetainedProperLoss
open PaperB.ExitActualContract
open PaperB.RamSealedPacker
open PaperB.RamProgram.ExitSummaryBuild
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open PaperB.RamForestProgram.Finish (packedPayload)
open PaperB.ExitMap.Retention (TagsFit)
open PaperB.OracleContract (L)


/-! ### 5. Loop Invariant, Sub-Program Chaining, and `run_exit_family_loop` -/

section LoopInductionAndMain

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

private theorem exitLarge_sub_steps
    (h100 : 100 ≤ 2 ^ bits) (input : Input L16)
    {origData : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ j : Fin dense.length, (S.ramQuotient j).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (origData[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (j : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs j).length),
      let ea := (countingSortedArcs (1 + (S.childSlice j).length) (S.emittedArcs j))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds j hx).2.1)).symm)
      (origData[emitBaseOf workCap + 3 * n + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (origData[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.headLocal ∧
      (origData[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ j : Fin dense.length,
      OwnerForestPackedRecordAt S j (loopBaseOf workCap) n m forestUsed origData)
    {d : Fin dense.length} {exitUsed : Nat} {s₀ : State L16}
    (hInv : ExitLoopInv S n m Q forestUsed d.val exitUsed s₀)
    (hPC : s₀.pc = offLargeA)
    (hr11 : (reg s₀ r11).val = 1 + (S.childSlice d).length)
    (hLarge : 3 ≤ 1 + (S.childSlice d).length) :
    let code := exitFamilyLoopProgram hi hw h100
    ∃ (sEnd : State L16) (kIter newExitUsed : Nat),
      kIter ≤ 12300 * (2 * (S.childSlice d).length + (S.emittedArcs d).length) * OracleContract.L n ∧
      Steps code input kIter s₀ sEnd ∧
      sEnd.pc = offHdr ∧
      ExitLoopInv S n m Q forestUsed (d.val + 1) newExitUsed sEnd := by
  let subCode := exitSubProgram hw h100
  let code := exitFamilyLoopProgram hi hw h100
  have hCodeSize : code.size = 397 + 4 * subCode.size :=
    exitFamilyLoopCodeOf_size (hi := hi) (hw := hw) subCode h100
  let treeBase := prefixTreeBase workCap
  let emitBase := emitBaseOf workCap
  let loopBase := loopBaseOf workCap
  let fpPtrBase := ownerForestPtrsBase loopBase n m + 6 * d.val
  let ep0 := exitArenaBase loopBase n m + exitUsed
  let stBase := exitSubStateBase loopBase n m
  let inBase := exitSubInBase loopBase n m
  let dataBase := exitSubWorkBase loopBase n m workCap
  let n_d := 1 + (S.childSlice d).length
  let m_d := (S.emittedArcs d).length
  have hnPos : 1 ≤ n := by rw [hn]; exact Fin.pos r
  have hQn : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have h4 : 4 * prefixQuarter workCap ≤ workCap := Nat.mul_div_le workCap 4
  have h64 : 64 * (workCap / 64) ≤ workCap := Nat.mul_div_le workCap 64
  have h16 : 16 * (workCap / 16) ≤ workCap := Nat.mul_div_le workCap 16
  have hWorkEnd : exitSubWorkBase loopBase n m workCap + workCap / 16 ≤ workCap :=
    exitSubWorkEnd_le_workCap hCap
  have hTreeFit : treeBase + staticTreeWords Q ≤ workCap := by
    first | (simp only [treeBase, prefixTreeBase, staticTreeWords]; omega) | omega
  have hEmitFit : emitBase + emitterWorkWords n m ≤ workCap := by
    first | (simp only [emitBase, emitBaseOf, emitterWorkWords]; omega) | omega
  have hDisjEmit : emitBase + emitterWorkWords n m ≤ loopBase := by
    first | (simp only [emitBase, emitBaseOf, loopBase, loopBaseOf, emitterWorkWords, prefixQuarter]; omega) | omega
  have hdQ : d.val < Q := by rw [hQ]; exact d.isLt
  have hInData : dataBase = inBase + workCap / 64 := rfl
  have hDataEnd : dataBase + workCap / 16 ≤ workCap := hWorkEnd
  have hWork64 : 12 ≤ workCap / 64 := by omega
  have hWork16 : 2 ≤ workCap / 16 := by omega
  have hDataGt : inBase + 4 ≤ dataBase := by omega
  have hPtrIn : exitPtrsBase loopBase n m < inBase := by
    simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]
    omega
  have hFAEnd : forestArenaBase loopBase n m + forestUsed ≤ exitPtrsBase loopBase n m := by
    have h := forestArenaEnd_eq loopBase n m
    unfold exitPtrsBase
    omega
  have hDisjEmitIn : emitBase + emitterWorkWords n m ≤ inBase := by
    have : loopBase ≤ exitPtrsBase loopBase n m := by first | (simp only [exitPtrsBase]; omega) | omega
    first | (simp only [inBase, exitSubInBase, exitSubStateBase, exitArenaBase]; omega) | omega
  have hDisjFP : ownerForestPtrsBase loopBase n m + 6 * Q ≤ exitArenaBase loopBase n m := by
    have := ownerForestPtrsBase_add_44n loopBase n m
    first | (simp only [exitArenaBase]; omega) | omega
  have hEndEP : exitPtrsBase loopBase n m + 3 * Q ≤ exitArenaBase loopBase n m := by
    first | (simp only [exitArenaBase]; omega) | omega
  have hEnter : stBase + 16 = inBase := rfl
  have hArenaIn : exitArenaBase loopBase n m ≤ inBase := by
    simp only [inBase, exitSubInBase, stBase, exitSubStateBase]
    omega
  have hArena48 : exitArenaBase loopBase n m + 48 * n ≤ stBase := by
    first | (simp only [stBase, exitSubStateBase]; omega) | omega
  have hNdLe : n_d ≤ n := by rw [hn]; exact ramQuotient_vertexCount_le S d
  have hmEq : (S.ramQuotient d).arcCount = m_d := ramQuotient_arcCount_eq S d
  have hmLe : m_d ≤ m := by rw [hm, ← hmEq]; exact ramQuotient_arcCount_le S d
  obtain ⟨pH, dataH, sizeH, rankH, hlargeH, incH, covH, rArcH, ordResH, hWidth, ptrBase,
    sE2, sSaved, subIn, hfaLo, hfaHi, hfp0_s0, hfp1_s0, hfp2_s0, hfp3_s0, hfp4_s0, hfp5_s0,
    hPay_s0, hNextLe, hStagedCost, pcSave, regsE2, hSavedSlots, hKeepLowSave,
    hSavedKeep, hIn0Saved, hIn2Saved, hInSliceEq, hBuildIn⟩ :=
    exitLarge_stage_steps h100 input S hn hm hQ hFlat hCap hBits hForestLe hQStarts hArcs hRecs
      hInv hPC hr11 hLarge
  let wCols := packWordColumns ordResH hWidth
  let N_d := ordResH.out.tables.next
  change N_d ≤ n_d + 1 at hNextLe
  change ∀ addr < stBase, sSaved.data[addr]? = s₀.data[addr]? at hKeepLowSave
  change ∀ j : Nat, 11 ≤ j → j < 15 → sSaved.data[stBase + j]? = s₀.data[stBase + j]? at hSavedKeep
  have hStToIn : inBase = stBase + 16 := rfl
  have hInEnd : inBase + exitFamilySubInCap workCap ≤ workCap := by
    change inBase + workCap / 64 ≤ workCap
    omega
  have szSave : sSaved.data.size = workCap := sSaved.data_size
  have hSt11Save : (sSaved.data[stBase + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) := by
    rw [hSavedKeep 11 (by decide : 11 ≤ 11) (by decide : 11 < 15)]
    exact hInv.st11
  have hSt12Save : (sSaved.data[stBase + 12]?).map Fin.val = some (exitArenaBase loopBase n m) := by
    rw [hSavedKeep 12 (by decide : 11 ≤ 12) (by decide : 12 < 15)]
    exact hInv.st12
  have hSubWorkFit : exitWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤
      exitFamilySubWorkCap workCap := by
    change exitWorkCap n_d (S.ramQuotient d).arcCount ≤ workCap / 16
    rw [hmEq]
    exact exitSubWorkCap_fits hCap hLarge hNdLe hmLe
  let subStart0 : State (RamForestProgram.layout bits (exitFamilySubInCap workCap) (exitFamilySubWorkCap workCap)
      (by first | (simp only [exitFamilySubInCap]; omega) | omega) (by first | (simp only [exitFamilySubWorkCap]; omega) | omega)) :=
    { regs := Array.ofFn (fun i : Fin 15 => sSaved.regs[i.val]?.getD 0)
      data := Array.ofFn (fun j : Fin (exitFamilySubWorkCap workCap) => sSaved.data[dataBase + j.val]?.getD 0)
      pc := 0
      regs_size := Array.size_ofFn
      data_size := Array.size_ofFn }
  have hStGt : 2 < stBase := by simp only [stBase, exitSubStateBase]; omega
  have hInLo : inBase < dataBase := by omega
  have hInPtrSaved : (sSaved.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepLowSave inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hInv.inPtr
  have hDataPtrSaved : (sSaved.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepLowSave dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hInv.dataPtr
  have hInBaseLt : inBase < 2 ^ bits := by omega
  have hDataBaseLt : dataBase < 2 ^ bits := by omega
  have hCfg : SliceConfig _ L16 (w100 h100 inPtrAddr) (w100 h100 dataPtrAddr)
      inBase dataBase subIn sSaved.data :=
    { inBaseLt := hInBaseLt
      dataBaseLt := hDataBaseLt
      inPtr_lt := by show inPtrAddr < workCap; simp only [inPtrAddr]; omega
      dataPtr_lt := by show dataPtrAddr < workCap; simp only [dataPtrAddr]; omega
      inFit := hInEnd
      dataFit := hDataEnd
      inPtr_at := by
        change sSaved.data[inPtrAddr]? = some ⟨inBase, hInBaseLt⟩
        obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hInPtrSaved
        exact hwM.trans (congrArg some (Fin.ext hwV))
      dataPtr_at := by
        change sSaved.data[dataPtrAddr]? = some ⟨dataBase, hDataBaseLt⟩
        obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hDataPtrSaved
        exact hwM.trans (congrArg some (Fin.ext hwV))
      inPtr_outside := Or.inl (by show inPtrAddr < dataBase; simp only [inPtrAddr]; omega)
      dataPtr_outside := Or.inl (by show dataPtrAddr < dataBase; simp only [dataPtrAddr]; omega)
      slices_disjoint := Or.inl (Nat.le_of_eq hInData.symm)
      inSlice_eq := hInSliceEq }
  have hSim : SliceSim rfl rfl dataBase offSub sSaved.data subStart0 sSaved :=
    { pc_eq := by rw [pcSave]; rfl
      regs_eq := fun i => by
        have hBnd : i.val < sSaved.regs.size := by rw [sSaved.regs_size]; exact Nat.lt_succ_of_lt i.isLt
        have hiSub : i.val < subStart0.regs.size := by rw [subStart0.regs_size]; exact i.isLt
        rw [getElem?_pos subStart0.regs i.val hiSub]
        change sSaved.regs[i.val]? =
          some ((Array.ofFn (fun k : Fin 15 => sSaved.regs[k.val]?.getD 0))[i.val]'hiSub)
        rw [Array.getElem_ofFn, getElem?_pos sSaved.regs i.val hBnd]
        rfl
      dataSlice_eq := fun j hj => by
        change j < exitFamilySubWorkCap workCap at hj
        have hSubCap : dataBase + exitFamilySubWorkCap workCap ≤ workCap := hDataEnd
        have hBnd : dataBase + j < sSaved.data.size := by rw [szSave]; omega
        have hjSub : j < subStart0.data.size := by rw [subStart0.data_size]; exact hj
        rw [getElem?_pos subStart0.data j hjSub]
        change sSaved.data[dataBase + j]? =
          some ((Array.ofFn (fun k : Fin (exitFamilySubWorkCap workCap) =>
            sSaved.data[dataBase + k.val]?.getD 0))[j]'hjSub)
        rw [Array.getElem_ofFn, getElem?_pos sSaved.data (dataBase + j) hBnd]
        rfl
      frame_eq := fun _ _ => rfl }
  obtain ⟨bigT, subMem, mSub, hSubCost, hsSub, pcBig, hBigData, hFrBig,
      C, hSubFitR, hSubBits, hSealFit, hOccU, hDecU, hPlacedU⟩ :=
    run_exitSub_lifted (code := code) h100 input (hFlat d) incH covH rArcH
      hBuildIn hSubWorkFit rfl hCfg hSim (bodyRelocated_exitSub subCode h100)
      (by rw [hCodeSize]; change offSub + 4 * subCode.size < 397 + 4 * subCode.size
          simp only [offSub]; omega)
  have hSzBig : bigT.data.size = workCap := bigT.data_size
  have hFrBigLow : ∀ addr, addr < dataBase → bigT.data[addr]? = sSaved.data[addr]? :=
    fun a ha => hFrBig a (Or.inl ha)
  -- 7. `exitRestoreRegs`
  obtain ⟨sRest, hsRest, pcRest, hDataRest, regsRest⟩ :=
    exitRestoreRegs_steps (code := code) (input := input) h100 (sp_restoreRegs subCode h100)
      (by rw [hCodeSize]; first | (simp only [offPostSetup]; omega) | omega)
      (by rw [pcBig]; rfl) hSzBig regsE2
      (by rw [hFrBigLow statePtrAddr (by simp only [statePtrAddr]; omega),
        hKeepLowSave statePtrAddr (by simp only [statePtrAddr]; omega)]; exact hInv.statePtr)
      (fun k => by
        change bigT.data[stBase + k.val]? = _
        rw [hFrBigLow (stBase + k.val) (by have := k.isLt; omega)]
        exact hSavedSlots k)
      (show stBase + 11 ≤ workCap from by omega) hBits
  have hSzRest : sRest.data.size = workCap := by rw [hDataRest, hSzBig]
  have hIn0Rest : (sRest.data[inBase]?).map Fin.val = some n_d := by
    rw [hDataRest, hFrBigLow inBase hInLo]
    exact hIn0Saved
  have hIn2Rest : (sRest.data[inBase + 2]?).map Fin.val = some N_d := by
    rw [hDataRest, hFrBigLow (inBase + 2) (by omega)]
    exact hIn2Saved
  -- Bound `exitUsed + (19 * N_d + 6 * n_d)`
  let totalLen := 19 * N_d + 6 * n_d
  have hTotalLe47 : totalLen ≤ 47 * (S.childSlice d).length := by
    dsimp only [totalLen, N_d, n_d]
    have hc2 : 2 ≤ (S.childSlice d).length := by omega
    have hNL : ordResH.out.tables.next ≤ (S.childSlice d).length + 2 := by
      simpa only [N_d, n_d, Nat.add_assoc, Nat.add_comm 1 (S.childSlice d).length] using hNextLe
    omega
  have hUsedNextLe : exitUsed + totalLen ≤ exitUsedPrefix S (d.val + 1) := by
    have hSucc := exitUsedPrefix_succ S d.isLt
    rw [ite_eq_left hLarge] at hSucc
    change exitUsedPrefix S (d.val + 1) =
      exitUsedPrefix S d.val + 47 * (S.childSlice d).length at hSucc
    rw [hSucc]
    exact Nat.add_le_add hInv.usedLe hTotalLe47
  have hUsedNext48 : exitUsed + totalLen ≤ 48 * n := by
    rw [hn]; exact Nat.le_trans hUsedNextLe (exitUsedPrefix_le_48n S d.isLt)
  have hTotalCap : totalLen ≤ exitFamilySubWorkCap workCap := by
    change (33 * n_d + 2 * (S.ramQuotient d).arcCount + 80) ≤ exitFamilySubWorkCap workCap at hSubWorkFit
    change 19 * N_d + 6 * n_d ≤ exitFamilySubWorkCap workCap
    omega
  have hSubWorkTotal : dataBase + totalLen ≤ workCap := by
    change dataBase + exitFamilySubWorkCap workCap ≤ workCap at hDataEnd
    omega
  have hArenaBeforeState : ep0 + totalLen ≤ stBase := by
    change exitArenaBase loopBase n m + exitUsed + totalLen ≤ stBase
    omega
  have hArenaFit : ep0 + totalLen ≤ workCap := by omega
  have hLowRest (addr : Nat) (ha : addr < stBase) :
      sRest.data[addr]? = s₀.data[addr]? := by
    rw [hDataRest, hFrBigLow addr (by omega), hKeepLowSave addr ha]
  have hSt11Rest : (sRest.data[stBase + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) := by
    rw [hDataRest, hFrBigLow (stBase + 11) (by omega)]
    exact hSt11Save
  have hSt12Rest : (sRest.data[stBase + 12]?).map Fin.val = some (exitArenaBase loopBase n m) := by
    rw [hDataRest, hFrBigLow (stBase + 12) (by omega)]
    exact hSt12Save
  -- Set the owner pointers, copy the sealed exit summary, and advance.
  obtain ⟨sPostS, hsPostS, pcPostS, szPostS, regsPostS, rP11, rP12, rP13, rP15,
      hep0, hep1, hep2, hFrPostS⟩ :=
    exitPostSetup_steps (code := code) (input := input) h100 (sp_postSetup subCode h100)
      (by rw [hCodeSize]; simp only [offPostCopy]; omega)
      pcRest hSzRest regsRest hdQ hQn
      (by rw [hLowRest inPtrAddr (by simp only [inPtrAddr]; omega)]; exact hInv.inPtr)
      (by rw [hLowRest dataPtrAddr (by simp only [dataPtrAddr]; omega)]; exact hInv.dataPtr)
      (by rw [hLowRest statePtrAddr (by simp only [statePtrAddr]; omega)]; exact hInv.statePtr)
      hSt11Rest hSt12Rest hIn0Rest hIn2Rest hEndEP hArenaFit hSubWorkTotal
      (show inBase + 3 ≤ workCap from by omega) hBits
  obtain ⟨sEnd, hsPostC, pcEnd, szEnd, regsEnd, hCpEnd, hFrPostC⟩ :=
    exitPostCopyAndStep_steps (code := code) (input := input) (sp_postCopy subCode h100)
      (sp_postStep subCode h100)
      (by rw [hCodeSize]; simp only [offPostStep]; omega)
      pcPostS szPostS regsPostS rP11 rP12 rP13 rP15 hdQ hQn hArenaBeforeState hSubWorkTotal hBits
  change ∀ addr, (addr < exitPtrsBase loopBase n m + 3 * d.val ∨
      exitPtrsBase loopBase n m + 3 * d.val + 3 ≤ addr) →
      sPostS.data[addr]? = sRest.data[addr]? at hFrPostS
  change ∀ addr, (addr < ep0 ∨ ep0 + totalLen ≤ addr) →
      sEnd.data[addr]? = sPostS.data[addr]? at hFrPostC
  change ∀ k < totalLen, sEnd.data[ep0 + k]? = sPostS.data[dataBase + k]? at hCpEnd
  -- Combine Steps & Bound total steps
  have hAllSteps : Steps code input
      (19 + 28 + (6 * n_d + 14) + 4 * (6 * N_d + 14) + 3 * (6 * m_d + 16) + 23 + mSub + 24 + 43 +
        (6 * totalLen + 4)) s₀ sEnd := by
    as_aux_lemma =>
      have hT := hStagedCost.append (hsSub.append (hsRest.append (hsPostS.append hsPostC)))
      simpa only [Nat.add_assoc] using hT
  have hStepBound : 19 + 28 + (6 * n_d + 14) + 4 * (6 * N_d + 14) + 3 * (6 * m_d + 16) + 23 +
      mSub + 24 + 43 + (6 * totalLen + 4) ≤
      12300 * (2 * (S.childSlice d).length + m_d) * OracleContract.L n := by
    as_aux_lemma =>
      have hLPos : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
      have hLMon : OracleContract.L n_d ≤ OracleContract.L n := L_mono hNdLe
      have hc2 : 2 ≤ (S.childSlice d).length := by omega
      have hSum : (S.ramQuotient d).vertexCount + (S.ramQuotient d).arcCount + 1 ≤
          2 * (S.childSlice d).length + m_d := by
        change n_d + (S.ramQuotient d).arcCount + 1 ≤ _; rw [hmEq]; omega
      have hm1 : mSub ≤ 12000 * (2 * (S.childSlice d).length + m_d) * OracleContract.L n :=
        Nat.le_trans hSubCost (Nat.mul_le_mul (Nat.mul_le_mul_left 12000 hSum) hLMon)
      have hOvh : 19 + 28 + (6 * n_d + 14) + 4 * (6 * N_d + 14) + 3 * (6 * m_d + 16) + 23 + 24 + 43 +
          (6 * totalLen + 4) ≤ 300 * (2 * (S.childSlice d).length + m_d) * OracleContract.L n := by
        have hNL : N_d ≤ (S.childSlice d).length + 2 := by
          simpa only [n_d, Nat.add_assoc, Nat.add_comm 1 (S.childSlice d).length] using hNextLe
        have hLin : 19 + 28 + (6 * n_d + 14) + 4 * (6 * N_d + 14) + 3 * (6 * m_d + 16) + 23 + 24 + 43 +
            (6 * totalLen + 4) ≤ 300 * (2 * (S.childSlice d).length + m_d) := by
          dsimp only [totalLen, n_d]
          omega
        exact Nat.le_trans hLin (Nat.le_mul_of_pos_right _ hLPos)
      have hSumEq : 12000 * (2 * (S.childSlice d).length + m_d) * OracleContract.L n +
          300 * (2 * (S.childSlice d).length + m_d) * OracleContract.L n =
          12300 * (2 * (S.childSlice d).length + m_d) * OracleContract.L n := by
        rw [← Nat.add_mul, ← Nat.add_mul] <;> rfl
      omega
  -- Establish the frame for the unchanged registers and previously built records.
  have hPtrWriteEnd : exitPtrsBase loopBase n m + 3 * d.val + 3 ≤ exitArenaBase loopBase n m := by
    omega
  have hEpLo : exitArenaBase loopBase n m ≤ ep0 := by dsimp only [ep0]; omega
  have hEpHi : ep0 + totalLen ≤ stBase := hArenaBeforeState
  have hFrameEnd (addr : Nat) (ha : addr < stBase)
      (hp : addr < exitPtrsBase loopBase n m + 3 * d.val ∨
        exitPtrsBase loopBase n m + 3 * d.val + 3 ≤ addr)
      (hc : addr < ep0 ∨ ep0 + totalLen ≤ addr) : sEnd.data[addr]? = s₀.data[addr]? :=
    (hFrPostC addr hc).trans ((hFrPostS addr hp).trans (hLowRest addr ha))
  have hPrePtrsEnd (addr : Nat) (ha : addr < exitPtrsBase loopBase n m) :
      sEnd.data[addr]? = s₀.data[addr]? :=
    hFrameEnd addr (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  have hStKeepEnd (j : Nat) (hj1 : 11 ≤ j) (hj2 : j < 15) :
      sEnd.data[stBase + j]? = s₀.data[stBase + j]? := by
    rw [hFrPostC (stBase + j) (Or.inr (by omega)),
      hFrPostS (stBase + j) (Or.inr (by omega)), hDataRest,
      hFrBigLow (stBase + j) (by omega), hSavedKeep j hj1 hj2]
  have hNewPtrs (k : Nat) (hk : k < 3) :
      sEnd.data[exitPtrsBase loopBase n m + 3 * d.val + k]? =
      sPostS.data[exitPtrsBase loopBase n m + 3 * d.val + k]? :=
    hFrPostC _ (Or.inl (show exitPtrsBase loopBase n m + 3 * d.val + k < ep0 from by omega))
  have hSubMemEnd (k : Nat) (hk : k < totalLen) : sEnd.data[ep0 + k]? = subMem[k]? := by
    rw [hCpEnd k hk, hFrPostS (dataBase + k) (Or.inr (by omega)), hDataRest,
      hBigData k (show k < exitFamilySubWorkCap workCap from by omega)]
  have hfaHi' : ptrBase + wCols.wordCount ≤ forestArenaBase loopBase n m + forestUsed := hfaHi
  have hPackedEnd : ptrBase + wCols.wordCount ≤ exitPtrsBase loopBase n m :=
    Nat.le_trans hfaHi' hFAEnd
  have hPackedLo : 3 ≤ ptrBase := by
    change forestArenaBase loopBase n m ≤ ptrBase at hfaLo
    simp only [forestArenaBase, ownerForestPtrsBase, loopSortEntryBase, loopCursorBase,
      loopDegBase, loopSubStateBase, loopSubWorkBase, rawInputCap] at hfaLo
    omega
  have hPtrDataFit' : ptrBase + wCols.wordCount ≤ sEnd.data.size := by
    rw [szEnd]
    omega
  have hfp0' : (sEnd.data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase := by
    have hAddr : ownerForestPtrsBase loopBase n m + 6 * d.val < exitPtrsBase loopBase n m := by
      have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
      omega
    rw [hPrePtrsEnd (ownerForestPtrsBase loopBase n m + 6 * d.val) hAddr]
    exact hfp0_s0
  have hfp1' : (sEnd.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0))) := by
    have hAddr : ownerForestPtrsBase loopBase n m + 6 * d.val + 1 < exitPtrsBase loopBase n m := by
      have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
      omega
    rw [hPrePtrsEnd (ownerForestPtrsBase loopBase n m + 6 * d.val + 1) hAddr]
    exact hfp1_s0
  have hfp2' : (sEnd.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + (n_d + 1)) := by
    have hAddr : ownerForestPtrsBase loopBase n m + 6 * d.val + 2 < exitPtrsBase loopBase n m := by
      have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
      omega
    rw [hPrePtrsEnd (ownerForestPtrsBase loopBase n m + 6 * d.val + 2) hAddr]
    exact hfp2_s0
  have hfp3' : (sEnd.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + 2 * (n_d + 1)) := by
    have hAddr : ownerForestPtrsBase loopBase n m + 6 * d.val + 3 < exitPtrsBase loopBase n m := by
      have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
      omega
    rw [hPrePtrsEnd (ownerForestPtrsBase loopBase n m + 6 * d.val + 3) hAddr]
    exact hfp3_s0
  have hfp4' : (sEnd.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + 2 * (n_d + 1) + n_d) := by
    have hAddr : ownerForestPtrsBase loopBase n m + 6 * d.val + 4 < exitPtrsBase loopBase n m := by
      have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
      omega
    rw [hPrePtrsEnd (ownerForestPtrsBase loopBase n m + 6 * d.val + 4) hAddr]
    exact hfp4_s0
  have hfp5' : (sEnd.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val =
      some (ptrBase + (1 + 3 * (((wCols.dictionary[0]?).map Fin.val).getD 0)) + 2 * (n_d + 1) + n_d +
        wCols.entry.size) := by
    have hAddr : ownerForestPtrsBase loopBase n m + 6 * d.val + 5 < exitPtrsBase loopBase n m := by
      have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
      omega
    rw [hPrePtrsEnd (ownerForestPtrsBase loopBase n m + 6 * d.val + 5) hAddr]
    exact hfp5_s0
  have hPay' : ∀ k < wCols.wordCount,
      sEnd.data[ptrBase + k]? = (RamForestProgram.Finish.packedPayload wCols)[k]? := by
    intro k hk
    have hBefore : ptrBase + k < exitPtrsBase loopBase n m := by omega
    rw [hPrePtrsEnd (ptrBase + k) hBefore]
    exact hPay_s0 k hk
  have hep0' : (sEnd.data[exitPtrsBase loopBase n m + 3 * d.val]?).map Fin.val = some ep0 := by
    have h := hNewPtrs 0 (by decide)
    rw [Nat.add_zero] at h
    rw [h]
    exact hep0
  have hep1' : (sEnd.data[exitPtrsBase loopBase n m + 3 * d.val + 1]?).map Fin.val = some (ep0 + N_d) := by
    rw [hNewPtrs 1 (by decide)]
    exact hep1
  have hep2' : (sEnd.data[exitPtrsBase loopBase n m + 3 * d.val + 2]?).map Fin.val = some (ep0 + 19 * N_d) := by
    rw [hNewPtrs 2 (by decide)]
    exact hep2
  have hEAhi' : ep0 + 19 * N_d + 6 * n_d ≤ exitArenaBase loopBase n m + (exitUsed + totalLen) := by
    dsimp only [ep0, totalLen]; omega
  have hDataFit' : ep0 + 19 * N_d + 6 * n_d ≤ sEnd.data.size := by
    rw [szEnd]
    simpa only [totalLen, Nat.add_assoc] using hArenaFit
  have hArenaD : OwnerExitArenaAt S d (ownerForestPtrsBase loopBase n m)
      (forestArenaBase loopBase n m) forestUsed (exitPtrsBase loopBase n m)
      (exitArenaBase loopBase n m) (exitUsed + totalLen) sEnd.data := by
    as_aux_lemma =>
      exact ownerExitArenaAt_of_built S d hLarge (hFlat d) (ramQuotient_vertexCount_le S d)
        pH dataH sizeH rankH incH covH rArcH ordResH hWidth hfaLo hfaHi'
        hfp0' hfp1' hfp2' hfp3' hfp4' hfp5' hPay' hPtrDataFit'
        hep0' hep1' hep2' (by dsimp only [ep0]; omega) rfl (by omega) hEAhi' (by rw [szEnd]; exact hw) hDataFit'
        C hSubFitR hSubBits hSubMemEnd hOccU hDecU hSealFit hPlacedU
  have hKeepOldPtr (j : Fin dense.length) (hjLt : j.val < d.val) (k : Nat) (hk : k < 3) :
      sEnd.data[exitPtrsBase loopBase n m + 3 * j.val + k]? =
        s₀.data[exitPtrsBase loopBase n m + 3 * j.val + k]? := by
    let addr := exitPtrsBase loopBase n m + 3 * j.val + k
    change sEnd.data[addr]? = s₀.data[addr]?
    have hAddr : addr < exitPtrsBase loopBase n m + 3 * d.val := by dsimp only [addr]; omega
    exact hFrameEnd addr (by omega) (Or.inl hAddr) (Or.inl (by omega))
  have hKeepOldPayload (addr : Nat) (ha1 : exitArenaBase loopBase n m ≤ addr)
      (ha2 : addr < exitArenaBase loopBase n m + exitUsed) :
      sEnd.data[addr]? = s₀.data[addr]? := by
    have hAddr : addr < ep0 := ha2
    exact hFrameEnd addr (by omega) (Or.inr (by omega)) (Or.inl hAddr)
  have hInvEnd : ExitLoopInv S n m Q forestUsed (d.val + 1) (exitUsed + totalLen) sEnd :=
    hInv.advance hdQ hQn hForestLe szEnd regsEnd hUsedNextLe hPrePtrsEnd hStKeepEnd
      hKeepOldPtr hKeepOldPayload hArenaD
  exact ⟨sEnd, _, exitUsed + totalLen, hStepBound, hAllSteps, pcEnd, hInvEnd⟩

theorem run_exit_family_loop
    (h100 : 100 ≤ 2 ^ bits) (input : Input L16)
    {s₀ : State L16}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice s₀.data (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ d : Fin dense.length, (S.ramQuotient d).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
      (loopBaseOf workCap) Q forestUsed s₀)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds d hx).2.1)).symm)
      (s₀.data[emitBaseOf workCap + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ d : Fin dense.length,
      OwnerForestPackedRecordAt S d (loopBaseOf workCap) n m forestUsed s₀.data) :
    let code := exitFamilyLoopProgram hi hw h100
    ∃ (t : State L16) (states : List (State L16)) (steps exitUsed : Nat),
      steps ≤ 30000 * ((n + m + 1) * OracleContract.L n) ∧
      steps ≤ 30000 * ((n + m + 1) * OracleContract.L n ^ 2) ∧
      Steps code input (steps - 1) (Phase.initial s₀) t ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = inputCap + workCap + 16 ∧
      t.pc = code.size - 1 ∧
      exitUsed ≤ 48 * n ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m r.val Q (prefixTreeBase workCap)
        (ownerForestPtrsBase (loopBaseOf workCap) n m)
        (exitPtrsBase (loopBaseOf workCap) n m) (5 * n) t ∧
      SealedDisjointLayout n Q (prefixTreeBase workCap)
        (ownerForestPtrsBase (loopBaseOf workCap) n m)
        (forestArenaBase (loopBaseOf workCap) n m) forestUsed
        (exitPtrsBase (loopBaseOf workCap) n m)
        (exitArenaBase (loopBaseOf workCap) n m) exitUsed (5 * n) workCap ∧
      (∀ d : Fin dense.length,
        OwnerExitArenaAt S d (ownerForestPtrsBase (loopBaseOf workCap) n m)
          (forestArenaBase (loopBaseOf workCap) n m) forestUsed
          (exitPtrsBase (loopBaseOf workCap) n m)
          (exitArenaBase (loopBaseOf workCap) n m) exitUsed t.data) ∧
      (∀ addr, 3 ≤ addr → addr < exitPtrsBase (loopBaseOf workCap) n m →
        t.data[addr]? = s₀.data[addr]?) :=
  run_exit_family_loop_of_large
    (exitLarge_sub_steps (hi := hi) (hw := hw))
    h100 input S hn hm hQ hFlat hCap hBits hSz hRegs hForestLe hQStarts hArcs hRecs

end LoopInductionAndMain

end PaperB.RamExitFamilyLoop
