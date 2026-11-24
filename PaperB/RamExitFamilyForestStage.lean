module

public import PaperB.RamExitFamilyCopies
public import PaperB.RamExitFamilyProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxRecDepth 1024

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter prefixTreeBase)
open PaperB.ForestHead (Vertex)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex)
open PaperB.ForestSlimIndex
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
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


variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

/-- Copies the five forest columns into the builder input bank. The source
records and both the earlier header and the separate work bank are preserved. -/
theorem stageForestColumns_steps (input : Input L16) (h100 : 100 ≤ 2 ^ bits)
    {sB : State L16}
    {n m root Q treeBase emitBase loopBase d exitUsed n_d N_d : Nat}
    {fpPtrBase fp1Val fp2Val fp3Val fp4Val fp5Val : Nat}
    (pcB : sB.pc = offFp 0) (szB : sB.data.size = workCap)
    (regsB : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed sB)
    (hMem0B : (sB.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hMem1B : (sB.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hW1B : (sB.data[exitSubWorkBase loopBase n m workCap + 1]?).map Fin.val = some fpPtrBase)
    (hIn0B : (sB.data[exitSubInBase loopBase n m]?).map Fin.val = some n_d)
    (hIn2B' : (sB.data[exitSubInBase loopBase n m + 2]?).map Fin.val = some N_d)
    (rB15 : (reg sB r15).val = exitSubInBase loopBase n m + 4)
    (hFpTableFit : fpPtrBase + 5 < exitSubInBase loopBase n m)
    (hfp1B : (sB.data[fpPtrBase + 1]?).map Fin.val = some fp1Val)
    (hfp2B : (sB.data[fpPtrBase + 2]?).map Fin.val = some fp2Val)
    (hfp3B : (sB.data[fpPtrBase + 3]?).map Fin.val = some fp3Val)
    (hfp4B : (sB.data[fpPtrBase + 4]?).map Fin.val = some fp4Val)
    (hfp5B : (sB.data[fpPtrBase + 5]?).map Fin.val = some fp5Val)
    (hSrc1 : fp1Val + N_d ≤ exitSubInBase loopBase n m)
    (hSrc2 : fp2Val + N_d ≤ exitSubInBase loopBase n m)
    (hSrc3 : fp3Val + n_d ≤ exitSubInBase loopBase n m)
    (hSrc4 : fp4Val + N_d ≤ exitSubInBase loopBase n m)
    (hSrc5 : fp5Val + N_d ≤ exitSubInBase loopBase n m)
    (hCopyEnd : exitSubInBase loopBase n m + 4 + n_d + 4 * N_d ≤
      exitSubWorkBase loopBase n m workCap)
    (hDataEnd : exitSubWorkBase loopBase n m workCap ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    let code := exitFamilyLoopProgram hi hw h100
    let orig := exitSubInBase loopBase n m + 4
    ∃ t : State L16,
      Steps code input ((6 * n_d + 14) + 4 * (6 * N_d + 14)) sB t ∧
      t.pc = offFp 4 + 19 ∧ t.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed t ∧
      (reg t r15).val = orig + n_d + 4 * N_d ∧
      (∀ j < n_d, t.data[orig + j]? = sB.data[fp3Val + j]?) ∧
      (∀ j < N_d, t.data[orig + n_d + j]? = sB.data[fp1Val + j]?) ∧
      (∀ j < N_d, t.data[orig + n_d + N_d + j]? = sB.data[fp2Val + j]?) ∧
      (∀ j < N_d, t.data[orig + n_d + 2 * N_d + j]? = sB.data[fp4Val + j]?) ∧
      (∀ j < N_d, t.data[orig + n_d + 3 * N_d + j]? = sB.data[fp5Val + j]?) ∧
      (∀ addr, addr < orig → t.data[addr]? = sB.data[addr]?) ∧
      (∀ addr, exitSubWorkBase loopBase n m workCap ≤ addr → t.data[addr]? = sB.data[addr]?) := by
  let subCode := exitSubProgram hw h100
  let code := exitFamilyLoopProgram hi hw h100
  have hCodeSize : code.size = 397 + 4 * subCode.size :=
    exitFamilyLoopCodeOf_size (hi := hi) (hw := hw) subCode h100
  let inBase := exitSubInBase loopBase n m
  let dataBase := exitSubWorkBase loopBase n m workCap
  change inBase + 4 + n_d + 4 * N_d ≤ dataBase at hCopyEnd
  change dataBase ≤ workCap at hDataEnd
  change fpPtrBase + 5 < inBase at hFpTableFit
  -- Copy the five forest columns into one contiguous input bank.
  have hInGt : 2 < inBase := by simp only [inBase, exitSubInBase]; omega
  obtain ⟨sF0, hsF0, pcF0, szF0, regsF0, rF0_15, hCpF0, hFrF0⟩ :=
    copyFromFpBlock_steps (code := code) (input := input) h100 (base := offFp 0)
      (idx := 3) (lenIdx := 0) (by decide) (by decide)
      (sp_fp0 subCode h100) (by rw [hCodeSize]; simp only [offFp]; omega)
      pcB szB regsB
      hMem0B hMem1B hW1B hfp3B hIn0B rB15
      (show fp3Val + n_d ≤ inBase from by omega)
      (show inBase ≤ inBase + 4 from by omega)
      (show inBase + 4 + n_d ≤ workCap from by omega) hBits
  have hR15F0 : (reg sF0 r15).val = inBase + 4 + n_d := by rw [rF0_15] <;> omega
  have hPreF0 (addr : Nat) (ha : addr < inBase + 4) : sF0.data[addr]? = sB.data[addr]? :=
    hFrF0 addr (Or.inl ha)
  have hKeepHeaderF0 (addr : Nat) (ha : addr < inBase + 4) : sF0.data[addr]? = sB.data[addr]? :=
    hPreF0 addr ha
  have hKeepBeforeF0 (addr : Nat) (ha : addr < inBase) : sF0.data[addr]? = sB.data[addr]? :=
    hKeepHeaderF0 addr (by omega)
  have hKeepWorkF0 (addr : Nat) (ha : dataBase ≤ addr) : sF0.data[addr]? = sB.data[addr]? := by
    have h := hFrF0 addr (Or.inr (show inBase + 4 + n_d ≤ addr from by omega))
    exact h
  have hW1_F0 : (sF0.data[dataBase + 1]?).map Fin.val = some fpPtrBase := by
    rw [hKeepWorkF0 (dataBase + 1) (by omega)]
    exact hW1B
  have hFp1Read : (sF0.data[fpPtrBase + 1]?).map Fin.val = some fp1Val := by
    rw [hKeepBeforeF0 (fpPtrBase + 1) (by omega)]
    exact hfp1B
  have hPtr0F1 : (sF0.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeF0 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0B
  have hPtr1F1 : (sF0.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeF0 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1B
  have hLenF1 : (sF0.data[inBase + 2]?).map Fin.val = some N_d := by
    rw [hKeepHeaderF0 (inBase + 2) (by omega)]
    exact hIn2B'
  obtain ⟨sF1, hsF1, pcF1, szF1, regsF1, rF1_15, hCpF1, hFrF1⟩ :=
    copyFromFpBlock_steps (code := code) (input := input) h100 (base := offFp 1)
      (idx := 1) (lenIdx := 2) (by decide) (by decide)
      (sp_fp1 subCode h100) (by rw [hCodeSize]; simp only [offFp]; omega)
      (by rw [pcF0]; change offFp 0 + 19 = offFp 1; rfl) szF0 regsF0
      hPtr0F1 hPtr1F1 hW1_F0 hFp1Read hLenF1 hR15F0
      (show fp1Val + N_d ≤ inBase from by omega)
      (show inBase ≤ inBase + 4 + n_d from by omega)
      (show inBase + 4 + n_d + N_d ≤ workCap from by omega) hBits
  have hR15F1 : (reg sF1 r15).val = inBase + 4 + n_d + N_d := by rw [rF1_15] <;> omega
  have hPreF1 (addr : Nat) (ha : addr < inBase + 4 + n_d) : sF1.data[addr]? = sF0.data[addr]? :=
    hFrF1 addr (Or.inl ha)
  have hKeepHeaderF1 (addr : Nat) (ha : addr < inBase + 4) : sF1.data[addr]? = sB.data[addr]? :=
    (hPreF1 addr (by omega)).trans (hKeepHeaderF0 addr ha)
  have hKeepBeforeF1 (addr : Nat) (ha : addr < inBase) : sF1.data[addr]? = sB.data[addr]? :=
    hKeepHeaderF1 addr (by omega)
  have hKeepWorkF1 (addr : Nat) (ha : dataBase ≤ addr) : sF1.data[addr]? = sB.data[addr]? := by
    have h := hFrF1 addr (Or.inr (show inBase + 4 + n_d + N_d ≤ addr from by omega))
    exact h.trans (hKeepWorkF0 addr ha)
  have hW1_F1 : (sF1.data[dataBase + 1]?).map Fin.val = some fpPtrBase := by
    rw [hKeepWorkF1 (dataBase + 1) (by omega)]
    exact hW1B
  have hFp2Read : (sF1.data[fpPtrBase + 2]?).map Fin.val = some fp2Val := by
    rw [hKeepBeforeF1 (fpPtrBase + 2) (by omega)]
    exact hfp2B
  have hPtr0F2 : (sF1.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeF1 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0B
  have hPtr1F2 : (sF1.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeF1 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1B
  have hLenF2 : (sF1.data[inBase + 2]?).map Fin.val = some N_d := by
    rw [hKeepHeaderF1 (inBase + 2) (by omega)]
    exact hIn2B'
  obtain ⟨sF2, hsF2, pcF2, szF2, regsF2, rF2_15, hCpF2, hFrF2⟩ :=
    copyFromFpBlock_steps (code := code) (input := input) h100 (base := offFp 2)
      (idx := 2) (lenIdx := 2) (by decide) (by decide)
      (sp_fp2 subCode h100) (by rw [hCodeSize]; simp only [offFp]; omega)
      (by rw [pcF1]; change offFp 1 + 19 = offFp 2; rfl) szF1 regsF1
      hPtr0F2 hPtr1F2 hW1_F1 hFp2Read hLenF2 hR15F1
      (show fp2Val + N_d ≤ inBase from by omega)
      (show inBase ≤ inBase + 4 + n_d + N_d from by omega)
      (show inBase + 4 + n_d + N_d + N_d ≤ workCap from by omega) hBits
  have hR15F2 : (reg sF2 r15).val = inBase + 4 + n_d + 2 * N_d := by rw [rF2_15] <;> omega
  have hPreF2 (addr : Nat) (ha : addr < inBase + 4 + n_d + N_d) : sF2.data[addr]? = sF1.data[addr]? :=
    hFrF2 addr (Or.inl ha)
  have hKeepHeaderF2 (addr : Nat) (ha : addr < inBase + 4) : sF2.data[addr]? = sB.data[addr]? :=
    (hPreF2 addr (by omega)).trans (hKeepHeaderF1 addr ha)
  have hKeepBeforeF2 (addr : Nat) (ha : addr < inBase) : sF2.data[addr]? = sB.data[addr]? :=
    hKeepHeaderF2 addr (by omega)
  have hKeepWorkF2 (addr : Nat) (ha : dataBase ≤ addr) : sF2.data[addr]? = sB.data[addr]? := by
    have h := hFrF2 addr (Or.inr (show inBase + 4 + n_d + N_d + N_d ≤ addr from by omega))
    exact h.trans (hKeepWorkF1 addr ha)
  have hW1_F2 : (sF2.data[dataBase + 1]?).map Fin.val = some fpPtrBase := by
    rw [hKeepWorkF2 (dataBase + 1) (by omega)]
    exact hW1B
  have hFp3Read : (sF2.data[fpPtrBase + 4]?).map Fin.val = some fp4Val := by
    rw [hKeepBeforeF2 (fpPtrBase + 4) (by omega)]
    exact hfp4B
  have hPtr0F3 : (sF2.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeF2 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0B
  have hPtr1F3 : (sF2.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeF2 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1B
  have hLenF3 : (sF2.data[inBase + 2]?).map Fin.val = some N_d := by
    rw [hKeepHeaderF2 (inBase + 2) (by omega)]
    exact hIn2B'
  obtain ⟨sF3, hsF3, pcF3, szF3, regsF3, rF3_15, hCpF3, hFrF3⟩ :=
    copyFromFpBlock_steps (code := code) (input := input) h100 (base := offFp 3)
      (idx := 4) (lenIdx := 2) (by decide) (by decide)
      (sp_fp3 subCode h100) (by rw [hCodeSize]; simp only [offFp]; omega)
      (by rw [pcF2]; change offFp 2 + 19 = offFp 3; rfl) szF2 regsF2
      hPtr0F3 hPtr1F3 hW1_F2 hFp3Read hLenF3 hR15F2
      (show fp4Val + N_d ≤ inBase from by omega)
      (show inBase ≤ inBase + 4 + n_d + 2 * N_d from by omega)
      (show inBase + 4 + n_d + 2 * N_d + N_d ≤ workCap from by omega) hBits
  have hR15F3 : (reg sF3 r15).val = inBase + 4 + n_d + 3 * N_d := by rw [rF3_15] <;> omega
  have hPreF3 (addr : Nat) (ha : addr < inBase + 4 + n_d + 2 * N_d) : sF3.data[addr]? = sF2.data[addr]? :=
    hFrF3 addr (Or.inl ha)
  have hKeepHeaderF3 (addr : Nat) (ha : addr < inBase + 4) : sF3.data[addr]? = sB.data[addr]? :=
    (hPreF3 addr (by omega)).trans (hKeepHeaderF2 addr ha)
  have hKeepBeforeF3 (addr : Nat) (ha : addr < inBase) : sF3.data[addr]? = sB.data[addr]? :=
    hKeepHeaderF3 addr (by omega)
  have hKeepWorkF3 (addr : Nat) (ha : dataBase ≤ addr) : sF3.data[addr]? = sB.data[addr]? := by
    have h := hFrF3 addr (Or.inr (show inBase + 4 + n_d + 2 * N_d + N_d ≤ addr from by omega))
    exact h.trans (hKeepWorkF2 addr ha)
  have hW1_F3 : (sF3.data[dataBase + 1]?).map Fin.val = some fpPtrBase := by
    rw [hKeepWorkF3 (dataBase + 1) (by omega)]
    exact hW1B
  have hFp4Read : (sF3.data[fpPtrBase + 5]?).map Fin.val = some fp5Val := by
    rw [hKeepBeforeF3 (fpPtrBase + 5) (by omega)]
    exact hfp5B
  have hPtr0F4 : (sF3.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeF3 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0B
  have hPtr1F4 : (sF3.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeF3 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1B
  have hLenF4 : (sF3.data[inBase + 2]?).map Fin.val = some N_d := by
    rw [hKeepHeaderF3 (inBase + 2) (by omega)]
    exact hIn2B'
  obtain ⟨sF4, hsF4, pcF4, szF4, regsF4, rF4_15, hCpF4, hFrF4⟩ :=
    copyFromFpBlock_steps (code := code) (input := input) h100 (base := offFp 4)
      (idx := 5) (lenIdx := 2) (by decide) (by decide)
      (sp_fp4 subCode h100) (by rw [hCodeSize]; simp only [offFp]; omega)
      (by rw [pcF3]; change offFp 3 + 19 = offFp 4; rfl) szF3 regsF3
      hPtr0F4 hPtr1F4 hW1_F3 hFp4Read hLenF4 hR15F3
      (show fp5Val + N_d ≤ inBase from by omega)
      (show inBase ≤ inBase + 4 + n_d + 3 * N_d from by omega)
      (show inBase + 4 + n_d + 3 * N_d + N_d ≤ workCap from by omega) hBits
  have hR15F4 : (reg sF4 r15).val = inBase + 4 + n_d + 4 * N_d := by rw [rF4_15] <;> omega
  have hPreF4 (addr : Nat) (ha : addr < inBase + 4 + n_d + 3 * N_d) : sF4.data[addr]? = sF3.data[addr]? :=
    hFrF4 addr (Or.inl ha)
  have hKeepHeaderF4 (addr : Nat) (ha : addr < inBase + 4) : sF4.data[addr]? = sB.data[addr]? :=
    (hPreF4 addr (by omega)).trans (hKeepHeaderF3 addr ha)
  have hKeepBeforeF4 (addr : Nat) (ha : addr < inBase) : sF4.data[addr]? = sB.data[addr]? :=
    hKeepHeaderF4 addr (by omega)
  have hKeepWorkF4 (addr : Nat) (ha : dataBase ≤ addr) : sF4.data[addr]? = sB.data[addr]? := by
    have h := hFrF4 addr (Or.inr (show inBase + 4 + n_d + 3 * N_d + N_d ≤ addr from by omega))
    exact h.trans (hKeepWorkF3 addr ha)
  have hSteps : Steps code input ((6 * n_d + 14) + 4 * (6 * N_d + 14)) sB sF4 := by
    have h := hsF0.append (hsF1.append (hsF2.append (hsF3.append hsF4)))
    have hCost : (6 * n_d + 14) + ((6 * N_d + 14) + ((6 * N_d + 14) +
        ((6 * N_d + 14) + (6 * N_d + 14)))) =
        (6 * n_d + 14) + 4 * (6 * N_d + 14) := by omega
    rw [hCost] at h
    exact h
  refine ⟨sF4, hSteps, pcF4, szF4, regsF4, hR15F4, ?_, ?_, ?_, ?_, ?_,
    hKeepHeaderF4, hKeepWorkF4⟩
  · intro j hj
    change sF4.data[inBase + 4 + j]? = _
    rw [hPreF4 (inBase + 4 + j) (by omega),
      hPreF3 (inBase + 4 + j) (by omega),
      hPreF2 (inBase + 4 + j) (by omega),
      hPreF1 (inBase + 4 + j) (by omega),
      hCpF0 j hj]
  · intro j hj
    change sF4.data[inBase + 4 + n_d + j]? = _
    rw [hPreF4 (inBase + 4 + n_d + j) (by omega),
      hPreF3 (inBase + 4 + n_d + j) (by omega),
      hPreF2 (inBase + 4 + n_d + j) (by omega),
      hCpF1 j hj]
    exact hKeepBeforeF0 (fp1Val + j) (by
      have hSrc : fp1Val + N_d ≤ inBase := hSrc1
      omega)
  · intro j hj
    change sF4.data[inBase + 4 + n_d + N_d + j]? = _
    rw [hPreF4 (inBase + 4 + n_d + N_d + j) (by omega),
      hPreF3 (inBase + 4 + n_d + N_d + j) (by omega),
      hCpF2 j hj]
    exact hKeepBeforeF1 (fp2Val + j) (by
      have hSrc : fp2Val + N_d ≤ inBase := hSrc2
      omega)
  · intro j hj
    change sF4.data[inBase + 4 + n_d + 2 * N_d + j]? = _
    rw [hPreF4 (inBase + 4 + n_d + 2 * N_d + j) (by omega),
      hCpF3 j hj]
    exact hKeepBeforeF2 (fp4Val + j) (by
      have hSrc : fp4Val + N_d ≤ inBase := hSrc4
      omega)
  · intro j hj
    change sF4.data[inBase + 4 + n_d + 3 * N_d + j]? = _
    rw [hCpF4 j hj]
    exact hKeepBeforeF3 (fp5Val + j) (by
      have hSrc : fp5Val + N_d ≤ inBase := hSrc5
      omega)

end PaperB.RamExitFamilyLoop
