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

/-- Copies all three emitted arc columns while preserving the staged header
and forest columns. The destination columns are laid out contiguously. -/
theorem stageEmitColumns_steps (input : Input L16) (h100 : 100 ≤ 2 ^ bits)
    {sF4 : State L16}
    {n m root Q treeBase emitBase loopBase d exitUsed n_d N_d m_d qStart : Nat}
    (pcF4 : sF4.pc = offEmit 0) (szF4 : sF4.data.size = workCap)
    (regsF4 : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed sF4)
    (hMem0F4 : (sF4.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hMem1F4 : (sF4.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hW0_F4 : (sF4.data[exitSubWorkBase loopBase n m workCap]?).map Fin.val = some qStart)
    (hIn1F4 : (sF4.data[exitSubInBase loopBase n m + 1]?).map Fin.val = some m_d)
    (hR15F4 : (reg sF4 r15).val = exitSubInBase loopBase n m + 4 + n_d + 4 * N_d)
    (hmQStartBnd : qStart + m_d ≤ m)
    (hDisjEmitIn : emitBase + emitterWorkWords n m ≤ exitSubInBase loopBase n m)
    (hCopyEnd : exitSubInBase loopBase n m + 4 + n_d + 4 * N_d + 3 * m_d ≤
      exitSubWorkBase loopBase n m workCap)
    (hDataEnd : exitSubWorkBase loopBase n m workCap ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    let code := exitFamilyLoopProgram hi hw h100
    let orig := exitSubInBase loopBase n m + 4 + n_d + 4 * N_d
    ∃ t : State L16,
      Steps code input (3 * (6 * m_d + 16)) sF4 t ∧
      t.pc = offSave ∧ t.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed t ∧
      (∀ col : Fin 3, ∀ j < m_d, t.data[orig + col.val * m_d + j]? =
        sF4.data[emitBase + 3 * n + 1 + col.val * m + qStart + j]?) ∧
      (∀ addr, addr < orig → t.data[addr]? = sF4.data[addr]?) := by
  let subCode := exitSubProgram hw h100
  let code := exitFamilyLoopProgram hi hw h100
  have hCodeSize : code.size = 397 + 4 * subCode.size :=
    exitFamilyLoopCodeOf_size (hi := hi) (hw := hw) subCode h100
  let inBase := exitSubInBase loopBase n m
  let dataBase := exitSubWorkBase loopBase n m workCap
  change inBase + 4 + n_d + 4 * N_d + 3 * m_d ≤ dataBase at hCopyEnd
  change dataBase ≤ workCap at hDataEnd
  have hInGt : 2 < inBase := by simp only [inBase, exitSubInBase]; omega
  -- 4. `emit0..emit2`
  obtain ⟨sE0, hsE0, pcE0, szE0, regsE0, rE0_15, hCpE0, hFrE0⟩ :=
    copyFromEmitBlock_steps (code := code) (input := input) (base := offEmit 0) ⟨0, by decide⟩ (sp_emit0 subCode h100)
      (by rw [hCodeSize]; simp only [offEmit]; omega)
      pcF4 szF4 regsF4
      hMem0F4 hMem1F4 hW0_F4 hIn1F4 hR15F4 hmQStartBnd hDisjEmitIn
      (show inBase ≤ inBase + 4 + n_d + 4 * N_d from by omega)
      (show inBase + 4 + n_d + 4 * N_d + m_d ≤ workCap from by omega) hBits
  have hPreE0 (addr : Nat) (ha : addr < inBase + 4 + n_d + 4 * N_d) : sE0.data[addr]? = sF4.data[addr]? :=
    hFrE0 addr (Or.inl ha)
  have hKeepHeaderE0 (addr : Nat) (ha : addr < inBase + 4) : sE0.data[addr]? = sF4.data[addr]? :=
    hPreE0 addr (by omega)
  have hKeepBeforeE0 (addr : Nat) (ha : addr < inBase) : sE0.data[addr]? = sF4.data[addr]? :=
    hKeepHeaderE0 addr (by omega)
  have hR15E0 : (reg sE0 r15).val = inBase + 4 + n_d + 4 * N_d + m_d := by rw [rE0_15] <;> omega
  have hKeepWorkE0 (addr : Nat) (ha : dataBase ≤ addr) : sE0.data[addr]? = sF4.data[addr]? :=
    (hFrE0 addr (Or.inr (show inBase + 4 + n_d + 4 * N_d + m_d ≤ addr from by omega)))
  have hW0_E0 : (sE0.data[dataBase]?).map Fin.val = some (qStart) := by
    rw [hKeepWorkE0 dataBase (Nat.le_refl _)]
    exact hW0_F4
  have hMem0E0 : (sE0.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeE0 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0F4
  have hMem1E0 : (sE0.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeE0 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1F4
  have hIn1E0 : (sE0.data[inBase + 1]?).map Fin.val = some m_d := by
    rw [hKeepHeaderE0 (inBase + 1) (by omega)]
    exact hIn1F4
  obtain ⟨sE1, hsE1, pcE1, szE1, regsE1, rE1_15, hCpE1, hFrE1⟩ :=
    copyFromEmitBlock_steps (code := code) (input := input) (base := offEmit 1) ⟨1, by decide⟩ (sp_emit1 subCode h100)
      (by rw [hCodeSize]; simp only [offEmit]; omega)
      (by rw [pcE0]; change offEmit 0 + 21 = offEmit 1; rfl) szE0 regsE0
      hMem0E0 hMem1E0 hW0_E0 hIn1E0 hR15E0 hmQStartBnd hDisjEmitIn
      (show inBase ≤ inBase + 4 + n_d + 4 * N_d + m_d from by omega)
      (show inBase + 4 + n_d + 4 * N_d + m_d + m_d ≤ workCap from by omega) hBits
  have hPreE1 (addr : Nat) (ha : addr < inBase + 4 + n_d + 4 * N_d + m_d) : sE1.data[addr]? = sE0.data[addr]? :=
    hFrE1 addr (Or.inl ha)
  have hKeepHeaderE1 (addr : Nat) (ha : addr < inBase + 4) : sE1.data[addr]? = sF4.data[addr]? :=
    (hPreE1 addr (by omega)).trans (hKeepHeaderE0 addr ha)
  have hKeepBeforeE1 (addr : Nat) (ha : addr < inBase) : sE1.data[addr]? = sF4.data[addr]? :=
    hKeepHeaderE1 addr (by omega)
  have hR15E1 : (reg sE1 r15).val = inBase + 4 + n_d + 4 * N_d + 2 * m_d := by rw [rE1_15] <;> omega
  have hKeepWorkE1 (addr : Nat) (ha : dataBase ≤ addr) : sE1.data[addr]? = sF4.data[addr]? :=
    (hFrE1 addr (Or.inr (show inBase + 4 + n_d + 4 * N_d + m_d + m_d ≤ addr from by omega))).trans (hKeepWorkE0 addr ha)
  have hW0_E1 : (sE1.data[dataBase]?).map Fin.val = some (qStart) := by
    rw [hKeepWorkE1 dataBase (Nat.le_refl _)]
    exact hW0_F4
  have hMem0E1 : (sE1.data[inPtrAddr]?).map Fin.val = some inBase := by
    rw [hKeepBeforeE1 inPtrAddr (by simp only [inPtrAddr]; omega)]
    exact hMem0F4
  have hMem1E1 : (sE1.data[dataPtrAddr]?).map Fin.val = some dataBase := by
    rw [hKeepBeforeE1 dataPtrAddr (by simp only [dataPtrAddr]; omega)]
    exact hMem1F4
  have hIn1E1 : (sE1.data[inBase + 1]?).map Fin.val = some m_d := by
    rw [hKeepHeaderE1 (inBase + 1) (by omega)]
    exact hIn1F4
  obtain ⟨sE2, hsE2, pcE2, szE2, regsE2, rE2_15, hCpE2, hFrE2⟩ :=
    copyFromEmitBlock_steps (code := code) (input := input) (base := offEmit 2) ⟨2, by decide⟩ (sp_emit2 subCode h100)
      (by rw [hCodeSize]; simp only [offEmit]; omega)
      (by rw [pcE1]; change offEmit 1 + 21 = offEmit 2; rfl) szE1 regsE1
      hMem0E1 hMem1E1 hW0_E1 hIn1E1 hR15E1 hmQStartBnd hDisjEmitIn
      (show inBase ≤ inBase + 4 + n_d + 4 * N_d + 2 * m_d from by omega)
      (show inBase + 4 + n_d + 4 * N_d + 2 * m_d + m_d ≤ workCap from by omega) hBits
  have hPreE2 (addr : Nat) (ha : addr < inBase + 4 + n_d + 4 * N_d + 2 * m_d) : sE2.data[addr]? = sE1.data[addr]? :=
    hFrE2 addr (Or.inl ha)
  have hSteps : Steps code input (3 * (6 * m_d + 16)) sF4 sE2 := by
    have h := hsE0.append (hsE1.append hsE2)
    simpa only [show (6 * m_d + 16) + ((6 * m_d + 16) + (6 * m_d + 16)) =
      3 * (6 * m_d + 16) by omega] using h
  refine ⟨sE2, hSteps, pcE2, szE2, regsE2, ?_, ?_⟩
  · intro col j hj
    have hc : col.val = 0 ∨ col.val = 1 ∨ col.val = 2 := by have := col.isLt; omega
    let orig := inBase + 4 + n_d + 4 * N_d
    change sE2.data[orig + col.val * m_d + j]? = _
    rcases hc with h0 | h1 | h2
    · rw [h0, Nat.zero_mul, Nat.add_zero,
        hPreE2 (orig + j) (by dsimp only [orig]; omega),
        hPreE1 (orig + j) (by dsimp only [orig]; omega)]
      simpa only [Nat.zero_mul, Nat.add_zero] using hCpE0 j hj
    · rw [h1, Nat.one_mul,
        hPreE2 (orig + m_d + j) (by dsimp only [orig]; omega), hCpE1 j hj]
      have hSrc : emitBase + 3 * n + 1 + m + qStart + j < inBase := by
        simp only [emitterWorkWords] at hDisjEmitIn
        omega
      simpa only [Fin.val_mk, Nat.one_mul] using
        hPreE0 (emitBase + 3 * n + 1 + m + qStart + j) (by omega)
    · rw [h2, hCpE2 j hj]
      have hSrc : emitBase + 3 * n + 1 + 2 * m + qStart + j < inBase := by
        simp only [emitterWorkWords] at hDisjEmitIn
        omega
      let src := emitBase + 3 * n + 1 + 2 * m + qStart + j
      change sE1.data[src]? = sF4.data[src]?
      exact (hPreE1 src (by omega)).trans (hPreE0 src (by omega))
  · intro addr ha
    change addr < inBase + 4 + n_d + 4 * N_d at ha
    exact (hPreE2 addr (by omega)).trans ((hPreE1 addr (by omega)).trans (hPreE0 addr ha))

end PaperB.RamExitFamilyLoop
