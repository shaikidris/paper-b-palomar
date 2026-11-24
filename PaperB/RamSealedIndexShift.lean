module

public import PaperB.RamSealedPackerPrimitives

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! The last packing phase moves the retained index to the front of the RAM data array. -/

namespace PaperB.RamSealedPacker

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub add_no_wrap)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.ForestHead
open PaperB.EX16Assembly
open PaperB.DenseQuotientRows
open PaperB.DenseOriginalQuotient
open PaperB.EX44.ActualOnlineOracle
open PaperB.RamQuotientEmitter
open PaperB.OracleSealedIndexLayout
open PaperB.RamOracleQuery
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.ForestSlimIndex
open PaperB.RetainedProperLoss
open PaperB.RamDagReach
open PaperB.RamStaticReaderBridge

section ExecutionProofs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

theorem run_shiftToZeroPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase totalWords : Nat}
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hTot : (s₀.data[sealedBase + hdrTotalWords]?).map Fin.val = some totalWords)
    (hPosBase : 0 < sealedBase) (hFit : sealedBase + totalWords ≤ workCap) :
    let ph := shiftToZeroPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32
    ∃ (t : State L16) (steps : Nat),
      steps = 6 * totalWords + 8 ∧
      run ph.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      (∀ j < totalWords, t.data[j]? = s₀.data[sealedBase + j]?) := by
  intro ph
  let code := ph.code
  have hCodeSz : code.size = 13 := shiftToZeroCode_size h32
  have hTotIdx : sealedBase + hdrTotalWords < workCap := by
    rw [← hSz]
    if h : sealedBase + hdrTotalWords < s₀.data.size then exact h
    else rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hTot; cases hTot
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  obtain ⟨s1, hs1, pc1, r1_13, p1, d1⟩ := step_imm16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc]; rfl) (by rw [hCodeSz]; omega)
  obtain ⟨s2, hs2, pc2, r2_13, p2, d2⟩ := step_add16 (code := code) (input := input) (by rw [pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r2_13v : (reg s2 r13).val = sealedBase + hdrTotalWords := by
    have h9_1 : (reg s1 r9).val = sealedBase := by rw [p1 r9 (by decide)]; exact hRegs.sealedBaseVal
    rw [r2_13, add_no_wrap _ _ (by rw [h9_1, r1_13]; dsimp only; omega), h9_1, r1_13]
  have hd2 : s2.data = s₀.data := by rw [d2, d1]; rfl
  have hLTot : ∃ wT, s2.data[(reg s2 r13).val]? = some wT ∧ wT.val = totalWords := by
    rw [hd2, r2_13v]
    cases hG : s₀.data[sealedBase + hdrTotalWords]? with
    | none => rw [hG] at hTot; cases hTot
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hTot; exact ⟨w, rfl, hTot⟩
  obtain ⟨wT, hwT, hwTV⟩ := hLTot
  obtain ⟨s3, hs3, pc3, r3_13, p3, d3⟩ := step_loadData16 (code := code) (input := input) (by rw [pc2, pc1, h0pc]; rfl) hwT (by rw [pc2, pc1, h0pc, hCodeSz]; omega)
  obtain ⟨s4, hs4, pc4, r4_11, p4, d4⟩ := step_mov16 (code := code) (input := input) (by rw [pc3, pc2, pc1, h0pc]; rfl) (by rw [pc3, pc2, pc1, h0pc, hCodeSz]; omega)
  obtain ⟨s5, hs5, pc5, r5_12, p5, d5⟩ := step_mov16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [pc4, pc3, pc2, pc1, h0pc, hCodeSz]; omega)
  obtain ⟨s6, hs6, pc6, r6_13, p6, d6⟩ := step_add16 (code := code) (input := input) (by rw [pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [pc5, pc4, pc3, pc2, pc1, h0pc, hCodeSz]; omega)
  have hr5_9 : (reg s5 r9).val = sealedBase := by
    rw [p5 r9 (by decide), p4 r9 (by decide), p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide)]; exact hRegs.sealedBaseVal
  have hr5_13 : (reg s5 r13).val = totalWords := by
    rw [p5 r13 (by decide), p4 r13 (by decide), r3_13, hwTV]
  have r6_13v : (reg s6 r13).val = sealedBase + totalWords := by
    rw [r6_13, add_no_wrap _ _ (by rw [hr5_9, hr5_13]; omega), hr5_9, hr5_13]
  have hPl : SlicePlaced code 6 (copyLoopCode 6 12) := copyLoop_slicePlaced rfl rfl rfl rfl rfl rfl
  obtain ⟨t, kLoop, hkLoop, hLoop, pct, tsz, _, _, _, _, htcp, _⟩ :=
    run_copyLoop (input := input) hPl (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits
      hFit (by omega) (Or.inr (Or.inr hPosBase))
      (by rw [pc6, pc5, pc4, pc3, pc2, pc1, h0pc]) (by rw [d6, d5, d4, d3, d2, d1]; exact hSz)
      (by rw [p6 rOne (by decide), p5 rOne (by decide), p4 rOne (by decide), p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hRegs.consts.one)
      (by rw [p6 r11 (by decide), p5 r11 (by decide), r4_11, p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide)]; exact hRegs.sealedBaseVal)
      (by rw [p6 r12 (by decide), r5_12, p4 rZero (by decide), p3 rZero (by decide), p2 rZero (by decide), p1 rZero (by decide)]; exact hRegs.consts.zero)
      r6_13v
  have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [pct]; rfl)
  have hRun := ((Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (step1 hs6)))))).append hLoop).halts hHalt
  have hTotS : 6 + kLoop + 1 = 6 * totalWords + 8 := by omega
  rw [hTotS] at hRun
  refine ⟨t, 6 * totalWords + 8, rfl, hRun, tsz, fun j hj => ?_⟩
  have hj0 := htcp j hj
  rw [Nat.zero_add] at hj0
  rw [hj0, d6, d5, d4, d3, d2, d1]; rfl

end ExecutionProofs

end PaperB.RamSealedPacker
