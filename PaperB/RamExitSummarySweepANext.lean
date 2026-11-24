module

public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

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

theorem step4A_nextArc_spec {code : Program DomL} {input : Input DomL}
    (loopPc n m N arcPtr : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code loopPc (step4ALoopInstrs (bits := bits) loopPc h100))
    (hSz : loopPc + 406 < code.size)
    (hNLe : N ≤ n + 1) (hLarge : 3 ≤ n)
    (hWork : exitWorkCap n m ≤ workCap) (hWorkFit : workCap ≤ 2 ^ bits)
    (hArcLt : arcPtr < m)
    (st : State DomL) (hpc : st.pc = loopPc + 398)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hM : (reg st rMeta).val = metaArrBase n m N)
    (hPtr : (st.data[metaArrBase n m N + mIdxArcPtr]?).map Fin.val = some arcPtr) :
    ∃ t : State DomL, Steps code input 8 st t ∧ t.pc = loopPc ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaArrBase n m N ∧
      (t.data[metaArrBase n m N + mIdxArcPtr]?).map Fin.val = some (arcPtr + 1) ∧
      (∀ j, j ≠ metaArrBase n m N + mIdxArcPtr → t.data[j]? = st.data[j]?) := by
  have hMetaEq := metaArrBase_eq n m N
  have hArcOffset : mIdxArcPtr < 64 := by decide
  have hBoundMeta : metaArrBase n m N + 64 ≤ workCap := by
    unfold exitWorkCap at hWork
    omega
  have hArcFit : metaArrBase n m N + mIdxArcPtr < 2 ^ bits :=
    Nat.lt_of_lt_of_le (by omega) hWorkFit
  have hPlNext : Placed code (loopPc + 398) (step4A_advance loopPc h100) :=
    step4A_advance_placed hPl
  have hPlLoad : Placed code (loopPc + 398) (metaLoadInstrs (bits := bits) reg2 reg4 mIdxArcPtr
      (by dsimp only [mIdxArcPtr]; omega)) :=
    Placed_append_left (Placed_append_left (Placed_append_left hPlNext))
  obtain ⟨s1, hs1, hpc1, hd1, hr2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlLoad (by omega) hpc hM hArcFit hPtr
  have h1_1 : (reg s1 reg1).val = 1 := by rw [hPres1 reg1 (by intro h; cases h) (by intro h; cases h), h1]
  have h0_1 : (reg s1 reg0).val = 0 := by rw [hPres1 reg0 (by intro h; cases h) (by intro h; cases h), h0]
  have hM_1 : (reg s1 rMeta).val = metaArrBase n m N := by
    rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hM]
  have haAdd : code[s1.pc]? = some (.add reg2 reg2 reg1) := by
    rw [hpc1]; exact hPlNext 3 _ rfl
  obtain ⟨s2, hs2, hpc2, h2_2, ho2, hd2⟩ := step_add_at (input := input) haAdd (by omega)
  have h2Val : (reg s2 reg2).val = arcPtr + 1 := by
    rw [h2_2, add_no_wrap _ _ (by rw [hr2_1, h1_1]; omega), hr2_1, h1_1]
  have hM_2 : (reg s2 rMeta).val = metaArrBase n m N := by
    rw [ho2 rMeta (by intro h; cases h), hM_1]
  have hPlStore : Placed code (loopPc + 402) (metaStoreInstrs (bits := bits) reg2 reg4 mIdxArcPtr
      (by dsimp only [mIdxArcPtr]; omega)) := by
    intro i ins hi
    have hInstruction := hPlNext (4 + i) ins
      (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi)
    simpa only [← Nat.add_assoc] using hInstruction
  have hSz2 : metaArrBase n m N + mIdxArcPtr < s2.data.size := by
    rw [hd2, hd1]; exact lt_data_size (by omega)
  obtain ⟨s3, hs3, hpc3, hAt3, hFr3, hPres3⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlStore (by omega) (by rw [hpc2, hpc1])
    hM_2 hArcFit hSz2
  have haGo : code[s3.pc]? = some (.goto loopPc) := by
    rw [hpc3]; exact hPlNext 7 _ rfl
  obtain ⟨t, ht, hpct, hrt, hdt⟩ := step_goto_at (input := input) haGo (by omega)
  have hrTF := reg_of_regs_eq hrt
  refine ⟨t, hs1.append (Steps.cons hs2 (hs3.append (steps_1_of_step ht))), hpct,
    by rw [hrTF, hPres3 reg0 (by intro h; cases h), ho2 reg0 (by intro h; cases h), h0_1],
    by rw [hrTF, hPres3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), h1_1],
    by rw [hrTF, hPres3 rMeta (by intro h; cases h), hM_2],
    by rw [hdt, hAt3, Option.map_some, h2Val],
    fun j hj => by rw [hdt, hFr3 j hj, hd2, hd1]⟩

end PaperB.RamProgram.ExitSummaryBuild
