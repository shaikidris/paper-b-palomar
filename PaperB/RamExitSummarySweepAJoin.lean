module

public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! A word-RAM interval join with accumulator and input addresses given by metadata offsets. -/

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

def step4A_joinAtInstrs (entryPc dstOff srcOff : Nat)
    (hDst : dstOff < 2 ^ bits) (hSrc : srcOff < 2 ^ bits) : List (Instr bits 15) :=
  [ .imm reg2 ⟨dstOff, hDst⟩, .add reg2 rMeta reg2
  , .imm reg3 ⟨srcOff, hSrc⟩, .add reg3 rMeta reg3
  , .mov reg4 reg2
  ] ++
  intervalJoinInstrs (entryPc + 5)

theorem step4A_joinAt_spec {code : Program DomL} {input : Input DomL}
    (entryPc metaBase dstOff srcOff : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hOff : dstOff + 3 ≤ srcOff) (hSrc : srcOff + 3 ≤ 64)
    (hBoundMeta : metaBase + 64 ≤ workCap)
    (hPl : Placed code entryPc (step4A_joinAtInstrs entryPc dstOff srcOff (by omega) (by omega)))
    (hSz : entryPc + 30 < code.size)
    (s20 : State DomL) (hpc20 : s20.pc = entryPc)
    (h0_20 : (reg s20 reg0).val = 0) (h1_20 : (reg s20 reg1).val = 1)
    (hRM20 : (reg s20 rMeta).val = metaBase)
    (acc value : Interval)
    (hAcc : IntervalWordsAt s20.data (metaBase + dstOff) acc)
    (hValue : IntervalWordsAt s20.data (metaBase + srcOff) value) :
    ∃ k t, k ≤ 30 ∧ Steps code input k s20 t ∧ t.pc = entryPc + 30 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      IntervalWordsAt t.data (metaBase + dstOff) (Interval.join acc value) ∧
      (∀ j, j < metaBase + dstOff ∨ metaBase + dstOff + 3 ≤ j → t.data[j]? = s20.data[j]?) := by
  -- Set `reg2 = (metaBase + dstOff)`, `reg3 = metaBase + srcOff`, `reg4 = (metaBase + dstOff)`:
  have haI1 : code[s20.pc]? = some (.imm reg2 ⟨dstOff, by omega⟩) := by rw [hpc20]; exact hPl 0 _ rfl
  obtain ⟨s21, hs21Raw, hpc21, h2_21, ho21, hd21⟩ := step_imm_at (input := input) haI1 (by omega)
  have hs21 := steps_1_of_step hs21Raw
  have haA1 : code[s21.pc]? = some (.add reg2 rMeta reg2) := by rw [hpc21, hpc20]; exact hPl 1 _ rfl
  obtain ⟨s22, hs22Raw, hpc22, h2_22, ho22, hd22⟩ := step_add_at (input := input) haA1 (by omega)
  have hs22 := steps_1_of_step hs22Raw
  have h2Val22 : (reg s22 reg2).val = (metaBase + dstOff) := by
    rw [h2_22, add_no_wrap _ _ (by rw [ho21 rMeta (by intro h; cases h), hRM20, h2_21]; change metaBase + dstOff < 2 ^ bits; omega),
      ho21 rMeta (by intro h; cases h), hRM20, h2_21]
  have haI2 : code[s22.pc]? = some (.imm reg3 ⟨srcOff, by omega⟩) := by rw [hpc22, hpc21, hpc20]; exact hPl 2 _ rfl
  obtain ⟨s23, hs23Raw, hpc23, h3_23, ho23, hd23⟩ := step_imm_at (input := input) haI2 (by omega)
  have hs23 := steps_1_of_step hs23Raw
  have haA2 : code[s23.pc]? = some (.add reg3 rMeta reg3) := by rw [hpc23, hpc22, hpc21, hpc20]; exact hPl 3 _ rfl
  obtain ⟨s24, hs24Raw, hpc24, h3_24, ho24, hd24⟩ := step_add_at (input := input) haA2 (by omega)
  have hs24 := steps_1_of_step hs24Raw
  have hRM24 : (reg s24 rMeta).val = metaBase := by
    rw [ho24 rMeta (by intro h; cases h), ho23 rMeta (by intro h; cases h),
      ho22 rMeta (by intro h; cases h), ho21 rMeta (by intro h; cases h), hRM20]
  have h3Val24 : (reg s24 reg3).val = metaBase + srcOff := by
    rw [h3_24, add_no_wrap _ _ (by rw [ho23 rMeta (by intro h; cases h), ho22 rMeta (by intro h; cases h),
      ho21 rMeta (by intro h; cases h), hRM20, h3_23]; change metaBase + srcOff < 2 ^ bits; omega),
      ho23 rMeta (by intro h; cases h), ho22 rMeta (by intro h; cases h),
      ho21 rMeta (by intro h; cases h), hRM20, h3_23]
  have h2Val24 : (reg s24 reg2).val = (metaBase + dstOff) := by
    rw [ho24 reg2 (by intro h; cases h), ho23 reg2 (by intro h; cases h), h2Val22]
  have haMv : code[s24.pc]? = some (.mov reg4 reg2) := by rw [hpc24, hpc23, hpc22, hpc21, hpc20]; exact hPl 4 _ rfl
  obtain ⟨s25, hs25Raw, hpc25, h4_25, ho25, hd25⟩ := step_mov_at (input := input) haMv (by omega)
  have hs25 := steps_1_of_step hs25Raw
  have hd25' : s25.data = s20.data := by rw [hd25, hd24, hd23, hd22, hd21]
  have hAcc25 : IntervalWordsAt s25.data (metaBase + dstOff) acc := by
    rw [hd25']
    exact hAcc
  have hTmpSpan : IntervalWordsAt s25.data (metaBase + srcOff) value := by
    rw [hd25']
    exact hValue
  have hPlJoin : Placed code (entryPc + 5) (intervalJoinInstrs (bits := bits) (entryPc + 5)) :=
    Placed_window hPl 5 rfl
  obtain ⟨kJ, s26, hkJ, hs26, hpc26, hJoin26, hPres26, hFr26⟩ := run_intervalJoin (input := input)
    (entryPc + 5) hPlJoin (by omega) (metaBase + dstOff) (metaBase + srcOff) (metaBase + dstOff)
    acc value (by omega) (by omega) (by omega) (by omega)
    s25 (by omega)
    (by rw [ho25 reg0 (by intro h; cases h), ho24 reg0 (by intro h; cases h),
      ho23 reg0 (by intro h; cases h), ho22 reg0 (by intro h; cases h),
      ho21 reg0 (by intro h; cases h), h0_20])
    (by rw [ho25 reg1 (by intro h; cases h), ho24 reg1 (by intro h; cases h),
      ho23 reg1 (by intro h; cases h), ho22 reg1 (by intro h; cases h),
      ho21 reg1 (by intro h; cases h), h1_20])
    (by rw [ho25 reg2 (by intro h; cases h), h2Val24])
    (by rw [ho25 reg3 (by intro h; cases h), h3Val24])
    (by rw [h4_25, h2Val24])
    hAcc25 hTmpSpan

  have hTrace : Steps code input (5 + kJ) s20 s26 :=
    (hs21.append (hs22.append (hs23.append (hs24.append hs25)))).append hs26
  refine ⟨_, s26, by omega, hTrace, hpc26, ?_, ?_, ?_, hJoin26, ?_⟩
  · rw [hPres26 reg0 (Or.inl rfl), ho25 reg0 (by intro h; cases h),
      ho24 reg0 (by intro h; cases h), ho23 reg0 (by intro h; cases h),
      ho22 reg0 (by intro h; cases h), ho21 reg0 (by intro h; cases h), h0_20]
  · rw [hPres26 reg1 (Or.inr (Or.inl rfl)), ho25 reg1 (by intro h; cases h),
      ho24 reg1 (by intro h; cases h), ho23 reg1 (by intro h; cases h),
      ho22 reg1 (by intro h; cases h), ho21 reg1 (by intro h; cases h), h1_20]
  · rw [hPres26 rMeta (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))),
      ho25 rMeta (by intro h; cases h), hRM24]
  · intro j hj
    rw [hFr26 j hj, hd25']

end PaperB.RamProgram.ExitSummaryBuild
