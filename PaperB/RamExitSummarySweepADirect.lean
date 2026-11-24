module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepADecode
public import PaperB.RamExitSummarySweepANext

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! Word-RAM execution of the direct endpoint contribution to a prior-base accumulator. -/

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

theorem step4A_direct_spec {code : Program DomL} {input : Input DomL}
    (entryPc donePc accOff metaBase rTail : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hAccOff : accOff + 3 ≤ 42) (hBoundMeta : metaBase + 64 ≤ workCap)
    (hPl : Placed code entryPc (step4ADirectInstrs entryPc donePc accOff (by omega) h100))
    (hSz : entryPc + 40 < code.size) (hDone : donePc < code.size)
    (s17 : State DomL) (hpc17 : s17.pc = entryPc)
    (h0_17 : (reg s17 reg0).val = 0) (h1_17 : (reg s17 reg1).val = 1)
    (hRM17 : (reg s17 rMeta).val = metaBase) (h6_17 : (reg s17 reg6).val = rTail)
    (acc : Interval) (hAcc : IntervalWordsAt s17.data (metaBase + accOff) acc) :
    ∃ k t, k ≤ 40 ∧ Steps code input k s17 t ∧ t.pc = donePc ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      IntervalWordsAt t.data (metaBase + accOff) (Interval.join acc (.span rTail rTail)) ∧
      (∀ j, (j < metaBase + accOff ∨ metaBase + accOff + 3 ≤ j) →
        (j < metaBase + 42 ∨ metaBase + 45 ≤ j) → t.data[j]? = s17.data[j]?) := by
  -- Write `[1, rTail, rTail]` to `42, 43, 44`:
  have hPlW0 : Placed code (entryPc) (metaStoreInstrs (bits := bits) reg1 reg8 42 (by omega)) :=
    Placed_window hPl 0 rfl
  obtain ⟨s18, hs18, hpc18, hAt18, hFr18, hPres18⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlW0 (by omega) hpc17 hRM17 (by omega)
    (lt_data_size (by omega))
  have hRM18 : (reg s18 rMeta).val = metaBase := by rw [hPres18 rMeta (by intro h; cases h), hRM17]
  have h6_18 : (reg s18 reg6).val = rTail := by rw [hPres18 reg6 (by intro h; cases h), h6_17]
  have hPlW1 : Placed code (entryPc + 3) (metaStoreInstrs (bits := bits) reg6 reg8 43 (by omega)) :=
    Placed_window hPl 3 rfl
  obtain ⟨s19, hs19, hpc19, hAt19, hFr19, hPres19⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlW1 (by omega) hpc18 hRM18 (by omega)
    (by exact lt_data_size (by omega))
  have hRM19 : (reg s19 rMeta).val = metaBase := by rw [hPres19 rMeta (by intro h; cases h), hRM18]
  have hPlW2 : Placed code (entryPc + 6) (metaStoreInstrs (bits := bits) reg6 reg8 44 (by omega)) :=
    Placed_window hPl 6 rfl
  obtain ⟨s20, hs20, hpc20, hAt20, hFr20, hPres20⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlW2 (by omega) hpc19 hRM19 (by omega)
    (by exact lt_data_size (by omega))
  have hRM20 : (reg s20 rMeta).val = metaBase := by rw [hPres20 rMeta (by intro h; cases h), hRM19]
  have h1_20 : (reg s20 reg1).val = 1 := by
    rw [hPres20 reg1 (by intro h; cases h), hPres19 reg1 (by intro h; cases h),
      hPres18 reg1 (by intro h; cases h), h1_17]
  have h0_20 : (reg s20 reg0).val = 0 := by
    rw [hPres20 reg0 (by intro h; cases h), hPres19 reg0 (by intro h; cases h),
      hPres18 reg0 (by intro h; cases h), h0_17]
  -- Set `reg2 = (metaBase + accOff)`, `reg3 = metaBase + 42`, `reg4 = (metaBase + accOff)`:
  have haI1 : code[s20.pc]? = some (.imm reg2 ⟨accOff, by omega⟩) := by rw [hpc20]; exact hPl 9 _ rfl
  obtain ⟨s21, hs21Raw, hpc21, h2_21, ho21, hd21⟩ := step_imm_at (input := input) haI1 (by omega)
  have hs21 := steps_1_of_step hs21Raw
  have haA1 : code[s21.pc]? = some (.add reg2 rMeta reg2) := by rw [hpc21, hpc20]; exact hPl 10 _ rfl
  obtain ⟨s22, hs22Raw, hpc22, h2_22, ho22, hd22⟩ := step_add_at (input := input) haA1 (by omega)
  have hs22 := steps_1_of_step hs22Raw
  have h2Val22 : (reg s22 reg2).val = (metaBase + accOff) := by
    rw [h2_22, add_no_wrap _ _ (by rw [ho21 rMeta (by intro h; cases h), hRM20, h2_21]; change metaBase + accOff < 2 ^ bits; omega),
      ho21 rMeta (by intro h; cases h), hRM20, h2_21]
  have haI2 : code[s22.pc]? = some (.imm reg3 ⟨42, by omega⟩) := by rw [hpc22, hpc21, hpc20]; exact hPl 11 _ rfl
  obtain ⟨s23, hs23Raw, hpc23, h3_23, ho23, hd23⟩ := step_imm_at (input := input) haI2 (by omega)
  have hs23 := steps_1_of_step hs23Raw
  have haA2 : code[s23.pc]? = some (.add reg3 rMeta reg3) := by rw [hpc23, hpc22, hpc21, hpc20]; exact hPl 12 _ rfl
  obtain ⟨s24, hs24Raw, hpc24, h3_24, ho24, hd24⟩ := step_add_at (input := input) haA2 (by omega)
  have hs24 := steps_1_of_step hs24Raw
  have hRM24 : (reg s24 rMeta).val = metaBase := by
    rw [ho24 rMeta (by intro h; cases h), ho23 rMeta (by intro h; cases h),
      ho22 rMeta (by intro h; cases h), ho21 rMeta (by intro h; cases h), hRM20]
  have h3Val24 : (reg s24 reg3).val = metaBase + 42 := by
    rw [h3_24, add_no_wrap _ _ (by rw [ho23 rMeta (by intro h; cases h), ho22 rMeta (by intro h; cases h),
      ho21 rMeta (by intro h; cases h), hRM20, h3_23]; change metaBase + 42 < 2 ^ bits; omega),
      ho23 rMeta (by intro h; cases h), ho22 rMeta (by intro h; cases h),
      ho21 rMeta (by intro h; cases h), hRM20, h3_23]
  have h2Val24 : (reg s24 reg2).val = (metaBase + accOff) := by
    rw [ho24 reg2 (by intro h; cases h), ho23 reg2 (by intro h; cases h), h2Val22]
  have haMv : code[s24.pc]? = some (.mov reg4 reg2) := by rw [hpc24, hpc23, hpc22, hpc21, hpc20]; exact hPl 13 _ rfl
  obtain ⟨s25, hs25Raw, hpc25, h4_25, ho25, hd25⟩ := step_mov_at (input := input) haMv (by omega)
  have hs25 := steps_1_of_step hs25Raw
  have hd25' : s25.data = s20.data := by rw [hd25, hd24, hd23, hd22, hd21]
  have hData25 : ∀ j, j < metaBase + 42 ∨ metaBase + 45 ≤ j →
      s25.data[j]? = s17.data[j]? := by
    intro j hj
    rw [hd25', hFr20 j (by omega), hFr19 j (by omega), hFr18 j (by omega)]
  have hTmpSpan : IntervalWordsAt s25.data (metaBase + 42) (.span rTail rTail) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hd25', hFr20 _ (by omega), hFr19 _ (by omega), hAt18, Option.map_some,
        h1_17]
    · rw [hd25', hFr20 _ (by omega), hAt19, Option.map_some, h6_18]
    · rw [hd25', hAt20, Option.map_some, hPres19 reg6 (by intro h; cases h), h6_18]
  have hAcc25 : IntervalWordsAt s25.data (metaBase + accOff) acc :=
    intervalWordsAt_frame (fun i hi => hData25 _ (Or.inl (by omega))) hAcc
  have hPlJoin : Placed code (entryPc + 14) (intervalJoinInstrs (bits := bits) (entryPc + 14)) :=
    Placed_window hPl 14 rfl
  obtain ⟨kJ, s26, hkJ, hs26, hpc26, hJoin26, hPres26, hFr26⟩ := run_intervalJoin (input := input)
    (entryPc + 14) hPlJoin (by omega) ((metaBase + accOff)) (metaBase + 42) ((metaBase + accOff))
    acc (.span rTail rTail) (by omega) (by omega) (by omega) (by omega)
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
  have haGoN : code[s26.pc]? = some (.goto (donePc)) := by rw [hpc26]; exact hPl 39 _ rfl
  obtain ⟨s27, hs27Raw, hpc27, hr27, hd27⟩ := step_goto_at (input := input) haGoN (by omega)
  have hs27 := steps_1_of_step hs27Raw
  have hr27F := reg_of_regs_eq hr27
  have hFr27All : ∀ j, (j < metaBase + accOff ∨ metaBase + accOff + 3 ≤ j) →
      (j < metaBase + 42 ∨ metaBase + 45 ≤ j) → s27.data[j]? = s17.data[j]? := by
    intro j hAccFr hScratchFr
    rw [hd27, hFr26 j hAccFr, hData25 j hScratchFr]
  have hTrace : Steps code input (9 + (5 + (kJ + 1))) s17 s27 :=
    (hs18.append (hs19.append hs20)).append
      ((hs21.append (hs22.append (hs23.append (hs24.append hs25)))).append (hs26.append hs27))
  refine ⟨_, s27, by omega, hTrace, hpc27, ?_, ?_, ?_, by rw [hd27]; exact hJoin26, hFr27All⟩
  · rw [hr27F, hPres26 reg0 (Or.inl rfl), ho25 reg0 (by intro h; cases h),
      ho24 reg0 (by intro h; cases h), ho23 reg0 (by intro h; cases h),
      ho22 reg0 (by intro h; cases h), ho21 reg0 (by intro h; cases h), h0_20]
  · rw [hr27F, hPres26 reg1 (Or.inr (Or.inl rfl)), ho25 reg1 (by intro h; cases h),
      ho24 reg1 (by intro h; cases h), ho23 reg1 (by intro h; cases h),
      ho22 reg1 (by intro h; cases h), ho21 reg1 (by intro h; cases h), h1_20]
  · rw [hr27F, hPres26 rMeta (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))),
      ho25 rMeta (by intro h; cases h), hRM24]

end PaperB.RamProgram.ExitSummaryBuild
