module

public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! Word-RAM test for the nonzero label and its membership in an ancestry interval. -/

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

theorem step4A_ancestry_spec {code : Program DomL} {input : Input DomL}
    (loopPc n N metaBase u v vEntry ownerEntry ownerStop : Nat)
    (h100 : 100 ≤ 2 ^ bits) (hULt : u < n) (hVLt : v < N)
    (hBoundMeta : metaBase + 64 ≤ workCap) (hCap : 4 + n + 3 * N ≤ inputCap)
    (hAncestry : Placed code (loopPc + 118) (step4A_ancestry loopPc h100))
    (hSz : loopPc + 406 < code.size)
    (sL : State DomL) (hpcL : sL.pc = loopPc + 118)
    (h0L : (reg sL reg0).val = 0) (h1L : (reg sL reg1).val = 1)
    (hML : (reg sL rMeta).val = metaBase) (h5L : (reg sL reg5).val = u)
    (hLabels : (sL.data[metaBase + mIdxLabelsInBase]?).map Fin.val = some 4)
    (hEntryLoc : (sL.data[metaBase + mIdxFEntryInBase]?).map Fin.val = some (4 + n + 2 * N))
    (hAtLabel : (input.words[4 + u]?).map Fin.val = some v)
    (hAtEntry : (input.words[4 + n + 2 * N + v]?).map Fin.val = some vEntry)
    (hOwnEn : (sL.data[metaBase + 50]?).map Fin.val = some ownerEntry)
    (hOwnSt : (sL.data[metaBase + 51]?).map Fin.val = some ownerStop) :
    ∃ k t, k ≤ 19 ∧ Steps code input k sL t ∧
      t.pc = (if 0 < v ∧ ownerEntry ≤ vEntry ∧ vEntry < ownerStop then loopPc + 137 else loopPc + 398) ∧
      t.data = sL.data ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      (reg t reg5).val = u ∧ (reg t reg6).val = v := by
  have placed := step4A_ancestryCheck_placed hAncestry
  -- Load `v = input[labelsInBase + u]`:
  have hPlLab : Placed code (loopPc + 118) (metaLoadInstrs (bits := bits) reg6 reg7 mIdxLabelsInBase (by dsimp only [mIdxLabelsInBase]; omega)) :=
    Placed_window placed 0 rfl
  obtain ⟨s21, hs21, hpc21, hd21, h6_21, hPres21⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlLab (by omega) hpcL hML (by dsimp only [mIdxLabelsInBase]; omega)
    hLabels
  have h5_21 : (reg s21 reg5).val = u := by rw [hPres21 reg5 (by intro h; cases h) (by intro h; cases h), h5L]
  have haAddV : code[s21.pc]? = some (.add reg6 reg6 reg5) := by rw [hpc21]; exact placed 3 _ rfl
  obtain ⟨s22, hs22Raw, hpc22, h6_22, ho22, hd22⟩ := step_add_at (input := input) haAddV (by omega)
  have hs22 := steps_1_of_step hs22Raw
  have h6Val22 : (reg s22 reg6).val = 4 + u := by
    rw [h6_22, add_no_wrap _ _ (by rw [h6_21, h5_21]; omega), h6_21, h5_21]
  obtain ⟨wv, hwv, hwvV⟩ := Option.map_eq_some_iff.mp hAtLabel
  have haLoadV : code[s22.pc]? = some (.loadInput reg6 reg6) := by rw [hpc22, hpc21]; exact placed 4 _ rfl
  obtain ⟨s23, hs23Raw, hpc23, h6_23, ho23, hd23⟩ := step_loadInput_at (input := input) haLoadV (by omega)
    (by rw [h6Val22]; exact hwv)
  have hs23 := steps_1_of_step hs23Raw
  have hvVal23 : (reg s23 reg6).val = v := by rw [h6_23, hwvV]
  have h0_23 : (reg s23 reg0).val = 0 := by
    rw [ho23 reg0 (by intro h; cases h), ho22 reg0 (by intro h; cases h),
      hPres21 reg0 (by intro h; cases h) (by intro h; cases h), h0L]
  have h1_23 : (reg s23 reg1).val = 1 := by
    rw [ho23 reg1 (by intro h; cases h), ho22 reg1 (by intro h; cases h),
      hPres21 reg1 (by intro h; cases h) (by intro h; cases h), h1L]
  have hM_23 : (reg s23 rMeta).val = metaBase := by
    rw [ho23 rMeta (by intro h; cases h), ho22 rMeta (by intro h; cases h),
      hPres21 rMeta (by intro h; cases h) (by intro h; cases h), hML]
  have h5_23 : (reg s23 reg5).val = u := by
    rw [ho23 reg5 (by intro h; cases h), ho22 reg5 (by intro h; cases h), h5_21]
  have hData23 : s23.data = sL.data := by rw [hd23, hd22, hd21]
  have haBrV : code[s23.pc]? = some (.branchLt reg0 reg6 (loopPc + 124) (loopPc + 398)) := by
    rw [hpc23, hpc22, hpc21]; exact placed 5 _ rfl
  obtain ⟨s24, hs24Raw, hpc24, hr24, hd24⟩ := step_branchLt_at (input := input) haBrV (by split <;> omega)
  have hs24 := steps_1_of_step hs24Raw
  have hr24F := reg_of_regs_eq hr24
  by_cases hvPos : 0 < v
  · rw [ite_eq_left (by rw [h0_23, hvVal23]; exact hvPos)] at hpc24
    -- Load `fEntry[v]` and `ownerEntry`:
    have hPlFE : Placed code (loopPc + 124) (metaLoadInstrs (bits := bits) reg7 reg8 mIdxFEntryInBase
        (by dsimp only [mIdxFEntryInBase]; omega)) :=
      Placed_window placed 6 rfl
    obtain ⟨s25, hs25, hpc25, hd25, h7_25, hPres25⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlFE (by omega) hpc24
      (by rw [hr24F, hM_23]) (by dsimp only [mIdxFEntryInBase]; omega)
      (by rw [hd24, hData23]; exact hEntryLoc)
    have h6_25 : (reg s25 reg6).val = v := by
      rw [hPres25 reg6 (by intro h; cases h) (by intro h; cases h), hr24F, hvVal23]
    have haAddFE : code[s25.pc]? = some (.add reg7 reg7 reg6) := by rw [hpc25]; exact placed 9 _ rfl
    obtain ⟨s26, hs26Raw, hpc26, h7_26, ho26, hd26⟩ := step_add_at (input := input) haAddFE (by omega)
    have hs26 := steps_1_of_step hs26Raw
    have h7Val26 : (reg s26 reg7).val = 4 + n + 2 * N + v := by
      rw [h7_26, add_no_wrap _ _ (by rw [h7_25, h6_25]; omega), h7_25, h6_25]
    obtain ⟨wfe, hwfe, hwfeV⟩ := Option.map_eq_some_iff.mp hAtEntry
    have haLoadFE : code[s26.pc]? = some (.loadInput reg7 reg7) := by rw [hpc26, hpc25]; exact placed 10 _ rfl
    obtain ⟨s27, hs27Raw, hpc27, h7_27, ho27, hd27⟩ := step_loadInput_at (input := input) haLoadFE (by omega)
      (by rw [h7Val26]; exact hwfe)
    have hs27 := steps_1_of_step hs27Raw
    have hvEnVal : (reg s27 reg7).val =
        vEntry := by
      rw [h7_27, hwfeV]
    have hRM27 : (reg s27 rMeta).val = metaBase := by
      rw [ho27 rMeta (by intro h; cases h), ho26 rMeta (by intro h; cases h),
        hPres25 rMeta (by intro h; cases h) (by intro h; cases h), hr24F, hM_23]
    have hData27 : s27.data = sL.data := by rw [hd27, hd26, hd25, hd24, hData23]
    have hPlOE : Placed code (loopPc + 129) (metaLoadInstrs (bits := bits) reg8 reg9 50 (by omega)) :=
      Placed_window placed 11 rfl
    obtain ⟨s28, hs28, hpc28, hd28, h8_28, hPres28⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlOE (by omega) (by rw [hpc27, hpc26, hpc25]) hRM27 (by omega)
      (by rw [hData27]; exact hOwnEn)
    have h7_28 : (reg s28 reg7).val =
        vEntry := by
      rw [hPres28 reg7 (by intro h; cases h) (by intro h; cases h), hvEnVal]
    have h0_28 : (reg s28 reg0).val = 0 := by
      rw [hPres28 reg0 (by intro h; cases h) (by intro h; cases h), ho27 reg0 (by intro h; cases h),
        ho26 reg0 (by intro h; cases h), hPres25 reg0 (by intro h; cases h) (by intro h; cases h), hr24F, h0_23]
    have h1_28 : (reg s28 reg1).val = 1 := by
      rw [hPres28 reg1 (by intro h; cases h) (by intro h; cases h), ho27 reg1 (by intro h; cases h),
        ho26 reg1 (by intro h; cases h), hPres25 reg1 (by intro h; cases h) (by intro h; cases h), hr24F, h1_23]
    have hM_28 : (reg s28 rMeta).val = metaBase := by rw [hPres28 rMeta (by intro h; cases h) (by intro h; cases h), hRM27]
    have h5_28 : (reg s28 reg5).val = u := by
      rw [hPres28 reg5 (by intro h; cases h) (by intro h; cases h), ho27 reg5 (by intro h; cases h),
        ho26 reg5 (by intro h; cases h), hPres25 reg5 (by intro h; cases h) (by intro h; cases h), hr24F, h5_23]
    have h6_28 : (reg s28 reg6).val = v := by
      rw [hPres28 reg6 (by intro h; cases h) (by intro h; cases h), ho27 reg6 (by intro h; cases h),
        ho26 reg6 (by intro h; cases h), h6_25]
    have hData28 : s28.data = sL.data := by rw [hd28, hData27]
    have haBrEn : code[s28.pc]? = some (.branchLt reg7 reg8 (loopPc + 398) (loopPc + 133)) := by
      rw [hpc28]; exact placed 14 _ rfl
    obtain ⟨s29, hs29Raw, hpc29, hr29, hd29⟩ := step_branchLt_at (input := input) haBrEn (by split <;> omega)
    have hs29 := steps_1_of_step hs29Raw
    have hr29F := reg_of_regs_eq hr29
    by_cases hEnLe : ownerEntry ≤ vEntry
    · rw [ite_eq_right (by rw [h7_28, h8_28]; omega)] at hpc29
      have hPlOS : Placed code (loopPc + 133) (metaLoadInstrs (bits := bits) reg8 reg9 51 (by omega)) :=
        Placed_window placed 15 rfl
      obtain ⟨s30, hs30, hpc30, hd30, h8_30, hPres30⟩ := run_metaLoad_slice (input := input)
        (by intro h; cases h) (by intro h; cases h) hPlOS (by omega) hpc29
        (by rw [hr29F, hM_28]) (by omega)
        (by rw [hd29, hData28]; exact hOwnSt)
      have h7_30 : (reg s30 reg7).val =
          vEntry := by
        rw [hPres30 reg7 (by intro h; cases h) (by intro h; cases h), hr29F, h7_28]
      have h0_30 : (reg s30 reg0).val = 0 := by rw [hPres30 reg0 (by intro h; cases h) (by intro h; cases h), hr29F, h0_28]
      have h1_30 : (reg s30 reg1).val = 1 := by rw [hPres30 reg1 (by intro h; cases h) (by intro h; cases h), hr29F, h1_28]
      have hM_30 : (reg s30 rMeta).val = metaBase := by rw [hPres30 rMeta (by intro h; cases h) (by intro h; cases h), hr29F, hM_28]
      have h5_30 : (reg s30 reg5).val = u := by rw [hPres30 reg5 (by intro h; cases h) (by intro h; cases h), hr29F, h5_28]
      have h6_30 : (reg s30 reg6).val = v := by rw [hPres30 reg6 (by intro h; cases h) (by intro h; cases h), hr29F, h6_28]
      have hData30 : s30.data = sL.data := by rw [hd30, hd29, hData28]
      have haBrSt : code[s30.pc]? = some (.branchLt reg7 reg8 (loopPc + 137) (loopPc + 398)) := by
        rw [hpc30]; exact placed 18 _ rfl
      obtain ⟨s31, hs31Raw, hpc31, hr31, hd31⟩ := step_branchLt_at (input := input) haBrSt (by split <;> omega)
      have hs31 := steps_1_of_step hs31Raw
      have hr31F := reg_of_regs_eq hr31
      have hTrace : Steps code input 19 sL s31 :=
        hs21.append (hs22.append (hs23.append (hs24.append (hs25.append
          (hs26.append (hs27.append (hs28.append (hs29.append (hs30.append hs31)))))))))
      refine ⟨19, s31, by decide, hTrace, ?_, by rw [hd31, hData30],
        by rw [hr31F, h0_30], by rw [hr31F, h1_30], by rw [hr31F, hM_30],
        by rw [hr31F, h5_30], by rw [hr31F, h6_30]⟩
      by_cases hEnLtSt : vEntry < ownerStop
      · rw [ite_eq_left (by rw [h7_30, h8_30]; exact hEnLtSt)] at hpc31
        rw [ite_eq_left ⟨hvPos, hEnLe, hEnLtSt⟩]
        exact hpc31
      · rw [ite_eq_right (by rw [h7_30, h8_30]; exact hEnLtSt)] at hpc31
        rw [ite_eq_right (fun h => hEnLtSt h.2.2)]
        exact hpc31
    · rw [ite_eq_left (by rw [h7_28, h8_28]; omega)] at hpc29
      have hTrace : Steps code input 15 sL s29 :=
        hs21.append (hs22.append (hs23.append (hs24.append (hs25.append
          (hs26.append (hs27.append (hs28.append hs29)))))))
      rw [ite_eq_right (fun h => hEnLe h.2.1)]
      refine ⟨15, s29, by decide, hTrace, hpc29, by rw [hd29, hData28],
        by rw [hr29F, h0_28], by rw [hr29F, h1_28], by rw [hr29F, hM_28],
        by rw [hr29F, h5_28], by rw [hr29F, h6_28]⟩
  · rw [ite_eq_right (by rw [h0_23, hvVal23]; exact hvPos)] at hpc24
    have hTrace : Steps code input 6 sL s24 :=
      hs21.append (hs22.append (hs23.append hs24))
    rw [ite_eq_right (fun h => hvPos h.1)]
    refine ⟨6, s24, by decide, hTrace, hpc24, by rw [hd24, hData23],
      by rw [hr24F, h0_23], by rw [hr24F, h1_23], by rw [hr24F, hM_23],
      by rw [hr24F, h5_23], by rw [hr24F, hvVal23]⟩

end PaperB.RamProgram.ExitSummaryBuild
