module

public import PaperB.RamExitSummarySweepBROM
public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-! Correctness of the fixed word-RAM kernel computing the parent slot tag. -/

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

theorem run_step4BSlotTag {code : Program DomL} {input : Input DomL}
    (basePc sOff : Nat) (hsOff : sOff < 2 ^ bits) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4BSlotTagInstrs (bits := bits) basePc sOff hsOff h100))
    (hSz : basePc + 19 < code.size)
    {n m N : Nat} (hMetaFit : metaArrBase n m N + 64 ≤ workCap) (hWorkFit : workCap ≤ 2 ^ bits)
    (sVal aVal bVal : Nat) (_hNeAB : aVal ≠ bVal)
    (st : State DomL) (hpc : st.pc = basePc)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1) (hM : (reg st rMeta).val = metaArrBase n m N)
    (hS : (st.data[metaArrBase n m N + sOff]?).map Fin.val = some sVal)
    (hA : (st.data[metaArrBase n m N + 50]?).map Fin.val = some aVal)
    (hB : (st.data[metaArrBase n m N + 51]?).map Fin.val = some bVal) :
    let tag := if sVal = aVal then 1 else if sVal = bVal then 2 else 0
    ∃ k t, k ≤ 16 ∧ Steps code input k st t ∧ t.pc = basePc + 19 ∧
      t.data = st.data ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaArrBase n m N ∧
      (reg t reg4).val = tag ∧
      (∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → reg t r = reg st r) := by
  let metaBase := metaArrBase n m N
  have hSFit : metaBase + sOff < 2 ^ bits := by
    obtain ⟨w, hwAt, _⟩ := Option.map_eq_some_iff.mp hS
    have hAddr := (Array.getElem?_eq_some_iff.mp hwAt).1
    rw [st.data_size] at hAddr
    exact Nat.lt_of_lt_of_le hAddr hWorkFit
  have hPl0 : Placed code basePc (metaLoadInstrs (bits := bits) reg2 reg5 sOff hsOff) :=
    Placed_window hPl 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) hpc hM hSFit hS
  have hM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hM]
  have hPl1 : Placed code (basePc + 3) (metaLoadInstrs (bits := bits) reg3 reg5 50 (by omega)) :=
    Placed_window hPl 3 rfl
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc1 hM1 (by omega) (by rw [hd1]; exact hA)
  have h2_2 : (reg s2 reg2).val = sVal := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h0_2 : (reg s2 reg0).val = 0 := by
    rw [hPres2 reg0 (by intro h; cases h) (by intro h; cases h), hPres1 reg0 (by intro h; cases h) (by intro h; cases h), h0]
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [hPres2 reg1 (by intro h; cases h) (by intro h; cases h), hPres1 reg1 (by intro h; cases h) (by intro h; cases h), h1]
  have hM2 : (reg s2 rMeta).val = metaBase := by rw [hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1]
  have hPresS2 : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg5 → reg s2 r = reg st r := fun r hr2 hr3 hr5 => by
    rw [hPres2 r hr3 hr5, hPres1 r hr2 hr5]
  have hd2' : s2.data = st.data := by rw [hd2, hd1]
  have haBr1 : code[s2.pc]? = some (.branchLt reg2 reg3 (basePc + 9) (basePc + 7)) := by rw [hpc2]; exact hPl 6 _ rfl
  obtain ⟨s3, hs3Raw, hpc3, hr3, hd3⟩ := step_branchLt_at (input := input) haBr1 (by split <;> omega)
  have hs3 := steps_1_of_step hs3Raw
  have hr3F := reg_of_regs_eq hr3
  by_cases hEqA : sVal = aVal
  · rw [ite_eq_right (by rw [h2_2, h3_2, hEqA]; exact Nat.lt_irrefl _)] at hpc3
    have haBr2 : code[s3.pc]? = some (.branchLt reg3 reg2 (basePc + 9) (basePc + 16)) := by rw [hpc3]; exact hPl 7 _ rfl
    obtain ⟨s4, hs4Raw, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
    have hs4 := steps_1_of_step hs4Raw
    rw [ite_eq_right (by rw [hr3F reg2, hr3F reg3, h2_2, h3_2, hEqA]; exact Nat.lt_irrefl _)] at hpc4
    have haMv1 : code[s4.pc]? = some (.mov reg4 reg1) := by rw [hpc4]; exact hPl 16 _ rfl
    obtain ⟨s5, hs5Raw, hpc5, h4_5, ho5, hd5⟩ := step_mov_at (input := input) haMv1 (by omega)
    have hs5 := steps_1_of_step hs5Raw
    have haGo : code[s5.pc]? = some (.goto (basePc + 19)) := by rw [hpc5, hpc4]; exact hPl 17 _ rfl
    obtain ⟨t, htRaw, hpct, hrt, hdt⟩ := step_goto_at (input := input) haGo (by omega)
    have ht := steps_1_of_step htRaw
    have hr4F := reg_of_regs_eq hr4
    have hrTF := reg_of_regs_eq hrt
    rw [ite_eq_left hEqA]
    refine ⟨10, t, by omega, (hs1.append hs2).append (hs3.append (hs4.append (hs5.append ht))), hpct,
      by rw [hdt, hd5, hd4, hd3, hd2'],
      by rw [hrTF, ho5 reg0 (by intro h; cases h), hr4F, hr3F, h0_2],
      by rw [hrTF, ho5 reg1 (by intro h; cases h), hr4F, hr3F, h1_2],
      by rw [hrTF, ho5 rMeta (by intro h; cases h), hr4F, hr3F, hM2],
      by rw [hrTF, h4_5, hr4F, hr3F, h1_2],
      fun r hr2 hr3 hr4' hr5 => by rw [hrTF, ho5 r hr4', hr4F, hr3F, hPresS2 r hr2 hr3 hr5]⟩
  · rw [ite_eq_right hEqA]
    have hToB : ∃ k1 s4, (k1 = 7 ∨ k1 = 8) ∧ Steps code input k1 st s4 ∧ s4.pc = basePc + 9 ∧
        (reg s4 reg0).val = 0 ∧ (reg s4 reg1).val = 1 ∧ (reg s4 rMeta).val = metaBase ∧
        (reg s4 reg2).val = sVal ∧ s4.data = st.data ∧
        (∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg5 → reg s4 r = reg st r) := by
      by_cases hLt1 : sVal < aVal
      · rw [ite_eq_left (by rw [h2_2, h3_2]; exact hLt1)] at hpc3
        exact ⟨7, s3, Or.inl rfl, (hs1.append hs2).append hs3, hpc3,
          by rw [hr3F, h0_2], by rw [hr3F, h1_2], by rw [hr3F, hM2], by rw [hr3F, h2_2],
          by rw [hd3, hd2'], fun r hr2 hr3 hr5 => by rw [hr3F, hPresS2 r hr2 hr3 hr5]⟩
      · have hGt1 : aVal < sVal := by omega
        rw [ite_eq_right (by rw [h2_2, h3_2]; exact hLt1)] at hpc3
        have haBr2 : code[s3.pc]? = some (.branchLt reg3 reg2 (basePc + 9) (basePc + 16)) := by rw [hpc3]; exact hPl 7 _ rfl
        obtain ⟨s4, hs4Raw, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
        have hs4 := steps_1_of_step hs4Raw
        rw [ite_eq_left (by rw [hr3F reg2, hr3F reg3, h2_2, h3_2]; exact hGt1)] at hpc4
        have hr4F := reg_of_regs_eq hr4
        exact ⟨8, s4, Or.inr rfl, (hs1.append hs2).append (hs3.append hs4), hpc4,
          by rw [hr4F, hr3F, h0_2], by rw [hr4F, hr3F, h1_2], by rw [hr4F, hr3F, hM2],
          by rw [hr4F, hr3F, h2_2], by rw [hd4, hd3, hd2'],
          fun r hr2 hr3 hr5 => by rw [hr4F, hr3F, hPresS2 r hr2 hr3 hr5]⟩
    obtain ⟨k1, s4, hk1, hs4, hpc4, h0_4, h1_4, hM_4, h2_4, hd4, hP4⟩ := hToB
    have hPl2 : Placed code (basePc + 9) (metaLoadInstrs (bits := bits) reg3 reg5 51 (by omega)) :=
      Placed_window hPl 9 rfl
    obtain ⟨s5, hs5, hpc5, hd5, h3_5, hPres5⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl2 (by omega) hpc4 hM_4 (by omega) (by rw [hd4]; exact hB)
    have h2_5 : (reg s5 reg2).val = sVal := by rw [hPres5 reg2 (by intro h; cases h) (by intro h; cases h), h2_4]
    have h0_5 : (reg s5 reg0).val = 0 := by rw [hPres5 reg0 (by intro h; cases h) (by intro h; cases h), h0_4]
    have h1_5 : (reg s5 reg1).val = 1 := by rw [hPres5 reg1 (by intro h; cases h) (by intro h; cases h), h1_4]
    have hM_5 : (reg s5 rMeta).val = metaBase := by rw [hPres5 rMeta (by intro h; cases h) (by intro h; cases h), hM_4]
    have hP5 : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg5 → reg s5 r = reg st r := fun r hr2 hr3 hr5 => by
      rw [hPres5 r hr3 hr5, hP4 r hr2 hr3 hr5]
    have haBr3 : code[s5.pc]? = some (.branchLt reg2 reg3 (basePc + 18) (basePc + 13)) := by rw [hpc5]; exact hPl 12 _ rfl
    obtain ⟨s6, hs6Raw, hpc6, hr6, hd6⟩ := step_branchLt_at (input := input) haBr3 (by split <;> omega)
    have hs6 := steps_1_of_step hs6Raw
    have hr6F := reg_of_regs_eq hr6
    by_cases hEqB : sVal = bVal
    · rw [ite_eq_right (by rw [h2_5, h3_5, hEqB]; exact Nat.lt_irrefl _)] at hpc6
      have haBr4 : code[s6.pc]? = some (.branchLt reg3 reg2 (basePc + 18) (basePc + 14)) := by rw [hpc6]; exact hPl 13 _ rfl
      obtain ⟨s7, hs7Raw, hpc7, hr7, hd7⟩ := step_branchLt_at (input := input) haBr4 (by split <;> omega)
      have hs7 := steps_1_of_step hs7Raw
      rw [ite_eq_right (by rw [hr6F reg2, hr6F reg3, h2_5, h3_5, hEqB]; exact Nat.lt_irrefl _)] at hpc7
      have hr7F := reg_of_regs_eq hr7
      have haAdd : code[s7.pc]? = some (.add reg4 reg1 reg1) := by rw [hpc7]; exact hPl 14 _ rfl
      obtain ⟨s8, hs8Raw, hpc8, h4_8, ho8, hd8⟩ := step_add_at (input := input) haAdd (by omega)
      have hs8 := steps_1_of_step hs8Raw
      have h4Val : (reg s8 reg4).val = 2 := by
        rw [h4_8, add_no_wrap _ _ (by simp only [hr7F, hr6F, h1_5]; omega)]
        simp only [hr7F, hr6F, h1_5]
      have haGo : code[s8.pc]? = some (.goto (basePc + 19)) := by rw [hpc8, hpc7]; exact hPl 15 _ rfl
      obtain ⟨t, htRaw, hpct, hrt, hdt⟩ := step_goto_at (input := input) haGo (by omega)
      have ht := steps_1_of_step htRaw
      have hrTF := reg_of_regs_eq hrt
      rw [ite_eq_left hEqB]
      refine ⟨k1 + 7, t, by rcases hk1 with rfl | rfl <;> omega,
        (by simpa only [Nat.add_assoc] using hs4.append (hs5.append (hs6.append (hs7.append (hs8.append ht))))), hpct,
        by rw [hdt, hd8, hd7, hd6, hd5, hd4],
        by rw [hrTF, ho8 reg0 (by intro h; cases h), hr7F, hr6F, h0_5],
        by rw [hrTF, ho8 reg1 (by intro h; cases h), hr7F, hr6F, h1_5],
        by rw [hrTF, ho8 rMeta (by intro h; cases h), hr7F, hr6F, hM_5],
        by rw [hrTF, h4Val],
        fun r hr2 hr3 hr4' hr5 => by rw [hrTF, ho8 r hr4', hr7F, hr6F, hP5 r hr2 hr3 hr5]⟩
    · rw [ite_eq_right hEqB]
      by_cases hLt2 : sVal < bVal
      · rw [ite_eq_left (by rw [h2_5, h3_5]; exact hLt2)] at hpc6
        have haMv0 : code[s6.pc]? = some (.mov reg4 reg0) := by rw [hpc6]; exact hPl 18 _ rfl
        obtain ⟨t, htRaw, hpct, h4t, hot, hdt⟩ := step_mov_at (input := input) haMv0 (by omega)
        have ht := steps_1_of_step htRaw
        refine ⟨k1 + 5, t, by rcases hk1 with rfl | rfl <;> omega,
          (by simpa only [Nat.add_assoc] using hs4.append (hs5.append (hs6.append ht))), by rw [hpct, hpc6],
          by rw [hdt, hd6, hd5, hd4],
          by rw [hot reg0 (by intro h; cases h), hr6F, h0_5],
          by rw [hot reg1 (by intro h; cases h), hr6F, h1_5],
          by rw [hot rMeta (by intro h; cases h), hr6F, hM_5],
          by rw [h4t, hr6F, h0_5],
          fun r hr2 hr3 hr4' hr5 => by rw [hot r hr4', hr6F, hP5 r hr2 hr3 hr5]⟩
      · have hGt2 : bVal < sVal := by omega
        rw [ite_eq_right (by rw [h2_5, h3_5]; exact hLt2)] at hpc6
        have haBr4 : code[s6.pc]? = some (.branchLt reg3 reg2 (basePc + 18) (basePc + 14)) := by rw [hpc6]; exact hPl 13 _ rfl
        obtain ⟨s7, hs7Raw, hpc7, hr7, hd7⟩ := step_branchLt_at (input := input) haBr4 (by split <;> omega)
        have hs7 := steps_1_of_step hs7Raw
        rw [ite_eq_left (by rw [hr6F reg2, hr6F reg3, h2_5, h3_5]; exact hGt2)] at hpc7
        have hr7F := reg_of_regs_eq hr7
        have haMv0 : code[s7.pc]? = some (.mov reg4 reg0) := by rw [hpc7]; exact hPl 18 _ rfl
        obtain ⟨t, htRaw, hpct, h4t, hot, hdt⟩ := step_mov_at (input := input) haMv0 (by omega)
        have ht := steps_1_of_step htRaw
        refine ⟨k1 + 6, t, by rcases hk1 with rfl | rfl <;> omega,
          (by simpa only [Nat.add_assoc] using hs4.append (hs5.append (hs6.append (hs7.append ht)))), by rw [hpct, hpc7],
          by rw [hdt, hd7, hd6, hd5, hd4],
          by rw [hot reg0 (by intro h; cases h), hr7F, hr6F, h0_5],
          by rw [hot reg1 (by intro h; cases h), hr7F, hr6F, h1_5],
          by rw [hot rMeta (by intro h; cases h), hr7F, hr6F, hM_5],
          by rw [h4t, hr7F, hr6F, h0_5],
          fun r hr2 hr3 hr4' hr5 => by rw [hot r hr4', hr7F, hr6F, hP5 r hr2 hr3 hr5]⟩

end PaperB.RamProgram.ExitSummaryBuild
