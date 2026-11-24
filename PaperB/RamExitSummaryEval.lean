module

public import PaperB.RamExitSummaryIntervalJoin

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 / EX5.2 Stage 4 reusable Word-RAM slices (`PaperB/RamExitSummarySlices.lean`).
-/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
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


/-! ### 8. Stage 4 reusable `Interval` / `Coord` / `Map` Word-RAM slices -/

section Stage4Helpers

section MapEvalSlices

variable {bits : Nat}

def coordEvalInstrs (basePc : Nat) : List (Instr bits 15) :=
  [ .mov reg12 reg3
  , .add reg5 reg2 reg1
  , .add reg5 reg5 reg1
  , .add reg5 reg5 reg1
  , .loadData reg5 reg5
  , .branchLt reg0 reg5 (basePc + 17) (basePc + 6)
  , .loadData reg6 reg2
  , .storeData reg4 reg6
  , .add reg7 reg2 reg1
  , .loadData reg6 reg7
  , .add reg8 reg4 reg1
  , .storeData reg8 reg6
  , .add reg7 reg7 reg1
  , .loadData reg6 reg7
  , .add reg8 reg8 reg1
  , .storeData reg8 reg6
  , .goto (basePc + 46)
  , .branchLt reg1 reg5 (basePc + 18) (basePc + 21)
  , .add reg3 reg3 reg1
  , .add reg3 reg3 reg1
  , .add reg3 reg3 reg1
  ] ++ intervalJoinInstrs (basePc + 21) ++
  [ .mov reg3 reg12 ]

theorem coordEvalInstrs_length (basePc : Nat) :
    (coordEvalInstrs (bits := bits) basePc).length = 47 := by
  simp [coordEvalInstrs, intervalJoinInstrs_length]

theorem coordEvalInstrs_nonHalt (basePc : Nat) :
    (coordEvalInstrs (bits := bits) basePc).all sliceNonHalt = true := by
  rfl

def mapEvalInstrs (basePc : Nat) : List (Instr bits 15) :=
  coordEvalInstrs basePc ++
  [ .add reg12 reg1 reg1
  , .add reg12 reg12 reg1
  , .add reg4 reg4 reg12
  , .add reg12 reg12 reg1
  , .add reg2 reg2 reg12
  ] ++ coordEvalInstrs (basePc + 52)

theorem mapEvalInstrs_length (basePc : Nat) :
    (mapEvalInstrs (bits := bits) basePc).length = 99 := by
  simp [mapEvalInstrs, coordEvalInstrs_length]

theorem mapEvalInstrs_nonHalt (basePc : Nat) :
    (mapEvalInstrs (bits := bits) basePc).all sliceNonHalt = true := by
  rfl

variable {inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_coordEval {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (hPl : Placed code basePc (coordEvalInstrs (bits := bits) basePc))
    (hSz : basePc + 47 < code.size)
    (coordAddr inValAddr outIntAddr : Nat) (c : Coord) (xs : Values)
    (hFitC : coordAddr + 3 < 2 ^ bits) (hFitV : inValAddr + 5 < 2 ^ bits)
    (hFitO : outIntAddr + 2 < 2 ^ bits) (hOutLt : outIntAddr + 2 < workCap)
    (hDisjC : outIntAddr + 3 ≤ coordAddr ∨ coordAddr + 4 ≤ outIntAddr)
    (_hDisjV : outIntAddr + 3 ≤ inValAddr ∨ inValAddr + 6 ≤ outIntAddr)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hr2 : (reg st reg2).val = coordAddr) (hr3 : (reg st reg3).val = inValAddr)
    (hr4 : (reg st reg4).val = outIntAddr)
    (hC : CoordWordsAt st.data coordAddr c) (hXs : ValuesWordsAt st.data inValAddr xs) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 36 ∧ Steps code input k st t ∧ t.pc = basePc + 47 ∧
      IntervalWordsAt t.data outIntAddr (Coord.eval c xs) ∧
      (∀ r : Fin 15, r = reg0 ∨ r = reg1 ∨ r = reg2 ∨ r = reg3 ∨ r = reg4 ∨
        r = reg13 ∨ r = rMeta → reg t r = reg st r) ∧
      (∀ j, (j < outIntAddr ∨ outIntAddr + 3 ≤ j) → t.data[j]? = st.data[j]?) := by
  obtain ⟨s1, hs1, hpc1, h12_1, ho1, hd1⟩ := step_mov_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by omega)
  have h2_1 : (reg s1 reg2).val = coordAddr := by rw [ho1 reg2 (by intro h; cases h), hr2]
  have h1_1 : (reg s1 reg1).val = 1 := by rw [ho1 reg1 (by intro h; cases h), hr1]
  obtain ⟨s2, hs2, hpc2, h5_2, ho2, hd2⟩ := step_add_at (input := input)
    (by rw [hpc1, hpc]; exact hPl 1 _ rfl) (by omega)
  have h5Val2 : (reg s2 reg5).val = coordAddr + 1 := by
    rw [h5_2, add_no_wrap _ _ (by rw [h2_1, h1_1]; omega), h2_1, h1_1]
  have h1_2 : (reg s2 reg1).val = 1 := by rw [ho2 reg1 (by intro h; cases h), h1_1]
  obtain ⟨s3, hs3, hpc3, h5_3, ho3, hd3⟩ := step_add_at (input := input)
    (by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl) (by omega)
  have h5Val3 : (reg s3 reg5).val = coordAddr + 2 := by
    rw [h5_3, add_no_wrap _ _ (by rw [h5Val2, h1_2]; omega), h5Val2, h1_2]
  have h1_3 : (reg s3 reg1).val = 1 := by rw [ho3 reg1 (by intro h; cases h), h1_2]
  obtain ⟨s4, hs4, hpc4, h5_4, ho4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl) (by omega)
  have h5Val4 : (reg s4 reg5).val = coordAddr + 3 := by
    rw [h5_4, add_no_wrap _ _ (by rw [h5Val3, h1_3]; omega), h5Val3, h1_3]
  obtain ⟨wSl, hwSl, hwSlV⟩ := Option.map_eq_some_iff.mp hC.2
  have hd4' : s4.data = st.data := by rw [hd4, hd3, hd2, hd1]
  obtain ⟨s5, hs5, hpc5, h5_5, ho5, hd5⟩ := step_loadData_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl) (by omega)
    (by rw [h5Val4, hd4']; exact hwSl)
  have hPres5 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg12 → reg s5 r = reg st r := fun r hr5 hr12 => by
    rw [ho5 r hr5, ho4 r hr5, ho3 r hr5, ho2 r hr5, ho1 r hr12]
  have h12_5 : reg s5 reg12 = reg st reg3 := by
    rw [ho5 reg12 (by intro h; cases h), ho4 reg12 (by intro h; cases h),
      ho3 reg12 (by intro h; cases h), ho2 reg12 (by intro h; cases h), h12_1]
  have h0_5 : (reg s5 reg0).val = 0 := by rw [hPres5 reg0 (by intro h; cases h) (by intro h; cases h), hr0]
  have h1_5 : (reg s5 reg1).val = 1 := by rw [hPres5 reg1 (by intro h; cases h) (by intro h; cases h), hr1]
  have h2_5 : (reg s5 reg2).val = coordAddr := by rw [hPres5 reg2 (by intro h; cases h) (by intro h; cases h), hr2]
  have h3_5 : (reg s5 reg3).val = inValAddr := by rw [hPres5 reg3 (by intro h; cases h) (by intro h; cases h), hr3]
  have h4_5 : (reg s5 reg4).val = outIntAddr := by rw [hPres5 reg4 (by intro h; cases h) (by intro h; cases h), hr4]
  have hd5' : s5.data = st.data := by rw [hd5, hd4']
  have hPre5 : Steps code input 5 st s5 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5))))
  obtain ⟨s6, hs6, hpc6, hr6, hd6⟩ := step_branchLt_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl) (by split <;> omega)
  have hr6F := reg_of_regs_eq hr6
  rcases hSlot : c.slot with _ | idx
  · rw [ite_eq_right (by rw [h0_5, h5_5, hwSlV, hSlot]; simp)] at hpc6
    have hcAt0 : (st.data[coordAddr]?).map Fin.val =
        some (match c.base with | .empty => 0 | .span _ _ => 1) := by
      have hb := hC.1
      cases hBase : c.base <;> rw [hBase] at hb <;> exact hb.1
    have hcAt1 : (st.data[coordAddr + 1]?).map Fin.val =
        some (match c.base with | .empty => 0 | .span lo _ => lo) := by
      have hb := hC.1
      cases hBase : c.base <;> rw [hBase] at hb <;> exact hb.2.1
    have hcAt2 : (st.data[coordAddr + 2]?).map Fin.val =
        some (match c.base with | .empty => 0 | .span _ hi => hi) := by
      have hb := hC.1
      cases hBase : c.base <;> rw [hBase] at hb <;> exact hb.2.2
    obtain ⟨wc0, hwc0, hwc0V⟩ := Option.map_eq_some_iff.mp hcAt0
    obtain ⟨wc1, hwc1, hwc1V⟩ := Option.map_eq_some_iff.mp hcAt1
    obtain ⟨wc2, hwc2, hwc2V⟩ := Option.map_eq_some_iff.mp hcAt2
    obtain ⟨s7, hs7, hpc7, h6_7, ho7, hd7⟩ := step_loadData_at (input := input)
      (by rw [hpc6]; exact hPl 6 _ rfl) (by omega)
      (by rw [hr6F, h2_5, hd6, hd5']; exact hwc0)
    have h4_7 : (reg s7 reg4).val = outIntAddr := by
      rw [ho7 reg4 (by intro h; cases h), hr6F, h4_5]
    have hLt0 : (reg s7 reg4).val < s7.data.size := lt_data_size (by rw [h4_7]; omega)
    obtain ⟨s8, hs8, hpc8, hr8, hd8⟩ := step_storeData_opaque (input := input)
      (by rw [hpc7, hpc6]; exact hPl 7 _ rfl) hLt0 (by omega)
    have hr8F := reg_of_regs_eq hr8
    have h2_8 : (reg s8 reg2).val = coordAddr := by
      rw [hr8F, ho7 reg2 (by intro h; cases h), hr6F, h2_5]
    have h1_8 : (reg s8 reg1).val = 1 := by
      rw [hr8F, ho7 reg1 (by intro h; cases h), hr6F, h1_5]
    obtain ⟨s9, hs9, hpc9, h7_9, ho9, hd9⟩ := step_add_at (input := input)
      (by rw [hpc8, hpc7, hpc6]; exact hPl 8 _ rfl) (by omega)
    have hC1 : (reg s9 reg7).val = coordAddr + 1 := by
      rw [h7_9, add_no_wrap _ _ (by rw [h2_8, h1_8]; omega), h2_8, h1_8]
    have hNeC1 : coordAddr + 1 ≠ (reg s7 reg4).val := by rw [h4_7]; rcases hDisjC with h | h <;> omega
    have hwc1_9 : s9.data[(reg s9 reg7).val]? = some wc1 := by
      rw [hC1, hd9, hd8, Array.getElem?_set_ne hLt0 hNeC1.symm, hd7, hd6, hd5']; exact hwc1
    obtain ⟨s10, hs10, hpc10, h6_10, ho10, hd10⟩ := step_loadData_at (input := input)
      (by rw [hpc9, hpc8, hpc7, hpc6]; exact hPl 9 _ rfl) (by omega) hwc1_9
    have h4_10 : (reg s10 reg4).val = outIntAddr := by
      rw [ho10 reg4 (by intro h; cases h), ho9 reg4 (by intro h; cases h), hr8F, h4_7]
    have h1_10 : (reg s10 reg1).val = 1 := by
      rw [ho10 reg1 (by intro h; cases h), ho9 reg1 (by intro h; cases h), h1_8]
    obtain ⟨s11, hs11, hpc11, h8_11, ho11, hd11⟩ := step_add_at (input := input)
      (by rw [hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 10 _ rfl) (by omega)
    have hO1 : (reg s11 reg8).val = outIntAddr + 1 := by
      rw [h8_11, add_no_wrap _ _ (by rw [h4_10, h1_10]; omega), h4_10, h1_10]
    have hLt1 : (reg s11 reg8).val < s11.data.size := lt_data_size (by rw [hO1]; omega)
    obtain ⟨s12, hs12, hpc12, hr12, hd12⟩ := step_storeData_opaque (input := input)
      (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 11 _ rfl) hLt1 (by omega)
    have hr12F := reg_of_regs_eq hr12
    have h7_12 : (reg s12 reg7).val = coordAddr + 1 := by
      rw [hr12F, ho11 reg7 (by intro h; cases h), ho10 reg7 (by intro h; cases h), hC1]
    have h1_12 : (reg s12 reg1).val = 1 := by rw [hr12F, ho11 reg1 (by intro h; cases h), h1_10]
    obtain ⟨s13, hs13, hpc13, h7_13, ho13, hd13⟩ := step_add_at (input := input)
      (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 12 _ rfl) (by omega)
    have hC2 : (reg s13 reg7).val = coordAddr + 2 := by
      rw [h7_13, add_no_wrap _ _ (by rw [h7_12, h1_12]; omega), h7_12, h1_12]
    have hNeC2a : coordAddr + 2 ≠ (reg s11 reg8).val := by rw [hO1]; rcases hDisjC with h | h <;> omega
    have hNeC2b : coordAddr + 2 ≠ (reg s7 reg4).val := by rw [h4_7]; rcases hDisjC with h | h <;> omega
    have hwc2_13 : s13.data[(reg s13 reg7).val]? = some wc2 := by
      rw [hC2, hd13, hd12, Array.getElem?_set_ne hLt1 hNeC2a.symm, hd11, hd10, hd9, hd8,
        Array.getElem?_set_ne hLt0 hNeC2b.symm, hd7, hd6, hd5']; exact hwc2
    obtain ⟨s14, hs14, hpc14, h6_14, ho14, hd14⟩ := step_loadData_at (input := input)
      (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 13 _ rfl) (by omega) hwc2_13
    have h8_14 : (reg s14 reg8).val = outIntAddr + 1 := by
      rw [ho14 reg8 (by intro h; cases h), ho13 reg8 (by intro h; cases h), hr12F, hO1]
    have h1_14 : (reg s14 reg1).val = 1 := by rw [ho14 reg1 (by intro h; cases h), ho13 reg1 (by intro h; cases h), h1_12]
    obtain ⟨s15, hs15, hpc15, h8_15, ho15, hd15⟩ := step_add_at (input := input)
      (by rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 14 _ rfl) (by omega)
    have hO2 : (reg s15 reg8).val = outIntAddr + 2 := by
      rw [h8_15, add_no_wrap _ _ (by rw [h8_14, h1_14]; omega), h8_14, h1_14]
    have hLt2 : (reg s15 reg8).val < s15.data.size := lt_data_size (by rw [hO2]; omega)
    obtain ⟨s16, hs16, hpc16, hr16, hd16⟩ := step_storeData_opaque (input := input)
      (by rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 15 _ rfl) hLt2 (by omega)
    have hr16F := reg_of_regs_eq hr16
    obtain ⟨s17, hs17, hpc17, hr17, hd17⟩ := step_goto_at (input := input)
      (by rw [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPl 16 _ rfl) (by omega)
    have hr17F := reg_of_regs_eq hr17
    obtain ⟨t, hs18, hpct, hrt, hot, hdt⟩ := step_mov_at (input := input)
      (by rw [hpc17]; exact hPl 46 _ rfl) (by omega)
    have hAtT : ∀ a, t.data[a]? =
        if a = outIntAddr + 2 then some (reg s15 reg6)
        else if a = outIntAddr + 1 then some (reg s11 reg6)
        else if a = outIntAddr then some (reg s7 reg6)
        else st.data[a]? := by
      intro a
      rw [hdt, hd17, hd16]
      by_cases ha2 : a = outIntAddr + 2
      · subst ha2; rw [ite_eq_left rfl, ← hO2, Array.getElem?_set_self hLt2]
      · rw [ite_eq_right ha2, Array.getElem?_set_ne hLt2 (by rw [hO2]; exact Ne.symm ha2),
          hd15, hd14, hd13, hd12]
        by_cases ha1 : a = outIntAddr + 1
        · subst ha1; rw [ite_eq_left rfl, ← hO1, Array.getElem?_set_self hLt1]
        · rw [ite_eq_right ha1, Array.getElem?_set_ne hLt1 (by rw [hO1]; exact Ne.symm ha1),
            hd11, hd10, hd9, hd8]
          by_cases ha0 : a = outIntAddr
          · subst ha0; rw [ite_eq_left rfl, ← h4_7, Array.getElem?_set_self hLt0]
          · rw [ite_eq_right ha0, Array.getElem?_set_ne hLt0 (by rw [h4_7]; exact Ne.symm ha0),
              hd7, hd6, hd5']
    have hPresT : ∀ r : Fin 15, r ≠ reg3 → r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 →
        r ≠ reg12 → reg t r = reg st r := fun r hr3 hr5 hr6 hr7 hr8 hr12 => by
      rw [hot r hr3, hr17F, hr16F, ho15 r hr8, ho14 r hr6, ho13 r hr7, hr12F, ho11 r hr8,
        ho10 r hr6, ho9 r hr7, hr8F, ho7 r hr6, hr6F, hPres5 r hr5 hr12]
    have h3T : reg t reg3 = reg st reg3 := by
      rw [hrt, hr17F, hr16F, ho15 reg12 (by intro h; cases h), ho14 reg12 (by intro h; cases h),
        ho13 reg12 (by intro h; cases h), hr12F, ho11 reg12 (by intro h; cases h),
        ho10 reg12 (by intro h; cases h), ho9 reg12 (by intro h; cases h), hr8F,
        ho7 reg12 (by intro h; cases h), hr6F, h12_5]
    have hOutEval : IntervalWordsAt t.data outIntAddr (Coord.eval c xs) := by
      have hEvalEq : Coord.eval c xs = c.base := by simp [Coord.eval, hSlot]
      rw [hEvalEq]
      have hs76 : (reg s7 reg6).val = wc0.val := by rw [h6_7]
      have hs116 : (reg s11 reg6).val = wc1.val := by rw [ho11 reg6 (by intro h; cases h), h6_10]
      have hs156 : (reg s15 reg6).val = wc2.val := by rw [ho15 reg6 (by intro h; cases h), h6_14]
      cases hcB : c.base with
      | empty =>
        rw [hcB] at hwc0V hwc1V hwc2V
        refine ⟨?_, ?_, ?_⟩
        · rw [hAtT outIntAddr, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs76, hwc0V]
        · rw [hAtT (outIntAddr + 1), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs116, hwc1V]
        · rw [hAtT (outIntAddr + 2), ite_eq_left rfl, Option.map_some, hs156, hwc2V]
      | span lo hi =>
        rw [hcB] at hwc0V hwc1V hwc2V
        refine ⟨?_, ?_, ?_⟩
        · rw [hAtT outIntAddr, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs76, hwc0V]
        · rw [hAtT (outIntAddr + 1), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs116, hwc1V]
        · rw [hAtT (outIntAddr + 2), ite_eq_left rfl, Option.map_some, hs156, hwc2V]
    have hStepRest : Steps code input 13 s5 t :=
      Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15
          (Steps.cons hs16 (Steps.cons hs17 (steps_1_of_step hs18))))))))))))
    refine ⟨5 + 13, t, by omega, hPre5.append hStepRest, by rw [hpct, hpc17], hOutEval, fun r hr => ?_, fun j hj => ?_⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hPresT reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      · exact hPresT reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      · exact hPresT reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      · exact h3T
      · exact hPresT reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      · exact hPresT reg13 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      · exact hPresT rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    · rw [hAtT j, ite_eq_right (by rcases hj with h | h <;> omega),
        ite_eq_right (by rcases hj with h | h <;> omega), ite_eq_right (by rcases hj with h | h <;> omega)]
  · have hPosSl : 0 < (match some idx with | none => 0 | some 0 => 1 | some 1 => 2) := by
      rcases fin2_cases idx with rfl | rfl <;> simp
    rw [ite_eq_left (by rw [h0_5, h5_5, hwSlV, hSlot]; exact hPosSl)] at hpc6
    have hPlJoin : Placed code (basePc + 21) (intervalJoinInstrs (bits := bits) (basePc + 21)) := by
      have hL := Placed_append_left (by unfold coordEvalInstrs at hPl; exact hPl)
      have hR := Placed_append_right hL
      simpa only [List.length_cons, List.length_nil] using hR
    obtain ⟨s7, hs7, hpc7, hr7, hd7⟩ := step_branchLt_at (input := input)
      (by rw [hpc6]; exact hPl 17 _ rfl) (by split <;> omega)
    have hr7F := reg_of_regs_eq hr7
    have hOne6 : (reg s6 reg1).val = 1 := by rw [hr6F reg1, h1_5]
    have hSlotWord6 : reg s6 reg5 = wSl := by rw [hr6F reg5, h5_5]
    have hSrcAndSteps : ∃ (kPre : Nat) (sJ : State DomL),
        kPre ≤ 3 ∧ Steps code input kPre s7 sJ ∧ sJ.pc = basePc + 21 ∧ sJ.data = st.data ∧
        (reg sJ reg3).val = inValAddr + 3 * idx.val ∧
        IntervalWordsAt sJ.data (inValAddr + 3 * idx.val) (xs.get idx) ∧
        ∀ r : Fin 15, r ≠ reg3 → reg sJ r = reg s6 r := by
      rcases fin2_cases idx with h0Eq | h1Eq
      · subst h0Eq
        rw [ite_eq_right (by
          simpa only [hOne6, hSlotWord6, hwSlV, hSlot] using (show ¬ (1 : Nat) < 1 from by decide))] at hpc7
        exact ⟨0, s7, Nat.zero_le _, Steps.zero s7, hpc7, by rw [hd7, hd6, hd5'],
          by rw [hr7F, hr6F, h3_5]; rfl,
          by rw [hd7, hd6, hd5']; exact hXs.1, fun r _ => hr7F r⟩
      · subst h1Eq
        rw [ite_eq_left (by
          simpa only [hOne6, hSlotWord6, hwSlV, hSlot] using (show (1 : Nat) < 2 from by decide))] at hpc7
        have h3_7 : (reg s7 reg3).val = inValAddr := by rw [hr7F, hr6F, h3_5]
        have h1_7 : (reg s7 reg1).val = 1 := by rw [hr7F, hr6F, h1_5]
        obtain ⟨sa, hsa, hpca, h3a, hoa, hda⟩ := step_add_at (input := input)
          (by rw [hpc7]; exact hPl 18 _ rfl) (by omega)
        have h3aV : (reg sa reg3).val = inValAddr + 1 := by
          rw [h3a, add_no_wrap _ _ (by rw [h3_7, h1_7]; omega), h3_7, h1_7]
        have h1a : (reg sa reg1).val = 1 := by rw [hoa reg1 (by intro h; cases h), h1_7]
        obtain ⟨sb, hsb, hpcb, h3b, hob, hdb⟩ := step_add_at (input := input)
          (by rw [hpca, hpc7]; exact hPl 19 _ rfl) (by omega)
        have h3bV : (reg sb reg3).val = inValAddr + 2 := by
          rw [h3b, add_no_wrap _ _ (by rw [h3aV, h1a]; omega), h3aV, h1a]
        have h1b : (reg sb reg1).val = 1 := by rw [hob reg1 (by intro h; cases h), h1a]
        obtain ⟨sc, hsc, hpcc, h3c, hoc, hdc⟩ := step_add_at (input := input)
          (by rw [hpcb, hpca, hpc7]; exact hPl 20 _ rfl) (by omega)
        refine ⟨3, sc, Nat.le_refl _, Steps.cons hsa (Steps.cons hsb (steps_1_of_step hsc)),
          by omega, by rw [hdc, hdb, hda, hd7, hd6, hd5'],
          by rw [h3c, add_no_wrap _ _ (by rw [h3bV, h1b]; omega), h3bV, h1b]; omega,
          by rw [hdc, hdb, hda, hd7, hd6, hd5']; exact hXs.2,
          fun r hr => by rw [hoc r hr, hob r hr, hoa r hr, hr7F]⟩
    obtain ⟨kPre, sJ, hkPre, hStepsPre, hpcJ, hdJ', h3J, hBInt, hPresJ⟩ := hSrcAndSteps
    have hFitSrcB' : inValAddr + 3 * idx.val + 2 < 2 ^ bits := by
      rcases fin2_cases idx with rfl | rfl <;> simp <;> omega
    obtain ⟨kJ, sPost, hkJ, hStepsJ, hpcPost, hOutJ, hPresPost, hFrJ⟩ :=
      run_intervalJoin (basePc + 21) hPlJoin (by omega) coordAddr (inValAddr + 3 * idx.val) outIntAddr
        c.base (xs.get idx) (by omega) hFitSrcB' hFitO hOutLt sJ hpcJ
        (by rw [hPresJ reg0 (by intro h; cases h), hr6F, h0_5])
        (by rw [hPresJ reg1 (by intro h; cases h), hr6F, h1_5])
        (by rw [hPresJ reg2 (by intro h; cases h), hr6F, h2_5])
        h3J
        (by rw [hPresJ reg4 (by intro h; cases h), hr6F, h4_5])
        (by rw [hdJ']; exact hC.1) hBInt
    obtain ⟨t, hsFin, hpct, hrt, hot, hdt⟩ := step_mov_at (input := input)
      (by rw [hpcPost]; exact hPl 46 _ rfl) (by omega)
    have hEvalEq : Coord.eval c xs = Interval.join c.base (xs.get idx) := by
      simp [Coord.eval, hSlot]
    refine ⟨5 + 2 + kPre + kJ + 1, t, by omega,
      ((((hPre5.append (Steps.cons hs6 (steps_1_of_step hs7))).append
        hStepsPre).append hStepsJ).append (steps_1_of_step hsFin)),
      by omega, ?_, fun r hr => ?_, fun j hj => ?_⟩
    · rw [hdt, hEvalEq]; exact hOutJ
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hot reg0 (by intro h; cases h), hPresPost reg0 (by decide),
          hPresJ reg0 (by intro h; cases h), hr6F, hPres5 reg0 (by decide) (by decide)]
      · rw [hot reg1 (by intro h; cases h), hPresPost reg1 (by decide),
          hPresJ reg1 (by intro h; cases h), hr6F, hPres5 reg1 (by decide) (by decide)]
      · rw [hot reg2 (by intro h; cases h), hPresPost reg2 (by decide),
          hPresJ reg2 (by intro h; cases h), hr6F, hPres5 reg2 (by decide) (by decide)]
      · rw [hrt, hPresPost reg12 (by decide), hPresJ reg12 (by intro h; cases h), hr6F, h12_5]
      · rw [hot reg4 (by intro h; cases h), hPresPost reg4 (by decide),
          hPresJ reg4 (by intro h; cases h), hr6F, hPres5 reg4 (by decide) (by decide)]
      · rw [hot reg13 (by intro h; cases h), hPresPost reg13 (by decide),
          hPresJ reg13 (by intro h; cases h), hr6F, hPres5 reg13 (by decide) (by decide)]
      · rw [hot rMeta (by intro h; cases h), hPresPost rMeta (by decide),
          hPresJ rMeta (by intro h; cases h), hr6F, hPres5 rMeta (by decide) (by decide)]
    · rw [hdt, hFrJ j hj, hdJ']

theorem run_mapEval {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (hPl : Placed code basePc (mapEvalInstrs (bits := bits) basePc))
    (hSz : basePc + 99 < code.size)
    (mapAddr inValAddr outValAddr : Nat) (m : Map) (xs : Values)
    (hFitM : mapAddr + 7 < 2 ^ bits) (hFitV : inValAddr + 5 < 2 ^ bits)
    (hFitO : outValAddr + 5 < 2 ^ bits) (hOutLt : outValAddr + 5 < workCap)
    (hDisjM : outValAddr + 6 ≤ mapAddr ∨ mapAddr + 8 ≤ outValAddr)
    (hDisjV : outValAddr + 6 ≤ inValAddr ∨ inValAddr + 6 ≤ outValAddr)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hr2 : (reg st reg2).val = mapAddr) (hr3 : (reg st reg3).val = inValAddr)
    (hr4 : (reg st reg4).val = outValAddr)
    (hM : MapWordsAt st.data mapAddr m) (hXs : ValuesWordsAt st.data inValAddr xs) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 77 ∧ Steps code input k st t ∧ t.pc = basePc + 99 ∧
      ValuesWordsAt t.data outValAddr (Map.eval m xs) ∧
      (∀ r : Fin 15, r = reg0 ∨ r = reg1 ∨ r = reg3 ∨ r = reg13 ∨ r = rMeta → reg t r = reg st r) ∧
      (∀ j, (j < outValAddr ∨ outValAddr + 6 ≤ j) → t.data[j]? = st.data[j]?) := by
  have hPl1 : Placed code basePc (coordEvalInstrs (bits := bits) basePc) :=
    Placed_append_left (Placed_append_left (by unfold mapEvalInstrs at hPl; exact hPl))
  have hPlR1 := Placed_append_right (by unfold mapEvalInstrs at hPl; exact hPl)
  have hPlMid : Placed code (basePc + 47)
      ([Instr.add reg12 reg1 reg1, .add reg12 reg12 reg1, .add reg4 reg4 reg12,
        .add reg12 reg12 reg1, .add reg2 reg2 reg12] : List (Instr bits 15)) := by
    have hL := Placed_append_left (by unfold mapEvalInstrs at hPl; exact hPl)
    have hM := Placed_append_right hL
    rwa [coordEvalInstrs_length] at hM
  have hPl2 : Placed code (basePc + 52) (coordEvalInstrs (bits := bits) (basePc + 52)) := by
    have hL := Placed_append_left (by unfold mapEvalInstrs at hPl; exact hPl)
    rw [List.length_append, coordEvalInstrs_length,
      show ([Instr.add reg12 reg1 reg1, .add reg12 reg12 reg1, .add reg4 reg4 reg12,
        .add reg12 reg12 reg1, .add reg2 reg2 reg12] : List (Instr bits 15)).length = 5 by rfl] at hPlR1
    exact hPlR1
  obtain ⟨k1, s1, hk1, hSteps1, hpc1, hOut1, hPres1, hFr1⟩ :=
    run_coordEval basePc hPl1 (by omega) mapAddr inValAddr outValAddr m.x0 xs
      (by omega) hFitV (by omega) (by omega)
      (by rcases hDisjM with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      (by rcases hDisjV with h | h; exact Or.inl (by omega); exact Or.inr h)
      st hpc hr0 hr1 hr2 hr3 hr4 hM.1 hXs
  have h1_1 : (reg s1 reg1).val = 1 := by rw [hPres1 reg1 (Or.inr (Or.inl rfl)), hr1]
  have h2_1 : (reg s1 reg2).val = mapAddr := by rw [hPres1 reg2 (Or.inr (Or.inr (Or.inl rfl))), hr2]
  have h4_1 : (reg s1 reg4).val = outValAddr := by rw [hPres1 reg4 (by decide), hr4]
  obtain ⟨s2, hs2, hpc2, h12_2, ho2, hd2⟩ := step_add_at (input := input)
    (by rw [hpc1]; exact hPlMid 0 _ rfl) (by omega)
  have h12Val2 : (reg s2 reg12).val = 2 := by rw [h12_2, add_no_wrap _ _ (by rw [h1_1]; omega), h1_1]
  have h1_2 : (reg s2 reg1).val = 1 := by rw [ho2 reg1 (by intro h; cases h), h1_1]
  obtain ⟨s3, hs3, hpc3, h12_3, ho3, hd3⟩ := step_add_at (input := input)
    (by rw [hpc2, hpc1]; exact hPlMid 1 _ rfl) (by omega)
  have h12Val3 : (reg s3 reg12).val = 3 := by
    rw [h12_3, add_no_wrap _ _ (by rw [h12Val2, h1_2]; omega), h12Val2, h1_2]
  have h4_3 : (reg s3 reg4).val = outValAddr := by
    rw [ho3 reg4 (by intro h; cases h), ho2 reg4 (by intro h; cases h), h4_1]
  obtain ⟨s4, hs4, hpc4, h4_4, ho4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3, hpc2, hpc1]; exact hPlMid 2 _ rfl) (by omega)
  have h4Val4 : (reg s4 reg4).val = outValAddr + 3 := by
    rw [h4_4, add_no_wrap _ _ (by rw [h4_3, h12Val3]; omega), h4_3, h12Val3]
  have h12_4 : (reg s4 reg12).val = 3 := by rw [ho4 reg12 (by intro h; cases h), h12Val3]
  have h1_4 : (reg s4 reg1).val = 1 := by rw [ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), h1_2]
  obtain ⟨s5, hs5, hpc5, h12_5, ho5, hd5⟩ := step_add_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1]; exact hPlMid 3 _ rfl) (by omega)
  have h12Val5 : (reg s5 reg12).val = 4 := by
    rw [h12_5, add_no_wrap _ _ (by rw [h12_4, h1_4]; omega), h12_4, h1_4]
  have h2_5 : (reg s5 reg2).val = mapAddr := by
    rw [ho5 reg2 (by intro h; cases h), ho4 reg2 (by intro h; cases h),
      ho3 reg2 (by intro h; cases h), ho2 reg2 (by intro h; cases h), h2_1]
  obtain ⟨s6, hs6, hpc6, h2_6, ho6, hd6⟩ := step_add_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPlMid 4 _ rfl) (by omega)
  have h2Val6 : (reg s6 reg2).val = mapAddr + 4 := by
    rw [h2_6, add_no_wrap _ _ (by rw [h2_5, h12Val5]; omega), h2_5, h12Val5]
  have hPresMid : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg4 → r ≠ reg12 → reg s6 r = reg s1 r :=
    fun r hr2 hr4 hr12 => by rw [ho6 r hr2, ho5 r hr12, ho4 r hr4, ho3 r hr12, ho2 r hr12]
  have hd6' : s6.data = s1.data := by rw [hd6, hd5, hd4, hd3, hd2]
  have hStepMid : Steps code input 5 s1 s6 :=
    Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (steps_1_of_step hs6))))
  have hM1_6 : CoordWordsAt s6.data (mapAddr + 4) m.x1 := by
    refine coordWordsAt_frame (fun i hi => ?_) hM.2
    rw [hd6', hFr1 _ (by rcases hDisjM with h | h; exact Or.inr (by omega); exact Or.inl (by omega))]
  have hXs_6 : ValuesWordsAt s6.data inValAddr xs := by
    refine valuesWordsAt_frame (fun i hi => ?_) hXs
    rw [hd6', hFr1 _ (by rcases hDisjV with h | h; exact Or.inr (by omega); exact Or.inl (by omega))]
  obtain ⟨k2, t, hk2, hSteps2, hpc2', hOut2, hPres2, hFr2⟩ :=
    run_coordEval (basePc + 52) hPl2 (by omega) (mapAddr + 4) inValAddr (outValAddr + 3) m.x1 xs
      (by omega) hFitV (by omega) hOutLt
      (by rcases hDisjM with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      (by rcases hDisjV with h | h; exact Or.inl h; exact Or.inr (by omega))
      s6 (by omega)
      (by rw [hPresMid reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg0 (Or.inl rfl), hr0])
      (by rw [hPresMid reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_1])
      h2Val6
      (by rw [hPresMid reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg3 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hr3])
      (by rw [ho6 reg4 (by intro h; cases h), ho5 reg4 (by intro h; cases h), h4Val4])
      hM1_6 hXs_6
  refine ⟨k1 + 5 + k2, t, by omega, (hSteps1.append hStepMid).append hSteps2, by omega, ⟨?_, hOut2⟩,
    fun r hr => ?_, fun j hj => ?_⟩
  · exact intervalWordsAt_frame (fun i hi => by
      rw [hFr2 _ (Or.inl (by omega)), hd6']) hOut1
  · rcases hr with rfl | rfl | rfl | rfl | rfl
    · rw [hPres2 reg0 (Or.inl rfl), hPresMid reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg0 (Or.inl rfl)]
    · rw [hPres2 reg1 (Or.inr (Or.inl rfl)), hPresMid reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg1 (Or.inr (Or.inl rfl))]
    · rw [hPres2 reg3 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        hPresMid reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg3 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
    · rw [hPres2 reg13 (by decide),
        hPresMid reg13 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg13 (by decide)]
    · rw [hPres2 rMeta (by decide),
        hPresMid rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 rMeta (by decide)]
  · rw [hFr2 j (by rcases hj with h | h; exact Or.inl (by omega); exact Or.inr (by omega)), hd6',
      hFr1 j (by rcases hj with h | h; exact Or.inl h; exact Or.inr (by omega))]

end MapEvalSlices

end Stage4Helpers

end PaperB.RamProgram.ExitSummaryBuild
