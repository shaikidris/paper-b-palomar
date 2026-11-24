module

public import PaperB.RamExitSummaryEval

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

section MapEvalAndComposeSlices

variable {bits : Nat}

def coordComposeInstrs (basePc : Nat) : List (Instr bits 15) :=
  [ .mov reg12 reg2
  , .mov reg13 reg3
  , .add reg5 reg3 reg1
  , .add reg5 reg5 reg1
  , .add reg5 reg5 reg1
  , .loadData reg5 reg5
  , .branchLt reg0 reg5 (basePc + 22) (basePc + 7)
  , .loadData reg6 reg3
  , .storeData reg4 reg6
  , .add reg7 reg3 reg1
  , .loadData reg6 reg7
  , .add reg8 reg4 reg1
  , .storeData reg8 reg6
  , .add reg7 reg7 reg1
  , .loadData reg6 reg7
  , .add reg8 reg8 reg1
  , .storeData reg8 reg6
  , .add reg7 reg7 reg1
  , .loadData reg6 reg7
  , .add reg8 reg8 reg1
  , .storeData reg8 reg6
  , .goto (basePc + 60)
  , .branchLt reg1 reg5 (basePc + 23) (basePc + 27)
  , .add reg2 reg2 reg1
  , .add reg2 reg2 reg1
  , .add reg2 reg2 reg1
  , .add reg2 reg2 reg1
  , .add reg6 reg2 reg1
  , .add reg6 reg6 reg1
  , .add reg6 reg6 reg1
  , .loadData reg6 reg6
  , .add reg7 reg4 reg1
  , .add reg7 reg7 reg1
  , .add reg7 reg7 reg1
  , .storeData reg7 reg6
  ] ++ intervalJoinInstrs (basePc + 35) ++
  [ .mov reg2 reg12
  , .mov reg3 reg13
  ]

theorem coordComposeInstrs_length (basePc : Nat) :
    (coordComposeInstrs (bits := bits) basePc).length = 62 := by
  simp [coordComposeInstrs, intervalJoinInstrs_length]

theorem coordComposeInstrs_nonHalt (basePc : Nat) :
    (coordComposeInstrs (bits := bits) basePc).all sliceNonHalt = true := by
  rfl

def mapComposeInstrs (basePc : Nat) : List (Instr bits 15) :=
  coordComposeInstrs basePc ++
  [ .add reg5 reg1 reg1
  , .add reg5 reg5 reg5
  , .add reg3 reg3 reg5
  , .add reg4 reg4 reg5
  ] ++ coordComposeInstrs (basePc + 66)

theorem mapComposeInstrs_length (basePc : Nat) :
    (mapComposeInstrs (bits := bits) basePc).length = 128 := by
  simp [mapComposeInstrs, coordComposeInstrs_length]

theorem mapComposeInstrs_nonHalt (basePc : Nat) :
    (mapComposeInstrs (bits := bits) basePc).all sliceNonHalt = true := by
  rfl

variable {inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_coordCompose {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (hPl : Placed code basePc (coordComposeInstrs (bits := bits) basePc))
    (hSz : basePc + 62 < code.size)
    (innerAddr outerCoordAddr dstCoordAddr : Nat) (inner : Map) (c : Coord)
    (hFitI : innerAddr + 7 < 2 ^ bits) (hFitC : outerCoordAddr + 3 < 2 ^ bits)
    (hFitD : dstCoordAddr + 3 < 2 ^ bits) (hDstLt : dstCoordAddr + 3 < workCap)
    (hDisjI : dstCoordAddr + 4 ≤ innerAddr ∨ innerAddr + 8 ≤ dstCoordAddr)
    (hDisjC : dstCoordAddr + 4 ≤ outerCoordAddr ∨ outerCoordAddr + 4 ≤ dstCoordAddr)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hr2 : (reg st reg2).val = innerAddr) (hr3 : (reg st reg3).val = outerCoordAddr)
    (hr4 : (reg st reg4).val = dstCoordAddr)
    (hInner : MapWordsAt st.data innerAddr inner) (hC : CoordWordsAt st.data outerCoordAddr c) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 46 ∧ Steps code input k st t ∧ t.pc = basePc + 62 ∧
      CoordWordsAt t.data dstCoordAddr (Coord.compose inner c) ∧
      (∀ r : Fin 15, r = reg0 ∨ r = reg1 ∨ r = reg2 ∨ r = reg3 ∨ r = reg4 ∨
        r = rMeta → reg t r = reg st r) ∧
      (∀ j, (j < dstCoordAddr ∨ dstCoordAddr + 4 ≤ j) → t.data[j]? = st.data[j]?) := by
  obtain ⟨s1, hs1, hpc1, h12_1, ho1, hd1⟩ := step_mov_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by omega)
  obtain ⟨s2, hs2, hpc2, h13_2, ho2, hd2⟩ := step_mov_at (input := input)
    (by rw [hpc1, hpc]; exact hPl 1 _ rfl) (by omega)
  have h3_2 : (reg s2 reg3).val = outerCoordAddr := by
    rw [ho2 reg3 (by intro h; cases h), ho1 reg3 (by intro h; cases h), hr3]
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [ho2 reg1 (by intro h; cases h), ho1 reg1 (by intro h; cases h), hr1]
  obtain ⟨s3, hs3, hpc3, h5_3, ho3, hd3⟩ := step_add_at (input := input)
    (by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl) (by omega)
  have h5Val3 : (reg s3 reg5).val = outerCoordAddr + 1 := by
    rw [h5_3, add_no_wrap _ _ (by rw [h3_2, h1_2]; omega), h3_2, h1_2]
  have h1_3 : (reg s3 reg1).val = 1 := by rw [ho3 reg1 (by intro h; cases h), h1_2]
  obtain ⟨s4, hs4, hpc4, h5_4, ho4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl) (by omega)
  have h5Val4 : (reg s4 reg5).val = outerCoordAddr + 2 := by
    rw [h5_4, add_no_wrap _ _ (by rw [h5Val3, h1_3]; omega), h5Val3, h1_3]
  have h1_4 : (reg s4 reg1).val = 1 := by rw [ho4 reg1 (by intro h; cases h), h1_3]
  obtain ⟨s5, hs5, hpc5, h5_5, ho5, hd5⟩ := step_add_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl) (by omega)
  have h5Val5 : (reg s5 reg5).val = outerCoordAddr + 3 := by
    rw [h5_5, add_no_wrap _ _ (by rw [h5Val4, h1_4]; omega), h5Val4, h1_4]
  obtain ⟨wSl, hwSl, hwSlV⟩ := Option.map_eq_some_iff.mp hC.2
  have hd5' : s5.data = st.data := by rw [hd5, hd4, hd3, hd2, hd1]
  obtain ⟨s6, hs6, hpc6, h5_6, ho6, hd6⟩ := step_loadData_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl) (by omega)
    (by rw [h5Val5, hd5']; exact hwSl)
  have hPres6 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg12 → r ≠ reg13 → reg s6 r = reg st r :=
    fun r hr5 hr12 hr13 => by
      rw [ho6 r hr5, ho5 r hr5, ho4 r hr5, ho3 r hr5, ho2 r hr13, ho1 r hr12]
  have h12_6 : reg s6 reg12 = reg st reg2 := by
    rw [ho6 reg12 (by intro h; cases h), ho5 reg12 (by intro h; cases h),
      ho4 reg12 (by intro h; cases h), ho3 reg12 (by intro h; cases h),
      ho2 reg12 (by intro h; cases h), h12_1]
  have h13_6 : reg s6 reg13 = reg st reg3 := by
    rw [ho6 reg13 (by intro h; cases h), ho5 reg13 (by intro h; cases h),
      ho4 reg13 (by intro h; cases h), ho3 reg13 (by intro h; cases h),
      h13_2, ho1 reg3 (by intro h; cases h)]
  have h0_6 : (reg s6 reg0).val = 0 := by
    rw [hPres6 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0]
  have h1_6 : (reg s6 reg1).val = 1 := by
    rw [hPres6 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
  have h2_6 : (reg s6 reg2).val = innerAddr := by
    rw [hPres6 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2]
  have h3_6 : (reg s6 reg3).val = outerCoordAddr := by
    rw [hPres6 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3]
  have h4_6 : (reg s6 reg4).val = dstCoordAddr := by
    rw [hPres6 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4]
  have hd6' : s6.data = st.data := by rw [hd6, hd5']
  have hPre6 : Steps code input 6 st s6 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (steps_1_of_step hs6)))))
  obtain ⟨s7, hs7, hpc7, hr7, hd7⟩ := step_branchLt_at (input := input)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl) (by split <;> omega)
  have hr7F := reg_of_regs_eq hr7
  rcases hSlot : c.slot with _ | idx
  · rw [ite_eq_right (by rw [h0_6, h5_6, hwSlV, hSlot]; simp)] at hpc7
    have hcAt0 : (st.data[outerCoordAddr]?).map Fin.val =
        some (match c.base with | .empty => 0 | .span _ _ => 1) := by
      have hb := hC.1
      cases hBase : c.base <;> rw [hBase] at hb <;> exact hb.1
    have hcAt1 : (st.data[outerCoordAddr + 1]?).map Fin.val =
        some (match c.base with | .empty => 0 | .span lo _ => lo) := by
      have hb := hC.1
      cases hBase : c.base <;> rw [hBase] at hb <;> exact hb.2.1
    have hcAt2 : (st.data[outerCoordAddr + 2]?).map Fin.val =
        some (match c.base with | .empty => 0 | .span _ hi => hi) := by
      have hb := hC.1
      cases hBase : c.base <;> rw [hBase] at hb <;> exact hb.2.2
    obtain ⟨wc0, hwc0, hwc0V⟩ := Option.map_eq_some_iff.mp hcAt0
    obtain ⟨wc1, hwc1, hwc1V⟩ := Option.map_eq_some_iff.mp hcAt1
    obtain ⟨wc2, hwc2, hwc2V⟩ := Option.map_eq_some_iff.mp hcAt2
    obtain ⟨s8, hs8, hpc8, h6_8, ho8, hd8⟩ := step_loadData_at (input := input)
      (by rw [hpc7]; exact hPl 7 _ rfl) (by omega) (by rw [hr7F, h3_6, hd7, hd6']; exact hwc0)
    have h4_8 : (reg s8 reg4).val = dstCoordAddr := by rw [ho8 reg4 (by intro h; cases h), hr7F, h4_6]
    have hLt0 : (reg s8 reg4).val < s8.data.size := lt_data_size (by rw [h4_8]; omega)
    obtain ⟨s9, hs9, hpc9, hr9, hd9⟩ := step_storeData_opaque (input := input)
      (by rw [hpc8, hpc7]; exact hPl 8 _ rfl) hLt0 (by omega)
    have hr9F := reg_of_regs_eq hr9
    have h3_9 : (reg s9 reg3).val = outerCoordAddr := by
      rw [hr9F, ho8 reg3 (by intro h; cases h), hr7F, h3_6]
    have h1_9 : (reg s9 reg1).val = 1 := by rw [hr9F, ho8 reg1 (by intro h; cases h), hr7F, h1_6]
    obtain ⟨s10, hs10, hpc10, h7_10, ho10, hd10⟩ := step_add_at (input := input)
      (by rw [hpc9, hpc8, hpc7]; exact hPl 9 _ rfl) (by omega)
    have hC1 : (reg s10 reg7).val = outerCoordAddr + 1 := by
      rw [h7_10, add_no_wrap _ _ (by rw [h3_9, h1_9]; omega), h3_9, h1_9]
    have hNeC1 : outerCoordAddr + 1 ≠ (reg s8 reg4).val := by rw [h4_8]; rcases hDisjC with h | h <;> omega
    obtain ⟨s11, hs11, hpc11, h6_11, ho11, hd11⟩ := step_loadData_at (input := input)
      (by rw [hpc10, hpc9, hpc8, hpc7]; exact hPl 10 _ rfl) (by omega)
      (by rw [hC1, hd10, hd9, Array.getElem?_set_ne hLt0 hNeC1.symm, hd8, hd7, hd6']; exact hwc1)
    have h4_11 : (reg s11 reg4).val = dstCoordAddr := by
      rw [ho11 reg4 (by intro h; cases h), ho10 reg4 (by intro h; cases h), hr9F, h4_8]
    have h1_11 : (reg s11 reg1).val = 1 := by rw [ho11 reg1 (by intro h; cases h), ho10 reg1 (by intro h; cases h), h1_9]
    obtain ⟨s12, hs12, hpc12, h8_12, ho12, hd12⟩ := step_add_at (input := input)
      (by rw [hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 11 _ rfl) (by omega)
    have hD1 : (reg s12 reg8).val = dstCoordAddr + 1 := by
      rw [h8_12, add_no_wrap _ _ (by rw [h4_11, h1_11]; omega), h4_11, h1_11]
    have hLt1 : (reg s12 reg8).val < s12.data.size := lt_data_size (by rw [hD1]; omega)
    obtain ⟨s13, hs13, hpc13, hr13, hd13⟩ := step_storeData_opaque (input := input)
      (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 12 _ rfl) hLt1 (by omega)
    have hr13F := reg_of_regs_eq hr13
    have h7_13 : (reg s13 reg7).val = outerCoordAddr + 1 := by
      rw [hr13F, ho12 reg7 (by intro h; cases h), ho11 reg7 (by intro h; cases h), hC1]
    have h1_13 : (reg s13 reg1).val = 1 := by rw [hr13F, ho12 reg1 (by intro h; cases h), h1_11]
    obtain ⟨s14, hs14, hpc14, h7_14, ho14, hd14⟩ := step_add_at (input := input)
      (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 13 _ rfl) (by omega)
    have hC2 : (reg s14 reg7).val = outerCoordAddr + 2 := by
      rw [h7_14, add_no_wrap _ _ (by rw [h7_13, h1_13]; omega), h7_13, h1_13]
    have hNeC2a : outerCoordAddr + 2 ≠ (reg s12 reg8).val := by rw [hD1]; rcases hDisjC with h | h <;> omega
    have hNeC2b : outerCoordAddr + 2 ≠ (reg s8 reg4).val := by rw [h4_8]; rcases hDisjC with h | h <;> omega
    obtain ⟨s15, hs15, hpc15, h6_15, ho15, hd15⟩ := step_loadData_at (input := input)
      (by rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 14 _ rfl) (by omega)
      (by rw [hC2, hd14, hd13, Array.getElem?_set_ne hLt1 hNeC2a.symm, hd12, hd11, hd10, hd9,
        Array.getElem?_set_ne hLt0 hNeC2b.symm, hd8, hd7, hd6']; exact hwc2)
    have h8_15 : (reg s15 reg8).val = dstCoordAddr + 1 := by
      rw [ho15 reg8 (by intro h; cases h), ho14 reg8 (by intro h; cases h), hr13F, hD1]
    have h1_15 : (reg s15 reg1).val = 1 := by rw [ho15 reg1 (by intro h; cases h), ho14 reg1 (by intro h; cases h), h1_13]
    obtain ⟨s16, hs16, hpc16, h8_16, ho16, hd16⟩ := step_add_at (input := input)
      (by rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 15 _ rfl) (by omega)
    have hD2 : (reg s16 reg8).val = dstCoordAddr + 2 := by
      rw [h8_16, add_no_wrap _ _ (by rw [h8_15, h1_15]; omega), h8_15, h1_15]
    have hLt2 : (reg s16 reg8).val < s16.data.size := lt_data_size (by rw [hD2]; omega)
    obtain ⟨s17, hs17, hpc17, hr17, hd17⟩ := step_storeData_opaque (input := input)
      (by rw [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 16 _ rfl) hLt2 (by omega)
    have hr17F := reg_of_regs_eq hr17
    have h7_17 : (reg s17 reg7).val = outerCoordAddr + 2 := by
      rw [hr17F, ho16 reg7 (by intro h; cases h), ho15 reg7 (by intro h; cases h), hC2]
    have h1_17 : (reg s17 reg1).val = 1 := by rw [hr17F, ho16 reg1 (by intro h; cases h), h1_15]
    obtain ⟨s18, hs18, hpc18, h7_18, ho18, hd18⟩ := step_add_at (input := input)
      (by rw [hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 17 _ rfl) (by omega)
    have hC3 : (reg s18 reg7).val = outerCoordAddr + 3 := by
      rw [h7_18, add_no_wrap _ _ (by rw [h7_17, h1_17]; omega), h7_17, h1_17]
    have hNeC3a : outerCoordAddr + 3 ≠ (reg s16 reg8).val := by rw [hD2]; rcases hDisjC with h | h <;> omega
    have hNeC3b : outerCoordAddr + 3 ≠ (reg s12 reg8).val := by rw [hD1]; rcases hDisjC with h | h <;> omega
    have hNeC3c : outerCoordAddr + 3 ≠ (reg s8 reg4).val := by rw [h4_8]; rcases hDisjC with h | h <;> omega
    obtain ⟨s19, hs19, hpc19, h6_19, ho19, hd19⟩ := step_loadData_at (input := input)
      (by rw [hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 18 _ rfl) (by omega)
      (by rw [hC3, hd18, hd17, Array.getElem?_set_ne hLt2 hNeC3a.symm, hd16, hd15, hd14, hd13,
        Array.getElem?_set_ne hLt1 hNeC3b.symm, hd12, hd11, hd10, hd9,
        Array.getElem?_set_ne hLt0 hNeC3c.symm, hd8, hd7, hd6']; exact hwSl)
    have h8_19 : (reg s19 reg8).val = dstCoordAddr + 2 := by
      rw [ho19 reg8 (by intro h; cases h), ho18 reg8 (by intro h; cases h), hr17F, hD2]
    have h1_19 : (reg s19 reg1).val = 1 := by rw [ho19 reg1 (by intro h; cases h), ho18 reg1 (by intro h; cases h), h1_17]
    obtain ⟨s20, hs20, hpc20, h8_20, ho20, hd20⟩ := step_add_at (input := input)
      (by rw [hpc19, hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 19 _ rfl) (by omega)
    have hD3 : (reg s20 reg8).val = dstCoordAddr + 3 := by
      rw [h8_20, add_no_wrap _ _ (by rw [h8_19, h1_19]; omega), h8_19, h1_19]
    have hLt3 : (reg s20 reg8).val < s20.data.size := lt_data_size (by rw [hD3]; omega)
    obtain ⟨s21, hs21, hpc21, hr21, hd21⟩ := step_storeData_opaque (input := input)
      (by rw [hpc20, hpc19, hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 20 _ rfl) hLt3 (by omega)
    have hr21F := reg_of_regs_eq hr21
    obtain ⟨s22, hs22, hpc22, hr22, hd22⟩ := step_goto_at (input := input)
      (by rw [hpc21, hpc20, hpc19, hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7]; exact hPl 21 _ rfl) (by omega)
    have hr22F := reg_of_regs_eq hr22
    obtain ⟨s23, hs23, hpc23, h2_23, ho23, hd23⟩ := step_mov_at (input := input)
      (by rw [hpc22]; exact hPl 60 _ rfl) (by omega)
    obtain ⟨t, hs24, hpct, h3t, hot, hdt⟩ := step_mov_at (input := input)
      (by rw [hpc23, hpc22]; exact hPl 61 _ rfl) (by omega)
    have hAtT : ∀ a, t.data[a]? =
        if a = dstCoordAddr + 3 then some (reg s20 reg6)
        else if a = dstCoordAddr + 2 then some (reg s16 reg6)
        else if a = dstCoordAddr + 1 then some (reg s12 reg6)
        else if a = dstCoordAddr then some (reg s8 reg6)
        else st.data[a]? := by
      intro a
      rw [hdt, hd23, hd22, hd21]
      by_cases ha3 : a = dstCoordAddr + 3
      · subst ha3; rw [ite_eq_left rfl, ← hD3, Array.getElem?_set_self hLt3]
      · rw [ite_eq_right ha3, Array.getElem?_set_ne hLt3 (by rw [hD3]; exact Ne.symm ha3), hd20, hd19, hd18, hd17]
        by_cases ha2 : a = dstCoordAddr + 2
        · subst ha2; rw [ite_eq_left rfl, ← hD2, Array.getElem?_set_self hLt2]
        · rw [ite_eq_right ha2, Array.getElem?_set_ne hLt2 (by rw [hD2]; exact Ne.symm ha2), hd16, hd15, hd14, hd13]
          by_cases ha1 : a = dstCoordAddr + 1
          · subst ha1; rw [ite_eq_left rfl, ← hD1, Array.getElem?_set_self hLt1]
          · rw [ite_eq_right ha1, Array.getElem?_set_ne hLt1 (by rw [hD1]; exact Ne.symm ha1), hd12, hd11, hd10, hd9]
            by_cases ha0 : a = dstCoordAddr
            · subst ha0; rw [ite_eq_left rfl, ← h4_8, Array.getElem?_set_self hLt0]
            · rw [ite_eq_right ha0, Array.getElem?_set_ne hLt0 (by rw [h4_8]; exact Ne.symm ha0), hd8, hd7, hd6']
    have hPresPre : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg12 →
        r ≠ reg13 → reg s22 r = reg st r := fun r h5 h6 h7 h8 h12 h13 => by
      rw [hr22F, hr21F, ho20 r h8, ho19 r h6, ho18 r h7, hr17F, ho16 r h8, ho15 r h6,
        ho14 r h7, hr13F, ho12 r h8, ho11 r h6, ho10 r h7, hr9F, ho8 r h6, hr7F, hPres6 r h5 h12 h13]
    have hStepRest : Steps code input 18 s6 t :=
      Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11
        (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (Steps.cons hs16
          (Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19 (Steps.cons hs20 (Steps.cons hs21
            (Steps.cons hs22 (Steps.cons hs23 (steps_1_of_step hs24)))))))))))))))))
    have hOutComp : CoordWordsAt t.data dstCoordAddr (Coord.compose inner c) := by
      have hCompEq : Coord.compose inner c = c := by simp [Coord.compose, hSlot]
      rw [hCompEq]
      have hs8_6 : (reg s8 reg6).val = wc0.val := by rw [h6_8]
      have hs12_6 : (reg s12 reg6).val = wc1.val := by rw [ho12 reg6 (by intro h; cases h), h6_11]
      have hs16_6 : (reg s16 reg6).val = wc2.val := by rw [ho16 reg6 (by intro h; cases h), h6_15]
      have hs20_6 : (reg s20 reg6).val = wSl.val := by rw [ho20 reg6 (by intro h; cases h), h6_19]
      refine ⟨?_, ?_⟩
      · cases hcB : c.base with
        | empty =>
          rw [hcB] at hwc0V hwc1V hwc2V
          exact ⟨by rw [hAtT dstCoordAddr, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs8_6, hwc0V],
            by rw [hAtT (dstCoordAddr + 1), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs12_6, hwc1V],
            by rw [hAtT (dstCoordAddr + 2), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs16_6, hwc2V]⟩
        | span lo hi =>
          rw [hcB] at hwc0V hwc1V hwc2V
          exact ⟨by rw [hAtT dstCoordAddr, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs8_6, hwc0V],
            by rw [hAtT (dstCoordAddr + 1), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs12_6, hwc1V],
            by rw [hAtT (dstCoordAddr + 2), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hs16_6, hwc2V]⟩
      · rw [hAtT (dstCoordAddr + 3), ite_eq_left rfl, Option.map_some, hs20_6, hwSlV, hSlot]
    refine ⟨6 + 18, t, by omega, hPre6.append hStepRest, by omega, hOutComp, fun r hr => ?_, fun j hj => ?_⟩
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hot reg0 (by intro h; cases h), ho23 reg0 (by intro h; cases h), hPresPre reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
      · rw [hot reg1 (by intro h; cases h), ho23 reg1 (by intro h; cases h), hPresPre reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
      · rw [hot reg2 (by intro h; cases h), h2_23]
        rw [hr22F, hr21F, ho20 reg12 (by intro h; cases h), ho19 reg12 (by intro h; cases h), ho18 reg12 (by intro h; cases h), hr17F, ho16 reg12 (by intro h; cases h), ho15 reg12 (by intro h; cases h), ho14 reg12 (by intro h; cases h), hr13F, ho12 reg12 (by intro h; cases h), ho11 reg12 (by intro h; cases h), ho10 reg12 (by intro h; cases h), hr9F, ho8 reg12 (by intro h; cases h), hr7F, h12_6]
      · rw [h3t, ho23 reg13 (by intro h; cases h), hr22F, hr21F, ho20 reg13 (by intro h; cases h), ho19 reg13 (by intro h; cases h), ho18 reg13 (by intro h; cases h), hr17F, ho16 reg13 (by intro h; cases h), ho15 reg13 (by intro h; cases h), ho14 reg13 (by intro h; cases h), hr13F, ho12 reg13 (by intro h; cases h), ho11 reg13 (by intro h; cases h), ho10 reg13 (by intro h; cases h), hr9F, ho8 reg13 (by intro h; cases h), hr7F, h13_6]
      · rw [hot reg4 (by intro h; cases h), ho23 reg4 (by intro h; cases h), hPresPre reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
      · rw [hot rMeta (by intro h; cases h), ho23 rMeta (by intro h; cases h), hPresPre rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
    · rw [hAtT j, ite_eq_right (by rcases hj with h | h <;> omega), ite_eq_right (by rcases hj with h | h <;> omega),
        ite_eq_right (by rcases hj with h | h <;> omega), ite_eq_right (by rcases hj with h | h <;> omega)]
  · have hPosSl : 0 < (match some idx with | none => 0 | some 0 => 1 | some 1 => 2) := by
      rcases fin2_cases idx with rfl | rfl <;> simp
    rw [ite_eq_left (by rw [h0_6, h5_6, hwSlV, hSlot]; exact hPosSl)] at hpc7
    have hPlJoin : Placed code (basePc + 35) (intervalJoinInstrs (bits := bits) (basePc + 35)) := by
      have hL := Placed_append_left (by unfold coordComposeInstrs at hPl; exact hPl)
      have hR := Placed_append_right hL
      simpa only [List.length_cons, List.length_nil] using hR
    obtain ⟨s8, hs8, hpc8, hr8, hd8⟩ := step_branchLt_at (input := input)
      (by rw [hpc7]; exact hPl 22 _ rfl) (by split <;> omega)
    have hr8F := reg_of_regs_eq hr8
    have hOne7 : (reg s7 reg1).val = 1 := by rw [hr7F reg1, h1_6]
    have hSlotWord7 : reg s7 reg5 = wSl := by rw [hr7F reg5, h5_6]
    have hIcSelect : ∃ (kSel : Nat) (sSel : State DomL),
        kSel ≤ 4 ∧ Steps code input kSel s8 sSel ∧ sSel.pc = basePc + 27 ∧ sSel.data = st.data ∧
        (reg sSel reg2).val = innerAddr + 4 * idx.val ∧
        CoordWordsAt sSel.data (innerAddr + 4 * idx.val) (inner.get idx) ∧
        ∀ r : Fin 15, r ≠ reg2 → reg sSel r = reg s7 r := by
      rcases fin2_cases idx with h0Eq | h1Eq
      · subst h0Eq
        rw [ite_eq_right (by
          simpa only [hOne7, hSlotWord7, hwSlV, hSlot] using (show ¬ (1 : Nat) < 1 from by decide))] at hpc8
        exact ⟨0, s8, Nat.zero_le _, Steps.zero s8, hpc8, by rw [hd8, hd7, hd6'],
          by rw [hr8F, hr7F, h2_6]; rfl, by rw [hd8, hd7, hd6']; exact hInner.1, fun r _ => hr8F r⟩
      · subst h1Eq
        rw [ite_eq_left (by
          simpa only [hOne7, hSlotWord7, hwSlV, hSlot] using (show (1 : Nat) < 2 from by decide))] at hpc8
        have h2_8 : (reg s8 reg2).val = innerAddr := by rw [hr8F, hr7F, h2_6]
        have h1_8 : (reg s8 reg1).val = 1 := by rw [hr8F, hr7F, h1_6]
        obtain ⟨sa, hsa, hpca, h2a, hoa, hda⟩ := step_add_at (input := input)
          (by rw [hpc8]; exact hPl 23 _ rfl) (by omega)
        have h2aV : (reg sa reg2).val = innerAddr + 1 := by
          rw [h2a, add_no_wrap _ _ (by rw [h2_8, h1_8]; omega), h2_8, h1_8]
        have h1a : (reg sa reg1).val = 1 := by rw [hoa reg1 (by intro h; cases h), h1_8]
        obtain ⟨sb, hsb, hpcb, h2b, hob, hdb⟩ := step_add_at (input := input)
          (by rw [hpca, hpc8]; exact hPl 24 _ rfl) (by omega)
        have h2bV : (reg sb reg2).val = innerAddr + 2 := by
          rw [h2b, add_no_wrap _ _ (by rw [h2aV, h1a]; omega), h2aV, h1a]
        have h1b : (reg sb reg1).val = 1 := by rw [hob reg1 (by intro h; cases h), h1a]
        obtain ⟨sc, hsc, hpcc, h2c, hoc, hdc⟩ := step_add_at (input := input)
          (by rw [hpcb, hpca, hpc8]; exact hPl 25 _ rfl) (by omega)
        have h2cV : (reg sc reg2).val = innerAddr + 3 := by
          rw [h2c, add_no_wrap _ _ (by rw [h2bV, h1b]; omega), h2bV, h1b]
        have h1c : (reg sc reg1).val = 1 := by rw [hoc reg1 (by intro h; cases h), h1b]
        obtain ⟨sd, hsd, hpcd, h2d, hod, hdd⟩ := step_add_at (input := input)
          (by rw [hpcc, hpcb, hpca, hpc8]; exact hPl 26 _ rfl) (by omega)
        refine ⟨4, sd, Nat.le_refl _,
          Steps.cons hsa (Steps.cons hsb (Steps.cons hsc (steps_1_of_step hsd))),
          by omega, by rw [hdd, hdc, hdb, hda, hd8, hd7, hd6'],
          by rw [h2d, add_no_wrap _ _ (by rw [h2cV, h1c]; omega), h2cV, h1c]; omega,
          by rw [hdd, hdc, hdb, hda, hd8, hd7, hd6']; exact hInner.2,
          fun r hr => by rw [hod r hr, hoc r hr, hob r hr, hoa r hr, hr8F]⟩
    obtain ⟨kSel, sSel, hkSel, hStepsSel, hpcSel, hdSel', h2Sel, hIcAt, hPresSel⟩ := hIcSelect
    have hIcSlAddrFit : innerAddr + 4 * idx.val + 3 < 2 ^ bits := by
      rcases fin2_cases idx with rfl | rfl <;> simp <;> omega
    have h1Sel : (reg sSel reg1).val = 1 := by rw [hPresSel reg1 (by intro h; cases h), hr7F, h1_6]
    have h4Sel : (reg sSel reg4).val = dstCoordAddr := by rw [hPresSel reg4 (by intro h; cases h), hr7F, h4_6]
    obtain ⟨s9, hs9, hpc9, h6_9, ho9, hd9⟩ := step_add_at (input := input)
      (by rw [hpcSel]; exact hPl 27 _ rfl) (by omega)
    have h6Val9 : (reg s9 reg6).val = innerAddr + 4 * idx.val + 1 := by
      rw [h6_9, add_no_wrap _ _ (by rw [h2Sel, h1Sel]; omega), h2Sel, h1Sel]
    have h1_9 : (reg s9 reg1).val = 1 := by rw [ho9 reg1 (by intro h; cases h), h1Sel]
    obtain ⟨s10, hs10, hpc10, h6_10, ho10, hd10⟩ := step_add_at (input := input)
      (by rw [hpc9, hpcSel]; exact hPl 28 _ rfl) (by omega)
    have h6Val10 : (reg s10 reg6).val = innerAddr + 4 * idx.val + 2 := by
      rw [h6_10, add_no_wrap _ _ (by rw [h6Val9, h1_9]; omega), h6Val9, h1_9]
    have h1_10 : (reg s10 reg1).val = 1 := by rw [ho10 reg1 (by intro h; cases h), h1_9]
    obtain ⟨s11, hs11, hpc11, h6_11, ho11, hd11⟩ := step_add_at (input := input)
      (by rw [hpc10, hpc9, hpcSel]; exact hPl 29 _ rfl) (by omega)
    have h6Val11 : (reg s11 reg6).val = innerAddr + 4 * idx.val + 3 := by
      rw [h6_11, add_no_wrap _ _ (by rw [h6Val10, h1_10]; omega), h6Val10, h1_10]
    obtain ⟨wIcSl, hwIcSl, hwIcSlV⟩ := Option.map_eq_some_iff.mp hIcAt.2
    obtain ⟨s12, hs12, hpc12, h6_12, ho12, hd12⟩ := step_loadData_at (input := input)
      (by rw [hpc11, hpc10, hpc9, hpcSel]; exact hPl 30 _ rfl) (by omega)
      (by rw [h6Val11, hd11, hd10, hd9]; exact hwIcSl)
    have h4_12 : (reg s12 reg4).val = dstCoordAddr := by
      rw [ho12 reg4 (by intro h; cases h), ho11 reg4 (by intro h; cases h),
        ho10 reg4 (by intro h; cases h), ho9 reg4 (by intro h; cases h), h4Sel]
    have h1_12 : (reg s12 reg1).val = 1 := by rw [ho12 reg1 (by intro h; cases h), ho11 reg1 (by intro h; cases h), h1_10]
    obtain ⟨s13, hs13, hpc13, h7_13, ho13, hd13⟩ := step_add_at (input := input)
      (by rw [hpc12, hpc11, hpc10, hpc9, hpcSel]; exact hPl 31 _ rfl) (by omega)
    have h7Val13 : (reg s13 reg7).val = dstCoordAddr + 1 := by
      rw [h7_13, add_no_wrap _ _ (by rw [h4_12, h1_12]; omega), h4_12, h1_12]
    have h1_13 : (reg s13 reg1).val = 1 := by rw [ho13 reg1 (by intro h; cases h), h1_12]
    obtain ⟨s14, hs14, hpc14, h7_14, ho14, hd14⟩ := step_add_at (input := input)
      (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpcSel]; exact hPl 32 _ rfl) (by omega)
    have h7Val14 : (reg s14 reg7).val = dstCoordAddr + 2 := by
      rw [h7_14, add_no_wrap _ _ (by rw [h7Val13, h1_13]; omega), h7Val13, h1_13]
    have h1_14 : (reg s14 reg1).val = 1 := by rw [ho14 reg1 (by intro h; cases h), h1_13]
    obtain ⟨s15, hs15, hpc15, h7_15, ho15, hd15⟩ := step_add_at (input := input)
      (by rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpcSel]; exact hPl 33 _ rfl) (by omega)
    have hD3 : (reg s15 reg7).val = dstCoordAddr + 3 := by
      rw [h7_15, add_no_wrap _ _ (by rw [h7Val14, h1_14]; omega), h7Val14, h1_14]
    have hLt3 : (reg s15 reg7).val < s15.data.size := lt_data_size (by rw [hD3]; omega)
    obtain ⟨s16, hs16, hpc16, hr16, hd16⟩ := step_storeData_opaque (input := input)
      (by rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpcSel]; exact hPl 34 _ rfl) hLt3 (by omega)
    have hr16F := reg_of_regs_eq hr16
    have hPres16 : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → reg s16 r = reg sSel r := fun r hr6 hr7 => by
      rw [hr16F, ho15 r hr7, ho14 r hr7, ho13 r hr7, ho12 r hr6, ho11 r hr6, ho10 r hr6, ho9 r hr6]
    have hd15' : s15.data = st.data := by rw [hd15, hd14, hd13, hd12, hd11, hd10, hd9, hdSel']
    have hLt3St : (reg s15 reg7).val < st.data.size := by rw [← hd15']; exact hLt3
    have hs16Data : s16.data = st.data.set (reg s15 reg7).val (reg s15 reg6) hLt3St := by
      rw [hd16]
      generalize st.data = mem at hd15' hLt3St ⊢
      cases hd15'
      rfl
    have hStepMid : Steps code input 8 sSel s16 :=
      Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12
        (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (steps_1_of_step hs16)))))))
    have hFitSrcA' : innerAddr + 4 * idx.val + 2 < 2 ^ bits := by omega
    have hIcBase16 : IntervalWordsAt s16.data (innerAddr + 4 * idx.val) (inner.get idx).base :=
      intervalWordsAt_frame (fun i hi => by
        rw [hs16Data, Array.getElem?_set_ne hLt3St (by rw [hD3]; rcases hDisjI with h | h <;> rcases fin2_cases idx with rfl | rfl <;> simp <;> omega), hdSel']) hIcAt.1
    have hCBase16 : IntervalWordsAt s16.data outerCoordAddr c.base :=
      intervalWordsAt_frame (fun i hi => by
        rw [hs16Data, Array.getElem?_set_ne hLt3St (by rw [hD3]; rcases hDisjC with h | h <;> omega)]) hC.1
    obtain ⟨kJ, sPost, hkJ, hStepsJ, hpcPost, hOutJ, hPresPost, hFrJ⟩ :=
      run_intervalJoin (basePc + 35) hPlJoin (by omega) (innerAddr + 4 * idx.val) outerCoordAddr dstCoordAddr
        (inner.get idx).base c.base hFitSrcA' (by omega) (by omega) (by omega)
        s16 (by omega)
        (by rw [hPres16 reg0 (by intro h; cases h) (by intro h; cases h), hPresSel reg0 (by intro h; cases h), hr7F, h0_6])
        (by rw [hPres16 reg1 (by intro h; cases h) (by intro h; cases h), h1Sel])
        (by rw [hPres16 reg2 (by intro h; cases h) (by intro h; cases h), h2Sel])
        (by rw [hPres16 reg3 (by intro h; cases h) (by intro h; cases h), hPresSel reg3 (by intro h; cases h), hr7F, h3_6])
        (by rw [hPres16 reg4 (by intro h; cases h) (by intro h; cases h), h4Sel])
        hIcBase16 hCBase16
    obtain ⟨sMov1, hsMov1, hpcM1, h2M1, hoM1, hdM1⟩ := step_mov_at (input := input)
      (by rw [hpcPost]; exact hPl 60 _ rfl) (by omega)
    obtain ⟨t, hsMov2, hpct, h3t, hot, hdt⟩ := step_mov_at (input := input)
      (by rw [hpcM1, hpcPost]; exact hPl 61 _ rfl) (by omega)
    have hCompEq : Coord.compose inner c = ⟨Interval.join c.base (inner.get idx).base, (inner.get idx).slot⟩ := by
      simp [Coord.compose, hSlot]
    refine ⟨6 + 2 + kSel + 8 + kJ + 2, t, by omega,
      (((((hPre6.append (Steps.cons hs7 (steps_1_of_step hs8))).append
        hStepsSel).append hStepMid).append hStepsJ).append (Steps.cons hsMov1 (steps_1_of_step hsMov2))),
      by omega, ?_, fun r hr => ?_, fun j hj => ?_⟩
    · rw [hCompEq]
      refine ⟨?_, ?_⟩
      · rw [hdt, hdM1, Interval.join_comm c.base (inner.get idx).base]; exact hOutJ
      · rw [hdt, hdM1, hFrJ _ (Or.inr (Nat.le_refl _)), hs16Data, ← hD3,
          Array.getElem?_set_self hLt3St, Option.map_some,
          ho15 reg6 (by intro h; cases h), ho14 reg6 (by intro h; cases h), ho13 reg6 (by intro h; cases h),
          h6_12, hwIcSlV]
    · rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hot reg0 (by intro h; cases h), hoM1 reg0 (by intro h; cases h), hPresPost reg0 (Or.inl rfl),
          hPres16 reg0 (by intro h; cases h) (by intro h; cases h), hPresSel reg0 (by intro h; cases h), hr7F, hPres6 reg0 (by decide) (by decide) (by decide)]
      · rw [hot reg1 (by intro h; cases h), hoM1 reg1 (by intro h; cases h), hPresPost reg1 (Or.inr (Or.inl rfl)),
          hPres16 reg1 (by intro h; cases h) (by intro h; cases h), hPresSel reg1 (by intro h; cases h), hr7F, hPres6 reg1 (by decide) (by decide) (by decide)]
      · rw [hot reg2 (by intro h; cases h), h2M1, hPresPost reg12 (by decide),
          hPres16 reg12 (by intro h; cases h) (by intro h; cases h), hPresSel reg12 (by intro h; cases h), hr7F, h12_6]
      · rw [h3t, hoM1 reg13 (by intro h; cases h), hPresPost reg13 (by decide),
          hPres16 reg13 (by intro h; cases h) (by intro h; cases h), hPresSel reg13 (by intro h; cases h), hr7F, h13_6]
      · rw [hot reg4 (by intro h; cases h), hoM1 reg4 (by intro h; cases h), hPresPost reg4 (by decide),
          hPres16 reg4 (by intro h; cases h) (by intro h; cases h), hPresSel reg4 (by intro h; cases h), hr7F, hPres6 reg4 (by decide) (by decide) (by decide)]
      · rw [hot rMeta (by intro h; cases h), hoM1 rMeta (by intro h; cases h), hPresPost rMeta (by decide),
          hPres16 rMeta (by intro h; cases h) (by intro h; cases h), hPresSel rMeta (by intro h; cases h), hr7F,
          hPres6 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
    · rw [hdt, hdM1, hFrJ j (by rcases hj with h | h; exact Or.inl h; exact Or.inr (by omega)),
        hs16Data, Array.getElem?_set_ne hLt3St (by rw [hD3]; rcases hj with h | h <;> omega)]

theorem run_mapCompose {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (hPl : Placed code basePc (mapComposeInstrs (bits := bits) basePc))
    (hSz : basePc + 128 < code.size)
    (innerAddr outerAddr dstAddr : Nat) (inner outer : Map)
    (hFitI : innerAddr + 7 < 2 ^ bits) (hFitO : outerAddr + 7 < 2 ^ bits)
    (hFitD : dstAddr + 7 < 2 ^ bits) (hDstLt : dstAddr + 7 < workCap)
    (hDisjI : dstAddr + 8 ≤ innerAddr ∨ innerAddr + 8 ≤ dstAddr)
    (hDisjO : dstAddr + 8 ≤ outerAddr ∨ outerAddr + 8 ≤ dstAddr)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hr2 : (reg st reg2).val = innerAddr) (hr3 : (reg st reg3).val = outerAddr)
    (hr4 : (reg st reg4).val = dstAddr)
    (hInner : MapWordsAt st.data innerAddr inner) (hOuter : MapWordsAt st.data outerAddr outer) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 96 ∧ Steps code input k st t ∧ t.pc = basePc + 128 ∧
      MapWordsAt t.data dstAddr (Map.compose inner outer) ∧
      (∀ r : Fin 15, r = reg0 ∨ r = reg1 ∨ r = reg2 ∨ r = rMeta → reg t r = reg st r) ∧
      (∀ j, (j < dstAddr ∨ dstAddr + 8 ≤ j) → t.data[j]? = st.data[j]?) := by
  have hPl1 : Placed code basePc (coordComposeInstrs (bits := bits) basePc) :=
    Placed_append_left (Placed_append_left (by unfold mapComposeInstrs at hPl; exact hPl))
  have hPlR1 := Placed_append_right (by unfold mapComposeInstrs at hPl; exact hPl)
  have hPlMid : Placed code (basePc + 62)
      ([Instr.add reg5 reg1 reg1, .add reg5 reg5 reg5, .add reg3 reg3 reg5,
        .add reg4 reg4 reg5] : List (Instr bits 15)) := by
    have hL := Placed_append_left (by unfold mapComposeInstrs at hPl; exact hPl)
    have hM := Placed_append_right hL
    rwa [coordComposeInstrs_length] at hM
  have hPl2 : Placed code (basePc + 66) (coordComposeInstrs (bits := bits) (basePc + 66)) := by
    rw [List.length_append, coordComposeInstrs_length,
      show ([Instr.add reg5 reg1 reg1, .add reg5 reg5 reg5, .add reg3 reg3 reg5,
        .add reg4 reg4 reg5] : List (Instr bits 15)).length = 4 by rfl] at hPlR1
    exact hPlR1
  obtain ⟨k1, s1, hk1, hSteps1, hpc1, hOut1, hPres1, hFr1⟩ :=
    run_coordCompose (input := input) basePc hPl1 (by omega) innerAddr outerAddr dstAddr inner outer.x0
      hFitI (by omega) (by omega) (by omega)
      (by rcases hDisjI with h | h; exact Or.inl (by omega); exact Or.inr h)
      (by rcases hDisjO with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      st hpc hr0 hr1 hr2 hr3 hr4 hInner hOuter.1
  have h1_1 : (reg s1 reg1).val = 1 := by rw [hPres1 reg1 (Or.inr (Or.inl rfl)), hr1]
  have h3_1 : (reg s1 reg3).val = outerAddr := by rw [hPres1 reg3 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hr3]
  have h4_1 : (reg s1 reg4).val = dstAddr := by rw [hPres1 reg4 (by decide), hr4]
  obtain ⟨s2, hs2, hpc2, h5_2, ho2, hd2⟩ := step_add_at (input := input)
    (by rw [hpc1]; exact hPlMid 0 _ rfl) (by omega)
  have h5Val2 : (reg s2 reg5).val = 2 := by rw [h5_2, add_no_wrap _ _ (by rw [h1_1]; omega), h1_1]
  obtain ⟨s3, hs3, hpc3, h5_3, ho3, hd3⟩ := step_add_at (input := input)
    (by rw [hpc2, hpc1]; exact hPlMid 1 _ rfl) (by omega)
  have h5Val3 : (reg s3 reg5).val = 4 := by rw [h5_3, add_no_wrap _ _ (by rw [h5Val2]; omega), h5Val2]
  have h3_3 : (reg s3 reg3).val = outerAddr := by
    rw [ho3 reg3 (by intro h; cases h), ho2 reg3 (by intro h; cases h), h3_1]
  obtain ⟨s4, hs4, hpc4, h3_4, ho4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3, hpc2, hpc1]; exact hPlMid 2 _ rfl) (by omega)
  have h3Val4 : (reg s4 reg3).val = outerAddr + 4 := by
    rw [h3_4, add_no_wrap _ _ (by rw [h3_3, h5Val3]; omega), h3_3, h5Val3]
  have h4_4 : (reg s4 reg4).val = dstAddr := by
    rw [ho4 reg4 (by intro h; cases h), ho3 reg4 (by intro h; cases h), ho2 reg4 (by intro h; cases h), h4_1]
  have h5_4 : (reg s4 reg5).val = 4 := by rw [ho4 reg5 (by intro h; cases h), h5Val3]
  obtain ⟨s5, hs5, hpc5, h4_5, ho5, hd5⟩ := step_add_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1]; exact hPlMid 3 _ rfl) (by omega)
  have h4Val5 : (reg s5 reg4).val = dstAddr + 4 := by
    rw [h4_5, add_no_wrap _ _ (by rw [h4_4, h5_4]; omega), h4_4, h5_4]
  have hPresMid : ∀ r : Fin 15, r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → reg s5 r = reg s1 r :=
    fun r hr3 hr4 hr5 => by rw [ho5 r hr4, ho4 r hr3, ho3 r hr5, ho2 r hr5]
  have hd5' : s5.data = s1.data := by rw [hd5, hd4, hd3, hd2]
  have hStepMid : Steps code input 4 s1 s5 :=
    Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5)))
  have hInner5 : MapWordsAt s5.data innerAddr inner :=
    mapWordsAt_frame (fun i hi => by
      rw [hd5', hFr1 _ (by rcases hDisjI with h | h; exact Or.inr (by omega); exact Or.inl (by omega))]) hInner
  have hOuter5 : CoordWordsAt s5.data (outerAddr + 4) outer.x1 :=
    coordWordsAt_frame (fun i hi => by
      rw [hd5', hFr1 _ (by rcases hDisjO with h | h; exact Or.inr (by omega); exact Or.inl (by omega))]) hOuter.2
  obtain ⟨k2, t, hk2, hSteps2, hpc2', hOut2, hPres2, hFr2⟩ :=
    run_coordCompose (input := input) (basePc + 66) hPl2 (by omega) innerAddr (outerAddr + 4) (dstAddr + 4) inner outer.x1
      hFitI (by omega) hFitD hDstLt
      (by rcases hDisjI with h | h; exact Or.inl h; exact Or.inr (by omega))
      (by rcases hDisjO with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
      s5 (by omega)
      (by rw [hPresMid reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg0 (Or.inl rfl), hr0])
      (by rw [hPresMid reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_1])
      (by rw [hPresMid reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg2 (Or.inr (Or.inr (Or.inl rfl))), hr2])
      (by rw [ho5 reg3 (by intro h; cases h), h3Val4]) h4Val5 hInner5 hOuter5
  refine ⟨k1 + 4 + k2, t, by omega, (hSteps1.append hStepMid).append hSteps2, by omega, ⟨?_, hOut2⟩,
    fun r hr => ?_, fun j hj => ?_⟩
  · exact coordWordsAt_frame (fun i hi => by rw [hFr2 _ (Or.inl (by omega)), hd5']) hOut1
  · rcases hr with rfl | rfl | rfl | rfl
    · rw [hPres2 reg0 (Or.inl rfl), hPresMid reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg0 (Or.inl rfl)]
    · rw [hPres2 reg1 (Or.inr (Or.inl rfl)), hPresMid reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg1 (Or.inr (Or.inl rfl))]
    · rw [hPres2 reg2 (Or.inr (Or.inr (Or.inl rfl))), hPresMid reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 reg2 (Or.inr (Or.inr (Or.inl rfl)))]
    · rw [hPres2 rMeta (by decide), hPresMid rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h),
        hPres1 rMeta (by decide)]
  · rw [hFr2 j (by rcases hj with h | h; exact Or.inl (by omega); exact Or.inr (by omega)), hd5',
      hFr1 j (by rcases hj with h | h; exact Or.inl h; exact Or.inr (by omega))]

end MapEvalAndComposeSlices

end Stage4Helpers

end PaperB.RamProgram.ExitSummaryBuild
