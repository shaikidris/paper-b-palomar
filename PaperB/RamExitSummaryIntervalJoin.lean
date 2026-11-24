module

public import PaperB.RamExitSummaryWordCodec

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

section IntervalJoinSlice

variable {bits : Nat}

def intervalJoinInstrs (basePc : Nat) : List (Instr bits 15) :=
  [ .loadData reg5 reg2
  , .add reg11 reg2 reg1
  , .loadData reg6 reg11
  , .add reg11 reg11 reg1
  , .loadData reg7 reg11
  , .loadData reg8 reg3
  , .add reg11 reg3 reg1
  , .loadData reg9 reg11
  , .add reg11 reg11 reg1
  , .loadData reg10 reg11
  , .branchLt reg0 reg5 (basePc + 15) (basePc + 11)
  , .mov reg5 reg8
  , .mov reg6 reg9
  , .mov reg7 reg10
  , .goto (basePc + 20)
  , .branchLt reg0 reg8 (basePc + 16) (basePc + 20)
  , .branchLt reg9 reg6 (basePc + 17) (basePc + 18)
  , .mov reg6 reg9
  , .branchLt reg7 reg10 (basePc + 19) (basePc + 20)
  , .mov reg7 reg10
  , .storeData reg4 reg5
  , .add reg11 reg4 reg1
  , .storeData reg11 reg6
  , .add reg11 reg11 reg1
  , .storeData reg11 reg7
  ]

theorem intervalJoinInstrs_length (basePc : Nat) :
    (intervalJoinInstrs (bits := bits) basePc).length = 25 := rfl

def sliceNonHalt (op : Instr bits 15) : Bool :=
  match op with
  | .halt => false
  | _ => true

theorem intervalJoinInstrs_nonHalt (basePc : Nat) :
    (intervalJoinInstrs (bits := bits) basePc).all sliceNonHalt = true := by
  rfl

variable {inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_intervalJoin {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (hPl : Placed code basePc (intervalJoinInstrs (bits := bits) basePc))
    (hSz : basePc + 25 < code.size)
    (srcA srcB dst : Nat) (a b : Interval)
    (hFitSrcA : srcA + 2 < 2 ^ bits) (hFitSrcB : srcB + 2 < 2 ^ bits)
    (hFitDst : dst + 2 < 2 ^ bits) (hDstLt : dst + 2 < workCap)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hr2 : (reg st reg2).val = srcA) (hr3 : (reg st reg3).val = srcB)
    (hr4 : (reg st reg4).val = dst)
    (hA : IntervalWordsAt st.data srcA a) (hB : IntervalWordsAt st.data srcB b) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 21 ∧ Steps code input k st t ∧ t.pc = basePc + 25 ∧
      IntervalWordsAt t.data dst (Interval.join a b) ∧
      (∀ r : Fin 15, r = reg0 ∨ r = reg1 ∨ r = reg2 ∨ r = reg3 ∨ r = reg4 ∨
        r = reg12 ∨ r = reg13 ∨ r = rMeta → reg t r = reg st r) ∧
      (∀ j, (j < dst ∨ dst + 3 ≤ j) → t.data[j]? = st.data[j]?) := by
  have hAtA0 : (st.data[srcA]?).map Fin.val = some (match a with | .empty => 0 | .span _ _ => 1) := by
    cases a <;> exact hA.1
  have hAtA1 : (st.data[srcA + 1]?).map Fin.val = some (match a with | .empty => 0 | .span lo _ => lo) := by
    cases a <;> exact hA.2.1
  have hAtA2 : (st.data[srcA + 2]?).map Fin.val = some (match a with | .empty => 0 | .span _ hi => hi) := by
    cases a <;> exact hA.2.2
  have hAtB0 : (st.data[srcB]?).map Fin.val = some (match b with | .empty => 0 | .span _ _ => 1) := by
    cases b <;> exact hB.1
  have hAtB1 : (st.data[srcB + 1]?).map Fin.val = some (match b with | .empty => 0 | .span lo _ => lo) := by
    cases b <;> exact hB.2.1
  have hAtB2 : (st.data[srcB + 2]?).map Fin.val = some (match b with | .empty => 0 | .span _ hi => hi) := by
    cases b <;> exact hB.2.2
  obtain ⟨wa0, hwa0, hwa0V⟩ := Option.map_eq_some_iff.mp hAtA0
  obtain ⟨wa1, hwa1, hwa1V⟩ := Option.map_eq_some_iff.mp hAtA1
  obtain ⟨wa2, hwa2, hwa2V⟩ := Option.map_eq_some_iff.mp hAtA2
  obtain ⟨wb0, hwb0, hwb0V⟩ := Option.map_eq_some_iff.mp hAtB0
  obtain ⟨wb1, hwb1, hwb1V⟩ := Option.map_eq_some_iff.mp hAtB1
  obtain ⟨wb2, hwb2, hwb2V⟩ := Option.map_eq_some_iff.mp hAtB2
  -- Steps 0..9: load a into r5..r7, b into r8..r10
  obtain ⟨s1, hs1, hpc1, h5_1, ho1, hd1⟩ := step_loadData_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by omega) (by rw [hr2]; exact hwa0)
  have ha1 : code[s1.pc]? = some (.add reg11 reg2 reg1) := by rw [hpc1, hpc]; exact hPl 1 _ rfl
  have h2_1 : (reg s1 reg2).val = srcA := by rw [ho1 reg2 (by intro h; cases h), hr2]
  have h1_1 : (reg s1 reg1).val = 1 := by rw [ho1 reg1 (by intro h; cases h), hr1]
  obtain ⟨s2, hs2, hpc2, h11_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by omega)
  have hA1 : (reg s2 reg11).val = srcA + 1 := by
    rw [h11_2, add_no_wrap _ _ (by rw [h2_1, h1_1]; omega), h2_1, h1_1]
  obtain ⟨s3, hs3, hpc3, h6_3, ho3, hd3⟩ := step_loadData_at (input := input)
    (by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl) (by omega) (by rw [hA1, hd2, hd1]; exact hwa1)
  have h11_3 : (reg s3 reg11).val = srcA + 1 := by rw [ho3 reg11 (by intro h; cases h), hA1]
  have h1_3 : (reg s3 reg1).val = 1 := by
    rw [ho3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), h1_1]
  obtain ⟨s4, hs4, hpc4, h11_4, ho4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl) (by omega)
  have hA2 : (reg s4 reg11).val = srcA + 2 := by
    rw [h11_4, add_no_wrap _ _ (by rw [h11_3, h1_3]; omega), h11_3, h1_3]
  obtain ⟨s5, hs5, hpc5, h7_5, ho5, hd5⟩ := step_loadData_at (input := input)
    (by rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl) (by omega)
    (by rw [hA2, hd4, hd3, hd2, hd1]; exact hwa2)
  have hPres5 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg11 → reg s5 r = reg st r :=
    fun r hr5 hr6 hr7 hr11 => by
      rw [ho5 r hr7, ho4 r hr11, ho3 r hr6, ho2 r hr11, ho1 r hr5]
  have h3_5 : (reg s5 reg3).val = srcB := by
    rw [hPres5 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3]
  have hd5' : s5.data = st.data := by rw [hd5, hd4, hd3, hd2, hd1]
  obtain ⟨s6, hs6, hpc6, h8_6, ho6, hd6⟩ := step_loadData_at (input := input)
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl) (by omega)
    (by rw [h3_5, hd5']; exact hwb0)
  have h3_6 : (reg s6 reg3).val = srcB := by rw [ho6 reg3 (by intro h; cases h), h3_5]
  have h1_6 : (reg s6 reg1).val = 1 := by
    rw [ho6 reg1 (by intro h; cases h),
      hPres5 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
  obtain ⟨s7, hs7, hpc7, h11_7, ho7, hd7⟩ := step_add_at (input := input)
    (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl) (by omega)
  have hB1 : (reg s7 reg11).val = srcB + 1 := by
    rw [h11_7, add_no_wrap _ _ (by rw [h3_6, h1_6]; omega), h3_6, h1_6]
  obtain ⟨s8, hs8, hpc8, h9_8, ho8, hd8⟩ := step_loadData_at (input := input)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 7 _ rfl) (by omega)
    (by rw [hB1, hd7, hd6, hd5']; exact hwb1)
  have h11_8 : (reg s8 reg11).val = srcB + 1 := by rw [ho8 reg11 (by intro h; cases h), hB1]
  have h1_8 : (reg s8 reg1).val = 1 := by
    rw [ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h), h1_6]
  obtain ⟨s9, hs9, hpc9, h11_9, ho9, hd9⟩ := step_add_at (input := input)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 8 _ rfl) (by omega)
  have hB2 : (reg s9 reg11).val = srcB + 2 := by
    rw [h11_9, add_no_wrap _ _ (by rw [h11_8, h1_8]; omega), h11_8, h1_8]
  obtain ⟨s10, hs10, hpc10, h10_10, ho10, hd10⟩ := step_loadData_at (input := input)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 9 _ rfl) (by omega)
    (by rw [hB2, hd9, hd8, hd7, hd6, hd5']; exact hwb2)
  have hPre10 : Steps code input 10 st s10 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (steps_1_of_step hs10)))))))))
  have hPres10 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg9 → r ≠ reg10 →
      r ≠ reg11 → reg s10 r = reg st r := fun r h5 h6 h7 h8 h9 h10 h11 => by
    rw [ho10 r h10, ho9 r h11, ho8 r h9, ho7 r h11, ho6 r h8, hPres5 r h5 h6 h7 h11]
  have hd10' : s10.data = st.data := by rw [hd10, hd9, hd8, hd7, hd6, hd5']
  have hpc10Eq : s10.pc = basePc + 10 := by omega
  have h5_10 : reg s10 reg5 = wa0 := by
    rw [ho10 reg5 (by intro h; cases h), ho9 reg5 (by intro h; cases h), ho8 reg5 (by intro h; cases h),
      ho7 reg5 (by intro h; cases h), ho6 reg5 (by intro h; cases h),
      ho5 reg5 (by intro h; cases h), ho4 reg5 (by intro h; cases h),
      ho3 reg5 (by intro h; cases h), ho2 reg5 (by intro h; cases h), h5_1]
  have h6_10 : reg s10 reg6 = wa1 := by
    rw [ho10 reg6 (by intro h; cases h), ho9 reg6 (by intro h; cases h), ho8 reg6 (by intro h; cases h),
      ho7 reg6 (by intro h; cases h), ho6 reg6 (by intro h; cases h),
      ho5 reg6 (by intro h; cases h), ho4 reg6 (by intro h; cases h), h6_3]
  have h7_10 : reg s10 reg7 = wa2 := by
    rw [ho10 reg7 (by intro h; cases h), ho9 reg7 (by intro h; cases h), ho8 reg7 (by intro h; cases h),
      ho7 reg7 (by intro h; cases h), ho6 reg7 (by intro h; cases h), h7_5]
  have h8_10 : reg s10 reg8 = wb0 := by
    rw [ho10 reg8 (by intro h; cases h), ho9 reg8 (by intro h; cases h), ho8 reg8 (by intro h; cases h),
      ho7 reg8 (by intro h; cases h), h8_6]
  have h9_10 : reg s10 reg9 = wb1 := by
    rw [ho10 reg9 (by intro h; cases h), ho9 reg9 (by intro h; cases h), h9_8]
  have h0_10 : (reg s10 reg0).val = 0 := by
    rw [hPres10 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0]
  -- Now finish cleanly from PC `basePc + 20` once `(r5, r6, r7)` holds `Interval.join a b`:
  have hWriteOut : ∀ (sw : State DomL), sw.pc = basePc + 20 →
      (reg sw reg1).val = 1 → (reg sw reg4).val = dst →
      sw.data = st.data →
      ((reg sw reg5).val = match Interval.join a b with | .empty => 0 | .span _ _ => 1) →
      ((reg sw reg6).val = match Interval.join a b with | .empty => 0 | .span lo _ => lo) →
      ((reg sw reg7).val = match Interval.join a b with | .empty => 0 | .span _ hi => hi) →
      ∃ sEnd : State DomL, Steps code input 5 sw sEnd ∧ sEnd.pc = basePc + 25 ∧
        IntervalWordsAt sEnd.data dst (Interval.join a b) ∧
        (∀ r : Fin 15, r ≠ reg11 → reg sEnd r = reg sw r) ∧
        (∀ j, (j < dst ∨ dst + 3 ≤ j) → sEnd.data[j]? = st.data[j]?) := by
    intro sw hpcW h1W h4W hdW hw5 hw6 hw7
    have hLt0 : (reg sw reg4).val < sw.data.size := lt_data_size (by rw [h4W]; omega)
    obtain ⟨w1, hw1, hpcw1, hregw1, hdw1⟩ := step_storeData_opaque (input := input)
      (by rw [hpcW]; exact hPl 20 _ rfl) hLt0 (by omega)
    have hrw1 := reg_of_regs_eq hregw1
    have h4_w1 : (reg w1 reg4).val = dst := by rw [hrw1, h4W]
    have h1_w1 : (reg w1 reg1).val = 1 := by rw [hrw1, h1W]
    obtain ⟨w2, hw2, hpcw2, h11_w2, how2, hdw2⟩ := step_add_at (input := input)
      (by rw [hpcw1, hpcW]; exact hPl 21 _ rfl) (by omega)
    have hD1 : (reg w2 reg11).val = dst + 1 := by
      rw [h11_w2, add_no_wrap _ _ (by rw [h4_w1, h1_w1]; omega), h4_w1, h1_w1]
    have hLt1 : (reg w2 reg11).val < w2.data.size := lt_data_size (by rw [hD1]; omega)
    obtain ⟨w3, hw3, hpcw3, hregw3, hdw3⟩ := step_storeData_opaque (input := input)
      (by rw [hpcw2, hpcw1, hpcW]; exact hPl 22 _ rfl) hLt1 (by omega)
    have hrw3 := reg_of_regs_eq hregw3
    have h11_w3 : (reg w3 reg11).val = dst + 1 := by rw [hrw3, hD1]
    have h1_w3 : (reg w3 reg1).val = 1 := by rw [hrw3, how2 reg1 (by intro h; cases h), h1_w1]
    obtain ⟨w4, hw4, hpcw4, h11_w4, how4, hdw4⟩ := step_add_at (input := input)
      (by rw [hpcw3, hpcw2, hpcw1, hpcW]; exact hPl 23 _ rfl) (by omega)
    have hD2 : (reg w4 reg11).val = dst + 2 := by
      rw [h11_w4, add_no_wrap _ _ (by rw [h11_w3, h1_w3]; omega), h11_w3, h1_w3]
    have hLt2 : (reg w4 reg11).val < w4.data.size := lt_data_size (by rw [hD2]; omega)
    obtain ⟨w5, hw5Step, hpcw5, hregw5, hdw5⟩ := step_storeData_opaque (input := input)
      (by rw [hpcw4, hpcw3, hpcw2, hpcw1, hpcW]; exact hPl 24 _ rfl) hLt2 (by omega)
    have hrw5 := reg_of_regs_eq hregw5
    have hPresW : ∀ r : Fin 15, r ≠ reg11 → reg w5 r = reg sw r := fun r hr => by
      rw [hrw5, how4 r hr, hrw3, how2 r hr, hrw1]
    have hAtOut : ∀ a, w5.data[a]? =
        if a = dst + 2 then some (reg w4 reg7)
        else if a = dst + 1 then some (reg w2 reg6)
        else if a = dst then some (reg sw reg5)
        else st.data[a]? := by
      intro a
      rw [hdw5]
      by_cases ha2 : a = dst + 2
      · subst a
        rw [ite_eq_left rfl, ← hD2, Array.getElem?_set_self hLt2]
      · rw [ite_eq_right ha2, Array.getElem?_set_ne hLt2 (by rw [hD2]; exact Ne.symm ha2),
          hdw4, hdw3]
        by_cases ha1 : a = dst + 1
        · subst a
          rw [ite_eq_left rfl, ← hD1, Array.getElem?_set_self hLt1]
        · rw [ite_eq_right ha1, Array.getElem?_set_ne hLt1 (by rw [hD1]; exact Ne.symm ha1),
            hdw2, hdw1]
          by_cases ha0 : a = dst
          · subst a
            rw [ite_eq_left rfl, ← h4W, Array.getElem?_set_self hLt0]
          · rw [ite_eq_right ha0, Array.getElem?_set_ne hLt0 (by rw [h4W]; exact Ne.symm ha0), hdW]
    have h6_w2 : (reg w2 reg6).val = (reg sw reg6).val := by
      rw [how2 reg6 (by intro h; cases h), hrw1]
    have h7_w4 : (reg w4 reg7).val = (reg sw reg7).val := by
      rw [how4 reg7 (by intro h; cases h), hrw3, how2 reg7 (by intro h; cases h), hrw1]
    refine ⟨w5, Steps.cons hw1 (Steps.cons hw2 (Steps.cons hw3 (Steps.cons hw4 (steps_1_of_step hw5Step)))),
      by omega, ?_, hPresW, fun j hj => ?_⟩
    · cases hJoin : Interval.join a b with
      | empty =>
        refine ⟨?_, ?_, ?_⟩
        · rw [hAtOut dst, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hw5, hJoin]
        · rw [hAtOut (dst + 1), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, h6_w2, hw6, hJoin]
        · rw [hAtOut (dst + 2), ite_eq_left rfl, Option.map_some, h7_w4, hw7, hJoin]
      | span lo hi =>
        refine ⟨?_, ?_, ?_⟩
        · rw [hAtOut dst, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, hw5, hJoin]
        · rw [hAtOut (dst + 1), ite_eq_right (by omega), ite_eq_left rfl, Option.map_some, h6_w2, hw6, hJoin]
        · rw [hAtOut (dst + 2), ite_eq_left rfl, Option.map_some, h7_w4, hw7, hJoin]
    · rw [hAtOut j, ite_eq_right (by rcases hj with h | h <;> omega),
        ite_eq_right (by rcases hj with h | h <;> omega), ite_eq_right (by rcases hj with h | h <;> omega)]
  -- Execute decision tree from basePc + 10
  obtain ⟨s11, hs11, hpc11, hr11, hd11⟩ := step_branchLt_at (input := input)
    (by rw [hpc10Eq]; exact hPl 10 _ rfl) (by split <;> omega)
  have hr11F := reg_of_regs_eq hr11
  cases a with
  | empty =>
    change wa0.val = 0 at hwa0V
    rw [ite_eq_right (by rw [h0_10, h5_10, hwa0V]; simp)] at hpc11
    obtain ⟨s12, hs12, hpc12, h5_12, ho12, hd12⟩ := step_mov_at (input := input)
      (by rw [hpc11]; exact hPl 11 _ rfl) (by omega)
    obtain ⟨s13, hs13, hpc13, h6_13, ho13, hd13⟩ := step_mov_at (input := input)
      (by rw [hpc12, hpc11]; exact hPl 12 _ rfl) (by omega)
    obtain ⟨s14, hs14, hpc14, h7_14, ho14, hd14⟩ := step_mov_at (input := input)
      (by rw [hpc13, hpc12, hpc11]; exact hPl 13 _ rfl) (by omega)
    obtain ⟨s15, hs15, hpc15, hr15, hd15⟩ := step_goto_at (input := input)
      (by rw [hpc14, hpc13, hpc12, hpc11]; exact hPl 14 _ rfl) (by omega)
    have hr15F := reg_of_regs_eq hr15
    have hPresMid : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg9 →
        r ≠ reg10 → r ≠ reg11 → reg s15 r = reg st r := fun r h5 h6 h7 h8 h9 h10 h11 => by
      rw [hr15F, ho14 r h7, ho13 r h6, ho12 r h5, hr11F, hPres10 r h5 h6 h7 h8 h9 h10 h11]
    obtain ⟨sEnd, hStepsW, hpcEnd, hOut, hPresW, hFrW⟩ := hWriteOut s15 hpc15
      (by rw [hPresMid reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1])
      (by rw [hPresMid reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4])
      (by rw [hd15, hd14, hd13, hd12, hd11, hd10'])
      (by rw [hr15F, ho14 reg5 (by intro h; cases h), ho13 reg5 (by intro h; cases h), h5_12,
        hr11F, h8_10, hwb0V]; cases b <;> rfl)
      (by rw [hr15F, ho14 reg6 (by intro h; cases h), h6_13, ho12 reg9 (by intro h; cases h),
        hr11F, h9_10, hwb1V]; cases b <;> rfl)
      (by rw [hr15F, h7_14, ho13 reg10 (by intro h; cases h), ho12 reg10 (by intro h; cases h),
        hr11F, h10_10, hwb2V]; cases b <;> rfl)
    refine ⟨15 + 5, sEnd, by omega,
      (hPre10.append (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (steps_1_of_step hs15)))))).append hStepsW,
      hpcEnd, hOut, fun r hr => ?_, hFrW⟩
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [hPresW _ (by intro h; cases h), hPresMid _ (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
  | span loA hiA =>
    change wa0.val = 1 at hwa0V
    change wa1.val = loA at hwa1V
    change wa2.val = hiA at hwa2V
    rw [ite_eq_left (by rw [h0_10, h5_10, hwa0V]; omega)] at hpc11
    obtain ⟨s12, hs12, hpc12, hr12, hd12⟩ := step_branchLt_at (input := input)
      (by rw [hpc11]; exact hPl 15 _ rfl) (by split <;> omega)
    have hr12F := reg_of_regs_eq hr12
    cases b with
    | empty =>
      change wb0.val = 0 at hwb0V
      rw [ite_eq_right (by simp only [hr11F, h0_10, h8_10, hwb0V, Nat.lt_irrefl, not_false_eq_true])] at hpc12
      have hPresMid : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg9 →
          r ≠ reg10 → r ≠ reg11 → reg s12 r = reg st r := fun r h5 h6 h7 h8 h9 h10 h11 => by
        rw [hr12F, hr11F, hPres10 r h5 h6 h7 h8 h9 h10 h11]
      obtain ⟨sEnd, hStepsW, hpcEnd, hOut, hPresW, hFrW⟩ := hWriteOut s12 hpc12
        (by rw [hPresMid reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1])
        (by rw [hPresMid reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4])
        (by rw [hd12, hd11, hd10'])
        (by rw [hr12F, hr11F, h5_10, hwa0V]; rfl)
        (by rw [hr12F, hr11F, h6_10, hwa1V]; rfl)
        (by rw [hr12F, hr11F, h7_10, hwa2V]; rfl)
      refine ⟨12 + 5, sEnd, by omega,
        (hPre10.append (Steps.cons hs11 (steps_1_of_step hs12))).append hStepsW,
        hpcEnd, hOut, fun r hr => ?_, hFrW⟩
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hPresW _ (by intro h; cases h), hPresMid _ (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]
    | span loB hiB =>
      change wb0.val = 1 at hwb0V
      change wb1.val = loB at hwb1V
      change wb2.val = hiB at hwb2V
      rw [ite_eq_left (by simp only [hr11F, h0_10, h8_10, hwb0V]; decide)] at hpc12
      -- Step 16..19: min loA loB -> r6, max hiA hiB -> r7
      obtain ⟨s13, hs13, hpc13, hr13, hd13⟩ := step_branchLt_at (input := input)
        (by rw [hpc12]; exact hPl 16 _ rfl) (by split <;> omega)
      have hr13F := reg_of_regs_eq hr13
      have hMinJoin : ∃ (kMin : Nat) (sMin : State DomL),
          kMin ≤ 1 ∧ Steps code input kMin s13 sMin ∧ sMin.pc = basePc + 18 ∧
          sMin.data = st.data ∧ (reg sMin reg5).val = 1 ∧ (reg sMin reg6).val = min loA loB ∧
          (reg sMin reg7).val = hiA ∧ (reg sMin reg10).val = hiB ∧
          ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg9 →
            r ≠ reg10 → r ≠ reg11 → reg sMin r = reg st r := by
        by_cases hMin : loB < loA
        · rw [ite_eq_left (by simpa only [hr12F, hr11F, h9_10, h6_10, hwb1V, hwa1V] using hMin)] at hpc13
          obtain ⟨sM, hsM, hpcM, h6M, hoM, hdM⟩ := step_mov_at (input := input)
            (by rw [hpc13]; exact hPl 17 _ rfl) (by omega)
          refine ⟨1, sM, Nat.le_refl _, steps_1_of_step hsM, by rw [hpcM, hpc13],
            by rw [hdM, hd13, hd12, hd11, hd10'],
            by rw [hoM reg5 (by intro h; cases h), hr13F, hr12F, hr11F, h5_10, hwa0V],
            by rw [h6M, hr13F, hr12F, hr11F, h9_10, hwb1V, Nat.min_eq_right (Nat.le_of_lt hMin)],
            by rw [hoM reg7 (by intro h; cases h), hr13F, hr12F, hr11F, h7_10, hwa2V],
            by rw [hoM reg10 (by intro h; cases h), hr13F, hr12F, hr11F, h10_10, hwb2V],
            fun r h5 h6 h7 h8 h9 h10 h11 => by
              rw [hoM r h6, hr13F, hr12F, hr11F, hPres10 r h5 h6 h7 h8 h9 h10 h11]⟩
        · rw [ite_eq_right (by simpa only [hr12F, hr11F, h9_10, h6_10, hwb1V, hwa1V] using hMin)] at hpc13
          refine ⟨0, s13, Nat.zero_le _, Steps.zero s13, hpc13,
            by rw [hd13, hd12, hd11, hd10'],
            by rw [hr13F, hr12F, hr11F, h5_10, hwa0V],
            by rw [hr13F, hr12F, hr11F, h6_10, hwa1V, Nat.min_eq_left (Nat.le_of_not_gt hMin)],
            by rw [hr13F, hr12F, hr11F, h7_10, hwa2V],
            by rw [hr13F, hr12F, hr11F, h10_10, hwb2V],
            fun r h5 h6 h7 h8 h9 h10 h11 => by
              rw [hr13F, hr12F, hr11F, hPres10 r h5 h6 h7 h8 h9 h10 h11]⟩
      obtain ⟨kMin, sMin, hkMin, hStepsMin, hpcMin, hdMin', h5Min, h6Min, h7Min, h10Min, hPresMin⟩ := hMinJoin
      obtain ⟨s14, hs14, hpc14, hr14, hd14⟩ := step_branchLt_at (input := input)
        (by rw [hpcMin]; exact hPl 18 _ rfl) (by split <;> omega)
      have hr14F := reg_of_regs_eq hr14
      have hMaxJoin : ∃ (kMax : Nat) (sMax : State DomL),
          kMax ≤ 1 ∧ Steps code input kMax s14 sMax ∧ sMax.pc = basePc + 20 ∧
          sMax.data = st.data ∧ (reg sMax reg5).val = 1 ∧ (reg sMax reg6).val = min loA loB ∧
          (reg sMax reg7).val = max hiA hiB ∧
          ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg9 →
            r ≠ reg10 → r ≠ reg11 → reg sMax r = reg st r := by
        by_cases hMax : hiA < hiB
        · rw [ite_eq_left (by rw [h7Min, h10Min]; exact hMax)] at hpc14
          obtain ⟨sM, hsM, hpcM, h7M, hoM, hdM⟩ := step_mov_at (input := input)
            (by rw [hpc14]; exact hPl 19 _ rfl) (by omega)
          refine ⟨1, sM, Nat.le_refl _, steps_1_of_step hsM, by rw [hpcM, hpc14],
            by rw [hdM, hd14, hdMin'],
            by rw [hoM reg5 (by intro h; cases h), hr14F, h5Min],
            by rw [hoM reg6 (by intro h; cases h), hr14F, h6Min],
            by rw [h7M, hr14F, h10Min, Nat.max_eq_right (Nat.le_of_lt hMax)],
            fun r h5 h6 h7 h8 h9 h10 h11 => by
              rw [hoM r h7, hr14F, hPresMin r h5 h6 h7 h8 h9 h10 h11]⟩
        · rw [ite_eq_right (by rw [h7Min, h10Min]; exact hMax)] at hpc14
          refine ⟨0, s14, Nat.zero_le _, Steps.zero s14, hpc14,
            by rw [hd14, hdMin'],
            by rw [hr14F, h5Min],
            by rw [hr14F, h6Min],
            by rw [hr14F, h7Min, Nat.max_eq_left (Nat.le_of_not_gt hMax)],
            fun r h5 h6 h7 h8 h9 h10 h11 => by
              rw [hr14F, hPresMin r h5 h6 h7 h8 h9 h10 h11]⟩
      obtain ⟨kMax, sMax, hkMax, hStepsMax, hpcMax, hdMax', h5Max, h6Max, h7Max, hPresMax⟩ := hMaxJoin
      obtain ⟨sEnd, hStepsW, hpcEnd, hOut, hPresW, hFrW⟩ := hWriteOut sMax hpcMax
        (by rw [hPresMax reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1])
        (by rw [hPresMax reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4])
        hdMax' h5Max h6Max h7Max
      refine ⟨13 + kMin + 1 + kMax + 5, sEnd, by omega,
        ((((hPre10.append (Steps.cons hs11 (Steps.cons hs12 (steps_1_of_step hs13)))).append
          hStepsMin).append (steps_1_of_step hs14)).append hStepsMax).append hStepsW,
        hpcEnd, hOut, fun r hr => ?_, hFrW⟩
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rw [hPresW _ (by intro h; cases h), hPresMax _ (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)]

end IntervalJoinSlice

end Stage4Helpers

end PaperB.RamProgram.ExitSummaryBuild
