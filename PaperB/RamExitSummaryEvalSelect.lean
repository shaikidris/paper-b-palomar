module

public import PaperB.RamExitSummaryEvalROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

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

/-! Read a live record and select its next vertex and map in 19 RAM steps. -/

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_eval15Select {code : Program DomL} {input : Input DomL}
    {basePc : Nat} {h100 : 100 ≤ 2 ^ bits}
    (hPl : Placed code basePc (eval15Instrs basePc h100))
    (hSz : basePc + 161 < code.size)
    {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    {n m N u targetD : Nat} (huLive : live u) (huLt : u < N)
    (hFSize : F.size = N)
    (hMetaFit : metaArrBase n m N + 48 ≤ workCap)
    {s4 : State DomL} (hpc : s4.pc = basePc + 8)
    (h0 : (reg s4 reg0).val = 0) (h1 : (reg s4 reg1).val = 1)
    (hM : (reg s4 rMeta).val = metaArrBase n m N)
    (hU : (reg s4 reg2).val = u) (hD : (reg s4 reg4).val = targetD)
    (hMetaSB : (s4.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N))
    (hDepth : ∀ w : Fin N, (s4.data[w.val]?).map Fin.val = some (F.depthOf w.val))
    (hStU : (s4.data[storedBase N + 18 * u]?).map Fin.val = some (ref u).parent ∧
      (s4.data[storedBase N + 18 * u + 1]?).map Fin.val = some (ref u).jump) :
    let mv := selectAtDepth F.depthOf targetD (ref u)
    let mapAddr :=
      if targetD ≤ F.depthOf (ref u).jump then storedBase N + 18 * u + 10
      else storedBase N + 18 * u + 2
    ∃ t : State DomL, Steps code input 19 s4 t ∧ t.pc = basePc + 33 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = metaArrBase n m N ∧ (reg t reg2).val = mapAddr ∧
      (t.data[metaArrBase n m N + mIdxEvalU]?).map Fin.val = some mv.dst ∧
      (∀ j, j ≠ metaArrBase n m N + mIdxEvalU → t.data[j]? = s4.data[j]?) := by
  have hStoreStart : N ≤ storedBase N := Nat.le_refl _
  have hStBound : storedBase N + 18 * N ≤ metaArrBase n m N := by
    unfold storedBase
    rw [metaArrBase_eq]
    omega
  have hPlSB : Placed code (basePc + 8) (metaLoadInstrs (bits := bits) reg6 reg5 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega)) := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (8 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi)
  have hPlStoreU1 : Placed code (basePc + 23) (metaStoreInstrs (bits := bits) reg7 reg5 mIdxEvalU (by dsimp only [mIdxEvalU]; omega)) := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (23 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi)
  have hPlStoreU2 : Placed code (basePc + 30) (metaStoreInstrs (bits := bits) reg7 reg5 mIdxEvalU (by dsimp only [mIdxEvalU]; omega)) := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (30 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi)
  obtain ⟨s5, hs5, hpc5, hd5, h6_5, ho5⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSB (by omega) hpc hM (by dsimp only [mIdxStoredBase]; omega)
    hMetaSB
  have h2_5 : (reg s5 reg2).val = u := by
    rw [ho5 reg2 (by intro h; cases h) (by intro h; cases h), hU]
  -- `mul18Instrs reg7 reg5 reg2` at 11..15
  obtain ⟨s6, hs6, hpc6, h5_6, ho6, hd6⟩ := step_add_at (input := input)
    (by rw [hpc5]; exact hPl 11 _ rfl) (by omega)
  have h5V6 : (reg s6 reg5).val = 2 * u := by
    rw [h5_6, add_no_wrap _ _ (by rw [h2_5]; omega), h2_5]; omega
  obtain ⟨s7, hs7, hpc7, h7_7, ho7, hd7⟩ := step_add_at (input := input)
    (by rw [hpc6, hpc5]; exact hPl 12 _ rfl) (by omega)
  have h7V7 : (reg s7 reg7).val = 4 * u := by
    rw [h7_7, add_no_wrap _ _ (by rw [h5V6]; omega), h5V6]; omega
  obtain ⟨s8, hs8, hpc8, h7_8, ho8, hd8⟩ := step_add_at (input := input)
    (by rw [hpc7, hpc6, hpc5]; exact hPl 13 _ rfl) (by omega)
  have h7V8 : (reg s8 reg7).val = 8 * u := by
    rw [h7_8, add_no_wrap _ _ (by rw [h7V7]; omega), h7V7]; omega
  obtain ⟨s9, hs9, hpc9, h7_9, ho9, hd9⟩ := step_add_at (input := input)
    (by rw [hpc8, hpc7, hpc6, hpc5]; exact hPl 14 _ rfl) (by omega)
  have h7V9 : (reg s9 reg7).val = 16 * u := by
    rw [h7_9, add_no_wrap _ _ (by rw [h7V8]; omega), h7V8]; omega
  have h5_9 : (reg s9 reg5).val = 2 * u := by
    rw [ho9 reg5 (by intro h; cases h), ho8 reg5 (by intro h; cases h),
      ho7 reg5 (by intro h; cases h), h5V6]
  obtain ⟨s10, hs10, hpc10, h7_10, ho10, hd10⟩ := step_add_at (input := input)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5]; exact hPl 15 _ rfl) (by omega)
  have h7V10 : (reg s10 reg7).val = 18 * u := by
    rw [h7_10, add_no_wrap _ _ (by rw [h7V9, h5_9]; omega), h7V9, h5_9]; omega
  have h6_10 : (reg s10 reg6).val = storedBase N := by
    rw [ho10 reg6 (by intro h; cases h), ho9 reg6 (by intro h; cases h),
      ho8 reg6 (by intro h; cases h), ho7 reg6 (by intro h; cases h),
      ho6 reg6 (by intro h; cases h), h6_5]
  obtain ⟨s11, hs11, hpc11, h6_11, ho11, hd11⟩ := step_add_at (input := input)
    (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hPl 16 _ rfl) (by omega)
  have hSlotAddr : (reg s11 reg6).val = storedBase N + 18 * u := by
    rw [h6_11, add_no_wrap _ _ (by rw [h6_10, h7V10]; omega), h6_10, h7V10]
  have hPres11 : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → r ≠ reg6 →
      r ≠ reg7 → reg s11 r = reg s4 r := fun r hr2 hr3 hr4 hr5 hr6 hr7 => by
    rw [ho11 r hr6, ho10 r hr7, ho9 r hr7, ho8 r hr7, ho7 r hr7, ho6 r hr5,
      ho5 r hr6 hr5]
  have h1_11 : (reg s11 reg1).val = 1 := by
    rw [hPres11 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1]
  obtain ⟨s12, hs12, hpc12, h7_12, ho12, hd12⟩ := step_add_at (input := input)
    (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hPl 17 _ rfl) (by omega)
  have hJAddr : (reg s12 reg7).val = storedBase N + 18 * u + 1 := by
    rw [h7_12, add_no_wrap _ _ (by rw [hSlotAddr, h1_11]; omega), hSlotAddr, h1_11]
  have hd12' : s12.data = s4.data := by
    rw [hd12, hd11, hd10, hd9, hd8, hd7, hd6, hd5]

  obtain ⟨wJ, hwJ, hwJV⟩ := Option.map_eq_some_iff.mp hStU.2
  obtain ⟨s13, hs13, hpc13, h7_13, ho13, hd13⟩ := step_loadData_at (input := input)
    (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hPl 18 _ rfl) (by omega)
    (by rw [hJAddr, hd12']; exact hwJ)
  have hJVal : (reg s13 reg7).val = (ref u).jump := by rw [h7_13, hwJV]
  have hJNatEq : (ref u).jump = F.jumpOf u := ok.jump_eq u huLive
  have hJLt : F.jumpOf u < N := hFSize ▸ valid.jumpOf_lt_size (hFSize.symm ▸ huLt)
  obtain ⟨wDJ, hwDJ, hwDJV⟩ := Option.map_eq_some_iff.mp (hDepth ⟨F.jumpOf u, hJLt⟩)
  obtain ⟨s14, hs14, hpc14, h8_14, ho14, hd14⟩ := step_loadData_at (input := input)
    (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hPl 19 _ rfl) (by omega)
    (by rw [hJVal, hJNatEq, hd13, hd12']; exact hwDJ)
  have hDJVal : (reg s14 reg8).val = F.depthOf (F.jumpOf u) := by rw [h8_14, hwDJV]
  have hPres14 : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → r ≠ reg6 →
      r ≠ reg7 → r ≠ reg8 → reg s14 r = reg s4 r := fun r hr2 hr3 hr4 hr5 hr6 hr7 hr8 => by
    rw [ho14 r hr8, ho13 r hr7, ho12 r hr7, hPres11 r hr2 hr3 hr4 hr5 hr6 hr7]
  have h4_14 : (reg s14 reg4).val = targetD := by
    rw [ho14 reg4 (by intro h; cases h), ho13 reg4 (by intro h; cases h), ho12 reg4 (by intro h; cases h),
      ho11 reg4 (by intro h; cases h), ho10 reg4 (by intro h; cases h), ho9 reg4 (by intro h; cases h),
      ho8 reg4 (by intro h; cases h), ho7 reg4 (by intro h; cases h), ho6 reg4 (by intro h; cases h),
      ho5 reg4 (by intro h; cases h) (by intro h; cases h), hD]
  obtain ⟨s15, hs15, hpc15, hr15, hd15⟩ := step_branchLt_at (input := input)
    (by rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hPl 20 _ rfl)
    (by split <;> omega)
  have hr15F := reg_of_regs_eq hr15
  have hd15' : s15.data = s4.data := by rw [hd15, hd14, hd13, hd12']
  have h6_15 : (reg s15 reg6).val = storedBase N + 18 * u := by
    rw [hr15F, ho14 reg6 (by intro h; cases h), ho13 reg6 (by intro h; cases h),
      ho12 reg6 (by intro h; cases h), hSlotAddr]
  have hPre13 : Steps code input 13 s4 s15 :=
    hs5.append (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
      (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13
        (Steps.cons hs14 (steps_1_of_step hs15))))))))))
  let mv := selectAtDepth F.depthOf targetD (ref u)
  let mapAddr : Nat :=
    if targetD ≤ F.depthOf (ref u).jump then storedBase N + 18 * u + 10 else storedBase N + 18 * u + 2
  have hFitEvalU : metaArrBase n m N + mIdxEvalU < 2 ^ bits := by
    dsimp only [mIdxEvalU]; omega
  have hLtEvalU : metaArrBase n m N + mIdxEvalU < s4.data.size :=
    lt_data_size (by dsimp only [mIdxEvalU]; omega)
  have hBranch21 : ∃ s21 : State DomL, Steps code input 6 s15 s21 ∧ s21.pc = basePc + 33 ∧
      (reg s21 reg0).val = 0 ∧ (reg s21 reg1).val = 1 ∧ (reg s21 rMeta).val = metaArrBase n m N ∧
      (reg s21 reg2).val = mapAddr ∧
      (s21.data[metaArrBase n m N + mIdxEvalU]?).map Fin.val = some mv.dst ∧
      (∀ j, j ≠ metaArrBase n m N + mIdxEvalU → s21.data[j]? = s4.data[j]?) := by
    have h0_15 : (reg s15 reg0).val = 0 := by
      rw [hr15F, hPres14 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0]
    have h1_15 : (reg s15 reg1).val = 1 := by
      rw [hr15F, hPres14 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1]
    have hM_15 : (reg s15 rMeta).val = metaArrBase n m N := by
      rw [hr15F, hPres14 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM]
    have h7_15 : (reg s15 reg7).val = (ref u).jump := by
      rw [hr15F, ho14 reg7 (by intro h; cases h), hJVal]
    by_cases hJCond : targetD ≤ F.depthOf (ref u).jump
    · have hBrTrue : ¬ (reg s14 reg8).val < (reg s14 reg4).val := by
        rw [hDJVal, h4_14, ← hJNatEq]; omega
      rw [ite_eq_right hBrTrue] at hpc15
      obtain ⟨s16, hs16, hpc16, h5_16, ho16, hd16⟩ := step_imm_at (input := input)
        (by rw [hpc15]; exact hPl 21 _ rfl) (by omega)
      have h6_16 : (reg s16 reg6).val = storedBase N + 18 * u := by
        rw [ho16 reg6 (by intro h; cases h), h6_15]
      have h5V16 : (reg s16 reg5).val = 10 := by rw [h5_16]
      obtain ⟨s17, hs17, hpc17, h2_17, ho17, hd17⟩ := step_add_at (input := input)
        (by rw [hpc16, hpc15]; exact hPl 22 _ rfl) (by omega)
      have h2V17 : (reg s17 reg2).val = storedBase N + 18 * u + 10 := by
        rw [h2_17, add_no_wrap _ _ (by rw [h6_16, h5V16]; omega), h6_16, h5V16]
      have hM_17 : (reg s17 rMeta).val = metaArrBase n m N := by
        rw [ho17 rMeta (by intro h; cases h), ho16 rMeta (by intro h; cases h), hM_15]
      have hd17' : s17.data = s4.data := by rw [hd17, hd16, hd15']
      obtain ⟨s20, hs20, hpc20, hs20At, hs20Fr, ho20⟩ := run_metaStore_slice (input := input)
        (by intro h; cases h) (by intro h; cases h) hPlStoreU1 (by omega) (by rw [hpc17, hpc16, hpc15])
        hM_17 hFitEvalU (by rw [hd17']; exact hLtEvalU)
      obtain ⟨s21, hs21, hpc21, hr21, hd21⟩ := step_goto_at (input := input)
        (by rw [hpc20]; exact hPl 26 _ rfl) (by omega)
      have hr21F := reg_of_regs_eq hr21
      refine ⟨s21, Steps.cons hs16 (Steps.cons hs17 (hs20.append (steps_1_of_step hs21))),
        hpc21,
        by rw [hr21F, ho20 reg0 (by intro h; cases h), ho17 reg0 (by intro h; cases h), ho16 reg0 (by intro h; cases h), h0_15],
        by rw [hr21F, ho20 reg1 (by intro h; cases h), ho17 reg1 (by intro h; cases h), ho16 reg1 (by intro h; cases h), h1_15],
        by rw [hr21F, ho20 rMeta (by intro h; cases h), hM_17],
        by dsimp only [mapAddr]; rw [ite_eq_left hJCond, hr21F, ho20 reg2 (by intro h; cases h), h2V17],
        by rw [hd21, hs20At, Option.map_some, ho17 reg7 (by intro h; cases h), ho16 reg7 (by intro h; cases h), h7_15]
           dsimp only [mv, selectAtDepth]; rw [ite_eq_left hJCond]; rfl,
        fun j hj => by rw [hd21, hs20Fr j hj, hd17']⟩
    · have hBrFalse : (reg s14 reg8).val < (reg s14 reg4).val := by
        rw [hDJVal, h4_14, ← hJNatEq]; omega
      rw [ite_eq_left hBrFalse] at hpc15
      obtain ⟨wP, hwP, hwPV⟩ := Option.map_eq_some_iff.mp hStU.1
      obtain ⟨s16, hs16, hpc16, h7_16, ho16, hd16⟩ := step_loadData_at (input := input)
        (by rw [hpc15]; exact hPl 27 _ rfl) (by omega) (by rw [h6_15, hd15']; exact hwP)
      have h1_16 : (reg s16 reg1).val = 1 := by rw [ho16 reg1 (by intro h; cases h), h1_15]
      obtain ⟨s17, hs17, hpc17, h2_17, ho17, hd17⟩ := step_add_at (input := input)
        (by rw [hpc16, hpc15]; exact hPl 28 _ rfl) (by omega)
      have h2V17 : (reg s17 reg2).val = 2 := by
        rw [h2_17, add_no_wrap _ _ (by rw [h1_16]; omega), h1_16]
      have h6_17 : (reg s17 reg6).val = storedBase N + 18 * u := by
        rw [ho17 reg6 (by intro h; cases h), ho16 reg6 (by intro h; cases h), h6_15]
      obtain ⟨s18, hs18, hpc18, h2_18, ho18, hd18⟩ := step_add_at (input := input)
        (by rw [hpc17, hpc16, hpc15]; exact hPl 29 _ rfl) (by omega)
      have h2V18 : (reg s18 reg2).val = storedBase N + 18 * u + 2 := by
        rw [h2_18, add_no_wrap _ _ (by rw [h6_17, h2V17]; omega), h6_17, h2V17]
      have hM_18 : (reg s18 rMeta).val = metaArrBase n m N := by
        rw [ho18 rMeta (by intro h; cases h), ho17 rMeta (by intro h; cases h),
          ho16 rMeta (by intro h; cases h), hM_15]
      have hd18' : s18.data = s4.data := by rw [hd18, hd17, hd16, hd15']
      obtain ⟨s21, hs21, hpc21, hs21At, hs21Fr, ho21⟩ := run_metaStore_slice (input := input)
        (by intro h; cases h) (by intro h; cases h) hPlStoreU2 (by omega) (by rw [hpc18, hpc17, hpc16, hpc15])
        hM_18 hFitEvalU (by rw [hd18']; exact hLtEvalU)
      refine ⟨s21, Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 hs21)),
        by rw [hpc21],
        by rw [ho21 reg0 (by intro h; cases h), ho18 reg0 (by intro h; cases h), ho17 reg0 (by intro h; cases h), ho16 reg0 (by intro h; cases h), h0_15],
        by rw [ho21 reg1 (by intro h; cases h), ho18 reg1 (by intro h; cases h), ho17 reg1 (by intro h; cases h), h1_16],
        by rw [ho21 rMeta (by intro h; cases h), hM_18],
        by dsimp only [mapAddr]; rw [ite_eq_right hJCond, ho21 reg2 (by intro h; cases h), h2V18],
        by rw [hs21At, Option.map_some, ho18 reg7 (by intro h; cases h), ho17 reg7 (by intro h; cases h),
             h7_16, hwPV]
           dsimp only [mv, selectAtDepth]; rw [ite_eq_right hJCond]; rfl,
        fun j hj => by rw [hs21Fr j hj, hd18']⟩
  obtain ⟨t, hSteps, hpc', hr0, hr1, hrM, hr2, hEvalU, hFrame⟩ := hBranch21
  exact ⟨t, hPre13.append hSteps, hpc', hr0, hr1, hrM, hr2, hEvalU, hFrame⟩

end PaperB.RamProgram.ExitSummaryBuild
