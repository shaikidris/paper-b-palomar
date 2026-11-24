module

public import PaperB.RamExitSummarySweepBJumpFirst
public import PaperB.RamExitSummarySweepBJumpSecond
public import PaperB.RamExitSummarySweepAROM
public import PaperB.RamExitSummarySweepBCopy

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

/-! Correctness and operation count for the cached jump-map update. -/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add_no_wrap)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.ArcParents
open PaperB.ExitMap

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4B_jumpMap_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4BOneNodeInstrs (bits := bits) basePc h100))
    (hSz : basePc + 1039 < code.size)
    (n m N nGlobal : Nat) (w pN jN aJ : Nat)
    (hwLt : w < N) (hpLt : pN < N) (haJLt : aJ < N)
    (hBoundMeta : metaArrBase n m N + 64 ≤ workCap)
    (pm parentJump ancestorJump : Map)
    (st : State DomL) (hpc : st.pc = basePc + 703)
    (hMeta : MetaReady st n m N nGlobal)
    (h48 : (st.data[metaArrBase n m N + 48]?).map Fin.val = some pN)
    (h49 : (st.data[metaArrBase n m N + 49]?).map Fin.val = some jN)
    (h55 : (st.data[metaArrBase n m N + 55]?).map Fin.val = some (storedBase N + 18 * w))
    (hPMW : MapWordsAt st.data (storedBase N + 18 * w + 2) pm)
    (hJumpP : (st.data[storedBase N + 18 * pN + 1]?).map Fin.val = some aJ)
    (hStP : MapWordsAt st.data (storedBase N + 18 * pN + 10) parentJump)
    (hStAJ : MapWordsAt st.data (storedBase N + 18 * aJ + 10) ancestorJump) :
    let jm := if jN = pN then pm else Map.compose pm (Map.compose parentJump ancestorJump)
    ∃ k t, k ≤ 250 ∧ Steps code input k st t ∧ t.pc = basePc + 1039 ∧
      MetaReady t n m N nGlobal ∧
      MapWordsAt t.data (storedBase N + 18 * w + 10) jm ∧
      (∀ j, (j < storedBase N + 18 * w + 10 ∨
          (storedBase N + 18 * w + 18 ≤ j ∧ j < metaArrBase n m N + 56) ∨
          metaArrBase n m N + 64 ≤ j) → t.data[j]? = st.data[j]?) := by
  let metaBase := metaArrBase n m N
  intro jm
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  change metaBase + 64 ≤ workCap at hBoundMeta
  have hRM : (reg st rMeta).val = metaBase := hMeta.rMeta_eq
  obtain ⟨hSelect, hComposeFirst, hComposeSecond, hCopy⟩ := step4B_jump_placed hPl
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits := by omega
  have recordEnd (u : Nat) (hu : u < N) : storedBase N + 18 * u + 18 ≤ metaBase := by
    unfold storedBase
    omega
  have recordFit (u off : Nat) (hu : u < N) (hOff : off < 18) :
      storedBase N + 18 * u + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (by have := recordEnd u hu; omega) hWorkFit
  have hWEnd := recordEnd w hwLt
  have hPlP : Placed code (basePc + 703) (metaLoadInstrs (bits := bits) reg2 reg4 48 (by omega)) := by
    exact Placed_window hSelect 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlP (by omega) hpc hRM (hOffsetFit 48 (by decide)) h48
  have hM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hRM]
  have hPlJ : Placed code (basePc + 706) (metaLoadInstrs (bits := bits) reg3 reg4 49 (by omega)) := by
    exact Placed_window hSelect 3 rfl
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlJ (by omega) hpc1 hM1 (hOffsetFit 49 (by decide)) (by rw [hd1]; exact h49)
  change (reg s2 reg3).val = jN at h3_2
  have h2_2 : (reg s2 reg2).val = pN := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h0_2 : (reg s2 reg0).val = 0 := by
    rw [hPres2 reg0 (by intro h; cases h) (by intro h; cases h), hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero]
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [hPres2 reg1 (by intro h; cases h) (by intro h; cases h), hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one]
  have hM2 : (reg s2 rMeta).val = metaBase := by rw [hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1]
  have hd2' : s2.data = st.data := by rw [hd2, hd1]
  have haBr1 : code[s2.pc]? = some (.branchLt reg2 reg3 (basePc + 711) (basePc + 710)) := by
    rw [hpc2]; exact hSelect 6 _ rfl
  obtain ⟨s3, hs3Raw, hpc3, hr3, hd3⟩ := step_branchLt_at (input := input) haBr1 (by split <;> omega)
  have hs3 := steps_1_of_step hs3Raw
  have hr3F := reg_of_regs_eq hr3
  by_cases hEqJP : jN = pN
  · rw [ite_eq_right (by rw [h2_2, h3_2, hEqJP]; exact Nat.lt_irrefl _)] at hpc3
    have haBr2 : code[s3.pc]? = some (.branchLt reg3 reg2 (basePc + 711) (basePc + 1002)) := by
      rw [hpc3]; exact hSelect 7 _ rfl
    obtain ⟨s4, hs4Raw, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
    have hs4 := steps_1_of_step hs4Raw
    rw [ite_eq_right (by rw [hr3F reg2, hr3F reg3, h2_2, h3_2, hEqJP]; exact Nat.lt_irrefl _)] at hpc4
    have hr4F := reg_of_regs_eq hr4
    have hM4 : (reg s4 rMeta).val = metaBase := by rw [hr4F, hr3F, hM2]
    have h1_4 : (reg s4 reg1).val = 1 := by rw [hr4F, hr3F, h1_2]
    have h0_4 : (reg s4 reg0).val = 0 := by rw [hr4F, hr3F, h0_2]
    have hd4' : s4.data = st.data := by rw [hd4, hd3, hd2']
    have hPl55 : Placed code (basePc + 1002) (metaLoadInstrs (bits := bits) reg3 reg5 55 (by omega)) := by
      exact Placed_window hCopy 0 rfl
    obtain ⟨s5, hs5, hpc5, hd5, h3_5, hPres5⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl55 (by omega) hpc4 hM4 (hOffsetFit 55 (by decide)) (by rw [hd4']; exact h55)
    have h1_5 : (reg s5 reg1).val = 1 := by rw [hPres5 reg1 (by intro h; cases h) (by intro h; cases h), h1_4]
    have haA1 : code[s5.pc]? = some (.add reg3 reg3 reg1) := by rw [hpc5]; exact hCopy 3 _ rfl
    obtain ⟨s6, hs6Raw, hpc6, h3_6, ho6, hd6⟩ := step_add_at (input := input) haA1 (by omega)
    have hs6 := steps_1_of_step hs6Raw
    have h3Val6 : (reg s6 reg3).val = storedBase N + 18 * w + 1 := by
      rw [h3_6, add_no_wrap _ _ (by rw [h3_5, h1_5]; try dsimp only [storedBase]; omega), h3_5, h1_5]
    have h1_6 : (reg s6 reg1).val = 1 := by rw [ho6 reg1 (by intro h; cases h), h1_5]
    have haA2 : code[s6.pc]? = some (.add reg3 reg3 reg1) := by rw [hpc6, hpc5]; exact hCopy 4 _ rfl
    obtain ⟨s7, hs7Raw, hpc7, h3_7, ho7, hd7⟩ := step_add_at (input := input) haA2 (by omega)
    have hs7 := steps_1_of_step hs7Raw
    have h3Val7 : (reg s7 reg3).val = storedBase N + 18 * w + 2 := by
      rw [h3_7, add_no_wrap _ _ (by rw [h3Val6, h1_6]; try dsimp only [storedBase]; omega), h3Val6, h1_6]
    have haI : code[s7.pc]? = some (.imm reg2 ⟨8, by omega⟩) := by rw [hpc7, hpc6, hpc5]; exact hCopy 5 _ rfl
    obtain ⟨s8, hs8Raw, hpc8, h2_8, ho8, hd8⟩ := step_imm_at (input := input) haI (by omega)
    have hs8 := steps_1_of_step hs8Raw
    have h3_8 : (reg s8 reg3).val = storedBase N + 18 * w + 2 := by rw [ho8 reg3 (by intro h; cases h), h3Val7]
    have haA3 : code[s8.pc]? = some (.add reg2 reg3 reg2) := by rw [hpc8, hpc7, hpc6, hpc5]; exact hCopy 6 _ rfl
    obtain ⟨s9, hs9Raw, hpc9, h2_9, ho9, hd9⟩ := step_add_at (input := input) haA3 (by omega)
    have hs9 := steps_1_of_step hs9Raw
    have h2Val9 : (reg s9 reg2).val = storedBase N + 18 * w + 10 := by
      rw [h2_9, add_no_wrap _ _ (by rw [h3_8, h2_8]; change storedBase N + 18 * w + 10 < 2 ^ bits; exact recordFit w 10 hwLt (by decide)), h3_8, h2_8] <;> rfl
    have h3_9 : (reg s9 reg3).val = storedBase N + 18 * w + 2 := by rw [ho9 reg3 (by intro h; cases h), h3_8]
    have h1_9 : (reg s9 reg1).val = 1 := by
      rw [ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h), h1_6]
    have h0_9 : (reg s9 reg0).val = 0 := by
      rw [ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h),
        ho6 reg0 (by intro h; cases h), hPres5 reg0 (by intro h; cases h) (by intro h; cases h), h0_4]
    have hM_9 : (reg s9 rMeta).val = metaBase := by
      rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h),
        ho6 rMeta (by intro h; cases h), hPres5 rMeta (by intro h; cases h) (by intro h; cases h), hM4]
    have hd9' : s9.data = st.data := by rw [hd9, hd8, hd7, hd6, hd5, hd4']
    have hPlC8 : Placed code (basePc + 1009) (copy8Instrs (bits := bits) reg2 reg3 reg4) := by
      exact Placed_window hCopy 7 rfl
    obtain ⟨t, ht, hpct, hMapT, hPresT, hFrT⟩ := run_copy8 (input := input) (basePc + 1009) reg2 reg3 reg4
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      hPlC8 (by omega) (storedBase N + 18 * w + 2) (storedBase N + 18 * w + 10) pm
      (by unfold storedBase; omega) (by unfold storedBase; omega) (by unfold storedBase; omega)
      (Or.inr (by omega)) s9 (by rw [hpc9, hpc8, hpc7, hpc6, hpc5]) h1_9 h3_9 h2Val9 (by rw [hd9']; exact hPMW)
    dsimp only [jm]
    rw [ite_eq_left hEqJP]
    have hFrAll : ∀ j, (j < storedBase N + 18 * w + 10 ∨
        (storedBase N + 18 * w + 18 ≤ j ∧ j < metaBase + 56) ∨
        metaBase + 64 ≤ j) → t.data[j]? = st.data[j]? := fun j hj => by
      rw [hFrT j (by omega), hd9']
    exact ⟨8 + 7 + 30, t, by omega,
      (((hs1.append hs2).append (hs3.append hs4)).append ((hs5.append (hs6.append hs7)).append (hs8.append hs9))).append ht,
      by omega,
      hMeta.preserve (by rw [hPresT rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM_9])
        (by rw [hPresT reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_9])
        (by rw [hPresT reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_9])
        (fun i hi => hFrAll (metaBase + i) (Or.inr (Or.inl ⟨by omega, by omega⟩))),
      hMapT, hFrAll⟩
  · -- `jN ≠ pN` (`skew` branch at `basePc + 711..1001`):
    have hToSkew : ∃ k1 s4, (k1 = 7 ∨ k1 = 8) ∧ Steps code input k1 st s4 ∧ s4.pc = basePc + 711 ∧
        (reg s4 reg0).val = 0 ∧ (reg s4 reg1).val = 1 ∧ (reg s4 rMeta).val = metaBase ∧
        (reg s4 reg2).val = pN ∧ s4.data = st.data := by
      by_cases hLt1 : pN < jN
      · rw [ite_eq_left (by rw [h2_2, h3_2]; exact hLt1)] at hpc3
        exact ⟨7, s3, Or.inl rfl, (hs1.append hs2).append hs3, hpc3,
          by rw [hr3F, h0_2], by rw [hr3F, h1_2], by rw [hr3F, hM2], by rw [hr3F, h2_2], by rw [hd3, hd2']⟩
      · have hGt1 : jN < pN := by omega
        rw [ite_eq_right (by rw [h2_2, h3_2]; exact hLt1)] at hpc3
        have haBr2 : code[s3.pc]? = some (.branchLt reg3 reg2 (basePc + 711) (basePc + 1002)) := by
          rw [hpc3]; exact hSelect 7 _ rfl
        obtain ⟨s4, hs4Raw, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input) haBr2 (by split <;> omega)
        have hs4 := steps_1_of_step hs4Raw
        rw [ite_eq_left (by rw [hr3F reg2, hr3F reg3, h2_2, h3_2]; exact hGt1)] at hpc4
        have hr4F := reg_of_regs_eq hr4
        exact ⟨8, s4, Or.inr rfl, (hs1.append hs2).append (hs3.append hs4), hpc4,
          by rw [hr4F, hr3F, h0_2], by rw [hr4F, hr3F, h1_2], by rw [hr4F, hr3F, hM2],
          by rw [hr4F, hr3F, h2_2], by rw [hd4, hd3, hd2']⟩
    obtain ⟨k1, s4, hk1, hs4, hpc4, h0_4, h1_4, hM_4, h2_4, hd4⟩ := hToSkew
    obtain ⟨kA, s26, hkA, hs26, hpc26, h0_26, h1_26, hM_26, hTmpMap, hFr26⟩ :=
      step4B_composeAncestors_spec (input := input) basePc h100 hSelect hComposeFirst (by omega)
        N metaBase pN aJ hpLt haJLt hBoundMeta recordEnd parentJump ancestorJump
        s4 hpc4 h0_4 h1_4 hM_4 h2_4 (by rw [hd4]; exact hMeta.meta_storedBase)
        (by rw [hd4]; exact hJumpP) (by rw [hd4]; exact hStP) (by rw [hd4]; exact hStAJ)
    have hSaved : ∀ j, j < metaBase + 56 ∨ metaBase + 64 ≤ j → s26.data[j]? = st.data[j]? :=
      fun j hj => (hFr26 j hj).trans (congrArg (fun d => d[j]?) hd4)
    have hPM26 : MapWordsAt s26.data (storedBase N + 18 * w + 2) pm :=
      mapWordsAt_frame (fun i hi => hSaved _ (Or.inl (by omega))) hPMW
    obtain ⟨kB, t, hkB, hsB, hpcT, h0T, h1T, hMT, hMapT, hFrT⟩ :=
      step4B_finishJump_spec (input := input) basePc h100 hComposeSecond hSz N metaBase w hWEnd hBoundMeta
        pm (Map.compose parentJump ancestorJump) s26 hpc26 h0_26 h1_26 hM_26
        (by rw [hSaved _ (Or.inl (by omega))]; exact h55) hPM26 hTmpMap
    have hFrAll : ∀ j, (j < storedBase N + 18 * w + 10 ∨
        (storedBase N + 18 * w + 18 ≤ j ∧ j < metaBase + 56) ∨
        metaBase + 64 ≤ j) → t.data[j]? = st.data[j]? := fun j hj => by
      rw [hFrT j (by rcases hj with h | ⟨h, _⟩ | h <;> omega)]
      exact hSaved j (by rcases hj with h | ⟨_, h⟩ | h <;> omega)
    dsimp only [jm]
    rw [ite_eq_right hEqJP]
    exact ⟨k1 + kA + kB, t, by rcases hk1 with rfl | rfl <;> omega,
      (hs4.append hs26).append hsB, hpcT,
      hMeta.preserve hMT h0T h1T
        (fun i hi => hFrAll (metaBase + i) (Or.inr (Or.inl ⟨by omega, by omega⟩))),
      hMapT, hFrAll⟩

end PaperB.RamProgram.ExitSummaryBuild
