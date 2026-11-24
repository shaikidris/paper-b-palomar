module

public import PaperB.RamExitSummarySweepBROM
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

theorem step4B_finishJump_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hComposeSecond : Placed code (basePc + 864) (step4BOneNode_composeSecond basePc h100))
    (hSz : basePc + 1039 < code.size)
    (N metaBase w : Nat) (hWEnd : storedBase N + 18 * w + 18 ≤ metaBase)
    (hBoundMeta : metaBase + 64 ≤ workCap)
    (pm tmpMap : Map) (s26 : State DomL) (hpc26 : s26.pc = basePc + 864)
    (h0_26 : (reg s26 reg0).val = 0) (h1_26 : (reg s26 reg1).val = 1)
    (hM_26 : (reg s26 rMeta).val = metaBase)
    (h55 : (s26.data[metaBase + 55]?).map Fin.val = some (storedBase N + 18 * w))
    (hPMW : MapWordsAt s26.data (storedBase N + 18 * w + 2) pm)
    (hTmpMap : MapWordsAt s26.data (metaBase + 56) tmpMap) :
    ∃ k t, k ≤ 106 ∧ Steps code input k s26 t ∧ t.pc = basePc + 1039 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      MapWordsAt t.data (storedBase N + 18 * w + 10) (Map.compose pm tmpMap) ∧
      (∀ j, (j < storedBase N + 18 * w + 10 ∨ storedBase N + 18 * w + 18 ≤ j) →
        t.data[j]? = s26.data[j]?) := by
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hOffsetFit (off : Nat) (hoff : off < 64) : metaBase + off < 2 ^ bits := by omega
  have hPl55 : Placed code (basePc + 864) (metaLoadInstrs (bits := bits) reg2 reg5 55 (by omega)) := by
    exact Placed_window hComposeSecond 0 rfl
  obtain ⟨s27, hs27, hpc27, hd27, h2_27, hPres27⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl55 (by omega) hpc26 hM_26 (hOffsetFit 55 (by decide))
    h55
  have h1_27 : (reg s27 reg1).val = 1 := by rw [hPres27 reg1 (by intro h; cases h) (by intro h; cases h), h1_26]
  have haB1 : code[s27.pc]? = some (.add reg2 reg2 reg1) := by rw [hpc27]; exact hComposeSecond 3 _ rfl
  obtain ⟨s28, hs28Raw, hpc28, h2_28, ho28, hd28⟩ := step_add_at (input := input) haB1 (by omega)
  have hs28 := steps_1_of_step hs28Raw
  have h2Val28 : (reg s28 reg2).val = storedBase N + 18 * w + 1 := by
    rw [h2_28, add_no_wrap _ _ (by rw [h2_27, h1_27]; omega), h2_27, h1_27]
  have h1_28 : (reg s28 reg1).val = 1 := by rw [ho28 reg1 (by intro h; cases h), h1_27]
  have haB2 : code[s28.pc]? = some (.add reg2 reg2 reg1) := by rw [hpc28, hpc27]; exact hComposeSecond 4 _ rfl
  obtain ⟨s29, hs29Raw, hpc29, h2_29, ho29, hd29⟩ := step_add_at (input := input) haB2 (by omega)
  have hs29 := steps_1_of_step hs29Raw
  have h2Val29 : (reg s29 reg2).val = storedBase N + 18 * w + 2 := by
    rw [h2_29, add_no_wrap _ _ (by rw [h2Val28, h1_28]; omega), h2Val28, h1_28]
  have haI56b : code[s29.pc]? = some (.imm reg3 ⟨56, by omega⟩) := by rw [hpc29, hpc28, hpc27]; exact hComposeSecond 5 _ rfl
  obtain ⟨s30, hs30Raw, hpc30, h3_30, ho30, hd30⟩ := step_imm_at (input := input) haI56b (by omega)
  have hs30 := steps_1_of_step hs30Raw
  have hM_30 : (reg s30 rMeta).val = metaBase := by
    rw [ho30 rMeta (by intro h; cases h), ho29 rMeta (by intro h; cases h), ho28 rMeta (by intro h; cases h),
      hPres27 rMeta (by intro h; cases h) (by intro h; cases h), hM_26]
  have haAT56b : code[s30.pc]? = some (.add reg3 rMeta reg3) := by rw [hpc30, hpc29, hpc28, hpc27]; exact hComposeSecond 6 _ rfl
  obtain ⟨s31, hs31Raw, hpc31, h3_31, ho31, hd31⟩ := step_add_at (input := input) haAT56b (by omega)
  have hs31 := steps_1_of_step hs31Raw
  have h3Val31 : (reg s31 reg3).val = metaBase + 56 := by
    rw [h3_31, add_no_wrap _ _ (by rw [hM_30, h3_30]; exact hOffsetFit 56 (by decide)), hM_30, h3_30]
  have haI8b : code[s31.pc]? = some (.imm reg4 ⟨8, by omega⟩) := by rw [hpc31, hpc30, hpc29, hpc28, hpc27]; exact hComposeSecond 7 _ rfl
  obtain ⟨s32, hs32Raw, hpc32, h4_32, ho32, hd32⟩ := step_imm_at (input := input) haI8b (by omega)
  have hs32 := steps_1_of_step hs32Raw
  have h2_32 : (reg s32 reg2).val = storedBase N + 18 * w + 2 := by
    rw [ho32 reg2 (by intro h; cases h), ho31 reg2 (by intro h; cases h), ho30 reg2 (by intro h; cases h), h2Val29]
  have haAB8 : code[s32.pc]? = some (.add reg4 reg2 reg4) := by rw [hpc32, hpc31, hpc30, hpc29, hpc28, hpc27]; exact hComposeSecond 8 _ rfl
  obtain ⟨s33, hs33Raw, hpc33, h4_33, ho33, hd33⟩ := step_add_at (input := input) haAB8 (by omega)
  have hs33 := steps_1_of_step hs33Raw
  have h4Val33 : (reg s33 reg4).val = storedBase N + 18 * w + 10 := by
    have hFit : (reg s32 reg2).val + (reg s32 reg4).val < 2 ^ bits := by
      rw [h2_32, h4_32]
      change storedBase N + 18 * w + 2 + 8 < 2 ^ bits
      omega
    rw [h4_33, add_no_wrap _ _ hFit, h2_32, h4_32] <;> rfl
  have h2Val33 : (reg s33 reg2).val = storedBase N + 18 * w + 2 := by rw [ho33 reg2 (by intro h; cases h), h2_32]
  have h3Val33 : (reg s33 reg3).val = metaBase + 56 := by
    rw [ho33 reg3 (by intro h; cases h), ho32 reg3 (by intro h; cases h), h3Val31]
  have h1_33 : (reg s33 reg1).val = 1 := by
    rw [ho33 reg1 (by intro h; cases h), ho32 reg1 (by intro h; cases h), ho31 reg1 (by intro h; cases h),
      ho30 reg1 (by intro h; cases h), ho29 reg1 (by intro h; cases h), h1_28]
  have h0_33 : (reg s33 reg0).val = 0 := by
    rw [ho33 reg0 (by intro h; cases h), ho32 reg0 (by intro h; cases h), ho31 reg0 (by intro h; cases h),
      ho30 reg0 (by intro h; cases h), ho29 reg0 (by intro h; cases h), ho28 reg0 (by intro h; cases h),
      hPres27 reg0 (by intro h; cases h) (by intro h; cases h), h0_26]
  have hM_33 : (reg s33 rMeta).val = metaBase := by
    rw [ho33 rMeta (by intro h; cases h), ho32 rMeta (by intro h; cases h), ho31 rMeta (by intro h; cases h), hM_30]
  have hd33' : s33.data = s26.data := by rw [hd33, hd32, hd31, hd30, hd29, hd28, hd27]
  have hPM33 : MapWordsAt s33.data (storedBase N + 18 * w + 2) pm := hd33'.symm ▸ hPMW
  have hPlMC2 : Placed code (basePc + 873) (mapComposeInstrs (bits := bits) (basePc + 873)) := by
    unfold step4BOneNode_composeSecond at hComposeSecond
    simpa only [List.length_append, metaLoadInstrs, List.length_cons, List.length_nil,
      Nat.reduceAdd] using Placed_append_right (Placed_append_left hComposeSecond)
  obtain ⟨kC2, s34, hkC2, hs34, hpc34, hJM34, hPres34, hFr34⟩ := run_mapCompose (input := input)
    (basePc + 873) hPlMC2 (by omega)
    (storedBase N + 18 * w + 2) (metaBase + 56) (storedBase N + 18 * w + 10)
    pm tmpMap
    (by omega) (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inl (by omega))
    s33 (by rw [hpc33, hpc32, hpc31, hpc30, hpc29, hpc28, hpc27]) h0_33 h1_33 h2Val33 h3Val33 h4Val33
    hPM33 (by rw [hd33']; exact hTmpMap)
  have hGoEnd : Placed code (basePc + 1001) [.goto (basePc + 1039)] := by
    unfold step4BOneNode_composeSecond at hComposeSecond
    simpa only [List.length_append, metaLoadInstrs, mapComposeInstrs_length,
      List.length_cons, List.length_nil, Nat.reduceAdd] using Placed_append_right hComposeSecond
  have haGoEnd : code[s34.pc]? = some (.goto (basePc + 1039)) := by
    rw [hpc34]
    exact hGoEnd 0 _ rfl
  obtain ⟨t, htRaw, hpct, hrt, hdt⟩ := step_goto_at (input := input) haGoEnd (by omega)
  have ht := steps_1_of_step htRaw
  have hrTF := reg_of_regs_eq hrt
  have hStepsAll : Steps code input (9 + kC2 + 1) s26 t := by
    exact ((((hs27.append (hs28.append hs29)).append (hs30.append (hs31.append (hs32.append hs33)))).append hs34)).append ht
  exact ⟨9 + kC2 + 1, t, by omega, hStepsAll, hpct,
    by rw [hrTF, hPres34 reg0 (Or.inl rfl), h0_33],
    by rw [hrTF, hPres34 reg1 (Or.inr (Or.inl rfl)), h1_33],
    by rw [hrTF, hPres34 rMeta (Or.inr (Or.inr (Or.inr rfl))), hM_33],
    by rw [hdt]; exact hJM34,
    fun j hj => by rw [hdt, hFr34 j (by rcases hj with h | h <;> omega), hd33']⟩

end PaperB.RamProgram.ExitSummaryBuild
