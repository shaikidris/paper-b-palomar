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

theorem step4B_composeAncestors_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hSelect : Placed code (basePc + 703) (step4BOneNode_selectJump basePc h100))
    (hComposeFirst : Placed code (basePc + 730) (step4BOneNode_composeFirst basePc h100))
    (hSz : basePc + 864 < code.size)
    (N metaBase pN aJ : Nat) (hpLt : pN < N) (haJLt : aJ < N)
    (hBoundMeta : metaBase + 64 ≤ workCap)
    (recordEnd : ∀ u < N, storedBase N + 18 * u + 18 ≤ metaBase)
    (parentJump ancestorJump : Map)
    (st : State DomL) (hpc4 : st.pc = basePc + 711)
    (h0_4 : (reg st reg0).val = 0) (h1_4 : (reg st reg1).val = 1)
    (hM_4 : (reg st rMeta).val = metaBase) (h2_4 : (reg st reg2).val = pN)
    (hStoredBase : (st.data[metaBase + mIdxStoredBase]?).map Fin.val = some (storedBase N))
    (hJumpP : (st.data[storedBase N + 18 * pN + 1]?).map Fin.val = some aJ)
    (hStP : MapWordsAt st.data (storedBase N + 18 * pN + 10) parentJump)
    (hStAJ : MapWordsAt st.data (storedBase N + 18 * aJ + 10) ancestorJump) :
    ∃ k t, k ≤ 121 ∧ Steps code input k st t ∧ t.pc = basePc + 864 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      MapWordsAt t.data (metaBase + 56) (Map.compose parentJump ancestorJump) ∧
      (∀ j, j < metaBase + 56 ∨ metaBase + 64 ≤ j → t.data[j]? = st.data[j]?) := by
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hPEnd := recordEnd pN hpLt
  have hAEnd := recordEnd aJ haJLt
  have hOffsetFit (off : Nat) (hoff : off < 64) : metaBase + off < 2 ^ bits := by omega
  have recordFit (u off : Nat) (hu : u < N) (hoff : off < 18) :
      storedBase N + 18 * u + off < 2 ^ bits := by
    have := recordEnd u hu
    omega
  -- `mul18 reg7 reg8 reg2` (`18 * pN`), read `baseP`, read `aJ = stored[p].jump`, `mul18 reg2 reg9 reg8`:
  have haM0 : code[st.pc]? = some (.add reg8 reg2 reg2) := by rw [hpc4]; exact hSelect 8 _ rfl
  obtain ⟨s5, hs5Raw, hpc5, h8_5, ho5, hd5⟩ := step_add_at (input := input) (s := st) haM0 (by omega)
  have hs5 := steps_1_of_step hs5Raw
  have h8Val5 : (reg s5 reg8).val = 2 * pN := by rw [h8_5, add_no_wrap _ _ (by rw [h2_4]; omega), h2_4]; omega
  have haM1 : code[s5.pc]? = some (.add reg7 reg8 reg8) := by rw [hpc5, hpc4]; exact hSelect 9 _ rfl
  obtain ⟨s6, hs6Raw, hpc6, h7_6, ho6, hd6⟩ := step_add_at (input := input) haM1 (by omega)
  have hs6 := steps_1_of_step hs6Raw
  have h7Val6 : (reg s6 reg7).val = 4 * pN := by rw [h7_6, add_no_wrap _ _ (by rw [h8Val5]; omega), h8Val5]; omega
  have haM2 : code[s6.pc]? = some (.add reg7 reg7 reg7) := by rw [hpc6, hpc5, hpc4]; exact hSelect 10 _ rfl
  obtain ⟨s7, hs7Raw, hpc7, h7_7, ho7, hd7⟩ := step_add_at (input := input) haM2 (by omega)
  have hs7 := steps_1_of_step hs7Raw
  have h7Val7 : (reg s7 reg7).val = 8 * pN := by rw [h7_7, add_no_wrap _ _ (by rw [h7Val6]; omega), h7Val6]; omega
  have haM3 : code[s7.pc]? = some (.add reg7 reg7 reg7) := by rw [hpc7, hpc6, hpc5, hpc4]; exact hSelect 11 _ rfl
  obtain ⟨s8, hs8Raw, hpc8, h7_8, ho8, hd8⟩ := step_add_at (input := input) haM3 (by omega)
  have hs8 := steps_1_of_step hs8Raw
  have h7Val8 : (reg s8 reg7).val = 16 * pN := by rw [h7_8, add_no_wrap _ _ (by rw [h7Val7]; omega), h7Val7]; omega
  have h8_8 : (reg s8 reg8).val = 2 * pN := by
    rw [ho8 reg8 (by intro h; cases h), ho7 reg8 (by intro h; cases h), ho6 reg8 (by intro h; cases h), h8Val5]
  have haM4 : code[s8.pc]? = some (.add reg7 reg7 reg8) := by rw [hpc8, hpc7, hpc6, hpc5, hpc4]; exact hSelect 12 _ rfl
  obtain ⟨s9, hs9Raw, hpc9, h7_9, ho9, hd9⟩ := step_add_at (input := input) haM4 (by omega)
  have hs9 := steps_1_of_step hs9Raw
  have h7Val9 : (reg s9 reg7).val = 18 * pN := by
    rw [h7_9, add_no_wrap _ _ (by rw [h7Val8, h8_8]; omega), h7Val8, h8_8]; omega
  have hM_9 : (reg s9 rMeta).val = metaBase := by
    rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h),
      ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h), hM_4]
  have hd9' : s9.data = st.data := by rw [hd9, hd8, hd7, hd6, hd5]
  have hPlSB1 : Placed code (basePc + 716) (metaLoadInstrs (bits := bits) reg8 reg9 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega)) := by
    exact Placed_window hSelect 13 rfl
  obtain ⟨s10, hs10, hpc10, hd10, h8_10, hPres10⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSB1 (by omega) (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4])
    hM_9 (hOffsetFit mIdxStoredBase (by decide)) (by rw [hd9']; exact hStoredBase)
  have h7_10 : (reg s10 reg7).val = 18 * pN := by rw [hPres10 reg7 (by intro h; cases h) (by intro h; cases h), h7Val9]
  have haAP : code[s10.pc]? = some (.add reg7 reg8 reg7) := by rw [hpc10]; exact hSelect 16 _ rfl
  obtain ⟨s11, hs11Raw, hpc11, h7_11, ho11, hd11⟩ := step_add_at (input := input) haAP (by omega)
  have hs11 := steps_1_of_step hs11Raw
  have hBPVal11 : (reg s11 reg7).val = storedBase N + 18 * pN := by
    rw [h7_11, add_no_wrap _ _ (by rw [h8_10, h7_10]; change storedBase N + 18 * pN < 2 ^ bits; exact recordFit pN 0 hpLt (by decide)),
      h8_10, h7_10]
  have h1_11 : (reg s11 reg1).val = 1 := by
    rw [ho11 reg1 (by intro h; cases h), hPres10 reg1 (by intro h; cases h) (by intro h; cases h),
      ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h),
      ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h), h1_4]
  have haAP1 : code[s11.pc]? = some (.add reg8 reg7 reg1) := by rw [hpc11, hpc10]; exact hSelect 17 _ rfl
  obtain ⟨s12, hs12Raw, hpc12, h8_12, ho12, hd12⟩ := step_add_at (input := input) haAP1 (by omega)
  have hs12 := steps_1_of_step hs12Raw
  have h8Val12 : (reg s12 reg8).val = storedBase N + 18 * pN + 1 := by
    rw [h8_12, add_no_wrap _ _ (by rw [hBPVal11, h1_11]; exact recordFit pN 1 hpLt (by decide)), hBPVal11, h1_11]
  obtain ⟨waj, hwaj, hwajV⟩ := Option.map_eq_some_iff.mp hJumpP
  have haLAJ : code[s12.pc]? = some (.loadData reg8 reg8) := by rw [hpc12, hpc11, hpc10]; exact hSelect 18 _ rfl
  obtain ⟨s13, hs13Raw, hpc13, h8_13, ho13, hd13⟩ := step_loadData_at (input := input) haLAJ (by omega)
    (by rw [h8Val12, hd12, hd11, hd10, hd9']; exact hwaj)
  have hs13 := steps_1_of_step hs13Raw
  have haJVal13 : (reg s13 reg8).val = aJ := by rw [h8_13, hwajV]
  have h7_13 : (reg s13 reg7).val = storedBase N + 18 * pN := by
    rw [ho13 reg7 (by intro h; cases h), ho12 reg7 (by intro h; cases h), hBPVal11]
  have hM_13 : (reg s13 rMeta).val = metaBase := by
    rw [ho13 rMeta (by intro h; cases h), ho12 rMeta (by intro h; cases h),
      ho11 rMeta (by intro h; cases h), hPres10 rMeta (by intro h; cases h) (by intro h; cases h), hM_9]
  have hd13' : s13.data = st.data := by rw [hd13, hd12, hd11, hd10, hd9']
  -- `mul18 reg2 reg9 reg8` (`18 * aJ`):
  have haN0 : code[s13.pc]? = some (.add reg9 reg8 reg8) := by rw [hpc13, hpc12, hpc11, hpc10]; exact hSelect 19 _ rfl
  obtain ⟨s14, hs14Raw, hpc14, h9_14, ho14, hd14⟩ := step_add_at (input := input) haN0 (by omega)
  have hs14 := steps_1_of_step hs14Raw
  have h9Val14 : (reg s14 reg9).val = 2 * aJ := by
    rw [h9_14, add_no_wrap _ _ (by rw [haJVal13]; omega), haJVal13]; omega
  have haN1 : code[s14.pc]? = some (.add reg2 reg9 reg9) := by rw [hpc14, hpc13, hpc12, hpc11, hpc10]; exact hSelect 20 _ rfl
  obtain ⟨s15, hs15Raw, hpc15, h2_15, ho15, hd15⟩ := step_add_at (input := input) haN1 (by omega)
  have hs15 := steps_1_of_step hs15Raw
  have h2Val15 : (reg s15 reg2).val = 4 * aJ := by
    rw [h2_15, add_no_wrap _ _ (by rw [h9Val14]; omega), h9Val14]; omega
  have haN2 : code[s15.pc]? = some (.add reg2 reg2 reg2) := by rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10]; exact hSelect 21 _ rfl
  obtain ⟨s16, hs16Raw, hpc16, h2_16, ho16, hd16⟩ := step_add_at (input := input) haN2 (by omega)
  have hs16 := steps_1_of_step hs16Raw
  have h2Val16 : (reg s16 reg2).val = 8 * aJ := by
    rw [h2_16, add_no_wrap _ _ (by rw [h2Val15]; omega), h2Val15]; omega
  have haN3 : code[s16.pc]? = some (.add reg2 reg2 reg2) := by rw [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10]; exact hSelect 22 _ rfl
  obtain ⟨s17, hs17Raw, hpc17, h2_17, ho17, hd17⟩ := step_add_at (input := input) haN3 (by omega)
  have hs17 := steps_1_of_step hs17Raw
  have h2Val17 : (reg s17 reg2).val = 16 * aJ := by
    rw [h2_17, add_no_wrap _ _ (by rw [h2Val16]; omega), h2Val16]; omega
  have h9_17 : (reg s17 reg9).val = 2 * aJ := by
    rw [ho17 reg9 (by intro h; cases h), ho16 reg9 (by intro h; cases h), ho15 reg9 (by intro h; cases h), h9Val14]
  have haN4 : code[s17.pc]? = some (.add reg2 reg2 reg9) := by rw [hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10]; exact hSelect 23 _ rfl
  obtain ⟨s18, hs18Raw, hpc18, h2_18, ho18, hd18⟩ := step_add_at (input := input) haN4 (by omega)
  have hs18 := steps_1_of_step hs18Raw
  have h2Val18 : (reg s18 reg2).val = 18 * aJ := by
    rw [h2_18, add_no_wrap _ _ (by rw [h2Val17, h9_17]; omega), h2Val17, h9_17]; omega
  have h7_18 : (reg s18 reg7).val = storedBase N + 18 * pN := by
    rw [ho18 reg7 (by intro h; cases h), ho17 reg7 (by intro h; cases h), ho16 reg7 (by intro h; cases h),
      ho15 reg7 (by intro h; cases h), ho14 reg7 (by intro h; cases h), h7_13]
  have hM_18 : (reg s18 rMeta).val = metaBase := by
    rw [ho18 rMeta (by intro h; cases h), ho17 rMeta (by intro h; cases h), ho16 rMeta (by intro h; cases h),
      ho15 rMeta (by intro h; cases h), ho14 rMeta (by intro h; cases h), hM_13]
  have hd18' : s18.data = st.data := by rw [hd18, hd17, hd16, hd15, hd14, hd13']
  have hPlSB2 : Placed code (basePc + 727) (metaLoadInstrs (bits := bits) reg8 reg9 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega)) := by
    exact Placed_window hSelect 24 rfl
  obtain ⟨s19, hs19, hpc19, hd19, h8_19, hPres19⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSB2 (by omega)
    (by rw [hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10])
    hM_18 (hOffsetFit mIdxStoredBase (by decide)) (by rw [hd18']; exact hStoredBase)
  have h2_19 : (reg s19 reg2).val = 18 * aJ := by
    rw [hPres19 reg2 (by intro h; cases h) (by intro h; cases h), h2Val18]
  have h7_19 : (reg s19 reg7).val = storedBase N + 18 * pN := by
    rw [hPres19 reg7 (by intro h; cases h) (by intro h; cases h), h7_18]
  have haAAJ : code[s19.pc]? = some (.add reg2 reg8 reg2) := by rw [hpc19]; exact hComposeFirst 0 _ rfl
  obtain ⟨s20, hs20Raw, hpc20, h2_20, ho20, hd20⟩ := step_add_at (input := input) haAAJ (by omega)
  have hs20 := steps_1_of_step hs20Raw
  have hBAJVal20 : (reg s20 reg2).val = storedBase N + 18 * aJ := by
    have hFit : (reg s19 reg8).val + (reg s19 reg2).val < 2 ^ bits := by
      rw [h8_19, h2_19]
      exact recordFit aJ 0 haJLt (by decide)
    rw [h2_20, add_no_wrap _ _ hFit, h8_19, h2_19]
  have haI10 : code[s20.pc]? = some (.imm reg9 ⟨10, by omega⟩) := by rw [hpc20, hpc19]; exact hComposeFirst 1 _ rfl
  obtain ⟨s21, hs21Raw, hpc21, h9_21, ho21, hd21⟩ := step_imm_at (input := input) haI10 (by omega)
  have hs21 := steps_1_of_step hs21Raw
  have haAAJJ : code[s21.pc]? = some (.add reg3 reg2 reg9) := by rw [hpc21, hpc20, hpc19]; exact hComposeFirst 2 _ rfl
  obtain ⟨s22, hs22Raw, hpc22, h3_22, ho22, hd22⟩ := step_add_at (input := input) haAAJJ (by omega)
  have hs22 := steps_1_of_step hs22Raw
  have h3Val22 : (reg s22 reg3).val = storedBase N + 18 * aJ + 10 := by
    rw [h3_22, add_no_wrap _ _ (by rw [ho21 reg2 (by intro h; cases h), hBAJVal20, h9_21]; exact recordFit aJ 10 haJLt (by decide)),
      ho21 reg2 (by intro h; cases h), hBAJVal20, h9_21]
  have h7_22 : (reg s22 reg7).val = storedBase N + 18 * pN := by
    rw [ho22 reg7 (by intro h; cases h), ho21 reg7 (by intro h; cases h), ho20 reg7 (by intro h; cases h), h7_19]
  have h9_22 : (reg s22 reg9).val = 10 := by rw [ho22 reg9 (by intro h; cases h), h9_21]
  have haAPJ : code[s22.pc]? = some (.add reg2 reg7 reg9) := by rw [hpc22, hpc21, hpc20, hpc19]; exact hComposeFirst 3 _ rfl
  obtain ⟨s23, hs23Raw, hpc23, h2_23, ho23, hd23⟩ := step_add_at (input := input) haAPJ (by omega)
  have hs23 := steps_1_of_step hs23Raw
  have h2Val23 : (reg s23 reg2).val = storedBase N + 18 * pN + 10 := by
    rw [h2_23, add_no_wrap _ _ (by rw [h7_22, h9_22]; exact recordFit pN 10 hpLt (by decide)), h7_22, h9_22]
  have haI56 : code[s23.pc]? = some (.imm reg4 ⟨56, by omega⟩) := by rw [hpc23, hpc22, hpc21, hpc20, hpc19]; exact hComposeFirst 4 _ rfl
  obtain ⟨s24, hs24Raw, hpc24, h4_24, ho24, hd24⟩ := step_imm_at (input := input) haI56 (by omega)
  have hs24 := steps_1_of_step hs24Raw
  have hM_24 : (reg s24 rMeta).val = metaBase := by
    rw [ho24 rMeta (by intro h; cases h), ho23 rMeta (by intro h; cases h), ho22 rMeta (by intro h; cases h),
      ho21 rMeta (by intro h; cases h), ho20 rMeta (by intro h; cases h),
      hPres19 rMeta (by intro h; cases h) (by intro h; cases h), hM_18]
  have haAT56 : code[s24.pc]? = some (.add reg4 rMeta reg4) := by rw [hpc24, hpc23, hpc22, hpc21, hpc20, hpc19]; exact hComposeFirst 5 _ rfl
  obtain ⟨s25, hs25Raw, hpc25, h4_25, ho25, hd25⟩ := step_add_at (input := input) haAT56 (by omega)
  have hs25 := steps_1_of_step hs25Raw
  have h4Val25 : (reg s25 reg4).val = metaBase + 56 := by
    rw [h4_25, add_no_wrap _ _ (by rw [hM_24, h4_24]; exact hOffsetFit 56 (by decide)), hM_24, h4_24]
  have hM_25 : (reg s25 rMeta).val = metaBase := by rw [ho25 rMeta (by intro h; cases h), hM_24]
  have h1_25 : (reg s25 reg1).val = 1 := by
    rw [ho25 reg1 (by intro h; cases h), ho24 reg1 (by intro h; cases h), ho23 reg1 (by intro h; cases h),
      ho22 reg1 (by intro h; cases h), ho21 reg1 (by intro h; cases h), ho20 reg1 (by intro h; cases h),
      hPres19 reg1 (by intro h; cases h) (by intro h; cases h), ho18 reg1 (by intro h; cases h),
      ho17 reg1 (by intro h; cases h), ho16 reg1 (by intro h; cases h), ho15 reg1 (by intro h; cases h),
      ho14 reg1 (by intro h; cases h), ho13 reg1 (by intro h; cases h), ho12 reg1 (by intro h; cases h), h1_11]
  have h0_25 : (reg s25 reg0).val = 0 := by
    rw [ho25 reg0 (by intro h; cases h), ho24 reg0 (by intro h; cases h), ho23 reg0 (by intro h; cases h),
      ho22 reg0 (by intro h; cases h), ho21 reg0 (by intro h; cases h), ho20 reg0 (by intro h; cases h),
      hPres19 reg0 (by intro h; cases h) (by intro h; cases h), ho18 reg0 (by intro h; cases h),
      ho17 reg0 (by intro h; cases h), ho16 reg0 (by intro h; cases h), ho15 reg0 (by intro h; cases h),
      ho14 reg0 (by intro h; cases h), ho13 reg0 (by intro h; cases h), ho12 reg0 (by intro h; cases h),
      ho11 reg0 (by intro h; cases h), hPres10 reg0 (by intro h; cases h) (by intro h; cases h),
      ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h),
      ho6 reg0 (by intro h; cases h), ho5 reg0 (by intro h; cases h), h0_4]
  have h2Val25 : (reg s25 reg2).val = storedBase N + 18 * pN + 10 := by
    rw [ho25 reg2 (by intro h; cases h), ho24 reg2 (by intro h; cases h), h2Val23]
  have h3Val25 : (reg s25 reg3).val = storedBase N + 18 * aJ + 10 := by
    rw [ho25 reg3 (by intro h; cases h), ho24 reg3 (by intro h; cases h), ho23 reg3 (by intro h; cases h), h3Val22]
  have hd25' : s25.data = st.data := by rw [hd25, hd24, hd23, hd22, hd21, hd20, hd19, hd18']
  have hPlMC1 : Placed code (basePc + 736) (mapComposeInstrs (bits := bits) (basePc + 736)) := by
    exact Placed_window hComposeFirst 6 rfl
  obtain ⟨kC1, s26, hkC1, hs26, hpc26, hTmpMap, hPres26, hFr26⟩ := run_mapCompose (input := input)
    (basePc + 736) hPlMC1 (by omega)
    (storedBase N + 18 * pN + 10) (storedBase N + 18 * aJ + 10) (metaBase + 56)
    parentJump ancestorJump
    (recordFit pN 17 hpLt (by decide)) (recordFit aJ 17 haJLt (by decide)) (by omega) (by omega)
    (Or.inr (Nat.le_trans (recordEnd pN hpLt) (Nat.le_add_right _ _)))
    (Or.inr (Nat.le_trans (recordEnd aJ haJLt) (Nat.le_add_right _ _)))
    s25 (by rw [hpc25, hpc24, hpc23, hpc22, hpc21, hpc20, hpc19]) h0_25 h1_25 h2Val25 h3Val25 h4Val25
    (by rw [hd25']; exact hStP) (by rw [hd25']; exact hStAJ)
  have h0_26 : (reg s26 reg0).val = 0 := by rw [hPres26 reg0 (Or.inl rfl), h0_25]
  have h1_26 : (reg s26 reg1).val = 1 := by rw [hPres26 reg1 (Or.inr (Or.inl rfl)), h1_25]
  have hM_26 : (reg s26 rMeta).val = metaBase := by rw [hPres26 rMeta (Or.inr (Or.inr (Or.inr rfl))), hM_25]
  have hA : Steps code input 16 st s18 := by
    exact (((hs5.append (hs6.append (hs7.append hs8))).append (hs9.append (hs10.append (hs11.append (hs12.append hs13))))).append
      (hs14.append (hs15.append (hs16.append (hs17.append hs18)))))
  have hB : Steps code input 9 s18 s25 :=
    hs19.append (hs20.append (hs21.append (hs22.append (hs23.append (hs24.append hs25)))))
  exact ⟨25 + kC1, s26, by omega, (hA.append hB).append hs26, hpc26, h0_26, h1_26, hM_26,
    hTmpMap, fun j hj => (hFr26 j hj).trans (congrArg (fun d => d[j]?) hd25')⟩

end PaperB.RamProgram.ExitSummaryBuild
