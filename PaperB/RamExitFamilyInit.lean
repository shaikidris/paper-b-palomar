module

public import PaperB.RamExitFamilyRom
public import PaperB.RamExitFamilyLoop

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxErrors 220
set_option maxHeartbeats 500000

/-!
EX5.1 Exit-Summary Family Loop Program and End-to-End Proof (`PaperB.RamExitFamilyLoop`):
Sections 3–5 constructing `exitFamilyLoopProgram` and proving `run_exit_family_loop`,
chaining from `prefixAndForestLoopProgram` into `sealedPackAndShiftProgram`.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex)
open PaperB.ForestSlimIndex
open PaperB.ExitMap.Retention (TagsFit)
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
open PaperB.RamFamilyForestLoop
open PaperB.RamQuotientEmitter
open PaperB.RamDataSliceAdapter
open PaperB.RetainedProperLoss
open PaperB.ExitActualContract
open PaperB.RamSealedPacker
open PaperB.RamProgram.ExitSummaryBuild
open _root_.EX24.PreparedSweep (orderedVertexAt)

/-! ### 3. Fixed 16-Register Program, Offsets, `.size`, and Fetch Lemmas -/


/-! ### 4. Modular Small-Step Execution Helpers (`≤ 17` Sequential Steps per Block) -/

section SmallStepHelpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

local macro "exit_rom_bound" : tactic => `(tactic|
  simp only [exitInitACode_size, exitInitBCode_size, exitHdrCode_size, exitPrepCode_size,
    exitSmallCode_size, exitLargeACode_size, exitLargeBCode_size, copyFromFpBlock_size,
    copyFromEmitBlock_size, exitSaveRegsCode_size, exitRestoreRegsCode_size, exitPostSetupCode_size,
    copyLoopCode16_size, exitPostStepCode_size, exitFinishCode_size] <;> decide)

local macro "exit_arith" : tactic => `(tactic| first
  | omega
  | (simp only [offInitA, offInitB, offHdr, offPrep, offSmall, offLargeA, offLargeB,
        offFp, offEmit, offSave, offSub, offRestore, offPostSetup, offPostCopy,
        offPostStep, offFinish, Fin.val_mk, Nat.add_zero, layout16, Fin.ext_iff,
        r11, r12, r13, r14, r15, r9, r10, w100, inPtrAddr, dataPtrAddr, statePtrAddr] at *; omega))

theorem step1 {code : Program L16} {input : Input L16} {s t : State L16}
    (hs : step code input s = some (.next t)) : Steps code input 1 s t :=
  Steps.cons hs (Steps.zero t)

theorem sub_exact {x y : Word bits} (h : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  rw [WordOps.sub_val, show 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits by exit_arith,
    Nat.add_mod_right]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) x.isLt)

theorem run_copyLoop16 {code : Program L16} {input : Input L16}
    {loopPC exitPC : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code
      (copyLoopCode (hi := hi) (hw := hw) loopPC exitPC) loopPC)
    (hExit : exitPC < code.size) (hFit : loopPC + 5 < code.size)
    (hBits : workCap < 2 ^ bits)
    {src₀ dst₀ len : Nat}
    (hSrcBound : src₀ + len ≤ workCap) (hDstBound : dst₀ + len ≤ workCap)
    (hSafe : dst₀ + len ≤ src₀ ∨ src₀ + len ≤ dst₀ ∨ dst₀ < src₀)
    {s₀ : State L16}
    (hPC : s₀.pc = loopPC) (hSz : s₀.data.size = workCap)
    (hOne : (reg s₀ rOne).val = 1)
    (hR11 : (reg s₀ r11).val = src₀) (hR12 : (reg s₀ r12).val = dst₀)
    (hR13 : (reg s₀ r13).val = src₀ + len) :
    ∃ (t : State L16) (k : Nat),
      k = 6 * len + 1 ∧
      Steps code input k s₀ t ∧
      t.pc = exitPC ∧
      t.data.size = workCap ∧
      (reg t r11).val = src₀ + len ∧
      (reg t r12).val = dst₀ + len ∧
      (reg t r13).val = src₀ + len ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r14 → reg t r = reg s₀ r) ∧
      (∀ j < len, t.data[dst₀ + j]? = s₀.data[src₀ + j]?) ∧
      (∀ addr, (addr < dst₀ ∨ dst₀ + len ≤ addr) → t.data[addr]? = s₀.data[addr]?) :=
  PaperB.RamSealedPacker.run_copyLoop
    (fun k hk => hPl k hk) hExit hFit hBits hSrcBound hDstBound hSafe
    hPC hSz hOne hR11 hR12 hR13

/-! #### Block 0: `exitInitA` (`0..24`) and `exitInitB` (`25..46`) -/

private theorem exitInitA1_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitInitACode h100) offInitA)
    (hFit : offInitA + 17 < code.size)
    {n m root Q treeBase emitBase loopBase : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offInitA)
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hBound : loopBase + loopWorkWords n m < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 17 s₀ s1 ∧
      s1.pc = offInitA + 17 ∧
      s1.data = s₀.data ∧
      (reg s1 r11).val = exitPtrsBase loopBase n m ∧
      (∀ r : Fin 16, r.val ≤ 10 → reg s1 r = reg s₀ r) := by
  have hnB : 78 * n < 2 ^ bits := by unfold loopWorkWords at hBound <;> exit_arith
  have hmB : 10 * m < 2 ^ bits := by unfold loopWorkWords at hBound <;> exit_arith
  have hL : exitPtrsBase loopBase n m < 2 ^ bits := by
    unfold exitPtrsBase loopWorkWords at * <;> exit_arith
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1 : (reg t1 r11).val = 2 * n := by
    rw [r1_11, add_no_wrap _ _ (by rw [hRegs.consts.nVal] <;> exit_arith), hRegs.consts.nVal] <;> exit_arith
  obtain ⟨t2, hs2, pc2, r2_12, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2 : (reg t2 r12).val = 4 * n := by
    rw [r2_12, add_no_wrap _ _ (by rw [v1] <;> exit_arith), v1] <;> exit_arith
  have v2_11 : (reg t2 r11).val = 2 * n := by rw [p2 r11 (by decide), v1]
  obtain ⟨t3, hs3, pc3, r3_11, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3 : (reg t3 r11).val = 6 * n := by
    rw [r3_11, add_no_wrap _ _ (by rw [v2_11, v2] <;> exit_arith), v2_11, v2] <;> exit_arith
  have v3_12 : (reg t3 r12).val = 4 * n := by rw [p3 r12 (by decide), v2]
  obtain ⟨t4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4 : (reg t4 r12).val = 8 * n := by
    rw [r4_12, add_no_wrap _ _ (by rw [v3_12] <;> exit_arith), v3_12] <;> exit_arith
  have v4_11 : (reg t4 r11).val = 6 * n := by rw [p4 r11 (by decide), v3]
  obtain ⟨t5, hs5, pc5, r5_11, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5 : (reg t5 r11).val = 14 * n := by
    rw [r5_11, add_no_wrap _ _ (by rw [v4_11, v4] <;> exit_arith), v4_11, v4] <;> exit_arith
  have v5_12 : (reg t5 r12).val = 8 * n := by rw [p5 r12 (by decide), v4]
  obtain ⟨t6, hs6, pc6, r6_12, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6 : (reg t6 r12).val = 16 * n := by
    rw [r6_12, add_no_wrap _ _ (by rw [v5_12] <;> exit_arith), v5_12] <;> exit_arith
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7 : (reg t7 r12).val = 32 * n := by
    rw [r7_12, add_no_wrap _ _ (by rw [v6] <;> exit_arith), v6] <;> exit_arith
  obtain ⟨t8, hs8, pc8, r8_12, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8 : (reg t8 r12).val = 64 * n := by
    rw [r8_12, add_no_wrap _ _ (by rw [v7] <;> exit_arith), v7] <;> exit_arith
  have v8_11 : (reg t8 r11).val = 14 * n := by
    rw [p8 r11 (by decide), p7 r11 (by decide), p6 r11 (by decide), v5]
  obtain ⟨t9, hs9, pc9, r9_11, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9 : (reg t9 r11).val = 78 * n := by
    rw [r9_11, add_no_wrap _ _ (by rw [v8_11, v8] <;> exit_arith), v8_11, v8] <;> exit_arith
  have v9_m : (reg t9 r3).val = m := by
    rw [p9 r3 (by decide), p8 r3 (by decide), p7 r3 (by decide), p6 r3 (by decide),
      p5 r3 (by decide), p4 r3 (by decide), p3 r3 (by decide), p2 r3 (by decide),
      p1 r3 (by decide), hRegs.consts.mVal]
  obtain ⟨t10, hs10, pc10, r10_12, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10 : (reg t10 r12).val = 2 * m := by
    rw [r10_12, add_no_wrap _ _ (by rw [v9_m] <;> exit_arith), v9_m] <;> exit_arith
  obtain ⟨t11, hs11, pc11, r11_13, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11 : (reg t11 r13).val = 4 * m := by
    rw [r11_13, add_no_wrap _ _ (by rw [v10] <;> exit_arith), v10] <;> exit_arith
  obtain ⟨t12, hs12, pc12, r12_13, p12, d12⟩ := step_add16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12 : (reg t12 r13).val = 8 * m := by
    rw [r12_13, add_no_wrap _ _ (by rw [v11] <;> exit_arith), v11] <;> exit_arith
  have v12_12 : (reg t12 r12).val = 2 * m := by
    rw [p12 r12 (by decide), p11 r12 (by decide), v10]
  obtain ⟨t13, hs13, pc13, r13_12, p13, d13⟩ := step_add16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith)
  have v13 : (reg t13 r12).val = 10 * m := by
    rw [r13_12, add_no_wrap _ _ (by rw [v12_12, v12] <;> exit_arith), v12_12, v12] <;> exit_arith
  have v13_11 : (reg t13 r11).val = 78 * n := by
    rw [p13 r11 (by decide), p12 r11 (by decide), p11 r11 (by decide), p10 r11 (by decide), v9]
  obtain ⟨t14, hs14, pc14, r14_11, p14, d14⟩ := step_add16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13] <;> exit_arith)
  have v14 : (reg t14 r11).val = 78 * n + 10 * m := by
    rw [r14_11, add_no_wrap _ _ (by rw [v13_11, v13]; simp only [loopWorkWords] at hBound <;> exit_arith), v13_11, v13]
  obtain ⟨t15, hs15, pc15, r15_12, p15, d15⟩ := step_imm16 (input := input) (s := t14) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc14] <;> exit_arith)
  have v15_11 : (reg t15 r11).val = 78 * n + 10 * m := by rw [p15 r11 (by decide), v14]
  have v15_12 : (reg t15 r12).val = 37 := by rw [r15_12] <;> rfl
  obtain ⟨t16, hs16, pc16, r16_11, p16, d16⟩ := step_add16 (input := input) (s := t15) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) (by rw [pc15] <;> exit_arith)
  have v16 : (reg t16 r11).val = loopWorkWords n m := by
    rw [r16_11, add_no_wrap _ _ (by rw [v15_11, v15_12]; simp only [loopWorkWords] at hBound ⊢ <;> exit_arith),
      v15_11, v15_12]; unfold loopWorkWords <;> exit_arith
  have v16_8 : (reg t16 r8).val = loopBase := by
    rw [p16 r8 (by decide), p15 r8 (by decide), p14 r8 (by decide), p13 r8 (by decide),
      p12 r8 (by decide), p11 r8 (by decide), p10 r8 (by decide), p9 r8 (by decide),
      p8 r8 (by decide), p7 r8 (by decide), p6 r8 (by decide), p5 r8 (by decide),
      p4 r8 (by decide), p3 r8 (by decide), p2 r8 (by decide), p1 r8 (by decide), hRegs.loopBaseVal]
  obtain ⟨t17, hs17, pc17, r17_11, p17, d17⟩ := step_add16 (input := input) (s := t16) (hPl.at 16 (by exit_rom_bound) (by exit_arith)) (by rw [pc16] <;> exit_arith)
  have v17 : (reg t17 r11).val = exitPtrsBase loopBase n m := by
    rw [r17_11, add_no_wrap _ _ (by rw [v16_8, v16]; unfold exitPtrsBase at hL <;> exit_arith), v16_8, v16]
    rfl
  refine ⟨t17, ?_, by rw [pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5,
      pc4, pc3, pc2, pc1, hPC], ?_, v17, ?_⟩
  · exact Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
      (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15
      (Steps.cons hs16 (step1 hs17))))))))))))))))
  · rw [d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  · intro r hr
    rw [p17 r (by exit_arith), p16 r (by exit_arith), p15 r (by exit_arith), p14 r (by exit_arith),
      p13 r (by exit_arith), p12 r (by exit_arith), p11 r (by exit_arith), p10 r (by exit_arith),
      p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith),
      p5 r (by exit_arith), p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]

private theorem exitInitA2_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitInitACode h100) offInitA)
    (hFit : offInitA + 25 < code.size)
    {n m root Q treeBase emitBase loopBase : Nat}
    {s1 : State L16} (hPC : s1.pc = offInitA + 17)
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s1)
    (hr11 : (reg s1 r11).val = exitPtrsBase loopBase n m)
    (hBound : exitSubStateBase loopBase n m < 2 ^ bits) :
    ∃ s2 : State L16,
      Steps code input 8 s1 s2 ∧
      s2.pc = offInitB ∧
      s2.data = s1.data ∧
      (reg s2 r11).val = exitPtrsBase loopBase n m ∧
      (reg s2 r12).val = exitArenaBase loopBase n m ∧
      (reg s2 r13).val = exitSubStateBase loopBase n m ∧
      (∀ r : Fin 16, r.val ≤ 10 → reg s2 r = reg s1 r) := by
  have h1 : exitArenaBase loopBase n m < 2 ^ bits := by
    unfold exitSubStateBase at hBound <;> exit_arith
  have h2 : 48 * n < 2 ^ bits := by
    unfold exitSubStateBase at hBound <;> exit_arith
  obtain ⟨t1, hs1, pc1, r1_13, p1, d1⟩ := step_add16 (input := input) (s := s1) (hPl.at 17 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1 : (reg t1 r13).val = 2 * n := by
    rw [r1_13, add_no_wrap _ _ (by rw [hRegs.consts.nVal] <;> exit_arith), hRegs.consts.nVal] <;> exit_arith
  have v1_2 : (reg t1 r2).val = n := by rw [p1 r2 (by decide), hRegs.consts.nVal]
  obtain ⟨t2, hs2, pc2, r2_13, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 18 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2 : (reg t2 r13).val = 3 * n := by
    rw [r2_13, add_no_wrap _ _ (by rw [v1, v1_2] <;> exit_arith), v1, v1_2] <;> exit_arith
  have v2_11 : (reg t2 r11).val = exitPtrsBase loopBase n m := by
    rw [p2 r11 (by decide), p1 r11 (by decide), hr11]
  obtain ⟨t3, hs3, pc3, r3_12, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 19 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3 : (reg t3 r12).val = exitArenaBase loopBase n m := by
    rw [r3_12, add_no_wrap _ _ (by rw [v2_11, v2]; exact h1), v2_11, v2] <;> rfl
  have v3_13 : (reg t3 r13).val = 3 * n := by rw [p3 r13 (by decide), v2]
  obtain ⟨t4, hs4, pc4, r4_14, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 20 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4 : (reg t4 r14).val = 6 * n := by
    rw [r4_14, add_no_wrap _ _ (by rw [v3_13] <;> exit_arith), v3_13] <;> exit_arith
  obtain ⟨t5, hs5, pc5, r5_14, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 21 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5 : (reg t5 r14).val = 12 * n := by
    rw [r5_14, add_no_wrap _ _ (by rw [v4] <;> exit_arith), v4] <;> exit_arith
  obtain ⟨t6, hs6, pc6, r6_14, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 22 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6 : (reg t6 r14).val = 24 * n := by
    rw [r6_14, add_no_wrap _ _ (by rw [v5] <;> exit_arith), v5] <;> exit_arith
  obtain ⟨t7, hs7, pc7, r7_14, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 23 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7 : (reg t7 r14).val = 48 * n := by
    rw [r7_14, add_no_wrap _ _ (by rw [v6] <;> exit_arith), v6] <;> exit_arith
  have v7_12 : (reg t7 r12).val = exitArenaBase loopBase n m := by
    rw [p7 r12 (by decide), p6 r12 (by decide), p5 r12 (by decide), p4 r12 (by decide), v3]
  obtain ⟨t8, hs8, pc8, r8_13, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 24 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8 : (reg t8 r13).val = exitSubStateBase loopBase n m := by
    rw [r8_13, add_no_wrap _ _ (by rw [v7_12, v7]; exact hBound), v7_12, v7] <;> rfl
  have v8_11 : (reg t8 r11).val = exitPtrsBase loopBase n m := by
    rw [p8 r11 (by decide), p7 r11 (by decide), p6 r11 (by decide), p5 r11 (by decide),
      p4 r11 (by decide), p3 r11 (by decide), v2_11]
  have v8_12 : (reg t8 r12).val = exitArenaBase loopBase n m := by rw [p8 r12 (by decide), v7_12]
  refine ⟨t8, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (step1 hs8))))))),
    by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl,
    by rw [d8, d7, d6, d5, d4, d3, d2, d1], v8_11, v8_12, v8, ?_⟩
  intro r hr
  rw [p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith),
    p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]

private theorem exitInitB_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitInitBCode workCap hw h100) offInitB)
    (hFit : offInitB + 22 < code.size)
    {n m root Q treeBase emitBase loopBase : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offInitB) (hSz : s₀.data.size = workCap)
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hr11 : (reg s₀ r11).val = exitPtrsBase loopBase n m)
    (hr12 : (reg s₀ r12).val = exitArenaBase loopBase n m)
    (hr13 : (reg s₀ r13).val = exitSubStateBase loopBase n m)
    (hWorkBnd : exitSubWorkBase loopBase n m workCap ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 22 s₀ s1 ∧
      s1.pc = offHdr ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase 0 0 s1 ∧
      (s1.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m) ∧
      (s1.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) ∧
      (s1.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 13]?).map Fin.val = some (exitSubInBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 14]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) ∧
      (∀ addr, addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
        (addr < exitSubStateBase loopBase n m ∨ exitSubStateBase loopBase n m + 15 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  have hSubInLt : exitSubInBase loopBase n m ≤ workCap := by
    simp only [exitSubWorkBase, exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, loopWorkWords] at hWorkBnd ⊢
    exit_arith
  have hSubWorkLe : exitSubWorkBase loopBase n m workCap ≤ workCap := hWorkBnd
  have hStFit : exitSubStateBase loopBase n m + 15 ≤ workCap := by
    unfold exitSubWorkBase exitSubInBase at hWorkBnd <;> exit_arith
  have hSt15 : 2 < workCap := by
    unfold exitSubStateBase exitArenaBase exitPtrsBase loopWorkWords at hStFit <;> exit_arith
  -- Part 1: indices 0..13 (store mem[2], mem[st+11], mem[st+12], mem[0], mem[st+13])
  obtain ⟨t1, hs1, pc1, r1_14, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have b1 : (reg t1 r14).val < t1.data.size := by rw [d1, hSz, r1_14]; exact hSt15
  obtain ⟨t2, hs2, pc2, rg2, d2⟩ := step_storeData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc1, hPC] <;> exit_arith) b1
  obtain ⟨t3, hs3, pc3, r3_14, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2, pc1, hPC] <;> exit_arith)
  have v3_13 : (reg t3 r13).val = exitSubStateBase loopBase n m := by
    rw [p3 r13 (by decide), reg_eq_of_regs_eq rg2 r13, p1 r13 (by decide), hr13]
  have v3_14 : (reg t3 r14).val = 11 := by rw [r3_14] <;> rfl
  obtain ⟨t4, hs4, pc4, r4_15, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3, pc2, pc1, hPC] <;> exit_arith)
  have v4_15 : (reg t4 r15).val = exitSubStateBase loopBase n m + 11 := by
    rw [r4_15, add_no_wrap _ _ (by rw [v3_13, v3_14] <;> exit_arith), v3_13, v3_14]
  have b4 : (reg t4 r15).val < t4.data.size := by rw [d4, d3, d2, Array.size_set, d1, hSz, v4_15] <;> exit_arith
  obtain ⟨t5, hs5, pc5, rg5, d5⟩ := step_storeData16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4, pc3, pc2, pc1, hPC] <;> exit_arith) b4
  obtain ⟨t6, hs6, pc6, r6_14, p6, d6⟩ := step_imm16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
  have v6_13 : (reg t6 r13).val = exitSubStateBase loopBase n m := by
    rw [p6 r13 (by decide), reg_eq_of_regs_eq rg5 r13, p4 r13 (by decide), v3_13]
  have v6_14 : (reg t6 r14).val = 12 := by rw [r6_14] <;> rfl
  obtain ⟨t7, hs7, pc7, r7_15, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
  have v7_15 : (reg t7 r15).val = exitSubStateBase loopBase n m + 12 := by
    rw [r7_15, add_no_wrap _ _ (by rw [v6_13, v6_14] <;> exit_arith), v6_13, v6_14]
  have b7 : (reg t7 r15).val < t7.data.size := by rw [d7, d6, d5, Array.size_set, d4, d3, d2, Array.size_set, d1, hSz, v7_15] <;> exit_arith
  obtain ⟨t8, hs8, pc8, rg8, d8⟩ := step_storeData16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith) b7
  obtain ⟨t9, hs9, pc9, r9_14, p9, d9⟩ := step_imm16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
  have v9_13 : (reg t9 r13).val = exitSubStateBase loopBase n m := by
    rw [p9 r13 (by decide), reg_eq_of_regs_eq rg8 r13, p7 r13 (by decide), v6_13]
  have v9_14 : (reg t9 r14).val = 16 := by rw [r9_14] <;> rfl
  obtain ⟨t10, hs10, pc10, r10_11, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
  have v10_11 : (reg t10 r11).val = exitSubInBase loopBase n m := by
    rw [r10_11, add_no_wrap _ _ (by rw [v9_13, v9_14]; unfold exitSubInBase at hSubInLt <;> exit_arith), v9_13, v9_14] <;> rfl
  have v10_0 : (reg t10 r0).val = 0 := by
    rw [p10 r0 (by decide), p9 r0 (by decide), reg_eq_of_regs_eq rg8 r0, p7 r0 (by decide),
      p6 r0 (by decide), reg_eq_of_regs_eq rg5 r0, p4 r0 (by decide), p3 r0 (by decide),
      reg_eq_of_regs_eq rg2 r0, p1 r0 (by decide), hRegs.consts.zero]
  have b10 : (reg t10 r0).val < t10.data.size := by
    rw [d10, d9, d8, Array.size_set, d7, d6, d5, Array.size_set, d4, d3, d2, Array.size_set, d1, hSz, v10_0] <;> exit_arith
  obtain ⟨t11, hs11, pc11, rg11, d11⟩ := step_storeData16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith) b10
  obtain ⟨t12, hs12, pc12, r12_14, p12, d12⟩ := step_imm16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
  have v12_13 : (reg t12 r13).val = exitSubStateBase loopBase n m := by
    rw [p12 r13 (by decide), reg_eq_of_regs_eq rg11 r13, p10 r13 (by decide), v9_13]
  have v12_14 : (reg t12 r14).val = 13 := by rw [r12_14] <;> rfl
  obtain ⟨t13, hs13, pc13, r13_15, p13, d13⟩ := step_add16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
  have v13_15 : (reg t13 r15).val = exitSubStateBase loopBase n m + 13 := by
    rw [r13_15, add_no_wrap _ _ (by rw [v12_13, v12_14] <;> exit_arith), v12_13, v12_14]
  have b13 : (reg t13 r15).val < t13.data.size := by
    rw [d13, d12, d11, Array.size_set, d10, d9, d8, Array.size_set, d7, d6, d5, Array.size_set,
      d4, d3, d2, Array.size_set, d1, hSz, v13_15] <;> exit_arith
  obtain ⟨t14, hs14, pc14, rg14, d14⟩ := step_storeData16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith) b13
  -- Part 2: indices 14..21
  have pc14' : t14.pc = offInitB + 14 := by rw [pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]
  obtain ⟨t15, hs15, pc15, r15_14, p15, d15⟩ := step_imm16 (input := input) (s := t14) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc14']; try exit_arith)
  have v15_11 : (reg t15 r11).val = exitSubInBase loopBase n m := by
    rw [p15 r11 (by decide), reg_eq_of_regs_eq rg14 r11, p13 r11 (by decide), p12 r11 (by decide),
      reg_eq_of_regs_eq rg11 r11, v10_11]
  have v15_14 : (reg t15 r14).val = workCap / 64 := by rw [r15_14] <;> rfl
  obtain ⟨t16, hs16, pc16, r16_11, p16, d16⟩ := step_add16 (input := input) (s := t15) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) (by rw [pc15, pc14'] <;> exit_arith)
  have v16_11 : (reg t16 r11).val = exitSubWorkBase loopBase n m workCap := by
    rw [r16_11, add_no_wrap _ _ (by rw [v15_11, v15_14]; unfold exitSubWorkBase at hSubWorkLe <;> exit_arith), v15_11, v15_14] <;> rfl
  have v16_1 : (reg t16 r1).val = 1 := by
    rw [p16 r1 (by decide), p15 r1 (by decide), reg_eq_of_regs_eq rg14 r1, p13 r1 (by decide),
      p12 r1 (by decide), reg_eq_of_regs_eq rg11 r1, p10 r1 (by decide), p9 r1 (by decide),
      reg_eq_of_regs_eq rg8 r1, p7 r1 (by decide), p6 r1 (by decide), reg_eq_of_regs_eq rg5 r1,
      p4 r1 (by decide), p3 r1 (by decide), reg_eq_of_regs_eq rg2 r1, p1 r1 (by decide), hRegs.consts.one]
  have b16 : (reg t16 r1).val < t16.data.size := by
    rw [d16, d15, d14, Array.size_set, d13, d12, d11, Array.size_set, d10, d9, d8, Array.size_set,
      d7, d6, d5, Array.size_set, d4, d3, d2, Array.size_set, d1, hSz, v16_1] <;> exit_arith
  obtain ⟨t17, hs17, pc17, rg17, d17⟩ := step_storeData16 (input := input) (s := t16) (hPl.at 16 (by exit_rom_bound) (by exit_arith)) (by rw [pc16, pc15, pc14'] <;> exit_arith) b16
  obtain ⟨t18, hs18, pc18, r18_14, p18, d18⟩ := step_imm16 (input := input) (s := t17) (hPl.at 17 (by exit_rom_bound) (by exit_arith)) (by rw [pc17, pc16, pc15, pc14'] <;> exit_arith)
  have v18_13 : (reg t18 r13).val = exitSubStateBase loopBase n m := by
    rw [p18 r13 (by decide), reg_eq_of_regs_eq rg17 r13, p16 r13 (by decide), p15 r13 (by decide),
      reg_eq_of_regs_eq rg14 r13, p13 r13 (by decide), v12_13]
  have v18_14 : (reg t18 r14).val = 14 := by rw [r18_14] <;> rfl
  obtain ⟨t19, hs19, pc19, r19_15, p19, d19⟩ := step_add16 (input := input) (s := t18) (hPl.at 18 (by exit_rom_bound) (by exit_arith)) (by rw [pc18, pc17, pc16, pc15, pc14'] <;> exit_arith)
  have v19_15 : (reg t19 r15).val = exitSubStateBase loopBase n m + 14 := by
    rw [r19_15, add_no_wrap _ _ (by rw [v18_13, v18_14] <;> exit_arith), v18_13, v18_14]
  have b19 : (reg t19 r15).val < t19.data.size := by
    rw [d19, d18, d17, Array.size_set, d16, d15, d14, Array.size_set, d13, d12, d11, Array.size_set,
      d10, d9, d8, Array.size_set, d7, d6, d5, Array.size_set, d4, d3, d2, Array.size_set, d1, hSz, v19_15] <;> exit_arith
  obtain ⟨t20, hs20, pc20, rg20, d20⟩ := step_storeData16 (input := input) (s := t19) (hPl.at 19 (by exit_rom_bound) (by exit_arith)) (by rw [pc19, pc18, pc17, pc16, pc15, pc14'] <;> exit_arith) b19
  obtain ⟨t21, hs21, pc21, r21_9, p21, d21⟩ := step_mov16 (input := input) (s := t20) (hPl.at 20 (by exit_rom_bound) (by exit_arith)) (by rw [pc20, pc19, pc18, pc17, pc16, pc15, pc14'] <;> exit_arith)
  obtain ⟨t22, hs22, pc22, r22_10, p22, d22⟩ := step_mov16 (input := input) (s := t21) (hPl.at 21 (by exit_rom_bound) (by exit_arith)) (by rw [pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14'] <;> exit_arith)
  have hKeep08 : ∀ r : Fin 16, r.val ≤ 8 → reg t22 r = reg s₀ r := by
    intro r hr
    rw [p22 r (by exit_arith), p21 r (by exit_arith), reg_eq_of_regs_eq rg20 r, p19 r (by exit_arith),
      p18 r (by exit_arith), reg_eq_of_regs_eq rg17 r, p16 r (by exit_arith), p15 r (by exit_arith),
      reg_eq_of_regs_eq rg14 r, p13 r (by exit_arith), p12 r (by exit_arith), reg_eq_of_regs_eq rg11 r,
      p10 r (by exit_arith), p9 r (by exit_arith), reg_eq_of_regs_eq rg8 r, p7 r (by exit_arith), p6 r (by exit_arith),
      reg_eq_of_regs_eq rg5 r, p4 r (by exit_arith), p3 r (by exit_arith), reg_eq_of_regs_eq rg2 r, p1 r (by exit_arith)]
  have hExitRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase 0 0 t22 :=
    { entry :=
        { consts :=
            { zero := (congrArg Fin.val (hKeep08 rZero (by decide))).trans hRegs.consts.zero
              one := (congrArg Fin.val (hKeep08 rOne (by decide))).trans hRegs.consts.one
              nVal := (congrArg Fin.val (hKeep08 rN (by decide))).trans hRegs.consts.nVal
              mVal := (congrArg Fin.val (hKeep08 rM (by decide))).trans hRegs.consts.mVal
              rootVal := (congrArg Fin.val (hKeep08 rRoot (by decide))).trans hRegs.consts.rootVal }
          qVal := (congrArg Fin.val (hKeep08 r5 (by decide))).trans hRegs.qVal
          treeBaseVal := (congrArg Fin.val (hKeep08 r6 (by decide))).trans hRegs.treeBaseVal
          emitBaseVal := (congrArg Fin.val (hKeep08 r7 (by decide))).trans hRegs.emitBaseVal
          loopBaseVal := (congrArg Fin.val (hKeep08 r8 (by decide))).trans hRegs.loopBaseVal }
      dVal := by rw [p22 r9 (by decide), r21_9]; exact (congrArg Fin.val (hKeep08 rZero (by decide)) |> fun _ => by
        rw [reg_eq_of_regs_eq rg20 r0, p19 r0 (by decide), p18 r0 (by decide),
          reg_eq_of_regs_eq rg17 r0, p16 r0 (by decide), p15 r0 (by decide),
          reg_eq_of_regs_eq rg14 r0, p13 r0 (by decide), p12 r0 (by decide),
          reg_eq_of_regs_eq rg11 r0, v10_0])
      usedVal := by rw [r22_10, p21 r0 (by decide), reg_eq_of_regs_eq rg20 r0,
        p19 r0 (by decide), p18 r0 (by decide), reg_eq_of_regs_eq rg17 r0,
        p16 r0 (by decide), p15 r0 (by decide), reg_eq_of_regs_eq rg14 r0, p13 r0 (by decide), p12 r0 (by decide),
          reg_eq_of_regs_eq rg11 r0, v10_0] }
  have hDataEq : t22.data = t20.data := by rw [d22, d21]
  have hSteps : Steps code input 22 s₀ t22 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
      (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15
      (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19 (Steps.cons hs20
      (Steps.cons hs21 (step1 hs22)))))))))))))))))))))
  have hPCfin : t22.pc = offHdr := by rw [pc22, pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14'] <;> rfl
  have hSzFin : t22.data.size = workCap := by
    rw [hDataEq, d20, Array.size_set, d19, d18, d17, Array.size_set, d16, d15, d14, Array.size_set,
      d13, d12, d11, Array.size_set, d10, d9, d8, Array.size_set, d7, d6, d5, Array.size_set,
      d4, d3, d2, Array.size_set, d1, hSz]
  have h10_11 : (reg t10 r11).val = exitSubInBase loopBase n m := v10_11
  have h16_11 : (reg t16 r11).val = exitSubWorkBase loopBase n m workCap := v16_11
  have h4_11 : (reg t4 r11).val = exitPtrsBase loopBase n m := by
    rw [p4 r11 (by decide), p3 r11 (by decide), reg_eq_of_regs_eq rg2 r11, p1 r11 (by decide), hr11]
  have h7_12 : (reg t7 r12).val = exitArenaBase loopBase n m := by
    rw [p7 r12 (by decide), p6 r12 (by decide), reg_eq_of_regs_eq rg5 r12, p4 r12 (by decide),
      p3 r12 (by decide), reg_eq_of_regs_eq rg2 r12, p1 r12 (by decide), hr12]
  have h13_11 : (reg t13 r11).val = exitSubInBase loopBase n m := by
    rw [p13 r11 (by decide), p12 r11 (by decide), reg_eq_of_regs_eq rg11 r11, h10_11]
  have h19_11 : (reg t19 r11).val = exitSubWorkBase loopBase n m workCap := by
    rw [p19 r11 (by decide), p18 r11 (by decide), reg_eq_of_regs_eq rg17 r11, h16_11]
  have hInitial : 2 < exitSubStateBase loopBase n m := by
    unfold exitSubStateBase exitArenaBase exitPtrsBase loopWorkWords
    omega
  have hAddr2 : (reg t1 r14).val = statePtrAddr := by rw [r1_14] <;> rfl
  have hRead2 : (t2.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m) := by
    rw [d2, ← hAddr2, Array.getElem?_set_self, Option.map_some, p1 r13 (by decide), hr13]
  have hKeep2 (addr : Nat) (hf : (statePtrAddr) ≠ addr) :
      t2.data[addr]? = s₀.data[addr]? := by
    rw [d2, Array.getElem?_set_ne _ (by rw [hAddr2]; exact hf), d1]
  have hAddr5 : (reg t4 r15).val = exitSubStateBase loopBase n m + 11 := by rw [v4_15] <;> rfl
  have hRead5 : (t5.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) := by
    rw [d5, ← hAddr5, Array.getElem?_set_self, Option.map_some, h4_11]
  have hKeep5 (addr : Nat) (hf : (exitSubStateBase loopBase n m + 11) ≠ addr) :
      t5.data[addr]? = t2.data[addr]? := by
    rw [d5, Array.getElem?_set_ne _ (by rw [hAddr5]; exact hf), d4, d3]
  have hAddr8 : (reg t7 r15).val = exitSubStateBase loopBase n m + 12 := by rw [v7_15] <;> rfl
  have hRead8 : (t8.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m) := by
    rw [d8, ← hAddr8, Array.getElem?_set_self, Option.map_some, h7_12]
  have hKeep8 (addr : Nat) (hf : (exitSubStateBase loopBase n m + 12) ≠ addr) :
      t8.data[addr]? = t5.data[addr]? := by
    rw [d8, Array.getElem?_set_ne _ (by rw [hAddr8]; exact hf), d7, d6]
  have hAddr11 : (reg t10 r0).val = inPtrAddr := by rw [v10_0] <;> rfl
  have hRead11 : (t11.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m) := by
    rw [d11, ← hAddr11, Array.getElem?_set_self, Option.map_some, h10_11]
  have hKeep11 (addr : Nat) (hf : (inPtrAddr) ≠ addr) :
      t11.data[addr]? = t8.data[addr]? := by
    rw [d11, Array.getElem?_set_ne _ (by rw [hAddr11]; exact hf), d10, d9]
  have hAddr14 : (reg t13 r15).val = exitSubStateBase loopBase n m + 13 := by rw [v13_15] <;> rfl
  have hRead14 : (t14.data[exitSubStateBase loopBase n m + 13]?).map Fin.val = some (exitSubInBase loopBase n m) := by
    rw [d14, ← hAddr14, Array.getElem?_set_self, Option.map_some, h13_11]
  have hKeep14 (addr : Nat) (hf : (exitSubStateBase loopBase n m + 13) ≠ addr) :
      t14.data[addr]? = t11.data[addr]? := by
    rw [d14, Array.getElem?_set_ne _ (by rw [hAddr14]; exact hf), d13, d12]
  have hAddr17 : (reg t16 r1).val = dataPtrAddr := by rw [v16_1] <;> rfl
  have hRead17 : (t17.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) := by
    rw [d17, ← hAddr17, Array.getElem?_set_self, Option.map_some, h16_11]
  have hKeep17 (addr : Nat) (hf : (dataPtrAddr) ≠ addr) :
      t17.data[addr]? = t14.data[addr]? := by
    rw [d17, Array.getElem?_set_ne _ (by rw [hAddr17]; exact hf), d16, d15]
  have hAddr20 : (reg t19 r15).val = exitSubStateBase loopBase n m + 14 := by rw [v19_15] <;> rfl
  have hRead20 : (t20.data[exitSubStateBase loopBase n m + 14]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) := by
    rw [d20, ← hAddr20, Array.getElem?_set_self, Option.map_some, h19_11]
  have hKeep20 (addr : Nat) (hf : (exitSubStateBase loopBase n m + 14) ≠ addr) :
      t20.data[addr]? = t17.data[addr]? := by
    rw [d20, Array.getElem?_set_ne _ (by rw [hAddr20]; exact hf), d19, d18]
  have hAt2 : (t22.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m) := by
    rw [hDataEq]
    rw [hKeep20 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep17 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep14 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep11 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep8 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep5 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    exact hRead2
  have hAt11 : (t22.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) := by
    rw [hDataEq]
    rw [hKeep20 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep17 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep14 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep11 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep8 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    exact hRead5
  have hAt12 : (t22.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m) := by
    rw [hDataEq]
    rw [hKeep20 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep17 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep14 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep11 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    exact hRead8
  have hAt0 : (t22.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m) := by
    rw [hDataEq]
    rw [hKeep20 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep17 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep14 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    exact hRead11
  have hAt13 : (t22.data[exitSubStateBase loopBase n m + 13]?).map Fin.val = some (exitSubInBase loopBase n m) := by
    rw [hDataEq]
    rw [hKeep20 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    rw [hKeep17 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    exact hRead14
  have hAt1 : (t22.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) := by
    rw [hDataEq]
    rw [hKeep20 _ (by first | omega | (simp only [inPtrAddr, dataPtrAddr, statePtrAddr]; omega))]
    exact hRead17
  have hAt14 : (t22.data[exitSubStateBase loopBase n m + 14]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) := by
    rw [hDataEq]
    exact hRead20
  have hFrame : ∀ addr, addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
      (addr < exitSubStateBase loopBase n m ∨ exitSubStateBase loopBase n m + 15 ≤ addr) →
      t22.data[addr]? = s₀.data[addr]? := by
    intro addr h0 h1 h2 hSt
    rw [hDataEq, hKeep20 _ (by omega), hKeep17 _ (Ne.symm h1), hKeep14 _ (by omega),
      hKeep11 _ (Ne.symm h0), hKeep8 _ (by omega), hKeep5 _ (by omega), hKeep2 _ (Ne.symm h2)]
  exact ⟨t22, hSteps, hPCfin, hSzFin, hExitRegs, hAt0, hAt1, hAt2, hAt11, hAt12, hAt13, hAt14, hFrame⟩

theorem exitInit_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPlA : SlicePlaced (hi := hi) (hw := hw) code (exitInitACode h100) offInitA)
    (hPlB : SlicePlaced (hi := hi) (hw := hw) code (exitInitBCode workCap hw h100) offInitB)
    (hFit : offInitB + 22 < code.size)
    {n m root Q treeBase emitBase loopBase : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offInitA) (hSz : s₀.data.size = workCap)
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hWorkBnd : exitSubWorkBase loopBase n m workCap ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 47 s₀ s1 ∧
      s1.pc = offHdr ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase 0 0 s1 ∧
      (s1.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m) ∧
      (s1.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) ∧
      (s1.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 13]?).map Fin.val = some (exitSubInBase loopBase n m) ∧
      (s1.data[exitSubStateBase loopBase n m + 14]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap) ∧
      (∀ addr, addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
        (addr < exitSubStateBase loopBase n m ∨ exitSubStateBase loopBase n m + 15 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  have hBnd1 : loopBase + loopWorkWords n m < 2 ^ bits := by
    unfold exitSubWorkBase exitSubInBase exitSubStateBase exitArenaBase exitPtrsBase at hWorkBnd
    exit_arith
  have hBnd2 : exitSubStateBase loopBase n m < 2 ^ bits := by
    unfold exitSubWorkBase exitSubInBase at hWorkBnd
    exit_arith
  obtain ⟨s1, hs1, pc1, d1, r1_11, k1⟩ :=
    exitInitA1_steps h100 hPlA (by exit_arith) hPC hRegs hBnd1
  have hRegs1 : LoopEntryRegs n m root Q treeBase emitBase loopBase s1 :=
    (exitLoopRegs_of_keep ⟨hRegs, rfl, rfl⟩ (fun r hr => k1 r (by exit_arith))).entry
  obtain ⟨s2, hs2, pc2, d2, r2_11, r2_12, r2_13, k2⟩ :=
    exitInitA2_steps h100 hPlA (by exit_arith) pc1 hRegs1 r1_11 hBnd2
  have hRegs2 : LoopEntryRegs n m root Q treeBase emitBase loopBase s2 :=
    (exitLoopRegs_of_keep ⟨hRegs1, rfl, rfl⟩ (fun r hr => k2 r (by exit_arith))).entry
  have hSz2 : s2.data.size = workCap := by rw [d2, d1, hSz]
  obtain ⟨s3, hs3, pc3, sz3, regs3, m0, m1, m2, m11, m12, m13, m14, mf⟩ :=
    exitInitB_steps h100 hPlB hFit pc2 hSz2 hRegs2 r2_11 r2_12 r2_13 hWorkBnd hBits
  refine ⟨s3, hs1.append (hs2.append hs3), pc3, sz3, regs3, m0, m1, m2, m11, m12, m13, m14,
    fun a ha0 ha1 ha2 haSt => ?_⟩
  rw [mf a ha0 ha1 ha2 haSt, d2, d1]

/-! #### Block 1: `exitHdr` (`47`) and `exitPrep` (`48..60`) -/

theorem exitHdr_lt_step {code : Program L16} {input : Input L16} {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitHdrCode bits subLen) offHdr)
    (hFit : offHdr + 1 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offHdr)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hd : d < Q) :
    ∃ s1 : State L16,
      Steps code input 1 s₀ s1 ∧
      s1.pc = offPrep ∧
      s1.regs = s₀.regs ∧
      s1.data = s₀.data := by
  have hTrue : WordOps.ltb (reg s₀ r9) (reg s₀ r5) = true :=
    branchLt_true (by rw [hRegs.dVal, hRegs.entry.qVal]; exact hd)
  have hf := hPl.at 0 (by exit_rom_bound) (by exit_arith)
  have hs := PaperB.RamProgram.step_branchLt_at (code := code) (input := input) hf
    (by rw [hTrue, ite_eq_left rfl]; exact hFit)
  rw [hTrue, ite_eq_left rfl] at hs
  exact ⟨_, step1 hs, rfl, rfl, rfl⟩

theorem exitHdr_done_step {code : Program L16} {input : Input L16} {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitHdrCode bits subLen) offHdr)
    (hFinFit : offFinish subLen < code.size)
    {n m root Q treeBase emitBase loopBase exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offHdr)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase Q exitUsed s₀) :
    ∃ s1 : State L16,
      Steps code input 1 s₀ s1 ∧
      s1.pc = offFinish subLen ∧
      s1.regs = s₀.regs ∧
      s1.data = s₀.data := by
  have hFalse : WordOps.ltb (reg s₀ r9) (reg s₀ r5) = false :=
    branchLt_false (by rw [hRegs.dVal, hRegs.entry.qVal]; exact Nat.le_refl Q)
  have hf := hPl.at 0 (by exit_rom_bound) (by exit_arith)
  have hs := PaperB.RamProgram.step_branchLt_at (code := code) (input := input) hf
    (by rw [hFalse, ite_eq_right (by decide)]; exact hFinFit)
  rw [hFalse, ite_eq_right (by decide)] at hs
  exact ⟨_, step1 hs, rfl, rfl, rfl⟩

theorem exitPrep_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitPrepCode h100) offPrep)
    (hFit : offLargeA < code.size)
    {n m root Q treeBase emitBase loopBase exitUsed : Nat}
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hQ : Q = dense.length)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State L16} (hPC : s₀.pc = offPrep)
    (hTreeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s₀.data[k]? = mem[k]?)
    (d : Fin dense.length)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s₀) :
    let n_d := 1 + (S.childSlice d).length
    ∃ s1 : State L16,
      Steps code input 13 s₀ s1 ∧
      s1.pc = (if n_d < 3 then offSmall else offLargeA) ∧
      s1.data = s₀.data ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s1 ∧
      (reg s1 r11).val = n_d := by
  have hQFit : 8 * Q ≤ workCap := by unfold staticTreeWords at hTreeFit <;> exit_arith
  have hTB : treeBase + 7 * Q + Q ≤ workCap := by unfold staticTreeWords at hTreeFit <;> exit_arith
  have hdQ : d.val < Q := by rw [hQ]; exact d.isLt
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1 : (reg t1 r11).val = 2 * Q := by
    rw [r1_11, add_no_wrap _ _ (by rw [hRegs.entry.qVal] <;> exit_arith), hRegs.entry.qVal] <;> exit_arith
  obtain ⟨t2, hs2, pc2, r2_12, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2 : (reg t2 r12).val = 4 * Q := by
    rw [r2_12, add_no_wrap _ _ (by rw [v1] <;> exit_arith), v1] <;> exit_arith
  have v2_11 : (reg t2 r11).val = 2 * Q := by rw [p2 r11 (by decide), v1]
  obtain ⟨t3, hs3, pc3, r3_11, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3 : (reg t3 r11).val = 6 * Q := by
    rw [r3_11, add_no_wrap _ _ (by rw [v2_11, v2] <;> exit_arith), v2_11, v2] <;> exit_arith
  have v3_5 : (reg t3 r5).val = Q := by
    rw [p3 r5 (by decide), p2 r5 (by decide), p1 r5 (by decide), hRegs.entry.qVal]
  obtain ⟨t4, hs4, pc4, r4_11, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4 : (reg t4 r11).val = 7 * Q := by
    rw [r4_11, add_no_wrap _ _ (by rw [v3, v3_5] <;> exit_arith), v3, v3_5] <;> exit_arith
  have v4_6 : (reg t4 r6).val = treeBase := by
    rw [p4 r6 (by decide), p3 r6 (by decide), p2 r6 (by decide), p1 r6 (by decide), hRegs.entry.treeBaseVal]
  obtain ⟨t5, hs5, pc5, r5_11, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5 : (reg t5 r11).val = treeBase + 7 * Q := by
    rw [r5_11, add_no_wrap _ _ (by rw [v4_6, v4] <;> exit_arith), v4_6, v4]
  have v5_9 : (reg t5 r9).val = d.val := by
    rw [p5 r9 (by decide), p4 r9 (by decide), p3 r9 (by decide), p2 r9 (by decide),
      p1 r9 (by decide), hRegs.dVal]
  obtain ⟨t6, hs6, pc6, r6_11, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6 : (reg t6 r11).val = treeBase + 7 * Q + d.val := by
    rw [r6_11, add_no_wrap _ _ (by rw [v5, v5_9] <;> exit_arith), v5, v5_9]
  have hData6 : t6.data = s₀.data := by rw [d6, d5, d4, d3, d2, d1]
  have hCS0Lt : S.childStart d.val < 2 ^ bits := by
    have hM := S.childStart_mono d.val dense.length (Nat.le_of_lt d.isLt) (Nat.le_refl _)
    have hE := S.childStart_end <;> exit_arith
  have hLoad6 : t6.data[(reg t6 r11).val]? = some ⟨S.childStart d.val, hCS0Lt⟩ := by
    rw [hData6, v6, hQ, hTreeMem (treeBase + 7 * dense.length + d.val) (by exit_arith)
      (by unfold staticTreeWords <;> exit_arith)]
    have hCm := S.childStart_mem d.val (Nat.le_of_lt d.isLt)
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hCm
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ :=
    step_loadData16 (hPl.at 6 (by exit_rom_bound) (by exit_arith)) hLoad6 (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = S.childStart d.val := by rw [r7_12]
  have v7_11 : (reg t7 r11).val = treeBase + 7 * Q + d.val := by rw [p7 r11 (by decide), v6]
  have v7_1 : (reg t7 r1).val = 1 := by
    rw [p7 r1 (by decide), p6 r1 (by decide), p5 r1 (by decide), p4 r1 (by decide),
      p3 r1 (by decide), p2 r1 (by decide), p1 r1 (by decide), hRegs.entry.consts.one]
  obtain ⟨t8, hs8, pc8, r8_11, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8 : (reg t8 r11).val = treeBase + 7 * Q + (d.val + 1) := by
    rw [r8_11, add_no_wrap _ _ (by rw [v7_11, v7_1] <;> exit_arith), v7_11, v7_1] <;> exit_arith
  have hCS1Lt : S.childStart (d.val + 1) < 2 ^ bits := by
    have hM := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
    have hE := S.childStart_end <;> exit_arith
  have hLoad8 : t8.data[(reg t8 r11).val]? = some ⟨S.childStart (d.val + 1), hCS1Lt⟩ := by
    rw [d8, d7, hData6, v8, hQ, hTreeMem (treeBase + 7 * dense.length + (d.val + 1)) (by exit_arith)
      (by unfold staticTreeWords <;> exit_arith)]
    have hCm := S.childStart_mem (d.val + 1) d.isLt
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hCm
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t9, hs9, pc9, r9_13, p9, d9⟩ :=
    step_loadData16 (hPl.at 8 (by exit_rom_bound) (by exit_arith)) hLoad8 (by rw [pc8] <;> exit_arith)
  have v9_13 : (reg t9 r13).val = S.childStart (d.val + 1) := by rw [r9_13]
  have v9_12 : (reg t9 r12).val = S.childStart d.val := by
    rw [p9 r12 (by decide), p8 r12 (by decide), v7_12]
  have hCSMono : S.childStart d.val ≤ S.childStart (d.val + 1) :=
    S.childStart_mono d.val (d.val + 1) (Nat.le_succ _) d.isLt
  obtain ⟨t10, hs10, pc10, r10_11, p10, d10⟩ := step_sub16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have hSliceLen : (S.childSlice d).length = S.childStart (d.val + 1) - S.childStart d.val := by
    simp [StaticTreeSlice.childSlice]
  have v10_11 : (reg t10 r11).val = (S.childSlice d).length := by
    rw [r10_11, sub_exact (by rw [v9_12, v9_13]; exact hCSMono), v9_13, v9_12, hSliceLen]
  have v10_1 : (reg t10 r1).val = 1 := by
    rw [p10 r1 (by decide), p9 r1 (by decide), p8 r1 (by decide), v7_1]
  have hNdLt : 1 + (S.childSlice d).length < 2 ^ bits := by
    have hM := S.childStart_mono (d.val + 1) dense.length d.isLt (Nat.le_refl _)
    have hE := S.childStart_end <;> exit_arith
  obtain ⟨t11, hs11, pc11, r11_11, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_11 : (reg t11 r11).val = 1 + (S.childSlice d).length := by
    rw [r11_11, add_no_wrap _ _ (by rw [v10_11, v10_1] <;> exit_arith), v10_11, v10_1] <;> exit_arith
  obtain ⟨t12, hs12, pc12, r12_12, p12, d12⟩ := step_imm16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12_11 : (reg t12 r11).val = 1 + (S.childSlice d).length := by rw [p12 r11 (by decide), v11_11]
  have v12_12 : (reg t12 r12).val = 3 := by rw [r12_12] <;> rfl
  have hBrFetch := hPl.at 12 (by exit_rom_bound) (pc := t12.pc) (by exit_arith)
  have hKeep12 : ∀ r : Fin 16, r.val ≤ 10 → reg t12 r = reg s₀ r := by
    intro r hr
    rw [p12 r (by exit_arith), p11 r (by exit_arith), p10 r (by exit_arith), p9 r (by exit_arith),
      p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith),
      p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have hData12 : t12.data = s₀.data := by rw [d12, d11, d10, d9, d8, d7, hData6]
  dsimp only
  by_cases hSmall : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hSmall]
    have hTrue : WordOps.ltb (reg t12 r11) (reg t12 r12) = true :=
      branchLt_true (by rw [v12_11, v12_12]; exact hSmall)
    have hBr := PaperB.RamProgram.step_branchLt_at (code := code) (input := input) hBrFetch
      (by rw [hTrue, ite_eq_left rfl]; simp only [offSmall, offLargeA] at hFit ⊢ <;> exit_arith)
    rw [hTrue, ite_eq_left rfl] at hBr
    let t13 : State L16 := { t12 with pc := offSmall }
    refine ⟨t13, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (step1 hBr)))))))))))),
      rfl, hData12, exitLoopRegs_of_keep hRegs hKeep12, v12_11⟩
  · rw [ite_eq_right hSmall]
    have hFalse : WordOps.ltb (reg t12 r11) (reg t12 r12) = false :=
      branchLt_false (by rw [v12_11, v12_12] <;> exit_arith)
    have hBr := PaperB.RamProgram.step_branchLt_at (code := code) (input := input) hBrFetch
      (by rw [hFalse, ite_eq_right (by decide)]; exact hFit)
    rw [hFalse, ite_eq_right (by decide)] at hBr
    let t13 : State L16 := { t12 with pc := offLargeA }
    refine ⟨t13, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (step1 hBr)))))))))))),
      rfl, hData12, exitLoopRegs_of_keep hRegs hKeep12, v12_11⟩

/-! #### Block 2: `exitSmall` (`61..75`, `15` steps) -/

theorem exitSmall_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitSmallCode h100) offSmall)
    (hFit : offSmall + 15 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offSmall) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hd : d < Q) (hQn : Q ≤ n)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt11 : (s₀.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m))
    (hEnd : exitArenaBase loopBase n m ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 15 s₀ s1 ∧
      s1.pc = offHdr ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase (d + 1) exitUsed s1 ∧
      (∀ k < 3, (s1.data[exitPtrsBase loopBase n m + 3 * d + k]?).map Fin.val = some 0) ∧
      (∀ addr, (addr < exitPtrsBase loopBase n m + 3 * d ∨
          exitPtrsBase loopBase n m + 3 * d + 3 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  have hEPFit : exitPtrsBase loopBase n m + 3 * d + 3 ≤ workCap := by
    unfold exitArenaBase at hEnd <;> exit_arith
  have hEPBnd : exitPtrsBase loopBase n m + 3 * d + 2 < 2 ^ bits := by exit_arith
  have hStFit : exitSubStateBase loopBase n m + 11 < 2 ^ bits := by
    obtain ⟨w11, hw11, _⟩ := Option.map_eq_some_iff.mp hSt11
    have hLt := (Array.getElem?_eq_some_iff.mp hw11).1
    rw [hSz] at hLt
    exact Nat.lt_trans hLt hBits
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have hLoad1 : t1.data[(reg t1 r11).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d1, show (reg t1 r11).val = statePtrAddr by rw [r1_11] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_11, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_11 : (reg t2 r11).val = exitSubStateBase loopBase n m := by rw [r2_11]
  obtain ⟨t3, hs3, pc3, r3_12, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_11 : (reg t3 r11).val = exitSubStateBase loopBase n m := by rw [p3 r11 (by decide), v2_11]
  have v3_12 : (reg t3 r12).val = 11 := by rw [r3_12] <;> rfl
  obtain ⟨t4, hs4, pc4, r4_11, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_11 : (reg t4 r11).val = exitSubStateBase loopBase n m + 11 := by
    rw [r4_11, add_no_wrap _ _ (by rw [v3_11, v3_12]; exact hStFit), v3_11, v3_12]
  have hLoad4 : t4.data[(reg t4 r11).val]? = some ⟨exitPtrsBase loopBase n m, by exit_arith⟩ := by
    rw [d4, d3, d2, d1, v4_11]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt11
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t5, hs5, pc5, r5_11, p5, d5⟩ := step_loadData16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) hLoad4 (by rw [pc4] <;> exit_arith)
  have v5_11 : (reg t5 r11).val = exitPtrsBase loopBase n m := by rw [r5_11]
  have hKeep5 : ∀ r : Fin 16, r.val ≤ 10 → reg t5 r = reg s₀ r := by
    intro r hr
    rw [p5 r (by exit_arith), p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have v5_9 : (reg t5 r9).val = d := by rw [hKeep5 r9 (by decide), hRegs.dVal]
  have hData5 : t5.data = s₀.data := by rw [d5, d4, d3, d2, d1]
  obtain ⟨t6, hs6, pc6, r6_12, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_12 : (reg t6 r12).val = 2 * d := by
    rw [r6_12, add_no_wrap _ _ (by rw [v5_9] <;> exit_arith), v5_9] <;> exit_arith
  have v6_9 : (reg t6 r9).val = d := by rw [p6 r9 (by decide), v5_9]
  have v6_11 : (reg t6 r11).val = exitPtrsBase loopBase n m := by rw [p6 r11 (by decide), v5_11]
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = 3 * d := by
    rw [r7_12, add_no_wrap _ _ (by rw [v6_12, v6_9] <;> exit_arith), v6_12, v6_9] <;> exit_arith
  have v7_11 : (reg t7 r11).val = exitPtrsBase loopBase n m := by rw [p7 r11 (by decide), v6_11]
  obtain ⟨t8, hs8, pc8, r8_11, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_11 : (reg t8 r11).val = exitPtrsBase loopBase n m + 3 * d := by
    rw [r8_11, add_no_wrap _ _ (by rw [v7_11, v7_12] <;> exit_arith), v7_11, v7_12]
  have hKeep8 : ∀ r : Fin 16, r.val ≤ 10 → reg t8 r = reg s₀ r := by
    intro r hr; rw [p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith)]; exact hKeep5 r hr
  have b8 : (reg t8 r11).val < t8.data.size := by rw [d8, d7, d6, hData5, hSz, v8_11] <;> exit_arith
  obtain ⟨t9, hs9, pc9, rg9, d9⟩ := step_storeData16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith) b8
  have v9_11 : (reg t9 r11).val = exitPtrsBase loopBase n m + 3 * d := by
    rw [reg_eq_of_regs_eq rg9 r11, v8_11]
  have v9_1 : (reg t9 r1).val = 1 := by
    rw [reg_eq_of_regs_eq rg9 r1, hKeep8 r1 (by decide), hRegs.entry.consts.one]
  obtain ⟨t10, hs10, pc10, r10_11, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10_11 : (reg t10 r11).val = exitPtrsBase loopBase n m + 3 * d + 1 := by
    rw [r10_11, add_no_wrap _ _ (by rw [v9_11, v9_1] <;> exit_arith), v9_11, v9_1]
  have b10 : (reg t10 r11).val < t10.data.size := by
    rw [d10, d9, Array.size_set, d8, d7, d6, hData5, hSz, v10_11] <;> exit_arith
  obtain ⟨t11, hs11, pc11, rg11, d11⟩ := step_storeData16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith) b10
  have v11_11 : (reg t11 r11).val = exitPtrsBase loopBase n m + 3 * d + 1 := by
    rw [reg_eq_of_regs_eq rg11 r11, v10_11]
  have v11_1 : (reg t11 r1).val = 1 := by
    rw [reg_eq_of_regs_eq rg11 r1, p10 r1 (by decide), v9_1]
  obtain ⟨t12, hs12, pc12, r12_11, p12, d12⟩ := step_add16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12_11 : (reg t12 r11).val = exitPtrsBase loopBase n m + 3 * d + 2 := by
    rw [r12_11, add_no_wrap _ _ (by rw [v11_11, v11_1] <;> exit_arith), v11_11, v11_1] <;> exit_arith
  have b12 : (reg t12 r11).val < t12.data.size := by
    rw [d12, d11, Array.size_set, d10, d9, Array.size_set, d8, d7, d6, hData5, hSz, v12_11] <;> exit_arith
  obtain ⟨t13, hs13, pc13, rg13, d13⟩ := step_storeData16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith) b12
  have hKeep13 : ∀ r : Fin 16, r.val ≤ 10 → reg t13 r = reg s₀ r := by
    intro r hr
    rw [reg_eq_of_regs_eq rg13 r, p12 r (by exit_arith), reg_eq_of_regs_eq rg11 r,
      p10 r (by exit_arith), reg_eq_of_regs_eq rg9 r]
    exact hKeep8 r hr
  have v13_9 : (reg t13 r9).val = d := by rw [hKeep13 r9 (by decide), hRegs.dVal]
  have v13_1 : (reg t13 r1).val = 1 := by rw [hKeep13 r1 (by decide), hRegs.entry.consts.one]
  obtain ⟨t14, hs14, pc14, r14_9, p14, d14⟩ := step_add16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13] <;> exit_arith)
  have v14_9 : (reg t14 r9).val = d + 1 := by
    rw [r14_9, add_no_wrap _ _ (by rw [v13_9, v13_1] <;> exit_arith), v13_9, v13_1]
  have hGo := PaperB.RamProgram.step_goto_at (code := code) (input := input) (s := t14)
    (target := offHdr) (hPl.at 14 (by exit_rom_bound) (by rw [pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7,
      pc6, pc5, pc4, pc3, pc2, pc1, hPC])) (by simp only [offHdr, offSmall] at hFit ⊢ <;> exit_arith)
  let t15 : State L16 := { t14 with pc := offHdr }
  have hSteps : Steps code input 15 s₀ t15 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (step1 hGo))))))))))))))
  have hSz15 : t15.data.size = workCap := by
    change t14.data.size = workCap
    rw [d14, d13, Array.size_set, d12, d11, Array.size_set,
      d10, d9, Array.size_set, d8, d7, d6, hData5, hSz]
  have hKeep15 : ∀ r : Fin 16, r.val ≤ 10 → r ≠ r9 → reg t15 r = reg s₀ r := by
    intro r hr hNe9
    change reg t14 r = reg s₀ r
    rw [p14 r hNe9]; exact hKeep13 r hr
  have hExitRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase (d + 1) exitUsed t15 :=
    { entry :=
        { consts :=
            { zero := (congrArg Fin.val (hKeep15 rZero (by decide) (by decide))).trans hRegs.entry.consts.zero
              one := (congrArg Fin.val (hKeep15 rOne (by decide) (by decide))).trans hRegs.entry.consts.one
              nVal := (congrArg Fin.val (hKeep15 rN (by decide) (by decide))).trans hRegs.entry.consts.nVal
              mVal := (congrArg Fin.val (hKeep15 rM (by decide) (by decide))).trans hRegs.entry.consts.mVal
              rootVal := (congrArg Fin.val (hKeep15 rRoot (by decide) (by decide))).trans hRegs.entry.consts.rootVal }
          qVal := (congrArg Fin.val (hKeep15 r5 (by decide) (by decide))).trans hRegs.entry.qVal
          treeBaseVal := (congrArg Fin.val (hKeep15 r6 (by decide) (by decide))).trans hRegs.entry.treeBaseVal
          emitBaseVal := (congrArg Fin.val (hKeep15 r7 (by decide) (by decide))).trans hRegs.entry.emitBaseVal
          loopBaseVal := (congrArg Fin.val (hKeep15 r8 (by decide) (by decide))).trans hRegs.entry.loopBaseVal }
      dVal := v14_9
      usedVal := (congrArg Fin.val (hKeep15 r10 (by decide) (by decide))).trans hRegs.usedVal }
  have hz8 : (reg t8 r0).val = 0 := by rw [hKeep8 r0 (by decide), hRegs.entry.consts.zero]
  have hz10 : (reg t10 r0).val = 0 := by
    rw [p10 r0 (by decide), reg_eq_of_regs_eq rg9 r0, hKeep8 r0 (by decide), hRegs.entry.consts.zero]
  have hz12 : (reg t12 r0).val = 0 := by
    rw [p12 r0 (by decide), reg_eq_of_regs_eq rg11 r0, p10 r0 (by decide), reg_eq_of_regs_eq rg9 r0,
      hKeep8 r0 (by decide), hRegs.entry.consts.zero]
  have hLast (j : Nat) (h : (reg t12 r11).val ≠ j) :
      t15.data[j]? = t11.data[j]? := by
    change t14.data[j]? = _
    rw [d14, d13, Array.getElem?_set_ne _ h, d12]
  have hMid (j : Nat) (h : (reg t10 r11).val ≠ j) :
      t11.data[j]? = t9.data[j]? := by
    rw [d11, Array.getElem?_set_ne _ h, d10]
  have hFirst (j : Nat) (h : (reg t8 r11).val ≠ j) :
      t9.data[j]? = s₀.data[j]? := by
    rw [d9, Array.getElem?_set_ne _ h, d8, d7, d6, hData5]
  have hWr : ∀ k < 3, (t15.data[exitPtrsBase loopBase n m + 3 * d + k]?).map Fin.val = some 0 := by
    intro k hk
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with rfl | rfl | rfl
    · rw [hLast _ (by rw [v12_11]; omega), hMid _ (by rw [v10_11]; omega),
        d9, show exitPtrsBase loopBase n m + 3 * d + 0 = (reg t8 r11).val by rw [v8_11] <;> omega,
        Array.getElem?_set_self, Option.map_some, hz8]
    · rw [hLast _ (by rw [v12_11]; omega),
        d11, show exitPtrsBase loopBase n m + 3 * d + 1 = (reg t10 r11).val by rw [v10_11],
        Array.getElem?_set_self, Option.map_some, hz10]
    · change (t14.data[_]?).map Fin.val = some 0
      rw [d14, d13, show exitPtrsBase loopBase n m + 3 * d + 2 = (reg t12 r11).val by rw [v12_11],
        Array.getElem?_set_self, Option.map_some, hz12]
  have hFr : ∀ addr, (addr < exitPtrsBase loopBase n m + 3 * d ∨
        exitPtrsBase loopBase n m + 3 * d + 3 ≤ addr) →
      t15.data[addr]? = s₀.data[addr]? := by
    intro addr ha
    rw [hLast _ (by rw [v12_11]; omega), hMid _ (by rw [v10_11]; omega),
      hFirst _ (by rw [v8_11]; omega)]
  exact ⟨t15, hSteps, rfl, hSz15, hExitRegs, hWr, hFr⟩


end SmallStepHelpers

end PaperB.RamExitFamilyLoop
