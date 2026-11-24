module

public import PaperB.RamExitFamilyHeaders
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
        r11, r12, r13, r14, r15, r7, r8, r9, r10, w100, inPtrAddr, dataPtrAddr, statePtrAddr] at *; omega))

/-! #### Block 3: `exitLargeA` (`76..94`, `19` steps) and `exitLargeB` (`95..122`, `28` steps) -/

private theorem exitPostSetup1_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitPostSetupCode h100) (offPostSetup subLen))
    (hFit : offPostSetup subLen + 15 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offPostSetup subLen) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hd : d < Q) (hQn : Q ≤ n)
    (hMem0 : (s₀.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt11 : (s₀.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m))
    (hSt12 : (s₀.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m))
    (hArenaBnd : exitArenaBase loopBase n m + exitUsed ≤ workCap)
    (hEnd : exitArenaBase loopBase n m ≤ workCap)
    (hSubInFit : exitSubInBase loopBase n m + 3 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 15 s₀ s1 ∧
      s1.pc = offPostSetup subLen + 15 ∧
      s1.data = s₀.data ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r11).val = exitPtrsBase loopBase n m + 3 * d ∧
      (reg s1 r12).val = exitArenaBase loopBase n m + exitUsed ∧
      (reg s1 r15).val = exitSubInBase loopBase n m + 2 := by
  have hStFit : exitSubStateBase loopBase n m + 12 < 2 ^ bits := by
    obtain ⟨w12, hw12, _⟩ := Option.map_eq_some_iff.mp hSt12
    have hLt := (Array.getElem?_eq_some_iff.mp hw12).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have hLoad1 : t1.data[(reg t1 r11).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d1, show (reg t1 r11).val = statePtrAddr by rw [r1_11] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_14, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_14 : (reg t2 r14).val = exitSubStateBase loopBase n m := by rw [r2_14]
  obtain ⟨t3, hs3, pc3, r3_11, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_14 : (reg t3 r14).val = exitSubStateBase loopBase n m := by rw [p3 r14 (by decide), v2_14]
  have v3_11 : (reg t3 r11).val = 11 := by rw [r3_11] <;> rfl
  obtain ⟨t4, hs4, pc4, r4_11, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_11 : (reg t4 r11).val = exitSubStateBase loopBase n m + 11 := by
    rw [r4_11, add_no_wrap _ _ (by rw [v3_14, v3_11] <;> exit_arith), v3_14, v3_11]
  have hLoad4 : t4.data[(reg t4 r11).val]? = some ⟨exitPtrsBase loopBase n m, by
      unfold exitArenaBase at hEnd <;> exit_arith⟩ := by
    rw [d4, d3, d2, d1, v4_11]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt11; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t5, hs5, pc5, r5_11, p5, d5⟩ := step_loadData16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) hLoad4 (by rw [pc4] <;> exit_arith)
  have v5_11 : (reg t5 r11).val = exitPtrsBase loopBase n m := by rw [r5_11]
  have hIdxFit : 3 * Q ≤ workCap := by
    unfold exitArenaBase at hEnd
    omega
  have v5_9 : (reg t5 r9).val = d := by
    rw [p5 r9 (by decide), p4 r9 (by decide), p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide), hRegs.dVal]
  obtain ⟨t6, hs6, pc6, r6_13, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_13 : (reg t6 r13).val = 2 * d := by
    rw [r6_13, add_no_wrap _ _ (by rw [v5_9] <;> exit_arith), v5_9] <;> exit_arith
  have v6_9 : (reg t6 r9).val = d := by rw [p6 r9 (by decide), v5_9]
  have v6_11 : (reg t6 r11).val = exitPtrsBase loopBase n m := by rw [p6 r11 (by decide), v5_11]
  obtain ⟨t7, hs7, pc7, r7_13, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_13 : (reg t7 r13).val = 3 * d := by
    rw [r7_13, add_no_wrap _ _ (by rw [v6_13, v6_9] <;> exit_arith), v6_13, v6_9] <;> exit_arith
  have v7_11 : (reg t7 r11).val = exitPtrsBase loopBase n m := by rw [p7 r11 (by decide), v6_11]
  obtain ⟨t8, hs8, pc8, r8_11, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_11 : (reg t8 r11).val = exitPtrsBase loopBase n m + 3 * d := by
    rw [r8_11, add_no_wrap _ _ (by rw [v7_11, v7_13]; unfold exitArenaBase at hEnd <;> exit_arith), v7_11, v7_13]
  have v8_14 : (reg t8 r14).val = exitSubStateBase loopBase n m := by
    rw [p8 r14 (by decide), p7 r14 (by decide), p6 r14 (by decide), p5 r14 (by decide),
      p4 r14 (by decide), p3 r14 (by decide), v2_14]
  obtain ⟨t9, hs9, pc9, r9_12, p9, d9⟩ := step_imm16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_14 : (reg t9 r14).val = exitSubStateBase loopBase n m := by rw [p9 r14 (by decide), v8_14]
  have v9_12 : (reg t9 r12).val = 12 := by rw [r9_12] <;> rfl
  obtain ⟨t10, hs10, pc10, r10_12, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = exitSubStateBase loopBase n m + 12 := by
    rw [r10_12, add_no_wrap _ _ (by rw [v9_14, v9_12] <;> exit_arith), v9_14, v9_12]
  have hLoad10 : t10.data[(reg t10 r12).val]? = some ⟨exitArenaBase loopBase n m, by exit_arith⟩ := by
    rw [d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, v10_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt12; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t11, hs11, pc11, r11_12, p11, d11⟩ := step_loadData16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) hLoad10 (by rw [pc10] <;> exit_arith)
  have v11_12 : (reg t11 r12).val = exitArenaBase loopBase n m := by rw [r11_12]
  have hKeep11 : ∀ r : Fin 16, r.val ≤ 10 → reg t11 r = reg s₀ r := by
    intro r hr
    rw [p11 r (by exit_arith), p10 r (by exit_arith), p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith),
      p6 r (by exit_arith), p5 r (by exit_arith), p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have v11_10 : (reg t11 r10).val = exitUsed := by rw [hKeep11 r10 (by decide), hRegs.usedVal]
  obtain ⟨t12, hs12, pc12, r12_12, p12, d12⟩ := step_add16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12_12 : (reg t12 r12).val = exitArenaBase loopBase n m + exitUsed := by
    rw [r12_12, add_no_wrap _ _ (by rw [v11_12, v11_10] <;> exit_arith), v11_12, v11_10]
  have v12_0 : (reg t12 r0).val = 0 := by rw [p12 r0 (by decide), hKeep11 r0 (by decide), hRegs.entry.consts.zero]
  have hLoad12 : t12.data[(reg t12 r0).val]? = some ⟨exitSubInBase loopBase n m, by exit_arith⟩ := by
    rw [d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, v12_0]; change s₀.data[inPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem0; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t13, hs13, pc13, r13_13, p13, d13⟩ := step_loadData16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) hLoad12 (by rw [pc12] <;> exit_arith)
  have v13_13 : (reg t13 r13).val = exitSubInBase loopBase n m := by rw [r13_13]
  obtain ⟨t14, hs14, pc14, r14_15, p14, d14⟩ := step_imm16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13] <;> exit_arith)
  have v14_13 : (reg t14 r13).val = exitSubInBase loopBase n m := by rw [p14 r13 (by decide), v13_13]
  have v14_15 : (reg t14 r15).val = 2 := by rw [r14_15] <;> rfl
  obtain ⟨t15, hs15, pc15, r15_15, p15, d15⟩ := step_add16 (input := input) (s := t14) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc14] <;> exit_arith)
  have v15_15 : (reg t15 r15).val = exitSubInBase loopBase n m + 2 := by
    rw [r15_15, add_no_wrap _ _ (by rw [v14_13, v14_15] <;> exit_arith), v14_13, v14_15]
  have hKeep15 : ∀ r : Fin 16, r.val ≤ 10 → reg t15 r = reg s₀ r := by
    intro r hr
    rw [p15 r (by exit_arith), p14 r (by exit_arith), p13 r (by exit_arith), p12 r (by exit_arith), hKeep11 r hr]
  have v15_11 : (reg t15 r11).val = exitPtrsBase loopBase n m + 3 * d := by
    rw [p15 r11 (by decide), p14 r11 (by decide), p13 r11 (by decide), p12 r11 (by decide),
      p11 r11 (by decide), p10 r11 (by decide), p9 r11 (by decide), v8_11]
  have v15_12 : (reg t15 r12).val = exitArenaBase loopBase n m + exitUsed := by
    rw [p15 r12 (by decide), p14 r12 (by decide), p13 r12 (by decide), v12_12]
  have hSteps : Steps code input 15 s₀ t15 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (step1 hs15))))))))))))))
  have hPC15 : t15.pc = offPostSetup subLen + 15 := by
    rw [pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hData15 : t15.data = s₀.data := by
    rw [d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  exact ⟨t15, hSteps, hPC15, hData15, exitLoopRegs_of_keep hRegs hKeep15, v15_11, v15_12, v15_15⟩

private theorem exitPostSetup2_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitPostSetupCode h100) (offPostSetup subLen))
    (hFit : offPostSetup subLen + 30 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed N_d : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offPostSetup subLen + 15) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr11 : (reg s₀ r11).val = exitPtrsBase loopBase n m + 3 * d)
    (hr12 : (reg s₀ r12).val = exitArenaBase loopBase n m + exitUsed)
    (hr15 : (reg s₀ r15).val = exitSubInBase loopBase n m + 2)
    (hd : d < Q) (hQn : Q ≤ n)
    (hMem0 : (s₀.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hIn2 : (s₀.data[exitSubInBase loopBase n m + 2]?).map Fin.val = some N_d)
    (hEndEP : exitPtrsBase loopBase n m + 3 * Q ≤ exitArenaBase loopBase n m)
    (hArenaBnd : exitArenaBase loopBase n m + exitUsed + 19 * N_d ≤ workCap) (hBits : workCap < 2 ^ bits) :
    let ep0 := exitArenaBase loopBase n m + exitUsed
    ∃ s1 : State L16,
      Steps code input 15 s₀ s1 ∧
      s1.pc = offPostSetup subLen + 30 ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r13).val = 19 * N_d ∧
      (reg s1 r14).val = exitSubInBase loopBase n m ∧
      (reg s1 r15).val = N_d ∧
      (s1.data[exitPtrsBase loopBase n m + 3 * d]?).map Fin.val = some ep0 ∧
      (s1.data[exitPtrsBase loopBase n m + 3 * d + 1]?).map Fin.val = some (ep0 + N_d) ∧
      (s1.data[exitPtrsBase loopBase n m + 3 * d + 2]?).map Fin.val = some (ep0 + 19 * N_d) ∧
      (∀ addr, (addr < exitPtrsBase loopBase n m + 3 * d ∨
          exitPtrsBase loopBase n m + 3 * d + 3 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  intro ep0
  have h19Lt : 19 * N_d < 2 ^ bits := by exit_arith
  have hInLt : exitSubInBase loopBase n m < 2 ^ bits := by
    obtain ⟨w0, hw0, _⟩ := Option.map_eq_some_iff.mp hMem0
    have hLt := (Array.getElem?_eq_some_iff.mp hw0).1; rw [hSz] at hLt <;> exit_arith
  have hNe0 : ∀ k, exitPtrsBase loopBase n m + 3 * d + k ≠ inPtrAddr := by
    intro k; unfold inPtrAddr exitPtrsBase loopWorkWords <;> exit_arith
  have hEPFit : exitPtrsBase loopBase n m + 3 * d + 3 ≤ workCap := by exit_arith
  have hLoad0 : s₀.data[(reg s₀ r15).val]? = some ⟨N_d, by exit_arith⟩ := by
    rw [hr15]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hIn2; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t1, hs1, pc1, r1_15, p1, d1⟩ := step_loadData16 (input := input) (s := s₀) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) hLoad0 (by rw [hPC] <;> exit_arith)
  have v1_15 : (reg t1 r15).val = N_d := by rw [r1_15]
  have v1_11 : (reg t1 r11).val = exitPtrsBase loopBase n m + 3 * d := by rw [p1 r11 (by decide), hr11]
  have v1_12 : (reg t1 r12).val = ep0 := by rw [p1 r12 (by decide), hr12]
  have b1 : (reg t1 r11).val < t1.data.size := by rw [d1, hSz, v1_11] <;> exit_arith
  obtain ⟨t2, hs2, pc2, rg2, d2⟩ := step_storeData16 (input := input) (s := t1) (hPl.at 16 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith) b1
  have v2_11 : (reg t2 r11).val = exitPtrsBase loopBase n m + 3 * d := by rw [reg_eq_of_regs_eq rg2 r11, v1_11]
  have v2_1 : (reg t2 r1).val = 1 := by
    rw [reg_eq_of_regs_eq rg2 r1, p1 r1 (by decide), hRegs.entry.consts.one]
  obtain ⟨t3, hs3, pc3, r3_11, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 17 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_11 : (reg t3 r11).val = exitPtrsBase loopBase n m + 3 * d + 1 := by
    rw [r3_11, add_no_wrap _ _ (by rw [v2_11, v2_1] <;> exit_arith), v2_11, v2_1]
  have v3_12 : (reg t3 r12).val = ep0 := by rw [p3 r12 (by decide), reg_eq_of_regs_eq rg2 r12, v1_12]
  have v3_15 : (reg t3 r15).val = N_d := by rw [p3 r15 (by decide), reg_eq_of_regs_eq rg2 r15, v1_15]
  obtain ⟨t4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 18 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_12 : (reg t4 r12).val = ep0 + N_d := by
    rw [r4_12, add_no_wrap _ _ (by rw [v3_12, v3_15] <;> exit_arith), v3_12, v3_15]
  have v4_11 : (reg t4 r11).val = exitPtrsBase loopBase n m + 3 * d + 1 := by rw [p4 r11 (by decide), v3_11]
  have b4 : (reg t4 r11).val < t4.data.size := by rw [d4, d3, d2, Array.size_set, d1, hSz, v4_11] <;> exit_arith
  obtain ⟨t5, hs5, pc5, rg5, d5⟩ := step_storeData16 (input := input) (s := t4) (hPl.at 19 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith) b4
  have v5_11 : (reg t5 r11).val = exitPtrsBase loopBase n m + 3 * d + 1 := by rw [reg_eq_of_regs_eq rg5 r11, v4_11]
  have v5_1 : (reg t5 r1).val = 1 := by rw [reg_eq_of_regs_eq rg5 r1, p4 r1 (by decide), p3 r1 (by decide), v2_1]
  obtain ⟨t6, hs6, pc6, r6_11, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 20 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_11 : (reg t6 r11).val = exitPtrsBase loopBase n m + 3 * d + 2 := by
    rw [r6_11, add_no_wrap _ _ (by rw [v5_11, v5_1] <;> exit_arith), v5_11, v5_1] <;> exit_arith
  have v6_15 : (reg t6 r15).val = N_d := by
    rw [p6 r15 (by decide), reg_eq_of_regs_eq rg5 r15, p4 r15 (by decide), v3_15]
  obtain ⟨t7, hs7, pc7, r7_13, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 21 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_13 : (reg t7 r13).val = 2 * N_d := by
    rw [r7_13, add_no_wrap _ _ (by rw [v6_15] <;> exit_arith), v6_15] <;> exit_arith
  obtain ⟨t8, hs8, pc8, r8_14, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 22 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_14 : (reg t8 r14).val = 4 * N_d := by
    rw [r8_14, add_no_wrap _ _ (by rw [v7_13] <;> exit_arith), v7_13] <;> exit_arith
  obtain ⟨t9, hs9, pc9, r9_14, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 23 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_14 : (reg t9 r14).val = 8 * N_d := by
    rw [r9_14, add_no_wrap _ _ (by rw [v8_14] <;> exit_arith), v8_14] <;> exit_arith
  obtain ⟨t10, hs10, pc10, r10_14, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 24 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10_14 : (reg t10 r14).val = 16 * N_d := by
    rw [r10_14, add_no_wrap _ _ (by rw [v9_14] <;> exit_arith), v9_14] <;> exit_arith
  have v10_13 : (reg t10 r13).val = 2 * N_d := by
    rw [p10 r13 (by decide), p9 r13 (by decide), p8 r13 (by decide), v7_13]
  obtain ⟨t11, hs11, pc11, r11_13, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 25 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_13 : (reg t11 r13).val = 18 * N_d := by
    rw [r11_13, add_no_wrap _ _ (by rw [v10_13, v10_14] <;> exit_arith), v10_13, v10_14] <;> exit_arith
  have v11_12 : (reg t11 r12).val = ep0 + N_d := by
    rw [p11 r12 (by decide), p10 r12 (by decide), p9 r12 (by decide), p8 r12 (by decide),
      p7 r12 (by decide), p6 r12 (by decide), reg_eq_of_regs_eq rg5 r12, v4_12]
  obtain ⟨t12, hs12, pc12, r12_12, p12, d12⟩ := step_add16 (input := input) (s := t11) (hPl.at 26 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12_12 : (reg t12 r12).val = ep0 + 19 * N_d := by
    rw [r12_12, add_no_wrap _ _ (by rw [v11_12, v11_13] <;> exit_arith), v11_12, v11_13] <;> exit_arith
  have v12_11 : (reg t12 r11).val = exitPtrsBase loopBase n m + 3 * d + 2 := by
    rw [p12 r11 (by decide), p11 r11 (by decide), p10 r11 (by decide), p9 r11 (by decide),
      p8 r11 (by decide), p7 r11 (by decide), v6_11]
  have b12 : (reg t12 r11).val < t12.data.size := by
    rw [d12, d11, d10, d9, d8, d7, d6, d5, Array.size_set, d4, d3, d2, Array.size_set, d1, hSz, v12_11] <;> exit_arith
  obtain ⟨t13, hs13, pc13, rg13, d13⟩ := step_storeData16 (input := input) (s := t12) (hPl.at 27 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith) b12
  have v13_13 : (reg t13 r13).val = 18 * N_d := by
    rw [reg_eq_of_regs_eq rg13 r13, p12 r13 (by decide), v11_13]
  have v13_15 : (reg t13 r15).val = N_d := by
    rw [reg_eq_of_regs_eq rg13 r15, p12 r15 (by decide), p11 r15 (by decide), p10 r15 (by decide),
      p9 r15 (by decide), p8 r15 (by decide), p7 r15 (by decide), v6_15]
  obtain ⟨t14, hs14, pc14, r14_13, p14, d14⟩ := step_add16 (input := input) (s := t13) (hPl.at 28 (by exit_rom_bound) (by exit_arith)) (by rw [pc13] <;> exit_arith)
  have v14_13 : (reg t14 r13).val = 19 * N_d := by
    rw [r14_13, add_no_wrap _ _ (by rw [v13_13, v13_15] <;> exit_arith), v13_13, v13_15] <;> exit_arith
  have hKeep14 : ∀ r : Fin 16, r.val ≤ 10 → reg t14 r = reg s₀ r := by
    intro r hr
    rw [p14 r (by exit_arith), reg_eq_of_regs_eq rg13 r, p12 r (by exit_arith), p11 r (by exit_arith),
      p10 r (by exit_arith), p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith),
      reg_eq_of_regs_eq rg5 r, p4 r (by exit_arith), p3 r (by exit_arith), reg_eq_of_regs_eq rg2 r, p1 r (by exit_arith)]
  have v14_0 : (reg t14 r0).val = 0 := by rw [hKeep14 r0 (by decide), hRegs.entry.consts.zero]
  have hLoad14 : t14.data[(reg t14 r0).val]? = some ⟨exitSubInBase loopBase n m, by exit_arith⟩ := by
    rw [v14_0, d14, d13, Array.getElem?_set_ne _ (by rw [v12_11]; exact hNe0 2),
      d12, d11, d10, d9, d8, d7, d6, d5,
      Array.getElem?_set_ne _ (by rw [v4_11]; exact hNe0 1), d4, d3, d2,
      Array.getElem?_set_ne _ (by rw [v1_11]; exact hNe0 0), d1]
    change s₀.data[inPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem0; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t15, hs15, pc15, r15_14, p15, d15⟩ := step_loadData16 (input := input) (s := t14) (hPl.at 29 (by exit_rom_bound) (by exit_arith)) hLoad14 (by rw [pc14] <;> exit_arith)
  have hSteps : Steps code input 15 s₀ t15 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (step1 hs15))))))))))))))
  have hPC15 : t15.pc = offPostSetup subLen + 30 := by
    rw [pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith
  have hSz15 : t15.data.size = workCap := by
    rw [d15, d14, d13, Array.size_set, d12, d11, d10, d9, d8, d7, d6, d5, Array.size_set,
      d4, d3, d2, Array.size_set, d1, hSz]
  have hKeep15 : ∀ r : Fin 16, r.val ≤ 10 → reg t15 r = reg s₀ r := by
    intro r hr; rw [p15 r (by exit_arith), hKeep14 r hr]
  have v15_13 : (reg t15 r13).val = 19 * N_d := by rw [p15 r13 (by decide), v14_13]
  have v15_14 : (reg t15 r14).val = exitSubInBase loopBase n m := by rw [r15_14]
  have v15_15 : (reg t15 r15).val = N_d := by rw [p15 r15 (by decide), p14 r15 (by decide), v13_15]
  have hEP0 : (t15.data[exitPtrsBase loopBase n m + 3 * d]?).map Fin.val = some ep0 := by
    rw [d15, d14, d13, Array.getElem?_set_ne _ (by rw [v12_11] <;> exit_arith), d12, d11, d10, d9, d8, d7, d6, d5,
      Array.getElem?_set_ne _ (by rw [v4_11] <;> exit_arith), d4, d3, d2,
      show exitPtrsBase loopBase n m + 3 * d = (reg t1 r11).val from v1_11.symm,
      Array.getElem?_set_self, Option.map_some, v1_12]
  have hEP1 : (t15.data[exitPtrsBase loopBase n m + 3 * d + 1]?).map Fin.val = some (ep0 + N_d) := by
    rw [d15, d14, d13, Array.getElem?_set_ne _ (by rw [v12_11] <;> exit_arith), d12, d11, d10, d9, d8, d7, d6, d5,
      show exitPtrsBase loopBase n m + 3 * d + 1 = (reg t4 r11).val from v4_11.symm,
      Array.getElem?_set_self, Option.map_some, v4_12]
  have hEP2 : (t15.data[exitPtrsBase loopBase n m + 3 * d + 2]?).map Fin.val = some (ep0 + 19 * N_d) := by
    rw [d15, d14, d13, show exitPtrsBase loopBase n m + 3 * d + 2 = (reg t12 r11).val from v12_11.symm,
      Array.getElem?_set_self, Option.map_some, v12_12]
  have hFr15 : ∀ addr, (addr < exitPtrsBase loopBase n m + 3 * d ∨
        exitPtrsBase loopBase n m + 3 * d + 3 ≤ addr) →
      t15.data[addr]? = s₀.data[addr]? := by
    intro addr ha
    rw [d15, d14, d13, Array.getElem?_set_ne _ (by rw [v12_11] <;> exit_arith), d12, d11, d10, d9, d8, d7, d6, d5,
      Array.getElem?_set_ne _ (by rw [v4_11] <;> exit_arith), d4, d3, d2,
      Array.getElem?_set_ne _ (by rw [v1_11] <;> exit_arith), d1]
  exact ⟨t15, hSteps, hPC15, hSz15, exitLoopRegs_of_keep hRegs hKeep15,
    v15_13, v15_14, v15_15, hEP0, hEP1, hEP2, hFr15⟩

private theorem exitPostSetup3_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitPostSetupCode h100) (offPostSetup subLen))
    (hFit : offPostCopy subLen < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed N_d n_d : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offPostSetup subLen + 30) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr13 : (reg s₀ r13).val = 19 * N_d)
    (hr14 : (reg s₀ r14).val = exitSubInBase loopBase n m)
    (hMem1 : (s₀.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt12 : (s₀.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m))
    (hIn0 : (s₀.data[exitSubInBase loopBase n m]?).map Fin.val = some n_d)
    (hSubWorkEnd : exitSubWorkBase loopBase n m workCap + (19 * N_d + 6 * n_d) ≤ workCap)
    (hArenaBnd : exitArenaBase loopBase n m + exitUsed + (19 * N_d + 6 * n_d) ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 13 s₀ s1 ∧
      s1.pc = offPostCopy subLen ∧
      s1.data = s₀.data ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r11).val = exitSubWorkBase loopBase n m workCap ∧
      (reg s1 r12).val = exitArenaBase loopBase n m + exitUsed ∧
      (reg s1 r13).val = exitSubWorkBase loopBase n m workCap + (19 * N_d + 6 * n_d) ∧
      (reg s1 r15).val = 19 * N_d + 6 * n_d := by
  have hLenLt : 19 * N_d + 6 * n_d < 2 ^ bits := by exit_arith
  have hStFit : exitSubStateBase loopBase n m + 12 < 2 ^ bits := by
    obtain ⟨w12, hw12, _⟩ := Option.map_eq_some_iff.mp hSt12
    have hLt := (Array.getElem?_eq_some_iff.mp hw12).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  have hLoad0 : s₀.data[(reg s₀ r14).val]? = some ⟨n_d, by exit_arith⟩ := by
    rw [hr14]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hIn0; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t1, hs1, pc1, r1_14, p1, d1⟩ := step_loadData16 (input := input) (s := s₀) (hPl.at 30 (by exit_rom_bound) (by exit_arith)) hLoad0 (by rw [hPC] <;> exit_arith)
  have v1_14 : (reg t1 r14).val = n_d := by rw [r1_14]
  obtain ⟨t2, hs2, pc2, r2_15, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 31 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2_15 : (reg t2 r15).val = 2 * n_d := by
    rw [r2_15, add_no_wrap _ _ (by rw [v1_14] <;> exit_arith), v1_14] <;> exit_arith
  obtain ⟨t3, hs3, pc3, r3_14, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 32 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_14 : (reg t3 r14).val = 4 * n_d := by
    rw [r3_14, add_no_wrap _ _ (by rw [v2_15] <;> exit_arith), v2_15] <;> exit_arith
  have v3_15 : (reg t3 r15).val = 2 * n_d := by rw [p3 r15 (by decide), v2_15]
  obtain ⟨t4, hs4, pc4, r4_14, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 33 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_14 : (reg t4 r14).val = 6 * n_d := by
    rw [r4_14, add_no_wrap _ _ (by rw [v3_14, v3_15] <;> exit_arith), v3_14, v3_15] <;> exit_arith
  have v4_13 : (reg t4 r13).val = 19 * N_d := by
    rw [p4 r13 (by decide), p3 r13 (by decide), p2 r13 (by decide), p1 r13 (by decide), hr13]
  obtain ⟨t5, hs5, pc5, r5_15, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 34 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5_15 : (reg t5 r15).val = 19 * N_d + 6 * n_d := by
    rw [r5_15, add_no_wrap _ _ (by rw [v4_13, v4_14] <;> exit_arith), v4_13, v4_14]
  obtain ⟨t6, hs6, pc6, r6_12, p6, d6⟩ := step_imm16 (input := input) (s := t5) (hPl.at 35 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have hLoad6 : t6.data[(reg t6 r12).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d6, d5, d4, d3, d2, d1, show (reg t6 r12).val = statePtrAddr by rw [r6_12] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_loadData16 (input := input) (s := t6) (hPl.at 36 (by exit_rom_bound) (by exit_arith)) hLoad6 (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = exitSubStateBase loopBase n m := by rw [r7_12]
  obtain ⟨t8, hs8, pc8, r8_13, p8, d8⟩ := step_imm16 (input := input) (s := t7) (hPl.at 37 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = exitSubStateBase loopBase n m := by rw [p8 r12 (by decide), v7_12]
  have v8_13 : (reg t8 r13).val = 12 := by rw [r8_13] <;> rfl
  obtain ⟨t9, hs9, pc9, r9_12, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 38 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_12 : (reg t9 r12).val = exitSubStateBase loopBase n m + 12 := by
    rw [r9_12, add_no_wrap _ _ (by rw [v8_12, v8_13] <;> exit_arith), v8_12, v8_13]
  have hLoad9 : t9.data[(reg t9 r12).val]? = some ⟨exitArenaBase loopBase n m, by exit_arith⟩ := by
    rw [d9, d8, d7, d6, d5, d4, d3, d2, d1, v9_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt12; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t10, hs10, pc10, r10_12, p10, d10⟩ := step_loadData16 (input := input) (s := t9) (hPl.at 39 (by exit_rom_bound) (by exit_arith)) hLoad9 (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = exitArenaBase loopBase n m := by rw [r10_12]
  have hKeep10 : ∀ r : Fin 16, r.val ≤ 10 → reg t10 r = reg s₀ r := by
    intro r hr
    rw [p10 r (by exit_arith), p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith),
      p5 r (by exit_arith), p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have v10_10 : (reg t10 r10).val = exitUsed := by rw [hKeep10 r10 (by decide), hRegs.usedVal]
  obtain ⟨t11, hs11, pc11, r11_12, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 40 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_12 : (reg t11 r12).val = exitArenaBase loopBase n m + exitUsed := by
    rw [r11_12, add_no_wrap _ _ (by rw [v10_12, v10_10] <;> exit_arith), v10_12, v10_10]
  have v11_1 : (reg t11 r1).val = 1 := by
    rw [p11 r1 (by decide), hKeep10 r1 (by decide), hRegs.entry.consts.one]
  have hLoad11 : t11.data[(reg t11 r1).val]? = some ⟨exitSubWorkBase loopBase n m workCap, by exit_arith⟩ := by
    rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, v11_1]; change s₀.data[dataPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem1; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t12, hs12, pc12, r12_11, p12, d12⟩ := step_loadData16 (input := input) (s := t11) (hPl.at 41 (by exit_rom_bound) (by exit_arith)) hLoad11 (by rw [pc11] <;> exit_arith)
  have v12_11 : (reg t12 r11).val = exitSubWorkBase loopBase n m workCap := by rw [r12_11]
  have v12_15 : (reg t12 r15).val = 19 * N_d + 6 * n_d := by
    rw [p12 r15 (by decide), p11 r15 (by decide), p10 r15 (by decide), p9 r15 (by decide),
      p8 r15 (by decide), p7 r15 (by decide), p6 r15 (by decide), v5_15]
  obtain ⟨t13, hs13, pc13, r13_13, p13, d13⟩ := step_add16 (input := input) (s := t12) (hPl.at 42 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith)
  have hSteps : Steps code input 13 s₀ t13 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (step1 hs13))))))))))))
  have hPC13 : t13.pc = offPostCopy subLen := by
    rw [pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]
    simp only [offPostSetup, offPostCopy] <;> exit_arith
  have hData13 : t13.data = s₀.data := by
    rw [d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hKeep13 : ∀ r : Fin 16, r.val ≤ 10 → reg t13 r = reg s₀ r := by
    intro r hr; rw [p13 r (by exit_arith), p12 r (by exit_arith), p11 r (by exit_arith), hKeep10 r hr]
  have v13_11 : (reg t13 r11).val = exitSubWorkBase loopBase n m workCap := by
    rw [p13 r11 (by decide), v12_11]
  have v13_12 : (reg t13 r12).val = exitArenaBase loopBase n m + exitUsed := by
    rw [p13 r12 (by decide), p12 r12 (by decide), v11_12]
  have v13_13 : (reg t13 r13).val = exitSubWorkBase loopBase n m workCap + (19 * N_d + 6 * n_d) := by
    rw [r13_13, add_no_wrap _ _ (by rw [v12_11, v12_15] <;> exit_arith), v12_11, v12_15]
  have v13_15 : (reg t13 r15).val = 19 * N_d + 6 * n_d := by
    rw [p13 r15 (by decide), v12_15]
  exact ⟨t13, hSteps, hPC13, hData13, exitLoopRegs_of_keep hRegs hKeep13,
    v13_11, v13_12, v13_13, v13_15⟩

theorem exitPostSetup_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitPostSetupCode h100) (offPostSetup subLen))
    (hFit : offPostCopy subLen < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed N_d n_d : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offPostSetup subLen) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hd : d < Q) (hQn : Q ≤ n)
    (hMem0 : (s₀.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hMem1 : (s₀.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt11 : (s₀.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m))
    (hSt12 : (s₀.data[exitSubStateBase loopBase n m + 12]?).map Fin.val = some (exitArenaBase loopBase n m))
    (hIn0 : (s₀.data[exitSubInBase loopBase n m]?).map Fin.val = some n_d)
    (hIn2 : (s₀.data[exitSubInBase loopBase n m + 2]?).map Fin.val = some N_d)
    (hEndEP : exitPtrsBase loopBase n m + 3 * Q ≤ exitArenaBase loopBase n m)
    (hArenaBnd : exitArenaBase loopBase n m + exitUsed + (19 * N_d + 6 * n_d) ≤ workCap)
    (hSubWorkEnd : exitSubWorkBase loopBase n m workCap + (19 * N_d + 6 * n_d) ≤ workCap)
    (hSubInFit : exitSubInBase loopBase n m + 3 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    let ep0 := exitArenaBase loopBase n m + exitUsed
    ∃ s1 : State L16,
      Steps code input 43 s₀ s1 ∧
      s1.pc = offPostCopy subLen ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r11).val = exitSubWorkBase loopBase n m workCap ∧
      (reg s1 r12).val = ep0 ∧
      (reg s1 r13).val = exitSubWorkBase loopBase n m workCap + (19 * N_d + 6 * n_d) ∧
      (reg s1 r15).val = 19 * N_d + 6 * n_d ∧
      (s1.data[exitPtrsBase loopBase n m + 3 * d]?).map Fin.val = some ep0 ∧
      (s1.data[exitPtrsBase loopBase n m + 3 * d + 1]?).map Fin.val = some (ep0 + N_d) ∧
      (s1.data[exitPtrsBase loopBase n m + 3 * d + 2]?).map Fin.val = some (ep0 + 19 * N_d) ∧
      (∀ addr, (addr < exitPtrsBase loopBase n m + 3 * d ∨
          exitPtrsBase loopBase n m + 3 * d + 3 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  intro ep0
  obtain ⟨s1, hs1, pc1, hd1, regs1, r1_11, r1_12, r1_15⟩ :=
    exitPostSetup1_steps h100 hPl (by simp only [offPostSetup, offPostCopy] at hFit ⊢ <;> exit_arith)
      hPC hSz hRegs hd hQn hMem0 hSt2 hSt11 hSt12 (by exit_arith) (by exit_arith) hSubInFit hBits
  have hSz1 : s1.data.size = workCap := by rw [hd1, hSz]
  obtain ⟨s2, hs2, pc2, sz2, regs2, r2_13, r2_14, _, hep0, hep1, hep2, hfr2⟩ :=
    exitPostSetup2_steps h100 hPl (by simp only [offPostSetup, offPostCopy] at hFit ⊢ <;> exit_arith)
      pc1 hSz1 regs1 r1_11 r1_12 r1_15 hd hQn (by rw [hd1]; exact hMem0) (by rw [hd1]; exact hIn2)
      hEndEP (by exit_arith) hBits
  have hNe0 : ∀ k, exitPtrsBase loopBase n m + 3 * d + k ≠ dataPtrAddr := by
    intro k; unfold dataPtrAddr exitPtrsBase loopWorkWords <;> exit_arith
  have hNe2 : ∀ k, exitPtrsBase loopBase n m + 3 * d + k ≠ statePtrAddr := by
    intro k; unfold statePtrAddr exitPtrsBase loopWorkWords <;> exit_arith
  have hFrMem1 : s2.data[dataPtrAddr]? = s₀.data[dataPtrAddr]? := by
    rw [hfr2 _ (Or.inl (by unfold dataPtrAddr exitPtrsBase loopWorkWords <;> exit_arith)), hd1]
  have hFrSt2 : s2.data[statePtrAddr]? = s₀.data[statePtrAddr]? := by
    rw [hfr2 _ (Or.inl (by unfold statePtrAddr exitPtrsBase loopWorkWords <;> exit_arith)), hd1]
  have hFrSt12 : s2.data[exitSubStateBase loopBase n m + 12]? = s₀.data[exitSubStateBase loopBase n m + 12]? := by
    rw [hfr2 _ (Or.inr (by unfold exitSubStateBase <;> exit_arith)), hd1]
  have hFrIn0 : s2.data[exitSubInBase loopBase n m]? = s₀.data[exitSubInBase loopBase n m]? := by
    rw [hfr2 _ (Or.inr (by unfold exitSubInBase exitSubStateBase <;> exit_arith)), hd1]
  obtain ⟨s3, hs3, pc3, hd3, regs3, r3_11, r3_12, r3_13, r3_15⟩ :=
    exitPostSetup3_steps h100 hPl hFit pc2 sz2 regs2 r2_13 r2_14
      (by rw [hFrMem1]; exact hMem1) (by rw [hFrSt2]; exact hSt2)
      (by rw [hFrSt12]; exact hSt12) (by rw [hFrIn0]; exact hIn0)
      hSubWorkEnd hArenaBnd hBits
  refine ⟨s3, hs1.append (hs2.append hs3), pc3, by rw [hd3, sz2], regs3,
    r3_11, r3_12, r3_13, r3_15, by rw [hd3]; exact hep0, by rw [hd3]; exact hep1, by rw [hd3]; exact hep2,
    fun addr ha => by rw [hd3, hfr2 addr ha, hd1]⟩

theorem exitPostCopyAndStep_steps {code : Program L16} {input : Input L16}
    {subLen : Nat}
    (hPlCopy : SlicePlaced (hi := hi) (hw := hw) code
      (copyLoopCode (hi := hi) (hw := hw) (offPostCopy subLen) (offPostStep subLen))
      (offPostCopy subLen))
    (hPlStep : SlicePlaced (hi := hi) (hw := hw) code
      (exitPostStepCode (bits := bits)) (offPostStep subLen))
    (hFit : offPostStep subLen + 3 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed totalLen : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offPostCopy subLen) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr11 : (reg s₀ r11).val = exitSubWorkBase loopBase n m workCap)
    (hr12 : (reg s₀ r12).val = exitArenaBase loopBase n m + exitUsed)
    (hr13 : (reg s₀ r13).val = exitSubWorkBase loopBase n m workCap + totalLen)
    (hr15 : (reg s₀ r15).val = totalLen)
    (hd : d < Q) (hQn : Q ≤ n)
    (hArenaEnd : exitArenaBase loopBase n m + exitUsed + totalLen ≤ exitSubStateBase loopBase n m)
    (hSubWorkEnd : exitSubWorkBase loopBase n m workCap + totalLen ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    let ep0 := exitArenaBase loopBase n m + exitUsed
    ∃ s1 : State L16,
      Steps code input (6 * totalLen + 4) s₀ s1 ∧
      s1.pc = offHdr ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase (d + 1) (exitUsed + totalLen) s1 ∧
      (∀ k < totalLen, s1.data[ep0 + k]? = s₀.data[exitSubWorkBase loopBase n m workCap + k]?) ∧
      (∀ addr, (addr < ep0 ∨ ep0 + totalLen ≤ addr) → s1.data[addr]? = s₀.data[addr]?) := by
  intro ep0
  have hSafe : ep0 + totalLen ≤ exitSubWorkBase loopBase n m workCap := by
    unfold exitSubWorkBase exitSubInBase at * <;> exit_arith
  obtain ⟨t1, kC, hkC, hs1, pc1, sz1, _, _, _, p1, hCp1, hFr1⟩ :=
    run_copyLoop16 hPlCopy (by simp only [offPostStep] at hFit ⊢ <;> exit_arith)
      (by simp only [offPostCopy, offPostStep] at hFit ⊢ <;> exit_arith) hBits
      hSubWorkEnd (by unfold exitSubWorkBase exitSubInBase at hSubWorkEnd <;> exit_arith)
      (Or.inl hSafe) hPC hSz hRegs.entry.consts.one hr11 hr12 hr13
  have hKeep1 : ∀ r : Fin 16, r.val ≤ 10 → reg t1 r = reg s₀ r := by
    intro r hr; exact p1 r (by exit_arith) (by exit_arith) (by exit_arith)
  have hR15_1 : (reg t1 r15).val = totalLen := by rw [p1 r15 (by decide) (by decide) (by decide), hr15]
  have hR10_1 : (reg t1 r10).val = exitUsed := by rw [hKeep1 r10 (by decide), hRegs.usedVal]
  have hUsedBnd : exitUsed + totalLen < 2 ^ bits := by exit_arith
  obtain ⟨t2, hs2, pc2, r2_10, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPlStep.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2_10 : (reg t2 r10).val = exitUsed + totalLen := by
    rw [r2_10, add_no_wrap _ _ (by rw [hR10_1, hR15_1]; exact hUsedBnd), hR10_1, hR15_1]
  have v2_9 : (reg t2 r9).val = d := by rw [p2 r9 (by decide), hKeep1 r9 (by decide), hRegs.dVal]
  have v2_1 : (reg t2 r1).val = 1 := by rw [p2 r1 (by decide), hKeep1 r1 (by decide), hRegs.entry.consts.one]
  have hDBnd : d + 1 < 2 ^ bits := by
    have : Q ≤ workCap := by unfold exitSubWorkBase exitSubInBase exitSubStateBase exitArenaBase exitPtrsBase loopWorkWords at hSubWorkEnd <;> exit_arith
    exit_arith
  obtain ⟨t3, hs3, pc3, r3_9, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPlStep.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_9 : (reg t3 r9).val = d + 1 := by
    rw [r3_9, add_no_wrap _ _ (by rw [v2_9, v2_1]; exact hDBnd), v2_9, v2_1]
  have hGo := PaperB.RamProgram.step_goto_at (code := code) (input := input) (s := t3)
    (target := offHdr) (hPlStep.at 2 (by exit_rom_bound) (by exit_arith)) (by simp only [offHdr, offPostStep] at hFit ⊢ <;> exit_arith)
  let t4 : State L16 := { t3 with pc := offHdr }
  have hSteps : Steps code input (6 * totalLen + 4) s₀ t4 := by
    have hAll := hs1.append (Steps.cons hs2 (Steps.cons hs3 (step1 hGo)))
    rwa [hkC, show 6 * totalLen + 1 + 3 = 6 * totalLen + 4 by exit_arith] at hAll
  have hKeepLow : ∀ r : Fin 16, r.val ≤ 8 → reg t4 r = reg s₀ r := by
    intro r hr; change reg t3 r = reg s₀ r
    rw [p3 r (by exit_arith), p2 r (by exit_arith), hKeep1 r (by exit_arith)]
  have hRegs4 : ExitLoopRegs n m root Q treeBase emitBase loopBase (d + 1) (exitUsed + totalLen) t4 :=
    { entry :=
        { consts :=
            { zero := (congrArg Fin.val (hKeepLow rZero (by decide))).trans hRegs.entry.consts.zero
              one := (congrArg Fin.val (hKeepLow rOne (by decide))).trans hRegs.entry.consts.one
              nVal := (congrArg Fin.val (hKeepLow rN (by decide))).trans hRegs.entry.consts.nVal
              mVal := (congrArg Fin.val (hKeepLow rM (by decide))).trans hRegs.entry.consts.mVal
              rootVal := (congrArg Fin.val (hKeepLow rRoot (by decide))).trans hRegs.entry.consts.rootVal }
          qVal := (congrArg Fin.val (hKeepLow r5 (by decide))).trans hRegs.entry.qVal
          treeBaseVal := (congrArg Fin.val (hKeepLow r6 (by decide))).trans hRegs.entry.treeBaseVal
          emitBaseVal := (congrArg Fin.val (hKeepLow r7 (by decide))).trans hRegs.entry.emitBaseVal
          loopBaseVal := (congrArg Fin.val (hKeepLow r8 (by decide))).trans hRegs.entry.loopBaseVal }
      dVal := v3_9
      usedVal := by change (reg t3 r10).val = _; rw [p3 r10 (by decide), v2_10] }
  have hDataEq : t4.data = t1.data := by change t3.data = t1.data; rw [d3, d2]
  exact ⟨t4, hSteps, rfl, by rw [hDataEq, sz1], hRegs4,
    fun k hk => by rw [hDataEq, hCp1 k hk],
    fun a ha => by rw [hDataEq, hFr1 a ha]⟩

theorem exitFinish_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitFinishCode h100) (offFinish subLen))
    (hFit : offFinish subLen + 16 < code.size)
    {n m root Q treeBase emitBase loopBase exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offFinish subLen) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase Q exitUsed s₀)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt11 : (s₀.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m))
    (hEnd : exitPtrsBase loopBase n m ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 16 s₀ s1 ∧
      s1.pc = offFinish subLen + 16 ∧
      s1.data = s₀.data ∧
      SealedPackEntryRegs n m root Q treeBase (ownerForestPtrsBase loopBase n m)
        (exitPtrsBase loopBase n m) (5 * n) s1 := by
  have hL : exitPtrsBase loopBase n m < 2 ^ bits := Nat.lt_of_le_of_lt hEnd hBits
  have h44 : 44 * n < 2 ^ bits := by
    have := ownerForestPtrsBase_add_44n loopBase n m <;> exit_arith
  have hStFit : exitSubStateBase loopBase n m + 11 < 2 ^ bits := by
    obtain ⟨w11, hw11, _⟩ := Option.map_eq_some_iff.mp hSt11
    have hLt := (Array.getElem?_eq_some_iff.mp hw11).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have hLoad1 : t1.data[(reg t1 r11).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d1, show (reg t1 r11).val = statePtrAddr by rw [r1_11] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_11, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_11 : (reg t2 r11).val = exitSubStateBase loopBase n m := by rw [r2_11]
  obtain ⟨t3, hs3, pc3, r3_12, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_11 : (reg t3 r11).val = exitSubStateBase loopBase n m := by rw [p3 r11 (by decide), v2_11]
  have v3_12 : (reg t3 r12).val = 11 := by rw [r3_12] <;> rfl
  obtain ⟨t4, hs4, pc4, r4_11, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_11 : (reg t4 r11).val = exitSubStateBase loopBase n m + 11 := by
    rw [r4_11, add_no_wrap _ _ (by rw [v3_11, v3_12]; exact hStFit), v3_11, v3_12]
  have hLoad4 : t4.data[(reg t4 r11).val]? = some ⟨exitPtrsBase loopBase n m, hL⟩ := by
    rw [d4, d3, d2, d1, v4_11]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt11; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t5, hs5, pc5, r5_8, p5, d5⟩ := step_loadData16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) hLoad4 (by rw [pc4] <;> exit_arith)
  have v5_8 : (reg t5 r8).val = exitPtrsBase loopBase n m := by rw [r5_8]
  have v5_2 : (reg t5 r2).val = n := by
    rw [p5 r2 (by decide), p4 r2 (by decide), p3 r2 (by decide), p2 r2 (by decide),
      p1 r2 (by decide), hRegs.entry.consts.nVal]
  obtain ⟨t6, hs6, pc6, r6_11, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_11 : (reg t6 r11).val = 2 * n := by
    rw [r6_11, add_no_wrap _ _ (by rw [v5_2] <;> exit_arith), v5_2] <;> exit_arith
  obtain ⟨t7, hs7, pc7, r7_11, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_11 : (reg t7 r11).val = 4 * n := by
    rw [r7_11, add_no_wrap _ _ (by rw [v6_11] <;> exit_arith), v6_11] <;> exit_arith
  obtain ⟨t8, hs8, pc8, r8_12, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = 8 * n := by
    rw [r8_12, add_no_wrap _ _ (by rw [v7_11] <;> exit_arith), v7_11] <;> exit_arith
  have v8_11 : (reg t8 r11).val = 4 * n := by rw [p8 r11 (by decide), v7_11]
  obtain ⟨t9, hs9, pc9, r9_11, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_11 : (reg t9 r11).val = 12 * n := by
    rw [r9_11, add_no_wrap _ _ (by rw [v8_11, v8_12] <;> exit_arith), v8_11, v8_12] <;> exit_arith
  have v9_12 : (reg t9 r12).val = 8 * n := by rw [p9 r12 (by decide), v8_12]
  obtain ⟨t10, hs10, pc10, r10_12, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = 16 * n := by
    rw [r10_12, add_no_wrap _ _ (by rw [v9_12] <;> exit_arith), v9_12] <;> exit_arith
  obtain ⟨t11, hs11, pc11, r11_12, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_12 : (reg t11 r12).val = 32 * n := by
    rw [r11_12, add_no_wrap _ _ (by rw [v10_12] <;> exit_arith), v10_12] <;> exit_arith
  have v11_11 : (reg t11 r11).val = 12 * n := by rw [p11 r11 (by decide), p10 r11 (by decide), v9_11]
  obtain ⟨t12, hs12, pc12, r12_11, p12, d12⟩ := step_add16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12_11 : (reg t12 r11).val = 44 * n := by
    rw [r12_11, add_no_wrap _ _ (by rw [v11_11, v11_12] <;> exit_arith), v11_11, v11_12] <;> exit_arith
  have v12_8 : (reg t12 r8).val = exitPtrsBase loopBase n m := by
    rw [p12 r8 (by decide), p11 r8 (by decide), p10 r8 (by decide), p9 r8 (by decide),
      p8 r8 (by decide), p7 r8 (by decide), p6 r8 (by decide), v5_8]
  obtain ⟨t13, hs13, pc13, r13_7, p13, d13⟩ := step_sub16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith)
  have v13_7 : (reg t13 r7).val = ownerForestPtrsBase loopBase n m := by
    have hSub : 44 * n ≤ exitPtrsBase loopBase n m := by
      rw [← ownerForestPtrsBase_add_44n loopBase n m] <;> exit_arith
    rw [r13_7, sub_exact (by rw [v12_11, v12_8]; exact hSub), v12_8, v12_11,
      ← ownerForestPtrsBase_add_44n loopBase n m] <;> exit_arith
  have v13_2 : (reg t13 r2).val = n := by
    rw [p13 r2 (by decide), p12 r2 (by decide), p11 r2 (by decide), p10 r2 (by decide),
      p9 r2 (by decide), p8 r2 (by decide), p7 r2 (by decide), p6 r2 (by decide), v5_2]
  obtain ⟨t14, hs14, pc14, r14_11, p14, d14⟩ := step_add16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13] <;> exit_arith)
  have v14_11 : (reg t14 r11).val = 2 * n := by
    rw [r14_11, add_no_wrap _ _ (by rw [v13_2] <;> exit_arith), v13_2] <;> exit_arith
  obtain ⟨t15, hs15, pc15, r15_11, p15, d15⟩ := step_add16 (input := input) (s := t14) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc14] <;> exit_arith)
  have v15_11 : (reg t15 r11).val = 4 * n := by
    rw [r15_11, add_no_wrap _ _ (by rw [v14_11] <;> exit_arith), v14_11] <;> exit_arith
  have v15_2 : (reg t15 r2).val = n := by rw [p15 r2 (by decide), p14 r2 (by decide), v13_2]
  obtain ⟨t16, hs16, pc16, r16_9, p16, d16⟩ := step_add16 (input := input) (s := t15) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) (by rw [pc15] <;> exit_arith)
  have v16_9 : (reg t16 r9).val = 5 * n := by
    rw [r16_9, add_no_wrap _ _ (by rw [v15_11, v15_2] <;> exit_arith), v15_11, v15_2] <;> exit_arith
  have hSteps : Steps code input 16 s₀ t16 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14
          (Steps.cons hs15 (step1 hs16)))))))))))))))
  have hPC16 : t16.pc = offFinish subLen + 16 := by
    rw [pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hData16 : t16.data = s₀.data := by
    rw [d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hKeep6 : ∀ r : Fin 16, r.val ≤ 6 → reg t16 r = reg s₀ r := by
    intro r hr
    rw [p16 r (by exit_arith), p15 r (by exit_arith), p14 r (by exit_arith), p13 r (by exit_arith),
      p12 r (by exit_arith), p11 r (by exit_arith), p10 r (by exit_arith), p9 r (by exit_arith),
      p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith),
      p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have v16_7 : (reg t16 r7).val = ownerForestPtrsBase loopBase n m := by
    rw [p16 r7 (by decide), p15 r7 (by decide), p14 r7 (by decide), v13_7]
  have v16_8 : (reg t16 r8).val = exitPtrsBase loopBase n m := by
    rw [p16 r8 (by decide), p15 r8 (by decide), p14 r8 (by decide), p13 r8 (by decide), v12_8]
  have hSealed : SealedPackEntryRegs n m root Q treeBase (ownerForestPtrsBase loopBase n m)
      (exitPtrsBase loopBase n m) (5 * n) t16 :=
    { consts :=
        { zero := (congrArg Fin.val (hKeep6 rZero (by decide))).trans hRegs.entry.consts.zero
          one := (congrArg Fin.val (hKeep6 rOne (by decide))).trans hRegs.entry.consts.one
          nVal := (congrArg Fin.val (hKeep6 rN (by decide))).trans hRegs.entry.consts.nVal
          mVal := (congrArg Fin.val (hKeep6 rM (by decide))).trans hRegs.entry.consts.mVal
          rootVal := (congrArg Fin.val (hKeep6 rRoot (by decide))).trans hRegs.entry.consts.rootVal }
      qVal := (congrArg Fin.val (hKeep6 r5 (by decide))).trans hRegs.entry.qVal
      treeBaseVal := (congrArg Fin.val (hKeep6 r6 (by decide))).trans hRegs.entry.treeBaseVal
      forestPtrsVal := v16_7
      exitPtrsVal := v16_8
      sealedBaseVal := v16_9 }
  exact ⟨t16, hSteps, hPC16, hData16, hSealed⟩

end SmallStepHelpers

end PaperB.RamExitFamilyLoop
