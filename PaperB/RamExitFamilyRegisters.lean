module

public import PaperB.RamExitFamilyInit
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
set_option maxHeartbeats 1500000

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
        r11, r12, r13, r14, r15, r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, w100, inPtrAddr, dataPtrAddr, statePtrAddr] at *; omega))

/-! #### Block 3: `exitLargeA` (`76..94`, `19` steps) and `exitLargeB` (`95..122`, `28` steps) -/

private theorem exitSaveRegs1_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitSaveRegsCode h100) offSave)
    (hFit : offSave + 11 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offSave) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hStFit : exitSubStateBase loopBase n m + 11 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 11 s₀ s1 ∧
      s1.pc = offSave + 11 ∧
      s1.data.size = workCap ∧
      (∀ r : Fin 16, r.val ≤ 10 → reg s1 r = reg s₀ r) ∧
      (reg s1 r12).val = exitSubStateBase loopBase n m + 4 ∧
      (∀ (k : Nat) (hk : k < 5), s1.data[exitSubStateBase loopBase n m + k]? =
        some (reg s₀ ⟨k, (Nat.lt_trans hk (by decide : 5 < 16))⟩)) ∧
      (∀ addr, (addr < exitSubStateBase loopBase n m ∨ exitSubStateBase loopBase n m + 5 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  have hOne : (reg s₀ r1).val = 1 := hRegs.entry.consts.one
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have hLoad1 : t1.data[(reg t1 r11).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d1, show (reg t1 r11).val = statePtrAddr by rw [r1_11] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_12, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_12 : (reg t2 r12).val = exitSubStateBase loopBase n m := by rw [r2_12]
  have b2 : (reg t2 r12).val < t2.data.size := by rw [d2, d1, hSz, v2_12] <;> exit_arith
  obtain ⟨t3, hs3, pc3, rg3, d3⟩ := step_storeData16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith) b2
  have v3_12 : (reg t3 r12).val = exitSubStateBase loopBase n m := by rw [reg_eq_of_regs_eq rg3 r12, v2_12]
  have v3_1 : (reg t3 r1).val = 1 := by rw [reg_eq_of_regs_eq rg3 r1, p2 r1 (by decide), p1 r1 (by decide), hOne]
  obtain ⟨t4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_12 : (reg t4 r12).val = exitSubStateBase loopBase n m + 1 := by
    rw [r4_12, add_no_wrap _ _ (by rw [v3_12, v3_1] <;> exit_arith), v3_12, v3_1]
  have b4 : (reg t4 r12).val < t4.data.size := by rw [d4, d3, Array.size_set, d2, d1, hSz, v4_12] <;> exit_arith
  obtain ⟨t5, hs5, pc5, rg5, d5⟩ := step_storeData16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith) b4
  have v5_12 : (reg t5 r12).val = exitSubStateBase loopBase n m + 1 := by rw [reg_eq_of_regs_eq rg5 r12, v4_12]
  have v5_1 : (reg t5 r1).val = 1 := by rw [reg_eq_of_regs_eq rg5 r1, p4 r1 (by decide), v3_1]
  obtain ⟨t6, hs6, pc6, r6_12, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_12 : (reg t6 r12).val = exitSubStateBase loopBase n m + 2 := by
    rw [r6_12, add_no_wrap _ _ (by rw [v5_12, v5_1] <;> exit_arith), v5_12, v5_1] <;> exit_arith
  have b6 : (reg t6 r12).val < t6.data.size := by
    rw [d6, d5, Array.size_set, d4, d3, Array.size_set, d2, d1, hSz, v6_12] <;> exit_arith
  obtain ⟨t7, hs7, pc7, rg7, d7⟩ := step_storeData16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith) b6
  have v7_12 : (reg t7 r12).val = exitSubStateBase loopBase n m + 2 := by rw [reg_eq_of_regs_eq rg7 r12, v6_12]
  have v7_1 : (reg t7 r1).val = 1 := by rw [reg_eq_of_regs_eq rg7 r1, p6 r1 (by decide), v5_1]
  obtain ⟨t8, hs8, pc8, r8_12, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = exitSubStateBase loopBase n m + 3 := by
    rw [r8_12, add_no_wrap _ _ (by rw [v7_12, v7_1] <;> exit_arith), v7_12, v7_1] <;> exit_arith
  have b8 : (reg t8 r12).val < t8.data.size := by
    rw [d8, d7, Array.size_set, d6, d5, Array.size_set, d4, d3, Array.size_set, d2, d1, hSz, v8_12] <;> exit_arith
  obtain ⟨t9, hs9, pc9, rg9, d9⟩ := step_storeData16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith) b8
  have v9_12 : (reg t9 r12).val = exitSubStateBase loopBase n m + 3 := by rw [reg_eq_of_regs_eq rg9 r12, v8_12]
  have v9_1 : (reg t9 r1).val = 1 := by rw [reg_eq_of_regs_eq rg9 r1, p8 r1 (by decide), v7_1]
  obtain ⟨t10, hs10, pc10, r10_12, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = exitSubStateBase loopBase n m + 4 := by
    rw [r10_12, add_no_wrap _ _ (by rw [v9_12, v9_1] <;> exit_arith), v9_12, v9_1] <;> exit_arith
  have b10 : (reg t10 r12).val < t10.data.size := by
    rw [d10, d9, Array.size_set, d8, d7, Array.size_set, d6, d5, Array.size_set,
      d4, d3, Array.size_set, d2, d1, hSz, v10_12] <;> exit_arith
  obtain ⟨t11, hs11, pc11, rg11, d11⟩ := step_storeData16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith) b10
  have hSteps : Steps code input 11 s₀ t11 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (step1 hs11))))))))))
  have hPC11 : t11.pc = offSave + 11 := by
    rw [pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hSz11 : t11.data.size = workCap := by
    rw [d11, Array.size_set, d10, d9, Array.size_set, d8, d7, Array.size_set,
      d6, d5, Array.size_set, d4, d3, Array.size_set, d2, d1, hSz]
  have hKeep11 : ∀ r : Fin 16, r.val ≤ 10 → reg t11 r = reg s₀ r := by
    intro r hr
    rw [reg_eq_of_regs_eq rg11 r, p10 r (by exit_arith), reg_eq_of_regs_eq rg9 r,
      p8 r (by exit_arith), reg_eq_of_regs_eq rg7 r, p6 r (by exit_arith), reg_eq_of_regs_eq rg5 r,
      p4 r (by exit_arith), reg_eq_of_regs_eq rg3 r, p2 r (by exit_arith), p1 r (by exit_arith)]
  have v11_12 : (reg t11 r12).val = exitSubStateBase loopBase n m + 4 := by
    rw [reg_eq_of_regs_eq rg11 r12, v10_12]
  have hk0 : reg t2 r0 = reg s₀ r0 := by rw [p2 r0 (by decide), p1 r0 (by decide)]
  have hk1 : reg t4 r1 = reg s₀ r1 := by
    rw [p4 r1 (by decide), reg_eq_of_regs_eq rg3 r1, p2 r1 (by decide), p1 r1 (by decide)]
  have hk2 : reg t6 r2 = reg s₀ r2 := by
    rw [p6 r2 (by decide), reg_eq_of_regs_eq rg5 r2, p4 r2 (by decide), reg_eq_of_regs_eq rg3 r2,
      p2 r2 (by decide), p1 r2 (by decide)]
  have hk3 : reg t8 r3 = reg s₀ r3 := by
    rw [p8 r3 (by decide), reg_eq_of_regs_eq rg7 r3, p6 r3 (by decide), reg_eq_of_regs_eq rg5 r3,
      p4 r3 (by decide), reg_eq_of_regs_eq rg3 r3, p2 r3 (by decide), p1 r3 (by decide)]
  have hk4 : reg t10 r4 = reg s₀ r4 := by
    rw [p10 r4 (by decide), reg_eq_of_regs_eq rg9 r4, p8 r4 (by decide), reg_eq_of_regs_eq rg7 r4,
      p6 r4 (by decide), reg_eq_of_regs_eq rg5 r4, p4 r4 (by decide), reg_eq_of_regs_eq rg3 r4,
      p2 r4 (by decide), p1 r4 (by decide)]
  have hWr : ∀ (k : Nat) (hk : k < 5), t11.data[exitSubStateBase loopBase n m + k]? =
      some (reg s₀ ⟨k, (Nat.lt_trans hk (by decide : 5 < 16))⟩) := by
    intro k hk
    have hc : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by exit_arith
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [d11, Array.getElem?_set_ne _ (by rw [v10_12] <;> exit_arith), d10, d9,
        Array.getElem?_set_ne _ (by rw [v8_12] <;> exit_arith), d8, d7,
        Array.getElem?_set_ne _ (by rw [v6_12] <;> exit_arith), d6, d5,
        Array.getElem?_set_ne _ (by rw [v4_12] <;> exit_arith), d4, d3,
        show exitSubStateBase loopBase n m + 0 = (reg t2 r12).val by rw [v2_12] <;> exit_arith,
        Array.getElem?_set_self, hk0] <;> rfl
    · rw [d11, Array.getElem?_set_ne _ (by rw [v10_12] <;> exit_arith), d10, d9,
        Array.getElem?_set_ne _ (by rw [v8_12] <;> exit_arith), d8, d7,
        Array.getElem?_set_ne _ (by rw [v6_12] <;> exit_arith), d6, d5,
        show exitSubStateBase loopBase n m + 1 = (reg t4 r12).val from v4_12.symm,
        Array.getElem?_set_self, hk1] <;> rfl
    · rw [d11, Array.getElem?_set_ne _ (by rw [v10_12] <;> exit_arith), d10, d9,
        Array.getElem?_set_ne _ (by rw [v8_12] <;> exit_arith), d8, d7,
        show exitSubStateBase loopBase n m + 2 = (reg t6 r12).val from v6_12.symm,
        Array.getElem?_set_self, hk2] <;> rfl
    · rw [d11, Array.getElem?_set_ne _ (by rw [v10_12] <;> exit_arith), d10, d9,
        show exitSubStateBase loopBase n m + 3 = (reg t8 r12).val from v8_12.symm,
        Array.getElem?_set_self, hk3] <;> rfl
    · rw [d11, show exitSubStateBase loopBase n m + 4 = (reg t10 r12).val from v10_12.symm,
        Array.getElem?_set_self, hk4] <;> rfl
  have hFr : ∀ addr, (addr < exitSubStateBase loopBase n m ∨ exitSubStateBase loopBase n m + 5 ≤ addr) →
      t11.data[addr]? = s₀.data[addr]? := by
    intro addr ha
    rw [d11, Array.getElem?_set_ne _ (by rw [v10_12] <;> exit_arith), d10, d9,
      Array.getElem?_set_ne _ (by rw [v8_12] <;> exit_arith), d8, d7,
      Array.getElem?_set_ne _ (by rw [v6_12] <;> exit_arith), d6, d5,
      Array.getElem?_set_ne _ (by rw [v4_12] <;> exit_arith), d4, d3,
      Array.getElem?_set_ne _ (by rw [v2_12] <;> exit_arith), d2, d1]
  exact ⟨t11, hSteps, hPC11, hSz11, hKeep11, v11_12, hWr, hFr⟩

private theorem exitSaveRegs2_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitSaveRegsCode h100) offSave)
    (hFit : offSub < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offSave + 11) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr12 : (reg s₀ r12).val = exitSubStateBase loopBase n m + 4)
    (hStFit : exitSubStateBase loopBase n m + 11 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 12 s₀ s1 ∧
      s1.pc = offSub ∧
      s1.data.size = workCap ∧
      (∀ (k : Nat), 5 ≤ k → ∀ (hk : k < 11),
        s1.data[exitSubStateBase loopBase n m + k]? =
          some (reg s₀ ⟨k, (Nat.lt_trans hk (by decide : 11 < 16))⟩)) ∧
      (∀ addr, (addr < exitSubStateBase loopBase n m + 5 ∨ exitSubStateBase loopBase n m + 11 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  let arena := exitSubStateBase loopBase n m
  have hSweep (j : Nat) (hj : j ≤ 6) :
      ∃ t : State L16,
        Steps code input (2 * j) s₀ t ∧
        t.pc = offSave + 11 + 2 * j ∧
        (reg t r12).val = arena + 4 + j ∧
        (∀ k : Fin 11, reg t ⟨k.val, Nat.lt_trans k.isLt (by decide : 11 < 16)⟩ =
          reg s₀ ⟨k.val, Nat.lt_trans k.isLt (by decide : 11 < 16)⟩) ∧
        (∀ k : Fin 11, 5 ≤ k.val → k.val < 5 + j →
          t.data[arena + k.val]? =
            some (reg s₀ ⟨k.val, Nat.lt_trans k.isLt (by decide : 11 < 16)⟩)) ∧
        (∀ addr, (addr < arena + 5 ∨ arena + 5 + j ≤ addr) →
          t.data[addr]? = s₀.data[addr]?) := by
    induction j with
    | zero =>
      exact ⟨s₀, Steps.zero _, hPC, hr12, fun _ => rfl, fun _ h₁ h₂ => by omega, fun _ _ => rfl⟩
    | succ j ih =>
      obtain ⟨t, hTrace, hPc, hAddr, hKeep, hWritten, hFrame⟩ := ih (by omega)
      have hj' : j < 6 := by omega
      let k : Fin 11 := ⟨5 + j, by omega⟩
      let src : Fin 16 := ⟨k.val, Nat.lt_trans k.isLt (by decide : 11 < 16)⟩
      have hFetchAdd : code[t.pc]? = some (.add r12 r12 r1) := by
        have h := hPl.at (11 + 2 * j) (by rw [exitSaveRegsCode_size]; omega)
          (pc := t.pc) (by rw [hPc, Nat.add_assoc])
        have hCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
        rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h
      obtain ⟨u, hs, hPcU, hAddrU, hKeepU, hDataU⟩ :=
        step_add16 (input := input) (s := t) hFetchAdd (by
          simp only [offSave, offSub] at hPc hFit
          omega)
      have hOne : (reg t r1).val = 1 :=
        (congrArg Fin.val (hKeep ⟨1, by decide⟩)).trans hRegs.entry.consts.one
      have hAddrVal : (reg u r12).val = arena + k.val := by
        have hBound : arena + 4 + j + 1 < 2 ^ bits := by
          change arena + 11 ≤ workCap at hStFit
          omega
        rw [hAddrU, add_no_wrap _ _ (by rw [hAddr, hOne]; exact hBound), hAddr, hOne]
        change arena + 4 + j + 1 = arena + (5 + j)
        omega
      have hFetchStore : code[u.pc]? = some (.storeData r12 src) := by
        have h := hPl.at (12 + 2 * j) (by rw [exitSaveRegsCode_size]; omega)
          (pc := u.pc) (by rw [hPcU, hPc]; omega)
        have hCases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
        rcases hCases with rfl | rfl | rfl | rfl | rfl | rfl <;> exact h
      have hWriteFit : (reg u r12).val < u.data.size := by
        rw [hAddrVal, u.data_size]
        change arena + k.val < workCap
        have hk := k.isLt
        change arena + 11 ≤ workCap at hStFit
        omega
      obtain ⟨v, hs', hPcV, hRegsV, hDataV⟩ :=
        step_storeData16 (input := input) (s := u) hFetchStore (by
          simp only [offSave, offSub] at hPc hFit
          omega) hWriteFit
      have hKeepV (i : Fin 11) :
          reg v ⟨i.val, Nat.lt_trans i.isLt (by decide : 11 < 16)⟩ =
            reg s₀ ⟨i.val, Nat.lt_trans i.isLt (by decide : 11 < 16)⟩ := by
        rw [reg_eq_of_regs_eq hRegsV]
        exact (hKeepU _ (by intro h; have hv := congrArg Fin.val h; have hi := i.isLt; change i.val = 12 at hv; omega)).trans
          (hKeep i)
      have hCell (addr : Nat) (ha : arena + k.val ≠ addr) :
          v.data[addr]? = t.data[addr]? := by
        rw [hDataV, Array.getElem?_set_ne _ (by rw [hAddrVal]; exact ha), hDataU]
      refine ⟨v, ?_, by rw [hPcV, hPcU, hPc]; omega, ?_, hKeepV, ?_, ?_⟩
      · have hSegment := Steps.cons hs (step1 hs')
        simpa only [Nat.mul_add] using hTrace.append hSegment
      · rw [reg_eq_of_regs_eq hRegsV, hAddrVal]
        change arena + (5 + j) = arena + 4 + (j + 1)
        omega
      · intro i hi₀ hi₁
        by_cases hEq : i = k
        · subst i
          rw [hDataV, ← hAddrVal, Array.getElem?_set_self]
          exact congrArg some ((hKeepU src (by intro h; have hv := congrArg Fin.val h; have hk := k.isLt; change k.val = 12 at hv; omega)).trans (hKeep k))
        · have hNe : i.val ≠ k.val := fun h => hEq (Fin.ext h)
          have hkVal : k.val = 5 + j := rfl
          rw [hCell _ (by omega)]
          exact hWritten i hi₀ (by omega)
      · intro addr ha
        have hkVal : k.val = 5 + j := rfl
        rw [hCell _ (by omega)]
        exact hFrame addr (by omega)
  obtain ⟨t, hSteps, hPc, _, _, hWritten, hFr⟩ := hSweep 6 (by decide)
  refine ⟨t, hSteps, by rw [hPc]; rfl, t.data_size, ?_, ?_⟩
  · intro k hk0 hk1
    exact hWritten ⟨k, hk1⟩ hk0 hk1
  · intro addr ha
    exact hFr addr (by change addr < arena + 5 ∨ arena + 11 ≤ addr at ha; exact ha)

theorem exitSaveRegs_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitSaveRegsCode h100) offSave)
    (hFit : offSub < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offSave) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hStFit : exitSubStateBase loopBase n m + 11 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 23 s₀ s1 ∧
      s1.pc = offSub ∧
      s1.data.size = workCap ∧
      (∀ k : Fin 11, s1.data[exitSubStateBase loopBase n m + k.val]? = some (reg s₀ ⟨k.val, by exit_arith⟩)) ∧
      (∀ addr, (addr < exitSubStateBase loopBase n m ∨ exitSubStateBase loopBase n m + 11 ≤ addr) →
        s1.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨s1, hs1, pc1, sz1, keep1, r1_12, hw1, hf1⟩ :=
    exitSaveRegs1_steps h100 hPl (by simp only [offSave, offSub] at hFit ⊢ <;> exit_arith) hPC hSz hRegs hSt2 hStFit hBits
  obtain ⟨s2, hs2, pc2, sz2, hw2, hf2⟩ :=
    exitSaveRegs2_steps h100 hPl hFit pc1 sz1 (exitLoopRegs_of_keep hRegs keep1) r1_12 hStFit hBits
  refine ⟨s2, hs1.append hs2, pc2, sz2, fun k => ?_, fun addr ha => ?_⟩
  · by_cases hk : k.val < 5
    · rw [hf2 _ (Or.inl (by exit_arith)), hw1 k.val hk]
    · rw [hw2 k.val (by exit_arith) k.isLt, keep1 ⟨k.val, by exit_arith⟩ (by exit_arith)]
  · rw [hf2 addr (by rcases ha with h | h <;> exit_arith), hf1 addr (by rcases ha with h | h <;> exit_arith)]

private theorem exitRestoreRegs1_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitRestoreRegsCode h100) (offRestore subLen))
    (hFit : offRestore subLen + 12 < code.size)
    {loopBase n m : Nat}
    {s₀ sSaved : State L16} (hPC : s₀.pc = offRestore subLen) (hSz : s₀.data.size = workCap)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSaved : ∀ k : Fin 11, s₀.data[exitSubStateBase loopBase n m + k.val]? = some (reg sSaved ⟨k.val, by exit_arith⟩))
    (hStFit : exitSubStateBase loopBase n m + 11 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 12 s₀ s1 ∧
      s1.pc = offRestore subLen + 12 ∧
      s1.data = s₀.data ∧
      (reg s1 r12).val = exitSubStateBase loopBase n m + 4 ∧
      (reg s1 r13).val = 1 ∧
      (∀ r : Fin 16, r.val ≤ 4 → reg s1 r = reg sSaved r) := by
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have hLoad1 : t1.data[(reg t1 r11).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d1, show (reg t1 r11).val = statePtrAddr by rw [r1_11] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_12, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_12 : (reg t2 r12).val = exitSubStateBase loopBase n m := by rw [r2_12]
  obtain ⟨t3, hs3, pc3, r3_13, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_12 : (reg t3 r12).val = exitSubStateBase loopBase n m := by rw [p3 r12 (by decide), v2_12]
  have v3_13 : (reg t3 r13).val = 1 := by rw [r3_13] <;> rfl
  have hLoad3 : t3.data[(reg t3 r12).val]? = some (reg sSaved r0) := by
    rw [d3, d2, d1, v3_12]
    exact hSaved ⟨0, by decide⟩
  obtain ⟨t4, hs4, pc4, r4_0, p4, d4⟩ := step_loadData16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) hLoad3 (by rw [pc3] <;> exit_arith)
  have v4_12 : (reg t4 r12).val = exitSubStateBase loopBase n m := by rw [p4 r12 (by decide), v3_12]
  have v4_13 : (reg t4 r13).val = 1 := by rw [p4 r13 (by decide), v3_13]
  obtain ⟨t5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5_12 : (reg t5 r12).val = exitSubStateBase loopBase n m + 1 := by
    rw [r5_12, add_no_wrap _ _ (by rw [v4_12, v4_13] <;> exit_arith), v4_12, v4_13]
  have hLoad5 : t5.data[(reg t5 r12).val]? = some (reg sSaved r1) := by
    rw [d5, d4, d3, d2, d1, v5_12]; exact hSaved ⟨1, by decide⟩
  obtain ⟨t6, hs6, pc6, r6_1, p6, d6⟩ := step_loadData16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) hLoad5 (by rw [pc5] <;> exit_arith)
  have v6_12 : (reg t6 r12).val = exitSubStateBase loopBase n m + 1 := by rw [p6 r12 (by decide), v5_12]
  have v6_13 : (reg t6 r13).val = 1 := by rw [p6 r13 (by decide), p5 r13 (by decide), v4_13]
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = exitSubStateBase loopBase n m + 2 := by
    rw [r7_12, add_no_wrap _ _ (by rw [v6_12, v6_13] <;> exit_arith), v6_12, v6_13] <;> exit_arith
  have hLoad7 : t7.data[(reg t7 r12).val]? = some (reg sSaved r2) := by
    rw [d7, d6, d5, d4, d3, d2, d1, v7_12]; exact hSaved ⟨2, by decide⟩
  obtain ⟨t8, hs8, pc8, r8_2, p8, d8⟩ := step_loadData16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) hLoad7 (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = exitSubStateBase loopBase n m + 2 := by rw [p8 r12 (by decide), v7_12]
  have v8_13 : (reg t8 r13).val = 1 := by rw [p8 r13 (by decide), p7 r13 (by decide), v6_13]
  obtain ⟨t9, hs9, pc9, r9_12, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_12 : (reg t9 r12).val = exitSubStateBase loopBase n m + 3 := by
    rw [r9_12, add_no_wrap _ _ (by rw [v8_12, v8_13] <;> exit_arith), v8_12, v8_13] <;> exit_arith
  have hLoad9 : t9.data[(reg t9 r12).val]? = some (reg sSaved r3) := by
    rw [d9, d8, d7, d6, d5, d4, d3, d2, d1, v9_12]; exact hSaved ⟨3, by decide⟩
  obtain ⟨t10, hs10, pc10, r10_3, p10, d10⟩ := step_loadData16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) hLoad9 (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = exitSubStateBase loopBase n m + 3 := by rw [p10 r12 (by decide), v9_12]
  have v10_13 : (reg t10 r13).val = 1 := by rw [p10 r13 (by decide), p9 r13 (by decide), v8_13]
  obtain ⟨t11, hs11, pc11, r11_12, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_12 : (reg t11 r12).val = exitSubStateBase loopBase n m + 4 := by
    rw [r11_12, add_no_wrap _ _ (by rw [v10_12, v10_13] <;> exit_arith), v10_12, v10_13] <;> exit_arith
  have hLoad11 : t11.data[(reg t11 r12).val]? = some (reg sSaved r4) := by
    rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, v11_12]; exact hSaved ⟨4, by decide⟩
  obtain ⟨t12, hs12, pc12, r12_4, p12, d12⟩ := step_loadData16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) hLoad11 (by rw [pc11] <;> exit_arith)
  have hSteps : Steps code input 12 s₀ t12 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (step1 hs12)))))))))))
  have hPC12 : t12.pc = offRestore subLen + 12 := by
    rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hData12 : t12.data = s₀.data := by
    rw [d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have v12_12 : (reg t12 r12).val = exitSubStateBase loopBase n m + 4 := by rw [p12 r12 (by decide), v11_12]
  have v12_13 : (reg t12 r13).val = 1 := by
    rw [p12 r13 (by decide), p11 r13 (by decide), v10_13]
  have hRegs12 : ∀ r : Fin 16, r.val ≤ 4 → reg t12 r = reg sSaved r := by
    intro r hr
    rcases r with ⟨rv, hrv⟩
    have hc : rv = 0 ∨ rv = 1 ∨ rv = 2 ∨ rv = 3 ∨ rv = 4 := by exit_arith
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · change reg t12 r0 = reg sSaved r0
      rw [p12 r0 (by decide), p11 r0 (by decide), p10 r0 (by decide), p9 r0 (by decide),
        p8 r0 (by decide), p7 r0 (by decide), p6 r0 (by decide), p5 r0 (by decide), r4_0] <;> rfl
    · change reg t12 r1 = reg sSaved r1
      rw [p12 r1 (by decide), p11 r1 (by decide), p10 r1 (by decide), p9 r1 (by decide),
        p8 r1 (by decide), p7 r1 (by decide), r6_1] <;> rfl
    · change reg t12 r2 = reg sSaved r2
      rw [p12 r2 (by decide), p11 r2 (by decide), p10 r2 (by decide), p9 r2 (by decide), r8_2] <;> rfl
    · change reg t12 r3 = reg sSaved r3
      rw [p12 r3 (by decide), p11 r3 (by decide), r10_3] <;> rfl
    · exact r12_4
  exact ⟨t12, hSteps, hPC12, hData12, v12_12, v12_13, hRegs12⟩

private theorem exitRestoreRegs2_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitRestoreRegsCode h100) (offRestore subLen))
    (hFit : offPostSetup subLen < code.size)
    {loopBase n m : Nat}
    {s₀ sSaved : State L16} (hPC : s₀.pc = offRestore subLen + 12) (hSz : s₀.data.size = workCap)
    (hr12 : (reg s₀ r12).val = exitSubStateBase loopBase n m + 4)
    (hr13 : (reg s₀ r13).val = 1)
    (hSaved : ∀ k : Fin 11, s₀.data[exitSubStateBase loopBase n m + k.val]? = some (reg sSaved ⟨k.val, by exit_arith⟩))
    (hStFit : exitSubStateBase loopBase n m + 11 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 12 s₀ s1 ∧
      s1.pc = offPostSetup subLen ∧
      s1.data = s₀.data ∧
      (∀ r : Fin 16, r.val ≤ 4 → reg s1 r = reg s₀ r) ∧
      (∀ r : Fin 16, 5 ≤ r.val → r.val ≤ 10 → reg s1 r = reg sSaved r) := by
  obtain ⟨t1, hs1, pc1, r1_12, p1, d1⟩ := step_add16 (input := input) (s := s₀) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1_12 : (reg t1 r12).val = exitSubStateBase loopBase n m + 5 := by
    rw [r1_12, add_no_wrap _ _ (by rw [hr12, hr13] <;> exit_arith), hr12, hr13] <;> exit_arith
  have hLoad1 : t1.data[(reg t1 r12).val]? = some (reg sSaved r5) := by
    rw [d1, v1_12]; exact hSaved ⟨5, by decide⟩
  obtain ⟨t2, hs2, pc2, r2_5, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_12 : (reg t2 r12).val = exitSubStateBase loopBase n m + 5 := by rw [p2 r12 (by decide), v1_12]
  have v2_13 : (reg t2 r13).val = 1 := by rw [p2 r13 (by decide), p1 r13 (by decide), hr13]
  obtain ⟨t3, hs3, pc3, r3_12, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_12 : (reg t3 r12).val = exitSubStateBase loopBase n m + 6 := by
    rw [r3_12, add_no_wrap _ _ (by rw [v2_12, v2_13] <;> exit_arith), v2_12, v2_13] <;> exit_arith
  have hLoad3 : t3.data[(reg t3 r12).val]? = some (reg sSaved r6) := by
    rw [d3, d2, d1, v3_12]; exact hSaved ⟨6, by decide⟩
  obtain ⟨t4, hs4, pc4, r4_6, p4, d4⟩ := step_loadData16 (input := input) (s := t3) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) hLoad3 (by rw [pc3] <;> exit_arith)
  have v4_12 : (reg t4 r12).val = exitSubStateBase loopBase n m + 6 := by rw [p4 r12 (by decide), v3_12]
  have v4_13 : (reg t4 r13).val = 1 := by rw [p4 r13 (by decide), p3 r13 (by decide), v2_13]
  obtain ⟨t5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 16 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5_12 : (reg t5 r12).val = exitSubStateBase loopBase n m + 7 := by
    rw [r5_12, add_no_wrap _ _ (by rw [v4_12, v4_13] <;> exit_arith), v4_12, v4_13] <;> exit_arith
  have hLoad5 : t5.data[(reg t5 r12).val]? = some (reg sSaved r7) := by
    rw [d5, d4, d3, d2, d1, v5_12]; exact hSaved ⟨7, by decide⟩
  obtain ⟨t6, hs6, pc6, r6_7, p6, d6⟩ := step_loadData16 (input := input) (s := t5) (hPl.at 17 (by exit_rom_bound) (by exit_arith)) hLoad5 (by rw [pc5] <;> exit_arith)
  have v6_12 : (reg t6 r12).val = exitSubStateBase loopBase n m + 7 := by rw [p6 r12 (by decide), v5_12]
  have v6_13 : (reg t6 r13).val = 1 := by rw [p6 r13 (by decide), p5 r13 (by decide), v4_13]
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 18 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = exitSubStateBase loopBase n m + 8 := by
    rw [r7_12, add_no_wrap _ _ (by rw [v6_12, v6_13] <;> exit_arith), v6_12, v6_13] <;> exit_arith
  have hLoad7 : t7.data[(reg t7 r12).val]? = some (reg sSaved r8) := by
    rw [d7, d6, d5, d4, d3, d2, d1, v7_12]; exact hSaved ⟨8, by decide⟩
  obtain ⟨t8, hs8, pc8, r8_8, p8, d8⟩ := step_loadData16 (input := input) (s := t7) (hPl.at 19 (by exit_rom_bound) (by exit_arith)) hLoad7 (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = exitSubStateBase loopBase n m + 8 := by rw [p8 r12 (by decide), v7_12]
  have v8_13 : (reg t8 r13).val = 1 := by rw [p8 r13 (by decide), p7 r13 (by decide), v6_13]
  obtain ⟨t9, hs9, pc9, r9_12, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 20 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_12 : (reg t9 r12).val = exitSubStateBase loopBase n m + 9 := by
    rw [r9_12, add_no_wrap _ _ (by rw [v8_12, v8_13] <;> exit_arith), v8_12, v8_13] <;> exit_arith
  have hLoad9 : t9.data[(reg t9 r12).val]? = some (reg sSaved r9) := by
    rw [d9, d8, d7, d6, d5, d4, d3, d2, d1, v9_12]; exact hSaved ⟨9, by decide⟩
  obtain ⟨t10, hs10, pc10, r10_9, p10, d10⟩ := step_loadData16 (input := input) (s := t9) (hPl.at 21 (by exit_rom_bound) (by exit_arith)) hLoad9 (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = exitSubStateBase loopBase n m + 9 := by rw [p10 r12 (by decide), v9_12]
  have v10_13 : (reg t10 r13).val = 1 := by rw [p10 r13 (by decide), p9 r13 (by decide), v8_13]
  obtain ⟨t11, hs11, pc11, r11_12, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 22 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_12 : (reg t11 r12).val = exitSubStateBase loopBase n m + 10 := by
    rw [r11_12, add_no_wrap _ _ (by rw [v10_12, v10_13] <;> exit_arith), v10_12, v10_13] <;> exit_arith
  have hLoad11 : t11.data[(reg t11 r12).val]? = some (reg sSaved r10) := by
    rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, v11_12]; exact hSaved ⟨10, by decide⟩
  obtain ⟨t12, hs12, pc12, r12_10, p12, d12⟩ := step_loadData16 (input := input) (s := t11) (hPl.at 23 (by exit_rom_bound) (by exit_arith)) hLoad11 (by rw [pc11] <;> exit_arith)
  have hSteps : Steps code input 12 s₀ t12 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (step1 hs12)))))))))))
  have hPC12 : t12.pc = offPostSetup subLen := by
    rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]
    simp only [offRestore, offPostSetup] <;> exit_arith
  have hData12 : t12.data = s₀.data := by
    rw [d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hKeepLow : ∀ r : Fin 16, r.val ≤ 4 → reg t12 r = reg s₀ r := by
    intro r hr
    rw [p12 r (by exit_arith), p11 r (by exit_arith), p10 r (by exit_arith), p9 r (by exit_arith),
      p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith),
      p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have hHigh : ∀ r : Fin 16, 5 ≤ r.val → r.val ≤ 10 → reg t12 r = reg sSaved r := by
    intro r hr1 hr2
    rcases r with ⟨rv, hrv⟩
    have hc : rv = 5 ∨ rv = 6 ∨ rv = 7 ∨ rv = 8 ∨ rv = 9 ∨ rv = 10 := by exit_arith
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    · change reg t12 r5 = reg sSaved r5
      rw [p12 r5 (by decide), p11 r5 (by decide), p10 r5 (by decide), p9 r5 (by decide),
        p8 r5 (by decide), p7 r5 (by decide), p6 r5 (by decide), p5 r5 (by decide),
        p4 r5 (by decide), p3 r5 (by decide), r2_5] <;> rfl
    · change reg t12 r6 = reg sSaved r6
      rw [p12 r6 (by decide), p11 r6 (by decide), p10 r6 (by decide), p9 r6 (by decide),
        p8 r6 (by decide), p7 r6 (by decide), p6 r6 (by decide), p5 r6 (by decide), r4_6] <;> rfl
    · change reg t12 r7 = reg sSaved r7
      rw [p12 r7 (by decide), p11 r7 (by decide), p10 r7 (by decide), p9 r7 (by decide),
        p8 r7 (by decide), p7 r7 (by decide), r6_7] <;> rfl
    · change reg t12 r8 = reg sSaved r8
      rw [p12 r8 (by decide), p11 r8 (by decide), p10 r8 (by decide), p9 r8 (by decide), r8_8] <;> rfl
    · change reg t12 r9 = reg sSaved r9
      rw [p12 r9 (by decide), p11 r9 (by decide), r10_9] <;> rfl
    · exact r12_10
  exact ⟨t12, hSteps, hPC12, hData12, hKeepLow, hHigh⟩

theorem exitRestoreRegs_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {subLen : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitRestoreRegsCode h100) (offRestore subLen))
    (hFit : offPostSetup subLen < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ sSaved : State L16} (hPC : s₀.pc = offRestore subLen) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed sSaved)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSaved : ∀ k : Fin 11, s₀.data[exitSubStateBase loopBase n m + k.val]? = some (reg sSaved ⟨k.val, by exit_arith⟩))
    (hStFit : exitSubStateBase loopBase n m + 11 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 24 s₀ s1 ∧
      s1.pc = offPostSetup subLen ∧
      s1.data = s₀.data ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 := by
  obtain ⟨s1, hs1, pc1, d1, r12, r13, hLow⟩ :=
    exitRestoreRegs1_steps h100 hPl (by simp only [offRestore, offPostSetup] at hFit ⊢ <;> exit_arith) hPC hSz hSt2 hSaved hStFit hBits
  obtain ⟨s2, hs2, pc2, d2, hKeepLow, hHigh⟩ :=
    exitRestoreRegs2_steps h100 hPl hFit pc1 (by rw [d1, hSz]) r12 r13 (by rw [d1]; exact hSaved) hStFit hBits
  have hKeepAll : ∀ r : Fin 16, r.val ≤ 10 → reg s2 r = reg sSaved r := by
    intro r hr
    by_cases hL : r.val ≤ 4
    · rw [hKeepLow r hL, hLow r hL]
    · exact hHigh r (by exit_arith) hr
  exact ⟨s2, hs1.append hs2, pc2, d2.trans d1, exitLoopRegs_of_keep hRegs hKeepAll⟩

/-! #### Block 6: `exitPostSetup` (`43` steps), `exitPostCopy + exitPostStep`, and `exitFinish` (`16` steps) -/

end SmallStepHelpers

end PaperB.RamExitFamilyLoop
