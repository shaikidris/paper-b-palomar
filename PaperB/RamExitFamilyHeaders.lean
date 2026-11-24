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

/-! #### Block 3: `exitLargeA` (`76..94`, `19` steps) and `exitLargeB` (`95..122`, `28` steps) -/

theorem ownerForestPtrsBase_add_44n (loopBase n m : Nat) :
    ownerForestPtrsBase loopBase n m + 44 * n = exitPtrsBase loopBase n m := by
  have h := forestArenaEnd_eq loopBase n m
  simp only [forestArenaBase] at h
  unfold exitPtrsBase
  omega

private theorem exitLargeA1_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitLargeACode h100) offLargeA)
    (hFit : offLargeA + 10 < code.size)
    {n m root Q treeBase emitBase loopBase exitUsed : Nat}
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hQn : Q ≤ n) (d : Fin dense.length)
    {s₀ : State L16} (hPC : s₀.pc = offLargeA) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s₀)
    (hr11 : (reg s₀ r11).val = 1 + (S.childSlice d).length)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt13 : (s₀.data[exitSubStateBase loopBase n m + 13]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hQStart0 : (s₀.data[emitBase + 2 * n + d.val]?).map Fin.val = some (qStartFn S d.val))
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisjEmit : emitBase + emitterWorkWords n m ≤ loopBase)
    (hSubInFit : exitSubInBase loopBase n m + 2 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 10 s₀ s1 ∧
      s1.pc = offLargeA + 10 ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s1 ∧
      (reg s1 r11).val = emitBase + 2 * n + d.val ∧
      (reg s1 r12).val = exitSubStateBase loopBase n m ∧
      (reg s1 r13).val = qStartFn S d.val ∧
      (reg s1 r15).val = exitSubInBase loopBase n m ∧
      (s1.data[exitSubInBase loopBase n m]?).map Fin.val = some (1 + (S.childSlice d).length) ∧
      (∀ addr, addr ≠ exitSubInBase loopBase n m → s1.data[addr]? = s₀.data[addr]?) := by
  have hStFit : exitSubStateBase loopBase n m + 13 < 2 ^ bits := by
    obtain ⟨w13, hw13, _⟩ := Option.map_eq_some_iff.mp hSt13
    have hLt := (Array.getElem?_eq_some_iff.mp hw13).1
    rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  have hQLeM : qStartFn S d.val ≤ m := by
    rw [hm]; exact qStartFn_le_arcCount S d.val
  have hEmitBnd : emitBase + 2 * n + d.val < workCap := by
    have hDn : d.val < n := by have := d.isLt <;> exit_arith
    unfold emitterWorkWords at hEmitFit <;> exit_arith
  have hMLe : m < workCap := by unfold emitterWorkWords at hEmitFit <;> exit_arith
  obtain ⟨t1, hs1, pc1, r1_12, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have hLoad1 : t1.data[(reg t1 r12).val]? = some ⟨exitSubStateBase loopBase n m, by exit_arith⟩ := by
    rw [d1, show (reg t1 r12).val = statePtrAddr by rw [r1_12] <;> rfl]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt2
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_12, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_12 : (reg t2 r12).val = exitSubStateBase loopBase n m := by rw [r2_12]
  obtain ⟨t3, hs3, pc3, r3_13, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_12 : (reg t3 r12).val = exitSubStateBase loopBase n m := by rw [p3 r12 (by decide), v2_12]
  have v3_13 : (reg t3 r13).val = 13 := by rw [r3_13] <;> rfl
  obtain ⟨t4, hs4, pc4, r4_13, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_13 : (reg t4 r13).val = exitSubStateBase loopBase n m + 13 := by
    rw [r4_13, add_no_wrap _ _ (by rw [v3_12, v3_13]; exact hStFit), v3_12, v3_13]
  have hLoad4 : t4.data[(reg t4 r13).val]? = some ⟨exitSubInBase loopBase n m, by exit_arith⟩ := by
    rw [d4, d3, d2, d1, v4_13]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt13
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t5, hs5, pc5, r5_15, p5, d5⟩ := step_loadData16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) hLoad4 (by rw [pc4] <;> exit_arith)
  have v5_15 : (reg t5 r15).val = exitSubInBase loopBase n m := by rw [r5_15]
  have b5 : (reg t5 r15).val < t5.data.size := by rw [d5, d4, d3, d2, d1, hSz, v5_15] <;> exit_arith
  obtain ⟨t6, hs6, pc6, rg6, d6⟩ := step_storeData16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith) b5
  have hKeep6 : ∀ r : Fin 16, r.val ≤ 10 → reg t6 r = reg s₀ r := by
    intro r hr
    rw [reg_eq_of_regs_eq rg6 r, p5 r (by exit_arith), p4 r (by exit_arith), p3 r (by exit_arith),
      p2 r (by exit_arith), p1 r (by exit_arith)]
  have v6_2 : (reg t6 r2).val = n := by rw [hKeep6 r2 (by decide), hRegs.entry.consts.nVal]
  have vr11_5 : (reg t5 r11).val = 1 + (S.childSlice d).length := by
    rw [p5 r11 (by decide), p4 r11 (by decide), p3 r11 (by decide), p2 r11 (by decide), p1 r11 (by decide), hr11]
  obtain ⟨t7, hs7, pc7, r7_11, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_11 : (reg t7 r11).val = 2 * n := by
    rw [r7_11, add_no_wrap _ _ (by rw [v6_2] <;> exit_arith), v6_2] <;> exit_arith
  have v7_7 : (reg t7 r7).val = emitBase := by
    rw [p7 r7 (by decide), hKeep6 r7 (by decide), hRegs.entry.emitBaseVal]
  obtain ⟨t8, hs8, pc8, r8_11, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_11 : (reg t8 r11).val = emitBase + 2 * n := by
    rw [r8_11, add_no_wrap _ _ (by rw [v7_7, v7_11] <;> exit_arith), v7_7, v7_11]
  have v8_9 : (reg t8 r9).val = d.val := by
    rw [p8 r9 (by decide), p7 r9 (by decide), hKeep6 r9 (by decide), hRegs.dVal]
  obtain ⟨t9, hs9, pc9, r9_11, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_11 : (reg t9 r11).val = emitBase + 2 * n + d.val := by
    rw [r9_11, add_no_wrap _ _ (by rw [v8_11, v8_9] <;> exit_arith), v8_11, v8_9]
  have hNeQS : emitBase + 2 * n + d.val ≠ exitSubInBase loopBase n m := by
    have hDn : d.val < n := by have := d.isLt <;> exit_arith
    simp only [exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, emitterWorkWords] at hDisjEmit ⊢
    exit_arith
  have hLoad9 : t9.data[(reg t9 r11).val]? = some ⟨qStartFn S d.val, by exit_arith⟩ := by
    rw [d9, d8, d7, d6, v9_11, Array.getElem?_set_ne _ (by rw [v5_15]; exact hNeQS.symm),
      d5, d4, d3, d2, d1]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hQStart0
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t10, hs10, pc10, r10_13, p10, d10⟩ := step_loadData16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) hLoad9 (by rw [pc9] <;> exit_arith)
  have hSteps : Steps code input 10 s₀ t10 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (step1 hs10)))))))))
  have hPC10 : t10.pc = offLargeA + 10 := by
    rw [pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hSz10 : t10.data.size = workCap := by
    rw [d10, d9, d8, d7, d6, Array.size_set, d5, d4, d3, d2, d1, hSz]
  have hKeep10 : ∀ r : Fin 16, r.val ≤ 10 → reg t10 r = reg s₀ r := by
    intro r hr
    rw [p10 r (by exit_arith), p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith)]
    exact hKeep6 r hr
  have v10_11 : (reg t10 r11).val = emitBase + 2 * n + d.val := by rw [p10 r11 (by decide), v9_11]
  have v10_12 : (reg t10 r12).val = exitSubStateBase loopBase n m := by
    rw [p10 r12 (by decide), p9 r12 (by decide), p8 r12 (by decide), p7 r12 (by decide),
      reg_eq_of_regs_eq rg6 r12, p5 r12 (by decide), p4 r12 (by decide), p3 r12 (by decide), v2_12]
  have v10_13 : (reg t10 r13).val = qStartFn S d.val := by rw [r10_13]
  have v10_15 : (reg t10 r15).val = exitSubInBase loopBase n m := by
    rw [p10 r15 (by decide), p9 r15 (by decide), p8 r15 (by decide), p7 r15 (by decide),
      reg_eq_of_regs_eq rg6 r15, v5_15]
  have hAtIn0 : (t10.data[exitSubInBase loopBase n m]?).map Fin.val = some (1 + (S.childSlice d).length) := by
    rw [d10, d9, d8, d7, d6, show exitSubInBase loopBase n m = (reg t5 r15).val from v5_15.symm,
      Array.getElem?_set_self, Option.map_some, vr11_5]
  have hFr10 : ∀ addr, addr ≠ exitSubInBase loopBase n m → t10.data[addr]? = s₀.data[addr]? := by
    intro addr ha
    rw [d10, d9, d8, d7, d6, Array.getElem?_set_ne _ (by rw [v5_15]; exact ha.symm), d5, d4, d3, d2, d1]
  exact ⟨t10, hSteps, hPC10, hSz10, exitLoopRegs_of_keep hRegs hKeep10,
    v10_11, v10_12, v10_13, v10_15, hAtIn0, hFr10⟩

private theorem exitLargeA2_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitLargeACode h100) offLargeA)
    (hFit : offLargeB < code.size)
    {n m root Q treeBase emitBase loopBase exitUsed : Nat}
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hQn : Q ≤ n) (d : Fin dense.length)
    {s₀ : State L16} (hPC : s₀.pc = offLargeA + 10) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s₀)
    (hr11 : (reg s₀ r11).val = emitBase + 2 * n + d.val)
    (hr12 : (reg s₀ r12).val = exitSubStateBase loopBase n m)
    (hr13 : (reg s₀ r13).val = qStartFn S d.val)
    (hr15 : (reg s₀ r15).val = exitSubInBase loopBase n m)
    (hSt14 : (s₀.data[exitSubStateBase loopBase n m + 14]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hQStart1 : (s₀.data[emitBase + 2 * n + (d.val + 1)]?).map Fin.val = some (qStartFn S (d.val + 1)))
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hSubInFit : exitSubInBase loopBase n m + 2 ≤ exitSubWorkBase loopBase n m workCap)
    (hSubWorkFit : exitSubWorkBase loopBase n m workCap + 2 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 9 s₀ s1 ∧
      s1.pc = offLargeB ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s1 ∧
      (reg s1 r11).val = exitSubWorkBase loopBase n m workCap ∧
      (reg s1 r12).val = exitSubStateBase loopBase n m ∧
      (reg s1 r15).val = exitSubInBase loopBase n m + 1 ∧
      (s1.data[exitSubInBase loopBase n m + 1]?).map Fin.val = some (S.emittedArcs d).length ∧
      (s1.data[exitSubWorkBase loopBase n m workCap]?).map Fin.val = some (qStartFn S d.val) ∧
      (∀ addr, addr ≠ exitSubInBase loopBase n m + 1 → addr ≠ exitSubWorkBase loopBase n m workCap →
        s1.data[addr]? = s₀.data[addr]?) := by
  have hQ1LeM : qStartFn S (d.val + 1) ≤ m := by
    rw [hm]; exact qStartFn_le_arcCount S (d.val + 1)
  have hQ0Le1 : qStartFn S d.val ≤ qStartFn S (d.val + 1) :=
    by rw [qStartFn_succ S d.isLt]; exact Nat.le_add_right _ _
  have hMLe : m < workCap := by unfold emitterWorkWords at hEmitFit <;> exit_arith
  have hEmitBnd : emitBase + 2 * n + (d.val + 1) < workCap := by
    have : d.val + 1 ≤ n := by have := d.isLt <;> exit_arith
    unfold emitterWorkWords at hEmitFit <;> exit_arith
  have hStFit : exitSubStateBase loopBase n m + 14 < workCap := by
    obtain ⟨w14, hw14, _⟩ := Option.map_eq_some_iff.mp hSt14
    have hLt := (Array.getElem?_eq_some_iff.mp hw14).1; rw [hSz] at hLt; exact hLt
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (input := input) (s := s₀) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1_11 : (reg t1 r11).val = emitBase + 2 * n + (d.val + 1) := by
    rw [r1_11, add_no_wrap _ _ (by rw [hr11, hRegs.entry.consts.one] <;> exit_arith), hr11, hRegs.entry.consts.one]
    exit_arith
  have hLoad1 : t1.data[(reg t1 r11).val]? = some ⟨qStartFn S (d.val + 1), by exit_arith⟩ := by
    rw [d1, v1_11]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hQStart1
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t2, hs2, pc2, r2_14, p2, d2⟩ := step_loadData16 (input := input) (s := t1) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) hLoad1 (by rw [pc1] <;> exit_arith)
  have v2_14 : (reg t2 r14).val = qStartFn S (d.val + 1) := by rw [r2_14]
  have v2_13 : (reg t2 r13).val = qStartFn S d.val := by rw [p2 r13 (by decide), p1 r13 (by decide), hr13]
  obtain ⟨t3, hs3, pc3, r3_14, p3, d3⟩ := step_sub16 (input := input) (s := t2) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_14 : (reg t3 r14).val = (S.emittedArcs d).length := by
    have hQS : qStartFn S (d.val + 1) = qStartFn S d.val + (S.emittedArcs d).length :=
      qStartFn_succ S d.isLt
    rw [r3_14, sub_exact (by rw [v2_13, v2_14]; exact hQ0Le1), v2_14, v2_13, hQS]
    omega
  have v3_15 : (reg t3 r15).val = exitSubInBase loopBase n m := by
    rw [p3 r15 (by decide), p2 r15 (by decide), p1 r15 (by decide), hr15]
  have v3_1 : (reg t3 r1).val = 1 := by
    rw [p3 r1 (by decide), p2 r1 (by decide), p1 r1 (by decide), hRegs.entry.consts.one]
  obtain ⟨t4, hs4, pc4, r4_15, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_15 : (reg t4 r15).val = exitSubInBase loopBase n m + 1 := by
    rw [r4_15, add_no_wrap _ _ (by rw [v3_15, v3_1] <;> exit_arith), v3_15, v3_1]
  have b4 : (reg t4 r15).val < t4.data.size := by rw [d4, d3, d2, d1, hSz, v4_15] <;> exit_arith
  obtain ⟨t5, hs5, pc5, rg5, d5⟩ := step_storeData16 (input := input) (s := t4) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith) b4
  have v5_12 : (reg t5 r12).val = exitSubStateBase loopBase n m := by
    rw [reg_eq_of_regs_eq rg5 r12, p4 r12 (by decide), p3 r12 (by decide), p2 r12 (by decide),
      p1 r12 (by decide), hr12]
  obtain ⟨t6, hs6, pc6, r6_11, p6, d6⟩ := step_imm16 (input := input) (s := t5) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_11 : (reg t6 r11).val = 14 := by rw [r6_11] <;> rfl
  have v6_12 : (reg t6 r12).val = exitSubStateBase loopBase n m := by rw [p6 r12 (by decide), v5_12]
  obtain ⟨t7, hs7, pc7, r7_11, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 16 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_11 : (reg t7 r11).val = exitSubStateBase loopBase n m + 14 := by
    rw [r7_11, add_no_wrap _ _ (by rw [v6_12, v6_11] <;> exit_arith), v6_12, v6_11]
  have hNeSt14 : exitSubStateBase loopBase n m + 14 ≠ exitSubInBase loopBase n m + 1 := by
    unfold exitSubInBase <;> exit_arith
  have hLoad7 : t7.data[(reg t7 r11).val]? = some ⟨exitSubWorkBase loopBase n m workCap, by exit_arith⟩ := by
    rw [v7_11, d7, d6, d5, Array.getElem?_set_ne _ (by rw [v4_15]; exact hNeSt14.symm), d4, d3, d2, d1]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt14
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t8, hs8, pc8, r8_11, p8, d8⟩ := step_loadData16 (input := input) (s := t7) (hPl.at 17 (by exit_rom_bound) (by exit_arith)) hLoad7 (by rw [pc7] <;> exit_arith)
  have v8_11 : (reg t8 r11).val = exitSubWorkBase loopBase n m workCap := by rw [r8_11]
  have b8 : (reg t8 r11).val < t8.data.size := by
    rw [d8, d7, d6, d5, Array.size_set, d4, d3, d2, d1, hSz, v8_11] <;> exit_arith
  obtain ⟨t9, hs9, pc9, rg9, d9⟩ := step_storeData16 (input := input) (s := t8) (hPl.at 18 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith) b8
  have hSteps : Steps code input 9 s₀ t9 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (step1 hs9))))))))
  have hPC9 : t9.pc = offLargeB := by
    rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hSz9 : t9.data.size = workCap := by
    rw [d9, Array.size_set, d8, d7, d6, d5, Array.size_set, d4, d3, d2, d1, hSz]
  have hKeep9 : ∀ r : Fin 16, r.val ≤ 10 → reg t9 r = reg s₀ r := by
    intro r hr
    rw [reg_eq_of_regs_eq rg9 r, p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith),
      reg_eq_of_regs_eq rg5 r, p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have v9_11 : (reg t9 r11).val = exitSubWorkBase loopBase n m workCap := by
    rw [reg_eq_of_regs_eq rg9 r11, v8_11]
  have v9_12 : (reg t9 r12).val = exitSubStateBase loopBase n m := by
    rw [reg_eq_of_regs_eq rg9 r12, p8 r12 (by exit_arith), p7 r12 (by exit_arith), v6_12]
  have v9_15 : (reg t9 r15).val = exitSubInBase loopBase n m + 1 := by
    rw [reg_eq_of_regs_eq rg9 r15, p8 r15 (by exit_arith), p7 r15 (by exit_arith), p6 r15 (by exit_arith),
      reg_eq_of_regs_eq rg5 r15, v4_15]
  have vr14_4 : (reg t4 r14).val = (S.emittedArcs d).length := by rw [p4 r14 (by decide), v3_14]
  have vr13_8 : (reg t8 r13).val = qStartFn S d.val := by
    rw [p8 r13 (by decide), p7 r13 (by decide), p6 r13 (by decide), reg_eq_of_regs_eq rg5 r13,
      p4 r13 (by decide), p3 r13 (by decide), v2_13]
  have hNeInW : exitSubInBase loopBase n m + 1 ≠ exitSubWorkBase loopBase n m workCap := by omega
  have hAtIn1 : (t9.data[exitSubInBase loopBase n m + 1]?).map Fin.val = some (S.emittedArcs d).length := by
    rw [d9, Array.getElem?_set_ne _ (by rw [v8_11]; exact Ne.symm hNeInW), d8, d7, d6, d5,
      show exitSubInBase loopBase n m + 1 = (reg t4 r15).val from v4_15.symm,
      Array.getElem?_set_self, Option.map_some, vr14_4]
  have hAtW0 : (t9.data[exitSubWorkBase loopBase n m workCap]?).map Fin.val = some (qStartFn S d.val) := by
    rw [d9, show exitSubWorkBase loopBase n m workCap = (reg t8 r11).val from v8_11.symm,
      Array.getElem?_set_self, Option.map_some, vr13_8]
  have hFr9 : ∀ addr, addr ≠ exitSubInBase loopBase n m + 1 → addr ≠ exitSubWorkBase loopBase n m workCap →
      t9.data[addr]? = s₀.data[addr]? := by
    intro addr h1 h2
    rw [d9, Array.getElem?_set_ne _ (by rw [v8_11]; exact h2.symm), d8, d7, d6, d5,
      Array.getElem?_set_ne _ (by rw [v4_15]; exact h1.symm), d4, d3, d2, d1]
  exact ⟨t9, hSteps, hPC9, hSz9, exitLoopRegs_of_keep hRegs hKeep9,
    v9_11, v9_12, v9_15, hAtIn1, hAtW0, hFr9⟩

theorem exitLargeA_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitLargeACode h100) offLargeA)
    (hFit : offLargeB < code.size)
    {n m root Q treeBase emitBase loopBase exitUsed : Nat}
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hQn : Q ≤ n) (d : Fin dense.length)
    {s₀ : State L16} (hPC : s₀.pc = offLargeA) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s₀)
    (hr11 : (reg s₀ r11).val = 1 + (S.childSlice d).length)
    (hSt2 : (s₀.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase loopBase n m))
    (hSt13 : (s₀.data[exitSubStateBase loopBase n m + 13]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hSt14 : (s₀.data[exitSubStateBase loopBase n m + 14]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hQStart0 : (s₀.data[emitBase + 2 * n + d.val]?).map Fin.val = some (qStartFn S d.val))
    (hQStart1 : (s₀.data[emitBase + 2 * n + (d.val + 1)]?).map Fin.val = some (qStartFn S (d.val + 1)))
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisjEmit : emitBase + emitterWorkWords n m ≤ loopBase)
    (hSubInFit : exitSubInBase loopBase n m + 2 ≤ exitSubWorkBase loopBase n m workCap)
    (hSubWorkFit : exitSubWorkBase loopBase n m workCap + 2 ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 19 s₀ s1 ∧
      s1.pc = offLargeB ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d.val exitUsed s1 ∧
      (reg s1 r11).val = exitSubWorkBase loopBase n m workCap ∧
      (reg s1 r12).val = exitSubStateBase loopBase n m ∧
      (reg s1 r15).val = exitSubInBase loopBase n m + 1 ∧
      (s1.data[exitSubInBase loopBase n m]?).map Fin.val = some (1 + (S.childSlice d).length) ∧
      (s1.data[exitSubInBase loopBase n m + 1]?).map Fin.val = some (S.emittedArcs d).length ∧
      (s1.data[exitSubWorkBase loopBase n m workCap]?).map Fin.val = some (qStartFn S d.val) ∧
      (∀ addr, addr ≠ exitSubInBase loopBase n m → addr ≠ exitSubInBase loopBase n m + 1 →
        addr ≠ exitSubWorkBase loopBase n m workCap → s1.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨s1, hs1, pc1, sz1, regs1, r1_11, r1_12, r1_13, r1_15, hIn0, hFr1⟩ :=
    exitLargeA1_steps h100 hPl (by simp only [offLargeA, offLargeB] at hFit ⊢ <;> exit_arith)
      S hm hQ hQn d hPC hSz hRegs hr11 hSt2 hSt13 hQStart0 hEmitFit hDisjEmit (by omega) hBits
  have hNeSt14 : exitSubStateBase loopBase n m + 14 ≠ exitSubInBase loopBase n m := by
    unfold exitSubInBase <;> exit_arith
  have hNeQS1 : emitBase + 2 * n + (d.val + 1) ≠ exitSubInBase loopBase n m := by
    have : d.val + 1 ≤ n := by have := d.isLt <;> exit_arith
    simp only [exitSubInBase, exitSubStateBase, exitArenaBase, exitPtrsBase, emitterWorkWords] at hDisjEmit ⊢ <;> exit_arith
  obtain ⟨s2, hs2, pc2, sz2, regs2, r2_11, r2_12, r2_15, hIn1, hW0, hFr2⟩ :=
    exitLargeA2_steps h100 hPl hFit S hm hQ hQn d pc1 sz1 regs1 r1_11 r1_12 r1_13 r1_15
      (by rw [hFr1 _ hNeSt14]; exact hSt14) (by rw [hFr1 _ hNeQS1]; exact hQStart1)
      hEmitFit hSubInFit hSubWorkFit hBits
  have hNe01 : exitSubInBase loopBase n m ≠ exitSubInBase loopBase n m + 1 := by exit_arith
  have hNe0W : exitSubInBase loopBase n m ≠ exitSubWorkBase loopBase n m workCap := by
    unfold exitSubWorkBase at * <;> exit_arith
  refine ⟨s2, hs1.append hs2, pc2, sz2, regs2, r2_11, r2_12, r2_15,
    (congrArg (Option.map Fin.val) (hFr2 _ hNe01 hNe0W)).trans hIn0, hIn1, hW0, fun a ha0 ha1 haW => ?_⟩
  rw [hFr2 a ha1 haW, hFr1 a ha0]

private theorem exitLargeB1_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitLargeBCode h100) offLargeB)
    (hFit : offLargeB + 15 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offLargeB) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr11 : (reg s₀ r11).val = exitSubWorkBase loopBase n m workCap)
    (hr12 : (reg s₀ r12).val = exitSubStateBase loopBase n m)
    (hr15 : (reg s₀ r15).val = exitSubInBase loopBase n m + 1)
    (hd : d < Q) (hQn : Q ≤ n)
    (hSt11 : (s₀.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m))
    (hEnd : exitArenaBase loopBase n m ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 15 s₀ s1 ∧
      s1.pc = offLargeB + 15 ∧
      s1.data = s₀.data ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r11).val = exitSubWorkBase loopBase n m workCap ∧
      (reg s1 r13).val = ownerForestPtrsBase loopBase n m + 6 * d ∧
      (reg s1 r15).val = exitSubInBase loopBase n m + 1 := by
  have hL : exitPtrsBase loopBase n m < 2 ^ bits := by unfold exitArenaBase at hEnd <;> exit_arith
  have h44 : 44 * n < 2 ^ bits := by
    have := ownerForestPtrsBase_add_44n loopBase n m <;> exit_arith
  have hFP6 : ownerForestPtrsBase loopBase n m + 6 * d < 2 ^ bits := by
    have := ownerForestPtrsBase_add_44n loopBase n m <;> exit_arith
  have hStFit : exitSubStateBase loopBase n m + 11 < 2 ^ bits := by
    obtain ⟨w11, hw11, _⟩ := Option.map_eq_some_iff.mp hSt11
    have hLt := (Array.getElem?_eq_some_iff.mp hw11).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  obtain ⟨t1, hs1, pc1, r1_13, p1, d1⟩ := step_imm16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1_12 : (reg t1 r12).val = exitSubStateBase loopBase n m := by rw [p1 r12 (by decide), hr12]
  have v1_13 : (reg t1 r13).val = 11 := by rw [r1_13] <;> rfl
  obtain ⟨t2, hs2, pc2, r2_13, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2_13 : (reg t2 r13).val = exitSubStateBase loopBase n m + 11 := by
    rw [r2_13, add_no_wrap _ _ (by rw [v1_12, v1_13]; exact hStFit), v1_12, v1_13]
  have hLoad2 : t2.data[(reg t2 r13).val]? = some ⟨exitPtrsBase loopBase n m, hL⟩ := by
    rw [d2, d1, v2_13]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hSt11
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t3, hs3, pc3, r3_13, p3, d3⟩ := step_loadData16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) hLoad2 (by rw [pc2] <;> exit_arith)
  have v3_13 : (reg t3 r13).val = exitPtrsBase loopBase n m := by rw [r3_13]
  have v3_2 : (reg t3 r2).val = n := by
    rw [p3 r2 (by decide), p2 r2 (by decide), p1 r2 (by decide), hRegs.entry.consts.nVal]
  obtain ⟨t4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_12 : (reg t4 r12).val = 2 * n := by
    rw [r4_12, add_no_wrap _ _ (by rw [v3_2] <;> exit_arith), v3_2] <;> exit_arith
  obtain ⟨t5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5_12 : (reg t5 r12).val = 4 * n := by
    rw [r5_12, add_no_wrap _ _ (by rw [v4_12] <;> exit_arith), v4_12] <;> exit_arith
  obtain ⟨t6, hs6, pc6, r6_14, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_14 : (reg t6 r14).val = 8 * n := by
    rw [r6_14, add_no_wrap _ _ (by rw [v5_12] <;> exit_arith), v5_12] <;> exit_arith
  have v6_12 : (reg t6 r12).val = 4 * n := by rw [p6 r12 (by decide), v5_12]
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_add16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = 12 * n := by
    rw [r7_12, add_no_wrap _ _ (by rw [v6_12, v6_14] <;> exit_arith), v6_12, v6_14] <;> exit_arith
  have v7_14 : (reg t7 r14).val = 8 * n := by rw [p7 r14 (by decide), v6_14]
  obtain ⟨t8, hs8, pc8, r8_14, p8, d8⟩ := step_add16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_14 : (reg t8 r14).val = 16 * n := by
    rw [r8_14, add_no_wrap _ _ (by rw [v7_14] <;> exit_arith), v7_14] <;> exit_arith
  obtain ⟨t9, hs9, pc9, r9_14, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_14 : (reg t9 r14).val = 32 * n := by
    rw [r9_14, add_no_wrap _ _ (by rw [v8_14] <;> exit_arith), v8_14] <;> exit_arith
  have v9_12 : (reg t9 r12).val = 12 * n := by rw [p9 r12 (by decide), p8 r12 (by decide), v7_12]
  obtain ⟨t10, hs10, pc10, r10_14, p10, d10⟩ := step_add16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith)
  have v10_14 : (reg t10 r14).val = 44 * n := by
    rw [r10_14, add_no_wrap _ _ (by rw [v9_12, v9_14] <;> exit_arith), v9_12, v9_14] <;> exit_arith
  have v10_13 : (reg t10 r13).val = exitPtrsBase loopBase n m := by
    rw [p10 r13 (by decide), p9 r13 (by decide), p8 r13 (by decide), p7 r13 (by decide),
      p6 r13 (by decide), p5 r13 (by decide), p4 r13 (by decide), v3_13]
  obtain ⟨t11, hs11, pc11, r11_13, p11, d11⟩ := step_sub16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_13 : (reg t11 r13).val = ownerForestPtrsBase loopBase n m := by
    have hSub : 44 * n ≤ exitPtrsBase loopBase n m := by
      rw [← ownerForestPtrsBase_add_44n loopBase n m] <;> exit_arith
    rw [r11_13, sub_exact (by rw [v10_14, v10_13]; exact hSub), v10_13, v10_14,
      ← ownerForestPtrsBase_add_44n loopBase n m] <;> exit_arith
  have v11_9 : (reg t11 r9).val = d := by
    rw [p11 r9 (by decide), p10 r9 (by decide), p9 r9 (by decide), p8 r9 (by decide),
      p7 r9 (by decide), p6 r9 (by decide), p5 r9 (by decide), p4 r9 (by decide),
      p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide), hRegs.dVal]
  obtain ⟨t12, hs12, pc12, r12_12, p12, d12⟩ := step_add16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have v12_12 : (reg t12 r12).val = 2 * d := by
    rw [r12_12, add_no_wrap _ _ (by rw [v11_9] <;> exit_arith), v11_9] <;> exit_arith
  obtain ⟨t13, hs13, pc13, r13_14, p13, d13⟩ := step_add16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith)
  have v13_14 : (reg t13 r14).val = 4 * d := by
    rw [r13_14, add_no_wrap _ _ (by rw [v12_12] <;> exit_arith), v12_12] <;> exit_arith
  have v13_12 : (reg t13 r12).val = 2 * d := by rw [p13 r12 (by decide), v12_12]
  obtain ⟨t14, hs14, pc14, r14_12, p14, d14⟩ := step_add16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13] <;> exit_arith)
  have v14_12 : (reg t14 r12).val = 6 * d := by
    rw [r14_12, add_no_wrap _ _ (by rw [v13_12, v13_14] <;> exit_arith), v13_12, v13_14] <;> exit_arith
  have v14_13 : (reg t14 r13).val = ownerForestPtrsBase loopBase n m := by
    rw [p14 r13 (by decide), p13 r13 (by decide), p12 r13 (by decide), v11_13]
  obtain ⟨t15, hs15, pc15, r15_13, p15, d15⟩ := step_add16 (input := input) (s := t14) (hPl.at 14 (by exit_rom_bound) (by exit_arith)) (by rw [pc14] <;> exit_arith)
  have v15_13 : (reg t15 r13).val = ownerForestPtrsBase loopBase n m + 6 * d := by
    rw [r15_13, add_no_wrap _ _ (by rw [v14_13, v14_12]; exact hFP6), v14_13, v14_12]
  have hKeep15 : ∀ r : Fin 16, r.val ≤ 10 → reg t15 r = reg s₀ r := by
    intro r hr
    rw [p15 r (by exit_arith), p14 r (by exit_arith), p13 r (by exit_arith), p12 r (by exit_arith),
      p11 r (by exit_arith), p10 r (by exit_arith), p9 r (by exit_arith), p8 r (by exit_arith),
      p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith), p4 r (by exit_arith),
      p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have v15_11 : (reg t15 r11).val = exitSubWorkBase loopBase n m workCap := by
    rw [p15 r11 (by exit_arith), p14 r11 (by exit_arith), p13 r11 (by exit_arith), p12 r11 (by exit_arith),
      p11 r11 (by exit_arith), p10 r11 (by exit_arith), p9 r11 (by exit_arith), p8 r11 (by exit_arith),
      p7 r11 (by exit_arith), p6 r11 (by exit_arith), p5 r11 (by exit_arith), p4 r11 (by exit_arith),
      p3 r11 (by exit_arith), p2 r11 (by exit_arith), p1 r11 (by exit_arith), hr11]
  have v15_15 : (reg t15 r15).val = exitSubInBase loopBase n m + 1 := by
    rw [p15 r15 (by exit_arith), p14 r15 (by exit_arith), p13 r15 (by exit_arith), p12 r15 (by exit_arith),
      p11 r15 (by exit_arith), p10 r15 (by exit_arith), p9 r15 (by exit_arith), p8 r15 (by exit_arith),
      p7 r15 (by exit_arith), p6 r15 (by exit_arith), p5 r15 (by exit_arith), p4 r15 (by exit_arith),
      p3 r15 (by exit_arith), p2 r15 (by exit_arith), p1 r15 (by exit_arith), hr15]
  have hSteps : Steps code input 15 s₀ t15 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (step1 hs15))))))))))))))
  have hPC15 : t15.pc = offLargeB + 15 := by
    rw [pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hData15 : t15.data = s₀.data := by
    rw [d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  exact ⟨t15, hSteps, hPC15, hData15, exitLoopRegs_of_keep hRegs hKeep15, v15_11, v15_13, v15_15⟩

private theorem exitLargeB2_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitLargeBCode h100) offLargeB)
    (hFit : offFp 0 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed fp4 fp5 : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offLargeB + 15) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr11 : (reg s₀ r11).val = exitSubWorkBase loopBase n m workCap)
    (hr13 : (reg s₀ r13).val = ownerForestPtrsBase loopBase n m + 6 * d)
    (hr15 : (reg s₀ r15).val = exitSubInBase loopBase n m + 1)
    (hfp4 : (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d + 4]?).map Fin.val = some fp4)
    (hfp5 : (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d + 5]?).map Fin.val = some fp5)
    (hfp4Le : fp4 ≤ fp5) (hfp5Lt : fp5 < workCap) (hd : d < Q) (hQn : Q ≤ n)
    (hSubInFit : exitSubInBase loopBase n m + 4 ≤ exitSubWorkBase loopBase n m workCap)
    (hSubWorkFit : exitSubWorkBase loopBase n m workCap + 2 ≤ workCap)
    (hDisjFP : ownerForestPtrsBase loopBase n m + 6 * Q ≤ exitArenaBase loopBase n m)
    (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 13 s₀ s1 ∧
      s1.pc = offFp 0 ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r15).val = exitSubInBase loopBase n m + 4 ∧
      (s1.data[exitSubWorkBase loopBase n m workCap + 1]?).map Fin.val =
        some (ownerForestPtrsBase loopBase n m + 6 * d) ∧
      (s1.data[exitSubInBase loopBase n m + 2]?).map Fin.val = some (fp5 - fp4) ∧
      (s1.data[exitSubInBase loopBase n m + 3]?).map Fin.val = some n ∧
      (∀ addr, addr ≠ exitSubWorkBase loopBase n m workCap + 1 →
        addr ≠ exitSubInBase loopBase n m + 2 → addr ≠ exitSubInBase loopBase n m + 3 →
        s1.data[addr]? = s₀.data[addr]?) := by
  have hFPBnd : ownerForestPtrsBase loopBase n m + 6 * d + 5 < 2 ^ bits := by
    have : ownerForestPtrsBase loopBase n m + 6 * Q < 2 ^ bits := by
      have hF := ownerForestPtrsBase_add_44n loopBase n m
      unfold exitSubWorkBase exitSubInBase exitSubStateBase exitArenaBase at hSubWorkFit
      omega
    exit_arith
  have hNeFPW : ∀ k < 6, ownerForestPtrsBase loopBase n m + 6 * d + k ≠ exitSubWorkBase loopBase n m workCap + 1 := by
    intro k hk
    have hF := ownerForestPtrsBase_add_44n loopBase n m
    simp only [exitSubWorkBase, exitSubInBase, exitSubStateBase, exitArenaBase]
    omega
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (input := input) (s := s₀) (hPl.at 15 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1_11 : (reg t1 r11).val = exitSubWorkBase loopBase n m workCap + 1 := by
    rw [r1_11, add_no_wrap _ _ (by rw [hr11, hRegs.entry.consts.one] <;> exit_arith), hr11, hRegs.entry.consts.one]
  have b1 : (reg t1 r11).val < t1.data.size := by rw [d1, hSz, v1_11] <;> exit_arith
  obtain ⟨t2, hs2, pc2, rg2, d2⟩ := step_storeData16 (input := input) (s := t1) (hPl.at 16 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith) b1
  have v2_13 : (reg t2 r13).val = ownerForestPtrsBase loopBase n m + 6 * d := by
    rw [reg_eq_of_regs_eq rg2 r13, p1 r13 (by decide), hr13]
  obtain ⟨t3, hs3, pc3, r3_12, p3, d3⟩ := step_imm16 (input := input) (s := t2) (hPl.at 17 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_13 : (reg t3 r13).val = ownerForestPtrsBase loopBase n m + 6 * d := by rw [p3 r13 (by decide), v2_13]
  have v3_12 : (reg t3 r12).val = 4 := by rw [r3_12] <;> rfl
  obtain ⟨t4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 18 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_12 : (reg t4 r12).val = ownerForestPtrsBase loopBase n m + 6 * d + 4 := by
    rw [r4_12, add_no_wrap _ _ (by rw [v3_13, v3_12] <;> exit_arith), v3_13, v3_12]
  have hLoad4 : t4.data[(reg t4 r12).val]? = some ⟨fp4, by omega⟩ := by
    rw [d4, d3, d2, Array.getElem?_set_ne _ (by rw [v1_11, v4_12]; exact Ne.symm (hNeFPW 4 (by decide))), d1, v4_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hfp4
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t5, hs5, pc5, r5_14, p5, d5⟩ := step_loadData16 (input := input) (s := t4) (hPl.at 19 (by exit_rom_bound) (by exit_arith)) hLoad4 (by rw [pc4] <;> exit_arith)
  have v5_14 : (reg t5 r14).val = fp4 := by rw [r5_14]
  have v5_12 : (reg t5 r12).val = ownerForestPtrsBase loopBase n m + 6 * d + 4 := by rw [p5 r12 (by decide), v4_12]
  have v5_1 : (reg t5 r1).val = 1 := by
    rw [p5 r1 (by decide), p4 r1 (by decide), p3 r1 (by decide), reg_eq_of_regs_eq rg2 r1,
      p1 r1 (by decide), hRegs.entry.consts.one]
  obtain ⟨t6, hs6, pc6, r6_12, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 20 (by exit_rom_bound) (by exit_arith)) (by rw [pc5] <;> exit_arith)
  have v6_12 : (reg t6 r12).val = ownerForestPtrsBase loopBase n m + 6 * d + 5 := by
    rw [r6_12, add_no_wrap _ _ (by rw [v5_12, v5_1] <;> exit_arith), v5_12, v5_1] <;> exit_arith
  have hLoad6 : t6.data[(reg t6 r12).val]? = some ⟨fp5, by omega⟩ := by
    rw [d6, d5, d4, d3, d2, Array.getElem?_set_ne _ (by rw [v1_11, v6_12]; exact Ne.symm (hNeFPW 5 (by decide))), d1, v6_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hfp5
    rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_loadData16 (input := input) (s := t6) (hPl.at 21 (by exit_rom_bound) (by exit_arith)) hLoad6 (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = fp5 := by rw [r7_12]
  have v7_14 : (reg t7 r14).val = fp4 := by rw [p7 r14 (by decide), p6 r14 (by decide), v5_14]
  obtain ⟨t8, hs8, pc8, r8_14, p8, d8⟩ := step_sub16 (input := input) (s := t7) (hPl.at 22 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_14 : (reg t8 r14).val = fp5 - fp4 := by
    rw [r8_14, sub_exact (by rw [v7_12, v7_14]; exact hfp4Le), v7_12, v7_14]
  have v8_15 : (reg t8 r15).val = exitSubInBase loopBase n m + 1 := by
    rw [p8 r15 (by decide), p7 r15 (by decide), p6 r15 (by decide), p5 r15 (by decide),
      p4 r15 (by decide), p3 r15 (by decide), reg_eq_of_regs_eq rg2 r15, p1 r15 (by decide), hr15]
  have v8_1 : (reg t8 r1).val = 1 := by
    rw [p8 r1 (by decide), p7 r1 (by decide), p6 r1 (by decide), v5_1]
  obtain ⟨t9, hs9, pc9, r9_15, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 23 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_15 : (reg t9 r15).val = exitSubInBase loopBase n m + 2 := by
    rw [r9_15, add_no_wrap _ _ (by rw [v8_15, v8_1] <;> exit_arith), v8_15, v8_1] <;> exit_arith
  have b9 : (reg t9 r15).val < t9.data.size := by
    rw [d9, d8, d7, d6, d5, d4, d3, d2, Array.size_set, d1, hSz, v9_15] <;> exit_arith
  obtain ⟨t10, hs10, pc10, rg10, d10⟩ := step_storeData16 (input := input) (s := t9) (hPl.at 24 (by exit_rom_bound) (by exit_arith)) (by rw [pc9] <;> exit_arith) b9
  have v10_15 : (reg t10 r15).val = exitSubInBase loopBase n m + 2 := by
    rw [reg_eq_of_regs_eq rg10 r15, v9_15]
  have v10_1 : (reg t10 r1).val = 1 := by rw [reg_eq_of_regs_eq rg10 r1, p9 r1 (by decide), v8_1]
  obtain ⟨t11, hs11, pc11, r11_15, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 25 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_15 : (reg t11 r15).val = exitSubInBase loopBase n m + 3 := by
    rw [r11_15, add_no_wrap _ _ (by rw [v10_15, v10_1] <;> exit_arith), v10_15, v10_1] <;> exit_arith
  have b11 : (reg t11 r15).val < t11.data.size := by
    rw [d11, d10, Array.size_set, d9, d8, d7, d6, d5, d4, d3, d2, Array.size_set, d1, hSz, v11_15] <;> exit_arith
  obtain ⟨t12, hs12, pc12, rg12, d12⟩ := step_storeData16 (input := input) (s := t11) (hPl.at 26 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith) b11
  have v12_15 : (reg t12 r15).val = exitSubInBase loopBase n m + 3 := by
    rw [reg_eq_of_regs_eq rg12 r15, v11_15]
  have v12_1 : (reg t12 r1).val = 1 := by
    rw [reg_eq_of_regs_eq rg12 r1, p11 r1 (by decide), v10_1]
  obtain ⟨t13, hs13, pc13, r13_15, p13, d13⟩ := step_add16 (input := input) (s := t12) (hPl.at 27 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith)
  have v13_15 : (reg t13 r15).val = exitSubInBase loopBase n m + 4 := by
    rw [r13_15, add_no_wrap _ _ (by rw [v12_15, v12_1] <;> exit_arith), v12_15, v12_1] <;> exit_arith
  have hSteps : Steps code input 13 s₀ t13 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (step1 hs13))))))))))))
  have hPC13 : t13.pc = offFp 0 := by
    rw [pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> rfl
  have hSz13 : t13.data.size = workCap := by
    rw [d13, d12, Array.size_set, d11, d10, Array.size_set, d9, d8, d7, d6, d5, d4, d3, d2,
      Array.size_set, d1, hSz]
  have hKeep13 : ∀ r : Fin 16, r.val ≤ 10 → reg t13 r = reg s₀ r := by
    intro r hr
    rw [p13 r (by exit_arith), reg_eq_of_regs_eq rg12 r, p11 r (by exit_arith), reg_eq_of_regs_eq rg10 r,
      p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith),
      p4 r (by exit_arith), p3 r (by exit_arith), reg_eq_of_regs_eq rg2 r, p1 r (by exit_arith)]
  have vr13_1 : (reg t1 r13).val = ownerForestPtrsBase loopBase n m + 6 * d := by
    rw [p1 r13 (by decide), hr13]
  have vr14_9 : (reg t9 r14).val = fp5 - fp4 := by rw [p9 r14 (by decide), v8_14]
  have vr2_11 : (reg t11 r2).val = n := by
    rw [p11 r2 (by decide), reg_eq_of_regs_eq rg10 r2, p9 r2 (by decide), p8 r2 (by decide),
      p7 r2 (by decide), p6 r2 (by decide), p5 r2 (by decide), p4 r2 (by decide),
      p3 r2 (by decide), reg_eq_of_regs_eq rg2 r2, p1 r2 (by decide), hRegs.entry.consts.nVal]
  have hNe2W : exitSubWorkBase loopBase n m workCap + 1 ≠ exitSubInBase loopBase n m + 2 := by
    omega
  have hNe3W : exitSubWorkBase loopBase n m workCap + 1 ≠ exitSubInBase loopBase n m + 3 := by
    omega
  have hAtW1 : (t13.data[exitSubWorkBase loopBase n m workCap + 1]?).map Fin.val =
      some (ownerForestPtrsBase loopBase n m + 6 * d) := by
    rw [d13, d12, Array.getElem?_set_ne _ (by rw [v11_15]; exact Ne.symm hNe3W), d11, d10,
      Array.getElem?_set_ne _ (by rw [v9_15]; exact Ne.symm hNe2W), d9, d8, d7, d6, d5, d4, d3, d2,
      show exitSubWorkBase loopBase n m workCap + 1 = (reg t1 r11).val from v1_11.symm,
      Array.getElem?_set_self, Option.map_some, vr13_1]
  have hAtIn2 : (t13.data[exitSubInBase loopBase n m + 2]?).map Fin.val = some (fp5 - fp4) := by
    rw [d13, d12, Array.getElem?_set_ne _ (by rw [v11_15] <;> exit_arith), d11, d10,
      show exitSubInBase loopBase n m + 2 = (reg t9 r15).val from v9_15.symm,
      Array.getElem?_set_self, Option.map_some, vr14_9]
  have hAtIn3 : (t13.data[exitSubInBase loopBase n m + 3]?).map Fin.val = some n := by
    rw [d13, d12, show exitSubInBase loopBase n m + 3 = (reg t11 r15).val from v11_15.symm,
      Array.getElem?_set_self, Option.map_some, vr2_11]
  have hFr13 : ∀ addr, addr ≠ exitSubWorkBase loopBase n m workCap + 1 →
      addr ≠ exitSubInBase loopBase n m + 2 → addr ≠ exitSubInBase loopBase n m + 3 →
      t13.data[addr]? = s₀.data[addr]? := by
    intro addr h1 h2 h3
    rw [d13, d12, Array.getElem?_set_ne _ (by rw [v11_15]; exact h3.symm), d11, d10,
      Array.getElem?_set_ne _ (by rw [v9_15]; exact h2.symm), d9, d8, d7, d6, d5, d4, d3, d2,
      Array.getElem?_set_ne _ (by rw [v1_11]; exact h1.symm), d1]
  exact ⟨t13, hSteps, hPC13, hSz13, exitLoopRegs_of_keep hRegs hKeep13, v13_15, hAtW1, hAtIn2, hAtIn3, hFr13⟩

theorem exitLargeB_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code (exitLargeBCode h100) offLargeB)
    (hFit : offFp 0 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed fp4 fp5 : Nat}
    {s₀ : State L16} (hPC : s₀.pc = offLargeB) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    (hr11 : (reg s₀ r11).val = exitSubWorkBase loopBase n m workCap)
    (hr12 : (reg s₀ r12).val = exitSubStateBase loopBase n m)
    (hr15 : (reg s₀ r15).val = exitSubInBase loopBase n m + 1)
    (hSt11 : (s₀.data[exitSubStateBase loopBase n m + 11]?).map Fin.val = some (exitPtrsBase loopBase n m))
    (hfp4 : (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d + 4]?).map Fin.val = some fp4)
    (hfp5 : (s₀.data[ownerForestPtrsBase loopBase n m + 6 * d + 5]?).map Fin.val = some fp5)
    (hfp4Le : fp4 ≤ fp5) (hfp5Lt : fp5 < workCap) (hd : d < Q) (hQn : Q ≤ n)
    (hSubInFit : exitSubInBase loopBase n m + 4 ≤ exitSubWorkBase loopBase n m workCap)
    (hSubWorkFit : exitSubWorkBase loopBase n m workCap + 2 ≤ workCap)
    (hDisjFP : ownerForestPtrsBase loopBase n m + 6 * Q ≤ exitArenaBase loopBase n m)
    (hEnd : exitArenaBase loopBase n m ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input 28 s₀ s1 ∧
      s1.pc = offFp 0 ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r15).val = exitSubInBase loopBase n m + 4 ∧
      (s1.data[exitSubWorkBase loopBase n m workCap + 1]?).map Fin.val =
        some (ownerForestPtrsBase loopBase n m + 6 * d) ∧
      (s1.data[exitSubInBase loopBase n m + 2]?).map Fin.val = some (fp5 - fp4) ∧
      (s1.data[exitSubInBase loopBase n m + 3]?).map Fin.val = some n ∧
      (∀ addr, addr ≠ exitSubWorkBase loopBase n m workCap + 1 →
        addr ≠ exitSubInBase loopBase n m + 2 → addr ≠ exitSubInBase loopBase n m + 3 →
        s1.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨s1, hs1, pc1, hd1, regs1, r1_11, r1_13, r1_15⟩ :=
    exitLargeB1_steps h100 hPl (by simp only [offLargeB, offFp] at hFit ⊢ <;> exit_arith) hPC hSz hRegs
      hr11 hr12 hr15 hd hQn hSt11 hEnd hBits
  have hSz1 : s1.data.size = workCap := by rw [hd1, hSz]
  obtain ⟨s2, hs2, pc2, sz2, regs2, r2_15, hw1, hin2, hin3, hfr2⟩ :=
    exitLargeB2_steps h100 hPl hFit pc1 hSz1 regs1 r1_11 r1_13 r1_15
      (by rw [hd1]; exact hfp4) (by rw [hd1]; exact hfp5) hfp4Le hfp5Lt hd hQn
      hSubInFit hSubWorkFit hDisjFP hBits
  exact ⟨s2, hs1.append hs2, pc2, sz2, regs2, r2_15, hw1, hin2, hin3,
    fun a h1 h2 h3 => by rw [hfr2 a h1 h2 h3, hd1]⟩

/-! #### Block 4: `copyFromFpBlock` and `copyFromEmitBlock` -/

end SmallStepHelpers

end PaperB.RamExitFamilyLoop
