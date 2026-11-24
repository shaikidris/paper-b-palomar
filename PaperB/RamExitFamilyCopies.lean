module

public import PaperB.RamExitFamilyRom
public import PaperB.RamExitFamilyInit
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

private theorem copyMiddlePlacement {code pre mid post : Array (Instr bits 16)}
    {base width : Nat} (hWidth : pre.size = width)
    (hPlace : SlicePlaced (hi := hi) (hw := hw) code (pre ++ mid ++ post) base) :
    SlicePlaced (hi := hi) (hw := hw) code mid (base + width) := by
  intro j hj
  have hBound : width + j < (pre ++ mid ++ post).size := by
    simp only [Array.size_append, hWidth]
    omega
  have hFetch := hPlace (width + j) hBound
  have hEq : (pre ++ mid ++ post)[width + j]? = some (mid[j]'hj) := by
    rw [Array.getElem?_append_left (by simp only [Array.size_append, hWidth]; omega),
      Array.getElem?_append_right (by rw [hWidth]; omega), hWidth,
      show width + j - width = j by omega]
    exact Array.getElem?_eq_getElem hj
  rw [Array.getElem?_eq_getElem hBound] at hEq
  rw [← Nat.add_assoc] at hFetch
  exact hFetch.trans hEq

private theorem copyLastPlacement {code pre mid : Array (Instr bits 16)}
    {base width : Nat} (op : Instr bits 16) (hWidth : (pre ++ mid).size = width)
    (hPlace : SlicePlaced (hi := hi) (hw := hw) code (pre ++ mid ++ #[op]) base) :
    code[base + width]? = some op := by
  have hBound : width < (pre ++ mid ++ #[op]).size := by
    rw [Array.size_append, hWidth]
    change width < width + 1
    omega
  have h := hPlace width hBound
  have hEq : (pre ++ mid ++ #[op])[width]? = some op := by
    rw [Array.getElem?_append_right (by rw [hWidth] <;> omega), hWidth, Nat.sub_self]
    rfl
  rwa [← Array.getElem?_eq_getElem hBound, hEq] at h

theorem copyFromFpBlock_steps {code : Program L16} {input : Input L16}
    (h100 : 100 ≤ 2 ^ bits) {base idx lenIdx : Nat} (hidx : idx < 100) (hlen : lenIdx < 100)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code
      (copyFromFpBlock (hi := hi) (hw := hw) h100 base idx lenIdx hidx hlen) base)
    (hFit : base + 19 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = base) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    {fpPtrBase src₀ len dst₀ : Nat}
    (hMem0 : (s₀.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hMem1 : (s₀.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hW1 : (s₀.data[exitSubWorkBase loopBase n m workCap + 1]?).map Fin.val = some fpPtrBase)
    (hFpIdx : (s₀.data[fpPtrBase + idx]?).map Fin.val = some src₀)
    (hInLen : (s₀.data[exitSubInBase loopBase n m + lenIdx]?).map Fin.val = some len)
    (hr15 : (reg s₀ r15).val = dst₀)
    (hSrcBound : src₀ + len ≤ exitSubInBase loopBase n m)
    (hDstLo : exitSubInBase loopBase n m ≤ dst₀)
    (hDstBound : dst₀ + len ≤ workCap) (hBits : workCap < 2 ^ bits) :
    ∃ s1 : State L16,
      Steps code input (6 * len + 14) s₀ s1 ∧
      s1.pc = base + 19 ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r15).val = dst₀ + len ∧
      (∀ j < len, s1.data[dst₀ + j]? = s₀.data[src₀ + j]?) ∧
      (∀ addr, (addr < dst₀ ∨ dst₀ + len ≤ addr) → s1.data[addr]? = s₀.data[addr]?) := by
  have hInLt : exitSubInBase loopBase n m < 2 ^ bits := by exit_arith
  have hWork1Lt : exitSubWorkBase loopBase n m workCap + 1 < 2 ^ bits := by
    obtain ⟨w1, hw1, _⟩ := Option.map_eq_some_iff.mp hW1
    have hLt := (Array.getElem?_eq_some_iff.mp hw1).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  have hFpIdxLt : fpPtrBase + idx < 2 ^ bits := by
    obtain ⟨wf, hwf, _⟩ := Option.map_eq_some_iff.mp hFpIdx
    have hLt := (Array.getElem?_eq_some_iff.mp hwf).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  have hInLenLt : exitSubInBase loopBase n m + lenIdx < 2 ^ bits := by
    obtain ⟨wl, hwl, _⟩ := Option.map_eq_some_iff.mp hInLen
    have hLt := (Array.getElem?_eq_some_iff.mp hwl).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  have hOne : (reg s₀ r1).val = 1 := hRegs.entry.consts.one
  have hLoad0 : s₀.data[(reg s₀ r1).val]? = some ⟨exitSubWorkBase loopBase n m workCap, by exit_arith⟩ := by
    rw [hOne]; change s₀.data[dataPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem1; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_loadData16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) hLoad0 (by rw [hPC] <;> exit_arith)
  have v1_11 : (reg t1 r11).val = exitSubWorkBase loopBase n m workCap := by rw [r1_11]
  have v1_1 : (reg t1 r1).val = 1 := by rw [p1 r1 (by decide), hOne]
  obtain ⟨t2, hs2, pc2, r2_11, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2_11 : (reg t2 r11).val = exitSubWorkBase loopBase n m workCap + 1 := by
    rw [r2_11, add_no_wrap _ _ (by rw [v1_11, v1_1] <;> exit_arith), v1_11, v1_1]
  obtain ⟨wFp, hFpAt, hFpVal⟩ := Option.map_eq_some_iff.mp hW1
  have hFpFit : fpPtrBase < 2 ^ bits := hFpVal ▸ wFp.isLt
  have hLoad2 : t2.data[(reg t2 r11).val]? = some ⟨fpPtrBase, hFpFit⟩ := by
    rw [d2, d1, v2_11, hFpAt]
    exact congrArg some (Fin.ext hFpVal)
  obtain ⟨t3, hs3, pc3, r3_11, p3, d3⟩ := step_loadData16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) hLoad2 (by rw [pc2] <;> exit_arith)
  have v3_11 : (reg t3 r11).val = fpPtrBase := by rw [r3_11]
  obtain ⟨t4, hs4, pc4, r4_12, p4, d4⟩ := step_imm16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_11 : (reg t4 r11).val = fpPtrBase := by rw [p4 r11 (by decide), v3_11]
  have v4_12 : (reg t4 r12).val = idx := by rw [r4_12] <;> rfl
  obtain ⟨t5, hs5, pc5, r5_11, p5, d5⟩ := step_add16 (input := input) (s := t4) (hPl.at 4 (by exit_rom_bound) (by exit_arith)) (by rw [pc4] <;> exit_arith)
  have v5_11 : (reg t5 r11).val = fpPtrBase + idx := by
    rw [r5_11, add_no_wrap _ _ (by rw [v4_11, v4_12]; exact hFpIdxLt), v4_11, v4_12]
  have hLoad5 : t5.data[(reg t5 r11).val]? = some ⟨src₀, by exit_arith⟩ := by
    rw [d5, d4, d3, d2, d1, v5_11]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hFpIdx; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t6, hs6, pc6, r6_11, p6, d6⟩ := step_loadData16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) hLoad5 (by rw [pc5] <;> exit_arith)
  have v6_11 : (reg t6 r11).val = src₀ := by rw [r6_11]
  have v6_0 : (reg t6 r0).val = 0 := by
    rw [p6 r0 (by decide), p5 r0 (by decide), p4 r0 (by decide), p3 r0 (by decide),
      p2 r0 (by decide), p1 r0 (by decide), hRegs.entry.consts.zero]
  have hLoad6 : t6.data[(reg t6 r0).val]? = some ⟨exitSubInBase loopBase n m, hInLt⟩ := by
    rw [d6, d5, d4, d3, d2, d1, v6_0]; change s₀.data[inPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem0; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_loadData16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) hLoad6 (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = exitSubInBase loopBase n m := by rw [r7_12]
  obtain ⟨t8, hs8, pc8, r8_13, p8, d8⟩ := step_imm16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = exitSubInBase loopBase n m := by rw [p8 r12 (by decide), v7_12]
  have v8_13 : (reg t8 r13).val = lenIdx := by rw [r8_13] <;> rfl
  obtain ⟨t9, hs9, pc9, r9_12, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_12 : (reg t9 r12).val = exitSubInBase loopBase n m + lenIdx := by
    rw [r9_12, add_no_wrap _ _ (by rw [v8_12, v8_13]; exact hInLenLt), v8_12, v8_13]
  have hLoad9 : t9.data[(reg t9 r12).val]? = some ⟨len, by exit_arith⟩ := by
    rw [d9, d8, d7, d6, d5, d4, d3, d2, d1, v9_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hInLen; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t10, hs10, pc10, r10_13, p10, d10⟩ := step_loadData16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) hLoad9 (by rw [pc9] <;> exit_arith)
  have v10_13 : (reg t10 r13).val = len := by rw [r10_13]
  have v10_11 : (reg t10 r11).val = src₀ := by
    rw [p10 r11 (by decide), p9 r11 (by decide), p8 r11 (by decide), p7 r11 (by decide), v6_11]
  obtain ⟨t11, hs11, pc11, r11_13, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_13 : (reg t11 r13).val = src₀ + len := by
    rw [r11_13, add_no_wrap _ _ (by rw [v10_11, v10_13] <;> exit_arith), v10_11, v10_13]
  have v11_15 : (reg t11 r15).val = dst₀ := by
    rw [p11 r15 (by decide), p10 r15 (by decide), p9 r15 (by decide), p8 r15 (by decide),
      p7 r15 (by decide), p6 r15 (by decide), p5 r15 (by decide), p4 r15 (by decide),
      p3 r15 (by decide), p2 r15 (by decide), p1 r15 (by decide), hr15]
  obtain ⟨t12, hs12, pc12, r12_12, p12, d12⟩ := step_mov16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) (by rw [pc11] <;> exit_arith)
  have hKeep12 : ∀ r : Fin 16, r.val ≤ 10 → reg t12 r = reg s₀ r := by
    intro r hr
    rw [p12 r (by exit_arith), p11 r (by exit_arith), p10 r (by exit_arith), p9 r (by exit_arith),
      p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith), p5 r (by exit_arith),
      p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have hPC12 : t12.pc = base + 12 := by
    rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC] <;> exit_arith
  have hData12 : t12.data = s₀.data := by
    rw [d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hPlCopy : SlicePlaced (hi := hi) (hw := hw) code
      (copyLoopCode (hi := hi) (hw := hw) (base + 12) (base + 18)) (base + 12) := by
    unfold copyFromFpBlock at hPl
    exact copyMiddlePlacement (hi := hi) (hw := hw) rfl hPl
  obtain ⟨t13, kC, hkC, hs13, pc13, sz13, _, r13_12, _, p13, hCp13, hFr13⟩ :=
    run_copyLoop16 (input := input) (exitPC := base + 18)
      (src₀ := src₀) (dst₀ := dst₀) (len := len) hPlCopy (by exit_arith) (by exit_arith) hBits (by exit_arith) hDstBound
      (Or.inr (Or.inl (by exit_arith))) hPC12 (by rw [hData12, hSz])
      (by rw [hKeep12 r1 (by decide), hOne])
      (by rw [p12 r11 (by decide), p11 r11 (by decide), v10_11])
      (by rw [r12_12, v11_15])
      (by rw [p12 r13 (by decide), v11_13])
  have hf18 : code[t13.pc]? = some (.mov r15 r12) := by
    rw [pc13]
    unfold copyFromFpBlock at hPl
    exact copyLastPlacement (hi := hi) (hw := hw) (.mov r15 r12) rfl hPl
  obtain ⟨t14, hs14, pc14, r14_15, p14, d14⟩ := step_mov16 (input := input) (s := t13) hf18 (by rw [pc13] <;> exit_arith)
  have hSteps : Steps code input (6 * len + 14) s₀ t14 := by
    have h12 : Steps code input 12 s₀ t12 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
        (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
          (Steps.cons hs11 (step1 hs12)))))))))))
    have hAll := h12.append (hs13.append (step1 hs14))
    rwa [hkC, show 12 + (6 * len + 1 + 1) = 6 * len + 14 by exit_arith] at hAll
  have hKeep14 : ∀ r : Fin 16, r.val ≤ 10 → reg t14 r = reg s₀ r := by
    intro r hr
    rw [p14 r (by exit_arith), p13 r (by exit_arith) (by exit_arith) (by exit_arith), hKeep12 r hr]
  refine ⟨t14, hSteps, by rw [pc14, pc13] <;> exit_arith, by rw [d14, sz13],
    exitLoopRegs_of_keep hRegs hKeep14, by rw [r14_15, r13_12],
    fun j hj => by rw [d14, hCp13 j hj, hData12],
    fun a ha => by rw [d14, hFr13 a ha, hData12]⟩

theorem copyFromEmitBlock_steps {code : Program L16} {input : Input L16}
    {base : Nat} (col : Fin 3)
    (hPl : SlicePlaced (hi := hi) (hw := hw) code
      (copyFromEmitBlock (hi := hi) (hw := hw) base col) base)
    (hFit : base + 21 < code.size)
    {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {s₀ : State L16} (hPC : s₀.pc = base) (hSz : s₀.data.size = workCap)
    (hRegs : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s₀)
    {qStart m_d dst₀ : Nat}
    (hMem0 : (s₀.data[inPtrAddr]?).map Fin.val = some (exitSubInBase loopBase n m))
    (hMem1 : (s₀.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase loopBase n m workCap))
    (hW0 : (s₀.data[exitSubWorkBase loopBase n m workCap]?).map Fin.val = some qStart)
    (hIn1 : (s₀.data[exitSubInBase loopBase n m + 1]?).map Fin.val = some m_d)
    (hr15 : (reg s₀ r15).val = dst₀)
    (hmBound : qStart + m_d ≤ m)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ exitSubInBase loopBase n m)
    (hDstLo : exitSubInBase loopBase n m ≤ dst₀)
    (hDstBound : dst₀ + m_d ≤ workCap) (hBits : workCap < 2 ^ bits) :
    let src₀ := emitBase + 3 * n + 1 + col.val * m + qStart
    ∃ s1 : State L16,
      Steps code input (6 * m_d + 16) s₀ s1 ∧
      s1.pc = base + 21 ∧
      s1.data.size = workCap ∧
      ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s1 ∧
      (reg s1 r15).val = dst₀ + m_d ∧
      (∀ j < m_d, s1.data[dst₀ + j]? = s₀.data[src₀ + j]?) ∧
      (∀ addr, (addr < dst₀ ∨ dst₀ + m_d ≤ addr) → s1.data[addr]? = s₀.data[addr]?) := by
  intro src₀
  have hInLt : exitSubInBase loopBase n m + 1 < 2 ^ bits := by
    obtain ⟨_, hSome, _⟩ := Option.map_eq_some_iff.mp hIn1
    have hAddr := (Array.getElem?_eq_some_iff.mp hSome).1
    exact Nat.lt_trans (hSz ▸ hAddr) hBits
  have hW0Lt : exitSubWorkBase loopBase n m workCap < 2 ^ bits := by
    obtain ⟨w0, hw0, _⟩ := Option.map_eq_some_iff.mp hW0
    have hLt := (Array.getElem?_eq_some_iff.mp hw0).1; rw [hSz] at hLt; exact Nat.lt_trans hLt hBits
  have hEmitBnd : emitBase + 3 * n + 1 + 2 * m + qStart + m_d < 2 ^ bits := by
    unfold emitterWorkWords at hEmitFit <;> exit_arith
  have hCM : col.val * m ≤ 2 * m := Nat.mul_le_mul_right m (Nat.le_of_lt_succ col.isLt)
  have hColBnd : emitBase + 3 * n + 1 + col.val * m < 2 ^ bits := by
    unfold emitterWorkWords at hEmitFit
    omega
  have hSrcIn : src₀ + m_d ≤ exitSubInBase loopBase n m := by
    dsimp only [src₀]
    unfold emitterWorkWords at hEmitFit
    omega
  have hOne : (reg s₀ r1).val = 1 := hRegs.entry.consts.one
  have hN : (reg s₀ r2).val = n := hRegs.entry.consts.nVal
  have hM : (reg s₀ r3).val = m := hRegs.entry.consts.mVal
  have hEmit : (reg s₀ r7).val = emitBase := hRegs.entry.emitBaseVal
  obtain ⟨t1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (input := input) (s := s₀) (hPl.at 0 (by exit_rom_bound) (by exit_arith)) (by rw [hPC] <;> exit_arith)
  have v1_11 : (reg t1 r11).val = 2 * n := by
    rw [r1_11, add_no_wrap _ _ (by rw [hN] <;> exit_arith), hN] <;> exit_arith
  have v1_2 : (reg t1 r2).val = n := by rw [p1 r2 (by decide), hN]
  obtain ⟨t2, hs2, pc2, r2_11, p2, d2⟩ := step_add16 (input := input) (s := t1) (hPl.at 1 (by exit_rom_bound) (by exit_arith)) (by rw [pc1] <;> exit_arith)
  have v2_11 : (reg t2 r11).val = 3 * n := by
    rw [r2_11, add_no_wrap _ _ (by rw [v1_11, v1_2] <;> exit_arith), v1_11, v1_2] <;> exit_arith
  have v2_7 : (reg t2 r7).val = emitBase := by rw [p2 r7 (by decide), p1 r7 (by decide), hEmit]
  obtain ⟨t3, hs3, pc3, r3_11, p3, d3⟩ := step_add16 (input := input) (s := t2) (hPl.at 2 (by exit_rom_bound) (by exit_arith)) (by rw [pc2] <;> exit_arith)
  have v3_11 : (reg t3 r11).val = emitBase + 3 * n := by
    rw [r3_11, add_no_wrap _ _ (by rw [v2_7, v2_11] <;> exit_arith), v2_7, v2_11]
  have v3_1 : (reg t3 r1).val = 1 := by
    rw [p3 r1 (by decide), p2 r1 (by decide), p1 r1 (by decide), hOne]
  obtain ⟨t4, hs4, pc4, r4_11, p4, d4⟩ := step_add16 (input := input) (s := t3) (hPl.at 3 (by exit_rom_bound) (by exit_arith)) (by rw [pc3] <;> exit_arith)
  have v4_11 : (reg t4 r11).val = emitBase + 3 * n + 1 := by
    rw [r4_11, add_no_wrap _ _ (by rw [v3_11, v3_1] <;> exit_arith), v3_11, v3_1]
  have hKeep4 : ∀ r : Fin 16, r.val ≤ 10 → reg t4 r = reg s₀ r := by
    intro r hr; rw [p4 r (by exit_arith), p3 r (by exit_arith), p2 r (by exit_arith), p1 r (by exit_arith)]
  have hc4 : ∃ (t5 : State L16), step code input t4 = some (.next t5) ∧ t5.pc = base + 5 ∧
      (reg t5 r12).val = col.val * m ∧ (∀ r : Fin 16, r ≠ r12 → reg t5 r = reg t4 r) ∧
      t5.data = t4.data := by
    rcases col with ⟨c, hc⟩
    have hC : c = 0 ∨ c = 1 ∨ c = 2 := by exit_arith
    rcases hC with rfl | rfl | rfl
    · have hAt : code[t4.pc]? = some (.add r12 r0 r0) :=
        hPl.at 4 (by exit_rom_bound) (by exit_arith)
      obtain ⟨t5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (input := input) (s := t4) hAt (by rw [pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
      refine ⟨t5, hs5, by rw [pc5, pc4, pc3, pc2, pc1, hPC], ?_, p5, d5⟩
      rw [r5_12, add_no_wrap _ _ (by rw [hKeep4 r0 (by decide), hRegs.entry.consts.zero] <;> exit_arith),
        hKeep4 r0 (by decide), hRegs.entry.consts.zero] <;> exit_arith
    · have hAt : code[t4.pc]? = some (.add r12 r0 r3) :=
        hPl.at 4 (by exit_rom_bound) (by exit_arith)
      obtain ⟨t5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (input := input) (s := t4) hAt (by rw [pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
      refine ⟨t5, hs5, by rw [pc5, pc4, pc3, pc2, pc1, hPC], ?_, p5, d5⟩
      rw [r5_12, add_no_wrap _ _ (by rw [hKeep4 r0 (by decide), hRegs.entry.consts.zero,
          hKeep4 r3 (by decide), hM] <;> exit_arith),
        hKeep4 r0 (by decide), hRegs.entry.consts.zero, hKeep4 r3 (by decide), hM] <;> exit_arith
    · have hAt : code[t4.pc]? = some (.add r12 r3 r3) :=
        hPl.at 4 (by exit_rom_bound) (by exit_arith)
      obtain ⟨t5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (input := input) (s := t4) hAt (by rw [pc4, pc3, pc2, pc1, hPC] <;> exit_arith)
      refine ⟨t5, hs5, by rw [pc5, pc4, pc3, pc2, pc1, hPC], ?_, p5, d5⟩
      rw [r5_12, add_no_wrap _ _ (by rw [hKeep4 r3 (by decide), hM] <;> exit_arith),
        hKeep4 r3 (by decide), hM] <;> exit_arith
  obtain ⟨t5, hs5, pc5, v5_12, p5, d5⟩ := hc4
  have v5_11 : (reg t5 r11).val = emitBase + 3 * n + 1 := by rw [p5 r11 (by decide), v4_11]
  have pc5' : t5.pc = base + 5 := pc5
  obtain ⟨t6, hs6, pc6, r6_11, p6, d6⟩ := step_add16 (input := input) (s := t5) (hPl.at 5 (by exit_rom_bound) (by exit_arith)) (by rw [pc5'] <;> exit_arith)
  have v6_11 : (reg t6 r11).val = emitBase + 3 * n + 1 + col.val * m := by
    rw [r6_11, add_no_wrap _ _ (by rw [v5_11, v5_12]; exact hColBnd), v5_11, v5_12]
  have v6_1 : (reg t6 r1).val = 1 := by
    rw [p6 r1 (by decide), p5 r1 (by decide), hKeep4 r1 (by decide), hOne]
  have hLoad6 : t6.data[(reg t6 r1).val]? = some ⟨exitSubWorkBase loopBase n m workCap, by exit_arith⟩ := by
    rw [d6, d5, d4, d3, d2, d1, v6_1]; change s₀.data[dataPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem1; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t7, hs7, pc7, r7_12, p7, d7⟩ := step_loadData16 (input := input) (s := t6) (hPl.at 6 (by exit_rom_bound) (by exit_arith)) hLoad6 (by rw [pc6] <;> exit_arith)
  have v7_12 : (reg t7 r12).val = exitSubWorkBase loopBase n m workCap := by rw [r7_12]
  have hLoad7 : t7.data[(reg t7 r12).val]? = some ⟨qStart, by exit_arith⟩ := by
    rw [d7, d6, d5, d4, d3, d2, d1, v7_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hW0; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t8, hs8, pc8, r8_12, p8, d8⟩ := step_loadData16 (input := input) (s := t7) (hPl.at 7 (by exit_rom_bound) (by exit_arith)) hLoad7 (by rw [pc7] <;> exit_arith)
  have v8_12 : (reg t8 r12).val = qStart := by rw [r8_12]
  have v8_11 : (reg t8 r11).val = emitBase + 3 * n + 1 + col.val * m := by
    rw [p8 r11 (by decide), p7 r11 (by decide), v6_11]
  obtain ⟨t9, hs9, pc9, r9_11, p9, d9⟩ := step_add16 (input := input) (s := t8) (hPl.at 8 (by exit_rom_bound) (by exit_arith)) (by rw [pc8] <;> exit_arith)
  have v9_11 : (reg t9 r11).val = src₀ := by
    rw [r9_11, add_no_wrap _ _ (by rw [v8_11, v8_12]; dsimp only [src₀] at *; exit_arith), v8_11, v8_12]
  have v9_0 : (reg t9 r0).val = 0 := by
    rw [p9 r0 (by decide), p8 r0 (by decide), p7 r0 (by decide), p6 r0 (by decide),
      p5 r0 (by decide), hKeep4 r0 (by decide), hRegs.entry.consts.zero]
  have hLoad9 : t9.data[(reg t9 r0).val]? = some ⟨exitSubInBase loopBase n m, by exit_arith⟩ := by
    rw [d9, d8, d7, d6, d5, d4, d3, d2, d1, v9_0]; change s₀.data[inPtrAddr]? = _
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hMem0; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t10, hs10, pc10, r10_12, p10, d10⟩ := step_loadData16 (input := input) (s := t9) (hPl.at 9 (by exit_rom_bound) (by exit_arith)) hLoad9 (by rw [pc9] <;> exit_arith)
  have v10_12 : (reg t10 r12).val = exitSubInBase loopBase n m := by rw [r10_12]
  have v10_1 : (reg t10 r1).val = 1 := by
    rw [p10 r1 (by decide), p9 r1 (by decide), p8 r1 (by decide), p7 r1 (by decide), v6_1]
  obtain ⟨t11, hs11, pc11, r11_12, p11, d11⟩ := step_add16 (input := input) (s := t10) (hPl.at 10 (by exit_rom_bound) (by exit_arith)) (by rw [pc10] <;> exit_arith)
  have v11_12 : (reg t11 r12).val = exitSubInBase loopBase n m + 1 := by
    rw [r11_12, add_no_wrap _ _ (by rw [v10_12, v10_1] <;> exit_arith), v10_12, v10_1]
  have hLoad11 : t11.data[(reg t11 r12).val]? = some ⟨m_d, by exit_arith⟩ := by
    rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, v11_12]
    obtain ⟨w, hwM, hwV⟩ := Option.map_eq_some_iff.mp hIn1; rw [hwM]; congr 1; exact Fin.ext hwV
  obtain ⟨t12, hs12, pc12, r12_13, p12, d12⟩ := step_loadData16 (input := input) (s := t11) (hPl.at 11 (by exit_rom_bound) (by exit_arith)) hLoad11 (by rw [pc11] <;> exit_arith)
  have v12_13 : (reg t12 r13).val = m_d := by rw [r12_13]
  have v12_11 : (reg t12 r11).val = src₀ := by
    rw [p12 r11 (by decide), p11 r11 (by decide), p10 r11 (by decide), v9_11]
  obtain ⟨t13, hs13, pc13, r13_13, p13, d13⟩ := step_add16 (input := input) (s := t12) (hPl.at 12 (by exit_rom_bound) (by exit_arith)) (by rw [pc12] <;> exit_arith)
  have v13_13 : (reg t13 r13).val = src₀ + m_d := by
    rw [r13_13, add_no_wrap _ _ (by rw [v12_11, v12_13]; dsimp only [src₀] at *; exit_arith), v12_11, v12_13]
  have hKeep13 : ∀ r : Fin 16, r.val ≤ 10 → reg t13 r = reg s₀ r := by
    intro r hr
    rw [p13 r (by exit_arith), p12 r (by exit_arith), p11 r (by exit_arith), p10 r (by exit_arith),
      p9 r (by exit_arith), p8 r (by exit_arith), p7 r (by exit_arith), p6 r (by exit_arith),
      p5 r (by exit_arith), hKeep4 r hr]
  have v13_15 : (reg t13 r15).val = dst₀ := by rw [p13 r15 (by decide), p12 r15 (by decide),
    p11 r15 (by decide), p10 r15 (by decide), p9 r15 (by decide), p8 r15 (by decide),
    p7 r15 (by decide), p6 r15 (by decide), p5 r15 (by decide), p4 r15 (by decide),
    p3 r15 (by decide), p2 r15 (by decide), p1 r15 (by decide), hr15]
  have pc13' : t13.pc = base + 13 := by
    rw [pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5'] <;> exit_arith
  obtain ⟨t14, hs14, pc14, r14_12, p14, d14⟩ := step_mov16 (input := input) (s := t13) (hPl.at 13 (by exit_rom_bound) (by exit_arith)) (by rw [pc13'] <;> exit_arith)
  have hKeep14 : ∀ r : Fin 16, r.val ≤ 10 → reg t14 r = reg s₀ r := by
    intro r hr; rw [p14 r (by exit_arith), hKeep13 r hr]
  have hData14 : t14.data = s₀.data := by
    rw [d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hPC14 : t14.pc = base + 14 := by rw [pc14, pc13']
  have hPlCopy : SlicePlaced (hi := hi) (hw := hw) code
      (copyLoopCode (hi := hi) (hw := hw) (base + 14) (base + 20)) (base + 14) := by
    unfold copyFromEmitBlock at hPl
    exact copyMiddlePlacement (hi := hi) (hw := hw) rfl hPl
  obtain ⟨t15, kC, hkC, hs15, pc15, sz15, _, r15_12, _, p15, hCp15, hFr15⟩ :=
    run_copyLoop16 (input := input) (exitPC := base + 20)
      (src₀ := src₀) (dst₀ := dst₀) (len := m_d) hPlCopy (by exit_arith) (by exit_arith) hBits (by exit_arith) hDstBound
      (Or.inr (Or.inl (by exit_arith))) hPC14 (by rw [hData14, hSz])
      (by rw [hKeep14 r1 (by decide), hOne])
      (by rw [p14 r11 (by decide), p13 r11 (by decide), v12_11])
      (by rw [r14_12, v13_15])
      (by rw [p14 r13 (by decide), v13_13])
  have hf20 : code[t15.pc]? = some (.mov r15 r12) := by
    rw [pc15]
    unfold copyFromEmitBlock at hPl
    exact copyLastPlacement (hi := hi) (hw := hw) (.mov r15 r12) rfl hPl
  obtain ⟨t16, hs16, pc16, r16_15, p16, d16⟩ := step_mov16 (input := input) (s := t15) hf20 (by rw [pc15] <;> exit_arith)
  have hSteps : Steps code input (6 * m_d + 16) s₀ t16 := by
    have h14 : Steps code input 14 s₀ t14 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
        (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
          (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (step1 hs14)))))))))))))
    have hAll := h14.append (hs15.append (step1 hs16))
    rwa [hkC, show 14 + (6 * m_d + 1 + 1) = 6 * m_d + 16 by exit_arith] at hAll
  have hKeep16 : ∀ r : Fin 16, r.val ≤ 10 → reg t16 r = reg s₀ r := by
    intro r hr; rw [p16 r (by exit_arith), p15 r (by exit_arith) (by exit_arith) (by exit_arith), hKeep14 r hr]
  refine ⟨t16, hSteps, by rw [pc16, pc15] <;> exit_arith, by rw [d16, sz15],
    exitLoopRegs_of_keep hRegs hKeep16, by rw [r16_15, r15_12],
    fun j hj => by rw [d16, hCp15 j hj, hData14],
    fun a ha => by rw [d16, hFr15 a ha, hData14]⟩

/-! #### Block 5: `exitSaveRegs` (`281..303`, `23` steps) and `exitRestoreRegs` (`24` steps) -/


end SmallStepHelpers

end PaperB.RamExitFamilyLoop
