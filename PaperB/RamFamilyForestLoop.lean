module

public import PaperB.RamFamilyForestLoopProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! Execution and resource proofs for the family forest loop. -/

namespace PaperB.RamFamilyForestLoop

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (zero add sub ltb ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.RamForestProgram.Sweep
open PaperB.RamForestProgram.ArcDecode
open PaperB.RamForestProgram.ArcParents
open PaperB.RamDataSliceAdapter
open PaperB.RamQuotientEmitter
open PaperB.RetainedProperLoss
open PaperB.ForestSlimIndex
open PaperB.ForestHead (Vertex)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next)
open PaperB.ForestIncomingRaw (Entry supplied arcHead)
open _root_.EX24.PreparedSweep (orderedConfig)

section PhaseSimulations

open PaperB.WordOps (add_no_wrap)

private theorem loopInitA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offInit) (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hDataSz : s₀.data.size = workCap)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    ∃ s14, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 14 s₀ s14 ∧
      s14.pc = offInit + 14 ∧
      s14.data.size = workCap ∧
      LoopEntryRegs n m root Q treeBase emitBase loopBase s14 ∧
      (reg s14 r9).val = 0 ∧
      (reg s14 r10).val = 0 ∧
      (reg s14 r11).val = loopSubWorkBase loopBase n m + 32 * n ∧
      s14.data[inPtrAddr]? = some ⟨loopBase, by unfold loopWorkWords at hFit; omega⟩ ∧
      s14.data[dataPtrAddr]? = some ⟨loopSubWorkBase loopBase n m, by
        unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega⟩ ∧
      (∀ k, k ≠ inPtrAddr → k ≠ dataPtrAddr → s14.data[k]? = s₀.data[k]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 15 → offInit + c < code.size := by
    intro c hc; rw [hSz]; unfold offInit; omega
  have hZeroVal : (reg s₀ rZero).val = 0 := hRegs.consts.zero
  have hOneVal : (reg s₀ rOne).val = 1 := hRegs.consts.one
  have hNVal : (reg s₀ rN).val = n := hRegs.consts.nVal
  have hMVal : (reg s₀ rM).val = m := hRegs.consts.mVal
  have hRootVal : (reg s₀ rRoot).val = root := hRegs.consts.rootVal
  have hQVal : (reg s₀ r5).val = Q := hRegs.qVal
  have hTVal : (reg s₀ r6).val = treeBase := hRegs.treeBaseVal
  have hEVal : (reg s₀ r7).val = emitBase := hRegs.emitBaseVal
  have hLVal : (reg s₀ r8).val = loopBase := hRegs.loopBaseVal
  have hBoundWork : loopBase + (3 + 2 * m) + 32 * n < 2 ^ bits := by
    unfold loopWorkWords at hFit; omega
  have h0Lt : 0 < s₀.data.size := by rw [hDataSz]; unfold loopWorkWords at hFit; omega
  have h1Lt : 1 < s₀.data.size := by rw [hDataSz]; unfold loopWorkWords at hFit; omega
  -- 0: mov r9 rZero
  obtain ⟨s1, st0, pc1, r9_1, keep1, d1⟩ :=
    step16_mov code input hpc (at_init subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  -- 1: mov r10 rZero
  obtain ⟨s2, st1, pc2, r10_2, keep2, d2⟩ :=
    step16_mov code input pc1 (at_init subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
  -- 2: storeData rZero r8
  have hBnd2 : (reg s2 rZero).val < s2.data.size := by
    rw [d2, d1, keep2 _ (by decide), keep1 _ (by decide), hZeroVal]; exact h0Lt
  obtain ⟨s3, st2, pc3, regs3, d3⟩ :=
    step16_storeData code input pc2 (at_init subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide)) hBnd2
  have reg3 : ∀ r : Fin 16, reg s3 r = reg s2 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs3 r
  -- 3: add r12 rM rM
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_init subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have r12v4 : (reg s4 r12).val = 2 * m := by
    rw [r12_4, add_no_wrap]
    · rw [reg3, keep2 _ (by decide), keep1 _ (by decide), hMVal]; omega
    · rw [reg3, keep2 _ (by decide), keep1 _ (by decide), hMVal]; omega
  -- 4: imm r13 3
  obtain ⟨s5, st4, pc5, r13_5, keep5, d5⟩ :=
    step16_imm code input pc4 (at_init subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  -- 5: add r12 r12 r13
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_init subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = 3 + 2 * m := by
    rw [r12_6, add_no_wrap]
    · rw [keep5 _ (by decide), r12v4, r13_5]; change 2 * m + 3 = 3 + 2 * m; omega
    · rw [keep5 _ (by decide), r12v4, r13_5]; change 2 * m + 3 < 2 ^ bits; omega
  -- 6: add r11 r8 r12
  obtain ⟨s7, st6, pc7, r11_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_init subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have h8eq6 : (reg s6 r8).val = loopBase := by
    rw [keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), reg3,
      keep2 _ (by decide), keep1 _ (by decide), hLVal]
  have r11v7 : (reg s7 r11).val = loopSubWorkBase loopBase n m := by
    rw [r11_7, add_no_wrap]
    · rw [h8eq6, r12v6]; unfold loopSubWorkBase rawInputCap; rfl
    · rw [h8eq6, r12v6]; omega
  -- 7: storeData rOne r11
  have h1eq7 : (reg s7 rOne).val = 1 := by
    rw [keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      reg3, keep2 _ (by decide), keep1 _ (by decide), hOneVal]
  have hBnd7 : (reg s7 rOne).val < s7.data.size := by
    rw [h1eq7, d7, d6, d5, d4, d3, Array.size_set, d2, d1]; exact h1Lt
  obtain ⟨s8, st7, pc8, regs8, d8⟩ :=
    step16_storeData code input pc7 (at_init subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide)) hBnd7
  have reg8 : ∀ r : Fin 16, reg s8 r = reg s7 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs8 r
  -- 8..12: 32 * n in r12
  have h2eq8 : (reg s8 rN).val = n := by
    rw [reg8, keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      reg3, keep2 _ (by decide), keep1 _ (by decide), hNVal]
  obtain ⟨s9, st8, pc9, r12_9, keep9, d9⟩ :=
    step16_add code input pc8 (at_init subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
  have r12v9 : (reg s9 r12).val = 2 * n := by
    rw [r12_9, add_no_wrap] <;> rw [h2eq8] <;> omega
  obtain ⟨s10, st9, pc10, r12_10, keep10, d10⟩ :=
    step16_add code input pc9 (at_init subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  have r12v10 : (reg s10 r12).val = 4 * n := by
    rw [r12_10, add_no_wrap] <;> rw [r12v9] <;> omega
  obtain ⟨s11, st10, pc11, r12_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_init subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have r12v11 : (reg s11 r12).val = 8 * n := by
    rw [r12_11, add_no_wrap] <;> rw [r12v10] <;> omega
  obtain ⟨s12, st11, pc12, r12_12, keep12, d12⟩ :=
    step16_add code input pc11 (at_init subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
  have r12v12 : (reg s12 r12).val = 16 * n := by
    rw [r12_12, add_no_wrap] <;> rw [r12v11] <;> omega
  obtain ⟨s13, st12, pc13, r12_13, keep13, d13⟩ :=
    step16_add code input pc12 (at_init subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
  have r12v13 : (reg s13 r12).val = 32 * n := by
    rw [r12_13, add_no_wrap] <;> rw [r12v12] <;> omega
  -- 13: add r11 r11 r12
  obtain ⟨s14, st13, pc14, r11_14, keep14, d14⟩ :=
    step16_add code input pc13 (at_init subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have r11eq13 : (reg s13 r11).val = loopSubWorkBase loopBase n m := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), reg8, r11v7]
  have r11v14 : (reg s14 r11).val = loopSubWorkBase loopBase n m + 32 * n := by
    rw [r11_14, add_no_wrap]
    · rw [r11eq13, r12v13]
    · rw [r11eq13, r12v13]; unfold loopSubWorkBase rawInputCap; omega
  have hSteps : Steps code input 14 s₀ s14 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3
      (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.cons st7
        (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11
          (Steps.cons st12 (Steps.cons st13 (Steps.zero s14))))))))))))))
  have hDataSize14 : s14.data.size = workCap := by
    rw [d14, d13, d12, d11, d10, d9, d8, Array.size_set, d7, d6, d5, d4, d3, Array.size_set, d2, d1, hDataSz]
  have hInAddr : (reg s2 rZero).val = inPtrAddr := by
    rw [keep2 _ (by decide), keep1 _ (by decide), hZeroVal]; rfl
  have hDataAddr : (reg s7 rOne).val = dataPtrAddr := by rw [h1eq7]; rfl
  have hDataAt : ∀ k, (if k = dataPtrAddr then some ⟨loopSubWorkBase loopBase n m, by
        unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega⟩
      else if k = inPtrAddr then some ⟨loopBase, by unfold loopWorkWords at hFit; omega⟩
      else s₀.data[k]?) = s14.data[k]? := by
    intro k
    rw [d14, d13, d12, d11, d10, d9, d8]
    by_cases hk1 : k = dataPtrAddr
    · subst hk1
      rw [ite_eq_left rfl, mem_set_same s7.data hDataAddr hBnd7]
      exact congrArg some (Fin.ext r11v7.symm)
    · rw [ite_eq_right hk1, mem_set_ne s7.data hBnd7 (fun e => hk1 (e.trans hDataAddr))]
      rw [d7, d6, d5, d4, d3]
      by_cases hk0 : k = inPtrAddr
      · subst hk0
        rw [ite_eq_left rfl, mem_set_same s2.data hInAddr hBnd2]
        exact congrArg some (Fin.ext (by
          rw [keep2 _ (by decide), keep1 _ (by decide), hLVal]))
      · rw [ite_eq_right hk0, mem_set_ne s2.data hBnd2 (fun e => hk0 (e.trans hInAddr)), d2, d1]
  refine ⟨s14, hSteps, pc14, hDataSize14, ?_, ?_, ?_, r11v14, ?_, ?_, ?_⟩
  · refine
      { consts :=
          { zero := by
              rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
                keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
                keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide), hZeroVal]
            one := by
              rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
                keep10 _ (by decide), keep9 _ (by decide), reg8, h1eq7]
            nVal := by
              rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
                keep10 _ (by decide), keep9 _ (by decide), h2eq8]
            mVal := by
              rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
                keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
                keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide), hMVal]
            rootVal := by
              rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
                keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
                keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide), hRootVal] }
        qVal := by
          rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
            keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
            keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide), hQVal]
        treeBaseVal := by
          rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
            keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
            keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide), hTVal]
        emitBaseVal := by
          rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
            keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
            keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide), hEVal]
        loopBaseVal := by
          rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
            keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), h8eq6] }
  · rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
      keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
      keep5 _ (by decide), keep4 _ (by decide), reg3, keep2 _ (by decide), r9_1, hZeroVal]
  · rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
      keep10 _ (by decide), keep9 _ (by decide), reg8, keep7 _ (by decide), keep6 _ (by decide),
      keep5 _ (by decide), keep4 _ (by decide), reg3, r10_2]
    rw [keep1 _ (by decide), hZeroVal]
  · rw [← hDataAt inPtrAddr]; rfl
  · rw [← hDataAt dataPtrAddr]; rfl
  · intro k hk0 hk1
    rw [← hDataAt k]
    simp [hk0, hk1]

/-- Registers during outer loop iteration `d` with `forestUsed` words allocated in `forestArena`. -/
structure LoopIterRegs (n m root Q treeBase emitBase loopBase d forestUsed : Nat)
    {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  entry : LoopEntryRegs n m root Q treeBase emitBase loopBase s
  dVal : (reg s r9).val = d
  usedVal : (reg s r10).val = forestUsed

private theorem loopEntryRegs_of_keep {n m root Q treeBase emitBase loopBase : Nat}
    {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {s t : State (layout16 bits inputCap workCap hi hw)}
    (h : LoopEntryRegs n m root Q treeBase emitBase loopBase s)
    (hKeep : ∀ r : Fin 16, r.val ≤ 8 → reg t r = reg s r) :
    LoopEntryRegs n m root Q treeBase emitBase loopBase t where
  consts :=
    { zero := (congrArg Fin.val (hKeep rZero (by decide))).trans h.consts.zero
      one := (congrArg Fin.val (hKeep rOne (by decide))).trans h.consts.one
      nVal := (congrArg Fin.val (hKeep rN (by decide))).trans h.consts.nVal
      mVal := (congrArg Fin.val (hKeep rM (by decide))).trans h.consts.mVal
      rootVal := (congrArg Fin.val (hKeep rRoot (by decide))).trans h.consts.rootVal }
  qVal := (congrArg Fin.val (hKeep r5 (by decide))).trans h.qVal
  treeBaseVal := (congrArg Fin.val (hKeep r6 (by decide))).trans h.treeBaseVal
  emitBaseVal := (congrArg Fin.val (hKeep r7 (by decide))).trans h.emitBaseVal
  loopBaseVal := (congrArg Fin.val (hKeep r8 (by decide))).trans h.loopBaseVal

private theorem loopIterRegs_of_keep {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {s t : State (layout16 bits inputCap workCap hi hw)}
    (h : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s)
    (hKeep : ∀ r : Fin 16, r.val ≤ 10 → reg t r = reg s r) :
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t where
  entry := loopEntryRegs_of_keep h.entry (fun r hr => hKeep r (by omega))
  dVal := (congrArg Fin.val (hKeep r9 (by decide))).trans h.dVal
  usedVal := (congrArg Fin.val (hKeep r10 (by decide))).trans h.usedVal

private theorem loopInitB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase : Nat}
    {s14 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s14.pc = offInit + 14) (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s14)
    (hr11 : (reg s14 r11).val = loopSubWorkBase loopBase n m + 32 * n)
    (hDataSz : s14.data.size = workCap)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    ∃ s28, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 14 s14 s28 ∧
      s28.pc = offInit + 28 ∧
      s28.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s28 ∧
      (reg s28 r11).val = loopSubStateBase loopBase n m ∧
      (reg s28 r12).val = loopDegBase loopBase n m ∧
      s28.data[statePtrAddr]? = some ⟨loopSubStateBase loopBase n m, by
        unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s28.data[loopSubStateBase loopBase n m + 11]? = some ⟨loopDegBase loopBase n m, by
        unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      (∀ k, k ≠ statePtrAddr → k ≠ loopSubStateBase loopBase n m + 11 → s28.data[k]? = s14.data[k]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 29 → offInit + c < code.size := by
    intro c hc; rw [hSz]; unfold offInit; omega
  have hMVal : (reg s14 rM).val = m := hRegs.entry.consts.mVal
  have hStateBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hMLt : 7 * m < 2 ^ bits := by
    unfold loopWorkWords at hFit; omega
  have hSubWorkLt : loopSubWorkBase loopBase n m + 32 * n + 7 * m + 17 < 2 ^ bits := by
    unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
  have hStLt : loopSubStateBase loopBase n m < 2 ^ bits := by omega
  have hDegLt : loopDegBase loopBase n m < 2 ^ bits := by
    unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  -- 14..18: 7 * m in r14
  obtain ⟨s15, st14, pc15, r13_15, keep15, d15⟩ :=
    step16_add code input hpc (at_init subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have r13v15 : (reg s15 r13).val = 2 * m := by
    rw [r13_15, add_no_wrap] <;> rw [hMVal] <;> omega
  obtain ⟨s16, st15, pc16, r14_16, keep16, d16⟩ :=
    step16_add code input pc15 (at_init subCode h32 (i := 15) (by decide)) (hPcLt 16 (by decide))
  have r14v16 : (reg s16 r14).val = 4 * m := by
    rw [r14_16, add_no_wrap] <;> rw [r13v15] <;> omega
  obtain ⟨s17, st16, pc17, r14_17, keep17, d17⟩ :=
    step16_add code input pc16 (at_init subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have r13eq16 : (reg s16 r13).val = 2 * m := (congrArg Fin.val (keep16 _ (by decide))).trans r13v15
  have r14v17 : (reg s17 r14).val = 6 * m := by
    rw [r14_17, add_no_wrap] <;> rw [r14v16, r13eq16] <;> omega
  obtain ⟨s18, st17, pc18, r14_18, keep18, d18⟩ :=
    step16_add code input pc17 (at_init subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide))
  have hMeq17 : (reg s17 rM).val = m := by
    rw [keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide), hMVal]
  have r14v18 : (reg s18 r14).val = 7 * m := by
    rw [r14_18, add_no_wrap] <;> rw [r14v17, hMeq17] <;> omega
  -- 18: add r11 r11 r14
  obtain ⟨s19, st18, pc19, r11_19, keep19, d19⟩ :=
    step16_add code input pc18 (at_init subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  have r11eq18 : (reg s18 r11).val = loopSubWorkBase loopBase n m + 32 * n := by
    rw [keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide), hr11]
  have r11v19 : (reg s19 r11).val = loopSubWorkBase loopBase n m + 32 * n + 7 * m := by
    rw [r11_19, add_no_wrap]
    · rw [r11eq18, r14v18]
    · rw [r11eq18, r14v18]; omega
  -- 19: imm r13 17; 20: add r11 r11 r13 -> r11 = loopSubStateBase
  obtain ⟨s20, st19, pc20, r13_20, keep20, d20⟩ :=
    step16_imm code input pc19 (at_init subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  obtain ⟨s21, st20, pc21, r11_21, keep21, d21⟩ :=
    step16_add code input pc20 (at_init subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide))
  have r11v21 : (reg s21 r11).val = loopSubStateBase loopBase n m := by
    rw [r11_21, add_no_wrap]
    · rw [keep20 _ (by decide), r11v19, r13_20]
      unfold loopSubStateBase rawWorkCap; change _ + 17 = _; omega
    · rw [keep20 _ (by decide), r11v19, r13_20]
      change _ + 17 < 2 ^ bits; omega
  -- 21: imm r13 2; 22: storeData r13 r11
  obtain ⟨s22, st21, pc22, r13_22, keep22, d22⟩ :=
    step16_imm code input pc21 (at_init subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
  have hAddr22 : (reg s22 r13).val = statePtrAddr := by rw [r13_22]; rfl
  have hBnd22 : (reg s22 r13).val < s22.data.size := by
    rw [hAddr22, d22, d21, d20, d19, d18, d17, d16, d15, hDataSz]
    unfold statePtrAddr loopWorkWords at *; omega
  obtain ⟨s23, st22, pc23, regs23, d23⟩ :=
    step16_storeData code input pc22 (at_init subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide)) hBnd22
  have reg23 : ∀ r : Fin 16, reg s23 r = reg s22 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs23 r
  -- 23: imm r12 16; 24: add r12 r11 r12 -> loopDegBase
  obtain ⟨s24, st23, pc24, r12_24, keep24, d24⟩ :=
    step16_imm code input pc23 (at_init subCode h32 (i := 23) (by decide)) (hPcLt 24 (by decide))
  obtain ⟨s25, st24, pc25, r12_25, keep25, d25⟩ :=
    step16_add code input pc24 (at_init subCode h32 (i := 24) (by decide)) (hPcLt 25 (by decide))
  have r11eq24 : (reg s24 r11).val = loopSubStateBase loopBase n m := by
    rw [keep24 _ (by decide), reg23, keep22 _ (by decide), r11v21]
  have r12v25 : (reg s25 r12).val = loopDegBase loopBase n m := by
    rw [r12_25, add_no_wrap]
    · rw [r11eq24, r12_24]; unfold loopDegBase; rfl
    · rw [r11eq24, r12_24]; exact hDegLt
  -- 25: imm r13 11; 26: add r14 r11 r13; 27: storeData r14 r12
  obtain ⟨s26, st25, pc26, r13_26, keep26, d26⟩ :=
    step16_imm code input pc25 (at_init subCode h32 (i := 25) (by decide)) (hPcLt 26 (by decide))
  obtain ⟨s27, st26, pc27, r14_27, keep27, d27⟩ :=
    step16_add code input pc26 (at_init subCode h32 (i := 26) (by decide)) (hPcLt 27 (by decide))
  have r11eq26 : (reg s26 r11).val = loopSubStateBase loopBase n m := by
    rw [keep26 _ (by decide), keep25 _ (by decide), r11eq24]
  have hAddr27 : (reg s27 r14).val = loopSubStateBase loopBase n m + 11 := by
    rw [r14_27, add_no_wrap]
    · rw [r11eq26, r13_26]; rfl
    · rw [r11eq26, r13_26]; change loopSubStateBase loopBase n m + 11 < 2 ^ bits; omega
  have hDataSz27 : s27.data.size = workCap := by
    rw [d27, d26, d25, d24, d23, Array.size_set, d22, d21, d20, d19, d18, d17, d16, d15, hDataSz]
  have hBnd27 : (reg s27 r14).val < s27.data.size := by rw [hAddr27, hDataSz27]; omega
  obtain ⟨s28, st27, pc28, regs28, d28⟩ :=
    step16_storeData code input pc27 (at_init subCode h32 (i := 27) (by decide)) (hPcLt 28 (by decide)) hBnd27
  have reg28 : ∀ r : Fin 16, reg s28 r = reg s27 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs28 r
  have hSteps : Steps code input 14 s14 s28 :=
    Steps.cons st14 (Steps.cons st15 (Steps.cons st16 (Steps.cons st17
      (Steps.cons st18 (Steps.cons st19 (Steps.cons st20 (Steps.cons st21
        (Steps.cons st22 (Steps.cons st23 (Steps.cons st24 (Steps.cons st25
          (Steps.cons st26 (Steps.cons st27 (Steps.zero s28))))))))))))))
  have hDataSz28 : s28.data.size = workCap := by rw [d28, Array.size_set, hDataSz27]
  have hRegs28 : LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s28 := by
    refine loopIterRegs_of_keep hRegs fun r hr => ?_
    have hne11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have hne12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have hne13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have hne14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    rw [reg28, keep27 _ hne14, keep26 _ hne13, keep25 _ hne12, keep24 _ hne12, reg23,
      keep22 _ hne13, keep21 _ hne11, keep20 _ hne13, keep19 _ hne11, keep18 _ hne14,
      keep17 _ hne14, keep16 _ hne14, keep15 _ hne13]
  have r11v28 : (reg s28 r11).val = loopSubStateBase loopBase n m := by
    rw [reg28, keep27 _ (by decide), r11eq26]
  have r12v28 : (reg s28 r12).val = loopDegBase loopBase n m := by
    rw [reg28, keep27 _ (by decide), keep26 _ (by decide), r12v25]
  have hDataAt : ∀ k, (if k = loopSubStateBase loopBase n m + 11 then some ⟨loopDegBase loopBase n m, hDegLt⟩
      else if k = statePtrAddr then some ⟨loopSubStateBase loopBase n m, hStLt⟩
      else s14.data[k]?) = s28.data[k]? := by
    intro k
    rw [d28]
    by_cases hkB : k = loopSubStateBase loopBase n m + 11
    · subst hkB
      rw [ite_eq_left rfl, mem_set_same s27.data hAddr27 hBnd27]
      exact congrArg some (Fin.ext (by rw [keep27 _ (by decide), keep26 _ (by decide), r12v25]))
    · rw [ite_eq_right hkB, mem_set_ne s27.data hBnd27 (fun e => hkB (e.trans hAddr27))]
      rw [d27, d26, d25, d24, d23]
      by_cases hkA : k = statePtrAddr
      · subst hkA
        rw [ite_eq_left rfl, mem_set_same s22.data hAddr22 hBnd22]
        exact congrArg some (Fin.ext (by rw [keep22 _ (by decide), r11v21]))
      · rw [ite_eq_right hkA, mem_set_ne s22.data hBnd22 (fun e => hkA (e.trans hAddr22)),
          d22, d21, d20, d19, d18, d17, d16, d15]
  refine ⟨s28, hSteps, pc28,
    hDataSz28, hRegs28, r11v28, r12v28, ?_, ?_, ?_⟩
  · rw [← hDataAt statePtrAddr]
    have hne : statePtrAddr ≠ loopSubStateBase loopBase n m + 11 := by
      unfold statePtrAddr loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
    rw [ite_eq_right hne, ite_eq_left rfl]
  · rw [← hDataAt (loopSubStateBase loopBase n m + 11)]
    rw [ite_eq_left rfl]
  · intro k hk1 hk2; rw [← hDataAt k]
    rw [ite_eq_right hk2, ite_eq_right hk1]

private theorem loopInitC_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase : Nat}
    {s28 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s28.pc = offInit + 28) (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s28)
    (hr11 : (reg s28 r11).val = loopSubStateBase loopBase n m)
    (hr12 : (reg s28 r12).val = loopDegBase loopBase n m)
    (hDataSz : s28.data.size = workCap)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    ∃ s48, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 20 s28 s48 ∧
      s48.pc = offHdr ∧
      s48.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s48 ∧
      s48.data[loopSubStateBase loopBase n m + 12]? = some ⟨loopCursorBase loopBase n m, by
        unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 13]? = some ⟨loopSortEntryBase loopBase n m, by
        unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 14]? = some ⟨ownerForestPtrsBase loopBase n m, by
        unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 15]? = some ⟨forestArenaBase loopBase n m, by
        unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      (∀ k, (k < loopSubStateBase loopBase n m + 12 ∨ loopSubStateBase loopBase n m + 16 ≤ k) →
        s48.data[k]? = s28.data[k]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 49 → offInit + c < code.size := by
    intro c hc; rw [hSz]; unfold offInit; omega
  have hOne : (reg s28 rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s28 rN).val = n := hRegs.entry.consts.nVal
  have hM : (reg s28 rM).val = m := hRegs.entry.consts.mVal
  have hStateBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hNLt : 32 * n < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hMLt : 7 * m < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hCurLt : loopCursorBase loopBase n m < 2 ^ bits := by
    unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hCurNLt : loopCursorBase loopBase n m + n < 2 ^ bits := by
    unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hEntLt : loopSortEntryBase loopBase n m < 2 ^ bits := by
    unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hPtrLt : ownerForestPtrsBase loopBase n m < 2 ^ bits := by
    unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hArenaLt : forestArenaBase loopBase n m < 2 ^ bits := by
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  -- 28: add r12 r12 r2 -> loopCursorBase
  obtain ⟨s29, st28, pc29, r12_29, keep29, d29⟩ :=
    step16_add code input hpc (at_init subCode h32 (i := 28) (by decide)) (hPcLt 29 (by decide))
  have r12v29 : (reg s29 r12).val = loopCursorBase loopBase n m := by
    rw [r12_29, add_no_wrap]
    · rw [hr12, hN]; rfl
    · rw [hr12, hN]; exact hCurLt
  -- 29: imm r13 12; 30: add r14 r11 r13; 31: storeData r14 r12
  obtain ⟨s30, st29, pc30, r13_30, keep30, d30⟩ :=
    step16_imm code input pc29 (at_init subCode h32 (i := 29) (by decide)) (hPcLt 30 (by decide))
  obtain ⟨s31, st30, pc31, r14_31, keep31, d31⟩ :=
    step16_add code input pc30 (at_init subCode h32 (i := 30) (by decide)) (hPcLt 31 (by decide))
  have r11eq30 : (reg s30 r11).val = loopSubStateBase loopBase n m := by
    rw [keep30 _ (by decide), keep29 _ (by decide), hr11]
  have hAddr31 : (reg s31 r14).val = loopSubStateBase loopBase n m + 12 := by
    rw [r14_31, add_no_wrap]
    · rw [r11eq30, r13_30]; rfl
    · rw [r11eq30, r13_30]; change _ + 12 < 2 ^ bits; omega
  have hBnd31 : (reg s31 r14).val < s31.data.size := by
    rw [hAddr31, d31, d30, d29, hDataSz]; omega
  obtain ⟨s32, st31, pc32, regs32, d32⟩ :=
    step16_storeData code input pc31 (at_init subCode h32 (i := 31) (by decide)) (hPcLt 32 (by decide)) hBnd31
  have reg32 : ∀ r : Fin 16, reg s32 r = reg s31 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs32 r
  -- 32: add r12 r12 r2; 33: add r12 r12 r1 -> loopSortEntryBase
  have r12eq32 : (reg s32 r12).val = loopCursorBase loopBase n m := by
    rw [reg32, keep31 _ (by decide), keep30 _ (by decide), r12v29]
  have hNeq32 : (reg s32 rN).val = n := by
    rw [reg32, keep31 _ (by decide), keep30 _ (by decide), keep29 _ (by decide), hN]
  have h1eq32 : (reg s32 rOne).val = 1 := by
    rw [reg32, keep31 _ (by decide), keep30 _ (by decide), keep29 _ (by decide), hOne]
  obtain ⟨s33, st32, pc33, r12_33, keep33, d33⟩ :=
    step16_add code input pc32 (at_init subCode h32 (i := 32) (by decide)) (hPcLt 33 (by decide))
  have r12v33 : (reg s33 r12).val = loopCursorBase loopBase n m + n := by
    rw [r12_33, add_no_wrap]
    · rw [r12eq32, hNeq32]
    · rw [r12eq32, hNeq32]; exact hCurNLt
  obtain ⟨s34, st33, pc34, r12_34, keep34, d34⟩ :=
    step16_add code input pc33 (at_init subCode h32 (i := 33) (by decide)) (hPcLt 34 (by decide))
  have r12v34 : (reg s34 r12).val = loopSortEntryBase loopBase n m := by
    rw [r12_34, add_no_wrap]
    · rw [r12v33, keep33 _ (by decide), h1eq32]; rfl
    · rw [r12v33, keep33 _ (by decide), h1eq32]; exact hEntLt
  -- 34: imm r13 13; 35: add r14 r11 r13; 36: storeData r14 r12
  obtain ⟨s35, st34, pc35, r13_35, keep35, d35⟩ :=
    step16_imm code input pc34 (at_init subCode h32 (i := 34) (by decide)) (hPcLt 35 (by decide))
  obtain ⟨s36, st35, pc36, r14_36, keep36, d36⟩ :=
    step16_add code input pc35 (at_init subCode h32 (i := 35) (by decide)) (hPcLt 36 (by decide))
  have r11eq35 : (reg s35 r11).val = loopSubStateBase loopBase n m := by
    rw [keep35 _ (by decide), keep34 _ (by decide), keep33 _ (by decide), reg32,
      keep31 _ (by decide), r11eq30]
  have hAddr36 : (reg s36 r14).val = loopSubStateBase loopBase n m + 13 := by
    rw [r14_36, add_no_wrap]
    · rw [r11eq35, r13_35]; rfl
    · rw [r11eq35, r13_35]; change _ + 13 < 2 ^ bits; omega
  have hBnd36 : (reg s36 r14).val < s36.data.size := by
    rw [hAddr36, d36, d35, d34, d33, d32, Array.size_set, d31, d30, d29, hDataSz]; omega
  obtain ⟨s37, st36, pc37, regs37, d37⟩ :=
    step16_storeData code input pc36 (at_init subCode h32 (i := 36) (by decide)) (hPcLt 37 (by decide)) hBnd36
  have reg37 : ∀ r : Fin 16, reg s37 r = reg s36 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs37 r
  -- 37: add r12 r12 r3 -> ownerForestPtrsBase
  have r12eq37 : (reg s37 r12).val = loopSortEntryBase loopBase n m := by
    rw [reg37, keep36 _ (by decide), keep35 _ (by decide), r12v34]
  have hMeq37 : (reg s37 rM).val = m := by
    rw [reg37, keep36 _ (by decide), keep35 _ (by decide), keep34 _ (by decide),
      keep33 _ (by decide), reg32, keep31 _ (by decide), keep30 _ (by decide), keep29 _ (by decide), hM]
  obtain ⟨s38, st37, pc38, r12_38, keep38, d38⟩ :=
    step16_add code input pc37 (at_init subCode h32 (i := 37) (by decide)) (hPcLt 38 (by decide))
  have r12v38 : (reg s38 r12).val = ownerForestPtrsBase loopBase n m := by
    rw [r12_38, add_no_wrap]
    · rw [r12eq37, hMeq37]; rfl
    · rw [r12eq37, hMeq37]; exact hPtrLt
  -- 38: imm r13 14; 39: add r14 r11 r13; 40: storeData r14 r12
  obtain ⟨s39, st38, pc39, r13_39, keep39, d39⟩ :=
    step16_imm code input pc38 (at_init subCode h32 (i := 38) (by decide)) (hPcLt 39 (by decide))
  obtain ⟨s40, st39, pc40, r14_40, keep40, d40⟩ :=
    step16_add code input pc39 (at_init subCode h32 (i := 39) (by decide)) (hPcLt 40 (by decide))
  have r11eq39 : (reg s39 r11).val = loopSubStateBase loopBase n m := by
    rw [keep39 _ (by decide), keep38 _ (by decide), reg37, keep36 _ (by decide), r11eq35]
  have hAddr40 : (reg s40 r14).val = loopSubStateBase loopBase n m + 14 := by
    rw [r14_40, add_no_wrap]
    · rw [r11eq39, r13_39]; rfl
    · rw [r11eq39, r13_39]; change _ + 14 < 2 ^ bits; omega
  have hBnd40 : (reg s40 r14).val < s40.data.size := by
    rw [hAddr40, d40, d39, d38, d37, Array.size_set, d36, d35, d34, d33, d32, Array.size_set,
      d31, d30, d29, hDataSz]; omega
  obtain ⟨s41, st40, pc41, regs41, d41⟩ :=
    step16_storeData code input pc40 (at_init subCode h32 (i := 40) (by decide)) (hPcLt 41 (by decide)) hBnd40
  have reg41 : ∀ r : Fin 16, reg s41 r = reg s40 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs41 r
  -- 41..44: 6 * n in r13; r12 = forestArenaBase
  have hNeq41 : (reg s41 rN).val = n := by
    rw [reg41, keep40 _ (by decide), keep39 _ (by decide), keep38 _ (by decide), reg37,
      keep36 _ (by decide), keep35 _ (by decide), keep34 _ (by decide), keep33 _ (by decide), hNeq32]
  obtain ⟨s42, st41, pc42, r13_42, keep42, d42⟩ :=
    step16_add code input pc41 (at_init subCode h32 (i := 41) (by decide)) (hPcLt 42 (by decide))
  have r13v42 : (reg s42 r13).val = 2 * n := by
    rw [r13_42, add_no_wrap] <;> rw [hNeq41] <;> omega
  obtain ⟨s43, st42, pc43, r14_43, keep43, d43⟩ :=
    step16_add code input pc42 (at_init subCode h32 (i := 42) (by decide)) (hPcLt 43 (by decide))
  have r14v43 : (reg s43 r14).val = 4 * n := by
    rw [r14_43, add_no_wrap] <;> rw [r13v42] <;> omega
  obtain ⟨s44, st43, pc44, r13_44, keep44, d44⟩ :=
    step16_add code input pc43 (at_init subCode h32 (i := 43) (by decide)) (hPcLt 44 (by decide))
  have r13v44 : (reg s44 r13).val = 6 * n := by
    rw [r13_44, add_no_wrap] <;> rw [keep43 _ (by decide), r13v42, r14v43] <;> omega
  obtain ⟨s45, st44, pc45, r12_45, keep45, d45⟩ :=
    step16_add code input pc44 (at_init subCode h32 (i := 44) (by decide)) (hPcLt 45 (by decide))
  have r12eq44 : (reg s44 r12).val = ownerForestPtrsBase loopBase n m := by
    rw [keep44 _ (by decide), keep43 _ (by decide), keep42 _ (by decide), reg41,
      keep40 _ (by decide), keep39 _ (by decide), r12v38]
  have r12v45 : (reg s45 r12).val = forestArenaBase loopBase n m := by
    rw [r12_45, add_no_wrap]
    · rw [r12eq44, r13v44]; rfl
    · rw [r12eq44, r13v44]; exact hArenaLt
  -- 45: imm r13 15; 46: add r14 r11 r13; 47: storeData r14 r12
  obtain ⟨s46, st45, pc46, r13_46, keep46, d46⟩ :=
    step16_imm code input pc45 (at_init subCode h32 (i := 45) (by decide)) (hPcLt 46 (by decide))
  obtain ⟨s47, st46, pc47, r14_47, keep47, d47⟩ :=
    step16_add code input pc46 (at_init subCode h32 (i := 46) (by decide)) (hPcLt 47 (by decide))
  have r11eq46 : (reg s46 r11).val = loopSubStateBase loopBase n m := by
    rw [keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), keep43 _ (by decide),
      keep42 _ (by decide), reg41, keep40 _ (by decide), r11eq39]
  have hAddr47 : (reg s47 r14).val = loopSubStateBase loopBase n m + 15 := by
    rw [r14_47, add_no_wrap]
    · rw [r11eq46, r13_46]; rfl
    · rw [r11eq46, r13_46]; change _ + 15 < 2 ^ bits; omega
  have hDataSz47 : s47.data.size = workCap := by
    rw [d47, d46, d45, d44, d43, d42, d41, Array.size_set, d40, d39, d38, d37, Array.size_set,
      d36, d35, d34, d33, d32, Array.size_set, d31, d30, d29, hDataSz]
  have hBnd47 : (reg s47 r14).val < s47.data.size := by rw [hAddr47, hDataSz47]; omega
  obtain ⟨s48, st47, pc48, regs48, d48⟩ :=
    step16_storeData code input pc47 (at_init subCode h32 (i := 47) (by decide)) (hPcLt 48 (by decide)) hBnd47
  have reg48 : ∀ r : Fin 16, reg s48 r = reg s47 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs48 r
  have hSteps : Steps code input 20 s28 s48 :=
    Steps.cons st28 (Steps.cons st29 (Steps.cons st30 (Steps.cons st31
      (Steps.cons st32 (Steps.cons st33 (Steps.cons st34 (Steps.cons st35
        (Steps.cons st36 (Steps.cons st37 (Steps.cons st38 (Steps.cons st39
          (Steps.cons st40 (Steps.cons st41 (Steps.cons st42 (Steps.cons st43
            (Steps.cons st44 (Steps.cons st45 (Steps.cons st46 (Steps.cons st47 (Steps.zero s48))))))))))))))))))))
  have hDataSz48 : s48.data.size = workCap := by rw [d48, Array.size_set, hDataSz47]
  have hRegs48 : LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s48 := by
    refine loopIterRegs_of_keep hRegs fun r hr => ?_
    have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    rw [reg48, keep47 _ h14, keep46 _ h13, keep45 _ h12, keep44 _ h13, keep43 _ h14, keep42 _ h13,
      reg41, keep40 _ h14, keep39 _ h13, keep38 _ h12, reg37, keep36 _ h14, keep35 _ h13,
      keep34 _ h12, keep33 _ h12, reg32, keep31 _ h14, keep30 _ h13, keep29 _ h12]
  have hDataAt : ∀ k, (if k = loopSubStateBase loopBase n m + 15 then some ⟨forestArenaBase loopBase n m, hArenaLt⟩
      else if k = loopSubStateBase loopBase n m + 14 then some ⟨ownerForestPtrsBase loopBase n m, hPtrLt⟩
      else if k = loopSubStateBase loopBase n m + 13 then some ⟨loopSortEntryBase loopBase n m, hEntLt⟩
      else if k = loopSubStateBase loopBase n m + 12 then some ⟨loopCursorBase loopBase n m, hCurLt⟩
      else s28.data[k]?) = s48.data[k]? := by
    intro k
    rw [d48]
    by_cases hk15 : k = loopSubStateBase loopBase n m + 15
    · subst hk15; rw [ite_eq_left rfl, mem_set_same s47.data hAddr47 hBnd47]
      exact congrArg some (Fin.ext (by rw [keep47 _ (by decide), keep46 _ (by decide), r12v45]))
    · rw [ite_eq_right hk15, mem_set_ne s47.data hBnd47 (fun e => hk15 (e.trans hAddr47))]
      rw [d47, d46, d45, d44, d43, d42, d41]
      by_cases hk14 : k = loopSubStateBase loopBase n m + 14
      · subst hk14; rw [ite_eq_left rfl, mem_set_same s40.data hAddr40 hBnd40]
        exact congrArg some (Fin.ext (by rw [keep40 _ (by decide), keep39 _ (by decide), r12v38]))
      · rw [ite_eq_right hk14, mem_set_ne s40.data hBnd40 (fun e => hk14 (e.trans hAddr40))]
        rw [d40, d39, d38, d37]
        by_cases hk13 : k = loopSubStateBase loopBase n m + 13
        · subst hk13; rw [ite_eq_left rfl, mem_set_same s36.data hAddr36 hBnd36]
          exact congrArg some (Fin.ext (by rw [keep36 _ (by decide), keep35 _ (by decide), r12v34]))
        · rw [ite_eq_right hk13, mem_set_ne s36.data hBnd36 (fun e => hk13 (e.trans hAddr36))]
          rw [d36, d35, d34, d33, d32]
          by_cases hk12 : k = loopSubStateBase loopBase n m + 12
          · subst hk12; rw [ite_eq_left rfl, mem_set_same s31.data hAddr31 hBnd31]
            exact congrArg some (Fin.ext (by rw [keep31 _ (by decide), keep30 _ (by decide), r12v29]))
          · rw [ite_eq_right hk12, mem_set_ne s31.data hBnd31 (fun e => hk12 (e.trans hAddr31)),
              d31, d30, d29]
  refine ⟨s48, hSteps, ?_, hDataSz48, hRegs48, ?_, ?_, ?_, ?_, ?_⟩
  · rw [pc48]; unfold offInit offHdr; omega
  · rw [← hDataAt (loopSubStateBase loopBase n m + 12)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  · rw [← hDataAt (loopSubStateBase loopBase n m + 13)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
  · rw [← hDataAt (loopSubStateBase loopBase n m + 14)]
    rw [ite_eq_right (by omega), ite_eq_left rfl]
  · rw [← hDataAt (loopSubStateBase loopBase n m + 15)]
    rw [ite_eq_left rfl]
  · intro k hk; rw [← hDataAt k]
    rcases hk with hl | hr <;>
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem loopInit_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase : Nat}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offInit) (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hDataSz : s₀.data.size = workCap)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    ∃ s48, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 48 s₀ s48 ∧
      s48.pc = offHdr ∧
      s48.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s48 ∧
      s48.data[inPtrAddr]? = some ⟨loopBase, by unfold loopWorkWords at hFit; omega⟩ ∧
      s48.data[dataPtrAddr]? = some ⟨loopSubWorkBase loopBase n m, by
        unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega⟩ ∧
      s48.data[statePtrAddr]? = some ⟨loopSubStateBase loopBase n m, by
        unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 11]? = some ⟨loopDegBase loopBase n m, by
        unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 12]? = some ⟨loopCursorBase loopBase n m, by
        unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 13]? = some ⟨loopSortEntryBase loopBase n m, by
        unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 14]? = some ⟨ownerForestPtrsBase loopBase n m, by
        unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      s48.data[loopSubStateBase loopBase n m + 15]? = some ⟨forestArenaBase loopBase n m, by
        unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega⟩ ∧
      (∀ k, k ≠ inPtrAddr → k ≠ dataPtrAddr → k ≠ statePtrAddr →
        (k < loopSubStateBase loopBase n m + 11 ∨ loopSubStateBase loopBase n m + 16 ≤ k) →
        s48.data[k]? = s₀.data[k]?) := by
  obtain ⟨s14, stA, pc14, sz14, hRegs14, d14, u14, hr11_14, hIn14, hDat14, hOutA⟩ :=
    loopInitA_steps subCode h32 input hpc hRegs hDataSz hFit hBits
  have hIter14 : LoopIterRegs n m root Q treeBase emitBase loopBase 0 0 s14 := ⟨hRegs14, d14, u14⟩
  obtain ⟨s28, stB, pc28, sz28, hRegs28, hr11_28, hr12_28, hSt28, hS11_28, hOutB⟩ :=
    loopInitB_steps subCode h32 input pc14 hIter14 hr11_14 sz14 hFit hBits
  obtain ⟨s48, stC, pc48, sz48, hRegs48, hS12, hS13, hS14, hS15, hOutC⟩ :=
    loopInitC_steps subCode h32 input pc28 hRegs28 hr11_28 hr12_28 sz28 hFit hBits
  have hStateGe3 : statePtrAddr < loopSubStateBase loopBase n m + 11 := by
    unfold statePtrAddr loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
  have hInNe : inPtrAddr ≠ statePtrAddr := by decide
  have hDatNe : dataPtrAddr ≠ statePtrAddr := by decide
  refine ⟨s48, stA.append (stB.append stC), pc48, sz48, hRegs48, ?_, ?_, ?_, ?_, hS12, hS13, hS14, hS15, ?_⟩
  · rw [hOutC _ (Or.inl (by unfold inPtrAddr; omega)),
        hOutB _ (by unfold inPtrAddr statePtrAddr; omega) (by unfold inPtrAddr; omega)]
    exact hIn14
  · rw [hOutC _ (Or.inl (by unfold dataPtrAddr; omega)),
        hOutB _ (by unfold dataPtrAddr statePtrAddr; omega) (by unfold dataPtrAddr; omega)]
    exact hDat14
  · rw [hOutC _ (Or.inl (by omega))]; exact hSt28
  · rw [hOutC _ (Or.inl (by omega))]; exact hS11_28
  · intro k hk0 hk1 hk2 hkRng
    have hkC : k < loopSubStateBase loopBase n m + 12 ∨ loopSubStateBase loopBase n m + 16 ≤ k := by omega
    have hkNe11 : k ≠ loopSubStateBase loopBase n m + 11 := by omega
    rw [hOutC k hkC, hOutB k hk2 hkNe11, hOutA k hk0 hk1]

private theorem prepOwnerA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hQ : Q = dense.length) (hd : d < Q)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offPrep)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hDataSz : s₀.data.size = workCap)
    (hTreeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s₀.data[k]? = origMem[k]?)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let n_d := 1 + (S.childSlice dFin).length
    ∃ s12, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 12 s₀ s12 ∧
      s12.pc = offPrep + 12 ∧
      s12.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s12 ∧
      s12.data[loopBase]? = some ⟨n_d, by
        have : n_d ≤ Q := hQ ▸ ownerVertexCount_le_Q S dFin
        have hQL : Q ≤ n := hQ.symm ▸ hn ▸ S.length_le
        unfold loopWorkWords at hFit; omega⟩ ∧
      (∀ k, k ≠ loopBase → s12.data[k]? = s₀.data[k]?) := by
  intro dFin n_d
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 13 → offPrep + c < code.size := by
    intro c hc; rw [hSz]; unfold offPrep; omega
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hQVal : (reg s₀ r5).val = Q := hRegs.entry.qVal
  have hTVal : (reg s₀ r6).val = treeBase := hRegs.entry.treeBaseVal
  have hLVal : (reg s₀ r8).val = loopBase := hRegs.entry.loopBaseVal
  have hdVal : (reg s₀ r9).val = d := hRegs.dVal
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hNdLe : n_d ≤ Q := by rw [hQ]; exact ownerVertexCount_le_Q S dFin
  have hQLt : 7 * Q < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hTreeBnd : treeBase + 7 * Q + d + 1 < 2 ^ bits := by
    unfold staticTreeWords at hTreeFit; omega
  -- 0..3: 7 * Q in r11
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_add code input hpc (at_prep subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have r11v1 : (reg s1 r11).val = 2 * Q := by
    rw [r11_1, add_no_wrap] <;> rw [hQVal] <;> omega
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_add code input pc1 (at_prep subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
  have r12v2 : (reg s2 r12).val = 4 * Q := by
    rw [r12_2, add_no_wrap] <;> rw [r11v1] <;> omega
  obtain ⟨s3, st2, pc3, r11_3, keep3, d3⟩ :=
    step16_add code input pc2 (at_prep subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  have r11eq2 : (reg s2 r11).val = 2 * Q := (congrArg Fin.val (keep2 _ (by decide))).trans r11v1
  have r11v3 : (reg s3 r11).val = 6 * Q := by
    rw [r11_3, add_no_wrap] <;> rw [r11eq2, r12v2] <;> omega
  obtain ⟨s4, st3, pc4, r11_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_prep subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have hQeq3 : (reg s3 r5).val = Q := by
    rw [keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hQVal]
  have r11v4 : (reg s4 r11).val = 7 * Q := by
    rw [r11_4, add_no_wrap] <;> rw [r11v3, hQeq3] <;> omega
  -- 4: add r11 r6 r11; 5: add r11 r11 r9 -> treeBase + 7*Q + d
  obtain ⟨s5, st4, pc5, r11_5, keep5, d5⟩ :=
    step16_add code input pc4 (at_prep subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have hTeq4 : (reg s4 r6).val = treeBase := by
    rw [keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hTVal]
  have r11v5 : (reg s5 r11).val = treeBase + 7 * Q := by
    rw [r11_5, add_no_wrap] <;> rw [hTeq4, r11v4] <;> omega
  obtain ⟨s6, st5, pc6, r11_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_prep subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have hdeq5 : (reg s5 r9).val = d := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide),
      keep1 _ (by decide), hdVal]
  have r11v6 : (reg s6 r11).val = treeBase + 7 * Q + d := by
    rw [r11_6, add_no_wrap] <;> rw [r11v5, hdeq5] <;> omega
  -- 6: loadData r12 r11
  have hMemC0 : s6.data[(reg s6 r11).val]? =
      some ⟨S.childStart d, Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt
        (S.childStart_mono d dense.length (by omega) (Nat.le_refl _))
        (by rw [S.childStart_end]; have := S.qPos; omega)) (by omega : dense.length ≤ 2 ^ bits)⟩ := by
    rw [r11v6, d6, d5, d4, d3, d2, d1, hTreeMem _ (by omega) (by unfold staticTreeWords; omega),
      show treeBase + 7 * Q + d = treeBase + 7 * dense.length + d by rw [hQ]]
    exact mem_word_of_map (S.childStart_mem d (by omega)) _
  obtain ⟨s7, st6, pc7, r12_7, keep7, d7⟩ :=
    step16_loadData code input pc6 (at_prep subCode h32 (i := 6) (by decide)) hMemC0 (hPcLt 7 (by decide))
  -- 7: add r11 r11 r1; 8: loadData r13 r11
  have h1eq7 : (reg s7 rOne).val = 1 := by
    rw [keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hOne]
  obtain ⟨s8, st7, pc8, r11_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_prep subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r11v8 : (reg s8 r11).val = treeBase + 7 * Q + d + 1 := by
    rw [r11_8, add_no_wrap]
    · rw [keep7 _ (by decide), r11v6, h1eq7]
    · rw [keep7 _ (by decide), r11v6, h1eq7]; omega
  have hMemC1 : s8.data[(reg s8 r11).val]? =
      some ⟨S.childStart (d + 1), Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt
        (S.childStart_mono (d + 1) dense.length (by omega) (Nat.le_refl _))
        (by rw [S.childStart_end]; have := S.qPos; omega)) (by omega : dense.length ≤ 2 ^ bits)⟩ := by
    rw [r11v8, d8, d7, d6, d5, d4, d3, d2, d1, hTreeMem _ (by omega) (by unfold staticTreeWords; omega),
      show treeBase + 7 * Q + d + 1 = treeBase + 7 * dense.length + (d + 1) by rw [hQ]; omega]
    exact mem_word_of_map (S.childStart_mem (d + 1) (by omega)) _
  obtain ⟨s9, st8, pc9, r13_9, keep9, d9⟩ :=
    step16_loadData code input pc8 (at_prep subCode h32 (i := 8) (by decide)) hMemC1 (hPcLt 9 (by decide))
  -- 9: sub r13 r13 r12; 10: add r11 r13 r1; 11: storeData r8 r11
  have r12eq8 : (reg s8 r12).val = S.childStart d := by
    rw [keep8 _ (by decide), r12_7]
  have hcLe : (reg s8 r12).val ≤ (reg s9 r13).val := by
    rw [r12eq8, r13_9]
    exact S.childStart_mono d (d + 1) (Nat.le_succ d) (by omega)
  obtain ⟨s10, st9, pc10, r13_10, keep10, d10⟩ :=
    step16_sub code input pc9 (at_prep subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  have r13v10 : (reg s10 r13).val = S.childStart (d + 1) - S.childStart d := by
    rw [r13_10, PaperB.RamDagReach.sub_exact _ _ (by rw [keep9 _ (by decide)]; exact hcLe),
      r13_9, keep9 _ (by decide), r12eq8]
  obtain ⟨s11, st10, pc11, r11_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_prep subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have h1eq10 : (reg s10 rOne).val = 1 := by
    rw [keep10 _ (by decide), keep9 _ (by decide), keep8 _ (by decide), h1eq7]
  have hChildEq : 1 + (S.childStart (d + 1) - S.childStart d) = n_d := by
    change _ = 1 + (S.childSlice dFin).length
    simp [StaticTreeSlice.childSlice, dFin]
  have r11v11 : (reg s11 r11).val = n_d := by
    rw [r11_11, add_no_wrap]
    · rw [r13v10, h1eq10]; omega
    · rw [r13v10, h1eq10]; omega
  have h8eq11 : (reg s11 r8).val = loopBase := by
    rw [keep11 _ (by decide), keep10 _ (by decide), keep9 _ (by decide), keep8 _ (by decide),
      keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hLVal]
  have hBnd11 : (reg s11 r8).val < s11.data.size := by
    rw [h8eq11, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1, hDataSz]
    unfold loopWorkWords at hFit; omega
  obtain ⟨s12, st11, pc12, regs12, d12⟩ :=
    step16_storeData code input pc11 (at_prep subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide)) hBnd11
  have reg12 : ∀ r : Fin 16, reg s12 r = reg s11 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs12 r
  have hSteps : Steps code input 12 s₀ s12 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3
      (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.cons st7
        (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11 (Steps.zero s12))))))))))))
  have hDataSame : s11.data = s₀.data := by rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hDataSz12 : s12.data.size = workCap := by rw [d12, Array.size_set, hDataSame, hDataSz]
  have hRegs12 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s12 := by
    refine loopIterRegs_of_keep hRegs fun r hr => ?_
    have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    rw [reg12, keep11 _ h11, keep10 _ h13, keep9 _ h13, keep8 _ h11, keep7 _ h12,
      keep6 _ h11, keep5 _ h11, keep4 _ h11, keep3 _ h11, keep2 _ h12, keep1 _ h11]
  refine ⟨s12, hSteps, pc12, hDataSz12, hRegs12, ?_, ?_⟩
  · rw [d12, mem_set_same s11.data h8eq11 hBnd11]
    exact congrArg some (Fin.ext r11v11)
  · intro k hk
    rw [d12, mem_set_ne s11.data hBnd11 (fun e => hk (e.trans h8eq11)), hDataSame]

private theorem prepOwnerB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    {s12 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s12.pc = offPrep + 12)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s12)
    (hDataSz : s12.data.size = workCap)
    (hQStarts : ∀ j ≤ Q, (s12.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let m_d := (S.emittedArcs dFin).length
    ∃ s23, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 11 s12 s23 ∧
      s23.pc = offZeroDeg ∧
      s23.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s23 ∧
      s23.data[loopBase + 1]? = some ⟨m_d, by
        have hLe : m_d ≤ m := hm.symm ▸ (by
          have hS : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S (hQ ▸ hd)
          have hA := qStartFn_le_arcCount S (d + 1)
          omega)
        unfold loopWorkWords at hFit; omega⟩ ∧
      s23.data[loopBase + 2]? = some ⟨0, by unfold loopWorkWords at hFit; omega⟩ ∧
      (∀ k, k ≠ loopBase + 1 → k ≠ loopBase + 2 → s23.data[k]? = s12.data[k]?) := by
  intro dFin m_d
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 24 → offPrep + c < code.size := by
    intro c hc; rw [hSz]; unfold offPrep; omega
  have hZero : (reg s12 rZero).val = 0 := hRegs.entry.consts.zero
  have hOne : (reg s12 rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s12 rN).val = n := hRegs.entry.consts.nVal
  have hE : (reg s12 r7).val = emitBase := hRegs.entry.emitBaseVal
  have hL : (reg s12 r8).val = loopBase := hRegs.entry.loopBaseVal
  have hdVal : (reg s12 r9).val = d := hRegs.dVal
  have hQL : Q ≤ n := hQ.symm ▸ hn ▸ S.length_le
  have hEmitBnd : emitBase + 2 * n + d + 1 < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have hQS0 : qStartFn S d ≤ m := hm.symm ▸ qStartFn_le_arcCount S d
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have hSucc : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S dFin.isLt
  have hMdLe : m_d ≤ m := by omega
  have hMLt : m < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have h2NLt : 2 * n < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  -- 12..14: emitBase + 2*n + d in r12
  obtain ⟨s13, st12, pc13, r12_13, keep13, d13⟩ :=
    step16_add code input hpc (at_prep subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
  have r12v13 : (reg s13 r12).val = 2 * n := by
    rw [r12_13, add_no_wrap] <;> rw [hN] <;> omega
  obtain ⟨s14, st13, pc14, r12_14, keep14, d14⟩ :=
    step16_add code input pc13 (at_prep subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have hEeq13 : (reg s13 r7).val = emitBase := (congrArg Fin.val (keep13 _ (by decide))).trans hE
  have r12v14 : (reg s14 r12).val = emitBase + 2 * n := by
    rw [r12_14, add_no_wrap] <;> rw [hEeq13, r12v13] <;> omega
  obtain ⟨s15, st14, pc15, r12_15, keep15, d15⟩ :=
    step16_add code input pc14 (at_prep subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have hdeq14 : (reg s14 r9).val = d := by
    rw [keep14 _ (by decide), keep13 _ (by decide), hdVal]
  have r12v15 : (reg s15 r12).val = emitBase + 2 * n + d := by
    rw [r12_15, add_no_wrap] <;> rw [r12v14, hdeq14] <;> omega
  -- 15: loadData r13 r12 -> qStart[d]
  have hMemQ0 : s15.data[(reg s15 r12).val]? = some ⟨qStartFn S d, by omega⟩ := by
    rw [r12v15, d15, d14, d13]
    exact mem_word_of_map (hQStarts d (by omega)) _
  obtain ⟨s16, st15, pc16, r13_16, keep16, d16⟩ :=
    step16_loadData code input pc15 (at_prep subCode h32 (i := 15) (by decide)) hMemQ0 (hPcLt 16 (by decide))
  -- 16: add r12 r12 r1; 17: loadData r14 r12 -> qStart[d+1]
  have h1eq16 : (reg s16 rOne).val = 1 := by
    rw [keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), keep13 _ (by decide), hOne]
  obtain ⟨s17, st16, pc17, r12_17, keep17, d17⟩ :=
    step16_add code input pc16 (at_prep subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have r12v17 : (reg s17 r12).val = emitBase + 2 * n + d + 1 := by
    rw [r12_17, add_no_wrap]
    · rw [keep16 _ (by decide), r12v15, h1eq16]
    · rw [keep16 _ (by decide), r12v15, h1eq16]; omega
  have hMemQ1 : s17.data[(reg s17 r12).val]? = some ⟨qStartFn S (d + 1), by omega⟩ := by
    rw [r12v17, d17, d16, d15, d14, d13]
    have hE' : emitBase + 2 * n + d + 1 = emitBase + 2 * n + (d + 1) := by omega
    rw [hE']
    exact mem_word_of_map (hQStarts (d + 1) (by omega)) _
  obtain ⟨s18, st17, pc18, r14_18, keep18, d18⟩ :=
    step16_loadData code input pc17 (at_prep subCode h32 (i := 17) (by decide)) hMemQ1 (hPcLt 18 (by decide))
  -- 18: sub r14 r14 r13 -> m_d
  have r13eq18 : (reg s18 r13).val = qStartFn S d := by
    rw [keep18 _ (by decide), keep17 _ (by decide), r13_16]
  have r14eq18 : (reg s18 r14).val = qStartFn S (d + 1) := congrArg Fin.val r14_18
  have hqLe : (reg s18 r13).val ≤ (reg s18 r14).val := by rw [r13eq18, r14eq18]; omega
  obtain ⟨s19, st18, pc19, r14_19, keep19, d19⟩ :=
    step16_sub code input pc18 (at_prep subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  have r14v19 : (reg s19 r14).val = m_d := by
    rw [r14_19, PaperB.RamDagReach.sub_exact _ _ hqLe, r14eq18, r13eq18]; omega
  -- 19: add r12 r8 r1; 20: storeData r12 r14
  have h8eq19 : (reg s19 r8).val = loopBase := by
    rw [keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide),
      keep15 _ (by decide), keep14 _ (by decide), keep13 _ (by decide), hL]
  have h1eq19 : (reg s19 rOne).val = 1 := by
    rw [keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), h1eq16]
  obtain ⟨s20, st19, pc20, r12_20, keep20, d20⟩ :=
    step16_add code input pc19 (at_prep subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  have r12v20 : (reg s20 r12).val = loopBase + 1 := by
    rw [r12_20, add_no_wrap]
    · rw [h8eq19, h1eq19]
    · rw [h8eq19, h1eq19]; unfold loopWorkWords at hFit; omega
  have hDataSame20 : s20.data = s12.data := by rw [d20, d19, d18, d17, d16, d15, d14, d13]
  have hBnd20 : (reg s20 r12).val < s20.data.size := by
    rw [r12v20, hDataSame20, hDataSz]; unfold loopWorkWords at hFit; omega
  obtain ⟨s21, st20, pc21, regs21, d21⟩ :=
    step16_storeData code input pc20 (at_prep subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide)) hBnd20
  have reg21 : ∀ r : Fin 16, reg s21 r = reg s20 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs21 r
  -- 21: add r12 r12 r1; 22: storeData r12 r0
  obtain ⟨s22, st21, pc22, r12_22, keep22, d22⟩ :=
    step16_add code input pc21 (at_prep subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
  have h1eq21 : (reg s21 rOne).val = 1 := by rw [reg21, keep20 _ (by decide), h1eq19]
  have r12v22 : (reg s22 r12).val = loopBase + 2 := by
    rw [r12_22, add_no_wrap]
    · rw [reg21, r12v20, h1eq21]
    · rw [reg21, r12v20, h1eq21]; unfold loopWorkWords at hFit; omega
  have hBnd22 : (reg s22 r12).val < s22.data.size := by
    rw [r12v22, d22, d21, Array.size_set, hDataSame20, hDataSz]; unfold loopWorkWords at hFit; omega
  obtain ⟨s23, st22, pc23, regs23, d23⟩ :=
    step16_storeData code input pc22 (at_prep subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide)) hBnd22
  have reg23 : ∀ r : Fin 16, reg s23 r = reg s22 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs23 r
  have hSteps : Steps code input 11 s12 s23 :=
    Steps.cons st12 (Steps.cons st13 (Steps.cons st14 (Steps.cons st15
      (Steps.cons st16 (Steps.cons st17 (Steps.cons st18 (Steps.cons st19
        (Steps.cons st20 (Steps.cons st21 (Steps.cons st22 (Steps.zero s23)))))))))))
  have hDataSz23 : s23.data.size = workCap := by
    rw [d23, Array.size_set, d22, d21, Array.size_set, hDataSame20, hDataSz]
  have hRegs23 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s23 := by
    refine loopIterRegs_of_keep hRegs fun r hr => ?_
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    rw [reg23, keep22 _ h12, reg21, keep20 _ h12, keep19 _ h14, keep18 _ h14,
      keep17 _ h12, keep16 _ h13, keep15 _ h12, keep14 _ h12, keep13 _ h12]
  have hDataAt : ∀ k, (if k = loopBase + 2 then some ⟨0, by unfold loopWorkWords at hFit; omega⟩
      else if k = loopBase + 1 then some ⟨m_d, by omega⟩
      else s12.data[k]?) = s23.data[k]? := by
    intro k
    rw [d23]
    by_cases hk2 : k = loopBase + 2
    · subst hk2; rw [ite_eq_left rfl, mem_set_same s22.data r12v22 hBnd22]
      exact congrArg some (Fin.ext (by rw [keep22 _ (by decide), reg21, keep20 _ (by decide),
        keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide),
        keep15 _ (by decide), keep14 _ (by decide), keep13 _ (by decide), hZero]))
    · rw [ite_eq_right hk2, mem_set_ne s22.data hBnd22 (fun e => hk2 (e.trans r12v22))]
      rw [d22, d21]
      by_cases hk1 : k = loopBase + 1
      · subst hk1; rw [ite_eq_left rfl, mem_set_same s20.data r12v20 hBnd20]
        exact congrArg some (Fin.ext (by rw [keep20 _ (by decide), r14v19]))
      · rw [ite_eq_right hk1, mem_set_ne s20.data hBnd20 (fun e => hk1 (e.trans r12v20)), hDataSame20]
  refine ⟨s23, hSteps, by rw [pc23]; unfold offPrep offZeroDeg; omega, hDataSz23, hRegs23, ?_, ?_, ?_⟩
  · rw [← hDataAt (loopBase + 1), ite_eq_right (by omega), ite_eq_left rfl]
  · rw [← hDataAt (loopBase + 2), ite_eq_left rfl]
  · intro k hk1 hk2; rw [← hDataAt k, ite_eq_right hk2, ite_eq_right hk1]

private theorem prepOwner_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offPrep)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hDataSz : s₀.data.size = workCap)
    (hTreeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s₀.data[k]? = origMem[k]?)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let n_d := 1 + (S.childSlice dFin).length
    let m_d := (S.emittedArcs dFin).length
    ∃ s23, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 23 s₀ s23 ∧
      s23.pc = offZeroDeg ∧
      s23.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s23 ∧
      s23.data[loopBase]? = some ⟨n_d, by
        have : n_d ≤ Q := by rw [hQ]; exact ownerVertexCount_le_Q S dFin
        have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
        unfold loopWorkWords at hFit; omega⟩ ∧
      s23.data[loopBase + 1]? = some ⟨m_d, by
        have hS : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S (hQ ▸ hd)
        have hA := qStartFn_le_arcCount S (d + 1)
        unfold loopWorkWords at hFit; omega⟩ ∧
      s23.data[loopBase + 2]? = some ⟨0, by unfold loopWorkWords at hFit; omega⟩ ∧
      (∀ k, (k < loopBase ∨ loopBase + 3 ≤ k) → s23.data[k]? = s₀.data[k]?) := by
  intro dFin n_d m_d
  obtain ⟨s12, stA, pc12, sz12, regs12, h0, hOutA⟩ :=
    prepOwnerA_steps subCode h32 input S hn hQ hd hpc hRegs hDataSz hTreeMem hFit hTreeFit hBits
  have hQS12 : ∀ j ≤ Q, (s12.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j) := by
    intro j hj
    have hQL : Q ≤ n := hQ.symm ▸ hn ▸ S.length_le
    have hNe : emitBase + 2 * n + j ≠ loopBase := by
      rcases hDisj with hl | hr
      · unfold loopWorkWords at hl; omega
      · unfold emitterWorkWords at hr; omega
    rw [hOutA _ hNe]; exact hQStarts j hj
  obtain ⟨s23, stB, pc23, sz23, regs23, h1, h2, hOutB⟩ :=
    prepOwnerB_steps subCode h32 input S hn hm hQ hd pc12 regs12 sz12 hQS12 hFit hEmitFit hBits
  refine ⟨s23, stA.append stB, pc23, sz23, regs23, ?_, h1, h2, ?_⟩
  · rw [hOutB _ (by omega) (by omega)]; exact h0
  · intro k hk
    rw [hOutB k (by omega) (by omega), hOutA k (by omega)]

private theorem zeroDeg_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed n_d : Nat}
    (hn_d : n_d ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offZeroDeg)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hDataSz : s₀.data.size = workCap)
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some n_d)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDegPtr : (s₀.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m)) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 5 * n_d + 8 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offCountDeg ∧
      t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t ∧
      (∀ u < n_d, (t.data[loopDegBase loopBase n m + u]?).map Fin.val = some 0) ∧
      (∀ k, (k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ k) → t.data[k]? = s₀.data[k]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 13 → offZeroDeg + c < code.size := by
    intro c hc; rw [hSz]; unfold offZeroDeg; omega
  have hZero : (reg s₀ rZero).val = 0 := hRegs.entry.consts.zero
  have hL : (reg s₀ r8).val = loopBase := hRegs.entry.loopBaseVal
  have hStLt : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hDegBnd : loopDegBase loopBase n m + n ≤ workCap := by
    unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hNdLt : n_d < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hMemNd : s₀.data[(reg s₀ r8).val]? = some ⟨n_d, hNdLt⟩ := by
    rw [hL]; exact mem_word_of_map hNdAt hNdLt
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_loadData code input hpc (at_zeroDeg subCode h32 (i := 0) (by decide)) hMemNd (hPcLt 1 (by decide))
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_imm code input pc1 (at_zeroDeg subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
  have hMemSt : s2.data[(reg s2 r12).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d2, d1, show (reg s2 r12).val = statePtrAddr by rw [r12_2]; rfl]
    exact mem_word_of_map hStPtr _
  obtain ⟨s3, st2, pc3, r15_3, keep3, d3⟩ :=
    step16_loadData code input pc2 (at_zeroDeg subCode h32 (i := 2) (by decide)) hMemSt (hPcLt 3 (by decide))
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_imm code input pc3 (at_zeroDeg subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  obtain ⟨s5, st4, pc5, r12_5, keep5, d5⟩ :=
    step16_add code input pc4 (at_zeroDeg subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have hAddr5 : (reg s5 r12).val = loopSubStateBase loopBase n m + 11 := by
    rw [r12_5, add_no_wrap]
    · rw [keep4 _ (by decide), r15_3, r12_4]; rfl
    · rw [keep4 _ (by decide), r15_3, r12_4]; dsimp only; change _ + 11 < 2 ^ bits; omega
  have hMemDeg : s5.data[(reg s5 r12).val]? = some ⟨loopDegBase loopBase n m, by omega⟩ := by
    rw [hAddr5, d5, d4, d3, d2, d1]; exact mem_word_of_map hDegPtr _
  obtain ⟨s6, st5, pc6, r15_6, keep6, d6⟩ :=
    step16_loadData code input pc5 (at_zeroDeg subCode h32 (i := 5) (by decide)) hMemDeg (hPcLt 6 (by decide))
  obtain ⟨s7, st6, pc7, r12_7, keep7, d7⟩ :=
    step16_mov code input pc6 (at_zeroDeg subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have hStepsPre : Steps code input 7 s₀ s7 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3
      (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.zero s7)))))))
  have hData7 : s7.data = s₀.data := by rw [d7, d6, d5, d4, d3, d2, d1]
  have hRegs7 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s7 := by
    refine loopIterRegs_of_keep hRegs fun r hr => ?_
    have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep7 _ h12, keep6 _ h15, keep5 _ h12, keep4 _ h12, keep3 _ h15, keep2 _ h12, keep1 _ h11]
  have hr11_7 : (reg s7 r11).val = n_d := by
    rw [keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      keep3 _ (by decide), keep2 _ (by decide), r11_1]
  have hr15_7 : (reg s7 r15).val = loopDegBase loopBase n m := by
    rw [keep7 _ (by decide), r15_6]
  have hr12_7 : (reg s7 r12).val = 0 := by
    rw [r12_7, keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hZero]
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun u s =>
    u ≤ n_d ∧ s.pc = offZeroDeg + 7 ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    s.data.size = workCap ∧
    (reg s r11).val = n_d ∧ (reg s r15).val = loopDegBase loopBase n m ∧ (reg s r12).val = u ∧
    (∀ j < u, (s.data[loopDegBase loopBase n m + j]?).map Fin.val = some 0) ∧
    (∀ k, (k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + u ≤ k) → s.data[k]? = s₀.data[k]?)
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offCountDeg ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (∀ u < n_d, (s.data[loopDegBase loopBase n m + u]?).map Fin.val = some 0) ∧
    (∀ k, (k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ k) → s.data[k]? = s₀.data[k]?)
  have hLoop := loop_steps_budget inv (fun u => n_d - u) (fun u => 1 + 5 * (n_d - u)) post
    (fun u s ⟨huLe, hpcS, hRgS, hSzS, hr11S, hr15S, hr12S, hZerosS, hOutS⟩ => by
      by_cases huEq : u = n_d
      · subst huEq
        have hGe : (reg s r11).val ≤ (reg s r12).val := by omega
        have stBr := step16_branchLt_false code input hpcS
          (at_zeroDeg subCode h32 (i := 7) (by decide)) (hPcLt 12 (by decide)) hGe
        refine Or.inl ⟨_, 1, by omega, steps_one stBr, ?_, hSzS,
          loopIterRegs_of_keep hRgS (fun _ _ => rfl), hZerosS, hOutS⟩
        change offZeroDeg + 12 = offCountDeg; unfold offZeroDeg offCountDeg; omega
      · have huLt : u < n_d := by omega
        have hLtR : (reg s r12).val < (reg s r11).val := by omega
        have st7 := step16_branchLt_true code input hpcS
          (at_zeroDeg subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide)) hLtR
        let s8 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s.regs, data := s.data, pc := offZeroDeg + 8,
            regs_size := s.regs_size, data_size := s.data_size }
        have reg8 : ∀ r : Fin 16, reg s8 r = reg s r := fun _ => rfl
        obtain ⟨s9, st8, pc9, r13_9, keep9, d9⟩ :=
          step16_add code input (rfl : s8.pc = offZeroDeg + 8)
            (at_zeroDeg subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
        have r13v9 : (reg s9 r13).val = loopDegBase loopBase n m + u := by
          rw [r13_9, add_no_wrap]
          · rw [reg8, reg8, hr15S, hr12S]
          · rw [reg8, reg8, hr15S, hr12S]; omega
        have hBnd9 : (reg s9 r13).val < s9.data.size := by rw [r13v9, d9]; change _ < s.data.size; omega
        obtain ⟨s10, st9, pc10, regs10, d10⟩ :=
          step16_storeData code input pc9
            (at_zeroDeg subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide)) hBnd9
        have reg10 : ∀ r : Fin 16, reg s10 r = reg s9 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs10 r
        obtain ⟨s11, st10, pc11, r12_11, keep11, d11⟩ :=
          step16_add code input pc10
            (at_zeroDeg subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
        have r12v11 : (reg s11 r12).val = u + 1 := by
          rw [r12_11, add_no_wrap]
          · rw [reg10, keep9 _ (by decide), reg8, hr12S, reg10, keep9 _ (by decide), reg8, hRgS.entry.consts.one]
          · rw [reg10, keep9 _ (by decide), reg8, hr12S, reg10, keep9 _ (by decide), reg8, hRgS.entry.consts.one]; omega
        have st11 := step16_goto code input pc11
          (at_zeroDeg subCode h32 (i := 11) (by decide)) (hPcLt 7 (by decide))
        let s12 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s11.regs, data := s11.data, pc := offZeroDeg + 7,
            regs_size := s11.regs_size, data_size := s11.data_size }
        have hStIter : Steps code input 5 s s12 :=
          Steps.cons st7 (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11 (Steps.zero s12)))))
        have hRg12 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s12 := by
          refine loopIterRegs_of_keep hRgS fun r hr => ?_
          have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
          have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
          change reg s11 r = reg s r
          rw [keep11 _ h12, reg10, keep9 _ h13]; rfl
        have hData12 : s12.data = s9.data.set (reg s9 r13).val (reg s9 rZero) hBnd9 := by
          change s11.data = _; rw [d11, d10]
        refine Or.inr ⟨u + 1, s12, 5, by omega, by omega, hStIter, ?_⟩
        refine ⟨huLt, rfl, hRg12, by change s11.data.size = _; rw [d11, d10, Array.size_set, d9]; exact hSzS,
          by change (reg s11 r11).val = _; rw [keep11 _ (by decide), reg10, keep9 _ (by decide)]; exact hr11S,
          by change (reg s11 r15).val = _; rw [keep11 _ (by decide), reg10, keep9 _ (by decide)]; exact hr15S,
          r12v11, ?_, ?_⟩
        · intro j hj
          rw [hData12]
          by_cases hju : j = u
          · subst hju
            rw [mem_set_same s9.data r13v9 hBnd9]
            rw [Option.map_some, keep9 _ (by decide)]; exact congrArg some hRgS.entry.consts.zero
          · rw [mem_set_ne s9.data hBnd9 (fun e => hju (by rw [r13v9] at e; omega)), d9]
            exact hZerosS j (by omega)
        · intro k hk
          rw [hData12, mem_set_ne s9.data hBnd9 (fun e => by rw [r13v9] at e; rcases hk with hl | hr <;> omega), d9]
          exact hOutS k (by rcases hk with hl | hr; exact Or.inl hl; exact Or.inr (by omega)))
    n_d 0 s7 (by omega)
    ⟨Nat.zero_le _, pc7, hRegs7, by rw [hData7, hDataSz],
      hr11_7, hr15_7, hr12_7, fun j hj => by omega, fun k _ => by rw [hData7]⟩
  obtain ⟨_, t, kL, hkL, hStL, hPost⟩ := hLoop
  exact ⟨t, 7 + kL, by omega, hStepsPre.append hStL, hPost⟩

private theorem emit_arc_disjoint_loopDeg
    {n m emitBase loopBase idx n_d : Nat}
    (hn_d : n_d ≤ n) (hIdx : idx < m)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase) :
    emitBase + 3 * n + 1 + idx < loopDegBase loopBase n m ∨
      loopDegBase loopBase n m + n_d ≤ emitBase + 3 * n + 1 + idx := by
  unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
  unfold loopWorkWords at hDisj
  unfold emitterWorkWords at hDisj
  omega

private theorem countDegPre_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offCountDeg)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hDataSz : s₀.data.size = workCap)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDegPtr : (s₀.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m))
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)) :
    ∃ (s17 : State (layout16 bits inputCap workCap hi hw)),
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 17 s₀ s17 ∧
      s17.pc = offCountDeg + 17 ∧
      s17.data = s₀.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s17 ∧
      (reg s17 r15).val = loopDegBase loopBase n m ∧
      (reg s17 r13).val = emitBase + 3 * n + 1 + qStartFn S d ∧
      (reg s17 r14).val = emitBase + 3 * n + 1 + qStartFn S (d + 1) := by
  let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
  let m_d := (S.emittedArcs dFin).length
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 18 → offCountDeg + c < code.size := by
    intro c hc; rw [hSz]; unfold offCountDeg; omega
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s₀ rN).val = n := hRegs.entry.consts.nVal
  have hE : (reg s₀ r7).val = emitBase := hRegs.entry.emitBaseVal
  have hdVal : (reg s₀ r9).val = d := hRegs.dVal
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hQS0 : qStartFn S d ≤ m := hm.symm ▸ qStartFn_le_arcCount S d
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have hStLt : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hDegBnd : loopDegBase loopBase n m + n ≤ workCap := by
    unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hEmitBnd : emitBase + 3 * n + 1 + m ≤ workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h3NLt : 3 * n < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  obtain ⟨s1, st0, pc1, r12_1, keep1, d1⟩ :=
    step16_imm code input hpc (at_countDeg subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hMemSt : s1.data[(reg s1 r12).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d1, show (reg s1 r12).val = statePtrAddr by rw [r12_1]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s2, st1, pc2, r15_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_countDeg subCode h32 (i := 1) (by decide)) hMemSt (hPcLt 2 (by decide))
  obtain ⟨s3, st2, pc3, r12_3, keep3, d3⟩ :=
    step16_imm code input pc2 (at_countDeg subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_countDeg subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have hAddr4 : (reg s4 r12).val = loopSubStateBase loopBase n m + 11 := by
    rw [r12_4, add_no_wrap]
    · rw [keep3 _ (by decide), r15_2, r12_3]; rfl
    · rw [keep3 _ (by decide), r15_2, r12_3]; dsimp only; change _ + 11 < 2 ^ bits; omega
  have hMemDeg : s4.data[(reg s4 r12).val]? = some ⟨loopDegBase loopBase n m, by omega⟩ := by
    rw [hAddr4, d4, d3, d2, d1]; exact mem_word_of_map hDegPtr _
  obtain ⟨s5, st4, pc5, r15_5, keep5, d5⟩ :=
    step16_loadData code input pc4 (at_countDeg subCode h32 (i := 4) (by decide)) hMemDeg (hPcLt 5 (by decide))
  have hNeq5 : (reg s5 rN).val = n := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hN]
  have hEeq5 : (reg s5 r7).val = emitBase := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hE]
  have h1eq5 : (reg s5 rOne).val = 1 := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hOne]
  obtain ⟨s6, st5, pc6, r11_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_countDeg subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r11v6 : (reg s6 r11).val = 2 * n := by rw [r11_6, add_no_wrap] <;> rw [hNeq5] <;> omega
  obtain ⟨s7, st6, pc7, r11_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_countDeg subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have r11v7 : (reg s7 r11).val = 3 * n := by
    rw [r11_7, add_no_wrap] <;> rw [r11v6, keep6 _ (by decide), hNeq5] <;> omega
  obtain ⟨s8, st7, pc8, r11_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_countDeg subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r11v8 : (reg s8 r11).val = emitBase + 3 * n := by
    rw [r11_8, add_no_wrap]
    · rw [keep7 _ (by decide), keep6 _ (by decide), hEeq5, r11v7]
    · rw [keep7 _ (by decide), keep6 _ (by decide), hEeq5, r11v7]; omega
  obtain ⟨s9, st8, pc9, r11_9, keep9, d9⟩ :=
    step16_add code input pc8 (at_countDeg subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
  have r11v9 : (reg s9 r11).val = emitBase + 3 * n + 1 := by
    rw [r11_9, add_no_wrap]
    · rw [r11v8, keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), h1eq5]
    · rw [r11v8, keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), h1eq5]; omega
  have hNeq9 : (reg s9 rN).val = n := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), hNeq5]
  have hEeq9 : (reg s9 r7).val = emitBase := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), hEeq5]
  have hdeq9 : (reg s9 r9).val = d := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide),
      keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide),
      keep1 _ (by decide), hdVal]
  have h1eq9 : (reg s9 rOne).val = 1 := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), h1eq5]
  obtain ⟨s10, st9, pc10, r12_10, keep10, d10⟩ :=
    step16_add code input pc9 (at_countDeg subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  have r12v10 : (reg s10 r12).val = 2 * n := by rw [r12_10, add_no_wrap] <;> rw [hNeq9] <;> omega
  obtain ⟨s11, st10, pc11, r12_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_countDeg subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have r12v11 : (reg s11 r12).val = emitBase + 2 * n := by
    rw [r12_11, add_no_wrap] <;> rw [keep10 _ (by decide), hEeq9, r12v10] <;> omega
  obtain ⟨s12, st11, pc12, r12_12, keep12, d12⟩ :=
    step16_add code input pc11 (at_countDeg subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
  have r12v12 : (reg s12 r12).val = emitBase + 2 * n + d := by
    rw [r12_12, add_no_wrap] <;> rw [r12v11, keep11 _ (by decide), keep10 _ (by decide), hdeq9] <;> omega
  have hData12 : s12.data = s₀.data := by
    rw [d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hMemQ0 : s12.data[(reg s12 r12).val]? = some ⟨qStartFn S d, by omega⟩ := by
    rw [r12v12, hData12]; exact mem_word_of_map (hQStarts d (by omega)) _
  obtain ⟨s13, st12, pc13, r13_13, keep13, d13⟩ :=
    step16_loadData code input pc12 (at_countDeg subCode h32 (i := 12) (by decide)) hMemQ0 (hPcLt 13 (by decide))
  obtain ⟨s14, st13, pc14, r12_14, keep14, d14⟩ :=
    step16_add code input pc13 (at_countDeg subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have r12v14 : (reg s14 r12).val = emitBase + 2 * n + d + 1 := by
    rw [r12_14, add_no_wrap]
    · rw [keep13 _ (by decide), r12v12, keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide), h1eq9]
    · rw [keep13 _ (by decide), r12v12, keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide), h1eq9]; omega
  have hMemQ1 : s14.data[(reg s14 r12).val]? = some ⟨qStartFn S (d + 1), by omega⟩ := by
    rw [r12v14, d14, d13, hData12, show emitBase + 2 * n + d + 1 = emitBase + 2 * n + (d + 1) by omega]
    exact mem_word_of_map (hQStarts (d + 1) (by omega)) _
  obtain ⟨s15, st14, pc15, r14_15, keep15, d15⟩ :=
    step16_loadData code input pc14 (at_countDeg subCode h32 (i := 14) (by decide)) hMemQ1 (hPcLt 15 (by decide))
  have r11eq15 : (reg s15 r11).val = emitBase + 3 * n + 1 := by
    rw [keep15 _ (by decide), keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide),
      keep11 _ (by decide), keep10 _ (by decide), r11v9]
  have r13eq15 : (reg s15 r13).val = qStartFn S d := by
    rw [keep15 _ (by decide), keep14 _ (by decide), r13_13]
  obtain ⟨s16, st15, pc16, r13_16, keep16, d16⟩ :=
    step16_add code input pc15 (at_countDeg subCode h32 (i := 15) (by decide)) (hPcLt 16 (by decide))
  have r13v16 : (reg s16 r13).val = emitBase + 3 * n + 1 + qStartFn S d := by
    rw [r13_16, add_no_wrap] <;> rw [r11eq15, r13eq15] <;> omega
  obtain ⟨s17, st16, pc17, r14_17, keep17, d17⟩ :=
    step16_add code input pc16 (at_countDeg subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have r14v17 : (reg s17 r14).val = emitBase + 3 * n + 1 + qStartFn S (d + 1) := by
    rw [r14_17, add_no_wrap]
    · rw [keep16 _ (by decide), r11eq15, keep16 _ (by decide), r14_15]
    · rw [keep16 _ (by decide), r11eq15, keep16 _ (by decide), r14_15]; dsimp only; omega
  refine ⟨s17, Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3
      (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.cons st7
        (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11
          (Steps.cons st12 (Steps.cons st13 (Steps.cons st14 (Steps.cons st15
            (Steps.cons st16 (Steps.zero s17))))))))))))))))),
    pc17,
    by rw [d17, d16, d15, d14, d13, hData12],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, r14v17⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep17 _ h14, keep16 _ h13, keep15 _ h14, keep14 _ h12, keep13 _ h13, keep12 _ h12,
      keep11 _ h12, keep10 _ h12, keep9 _ h11, keep8 _ h11, keep7 _ h11, keep6 _ h11,
      keep5 _ h15, keep4 _ h12, keep3 _ h12, keep2 _ h15, keep1 _ h12]
  · rw [keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide),
      keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), r15_5]
  · rw [keep17 _ (by decide), r13v16]

private theorem countDeg_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offCountDeg)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hDataSz : s₀.data.size = workCap)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDegPtr : (s₀.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m))
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hSrcOrig : ∀ (p : Nat) (hp : p < (S.emittedArcs ⟨d, hQ ▸ hd⟩).length),
      (s₀.data[emitBase + 3 * n + 1 + (qStartFn S d + p)]?).map Fin.val =
        some ((S.emittedArcs ⟨d, hQ ▸ hd⟩)[p]'hp).srcLocal)
    (hZeroDeg : ∀ u < 1 + (S.childSlice ⟨d, hQ ▸ hd⟩).length,
      (s₀.data[loopDegBase loopBase n m + u]?).map Fin.val = some 0) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let n_d := 1 + (S.childSlice dFin).length
    let m_d := (S.emittedArcs dFin).length
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 8 * m_d + 18 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offPrefix ∧
      t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t ∧
      (∀ u < n_d, (t.data[loopDegBase loopBase n m + u]?).map Fin.val =
        some (bucketDeg (S.emittedArcs dFin) u)) ∧
      (∀ k, (k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ k) → t.data[k]? = s₀.data[k]?) := by
  intro dFin n_d m_d
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 26 → offCountDeg + c < code.size := by
    intro c hc; rw [hSz]; unfold offCountDeg; omega
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hNdLe : n_d ≤ n := Nat.le_trans (by rw [hQ]; exact ownerVertexCount_le_Q S dFin) hQL
  have hQS0 : qStartFn S d ≤ m := hm.symm ▸ qStartFn_le_arcCount S d
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have hSucc : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S dFin.isLt
  have hMdLe : m_d ≤ m := by omega
  have hDegBnd : loopDegBase loopBase n m + n ≤ workCap := by
    unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hEmitBnd : emitBase + 3 * n + 1 + m ≤ workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  obtain ⟨s17, hStepsPre, pc17, hData17, hRegs17, hr15_17, hr13_17, r14v17⟩ :=
    countDegPre_steps subCode h32 input S hn hm hQ hd hFit hEmitFit hBits hpc hRegs hDataSz
      hStPtr hDegPtr hQStarts
  have hDisjDegSrc : ∀ p < m_d, ∀ u < n_d,
      emitBase + 3 * n + 1 + (qStartFn S d + p) < loopDegBase loopBase n m ∨
      loopDegBase loopBase n m + n_d ≤ emitBase + 3 * n + 1 + (qStartFn S d + p) :=
    fun p hp _ _ => emit_arc_disjoint_loopDeg hNdLe (by omega) hDisj
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun p s =>
    p ≤ m_d ∧ s.pc = offCountDeg + 17 ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    s.data.size = workCap ∧
    (reg s r15).val = loopDegBase loopBase n m ∧
    (reg s r13).val = emitBase + 3 * n + 1 + (qStartFn S d + p) ∧
    (reg s r14).val = emitBase + 3 * n + 1 + qStartFn S (d + 1) ∧
    (∀ u < n_d, (s.data[loopDegBase loopBase n m + u]?).map Fin.val =
      some (bucketDeg ((S.emittedArcs dFin).take p) u)) ∧
    (∀ k, (k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ k) → s.data[k]? = s₀.data[k]?)
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offPrefix ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (∀ u < n_d, (s.data[loopDegBase loopBase n m + u]?).map Fin.val =
      some (bucketDeg (S.emittedArcs dFin) u)) ∧
    (∀ k, (k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ k) → s.data[k]? = s₀.data[k]?)
  have hLoop := loop_steps_budget inv (fun p => m_d - p) (fun p => 1 + 8 * (m_d - p)) post
    (fun p s ⟨hpLe, hpcS, hRgS, hSzS, hr15S, hr13S, hr14S, hDegS, hOutS⟩ => by
      by_cases hpEq : p = m_d
      · subst hpEq
        have hGe : (reg s r14).val ≤ (reg s r13).val := by rw [hr13S, hr14S, hSucc]; exact Nat.le_refl _
        have stBr := step16_branchLt_false code input hpcS
          (at_countDeg subCode h32 (i := 17) (by decide)) (hPcLt 25 (by decide)) hGe
        refine Or.inl ⟨_, 1, by omega, steps_one stBr, ?_, hSzS,
          loopIterRegs_of_keep hRgS (fun _ _ => rfl), ?_, hOutS⟩
        · change offCountDeg + 25 = offPrefix; unfold offCountDeg offPrefix; omega
        · intro u hu; have hT := hDegS u hu; rwa [List.take_of_length_le (Nat.le_refl _)] at hT
      · have hpLt : p < m_d := Nat.lt_of_le_of_ne hpLe hpEq
        have hLtR : (reg s r13).val < (reg s r14).val := by
          rw [hr13S, hr14S, hSucc]; exact Nat.add_lt_add_left (Nat.add_lt_add_left hpLt _) _
        have st17 := step16_branchLt_true code input hpcS
          (at_countDeg subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide)) hLtR
        let s18 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s.regs, data := s.data, pc := offCountDeg + 18,
            regs_size := s.regs_size, data_size := s.data_size }
        have reg18 : ∀ r : Fin 16, reg s18 r = reg s r := fun _ => rfl
        have d18 : s18.data = s.data := rfl
        let ea := (S.emittedArcs dFin)[p]'hpLt
        have hEaBnd := S.emittedArc_bounds dFin (List.getElem_mem hpLt)
        have hEaSrcLt : ea.srcLocal < n_d := hEaBnd.2.1
        have hSrcS : (s.data[emitBase + 3 * n + 1 + (qStartFn S d + p)]?).map Fin.val =
            some ea.srcLocal := by
          rw [hOutS _ (hDisjDegSrc p hpLt ea.srcLocal hEaSrcLt)]
          exact hSrcOrig p hpLt
        have hMem18 : s18.data[(reg s18 r13).val]? = some ⟨ea.srcLocal, by omega⟩ := by
          rw [d18, reg18, hr13S]; exact mem_word_of_map hSrcS _
        obtain ⟨s19, st18, pc19, r12_19, keep19, d19⟩ :=
          step16_loadData code input (rfl : s18.pc = offCountDeg + 18)
            (at_countDeg subCode h32 (i := 18) (by decide)) hMem18 (hPcLt 19 (by decide))
        obtain ⟨s20, st19, pc20, r12_20, keep20, d20⟩ :=
          step16_add code input pc19 (at_countDeg subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
        have r12v20 : (reg s20 r12).val = loopDegBase loopBase n m + ea.srcLocal := by
          rw [r12_20, add_no_wrap]
          · rw [keep19 _ (by decide), reg18, hr15S, r12_19]
          · rw [keep19 _ (by decide), reg18, hr15S, r12_19]; dsimp only; omega
        have hDegLe : bucketDeg ((S.emittedArcs dFin).take p) ea.srcLocal ≤ p := by
          unfold bucketDeg
          exact Nat.le_trans (List.length_filter_le _ _)
            (by rw [List.length_take]; exact Nat.min_le_left _ _)
        have hMemDeg20 : s20.data[(reg s20 r12).val]? =
            some ⟨bucketDeg ((S.emittedArcs dFin).take p) ea.srcLocal, by omega⟩ := by
          rw [r12v20, d20, d19, d18]; exact mem_word_of_map (hDegS ea.srcLocal hEaSrcLt) _
        obtain ⟨s21, st20, pc21, r11_21, keep21, d21⟩ :=
          step16_loadData code input pc20 (at_countDeg subCode h32 (i := 20) (by decide)) hMemDeg20 (hPcLt 21 (by decide))
        obtain ⟨s22, st21, pc22, r11_22, keep22, d22⟩ :=
          step16_add code input pc21 (at_countDeg subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
        have h1eq21 : (reg s21 rOne).val = 1 := by
          rw [keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), reg18]; exact hRgS.entry.consts.one
        have r11v22 : (reg s22 r11).val = bucketDeg ((S.emittedArcs dFin).take p) ea.srcLocal + 1 := by
          rw [r11_22, add_no_wrap] <;> rw [r11_21, h1eq21] <;> dsimp only <;> omega
        have r12eq22 : (reg s22 r12).val = loopDegBase loopBase n m + ea.srcLocal := by
          rw [keep22 _ (by decide), keep21 _ (by decide), r12v20]
        have hBnd22 : (reg s22 r12).val < s22.data.size := by
          rw [r12eq22, d22, d21, d20, d19, d18]; omega
        obtain ⟨s23, st22, pc23, regs23, d23⟩ :=
          step16_storeData code input pc22 (at_countDeg subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide)) hBnd22
        have reg23 : ∀ r : Fin 16, reg s23 r = reg s22 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs23 r
        obtain ⟨s24, st23, pc24, r13_24, keep24, d24⟩ :=
          step16_add code input pc23 (at_countDeg subCode h32 (i := 23) (by decide)) (hPcLt 24 (by decide))
        have r13v24 : (reg s24 r13).val = emitBase + 3 * n + 1 + (qStartFn S d + (p + 1)) := by
          rw [r13_24, add_no_wrap]
          · rw [reg23, keep22 _ (by decide), keep21 _ (by decide), keep20 _ (by decide),
              keep19 _ (by decide), reg18, hr13S, reg23, keep22 _ (by decide), h1eq21]; omega
          · rw [reg23, keep22 _ (by decide), keep21 _ (by decide), keep20 _ (by decide),
              keep19 _ (by decide), reg18, hr13S, reg23, keep22 _ (by decide), h1eq21]; omega
        have st24 := step16_goto code input pc24
          (at_countDeg subCode h32 (i := 24) (by decide)) (hPcLt 17 (by decide))
        let s25 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s24.regs, data := s24.data, pc := offCountDeg + 17,
            regs_size := s24.regs_size, data_size := s24.data_size }
        have hStIter : Steps code input 8 s s25 :=
          Steps.cons st17 (Steps.cons st18 (Steps.cons st19 (Steps.cons st20
            (Steps.cons st21 (Steps.cons st22 (Steps.cons st23 (Steps.cons st24 (Steps.zero s25))))))))
        have hRg25 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s25 := by
          refine loopIterRegs_of_keep hRgS fun r hr => ?_
          have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
          have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
          have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
          change reg s24 r = reg s r
          rw [keep24 _ h13, reg23, keep22 _ h11, keep21 _ h11, keep20 _ h12, keep19 _ h12, reg18]
        have hData25 : s25.data = s22.data.set (reg s22 r12).val (reg s22 r11) hBnd22 := by
          change s24.data = _; rw [d24, d23]
        have hSame22 : s22.data = s.data := by rw [d22, d21, d20, d19, d18]
        refine Or.inr ⟨p + 1, s25, 8, by omega, by omega, hStIter, ?_⟩
        refine ⟨hpLt, rfl, hRg25, by rw [hData25, Array.size_set, hSame22]; exact hSzS,
          by change (reg s24 r15).val = _; rw [keep24 _ (by decide), reg23, keep22 _ (by decide),
            keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), reg18]; exact hr15S,
          r13v24,
          by change (reg s24 r14).val = _; rw [keep24 _ (by decide), reg23, keep22 _ (by decide),
            keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), reg18]; exact hr14S,
          ?_, ?_⟩
        · intro u hu
          have hTake : (S.emittedArcs dFin).take (p + 1) = (S.emittedArcs dFin).take p ++ [ea] :=
            List.take_succ_eq_append_getElem hpLt
          rw [hTake, bucketDeg, List.filter_append, List.length_append]
          rw [hData25]
          by_cases heq : u = ea.srcLocal
          · subst heq
            rw [mem_set_same s22.data r12eq22 hBnd22, Option.map_some, r11v22]
            simp [bucketDeg, ea]
          · have hbf : (ea.srcLocal == u) = false := beq_false_of_ne (fun e => heq e.symm)
            rw [mem_set_ne s22.data hBnd22 (fun e => heq (by rw [r12eq22] at e; omega)), hSame22]
            simpa [bucketDeg, hbf] using hDegS u hu
        · intro k hk
          rw [hData25, mem_set_ne s22.data hBnd22 (fun e => by rw [r12eq22] at e; rcases hk with hl | hr <;> omega),
            hSame22]
          exact hOutS k hk)
    m_d 0 s17 (by omega)
    ⟨Nat.zero_le _, pc17, hRegs17, by rw [hData17, hDataSz],
      hr15_17, by simpa only [Nat.add_zero] using hr13_17,
      r14v17,
      fun u hu => by rw [hData17]; simpa [bucketDeg] using hZeroDeg u hu,
      fun k _ => by rw [hData17]⟩
  obtain ⟨_, t, kL, hkL, hStL, hPost⟩ := hLoop
  exact ⟨t, 17 + kL, by omega, hStepsPre.append hStL, hPost⟩

private theorem prefixCursor_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {Q : Nat} {arcs : List (EmittedArc Q)}
    {n m root Q0 treeBase emitBase loopBase d forestUsed n_d : Nat}
    (hn_d : n_d ≤ n) (hArcsBnd : ∀ ea ∈ arcs, ea.srcLocal < n_d) (hm_d : arcs.length ≤ m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offPrefix)
    (hRegs : LoopIterRegs n m root Q0 treeBase emitBase loopBase d forestUsed s₀)
    (hDataSz : s₀.data.size = workCap)
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some n_d)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDegPtr : (s₀.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m))
    (hCurPtr : (s₀.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m))
    (hDegs : ∀ u < n_d, (s₀.data[loopDegBase loopBase n m + u]?).map Fin.val = some (bucketDeg arcs u)) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 7 * n_d + 12 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offScatter ∧
      t.data.size = workCap ∧
      LoopIterRegs n m root Q0 treeBase emitBase loopBase d forestUsed t ∧
      (∀ u < n_d, (t.data[loopCursorBase loopBase n m + u]?).map Fin.val = some (bucketStart arcs u)) ∧
      (∀ k, (k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ k) →
        t.data[k]? = s₀.data[k]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 19 → offPrefix + c < code.size := by
    intro c hc; rw [hSz]; unfold offPrefix; omega
  have hZero : (reg s₀ rZero).val = 0 := hRegs.entry.consts.zero
  have hL : (reg s₀ r8).val = loopBase := hRegs.entry.loopBaseVal
  have hStLt : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hDegBnd : loopDegBase loopBase n m + n ≤ loopCursorBase loopBase n m := by
    unfold loopCursorBase; omega
  have hCurBnd : loopCursorBase loopBase n m + n ≤ workCap := by
    unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hNdLt : n_d < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hDegLt : loopDegBase loopBase n m < 2 ^ bits := by omega
  have hCurLt : loopCursorBase loopBase n m < 2 ^ bits := by omega
  have hMemNd : s₀.data[(reg s₀ r8).val]? = some ⟨n_d, hNdLt⟩ := by rw [hL]; exact mem_word_of_map hNdAt hNdLt
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_loadData code input hpc (at_prefix subCode h32 (i := 0) (by decide)) hMemNd (hPcLt 1 (by decide))
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_imm code input pc1 (at_prefix subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
  have hMemSt : s2.data[(reg s2 r12).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d2, d1, show (reg s2 r12).val = statePtrAddr by rw [r12_2]; rfl]
    exact mem_word_of_map hStPtr _
  obtain ⟨s3, st2, pc3, r13_3, keep3, d3⟩ :=
    step16_loadData code input pc2 (at_prefix subCode h32 (i := 2) (by decide)) hMemSt (hPcLt 3 (by decide))
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_imm code input pc3 (at_prefix subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  obtain ⟨s5, st4, pc5, r12_5, keep5, d5⟩ :=
    step16_add code input pc4 (at_prefix subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have hAddr5 : (reg s5 r12).val = loopSubStateBase loopBase n m + 11 := by
    rw [r12_5, add_no_wrap]
    · rw [keep4 _ (by decide), r13_3, r12_4]; rfl
    · rw [keep4 _ (by decide), r13_3, r12_4]; dsimp only; change _ + 11 < 2 ^ bits; omega
  have hMemDeg : s5.data[(reg s5 r12).val]? = some ⟨loopDegBase loopBase n m, hDegLt⟩ := by
    rw [hAddr5, d5, d4, d3, d2, d1]; exact mem_word_of_map hDegPtr _
  obtain ⟨s6, st5, pc6, r14_6, keep6, d6⟩ :=
    step16_loadData code input pc5 (at_prefix subCode h32 (i := 5) (by decide)) hMemDeg (hPcLt 6 (by decide))
  obtain ⟨s7, st6, pc7, r12_7, keep7, d7⟩ :=
    step16_imm code input pc6 (at_prefix subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  obtain ⟨s8, st7, pc8, r12_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_prefix subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r13eq7 : (reg s7 r13).val = loopSubStateBase loopBase n m := by
    rw [keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), r13_3]
  have hAddr8 : (reg s8 r12).val = loopSubStateBase loopBase n m + 12 := by
    rw [r12_8, add_no_wrap]
    · rw [r13eq7, r12_7]; rfl
    · rw [r13eq7, r12_7]; change _ + 12 < 2 ^ bits; omega
  have hMemCur : s8.data[(reg s8 r12).val]? = some ⟨loopCursorBase loopBase n m, hCurLt⟩ := by
    rw [hAddr8, d8, d7, d6, d5, d4, d3, d2, d1]; exact mem_word_of_map hCurPtr _
  obtain ⟨s9, st8, pc9, r15_9, keep9, d9⟩ :=
    step16_loadData code input pc8 (at_prefix subCode h32 (i := 8) (by decide)) hMemCur (hPcLt 9 (by decide))
  obtain ⟨s10, st9, pc10, r11_10, keep10, d10⟩ :=
    step16_add code input pc9 (at_prefix subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  have r14eq9 : (reg s9 r14).val = loopDegBase loopBase n m := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), r14_6]
  have r11eq9 : (reg s9 r11).val = n_d := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide),
      keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), r11_1]
  have r11v10 : (reg s10 r11).val = loopDegBase loopBase n m + n_d := by
    rw [r11_10, add_no_wrap] <;> rw [r14eq9, r11eq9] <;> omega
  obtain ⟨s11, st10, pc11, r13_11, keep11, d11⟩ :=
    step16_mov code input pc10 (at_prefix subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have hStepsPre : Steps code input 11 s₀ s11 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3
      (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.cons st7
        (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.zero s11)))))))))))
  have hData11 : s11.data = s₀.data := by rw [d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hRegs11 : LoopIterRegs n m root Q0 treeBase emitBase loopBase d forestUsed s11 := by
    refine loopIterRegs_of_keep hRegs fun r hr => ?_
    have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep11 _ h13, keep10 _ h11, keep9 _ h15, keep8 _ h12, keep7 _ h12, keep6 _ h14,
      keep5 _ h12, keep4 _ h12, keep3 _ h13, keep2 _ h12, keep1 _ h11]
  have hr11_11 : (reg s11 r11).val = loopDegBase loopBase n m + n_d := by
    rw [keep11 _ (by decide), r11v10]
  have hr14_11 : (reg s11 r14).val = loopDegBase loopBase n m := by
    rw [keep11 _ (by decide), keep10 _ (by decide), r14eq9]
  have hr15_11 : (reg s11 r15).val = loopCursorBase loopBase n m := by
    rw [keep11 _ (by decide), keep10 _ (by decide), r15_9]
  have hr13_11 : (reg s11 r13).val = 0 := by
    rw [r13_11, keep10 _ (by decide), keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide),
      keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide),
      keep2 _ (by decide), keep1 _ (by decide), hZero]
  have hAllBnd : bucketStart arcs n_d = arcs.length := sum_bucketDeg_all arcs hArcsBnd
  have hMono : ∀ u ≤ n_d, bucketStart arcs u ≤ m := by
    intro u hu
    have hLeAll : bucketStart arcs u ≤ bucketStart arcs n_d := by
      suffices ∀ rem, u + rem ≤ n_d → bucketStart arcs u ≤ bucketStart arcs (u + rem) by
        simpa only [Nat.add_sub_cancel' hu] using this (n_d - u) (by omega)
      intro rem
      induction rem with
      | zero => intro _; exact Nat.le_refl _
      | succ k ih =>
        intro hk
        rw [← Nat.add_assoc, bucketStart_succ]
        exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    omega
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun u s =>
    u ≤ n_d ∧ s.pc = offPrefix + 11 ∧
    LoopIterRegs n m root Q0 treeBase emitBase loopBase d forestUsed s ∧
    s.data.size = workCap ∧
    (reg s r11).val = loopDegBase loopBase n m + n_d ∧
    (reg s r14).val = loopDegBase loopBase n m + u ∧
    (reg s r15).val = loopCursorBase loopBase n m + u ∧
    (reg s r13).val = bucketStart arcs u ∧
    (∀ j < u, (s.data[loopCursorBase loopBase n m + j]?).map Fin.val = some (bucketStart arcs j)) ∧
    (∀ k, (k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + u ≤ k) → s.data[k]? = s₀.data[k]?)
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offScatter ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q0 treeBase emitBase loopBase d forestUsed s ∧
    (∀ u < n_d, (s.data[loopCursorBase loopBase n m + u]?).map Fin.val = some (bucketStart arcs u)) ∧
    (∀ k, (k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ k) → s.data[k]? = s₀.data[k]?)
  have hLoop := loop_steps_budget inv (fun u => n_d - u) (fun u => 1 + 7 * (n_d - u)) post
    (fun u s ⟨huLe, hpcS, hRgS, hSzS, hr11S, hr14S, hr15S, hr13S, hCurS, hOutS⟩ => by
      by_cases huEq : u = n_d
      · subst huEq
        have hGe : (reg s r11).val ≤ (reg s r14).val := by omega
        have stBr := step16_branchLt_false code input hpcS
          (at_prefix subCode h32 (i := 11) (by decide)) (hPcLt 18 (by decide)) hGe
        refine Or.inl ⟨_, 1, by omega, steps_one stBr, ?_, hSzS,
          loopIterRegs_of_keep hRgS (fun _ _ => rfl), hCurS, hOutS⟩
        change offPrefix + 18 = offScatter; unfold offPrefix offScatter; omega
      · have huLt : u < n_d := by omega
        have hLtR : (reg s r14).val < (reg s r11).val := by omega
        have st11 := step16_branchLt_true code input hpcS
          (at_prefix subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide)) hLtR
        let s12 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s.regs, data := s.data, pc := offPrefix + 12,
            regs_size := s.regs_size, data_size := s.data_size }
        have reg12 : ∀ r : Fin 16, reg s12 r = reg s r := fun _ => rfl
        have d12 : s12.data = s.data := rfl
        have hBnd12 : (reg s12 r15).val < s12.data.size := by rw [reg12, d12]; omega
        obtain ⟨s13, st12, pc13, regs13, d13⟩ :=
          step16_storeData code input (rfl : s12.pc = offPrefix + 12)
            (at_prefix subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide)) hBnd12
        have reg13 : ∀ r : Fin 16, reg s13 r = reg s12 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs13 r
        have hDegBndU : loopDegBase loopBase n m + u < loopCursorBase loopBase n m := by omega
        have hDegU : s13.data[(reg s13 r14).val]? = some ⟨bucketDeg arcs u, by
            have := hMono (u + 1) (by omega)
            rw [bucketStart_succ] at this
            unfold loopWorkWords at hFit
            omega⟩ := by
          rw [d13, mem_set_ne s12.data hBnd12 (by rw [reg13, reg12, reg12]; omega), reg13, reg12, d12]
          rw [hr14S, hOutS _ (Or.inl hDegBndU)]
          exact mem_word_of_map (hDegs u huLt) _
        obtain ⟨s14, st13, pc14, r12_14, keep14, d14⟩ :=
          step16_loadData code input pc13 (at_prefix subCode h32 (i := 13) (by decide)) hDegU (hPcLt 14 (by decide))
        obtain ⟨s15, st14, pc15, r13_15, keep15, d15⟩ :=
          step16_add code input pc14 (at_prefix subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
        have r13v15 : (reg s15 r13).val = bucketStart arcs (u + 1) := by
          have hMon := hMono (u + 1) (by omega)
          rw [bucketStart_succ] at hMon ⊢
          rw [r13_15, add_no_wrap]
          · rw [keep14 _ (by decide), reg13, reg12, hr13S, r12_14]
          · rw [keep14 _ (by decide), reg13, reg12, hr13S, r12_14]; dsimp only; unfold loopWorkWords at hFit; omega
        have h1eq15 : (reg s15 rOne).val = 1 := by
          rw [keep15 _ (by decide), keep14 _ (by decide), reg13, reg12]; exact hRgS.entry.consts.one
        obtain ⟨s16, st15, pc16, r14_16, keep16, d16⟩ :=
          step16_add code input pc15 (at_prefix subCode h32 (i := 15) (by decide)) (hPcLt 16 (by decide))
        have r14v16 : (reg s16 r14).val = loopDegBase loopBase n m + (u + 1) := by
          rw [r14_16, add_no_wrap]
          · rw [keep15 _ (by decide), keep14 _ (by decide), reg13, reg12, hr14S, h1eq15]; omega
          · rw [keep15 _ (by decide), keep14 _ (by decide), reg13, reg12, hr14S, h1eq15]; omega
        obtain ⟨s17, st16, pc17, r15_17, keep17, d17⟩ :=
          step16_add code input pc16 (at_prefix subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
        have r15v17 : (reg s17 r15).val = loopCursorBase loopBase n m + (u + 1) := by
          rw [r15_17, add_no_wrap]
          · rw [keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), reg13, reg12, hr15S,
              keep16 _ (by decide), h1eq15]; omega
          · rw [keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), reg13, reg12, hr15S,
              keep16 _ (by decide), h1eq15]; omega
        have st17 := step16_goto code input pc17
          (at_prefix subCode h32 (i := 17) (by decide)) (hPcLt 11 (by decide))
        let s18 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s17.regs, data := s17.data, pc := offPrefix + 11,
            regs_size := s17.regs_size, data_size := s17.data_size }
        have hStIter : Steps code input 7 s s18 :=
          Steps.cons st11 (Steps.cons st12 (Steps.cons st13 (Steps.cons st14
            (Steps.cons st15 (Steps.cons st16 (Steps.cons st17 (Steps.zero s18)))))))
        have hRg18 : LoopIterRegs n m root Q0 treeBase emitBase loopBase d forestUsed s18 := by
          refine loopIterRegs_of_keep hRgS fun r hr => ?_
          have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
          have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
          have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
          have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
          change reg s17 r = reg s r
          rw [keep17 _ h15, keep16 _ h14, keep15 _ h13, keep14 _ h12, reg13, reg12]
        have hData18 : s18.data = s12.data.set (reg s12 r15).val (reg s12 r13) hBnd12 := by
          change s17.data = _; rw [d17, d16, d15, d14, d13]
        refine Or.inr ⟨u + 1, s18, 7, by omega, by omega, hStIter, ?_⟩
        refine ⟨huLt, rfl, hRg18, by rw [hData18, Array.size_set, d12]; exact hSzS,
          by change (reg s17 r11).val = _; rw [keep17 _ (by decide), keep16 _ (by decide),
            keep15 _ (by decide), keep14 _ (by decide), reg13, reg12]; exact hr11S,
          by change (reg s17 r14).val = _; rw [keep17 _ (by decide)]; exact r14v16,
          r15v17, by change (reg s17 r13).val = _; rw [keep17 _ (by decide), keep16 _ (by decide)]; exact r13v15,
          ?_, ?_⟩
        · intro j hj
          rw [hData18]
          by_cases hju : j = u
          · subst hju
            rw [mem_set_same s12.data (by rw [reg12]; exact hr15S) hBnd12, Option.map_some, reg12]
            exact congrArg some hr13S
          · rw [mem_set_ne s12.data hBnd12 (fun e => hju (by rw [reg12, hr15S] at e; omega)), d12]
            exact hCurS j (by omega)
        · intro k hk
          rw [hData18, mem_set_ne s12.data hBnd12 (fun e => by
            rw [reg12, hr15S] at e; rcases hk with hl | hr <;> omega), d12]
          exact hOutS k (by rcases hk with hl | hr; exact Or.inl hl; exact Or.inr (by omega)))
    n_d 0 s11 (by omega)
    ⟨Nat.zero_le _, pc11, hRegs11, by rw [hData11, hDataSz],
      hr11_11, hr14_11, hr15_11, hr13_11, fun j hj => by omega, fun k _ => by rw [hData11]⟩
  obtain ⟨_, t, kL, hkL, hStL, hPost⟩ := hLoop
  exact ⟨t, 11 + kL, by omega, hStepsPre.append hStL, hPost⟩

private theorem bucketDeg_take_le {Q : Nat} (arcs : List (EmittedArc Q)) (p u : Nat) :
    bucketDeg (arcs.take p) u ≤ bucketDeg arcs u := by
  unfold bucketDeg
  have hEq := congrArg (fun l => (l.filter (fun ea => ea.srcLocal == u)).length) (List.take_append_drop p arcs)
  rw [List.filter_append, List.length_append] at hEq
  omega

private theorem bucketStart_mono_le {Q : Nat} (arcs : List (EmittedArc Q)) {u v : Nat} (h : u ≤ v) :
    bucketStart arcs u ≤ bucketStart arcs v := by
  suffices ∀ rem, bucketStart arcs u ≤ bucketStart arcs (u + rem) by
    simpa only [Nat.add_sub_cancel' h] using this (v - u)
  intro rem
  induction rem with
  | zero => exact Nat.le_refl _
  | succ k ih =>
    rw [← Nat.add_assoc, bucketStart_succ]
    exact Nat.le_trans ih (Nat.le_add_right _ _)

private theorem bucketStart_disjoint {Q : Nat} (arcs : List (EmittedArc Q))
    {u v ju jv : Nat} (hne : u ≠ v) (hju : ju < bucketDeg arcs u) (hjv : jv < bucketDeg arcs v) :
    bucketStart arcs u + ju ≠ bucketStart arcs v + jv := by
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have h1 : bucketStart arcs u + bucketDeg arcs u ≤ bucketStart arcs v := by
      rw [← bucketStart_succ]
      exact bucketStart_mono_le arcs hlt
    omega
  · have h1 : bucketStart arcs v + bucketDeg arcs v ≤ bucketStart arcs u := by
      rw [← bucketStart_succ]
      exact bucketStart_mono_le arcs hgt
    omega

private theorem bucket_decompose_prefix {Q : Nat} (arcs : List (EmittedArc Q)) (k pos : Nat)
    (h : pos < bucketStart arcs k) :
    ∃ u < k, ∃ j < bucketDeg arcs u, pos = bucketStart arcs u + j := by
  induction k with
  | zero => simp [bucketStart_zero] at h
  | succ k ih =>
    rw [bucketStart_succ] at h
    by_cases hp : pos < bucketStart arcs k
    · obtain ⟨u, hu, j, hj, hEq⟩ := ih hp
      exact ⟨u, Nat.lt_succ_of_lt hu, j, hj, hEq⟩
    · exact ⟨k, Nat.lt_succ_self k, pos - bucketStart arcs k, by omega, by omega⟩

private theorem bucket_decompose {Q n_d : Nat} (arcs : List (EmittedArc Q))
    (hBnd : ∀ ea ∈ arcs, ea.srcLocal < n_d) {pos : Nat} (hPos : pos < arcs.length) :
    ∃ u : Fin n_d, ∃ j < bucketDeg arcs u.val, pos = bucketStart arcs u.val + j := by
  have hAll := sum_bucketDeg_all arcs hBnd
  obtain ⟨u, hu, j, hj, hEq⟩ := bucket_decompose_prefix arcs n_d pos (hAll ▸ hPos)
  exact ⟨⟨u, hu⟩, j, hj, hEq⟩

private theorem emit_arc_disjoint_scatter
    {n m emitBase loopBase idx len : Nat}
    (hIdx : idx < 3 * n + 3 * m + 3) (hLen : len ≤ m)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase) :
    emitBase + idx < loopBase + 3 ∨ loopBase + 3 + 2 * len ≤ emitBase + idx := by
  unfold loopWorkWords at hDisj
  unfold emitterWorkWords at hDisj
  rcases hDisj with hl | hr <;> omega

private theorem emit_arc_disjoint_cursor
    {n m emitBase loopBase idx n_d : Nat}
    (hIdx : idx < 3 * n + 3 * m + 3) (hn_d : n_d ≤ n)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase) :
    emitBase + idx < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ emitBase + idx := by
  unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
  unfold loopWorkWords at hDisj
  unfold emitterWorkWords at hDisj
  omega

private theorem emit_arc_disjoint_entry
    {n m emitBase loopBase idx len : Nat}
    (hIdx : idx < 3 * n + 3 * m + 3) (hLen : len ≤ m)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase) :
    emitBase + idx < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + len ≤ emitBase + idx := by
  unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
  unfold loopWorkWords at hDisj
  unfold emitterWorkWords at hDisj
  omega

private theorem list_getElem_congr {α : Type _} {xs ys : List α} (h : xs = ys)
    {j : Nat} (hx : j < xs.length) (hy : j < ys.length) :
    xs[j]'hx = ys[j]'hy := by
  subst h; rfl

private theorem scatter_slot_disjoint {n m loopBase m_d sIdx pos eaSrc : Nat}
    (hsIdx : sIdx < m_d) (hPos : pos < m_d) (hm_d : m_d ≤ m) (hSrc : eaSrc < n) :
    (loopBase + 3 + sIdx ≠ loopBase + 3 + m_d + pos) ∧
    (loopBase + 3 + m_d + sIdx ≠ loopBase + 3 + pos) ∧
    (loopBase + 3 + sIdx ≠ loopSortEntryBase loopBase n m + pos) ∧
    (loopBase + 3 + m_d + sIdx ≠ loopSortEntryBase loopBase n m + pos) ∧
    (loopSortEntryBase loopBase n m + sIdx ≠ loopCursorBase loopBase n m + eaSrc) ∧
    (loopBase + 3 + sIdx ≠ loopCursorBase loopBase n m + eaSrc) ∧
    (loopBase + 3 + m_d + sIdx ≠ loopCursorBase loopBase n m + eaSrc) ∧
    (loopSortEntryBase loopBase n m + sIdx ≠ loopBase + 3 + pos) ∧
    (loopSortEntryBase loopBase n m + sIdx ≠ loopBase + 3 + m_d + pos) := by
  unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
    rawInputCap rawWorkCap
  omega

private theorem scatterPre_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offScatter)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)) :
    ∃ s4, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 4 s₀ s4 ∧
      s4.pc = offScatter + 4 ∧ s4.data = s₀.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s4 ∧
      (reg s4 r13).val = qStartFn S d := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 5 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hN : (reg s₀ rN).val = n := hRegs.entry.consts.nVal
  have hE : (reg s₀ r7).val = emitBase := hRegs.entry.emitBaseVal
  have hdVal : (reg s₀ r9).val = d := hRegs.dVal
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hQS0 : qStartFn S d ≤ m := hm.symm ▸ qStartFn_le_arcCount S d
  have hEmitBnd : emitBase + 2 * n + d < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h2NLt : 2 * n < 2 ^ bits := by unfold emitterWorkWords at hEmitFit; omega
  obtain ⟨s1, st0, pc1, r12_1, keep1, d1⟩ :=
    step16_add code input hpc (at_scatter subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have r12v1 : (reg s1 r12).val = 2 * n := by rw [r12_1, add_no_wrap] <;> rw [hN] <;> omega
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_add code input pc1 (at_scatter subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
  have r12v2 : (reg s2 r12).val = emitBase + 2 * n := by
    rw [r12_2, add_no_wrap] <;> rw [keep1 _ (by decide), hE, r12v1] <;> omega
  obtain ⟨s3, st2, pc3, r12_3, keep3, d3⟩ :=
    step16_add code input pc2 (at_scatter subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  have r12v3 : (reg s3 r12).val = emitBase + 2 * n + d := by
    rw [r12_3, add_no_wrap] <;> rw [r12v2, keep2 _ (by decide), keep1 _ (by decide), hdVal] <;> omega
  have hMemQ : s3.data[(reg s3 r12).val]? = some ⟨qStartFn S d, by unfold emitterWorkWords at hEmitFit; omega⟩ := by
    rw [r12v3, d3, d2, d1]; exact mem_word_of_map (hQStarts d (Nat.le_of_lt hd)) _
  obtain ⟨s4, st3, pc4, r13_4, keep4, d4⟩ :=
    step16_loadData code input pc3 (at_scatter subCode h32 (i := 3) (by decide)) hMemQ (hPcLt 4 (by decide))
  refine ⟨s4, Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.zero s4)))),
    by rw [pc4], by rw [d4, d3, d2, d1], loopIterRegs_of_keep hRegs fun r hr => ?_, by rw [r13_4]⟩
  have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
  have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
  rw [keep4 _ h13, keep3 _ h12, keep2 _ h12, keep1 _ h12]

private theorem scatterHdr_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offScatter + 4)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)) :
    ∃ s9, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 5 s₀ s9 ∧
      s9.pc = offScatter + 9 ∧ s9.data = s₀.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s9 ∧
      (reg s9 r13).val = (reg s₀ r13).val ∧
      (reg s9 r14).val = qStartFn S (d + 1) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 10 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s₀ rN).val = n := hRegs.entry.consts.nVal
  have hE : (reg s₀ r7).val = emitBase := hRegs.entry.emitBaseVal
  have hdVal : (reg s₀ r9).val = d := hRegs.dVal
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have h2NLt : 2 * n < 2 ^ bits := by unfold emitterWorkWords at hEmitFit; omega
  have hEmitBnd : emitBase + 2 * n + d + 1 < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  obtain ⟨s5, st4, pc5, r12_5, keep5, d5⟩ :=
    step16_add code input hpc (at_scatter subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have r12v5 : (reg s5 r12).val = 2 * n := by rw [r12_5, add_no_wrap] <;> rw [hN] <;> omega
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_scatter subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = emitBase + 2 * n := by
    rw [r12_6, add_no_wrap] <;> rw [keep5 _ (by decide), hE, r12v5] <;> omega
  obtain ⟨s7, st6, pc7, r12_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_scatter subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have r12v7 : (reg s7 r12).val = emitBase + 2 * n + d := by
    rw [r12_7, add_no_wrap] <;> rw [r12v6, keep6 _ (by decide), keep5 _ (by decide), hdVal] <;> omega
  obtain ⟨s8, st7, pc8, r12_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_scatter subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r12v8 : (reg s8 r12).val = emitBase + 2 * n + (d + 1) := by
    rw [r12_8, add_no_wrap]
    · rw [r12v7, keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), hOne]; omega
    · rw [r12v7, keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), hOne]; omega
  have hMemQ1 : s8.data[(reg s8 r12).val]? = some ⟨qStartFn S (d + 1), by unfold emitterWorkWords at hEmitFit; omega⟩ := by
    rw [r12v8, d8, d7, d6, d5]; exact mem_word_of_map (hQStarts (d + 1) (by omega)) _
  obtain ⟨s9, st8, pc9, r14_9, keep9, d9⟩ :=
    step16_loadData code input pc8 (at_scatter subCode h32 (i := 8) (by decide)) hMemQ1 (hPcLt 9 (by decide))
  refine ⟨s9, Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.cons st7 (Steps.cons st8 (Steps.zero s9))))),
    pc9, by rw [d9, d8, d7, d6, d5], loopIterRegs_of_keep hRegs fun r hr => ?_,
    ?_, by rw [r14_9]⟩
  · have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    rw [keep9 _ h14, keep8 _ h12, keep7 _ h12, keep6 _ h12, keep5 _ h12]
  · rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide)]

private theorem scatterBodyA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed qd p u pos : Nat}
    (hu : u < n) (hp : qd + p < m) (hPos : pos < m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₁₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₁₀.pc = offScatter + 10) (hDataSz : s₁₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₁₀)
    (hr13 : (reg s₁₀ r13).val = qd + p)
    (hSrc : (s₁₀.data[emitBase + 3 * n + 1 + (qd + p)]?).map Fin.val = some u)
    (hStPtr : (s₁₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hCurPtr : (s₁₀.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m))
    (hCurU : (s₁₀.data[loopCursorBase loopBase n m + u]?).map Fin.val = some pos) :
    ∃ s25, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 15 s₁₀ s25 ∧
      s25.pc = offScatter + 25 ∧ s25.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s25 ∧
      (reg s25 r11).val = u ∧ (reg s25 r13).val = qd + p ∧ (reg s25 r14).val = pos ∧
      (∀ k, (k = loopCursorBase loopBase n m + u →
          (s25.data[k]?).map Fin.val = some (pos + 1)) ∧
        (k ≠ loopCursorBase loopBase n m + u → s25.data[k]? = s₁₀.data[k]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 26 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hOne : (reg s₁₀ rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s₁₀ rN).val = n := hRegs.entry.consts.nVal
  have hE : (reg s₁₀ r7).val = emitBase := hRegs.entry.emitBaseVal
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hCurBnd : loopCursorBase loopBase n m + n ≤ workCap := by
    unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hEmitBnd : emitBase + 3 * n + 1 + m ≤ workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h3NLt : 3 * n < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  -- 10..15: load u
  obtain ⟨s11, st10, pc11, r11_11, keep11, d11⟩ :=
    step16_add code input hpc (at_scatter subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have r11v11 : (reg s11 r11).val = 2 * n := by rw [r11_11, add_no_wrap] <;> rw [hN] <;> omega
  obtain ⟨s12, st11, pc12, r11_12, keep12, d12⟩ :=
    step16_add code input pc11 (at_scatter subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
  have r11v12 : (reg s12 r11).val = 3 * n := by
    rw [r11_12, add_no_wrap] <;> rw [r11v11, keep11 _ (by decide), hN] <;> omega
  obtain ⟨s13, st12, pc13, r11_13, keep13, d13⟩ :=
    step16_add code input pc12 (at_scatter subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
  have r11v13 : (reg s13 r11).val = emitBase + 3 * n := by
    rw [r11_13, add_no_wrap]
    · rw [keep12 _ (by decide), keep11 _ (by decide), hE, r11v12]
    · rw [keep12 _ (by decide), keep11 _ (by decide), hE, r11v12]; omega
  obtain ⟨s14, st13, pc14, r11_14, keep14, d14⟩ :=
    step16_add code input pc13 (at_scatter subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have r11v14 : (reg s14 r11).val = emitBase + 3 * n + 1 := by
    rw [r11_14, add_no_wrap]
    · rw [r11v13, keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), hOne]
    · rw [r11v13, keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), hOne]; omega
  obtain ⟨s15, st14, pc15, r11_15, keep15, d15⟩ :=
    step16_add code input pc14 (at_scatter subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have r13eq14 : (reg s14 r13).val = qd + p := by
    rw [keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), hr13]
  have r11v15 : (reg s15 r11).val = emitBase + 3 * n + 1 + (qd + p) := by
    rw [r11_15, add_no_wrap] <;> rw [r11v14, r13eq14] <;> omega
  have hMemSrc : s15.data[(reg s15 r11).val]? = some ⟨u, by omega⟩ := by
    rw [r11v15, d15, d14, d13, d12, d11]; exact mem_word_of_map hSrc _
  obtain ⟨s16, st15, pc16, r11_16, keep16, d16⟩ :=
    step16_loadData code input pc15 (at_scatter subCode h32 (i := 15) (by decide)) hMemSrc (hPcLt 16 (by decide))
  -- 16..24: cursor[u]++
  obtain ⟨s17, st16, pc17, r15_17, keep17, d17⟩ :=
    step16_imm code input pc16 (at_scatter subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have hMemSt : s17.data[(reg s17 r15).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d17, d16, d15, d14, d13, d12, d11, show (reg s17 r15).val = statePtrAddr by rw [r15_17]; rfl]
    exact mem_word_of_map hStPtr _
  obtain ⟨s18, st17, pc18, r12_18, keep18, d18⟩ :=
    step16_loadData code input pc17 (at_scatter subCode h32 (i := 17) (by decide)) hMemSt (hPcLt 18 (by decide))
  obtain ⟨s19, st18, pc19, r15_19, keep19, d19⟩ :=
    step16_imm code input pc18 (at_scatter subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  obtain ⟨s20, st19, pc20, r12_20, keep20, d20⟩ :=
    step16_add code input pc19 (at_scatter subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  have hAddr20 : (reg s20 r12).val = loopSubStateBase loopBase n m + 12 := by
    rw [r12_20, add_no_wrap]
    · rw [keep19 _ (by decide), r12_18, r15_19]; rfl
    · rw [keep19 _ (by decide), r12_18, r15_19]; dsimp only; change _ + 12 < 2 ^ bits; omega
  have hMemCur : s20.data[(reg s20 r12).val]? = some ⟨loopCursorBase loopBase n m, by omega⟩ := by
    rw [hAddr20, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11]; exact mem_word_of_map hCurPtr _
  obtain ⟨s21, st20, pc21, r12_21, keep21, d21⟩ :=
    step16_loadData code input pc20 (at_scatter subCode h32 (i := 20) (by decide)) hMemCur (hPcLt 21 (by decide))
  have r11eq21 : (reg s21 r11).val = u := by
    rw [keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide),
      keep17 _ (by decide), r11_16]
  obtain ⟨s22, st21, pc22, r12_22, keep22, d22⟩ :=
    step16_add code input pc21 (at_scatter subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
  have r12v22 : (reg s22 r12).val = loopCursorBase loopBase n m + u := by
    rw [r12_22, add_no_wrap] <;> rw [r12_21, r11eq21] <;> dsimp only <;> omega
  have hMemCurU : s22.data[(reg s22 r12).val]? = some ⟨pos, by omega⟩ := by
    rw [r12v22, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11]; exact mem_word_of_map hCurU _
  obtain ⟨s23, st22, pc23, r14_23, keep23, d23⟩ :=
    step16_loadData code input pc22 (at_scatter subCode h32 (i := 22) (by decide)) hMemCurU (hPcLt 23 (by decide))
  obtain ⟨s24, st23, pc24, r15_24, keep24, d24⟩ :=
    step16_add code input pc23 (at_scatter subCode h32 (i := 23) (by decide)) (hPcLt 24 (by decide))
  have h1eq23 : (reg s23 rOne).val = 1 := by
    rw [keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide), keep20 _ (by decide),
      keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide),
      keep15 _ (by decide), keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide),
      keep11 _ (by decide), hOne]
  have r15v24 : (reg s24 r15).val = pos + 1 := by
    rw [r15_24, add_no_wrap] <;> rw [r14_23, h1eq23] <;> dsimp only <;> omega
  have r12eq24 : (reg s24 r12).val = loopCursorBase loopBase n m + u := by
    rw [keep24 _ (by decide), keep23 _ (by decide), r12v22]
  have hData24 : s24.data = s₁₀.data := by
    rw [d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14, d13, d12, d11]
  have hBnd24 : (reg s24 r12).val < s24.data.size := by rw [r12eq24, hData24, hDataSz]; omega
  obtain ⟨s25, st24, pc25, regs25, d25⟩ :=
    step16_storeData code input pc24 (at_scatter subCode h32 (i := 24) (by decide)) (hPcLt 25 (by decide)) hBnd24
  have reg25 : ∀ r : Fin 16, reg s25 r = reg s24 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs25 r
  have hSteps : Steps code input 15 s₁₀ s25 :=
    Steps.cons st10 (Steps.cons st11 (Steps.cons st12 (Steps.cons st13 (Steps.cons st14
      (Steps.cons st15 (Steps.cons st16 (Steps.cons st17 (Steps.cons st18 (Steps.cons st19
        (Steps.cons st20 (Steps.cons st21 (Steps.cons st22 (Steps.cons st23 (Steps.cons st24
          (Steps.zero s25)))))))))))))))
  refine ⟨s25, hSteps, pc25, by rw [d25, Array.size_set, hData24, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [reg25, keep24 _ h15, keep23 _ h14, keep22 _ h12, keep21 _ h12, keep20 _ h12, keep19 _ h15,
      keep18 _ h12, keep17 _ h15, keep16 _ h11, keep15 _ h11, keep14 _ h11, keep13 _ h11,
      keep12 _ h11, keep11 _ h11]
  · rw [reg25, keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), r11eq21]
  · rw [reg25, keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide),
      keep16 _ (by decide), keep15 _ (by decide), r13eq14]
  · rw [reg25, keep24 _ (by decide), r14_23]
  · intro k; rw [d25]
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · rw [mem_set_same s24.data (r12eq24.trans hk.symm) hBnd24, Option.map_some, r15v24]
    · rw [mem_set_ne s24.data hBnd24 (fun e => hne (e.trans r12eq24)), hData24]

private theorem scatterBodyB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed u hdLoc pos qd p : Nat}
    (hhd : hdLoc < n) (hp : qd + p < m) (hPos : pos < m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    {s25 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s25.pc = offScatter + 25) (hDataSz : s25.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s25)
    (hr11 : (reg s25 r11).val = u) (hr13 : (reg s25 r13).val = qd + p) (hr14 : (reg s25 r14).val = pos)
    (hHead : (s25.data[emitBase + 3 * n + m + 1 + (qd + p)]?).map Fin.val = some hdLoc) :
    ∃ s36, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 11 s25 s36 ∧
      s36.pc = offScatter + 36 ∧ s36.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s36 ∧
      (reg s36 r11).val = hdLoc ∧ (reg s36 r13).val = qd + p ∧ (reg s36 r14).val = pos ∧
      (∀ k, (k = loopBase + 3 + pos → (s36.data[k]?).map Fin.val = some u) ∧
        (k ≠ loopBase + 3 + pos → s36.data[k]? = s25.data[k]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 37 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hOne : (reg s25 rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s25 rN).val = n := hRegs.entry.consts.nVal
  have hM : (reg s25 rM).val = m := hRegs.entry.consts.mVal
  have hE : (reg s25 r7).val = emitBase := hRegs.entry.emitBaseVal
  have hL : (reg s25 r8).val = loopBase := hRegs.entry.loopBaseVal
  have hSrcBnd : loopBase + 3 + pos < workCap := by
    unfold loopWorkWords at hFit; omega
  have hEmitBnd : emitBase + 3 * n + m + 1 + (qd + p) < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h3NLt : 3 * n + m < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  -- 25..28: store src at loopBase + 3 + pos
  obtain ⟨s26, st25, pc26, r12_26, keep26, d26⟩ :=
    step16_imm code input hpc (at_scatter subCode h32 (i := 25) (by decide)) (hPcLt 26 (by decide))
  obtain ⟨s27, st26, pc27, r12_27, keep27, d27⟩ :=
    step16_add code input pc26 (at_scatter subCode h32 (i := 26) (by decide)) (hPcLt 27 (by decide))
  have r12v27 : (reg s27 r12).val = loopBase + 3 := by
    rw [r12_27, add_no_wrap]
    · rw [keep26 _ (by decide), hL, r12_26]; rfl
    · rw [keep26 _ (by decide), hL, r12_26]; change loopBase + 3 < 2 ^ bits; omega
  obtain ⟨s28, st27, pc28, r12_28, keep28, d28⟩ :=
    step16_add code input pc27 (at_scatter subCode h32 (i := 27) (by decide)) (hPcLt 28 (by decide))
  have r12v28 : (reg s28 r12).val = loopBase + 3 + pos := by
    rw [r12_28, add_no_wrap]
    · rw [r12v27, keep27 _ (by decide), keep26 _ (by decide), hr14]
    · rw [r12v27, keep27 _ (by decide), keep26 _ (by decide), hr14]; omega
  have hData28 : s28.data = s25.data := by rw [d28, d27, d26]
  have hBnd28 : (reg s28 r12).val < s28.data.size := by rw [r12v28, hData28, hDataSz]; exact hSrcBnd
  obtain ⟨s29, st28, pc29, regs29, d29⟩ :=
    step16_storeData code input pc28 (at_scatter subCode h32 (i := 28) (by decide)) (hPcLt 29 (by decide)) hBnd28
  have reg29 : ∀ r : Fin 16, reg s29 r = reg s28 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs29 r
  have r11eq29 : (reg s29 r11).val = u := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hr11]
  -- 29..35: load head
  have hNeq29 : (reg s29 rN).val = n := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hN]
  have hMeq29 : (reg s29 rM).val = m := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hM]
  have hEeq29 : (reg s29 r7).val = emitBase := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hE]
  have h1eq29 : (reg s29 rOne).val = 1 := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hOne]
  have r13eq29 : (reg s29 r13).val = qd + p := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hr13]
  have r14eq29 : (reg s29 r14).val = pos := by
    rw [reg29, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hr14]
  obtain ⟨s30, st29, pc30, r12_30, keep30, d30⟩ :=
    step16_add code input pc29 (at_scatter subCode h32 (i := 29) (by decide)) (hPcLt 30 (by decide))
  have r12v30 : (reg s30 r12).val = 2 * n := by rw [r12_30, add_no_wrap] <;> rw [hNeq29] <;> omega
  obtain ⟨s31, st30, pc31, r12_31, keep31, d31⟩ :=
    step16_add code input pc30 (at_scatter subCode h32 (i := 30) (by decide)) (hPcLt 31 (by decide))
  have r12v31 : (reg s31 r12).val = 3 * n := by
    rw [r12_31, add_no_wrap] <;> rw [r12v30, keep30 _ (by decide), hNeq29] <;> omega
  obtain ⟨s32, st31, pc32, r12_32, keep32, d32⟩ :=
    step16_add code input pc31 (at_scatter subCode h32 (i := 31) (by decide)) (hPcLt 32 (by decide))
  have r12v32 : (reg s32 r12).val = 3 * n + m := by
    rw [r12_32, add_no_wrap] <;> rw [r12v31, keep31 _ (by decide), keep30 _ (by decide), hMeq29] <;> omega
  obtain ⟨s33, st32, pc33, r12_33, keep33, d33⟩ :=
    step16_add code input pc32 (at_scatter subCode h32 (i := 32) (by decide)) (hPcLt 33 (by decide))
  have r12v33 : (reg s33 r12).val = emitBase + 3 * n + m := by
    rw [r12_33, add_no_wrap]
    · rw [keep32 _ (by decide), keep31 _ (by decide), keep30 _ (by decide), hEeq29, r12v32]; omega
    · rw [keep32 _ (by decide), keep31 _ (by decide), keep30 _ (by decide), hEeq29, r12v32]; omega
  obtain ⟨s34, st33, pc34, r12_34, keep34, d34⟩ :=
    step16_add code input pc33 (at_scatter subCode h32 (i := 33) (by decide)) (hPcLt 34 (by decide))
  have r12v34 : (reg s34 r12).val = emitBase + 3 * n + m + 1 := by
    rw [r12_34, add_no_wrap]
    · rw [r12v33, keep33 _ (by decide), keep32 _ (by decide), keep31 _ (by decide), keep30 _ (by decide), h1eq29]
    · rw [r12v33, keep33 _ (by decide), keep32 _ (by decide), keep31 _ (by decide), keep30 _ (by decide), h1eq29]; omega
  obtain ⟨s35, st34, pc35, r12_35, keep35, d35⟩ :=
    step16_add code input pc34 (at_scatter subCode h32 (i := 34) (by decide)) (hPcLt 35 (by decide))
  have r12v35 : (reg s35 r12).val = emitBase + 3 * n + m + 1 + (qd + p) := by
    rw [r12_35, add_no_wrap]
    · rw [r12v34, keep34 _ (by decide), keep33 _ (by decide), keep32 _ (by decide),
        keep31 _ (by decide), keep30 _ (by decide), r13eq29]
    · rw [r12v34, keep34 _ (by decide), keep33 _ (by decide), keep32 _ (by decide),
        keep31 _ (by decide), keep30 _ (by decide), r13eq29]; omega
  have hNeHead : emitBase + 3 * n + m + 1 + (qd + p) ≠ (reg s28 r12).val := by
    rw [r12v28]
    unfold loopWorkWords emitterWorkWords at hDisj
    omega
  have hNeHead' : emitBase + 3 * n + m + 1 + (qd + p) ≠ loopBase + 3 + pos := by
    rw [← r12v28]; exact hNeHead
  have hData35 : s35.data = s29.data := by rw [d35, d34, d33, d32, d31, d30]
  have hMemHead : s35.data[(reg s35 r12).val]? = some ⟨hdLoc, by omega⟩ := by
    rw [r12v35, hData35, d29, mem_set_ne s28.data hBnd28 (by rw [r12v28]; exact hNeHead'), hData28]
    exact mem_word_of_map hHead _
  obtain ⟨s36, st35, pc36, r11_36, keep36, d36⟩ :=
    step16_loadData code input pc35 (at_scatter subCode h32 (i := 35) (by decide)) hMemHead (hPcLt 36 (by decide))
  have hSteps : Steps code input 11 s25 s36 :=
    Steps.cons st25 (Steps.cons st26 (Steps.cons st27 (Steps.cons st28 (Steps.cons st29
      (Steps.cons st30 (Steps.cons st31 (Steps.cons st32 (Steps.cons st33 (Steps.cons st34
        (Steps.cons st35 (Steps.zero s36)))))))))))
  refine ⟨s36, hSteps, pc36,
    by rw [d36, hData35, d29, Array.size_set, hData28, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    rw [keep36 _ h11, keep35 _ h12, keep34 _ h12, keep33 _ h12, keep32 _ h12, keep31 _ h12,
      keep30 _ h12, reg29, keep28 _ h12, keep27 _ h12, keep26 _ h12]
  · rw [r11_36]
  · rw [keep36 _ (by decide), keep35 _ (by decide), keep34 _ (by decide), keep33 _ (by decide),
      keep32 _ (by decide), keep31 _ (by decide), keep30 _ (by decide), r13eq29]
  · rw [keep36 _ (by decide), keep35 _ (by decide), keep34 _ (by decide), keep33 _ (by decide),
      keep32 _ (by decide), keep31 _ (by decide), keep30 _ (by decide), r14eq29]
  · intro k; rw [d36, hData35, d29]
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · rw [mem_set_same s28.data (r12v28.trans hk.symm) hBnd28, Option.map_some,
        show (reg s28 r11).val = u by rw [keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), hr11]]
    · rw [mem_set_ne s28.data hBnd28 (fun e => hne (e.trans r12v28)), hData28]

private theorem scatterBodyC_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed hdLoc m_d pos qd p : Nat}
    (hm_d : m_d ≤ m) (hPos : pos < m_d) (hp : qd + p < m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s36 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s36.pc = offScatter + 36) (hDataSz : s36.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s36)
    (hr11 : (reg s36 r11).val = hdLoc) (hr13 : (reg s36 r13).val = qd + p) (hr14 : (reg s36 r14).val = pos)
    (hMdAt : (s36.data[loopBase + 1]?).map Fin.val = some m_d) :
    ∃ s50, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 14 s36 s50 ∧
      s50.pc = offScatter + 50 ∧ s50.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s50 ∧
      (reg s50 r12).val = emitBase + 3 * n + 2 * m + 1 + (qd + p) ∧
      (reg s50 r13).val = qd + p ∧ (reg s50 r14).val = pos ∧
      (∀ k, (k = loopBase + 3 + m_d + pos → (s50.data[k]?).map Fin.val = some hdLoc) ∧
        (k ≠ loopBase + 3 + m_d + pos → s50.data[k]? = s36.data[k]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 51 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hOne : (reg s36 rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s36 rN).val = n := hRegs.entry.consts.nVal
  have hM : (reg s36 rM).val = m := hRegs.entry.consts.mVal
  have hE : (reg s36 r7).val = emitBase := hRegs.entry.emitBaseVal
  have hL : (reg s36 r8).val = loopBase := hRegs.entry.loopBaseVal
  have hHeadBnd : loopBase + 3 + m_d + pos < workCap := by
    unfold loopWorkWords at hFit; omega
  have hEmitBnd : emitBase + 3 * n + 2 * m + 1 + (qd + p) < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h3NLt : 3 * n + 2 * m < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  -- 36..42: store headLocal at loopBase + 3 + m_d + pos
  obtain ⟨s37, st36, pc37, r15_37, keep37, d37⟩ :=
    step16_add code input hpc (at_scatter subCode h32 (i := 36) (by decide)) (hPcLt 37 (by decide))
  have r15v37 : (reg s37 r15).val = loopBase + 1 := by
    rw [r15_37, add_no_wrap] <;> rw [hL, hOne] <;> omega
  have hMemMd : s37.data[(reg s37 r15).val]? = some ⟨m_d, by omega⟩ := by
    rw [r15v37, d37]; exact mem_word_of_map hMdAt _
  obtain ⟨s38, st37, pc38, r12_38, keep38, d38⟩ :=
    step16_loadData code input pc37 (at_scatter subCode h32 (i := 37) (by decide)) hMemMd (hPcLt 38 (by decide))
  obtain ⟨s39, st38, pc39, r15_39, keep39, d39⟩ :=
    step16_imm code input pc38 (at_scatter subCode h32 (i := 38) (by decide)) (hPcLt 39 (by decide))
  obtain ⟨s40, st39, pc40, r15_40, keep40, d40⟩ :=
    step16_add code input pc39 (at_scatter subCode h32 (i := 39) (by decide)) (hPcLt 40 (by decide))
  have hLeq39 : (reg s39 r8).val = loopBase := by
    rw [keep39 _ (by decide), keep38 _ (by decide), keep37 _ (by decide), hL]
  have r15v40 : (reg s40 r15).val = loopBase + 3 := by
    rw [r15_40, add_no_wrap]
    · rw [hLeq39, r15_39]; rfl
    · rw [hLeq39, r15_39]; change loopBase + 3 < 2 ^ bits; omega
  obtain ⟨s41, st40, pc41, r15_41, keep41, d41⟩ :=
    step16_add code input pc40 (at_scatter subCode h32 (i := 40) (by decide)) (hPcLt 41 (by decide))
  have r15v41 : (reg s41 r15).val = loopBase + 3 + m_d := by
    rw [r15_41, add_no_wrap] <;> rw [r15v40, keep40 _ (by decide), keep39 _ (by decide), r12_38] <;> dsimp only <;> omega
  obtain ⟨s42, st41, pc42, r15_42, keep42, d42⟩ :=
    step16_add code input pc41 (at_scatter subCode h32 (i := 41) (by decide)) (hPcLt 42 (by decide))
  have r14eq41 : (reg s41 r14).val = pos := by
    rw [keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), keep38 _ (by decide),
      keep37 _ (by decide), hr14]
  have r15v42 : (reg s42 r15).val = loopBase + 3 + m_d + pos := by
    rw [r15_42, add_no_wrap] <;> rw [r15v41, r14eq41] <;> omega
  have r11eq42 : (reg s42 r11).val = hdLoc := by
    rw [keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide),
      keep38 _ (by decide), keep37 _ (by decide), hr11]
  have hData42 : s42.data = s36.data := by rw [d42, d41, d40, d39, d38, d37]
  have hBnd42 : (reg s42 r15).val < s42.data.size := by rw [r15v42, hData42, hDataSz]; exact hHeadBnd
  obtain ⟨s43, st42, pc43, regs43, d43⟩ :=
    step16_storeData code input pc42 (at_scatter subCode h32 (i := 42) (by decide)) (hPcLt 43 (by decide)) hBnd42
  have reg43 : ∀ r : Fin 16, reg s43 r = reg s42 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs43 r
  -- 43..49: compute emitBase + 3*n + 2*m + 1 + qStart + p
  have hNeq43 : (reg s43 rN).val = n := by
    rw [reg43, keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide),
      keep38 _ (by decide), keep37 _ (by decide), hN]
  have hMeq43 : (reg s43 rM).val = m := by
    rw [reg43, keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide),
      keep38 _ (by decide), keep37 _ (by decide), hM]
  have hEeq43 : (reg s43 r7).val = emitBase := by
    rw [reg43, keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide),
      keep38 _ (by decide), keep37 _ (by decide), hE]
  have h1eq43 : (reg s43 rOne).val = 1 := by
    rw [reg43, keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide),
      keep38 _ (by decide), keep37 _ (by decide), hOne]
  have r13eq43 : (reg s43 r13).val = qd + p := by
    rw [reg43, keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide),
      keep38 _ (by decide), keep37 _ (by decide), hr13]
  have r14eq43 : (reg s43 r14).val = pos := by
    rw [reg43, keep42 _ (by decide), r14eq41]
  obtain ⟨s44, st43, pc44, r12_44, keep44, d44⟩ :=
    step16_add code input pc43 (at_scatter subCode h32 (i := 43) (by decide)) (hPcLt 44 (by decide))
  have r12v44 : (reg s44 r12).val = 2 * n := by rw [r12_44, add_no_wrap] <;> rw [hNeq43] <;> omega
  obtain ⟨s45, st44, pc45, r12_45, keep45, d45⟩ :=
    step16_add code input pc44 (at_scatter subCode h32 (i := 44) (by decide)) (hPcLt 45 (by decide))
  have r12v45 : (reg s45 r12).val = 3 * n := by
    rw [r12_45, add_no_wrap] <;> rw [r12v44, keep44 _ (by decide), hNeq43] <;> omega
  obtain ⟨s46, st45, pc46, r12_46, keep46, d46⟩ :=
    step16_add code input pc45 (at_scatter subCode h32 (i := 45) (by decide)) (hPcLt 46 (by decide))
  have r12v46 : (reg s46 r12).val = 3 * n + m := by
    rw [r12_46, add_no_wrap] <;> rw [r12v45, keep45 _ (by decide), keep44 _ (by decide), hMeq43] <;> omega
  obtain ⟨s47, st46, pc47, r12_47, keep47, d47⟩ :=
    step16_add code input pc46 (at_scatter subCode h32 (i := 46) (by decide)) (hPcLt 47 (by decide))
  have r12v47 : (reg s47 r12).val = 3 * n + 2 * m := by
    rw [r12_47, add_no_wrap]
    · rw [r12v46, keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), hMeq43]; omega
    · rw [r12v46, keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), hMeq43]; omega
  obtain ⟨s48, st47, pc48, r12_48, keep48, d48⟩ :=
    step16_add code input pc47 (at_scatter subCode h32 (i := 47) (by decide)) (hPcLt 48 (by decide))
  have r12v48 : (reg s48 r12).val = emitBase + 3 * n + 2 * m := by
    rw [r12_48, add_no_wrap]
    · rw [keep47 _ (by decide), keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), hEeq43, r12v47]; omega
    · rw [keep47 _ (by decide), keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), hEeq43, r12v47]; omega
  obtain ⟨s49, st48, pc49, r12_49, keep49, d49⟩ :=
    step16_add code input pc48 (at_scatter subCode h32 (i := 48) (by decide)) (hPcLt 49 (by decide))
  have r12v49 : (reg s49 r12).val = emitBase + 3 * n + 2 * m + 1 := by
    rw [r12_49, add_no_wrap]
    · rw [r12v48, keep48 _ (by decide), keep47 _ (by decide), keep46 _ (by decide),
        keep45 _ (by decide), keep44 _ (by decide), h1eq43]
    · rw [r12v48, keep48 _ (by decide), keep47 _ (by decide), keep46 _ (by decide),
        keep45 _ (by decide), keep44 _ (by decide), h1eq43]; omega
  obtain ⟨s50, st49, pc50, r12_50, keep50, d50⟩ :=
    step16_add code input pc49 (at_scatter subCode h32 (i := 49) (by decide)) (hPcLt 50 (by decide))
  have r12v50 : (reg s50 r12).val = emitBase + 3 * n + 2 * m + 1 + (qd + p) := by
    rw [r12_50, add_no_wrap]
    · rw [r12v49, keep49 _ (by decide), keep48 _ (by decide), keep47 _ (by decide),
        keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), r13eq43]
    · rw [r12v49, keep49 _ (by decide), keep48 _ (by decide), keep47 _ (by decide),
        keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), r13eq43]; omega
  have hSteps : Steps code input 14 s36 s50 :=
    Steps.cons st36 (Steps.cons st37 (Steps.cons st38 (Steps.cons st39 (Steps.cons st40
      (Steps.cons st41 (Steps.cons st42 (Steps.cons st43 (Steps.cons st44 (Steps.cons st45
        (Steps.cons st46 (Steps.cons st47 (Steps.cons st48 (Steps.cons st49 (Steps.zero s50))))))))))))))
  refine ⟨s50, hSteps, pc50,
    by rw [d50, d49, d48, d47, d46, d45, d44, d43, Array.size_set, hData42, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, r12v50, ?_, ?_, ?_⟩
  · have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep50 _ h12, keep49 _ h12, keep48 _ h12, keep47 _ h12, keep46 _ h12, keep45 _ h12,
      keep44 _ h12, reg43, keep42 _ h15, keep41 _ h15, keep40 _ h15, keep39 _ h15,
      keep38 _ h12, keep37 _ h15]
  · rw [keep50 _ (by decide), keep49 _ (by decide), keep48 _ (by decide), keep47 _ (by decide),
      keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), r13eq43]
  · rw [keep50 _ (by decide), keep49 _ (by decide), keep48 _ (by decide), keep47 _ (by decide),
      keep46 _ (by decide), keep45 _ (by decide), keep44 _ (by decide), r14eq43]
  · intro k; rw [d50, d49, d48, d47, d46, d45, d44, d43]
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · rw [mem_set_same s42.data (r15v42.trans hk.symm) hBnd42, Option.map_some, r11eq42]
    · rw [mem_set_ne s42.data hBnd42 (fun e => hne (e.trans r15v42)), hData42]

private theorem scatterBodyD_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed tailE pos qd p : Nat}
    (htail : tailE < Q) (hp : qd + p < m) (hPos : pos < m)
    (hQLe : Q ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s50 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s50.pc = offScatter + 50) (hDataSz : s50.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s50)
    (hr12 : (reg s50 r12).val = emitBase + 3 * n + 2 * m + 1 + (qd + p))
    (hr13 : (reg s50 r13).val = qd + p) (hr14 : (reg s50 r14).val = pos)
    (hTail : (s50.data[emitBase + 3 * n + 2 * m + 1 + (qd + p)]?).map Fin.val = some tailE)
    (hStPtr : (s50.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hEntPtr : (s50.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m)) :
    ∃ s60, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 10 s50 s60 ∧
      s60.pc = offScatter + 4 ∧ s60.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s60 ∧
      (reg s60 r13).val = qd + (p + 1) ∧
      (∀ k, (k = loopSortEntryBase loopBase n m + pos → (s60.data[k]?).map Fin.val = some tailE) ∧
        (k ≠ loopSortEntryBase loopBase n m + pos → s60.data[k]? = s50.data[k]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 60 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hOne : (reg s50 rOne).val = 1 := hRegs.entry.consts.one
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hEntBnd : loopSortEntryBase loopBase n m + m ≤ workCap := by
    unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
      rawInputCap rawWorkCap loopWorkWords at *; omega
  have hTailLt : tailE < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hEmitLt : qd + p + 1 < 2 ^ bits := by unfold emitterWorkWords at hEmitFit; omega
  have hMemTail : s50.data[(reg s50 r12).val]? = some ⟨tailE, hTailLt⟩ := by
    rw [hr12]; exact mem_word_of_map hTail hTailLt
  obtain ⟨s51, st50, pc51, r11_51, keep51, d51⟩ :=
    step16_loadData code input hpc (at_scatter subCode h32 (i := 50) (by decide)) hMemTail (hPcLt 51 (by decide))
  obtain ⟨s52, st51, pc52, r15_52, keep52, d52⟩ :=
    step16_imm code input pc51 (at_scatter subCode h32 (i := 51) (by decide)) (hPcLt 52 (by decide))
  have hMemSt : s52.data[(reg s52 r15).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d52, d51, show (reg s52 r15).val = statePtrAddr by rw [r15_52]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s53, st52, pc53, r12_53, keep53, d53⟩ :=
    step16_loadData code input pc52 (at_scatter subCode h32 (i := 52) (by decide)) hMemSt (hPcLt 53 (by decide))
  obtain ⟨s54, st53, pc54, r15_54, keep54, d54⟩ :=
    step16_imm code input pc53 (at_scatter subCode h32 (i := 53) (by decide)) (hPcLt 54 (by decide))
  obtain ⟨s55, st54, pc55, r12_55, keep55, d55⟩ :=
    step16_add code input pc54 (at_scatter subCode h32 (i := 54) (by decide)) (hPcLt 55 (by decide))
  have hAddr55 : (reg s55 r12).val = loopSubStateBase loopBase n m + 13 := by
    rw [r12_55, add_no_wrap]
    · rw [keep54 _ (by decide), r12_53, r15_54]; rfl
    · rw [keep54 _ (by decide), r12_53, r15_54]; dsimp only; change _ + 13 < 2 ^ bits; omega
  have hMemEnt : s55.data[(reg s55 r12).val]? = some ⟨loopSortEntryBase loopBase n m, by omega⟩ := by
    rw [hAddr55, d55, d54, d53, d52, d51]; exact mem_word_of_map hEntPtr _
  obtain ⟨s56, st55, pc56, r12_56, keep56, d56⟩ :=
    step16_loadData code input pc55 (at_scatter subCode h32 (i := 55) (by decide)) hMemEnt (hPcLt 56 (by decide))
  obtain ⟨s57, st56, pc57, r12_57, keep57, d57⟩ :=
    step16_add code input pc56 (at_scatter subCode h32 (i := 56) (by decide)) (hPcLt 57 (by decide))
  have r14eq56 : (reg s56 r14).val = pos := by
    rw [keep56 _ (by decide), keep55 _ (by decide), keep54 _ (by decide), keep53 _ (by decide),
      keep52 _ (by decide), keep51 _ (by decide), hr14]
  have r12v57 : (reg s57 r12).val = loopSortEntryBase loopBase n m + pos := by
    rw [r12_57, add_no_wrap] <;> rw [r12_56, r14eq56] <;> dsimp only <;> omega
  have r11eq57 : (reg s57 r11).val = tailE := by
    rw [keep57 _ (by decide), keep56 _ (by decide), keep55 _ (by decide), keep54 _ (by decide),
      keep53 _ (by decide), keep52 _ (by decide), r11_51]
  have hData57 : s57.data = s50.data := by rw [d57, d56, d55, d54, d53, d52, d51]
  have hBnd57 : (reg s57 r12).val < s57.data.size := by rw [r12v57, hData57, hDataSz]; omega
  obtain ⟨s58, st57, pc58, regs58, d58⟩ :=
    step16_storeData code input pc57 (at_scatter subCode h32 (i := 57) (by decide)) (hPcLt 58 (by decide)) hBnd57
  have reg58 : ∀ r : Fin 16, reg s58 r = reg s57 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs58 r
  obtain ⟨s59, st58, pc59, r13_59, keep59, d59⟩ :=
    step16_add code input pc58 (at_scatter subCode h32 (i := 58) (by decide)) (hPcLt 59 (by decide))
  have r13eq58 : (reg s58 r13).val = qd + p := by
    rw [reg58, keep57 _ (by decide), keep56 _ (by decide), keep55 _ (by decide), keep54 _ (by decide),
      keep53 _ (by decide), keep52 _ (by decide), keep51 _ (by decide), hr13]
  have h1eq58 : (reg s58 rOne).val = 1 := by
    rw [reg58, keep57 _ (by decide), keep56 _ (by decide), keep55 _ (by decide), keep54 _ (by decide),
      keep53 _ (by decide), keep52 _ (by decide), keep51 _ (by decide), hOne]
  have r13v59 : (reg s59 r13).val = qd + (p + 1) := by
    rw [r13_59, add_no_wrap]
    · rw [r13eq58, h1eq58]; omega
    · rw [r13eq58, h1eq58]; omega
  have st59 := step16_goto code input pc59 (at_scatter subCode h32 (i := 59) (by decide)) (hPcLt 4 (by decide))
  let s60 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s59.regs, data := s59.data, pc := offScatter + 4,
      regs_size := s59.regs_size, data_size := s59.data_size }
  have hSteps : Steps code input 10 s50 s60 :=
    Steps.cons st50 (Steps.cons st51 (Steps.cons st52 (Steps.cons st53 (Steps.cons st54
      (Steps.cons st55 (Steps.cons st56 (Steps.cons st57 (Steps.cons st58 (Steps.cons st59 (Steps.zero s60))))))))))
  refine ⟨s60, hSteps, rfl, by change s59.data.size = _; rw [d59, d58, Array.size_set, hData57, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    change reg s59 r = reg s50 r
    rw [keep59 _ h13, reg58, keep57 _ h12, keep56 _ h12, keep55 _ h12, keep54 _ h15,
      keep53 _ h12, keep52 _ h15, keep51 _ h11]
  · change (reg s59 r13).val = _; exact r13v59
  · intro k
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · change (s59.data[k]?).map Fin.val = some tailE
      rw [d59, d58, mem_set_same s57.data (r12v57.trans hk.symm) hBnd57, Option.map_some, r11eq57]
    · change s59.data[k]? = s50.data[k]?
      rw [d59, d58, mem_set_ne s57.data hBnd57 (fun e => hne (e.trans r12v57)), hData57]

private theorem scatterSort_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offScatter) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hMdAt : (s₀.data[loopBase + 1]?).map Fin.val = some (S.emittedArcs ⟨d, hQ ▸ hd⟩).length)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hCurPtr : (s₀.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m))
    (hEntPtr : (s₀.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m))
    (hCursors : ∀ u < 1 + (S.childSlice ⟨d, hQ ▸ hd⟩).length,
      (s₀.data[loopCursorBase loopBase n m + u]?).map Fin.val = some (bucketStart (S.emittedArcs ⟨d, hQ ▸ hd⟩) u))
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcsOrig : ∀ (p : Nat) (hp : p < (S.emittedArcs ⟨d, hQ ▸ hd⟩).length),
      let ea := (S.emittedArcs ⟨d, hQ ▸ hd⟩)[p]'hp
      (s₀.data[emitBase + 3 * n + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBase + 3 * n + m + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.tailEntry) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let n_d := 1 + (S.childSlice dFin).length
    let m_d := (S.emittedArcs dFin).length
    let sorted := countingSortedArcs n_d (S.emittedArcs dFin)
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 56 * m_d + 10 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offWB ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t ∧
      (∀ (pos : Nat) (hp : pos < m_d),
        let ea := sorted[pos]'(by rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds dFin hx).2.1)]; exact hp)
        (t.data[loopBase + 3 + pos]?).map Fin.val = some ea.srcLocal ∧
        (t.data[loopBase + 3 + m_d + pos]?).map Fin.val = some ea.headLocal ∧
        (t.data[loopSortEntryBase loopBase n m + pos]?).map Fin.val = some ea.tailEntry) ∧
      (∀ k,
        (k < loopBase + 3 ∨ loopBase + 3 + 2 * m_d ≤ k) →
        (k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ k) →
        (k < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ k) →
        t.data[k]? = s₀.data[k]?) := by
  intro dFin n_d m_d sorted
  let arcs := S.emittedArcs dFin
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 61 → offScatter + c < code.size := by
    intro c hc; rw [hSz]; unfold offScatter; omega
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hNdLe : n_d ≤ n := Nat.le_trans (by rw [hQ]; exact ownerVertexCount_le_Q S dFin) hQL
  have hSucc : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S dFin.isLt
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have hMdLe : m_d ≤ m := by omega
  have hArcsBnd : ∀ ea ∈ arcs, ea.srcLocal < n_d := fun ea hea => (S.emittedArc_bounds dFin hea).2.1
  have hAllBnd : bucketStart arcs n_d = m_d := sum_bucketDeg_all arcs hArcsBnd
  have hStDisj : statePtrAddr < loopBase + 3 ∧
      statePtrAddr < loopCursorBase loopBase n m ∧ statePtrAddr < loopSortEntryBase loopBase n m := by
    unfold statePtrAddr loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
      loopSubWorkBase rawInputCap rawWorkCap; omega
  have hMetaDisj : ∀ off, loopSubStateBase loopBase n m ≤ off → off < loopSubStateBase loopBase n m + 16 →
      (loopBase + 3 + 2 * m_d ≤ off) ∧ (off < loopCursorBase loopBase n m) ∧ (off < loopSortEntryBase loopBase n m) := by
    intro off ho1 ho2
    unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
      loopSubWorkBase rawInputCap rawWorkCap at *; omega
  have hMdDisj : loopBase + 1 < loopBase + 3 ∧ loopBase + 1 < loopCursorBase loopBase n m ∧
      loopBase + 1 < loopSortEntryBase loopBase n m := by
    unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
      loopSubWorkBase rawInputCap rawWorkCap; omega
  have hQDisj : ∀ j ≤ Q,
      (emitBase + 2 * n + j < loopBase + 3 ∨ loopBase + 3 + 2 * m_d ≤ emitBase + 2 * n + j) ∧
      (emitBase + 2 * n + j < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ emitBase + 2 * n + j) ∧
      (emitBase + 2 * n + j < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ emitBase + 2 * n + j) := by
    intro j hj
    unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
    unfold loopWorkWords emitterWorkWords at hDisj
    omega
  obtain ⟨s4, hStPre, pc4, hData4, hRg4, hr13_4⟩ :=
    scatterPre_steps subCode h32 input S hn hm hQ hd hEmitFit hBits hpc hRegs hQStarts
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun p s =>
    p ≤ m_d ∧ s.pc = offScatter + 4 ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (reg s r13).val = qStartFn S d + p ∧
    (∀ u < n_d, (s.data[loopCursorBase loopBase n m + u]?).map Fin.val =
      some (bucketStart arcs u + bucketDeg (arcs.take p) u)) ∧
    (∀ u : Fin n_d, ∀ j (hj : j < bucketDeg (arcs.take p) u.val),
      let ea := ((arcs.take p).filter (fun x => x.srcLocal == u.val))[j]'hj
      let pos := bucketStart arcs u.val + j
      (s.data[loopBase + 3 + pos]?).map Fin.val = some ea.srcLocal ∧
      (s.data[loopBase + 3 + m_d + pos]?).map Fin.val = some ea.headLocal ∧
      (s.data[loopSortEntryBase loopBase n m + pos]?).map Fin.val = some ea.tailEntry) ∧
    (∀ k,
      (k < loopBase + 3 ∨ loopBase + 3 + 2 * m_d ≤ k) →
      (k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ k) →
      (k < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ k) →
      s.data[k]? = s₀.data[k]?)
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offWB ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (∀ (pos : Nat) (hp : pos < m_d),
      let ea := sorted[pos]'(by rw [countingSortedArcs_length _ hArcsBnd]; exact hp)
      (s.data[loopBase + 3 + pos]?).map Fin.val = some ea.srcLocal ∧
      (s.data[loopBase + 3 + m_d + pos]?).map Fin.val = some ea.headLocal ∧
      (s.data[loopSortEntryBase loopBase n m + pos]?).map Fin.val = some ea.tailEntry) ∧
    (∀ k,
      (k < loopBase + 3 ∨ loopBase + 3 + 2 * m_d ≤ k) →
      (k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ k) →
      (k < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ k) →
      s.data[k]? = s₀.data[k]?)
  have hLoop := loop_steps_budget inv (fun p => m_d - p) (fun p => 6 + 56 * (m_d - p)) post
    (fun p s ⟨hpLe, hpcS, hSzS, hRgS, hr13S, hCurS, hScatS, hOutS⟩ => by
      have hQS_S : ∀ j ≤ Q, (s.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j) := fun j hj => by
        have hD := hQDisj j hj
        rw [hOutS _ hD.1 hD.2.1 hD.2.2]; exact hQStarts j hj
      obtain ⟨s9, hStHdr, pc9, hData9, hRg9, hr13_9, hr14_9⟩ :=
        scatterHdr_steps subCode h32 input S hn hm hQ hd hEmitFit hBits hpcS hRgS hQS_S
      by_cases hpEq : p = m_d
      · subst hpEq
        have hGe : (reg s9 r14).val ≤ (reg s9 r13).val := by rw [hr13_9, hr13S, hr14_9, hSucc]; exact Nat.le_refl _
        have stBr := step16_branchLt_false code input pc9 (at_scatter subCode h32 (i := 9) (by decide))
          (hPcLt 60 (by decide)) hGe
        refine Or.inl ⟨_, 6, by omega, hStHdr.append (steps_one stBr), ?_, by rw [hData9, hSzS],
          loopIterRegs_of_keep hRg9 (fun _ _ => rfl), ?_, fun k h1 h2 h3 => by rw [hData9]; exact hOutS k h1 h2 h3⟩
        · change offScatter + 60 = offWB; unfold offScatter offWB; omega
        · intro pos hp
          obtain ⟨u, j, hj, hPosEq⟩ := bucket_decompose arcs hArcsBnd hp
          have hTakeAll : arcs.take m_d = arcs := List.take_of_length_le (Nat.le_refl _)
          have hjTake : j < bucketDeg (arcs.take m_d) u.val := by rwa [hTakeAll]
          have hSc := hScatS u j hjTake
          obtain ⟨_, hGet⟩ := countingSortedArcs_bucket_getElem arcs u j hj
          have hGetPos : sorted[pos]'(by rw [countingSortedArcs_length _ hArcsBnd]; exact hp) =
              (arcs.filter (fun x => x.srcLocal == u.val))[j]'hj := by
            simpa only [← hPosEq] using hGet
          have hElEq : ((arcs.take m_d).filter (fun x => x.srcLocal == u.val))[j]'hjTake =
              (arcs.filter (fun x => x.srcLocal == u.val))[j]'hj :=
            list_getElem_congr (by rw [hTakeAll]) hjTake hj
          have hSc' := hSc
          dsimp only at hSc'
          rw [← hPosEq, hElEq, ← hGetPos] at hSc'
          rw [hData9]
          exact hSc'
      · have hpLt : p < m_d := Nat.lt_of_le_of_ne hpLe hpEq
        have hLtR : (reg s9 r13).val < (reg s9 r14).val := by
          rw [hr13_9, hr13S, hr14_9, hSucc]; exact Nat.add_lt_add_left hpLt _
        have st9 := step16_branchLt_true code input pc9 (at_scatter subCode h32 (i := 9) (by decide))
          (hPcLt 10 (by decide)) hLtR
        let s10 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s9.regs, data := s9.data, pc := offScatter + 10,
            regs_size := s9.regs_size, data_size := s9.data_size }
        have hSt10 : Steps code input 6 s s10 := hStHdr.append (steps_one st9)
        have hD10 : s10.data = s.data := hData9
        have hSz10 : s10.data.size = workCap := by rw [hD10, hSzS]
        have hRg10 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s10 :=
          loopIterRegs_of_keep hRg9 (fun _ _ => rfl)
        have hr13_10 : (reg s10 r13).val = qStartFn S d + p := hr13_9.trans hr13S
        let ea := arcs[p]'hpLt
        have hEaBnd := S.emittedArc_bounds dFin (List.getElem_mem hpLt)
        have hSrcLtN : ea.srcLocal < n := Nat.lt_of_lt_of_le hEaBnd.2.1 hNdLe
        have hHdLtN : ea.headLocal < n := Nat.lt_of_lt_of_le hEaBnd.2.2.1 hNdLe
        have hArcPos := hArcsOrig p hpLt
        have hDisjS := emit_arc_disjoint_scatter (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
          (idx := 3 * n + 1 + (qStartFn S d + p)) (by omega) hMdLe hDisj
        have hDisjC := emit_arc_disjoint_cursor (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
          (idx := 3 * n + 1 + (qStartFn S d + p)) (by omega) hNdLe hDisj
        have hDisjE := emit_arc_disjoint_entry (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
          (idx := 3 * n + 1 + (qStartFn S d + p)) (by omega) hMdLe hDisj
        have hSrc10 : (s10.data[emitBase + 3 * n + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.srcLocal := by
          have hO := hOutS (emitBase + 3 * n + 1 + (qStartFn S d + p))
            (by simpa only [Nat.add_assoc] using hDisjS)
            (by simpa only [Nat.add_assoc] using hDisjC)
            (by simpa only [Nat.add_assoc] using hDisjE)
          rw [hD10, hO]; exact hArcPos.1
        have hStPtr10 : (s10.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
          rw [hD10, hOutS _ (Or.inl hStDisj.1) (Or.inl hStDisj.2.1) (Or.inl hStDisj.2.2)]; exact hStPtr
        have hCurPtr10 : (s10.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m) := by
          have hmD := hMetaDisj (loopSubStateBase loopBase n m + 12) (by omega) (by omega)
          rw [hD10, hOutS _ (Or.inr hmD.1) (Or.inl hmD.2.1) (Or.inl hmD.2.2)]; exact hCurPtr
        let oldDeg := bucketDeg (arcs.take p) ea.srcLocal
        let pos := bucketStart arcs ea.srcLocal + oldDeg
        have hDegLt : oldDeg < bucketDeg arcs ea.srcLocal := by
          have hSub : bucketDeg (arcs.take (p + 1)) ea.srcLocal ≤ bucketDeg arcs ea.srcLocal :=
            bucketDeg_take_le arcs (p + 1) ea.srcLocal
          have hTake : arcs.take (p + 1) = arcs.take p ++ [ea] := List.take_succ_eq_append_getElem hpLt
          have hLen1 : ([ea].filter (fun x => x.srcLocal == ea.srcLocal)).length = 1 := by simp
          have hEq : bucketDeg (arcs.take (p + 1)) ea.srcLocal = oldDeg + 1 := by
            change bucketDeg (arcs.take (p + 1)) ea.srcLocal = bucketDeg (arcs.take p) ea.srcLocal + 1
            unfold bucketDeg
            rw [hTake, List.filter_append, List.length_append, hLen1]
          omega
        have hPosLtMd : pos < m_d := by
          have hBndU : bucketStart arcs ea.srcLocal + bucketDeg arcs ea.srcLocal ≤ m_d := by
            rw [← bucketStart_succ, ← hAllBnd]
            exact bucketStart_mono_le arcs hEaBnd.2.1
          omega
        have hPosLtM : pos < m := Nat.lt_of_lt_of_le hPosLtMd hMdLe
        have hCurU10 : (s10.data[loopCursorBase loopBase n m + ea.srcLocal]?).map Fin.val = some pos := by
          rw [hD10]; exact hCurS ea.srcLocal hEaBnd.2.1
        obtain ⟨s25, hStA, pc25, sz25, hRg25, hr11_25, hr13_25, hr14_25, hMem25⟩ :=
          scatterBodyA_steps subCode h32 input hSrcLtN (by omega) hPosLtM hFit hEmitFit hBits rfl hSz10
            hRg10 hr13_10 hSrc10 hStPtr10 hCurPtr10 hCurU10
        have hDisjHS := emit_arc_disjoint_scatter (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
          (idx := 3 * n + m + 1 + (qStartFn S d + p)) (by omega) hMdLe hDisj
        have hDisjHC := emit_arc_disjoint_cursor (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
          (idx := 3 * n + m + 1 + (qStartFn S d + p)) (by omega) hNdLe hDisj
        have hDisjHE := emit_arc_disjoint_entry (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
          (idx := 3 * n + m + 1 + (qStartFn S d + p)) (by omega) hMdLe hDisj
        have hHead25 : (s25.data[emitBase + 3 * n + m + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.headLocal := by
          have hNeC : emitBase + 3 * n + m + 1 + (qStartFn S d + p) ≠ loopCursorBase loopBase n m + ea.srcLocal := by
            rcases hDisjHC with hl | hr
            · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by simpa only [Nat.add_assoc] using hl) (Nat.le_add_right _ _))
            · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hEaBnd.2.1 _) (by simpa only [Nat.add_assoc] using hr))
          have hO := hOutS (emitBase + 3 * n + m + 1 + (qStartFn S d + p))
            (by simpa only [Nat.add_assoc] using hDisjHS)
            (by simpa only [Nat.add_assoc] using hDisjHC)
            (by simpa only [Nat.add_assoc] using hDisjHE)
          rw [(hMem25 _).2 hNeC, hD10, hO]; exact hArcPos.2.1
        obtain ⟨s36, hStB, pc36, sz36, hRg36, hr11_36, hr13_36, hr14_36, hMem36⟩ :=
          scatterBodyB_steps subCode h32 input hHdLtN (by omega) hPosLtM hFit hEmitFit hDisj hBits
            pc25 sz25 hRg25 hr11_25 hr13_25 hr14_25 hHead25
        have hMd36 : (s36.data[loopBase + 1]?).map Fin.val = some m_d := by
          have h1 : loopBase + 1 ≠ loopBase + 3 + pos := by omega
          have h2 : loopBase + 1 ≠ loopCursorBase loopBase n m + ea.srcLocal := by omega
          rw [(hMem36 _).2 h1, (hMem25 _).2 h2, hD10, hOutS _ (Or.inl hMdDisj.1) (Or.inl hMdDisj.2.1) (Or.inl hMdDisj.2.2)]
          exact hMdAt
        obtain ⟨s50, hStC, pc50, sz50, hRg50, hr12_50, hr13_50, hr14_50, hMem50⟩ :=
          scatterBodyC_steps subCode h32 input hMdLe hPosLtMd (by omega) hFit hEmitFit hBits
            pc36 sz36 hRg36 hr11_36 hr13_36 hr14_36 hMd36
        have hTail50 : (s50.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.tailEntry := by
          have hDisjTS := emit_arc_disjoint_scatter (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
            (idx := 3 * n + 2 * m + 1 + (qStartFn S d + p)) (by omega) hMdLe hDisj
          have hDisjTC := emit_arc_disjoint_cursor (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
            (idx := 3 * n + 2 * m + 1 + (qStartFn S d + p)) (by omega) hNdLe hDisj
          have hDisjTE := emit_arc_disjoint_entry (n := n) (m := m) (emitBase := emitBase) (loopBase := loopBase)
            (idx := 3 * n + 2 * m + 1 + (qStartFn S d + p)) (by omega) hMdLe hDisj
          have hNeH : emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p) ≠ loopBase + 3 + m_d + pos := by
            rcases hDisjTS with hl | hr <;> omega
          have hNeS : emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p) ≠ loopBase + 3 + pos := by
            rcases hDisjTS with hl | hr <;> omega
          have hNeC : emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p) ≠ loopCursorBase loopBase n m + ea.srcLocal := by
            rcases hDisjTC with hl | hr
            · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (by simpa only [Nat.add_assoc] using hl) (Nat.le_add_right _ _))
            · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hEaBnd.2.1 _) (by simpa only [Nat.add_assoc] using hr))
          have hO := hOutS (emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p))
            (by simpa only [Nat.add_assoc] using hDisjTS)
            (by simpa only [Nat.add_assoc] using hDisjTC)
            (by simpa only [Nat.add_assoc] using hDisjTE)
          rw [(hMem50 _).2 hNeH, (hMem36 _).2 hNeS, (hMem25 _).2 hNeC, hD10, hO]
          exact hArcPos.2.2
        have hStPtr50 : (s50.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
          have h1 : statePtrAddr ≠ loopBase + 3 + m_d + pos := by omega
          have h2 : statePtrAddr ≠ loopBase + 3 + pos := by omega
          have h3 : statePtrAddr ≠ loopCursorBase loopBase n m + ea.srcLocal := by omega
          rw [(hMem50 _).2 h1, (hMem36 _).2 h2, (hMem25 _).2 h3, hStPtr10]
        have hEntPtr50 : (s50.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m) := by
          have hmD := hMetaDisj (loopSubStateBase loopBase n m + 13) (by omega) (by omega)
          have h1 : loopSubStateBase loopBase n m + 13 ≠ loopBase + 3 + m_d + pos := by omega
          have h2 : loopSubStateBase loopBase n m + 13 ≠ loopBase + 3 + pos := by omega
          have h3 : loopSubStateBase loopBase n m + 13 ≠ loopCursorBase loopBase n m + ea.srcLocal := by omega
          rw [(hMem50 _).2 h1, (hMem36 _).2 h2, (hMem25 _).2 h3, hD10,
            hOutS _ (Or.inr hmD.1) (Or.inl hmD.2.1) (Or.inl hmD.2.2)]
          exact hEntPtr
        obtain ⟨s60, hStD, pc60, sz60, hRg60, hr13_60, hMem60⟩ :=
          scatterBodyD_steps subCode h32 input (hQ.symm ▸ hEaBnd.2.2.2) (by omega) hPosLtM hQL hFit hEmitFit hBits
            pc50 sz50 hRg50 hr12_50 hr13_50 hr14_50 hTail50 hStPtr50 hEntPtr50
        have hStIter : Steps code input 56 s s60 :=
          ((hSt10.append hStA).append hStB).append (hStC.append hStD)
        have hTakeSucc : arcs.take (p + 1) = arcs.take p ++ [ea] := List.take_succ_eq_append_getElem hpLt
        refine Or.inr ⟨p + 1, s60, 56, by omega, by omega, hStIter,
          hpLt, pc60, sz60, hRg60, hr13_60, ?_, ?_, ?_⟩
        · intro u hu
          have hNeE : loopCursorBase loopBase n m + u ≠ loopSortEntryBase loopBase n m + pos := by
            unfold loopSortEntryBase loopCursorBase at *; omega
          have hNeH : loopCursorBase loopBase n m + u ≠ loopBase + 3 + m_d + pos := by
            unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
              rawInputCap rawWorkCap at *; omega
          have hNeS : loopCursorBase loopBase n m + u ≠ loopBase + 3 + pos := by
            unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
              rawInputCap rawWorkCap at *; omega
          rw [(hMem60 _).2 hNeE, (hMem50 _).2 hNeH, (hMem36 _).2 hNeS]
          by_cases heq : u = ea.srcLocal
          · subst heq
            have hLen1 : ([ea].filter (fun x => x.srcLocal == ea.srcLocal)).length = 1 := by simp
            have hEqD : bucketDeg (arcs.take (p + 1)) ea.srcLocal = oldDeg + 1 := by
              change bucketDeg (arcs.take (p + 1)) ea.srcLocal = bucketDeg (arcs.take p) ea.srcLocal + 1
              unfold bucketDeg
              rw [hTakeSucc, List.filter_append, List.length_append, hLen1]
            rw [(hMem25 _).1 rfl, hEqD]
            simp only [pos, oldDeg, Nat.add_assoc]
          · have hNeC : loopCursorBase loopBase n m + u ≠ loopCursorBase loopBase n m + ea.srcLocal := by omega
            have hbf : (ea.srcLocal == u) = false := beq_false_of_ne (fun e => heq e.symm)
            have hEqD : bucketDeg (arcs.take (p + 1)) u = bucketDeg (arcs.take p) u := by
              unfold bucketDeg
              rw [hTakeSucc, List.filter_append, List.length_append]
              simp [hbf]
            rw [(hMem25 _).2 hNeC, hD10, hEqD]
            exact hCurS u hu
        · intro u j hj
          have hsIdxLt : bucketStart arcs u.val + j < m_d := by
            have hLe := bucketDeg_take_le arcs (p + 1) u.val
            have hB1 : bucketStart arcs u.val + bucketDeg arcs u.val ≤ m_d := by
              rw [← bucketStart_succ, ← hAllBnd]; exact bucketStart_mono_le arcs u.isLt
            omega
          obtain ⟨hDisjCH, hDisjHS, hDisjCE, hDisjHE, hDisjEC, hDisjSC, hDisjHC, hDisjES, hDisjEH⟩ :=
            scatter_slot_disjoint hsIdxLt hPosLtMd hMdLe hSrcLtN
          by_cases hu : u.val = ea.srcLocal
          · have hjLe : j ≤ oldDeg := by
              have hLen1 : ([ea].filter (fun x => x.srcLocal == u.val)).length = 1 := by simp [hu]
              have hEq : bucketDeg (arcs.take (p + 1)) u.val = oldDeg + 1 := by
                change bucketDeg (arcs.take (p + 1)) u.val = bucketDeg (arcs.take p) ea.srcLocal + 1
                unfold bucketDeg
                rw [hTakeSucc, List.filter_append, List.length_append, hLen1, hu]
              omega
            by_cases hjEq : j = oldDeg
            · have hPosEq : bucketStart arcs u.val + j = pos := by rw [hu, hjEq]
              have hFilt : ((arcs.take (p + 1)).filter (fun x => x.srcLocal == u.val))[j]'hj = ea := by
                have hPrefLen : ((arcs.take p).filter (fun x => x.srcLocal == u.val)).length = oldDeg := by
                  change bucketDeg (arcs.take p) u.val = bucketDeg (arcs.take p) ea.srcLocal
                  rw [hu]
                simp only [hTakeSucc, List.filter_append, List.filter_cons, List.filter_nil,
                  show (ea.srcLocal == u.val) = true by simp [hu], ↓reduceIte]
                rw [List.getElem_append_right (by rw [hPrefLen]; omega)]
                simp [hPrefLen, hjEq]
              rw [hFilt]
              refine ⟨?_, ?_, ?_⟩
              · rw [(hMem60 _).2 hDisjCE, (hMem50 _).2 hDisjCH, (hMem36 _).1 (by rw [hPosEq])]
              · rw [(hMem60 _).2 hDisjHE, (hMem50 _).1 (by rw [hPosEq])]
              · rw [(hMem60 _).1 (by rw [hPosEq])]
            · have hjLt : j < oldDeg := by omega
              have hjOldU : j < bucketDeg (arcs.take p) u.val := by
                change j < bucketDeg (arcs.take p) u.val
                rw [hu]; exact hjLt
              have hPosNe : bucketStart arcs u.val + j ≠ pos := by rw [hu]; omega
              have hPrev := hScatS u j hjOldU
              have hFilt : ((arcs.take (p + 1)).filter (fun x => x.srcLocal == u.val))[j]'hj =
                  ((arcs.take p).filter (fun x => x.srcLocal == u.val))[j]'hjOldU := by
                simp only [hTakeSucc, List.filter_append]
                exact List.getElem_append_left hjOldU
              rw [hFilt]
              refine ⟨?_, ?_, ?_⟩
              · rw [(hMem60 _).2 hDisjCE, (hMem50 _).2 hDisjCH, (hMem36 _).2 (by omega),
                  (hMem25 _).2 hDisjSC, hD10]; exact hPrev.1
              · rw [(hMem60 _).2 hDisjHE, (hMem50 _).2 (by omega), (hMem36 _).2 hDisjHS,
                  (hMem25 _).2 hDisjHC, hD10]; exact hPrev.2.1
              · rw [(hMem60 _).2 (by omega), (hMem50 _).2 hDisjEH, (hMem36 _).2 hDisjES,
                  (hMem25 _).2 hDisjEC, hD10]; exact hPrev.2.2
          · have hbf : (ea.srcLocal == u.val) = false := beq_false_of_ne (fun e => hu e.symm)
            have hFiltList : (arcs.take (p + 1)).filter (fun x => x.srcLocal == u.val) =
                (arcs.take p).filter (fun x => x.srcLocal == u.val) := by
              rw [hTakeSucc, List.filter_append]
              simp [hbf]
            have hjOld : j < bucketDeg (arcs.take p) u.val := by
              simpa only [bucketDeg, hFiltList] using hj
            have hPosNe : bucketStart arcs u.val + j ≠ pos :=
              bucketStart_disjoint arcs hu (Nat.lt_of_lt_of_le hjOld (bucketDeg_take_le arcs p u.val)) hDegLt
            have hPrev := hScatS u j hjOld
            have hEaEq : ((arcs.take (p + 1)).filter (fun x => x.srcLocal == u.val))[j]'hj =
                ((arcs.take p).filter (fun x => x.srcLocal == u.val))[j]'hjOld :=
              list_getElem_congr hFiltList _ _
            rw [hEaEq]
            refine ⟨?_, ?_, ?_⟩
            · rw [(hMem60 _).2 hDisjCE, (hMem50 _).2 hDisjCH, (hMem36 _).2 (by omega),
                (hMem25 _).2 hDisjSC, hD10]; exact hPrev.1
            · rw [(hMem60 _).2 hDisjHE, (hMem50 _).2 (by omega), (hMem36 _).2 hDisjHS,
                (hMem25 _).2 hDisjHC, hD10]; exact hPrev.2.1
            · rw [(hMem60 _).2 (by omega), (hMem50 _).2 hDisjEH, (hMem36 _).2 hDisjES,
                (hMem25 _).2 hDisjEC, hD10]; exact hPrev.2.2
        · intro k h1 h2 h3
          have h1' : k ≠ loopBase + 3 + pos := by rcases h1 with hl | hr <;> omega
          have h2' : k ≠ loopBase + 3 + m_d + pos := by rcases h1 with hl | hr <;> omega
          have h3' : k ≠ loopCursorBase loopBase n m + ea.srcLocal := by
            rcases h2 with hl | hr
            · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hl (Nat.le_add_right _ _))
            · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hEaBnd.2.1 _) hr)
          have h4' : k ≠ loopSortEntryBase loopBase n m + pos := by rcases h3 with hl | hr <;> omega
          rw [(hMem60 k).2 h4', (hMem50 k).2 h2', (hMem36 k).2 h1', (hMem25 k).2 h3', hD10]
          exact hOutS k h1 h2 h3)
    m_d 0 s4 (by omega)
    ⟨Nat.zero_le _, pc4, by rw [hData4, hDataSz], hRg4, by simpa only [Nat.add_zero] using hr13_4,
      fun u hu => by rw [hData4]; simpa [bucketDeg] using hCursors u hu,
      fun u j hj => by simp [bucketDeg] at hj,
      fun k _ _ _ => by rw [hData4]⟩
  obtain ⟨_, t, kL, hkL, hStL, hPost⟩ := hLoop
  exact ⟨t, 4 + kL, by omega, hStPre.append hStL, hPost⟩

private theorem wbBodyA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed k srcVal m_d : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hkLt : k < m_d) (hm_d : m_d ≤ m) (hSrcLt : srcVal < n)
    (hSucc : qStartFn S (d + 1) = qStartFn S d + m_d)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s₄ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₄.pc = offWB + 4) (hDataSz : s₄.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₄)
    (hr13 : (reg s₄ r13).val = k) (hr14 : (reg s₄ r14).val = m_d)
    (hQAt : (s₄.data[emitBase + 2 * n + d]?).map Fin.val = some (qStartFn S d))
    (hSrcAt : (s₄.data[loopBase + 3 + k]?).map Fin.val = some srcVal) :
    ∃ s19, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 15 s₄ s19 ∧
      s19.pc = offWB + 19 ∧ s19.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s19 ∧
      (reg s19 r13).val = k ∧ (reg s19 r14).val = m_d ∧ (reg s19 r15).val = qStartFn S d + k ∧
      (∀ addr, (addr = emitBase + 3 * n + 1 + (qStartFn S d + k) → (s19.data[addr]?).map Fin.val = some srcVal) ∧
        (addr ≠ emitBase + 3 * n + 1 + (qStartFn S d + k) → s19.data[addr]? = s₄.data[addr]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 20 → offWB + c < code.size := by
    intro c hc; rw [hSz]; unfold offWB; omega
  have hOne : (reg s₄ rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s₄ rN).val = n := hRegs.entry.consts.nVal
  have hE : (reg s₄ r7).val = emitBase := hRegs.entry.emitBaseVal
  have hL : (reg s₄ r8).val = loopBase := hRegs.entry.loopBaseVal
  have hdVal : (reg s₄ r9).val = d := hRegs.dVal
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have hEmitBnd : emitBase + 3 * n + 1 + m ≤ workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have hLoopBnd : loopBase + 3 + m ≤ workCap := by
    unfold loopWorkWords at hFit; omega
  have h3NLt : 3 * n < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  -- 4..7: r15 := qStartFn S d
  obtain ⟨s5, st4, pc5, r12_5, keep5, d5⟩ :=
    step16_add code input hpc (at_wb subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have r12v5 : (reg s5 r12).val = 2 * n := by rw [r12_5, add_no_wrap] <;> rw [hN] <;> omega
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_wb subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = emitBase + 2 * n := by
    rw [r12_6, add_no_wrap] <;> rw [keep5 _ (by decide), hE, r12v5] <;> omega
  obtain ⟨s7, st6, pc7, r12_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_wb subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have r12v7 : (reg s7 r12).val = emitBase + 2 * n + d := by
    rw [r12_7, add_no_wrap] <;> rw [r12v6, keep6 _ (by decide), keep5 _ (by decide), hdVal] <;> omega
  have hMemQ : s7.data[(reg s7 r12).val]? = some ⟨qStartFn S d, by omega⟩ := by
    rw [r12v7, d7, d6, d5]; exact mem_word_of_map hQAt _
  obtain ⟨s8, st7, pc8, r15_8, keep8, d8⟩ :=
    step16_loadData code input pc7 (at_wb subCode h32 (i := 7) (by decide)) hMemQ (hPcLt 8 (by decide))
  -- 8: r15 := qStart + k
  have r13eq8 : (reg s8 r13).val = k := by
    rw [keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), hr13]
  obtain ⟨s9, st8, pc9, r15_9, keep9, d9⟩ :=
    step16_add code input pc8 (at_wb subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
  have r15v9 : (reg s9 r15).val = qStartFn S d + k := by
    rw [r15_9, add_no_wrap] <;> rw [r15_8, r13eq8] <;> dsimp only <;> omega
  -- 9..12: r11 := loopBase[3 + k]
  obtain ⟨s10, st9, pc10, r11_10, keep10, d10⟩ :=
    step16_imm code input pc9 (at_wb subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  obtain ⟨s11, st10, pc11, r11_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_wb subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have hLeq10 : (reg s10 r8).val = loopBase := by
    rw [keep10 _ (by decide), keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide),
      keep6 _ (by decide), keep5 _ (by decide), hL]
  have r11v11 : (reg s11 r11).val = loopBase + 3 := by
    rw [r11_11, add_no_wrap]
    · rw [hLeq10, r11_10]; rfl
    · rw [hLeq10, r11_10]; change loopBase + 3 < 2 ^ bits; omega
  obtain ⟨s12, st11, pc12, r11_12, keep12, d12⟩ :=
    step16_add code input pc11 (at_wb subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
  have r13eq11 : (reg s11 r13).val = k := by
    rw [keep11 _ (by decide), keep10 _ (by decide), keep9 _ (by decide), r13eq8]
  have r11v12 : (reg s12 r11).val = loopBase + 3 + k := by
    rw [r11_12, add_no_wrap] <;> rw [r11v11, r13eq11] <;> omega
  have hData12 : s12.data = s₄.data := by rw [d12, d11, d10, d9, d8, d7, d6, d5]
  have hMemSrc : s12.data[(reg s12 r11).val]? = some ⟨srcVal, by omega⟩ := by
    rw [r11v12, hData12]; exact mem_word_of_map hSrcAt _
  obtain ⟨s13, st12, pc13, r11_13, keep13, d13⟩ :=
    step16_loadData code input pc12 (at_wb subCode h32 (i := 12) (by decide)) hMemSrc (hPcLt 13 (by decide))
  -- 13..18: store srcVal at emitBase + 3*n + 1 + (qStart + k)
  have hNeq13 : (reg s13 rN).val = n := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), hN]
  have hEeq13 : (reg s13 r7).val = emitBase := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), hE]
  have h1eq13 : (reg s13 rOne).val = 1 := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), hOne]
  have r15eq13 : (reg s13 r15).val = qStartFn S d + k := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide), r15v9]
  obtain ⟨s14, st13, pc14, r12_14, keep14, d14⟩ :=
    step16_add code input pc13 (at_wb subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have r12v14 : (reg s14 r12).val = 2 * n := by rw [r12_14, add_no_wrap] <;> rw [hNeq13] <;> omega
  obtain ⟨s15, st14, pc15, r12_15, keep15, d15⟩ :=
    step16_add code input pc14 (at_wb subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have r12v15 : (reg s15 r12).val = 3 * n := by
    rw [r12_15, add_no_wrap] <;> rw [r12v14, keep14 _ (by decide), hNeq13] <;> omega
  obtain ⟨s16, st15, pc16, r12_16, keep16, d16⟩ :=
    step16_add code input pc15 (at_wb subCode h32 (i := 15) (by decide)) (hPcLt 16 (by decide))
  have r12v16 : (reg s16 r12).val = emitBase + 3 * n := by
    rw [r12_16, add_no_wrap]
    · rw [keep15 _ (by decide), keep14 _ (by decide), hEeq13, r12v15]
    · rw [keep15 _ (by decide), keep14 _ (by decide), hEeq13, r12v15]; omega
  obtain ⟨s17, st16, pc17, r12_17, keep17, d17⟩ :=
    step16_add code input pc16 (at_wb subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have r12v17 : (reg s17 r12).val = emitBase + 3 * n + 1 := by
    rw [r12_17, add_no_wrap]
    · rw [r12v16, keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), h1eq13]
    · rw [r12v16, keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), h1eq13]; omega
  obtain ⟨s18, st17, pc18, r12_18, keep18, d18⟩ :=
    step16_add code input pc17 (at_wb subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide))
  have r12v18 : (reg s18 r12).val = emitBase + 3 * n + 1 + (qStartFn S d + k) := by
    rw [r12_18, add_no_wrap]
    · rw [r12v17, keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), r15eq13]
    · rw [r12v17, keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), r15eq13]; omega
  have r11eq18 : (reg s18 r11).val = srcVal := by
    rw [keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide),
      keep14 _ (by decide), r11_13]
  have hData18 : s18.data = s₄.data := by rw [d18, d17, d16, d15, d14, d13, hData12]
  have hBnd18 : (reg s18 r12).val < s18.data.size := by rw [r12v18, hData18, hDataSz]; omega
  obtain ⟨s19, st18, pc19, regs19, d19⟩ :=
    step16_storeData code input pc18 (at_wb subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide)) hBnd18
  have reg19 : ∀ r : Fin 16, reg s19 r = reg s18 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs19 r
  have hSteps : Steps code input 15 s₄ s19 :=
    Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.cons st7 (Steps.cons st8
      (Steps.cons st9 (Steps.cons st10 (Steps.cons st11 (Steps.cons st12 (Steps.cons st13
        (Steps.cons st14 (Steps.cons st15 (Steps.cons st16 (Steps.cons st17 (Steps.cons st18
          (Steps.zero s19)))))))))))))))
  refine ⟨s19, hSteps, pc19, by rw [d19, Array.size_set, hData18, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [reg19, keep18 _ h12, keep17 _ h12, keep16 _ h12, keep15 _ h12, keep14 _ h12,
      keep13 _ h11, keep12 _ h11, keep11 _ h11, keep10 _ h11, keep9 _ h15,
      keep8 _ h15, keep7 _ h12, keep6 _ h12, keep5 _ h12]
  · rw [reg19, keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide),
      keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), r13eq11]
  · rw [reg19, keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide),
      keep14 _ (by decide), keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide),
      keep10 _ (by decide), keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide),
      keep6 _ (by decide), keep5 _ (by decide), hr14]
  · rw [reg19, keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide),
      keep14 _ (by decide), r15eq13]
  · intro addr; rw [d19]
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · rw [mem_set_same s18.data (r12v18.trans hk.symm) hBnd18, Option.map_some, r11eq18]
    · rw [mem_set_ne s18.data hBnd18 (fun e => hne (e.trans r12v18)), hData18]

private theorem wbBodyB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed k hdVal m_d qd : Nat}
    (hkLt : k < m_d) (hm_d : m_d ≤ m) (hHdLt : hdVal < n) (hqd : qd + m_d ≤ m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s19 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s19.pc = offWB + 19) (hDataSz : s19.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s19)
    (hr13 : (reg s19 r13).val = k) (hr14 : (reg s19 r14).val = m_d) (hr15 : (reg s19 r15).val = qd + k)
    (hHeadAt : (s19.data[loopBase + 3 + m_d + k]?).map Fin.val = some hdVal) :
    ∃ s31, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 12 s19 s31 ∧
      s31.pc = offWB + 31 ∧ s31.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s31 ∧
      (reg s31 r13).val = k ∧ (reg s31 r14).val = m_d ∧ (reg s31 r15).val = qd + k ∧
      (∀ addr, (addr = emitBase + 3 * n + m + 1 + (qd + k) → (s31.data[addr]?).map Fin.val = some hdVal) ∧
        (addr ≠ emitBase + 3 * n + m + 1 + (qd + k) → s31.data[addr]? = s19.data[addr]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 32 → offWB + c < code.size := by
    intro c hc; rw [hSz]; unfold offWB; omega
  have hOne : (reg s19 rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s19 rN).val = n := hRegs.entry.consts.nVal
  have hM : (reg s19 rM).val = m := hRegs.entry.consts.mVal
  have hE : (reg s19 r7).val = emitBase := hRegs.entry.emitBaseVal
  have hL : (reg s19 r8).val = loopBase := hRegs.entry.loopBaseVal
  have hLoopBnd : loopBase + 3 + m_d + k < workCap := by unfold loopWorkWords at hFit; omega
  have hEmitBnd : emitBase + 3 * n + m + 1 + (qd + k) < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h3NLt : 3 * n + m < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  -- 19..23: load sorted head
  obtain ⟨s20, st19, pc20, r11_20, keep20, d20⟩ :=
    step16_imm code input hpc (at_wb subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  obtain ⟨s21, st20, pc21, r11_21, keep21, d21⟩ :=
    step16_add code input pc20 (at_wb subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide))
  have r11v21 : (reg s21 r11).val = loopBase + 3 := by
    rw [r11_21, add_no_wrap]
    · rw [keep20 _ (by decide), hL, r11_20]; rfl
    · rw [keep20 _ (by decide), hL, r11_20]; change loopBase + 3 < 2 ^ bits; omega
  obtain ⟨s22, st21, pc22, r11_22, keep22, d22⟩ :=
    step16_add code input pc21 (at_wb subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
  have r14eq21 : (reg s21 r14).val = m_d := by
    rw [keep21 _ (by decide), keep20 _ (by decide), hr14]
  have r11v22 : (reg s22 r11).val = loopBase + 3 + m_d := by
    rw [r11_22, add_no_wrap] <;> rw [r11v21, r14eq21] <;> omega
  obtain ⟨s23, st22, pc23, r11_23, keep23, d23⟩ :=
    step16_add code input pc22 (at_wb subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide))
  have r13eq22 : (reg s22 r13).val = k := by
    rw [keep22 _ (by decide), keep21 _ (by decide), keep20 _ (by decide), hr13]
  have r11v23 : (reg s23 r11).val = loopBase + 3 + m_d + k := by
    rw [r11_23, add_no_wrap] <;> rw [r11v22, r13eq22] <;> omega
  have hData23 : s23.data = s19.data := by rw [d23, d22, d21, d20]
  have hMemH : s23.data[(reg s23 r11).val]? = some ⟨hdVal, by omega⟩ := by
    rw [r11v23, hData23]; exact mem_word_of_map hHeadAt _
  obtain ⟨s24, st23, pc24, r11_24, keep24, d24⟩ :=
    step16_loadData code input pc23 (at_wb subCode h32 (i := 23) (by decide)) hMemH (hPcLt 24 (by decide))
  -- 24..30: store head at emitBase + 3*n + m + 1 + qd + k
  have hNeq24 : (reg s24 rN).val = n := by
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), hN]
  have hMeq24 : (reg s24 rM).val = m := by
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), hM]
  have hEeq24 : (reg s24 r7).val = emitBase := by
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), hE]
  have h1eq24 : (reg s24 rOne).val = 1 := by
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), hOne]
  have r15eq24 : (reg s24 r15).val = qd + k := by
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), hr15]
  obtain ⟨s25, st24, pc25, r12_25, keep25, d25⟩ :=
    step16_add code input pc24 (at_wb subCode h32 (i := 24) (by decide)) (hPcLt 25 (by decide))
  have r12v25 : (reg s25 r12).val = 2 * n := by rw [r12_25, add_no_wrap] <;> rw [hNeq24] <;> omega
  obtain ⟨s26, st25, pc26, r12_26, keep26, d26⟩ :=
    step16_add code input pc25 (at_wb subCode h32 (i := 25) (by decide)) (hPcLt 26 (by decide))
  have r12v26 : (reg s26 r12).val = 3 * n := by
    rw [r12_26, add_no_wrap] <;> rw [r12v25, keep25 _ (by decide), hNeq24] <;> omega
  obtain ⟨s27, st26, pc27, r12_27, keep27, d27⟩ :=
    step16_add code input pc26 (at_wb subCode h32 (i := 26) (by decide)) (hPcLt 27 (by decide))
  have r12v27 : (reg s27 r12).val = 3 * n + m := by
    rw [r12_27, add_no_wrap] <;> rw [r12v26, keep26 _ (by decide), keep25 _ (by decide), hMeq24] <;> omega
  obtain ⟨s28, st27, pc28, r12_28, keep28, d28⟩ :=
    step16_add code input pc27 (at_wb subCode h32 (i := 27) (by decide)) (hPcLt 28 (by decide))
  have r12v28 : (reg s28 r12).val = emitBase + 3 * n + m := by
    rw [r12_28, add_no_wrap]
    · rw [keep27 _ (by decide), keep26 _ (by decide), keep25 _ (by decide), hEeq24, r12v27]; omega
    · rw [keep27 _ (by decide), keep26 _ (by decide), keep25 _ (by decide), hEeq24, r12v27]; omega
  obtain ⟨s29, st28, pc29, r12_29, keep29, d29⟩ :=
    step16_add code input pc28 (at_wb subCode h32 (i := 28) (by decide)) (hPcLt 29 (by decide))
  have r12v29 : (reg s29 r12).val = emitBase + 3 * n + m + 1 := by
    rw [r12_29, add_no_wrap]
    · rw [r12v28, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), keep25 _ (by decide), h1eq24]
    · rw [r12v28, keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), keep25 _ (by decide), h1eq24]; omega
  obtain ⟨s30, st29, pc30, r12_30, keep30, d30⟩ :=
    step16_add code input pc29 (at_wb subCode h32 (i := 29) (by decide)) (hPcLt 30 (by decide))
  have r12v30 : (reg s30 r12).val = emitBase + 3 * n + m + 1 + (qd + k) := by
    rw [r12_30, add_no_wrap]
    · rw [r12v29, keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide),
        keep25 _ (by decide), r15eq24]
    · rw [r12v29, keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide),
        keep25 _ (by decide), r15eq24]; omega
  have r11eq30 : (reg s30 r11).val = hdVal := by
    rw [keep30 _ (by decide), keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide),
      keep26 _ (by decide), keep25 _ (by decide), r11_24]
  have hData30 : s30.data = s19.data := by rw [d30, d29, d28, d27, d26, d25, d24, hData23]
  have hBnd30 : (reg s30 r12).val < s30.data.size := by rw [r12v30, hData30, hDataSz]; exact hEmitBnd
  obtain ⟨s31, st30, pc31, regs31, d31⟩ :=
    step16_storeData code input pc30 (at_wb subCode h32 (i := 30) (by decide)) (hPcLt 31 (by decide)) hBnd30
  have reg31 : ∀ r : Fin 16, reg s31 r = reg s30 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs31 r
  have hSteps : Steps code input 12 s19 s31 :=
    Steps.cons st19 (Steps.cons st20 (Steps.cons st21 (Steps.cons st22 (Steps.cons st23
      (Steps.cons st24 (Steps.cons st25 (Steps.cons st26 (Steps.cons st27 (Steps.cons st28
        (Steps.cons st29 (Steps.cons st30 (Steps.zero s31))))))))))))
  refine ⟨s31, hSteps, pc31, by rw [d31, Array.size_set, hData30, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    rw [reg31, keep30 _ h12, keep29 _ h12, keep28 _ h12, keep27 _ h12, keep26 _ h12, keep25 _ h12,
      keep24 _ h11, keep23 _ h11, keep22 _ h11, keep21 _ h11, keep20 _ h11]
  · rw [reg31, keep30 _ (by decide), keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide),
      keep26 _ (by decide), keep25 _ (by decide), keep24 _ (by decide), keep23 _ (by decide), r13eq22]
  · rw [reg31, keep30 _ (by decide), keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide),
      keep26 _ (by decide), keep25 _ (by decide), keep24 _ (by decide), keep23 _ (by decide),
      keep22 _ (by decide), r14eq21]
  · rw [reg31, keep30 _ (by decide), keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide),
      keep26 _ (by decide), keep25 _ (by decide), r15eq24]
  · intro addr; rw [d31]
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · rw [mem_set_same s30.data (r12v30.trans hk.symm) hBnd30, Option.map_some, r11eq30]
    · rw [mem_set_ne s30.data hBnd30 (fun e => hne (e.trans r12v30)), hData30]

private theorem wbBodyC_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed k tailE m_d qd : Nat}
    (hkLt : k < m_d) (hm_d : m_d ≤ m) (htail : tailE < Q) (hQLe : Q ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s31 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s31.pc = offWB + 31)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s31)
    (hr13 : (reg s31 r13).val = k) (hr14 : (reg s31 r14).val = m_d) (hr15 : (reg s31 r15).val = qd + k)
    (hStPtr : (s31.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hEntPtr : (s31.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m))
    (hTailAt : (s31.data[loopSortEntryBase loopBase n m + k]?).map Fin.val = some tailE) :
    ∃ s38, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 7 s31 s38 ∧
      s38.pc = offWB + 38 ∧ s38.data = s31.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s38 ∧
      (reg s38 r11).val = tailE ∧ (reg s38 r13).val = k ∧ (reg s38 r14).val = m_d ∧
      (reg s38 r15).val = qd + k := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 39 → offWB + c < code.size := by
    intro c hc; rw [hSz]; unfold offWB; omega
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hEntBnd : loopSortEntryBase loopBase n m + m ≤ workCap := by
    unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
      rawInputCap rawWorkCap loopWorkWords at *; omega
  have hTailLt : tailE < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  obtain ⟨s32, st31, pc32, r12_32, keep32, d32⟩ :=
    step16_imm code input hpc (at_wb subCode h32 (i := 31) (by decide)) (hPcLt 32 (by decide))
  have hMemSt : s32.data[(reg s32 r12).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d32, show (reg s32 r12).val = statePtrAddr by rw [r12_32]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s33, st32, pc33, r11_33, keep33, d33⟩ :=
    step16_loadData code input pc32 (at_wb subCode h32 (i := 32) (by decide)) hMemSt (hPcLt 33 (by decide))
  obtain ⟨s34, st33, pc34, r12_34, keep34, d34⟩ :=
    step16_imm code input pc33 (at_wb subCode h32 (i := 33) (by decide)) (hPcLt 34 (by decide))
  obtain ⟨s35, st34, pc35, r11_35, keep35, d35⟩ :=
    step16_add code input pc34 (at_wb subCode h32 (i := 34) (by decide)) (hPcLt 35 (by decide))
  have hAddr35 : (reg s35 r11).val = loopSubStateBase loopBase n m + 13 := by
    rw [r11_35, add_no_wrap]
    · rw [keep34 _ (by decide), r11_33, r12_34]; rfl
    · rw [keep34 _ (by decide), r11_33, r12_34]; dsimp only; change _ + 13 < 2 ^ bits; omega
  have hMemEnt : s35.data[(reg s35 r11).val]? = some ⟨loopSortEntryBase loopBase n m, by omega⟩ := by
    rw [hAddr35, d35, d34, d33, d32]; exact mem_word_of_map hEntPtr _
  obtain ⟨s36, st35, pc36, r11_36, keep36, d36⟩ :=
    step16_loadData code input pc35 (at_wb subCode h32 (i := 35) (by decide)) hMemEnt (hPcLt 36 (by decide))
  have r13eq36 : (reg s36 r13).val = k := by
    rw [keep36 _ (by decide), keep35 _ (by decide), keep34 _ (by decide), keep33 _ (by decide),
      keep32 _ (by decide), hr13]
  obtain ⟨s37, st36, pc37, r11_37, keep37, d37⟩ :=
    step16_add code input pc36 (at_wb subCode h32 (i := 36) (by decide)) (hPcLt 37 (by decide))
  have r11v37 : (reg s37 r11).val = loopSortEntryBase loopBase n m + k := by
    rw [r11_37, add_no_wrap] <;> rw [r11_36, r13eq36] <;> dsimp only <;> omega
  have hMemT : s37.data[(reg s37 r11).val]? = some ⟨tailE, hTailLt⟩ := by
    rw [r11v37, d37, d36, d35, d34, d33, d32]; exact mem_word_of_map hTailAt hTailLt
  obtain ⟨s38, st37, pc38, r11_38, keep38, d38⟩ :=
    step16_loadData code input pc37 (at_wb subCode h32 (i := 37) (by decide)) hMemT (hPcLt 38 (by decide))
  refine ⟨s38, Steps.cons st31 (Steps.cons st32 (Steps.cons st33 (Steps.cons st34
      (Steps.cons st35 (Steps.cons st36 (Steps.cons st37 (Steps.zero s38))))))),
    pc38, by rw [d38, d37, d36, d35, d34, d33, d32],
    loopIterRegs_of_keep hRegs fun r hr => ?_, by rw [r11_38], ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    rw [keep38 _ h11, keep37 _ h11, keep36 _ h11, keep35 _ h11, keep34 _ h12, keep33 _ h11, keep32 _ h12]
  · rw [keep38 _ (by decide), keep37 _ (by decide), r13eq36]
  · rw [keep38 _ (by decide), keep37 _ (by decide), keep36 _ (by decide), keep35 _ (by decide),
      keep34 _ (by decide), keep33 _ (by decide), keep32 _ (by decide), hr14]
  · rw [keep38 _ (by decide), keep37 _ (by decide), keep36 _ (by decide), keep35 _ (by decide),
      keep34 _ (by decide), keep33 _ (by decide), keep32 _ (by decide), hr15]

private theorem wbBodyD_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed k tailE m_d qd : Nat}
    (hkLt : k < m_d) (hm_d : m_d ≤ m) (hqd : qd + m_d ≤ m)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    {s38 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s38.pc = offWB + 38) (hDataSz : s38.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s38)
    (hr11 : (reg s38 r11).val = tailE) (hr13 : (reg s38 r13).val = k)
    (hr15 : (reg s38 r15).val = qd + k) :
    ∃ s48, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 10 s38 s48 ∧
      s48.pc = offWB + 1 ∧ s48.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s48 ∧
      (reg s48 r13).val = k + 1 ∧
      (∀ addr, (addr = emitBase + 3 * n + 2 * m + 1 + (qd + k) → (s48.data[addr]?).map Fin.val = some tailE) ∧
        (addr ≠ emitBase + 3 * n + 2 * m + 1 + (qd + k) → s48.data[addr]? = s38.data[addr]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 49 → offWB + c < code.size := by
    intro c hc; rw [hSz]; unfold offWB; omega
  have hOne : (reg s38 rOne).val = 1 := hRegs.entry.consts.one
  have hN : (reg s38 rN).val = n := hRegs.entry.consts.nVal
  have hM : (reg s38 rM).val = m := hRegs.entry.consts.mVal
  have hE : (reg s38 r7).val = emitBase := hRegs.entry.emitBaseVal
  have hEmitBnd : emitBase + 3 * n + 2 * m + 1 + (qd + k) < workCap := by
    unfold emitterWorkWords at hEmitFit; omega
  have h3NLt : 3 * n + 2 * m < 2 ^ bits := by unfold emitterWorkWords at hEmitFit; omega
  obtain ⟨s39, st38, pc39, r12_39, keep39, d39⟩ :=
    step16_add code input hpc (at_wb subCode h32 (i := 38) (by decide)) (hPcLt 39 (by decide))
  have r12v39 : (reg s39 r12).val = 2 * n := by rw [r12_39, add_no_wrap] <;> rw [hN] <;> omega
  obtain ⟨s40, st39, pc40, r12_40, keep40, d40⟩ :=
    step16_add code input pc39 (at_wb subCode h32 (i := 39) (by decide)) (hPcLt 40 (by decide))
  have r12v40 : (reg s40 r12).val = 3 * n := by
    rw [r12_40, add_no_wrap] <;> rw [r12v39, keep39 _ (by decide), hN] <;> omega
  obtain ⟨s41, st40, pc41, r12_41, keep41, d41⟩ :=
    step16_add code input pc40 (at_wb subCode h32 (i := 40) (by decide)) (hPcLt 41 (by decide))
  have r12v41 : (reg s41 r12).val = 3 * n + m := by
    rw [r12_41, add_no_wrap] <;> rw [r12v40, keep40 _ (by decide), keep39 _ (by decide), hM] <;> omega
  obtain ⟨s42, st41, pc42, r12_42, keep42, d42⟩ :=
    step16_add code input pc41 (at_wb subCode h32 (i := 41) (by decide)) (hPcLt 42 (by decide))
  have r12v42 : (reg s42 r12).val = 3 * n + 2 * m := by
    rw [r12_42, add_no_wrap]
    · rw [r12v41, keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hM]; omega
    · rw [r12v41, keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hM]; omega
  obtain ⟨s43, st42, pc43, r12_43, keep43, d43⟩ :=
    step16_add code input pc42 (at_wb subCode h32 (i := 42) (by decide)) (hPcLt 43 (by decide))
  have r12v43 : (reg s43 r12).val = emitBase + 3 * n + 2 * m := by
    rw [r12_43, add_no_wrap]
    · rw [keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hE, r12v42]; omega
    · rw [keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hE, r12v42]; omega
  obtain ⟨s44, st43, pc44, r12_44, keep44, d44⟩ :=
    step16_add code input pc43 (at_wb subCode h32 (i := 43) (by decide)) (hPcLt 44 (by decide))
  have r12v44 : (reg s44 r12).val = emitBase + 3 * n + 2 * m + 1 := by
    rw [r12_44, add_no_wrap]
    · rw [r12v43, keep43 _ (by decide), keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide),
        keep39 _ (by decide), hOne]
    · rw [r12v43, keep43 _ (by decide), keep42 _ (by decide), keep41 _ (by decide), keep40 _ (by decide),
        keep39 _ (by decide), hOne]; omega
  obtain ⟨s45, st44, pc45, r12_45, keep45, d45⟩ :=
    step16_add code input pc44 (at_wb subCode h32 (i := 44) (by decide)) (hPcLt 45 (by decide))
  have r12v45 : (reg s45 r12).val = emitBase + 3 * n + 2 * m + 1 + (qd + k) := by
    rw [r12_45, add_no_wrap]
    · rw [r12v44, keep44 _ (by decide), keep43 _ (by decide), keep42 _ (by decide), keep41 _ (by decide),
        keep40 _ (by decide), keep39 _ (by decide), hr15]
    · rw [r12v44, keep44 _ (by decide), keep43 _ (by decide), keep42 _ (by decide), keep41 _ (by decide),
        keep40 _ (by decide), keep39 _ (by decide), hr15]; omega
  have r11eq45 : (reg s45 r11).val = tailE := by
    rw [keep45 _ (by decide), keep44 _ (by decide), keep43 _ (by decide), keep42 _ (by decide),
      keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hr11]
  have hData45 : s45.data = s38.data := by rw [d45, d44, d43, d42, d41, d40, d39]
  have hBnd45 : (reg s45 r12).val < s45.data.size := by rw [r12v45, hData45, hDataSz]; exact hEmitBnd
  obtain ⟨s46, st45, pc46, regs46, d46⟩ :=
    step16_storeData code input pc45 (at_wb subCode h32 (i := 45) (by decide)) (hPcLt 46 (by decide)) hBnd45
  have reg46 : ∀ r : Fin 16, reg s46 r = reg s45 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs46 r
  obtain ⟨s47, st46, pc47, r13_47, keep47, d47⟩ :=
    step16_add code input pc46 (at_wb subCode h32 (i := 46) (by decide)) (hPcLt 47 (by decide))
  have r13eq46 : (reg s46 r13).val = k := by
    rw [reg46, keep45 _ (by decide), keep44 _ (by decide), keep43 _ (by decide), keep42 _ (by decide),
      keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hr13]
  have h1eq46 : (reg s46 rOne).val = 1 := by
    rw [reg46, keep45 _ (by decide), keep44 _ (by decide), keep43 _ (by decide), keep42 _ (by decide),
      keep41 _ (by decide), keep40 _ (by decide), keep39 _ (by decide), hOne]
  have r13v47 : (reg s47 r13).val = k + 1 := by
    rw [r13_47, add_no_wrap]
    · rw [r13eq46, h1eq46]
    · rw [r13eq46, h1eq46]; omega
  have st47 := step16_goto code input pc47 (at_wb subCode h32 (i := 47) (by decide)) (hPcLt 1 (by decide))
  let s48 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s47.regs, data := s47.data, pc := offWB + 1,
      regs_size := s47.regs_size, data_size := s47.data_size }
  have hSteps : Steps code input 10 s38 s48 :=
    Steps.cons st38 (Steps.cons st39 (Steps.cons st40 (Steps.cons st41 (Steps.cons st42
      (Steps.cons st43 (Steps.cons st44 (Steps.cons st45 (Steps.cons st46 (Steps.cons st47 (Steps.zero s48))))))))))
  refine ⟨s48, hSteps, rfl, by change s47.data.size = _; rw [d47, d46, Array.size_set, hData45, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_⟩
  · have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    change reg s47 r = reg s38 r
    rw [keep47 _ h13, reg46, keep45 _ h12, keep44 _ h12, keep43 _ h12, keep42 _ h12,
      keep41 _ h12, keep40 _ h12, keep39 _ h12]
  · change (reg s47 r13).val = _; exact r13v47
  · intro addr
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · change (s47.data[addr]?).map Fin.val = some tailE
      rw [d47, d46, mem_set_same s45.data (r12v45.trans hk.symm) hBnd45, Option.map_some, r11eq45]
    · change s47.data[addr]? = s38.data[addr]?
      rw [d47, d46, mem_set_ne s45.data hBnd45 (fun e => hne (e.trans r12v45)), hData45]

private theorem wb_slot_disjoint {emitBase n m qd j k m_d : Nat}
    (hjk : j ≠ k) (hj : j < m_d) (hk : k < m_d) (hm_d : m_d ≤ m) :
    (emitBase + 3 * n + 1 + (qd + j) ≠ emitBase + 3 * n + 2 * m + 1 + (qd + k)) ∧
    (emitBase + 3 * n + 1 + (qd + j) ≠ emitBase + 3 * n + m + 1 + (qd + k)) ∧
    (emitBase + 3 * n + 1 + (qd + j) ≠ emitBase + 3 * n + 1 + (qd + k)) ∧
    (emitBase + 3 * n + m + 1 + (qd + j) ≠ emitBase + 3 * n + 2 * m + 1 + (qd + k)) ∧
    (emitBase + 3 * n + m + 1 + (qd + j) ≠ emitBase + 3 * n + m + 1 + (qd + k)) ∧
    (emitBase + 3 * n + m + 1 + (qd + j) ≠ emitBase + 3 * n + 1 + (qd + k)) ∧
    (emitBase + 3 * n + 2 * m + 1 + (qd + j) ≠ emitBase + 3 * n + 2 * m + 1 + (qd + k)) ∧
    (emitBase + 3 * n + 2 * m + 1 + (qd + j) ≠ emitBase + 3 * n + m + 1 + (qd + k)) ∧
    (emitBase + 3 * n + 2 * m + 1 + (qd + j) ≠ emitBase + 3 * n + 1 + (qd + k)) := by
  omega

private def wbIsWritten (emitBase n m qd k addr : Nat) : Prop :=
  (emitBase + 3 * n + 1 + qd ≤ addr ∧ addr < emitBase + 3 * n + 1 + (qd + k)) ∨
  (emitBase + 3 * n + m + 1 + qd ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + (qd + k)) ∨
  (emitBase + 3 * n + 2 * m + 1 + qd ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + (qd + k))

private theorem writeBack_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    {n m root Q emitBase loopBase d forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length) (hd : d < Q)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisj : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offWB) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hMdAt : (s₀.data[loopBase + 1]?).map Fin.val = some (S.emittedArcs ⟨d, hQ ▸ hd⟩).length)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hEntPtr : (s₀.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m))
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hSortedBuf : ∀ (pos : Nat) (hp : pos < (S.emittedArcs ⟨d, hQ ▸ hd⟩).length),
      let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
      let ea := (countingSortedArcs (1 + (S.childSlice dFin).length) (S.emittedArcs dFin))[pos]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds dFin hx).2.1)]; exact hp)
      (s₀.data[loopBase + 3 + pos]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[loopBase + 3 + (S.emittedArcs dFin).length + pos]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[loopSortEntryBase loopBase n m + pos]?).map Fin.val = some ea.tailEntry) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let n_d := 1 + (S.childSlice dFin).length
    let m_d := (S.emittedArcs dFin).length
    let sorted := countingSortedArcs n_d (S.emittedArcs dFin)
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 48 * m_d + 8 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offBranch ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t ∧
      (∀ (k : Nat) (hk : k < m_d),
        let ea := sorted[k]'(by rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds dFin hx).2.1)]; exact hk)
        (t.data[emitBase + 3 * n + 1 + (qStartFn S d + k)]?).map Fin.val = some ea.srcLocal ∧
        (t.data[emitBase + 3 * n + m + 1 + (qStartFn S d + k)]?).map Fin.val = some ea.headLocal ∧
        (t.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + k)]?).map Fin.val = some ea.tailEntry) ∧
      (∀ addr,
        (addr < emitBase + 3 * n + 1 + qStartFn S d ∨
          (emitBase + 3 * n + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + qStartFn S d) ∨
          (emitBase + 3 * n + m + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + qStartFn S d) ∨
          emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro dFin n_d m_d sorted
  let arcs := S.emittedArcs dFin
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 49 → offWB + c < code.size := by
    intro c hc; rw [hSz]; unfold offWB; omega
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hNdLe : n_d ≤ n := Nat.le_trans (by rw [hQ]; exact ownerVertexCount_le_Q S dFin) hQL
  have hSucc : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S dFin.isLt
  have hQS1 : qStartFn S (d + 1) ≤ m := hm.symm ▸ qStartFn_le_arcCount S (d + 1)
  have hMdLe : m_d ≤ m := by omega
  have hArcsBnd : ∀ ea ∈ arcs, ea.srcLocal < n_d := fun ea hea => (S.emittedArc_bounds dFin hea).2.1
  have hSortBnd : ∀ ea ∈ sorted, ea.srcLocal < n_d ∧ ea.headLocal < n_d ∧ ea.tailEntry < Q := by
    intro ea hea
    unfold sorted countingSortedArcs at hea
    rw [List.mem_flatMap] at hea
    obtain ⟨_, _, hMem⟩ := hea
    have hMemOrig := (List.mem_filter.mp hMem).1
    have hb := S.emittedArc_bounds dFin hMemOrig
    exact ⟨hb.2.1, hb.2.2.1, hQ ▸ hb.2.2.2⟩
  have hZero : (reg s₀ rZero).val = 0 := hRegs.entry.consts.zero
  obtain ⟨s1, st0, pc1, r13_1, keep1, d1⟩ :=
    step16_mov code input hpc (at_wb subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hSt0 : Steps code input 1 s₀ s1 := steps_one st0
  have hRg1 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s1 :=
    loopIterRegs_of_keep hRegs fun r hr => keep1 r (fun e => absurd hr (by subst e; decide))
  have hr13_1 : (reg s1 r13).val = 0 := by rw [r13_1, hZero]
  have hBufDisj : ∀ k < m_d, ∀ j < m_d,
      ¬ wbIsWritten emitBase n m (qStartFn S d) k (loopBase + 3 + j) ∧
      ¬ wbIsWritten emitBase n m (qStartFn S d) k (loopBase + 3 + m_d + j) ∧
      ¬ wbIsWritten emitBase n m (qStartFn S d) k (loopSortEntryBase loopBase n m + j) := by
    intro k hk j hj
    unfold wbIsWritten loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
      rawInputCap rawWorkCap
    unfold loopWorkWords at hDisj
    unfold emitterWorkWords at hDisj
    omega
  have hMetaDisj : ∀ k ≤ m_d,
      ¬ wbIsWritten emitBase n m (qStartFn S d) k statePtrAddr ∧
      ¬ wbIsWritten emitBase n m (qStartFn S d) k (loopBase + 1) ∧
      ¬ wbIsWritten emitBase n m (qStartFn S d) k (loopSubStateBase loopBase n m + 13) ∧
      ¬ wbIsWritten emitBase n m (qStartFn S d) k (emitBase + 2 * n + d) := by
    intro k hk
    unfold wbIsWritten statePtrAddr loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
    unfold loopWorkWords at hDisj
    unfold emitterWorkWords at hDisj
    omega
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun k s =>
    k ≤ m_d ∧ s.pc = offWB + 1 ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (reg s r13).val = k ∧
    (∀ (j : Nat), j < k → ∀ (hj : j < m_d),
      let ea := sorted[j]'(by rw [countingSortedArcs_length _ hArcsBnd]; exact hj)
      (s.data[emitBase + 3 * n + 1 + (qStartFn S d + j)]?).map Fin.val = some ea.srcLocal ∧
      (s.data[emitBase + 3 * n + m + 1 + (qStartFn S d + j)]?).map Fin.val = some ea.headLocal ∧
      (s.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + j)]?).map Fin.val = some ea.tailEntry) ∧
    (∀ addr, ¬ wbIsWritten emitBase n m (qStartFn S d) k addr → s.data[addr]? = s₀.data[addr]?)
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offBranch ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (∀ (k : Nat) (hk : k < m_d),
      let ea := sorted[k]'(by rw [countingSortedArcs_length _ hArcsBnd]; exact hk)
      (s.data[emitBase + 3 * n + 1 + (qStartFn S d + k)]?).map Fin.val = some ea.srcLocal ∧
      (s.data[emitBase + 3 * n + m + 1 + (qStartFn S d + k)]?).map Fin.val = some ea.headLocal ∧
      (s.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + k)]?).map Fin.val = some ea.tailEntry) ∧
    (∀ addr,
      (addr < emitBase + 3 * n + 1 + qStartFn S d ∨
        (emitBase + 3 * n + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + qStartFn S d) ∨
        (emitBase + 3 * n + m + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + qStartFn S d) ∨
        emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr) →
      s.data[addr]? = s₀.data[addr]?)
  have hLoop := loop_steps_budget inv (fun k => m_d - k) (fun k => 3 + 47 * (m_d - k)) post
    (fun k s ⟨hkLe, hpcS, hSzS, hRgS, hr13S, hWrtS, hOutS⟩ => by
      have hMdS : (s.data[loopBase + 1]?).map Fin.val = some m_d := by
        rw [hOutS _ (hMetaDisj k hkLe).2.1]; exact hMdAt
      have hL : (reg s r8).val = loopBase := hRgS.entry.loopBaseVal
      have h1 : (reg s rOne).val = 1 := hRgS.entry.consts.one
      have hLoopBnd : loopBase + 1 < workCap := by unfold loopWorkWords at hFit; omega
      obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
        step16_add code input hpcS (at_wb subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
      have r12v2 : (reg s2 r12).val = loopBase + 1 := by rw [r12_2, add_no_wrap] <;> rw [hL, h1] <;> omega
      have hMemMd2 : s2.data[(reg s2 r12).val]? = some ⟨m_d, by unfold loopWorkWords at hFit; omega⟩ := by
        rw [r12v2, d2]; exact mem_word_of_map hMdS _
      obtain ⟨s3, st2, pc3, r14_3, keep3, d3⟩ :=
        step16_loadData code input pc2 (at_wb subCode h32 (i := 2) (by decide)) hMemMd2 (hPcLt 3 (by decide))
      have hr13_3 : (reg s3 r13).val = k := by rw [keep3 _ (by decide), keep2 _ (by decide), hr13S]
      have hRg3 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s3 :=
        loopIterRegs_of_keep hRgS fun r hr =>
          keep3 r (fun e => absurd hr (by subst e; decide)) |>.trans
            (keep2 r (fun e => absurd hr (by subst e; decide)))
      by_cases hkEq : k = m_d
      · subst hkEq
        have hGe : (reg s3 r14).val ≤ (reg s3 r13).val := by rw [r14_3, hr13_3]; exact Nat.le_refl _
        have stBr := step16_branchLt_false code input pc3 (at_wb subCode h32 (i := 3) (by decide))
          (hPcLt 48 (by decide)) hGe
        refine Or.inl ⟨_, 3, by omega, Steps.cons st1 (Steps.cons st2 (Steps.cons stBr (Steps.zero _))),
          ?_, by rw [d3, d2, hSzS], loopIterRegs_of_keep hRg3 (fun _ _ => rfl),
          fun j hj => by rw [d3, d2]; exact hWrtS j hj hj, fun addr ha => by
            rw [d3, d2]
            apply hOutS
            unfold wbIsWritten
            rw [hSucc] at ha
            omega⟩
        · change offWB + 48 = offBranch; unfold offWB offBranch; omega
      · have hkLt : k < m_d := Nat.lt_of_le_of_ne hkLe hkEq
        have hLtR : (reg s3 r13).val < (reg s3 r14).val := by rw [r14_3, hr13_3]; exact hkLt
        have st3 := step16_branchLt_true code input pc3 (at_wb subCode h32 (i := 3) (by decide))
          (hPcLt 4 (by decide)) hLtR
        let s4 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s3.regs, data := s3.data, pc := offWB + 4,
            regs_size := s3.regs_size, data_size := s3.data_size }
        have hSt4 : Steps code input 3 s s4 := Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.zero s4)))
        have hD4 : s4.data = s.data := by rw [d3, d2]
        have hSz4 : s4.data.size = workCap := by rw [hD4, hSzS]
        have hRg4 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s4 :=
          loopIterRegs_of_keep hRg3 (fun _ _ => rfl)
        let ea := sorted[k]'(by rw [countingSortedArcs_length _ hArcsBnd]; exact hkLt)
        have hEaMem : ea ∈ sorted := List.getElem_mem _
        have hEaB := hSortBnd ea hEaMem
        have hBufK := hSortedBuf k hkLt
        have hDisjK := hBufDisj k hkLt k hkLt
        have hMetaK := hMetaDisj k hkLe
        have hQAt4 : (s4.data[emitBase + 2 * n + d]?).map Fin.val = some (qStartFn S d) := by
          rw [hD4, hOutS _ hMetaK.2.2.2]; exact hQStarts d (Nat.le_of_lt hd)
        have hSrc4 : (s4.data[loopBase + 3 + k]?).map Fin.val = some ea.srcLocal := by
          rw [hD4, hOutS _ hDisjK.1]; exact hBufK.1
        obtain ⟨s19, hStA, pc19, sz19, hRg19, hr13_19, hr14_19, hr15_19, hMem19⟩ :=
          wbBodyA_steps subCode h32 input S hn hm hQ hd hkLt hMdLe (Nat.lt_of_lt_of_le hEaB.1 hNdLe)
            hSucc hFit hEmitFit hBits rfl hSz4 hRg4 hr13_3 (congrArg Fin.val r14_3) hQAt4 hSrc4
        have hLoopDisjEmit : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase := hDisj
        have hNeHA : loopBase + 3 + m_d + k ≠ emitBase + 3 * n + 1 + (qStartFn S d + k) := by
          unfold loopWorkWords emitterWorkWords at hLoopDisjEmit; omega
        have hHead19 : (s19.data[loopBase + 3 + m_d + k]?).map Fin.val = some ea.headLocal := by
          rw [(hMem19 _).2 hNeHA, hD4, hOutS _ hDisjK.2.1]; exact hBufK.2.1
        obtain ⟨s31, hStB, pc31, sz31, hRg31, hr13_31, hr14_31, hr15_31, hMem31⟩ :=
          wbBodyB_steps subCode h32 input hkLt hMdLe (Nat.lt_of_lt_of_le hEaB.2.1 hNdLe) (by omega)
            hFit hEmitFit hBits pc19 sz19 hRg19 hr13_19 hr14_19 hr15_19 hHead19
        have hStPtr31 : (s31.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
          have h1 : statePtrAddr ≠ emitBase + 3 * n + m + 1 + (qStartFn S d + k) := by
            unfold statePtrAddr; omega
          have h2 : statePtrAddr ≠ emitBase + 3 * n + 1 + (qStartFn S d + k) := by
            unfold statePtrAddr; omega
          rw [(hMem31 _).2 h1, (hMem19 _).2 h2, hD4, hOutS _ hMetaK.1]; exact hStPtr
        have hEntPtr31 : (s31.data[loopSubStateBase loopBase n m + 13]?).map Fin.val =
            some (loopSortEntryBase loopBase n m) := by
          have h1 : loopSubStateBase loopBase n m + 13 ≠ emitBase + 3 * n + m + 1 + (qStartFn S d + k) := by
            unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
            unfold loopWorkWords emitterWorkWords at hLoopDisjEmit; omega
          have h2 : loopSubStateBase loopBase n m + 13 ≠ emitBase + 3 * n + 1 + (qStartFn S d + k) := by
            unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap
            unfold loopWorkWords emitterWorkWords at hLoopDisjEmit; omega
          rw [(hMem31 _).2 h1, (hMem19 _).2 h2, hD4, hOutS _ hMetaK.2.2.1]; exact hEntPtr
        have hTail31 : (s31.data[loopSortEntryBase loopBase n m + k]?).map Fin.val = some ea.tailEntry := by
          have h1 : loopSortEntryBase loopBase n m + k ≠ emitBase + 3 * n + m + 1 + (qStartFn S d + k) := by
            unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
              rawInputCap rawWorkCap
            unfold loopWorkWords emitterWorkWords at hLoopDisjEmit; omega
          have h2 : loopSortEntryBase loopBase n m + k ≠ emitBase + 3 * n + 1 + (qStartFn S d + k) := by
            unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase
              rawInputCap rawWorkCap
            unfold loopWorkWords emitterWorkWords at hLoopDisjEmit; omega
          rw [(hMem31 _).2 h1, (hMem19 _).2 h2, hD4, hOutS _ hDisjK.2.2]; exact hBufK.2.2
        obtain ⟨s38, hStC, pc38, hD38, hRg38, hr11_38, hr13_38, _, hr15_38⟩ :=
          wbBodyC_steps subCode h32 input hkLt hMdLe hEaB.2.2 hQL hFit hBits pc31 hRg31
            hr13_31 hr14_31 hr15_31 hStPtr31 hEntPtr31 hTail31
        obtain ⟨s48, hStD, pc48, sz48, hRg48, hr13_48, hMem48⟩ :=
          wbBodyD_steps subCode h32 input hkLt hMdLe (by omega) hEmitFit hBits pc38 (by rw [hD38, sz31])
            hRg38 hr11_38 hr13_38 hr15_38
        have hStIter : Steps code input 47 s s48 :=
          ((hSt4.append hStA).append hStB).append (hStC.append hStD)
        refine Or.inr ⟨k + 1, s48, 47, by omega, by omega, hStIter,
          hkLt, pc48, sz48, hRg48, hr13_48, ?_, ?_⟩
        · intro j hj _hjMd
          by_cases hjk : j = k
          · subst hjk
            refine ⟨?_, ?_, ?_⟩
            · have hNe1 : emitBase + 3 * n + 1 + (qStartFn S d + j) ≠
                  emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + j) := by omega
              have hNe2 : emitBase + 3 * n + 1 + (qStartFn S d + j) ≠
                  emitBase + 3 * n + m + 1 + (qStartFn S d + j) := by omega
              rw [(hMem48 _).2 hNe1, hD38, (hMem31 _).2 hNe2, (hMem19 _).1 rfl]
            · have hNe1 : emitBase + 3 * n + m + 1 + (qStartFn S d + j) ≠
                  emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + j) := by omega
              rw [(hMem48 _).2 hNe1, hD38, (hMem31 _).1 rfl]
            · exact (hMem48 _).1 rfl
          · have hPrev := hWrtS j (by omega) _hjMd
            obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
              wb_slot_disjoint (emitBase := emitBase) (n := n) (m := m) (qd := qStartFn S d) hjk _hjMd hkLt hMdLe
            refine ⟨?_, ?_, ?_⟩
            · rw [(hMem48 _).2 h1, hD38, (hMem31 _).2 h2, (hMem19 _).2 h3, hD4]; exact hPrev.1
            · rw [(hMem48 _).2 h4, hD38, (hMem31 _).2 h5, (hMem19 _).2 h6, hD4]; exact hPrev.2.1
            · rw [(hMem48 _).2 h7, hD38, (hMem31 _).2 h8, (hMem19 _).2 h9, hD4]; exact hPrev.2.2
        · intro addr hNot
          have hNotUnf : ¬ ((emitBase + 3 * n + 1 + qStartFn S d ≤ addr ∧ addr < emitBase + 3 * n + 1 + (qStartFn S d + (k + 1))) ∨
              (emitBase + 3 * n + m + 1 + qStartFn S d ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + (qStartFn S d + (k + 1))) ∨
              (emitBase + 3 * n + 2 * m + 1 + qStartFn S d ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + (k + 1)))) :=
            hNot
          have h1 : ¬ wbIsWritten emitBase n m (qStartFn S d) k addr := fun hW => hNotUnf (by
            rcases hW with h | h | h
            · exact Or.inl ⟨h.1, Nat.lt_succ_of_lt h.2⟩
            · exact Or.inr (Or.inl ⟨h.1, Nat.lt_succ_of_lt h.2⟩)
            · exact Or.inr (Or.inr ⟨h.1, Nat.lt_succ_of_lt h.2⟩))
          have hNeT : addr ≠ emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + k) := fun e =>
            hNotUnf (Or.inr (Or.inr ⟨by rw [e]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _, by rw [e]; exact Nat.lt_succ_self _⟩))
          have hNeH : addr ≠ emitBase + 3 * n + m + 1 + (qStartFn S d + k) := fun e =>
            hNotUnf (Or.inr (Or.inl ⟨by rw [e]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _, by rw [e]; exact Nat.lt_succ_self _⟩))
          have hNeS : addr ≠ emitBase + 3 * n + 1 + (qStartFn S d + k) := fun e =>
            hNotUnf (Or.inl ⟨by rw [e]; exact Nat.add_le_add_left (Nat.le_add_right _ _) _, by rw [e]; exact Nat.lt_succ_self _⟩)
          rw [(hMem48 addr).2 hNeT, hD38, (hMem31 addr).2 hNeH, (hMem19 addr).2 hNeS, hD4]
          exact hOutS addr h1)
    m_d 0 s1 (by omega)
    ⟨Nat.zero_le _, pc1, by rw [d1, hDataSz], hRg1, hr13_1, fun j hj _ => by omega,
      fun addr _ => by rw [d1]⟩
  obtain ⟨_, t, kL, hkL, hStL, hPost⟩ := hLoop
  exact ⟨t, 1 + kL, by omega, hSt0.append hStL, hPost⟩

private theorem smallBranchA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hd : d < n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offSmall) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hPtrsPtr : (s₀.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m)) :
    ∃ s11, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 11 s₀ s11 ∧
      s11.pc = offSmall + 11 ∧ s11.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s11 ∧
      (reg s11 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 1 ∧
      (∀ addr, (addr = ownerForestPtrsBase loopBase n m + 6 * d → (s11.data[addr]?).map Fin.val = some 0) ∧
        (addr ≠ ownerForestPtrsBase loopBase n m + 6 * d → s11.data[addr]? = s₀.data[addr]?)) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 12 → offSmall + c < code.size := by intro c hc; rw [hSz]; unfold offSmall; omega
  have hZero : (reg s₀ rZero).val = 0 := hRegs.entry.consts.zero
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hdVal : (reg s₀ r9).val = d := hRegs.dVal
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hPtrsBnd : ownerForestPtrsBase loopBase n m + 6 * n ≤ workCap := by
    unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
      loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hNLt : 6 * n < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  obtain ⟨s1, st0, pc1, r12_1, keep1, d1⟩ :=
    step16_imm code input hpc (at_small subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hMemSt : s1.data[(reg s1 r12).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d1, show (reg s1 r12).val = statePtrAddr by rw [r12_1]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s2, st1, pc2, r11_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_small subCode h32 (i := 1) (by decide)) hMemSt (hPcLt 2 (by decide))
  obtain ⟨s3, st2, pc3, r12_3, keep3, d3⟩ :=
    step16_imm code input pc2 (at_small subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  obtain ⟨s4, st3, pc4, r11_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_small subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have hAddr4 : (reg s4 r11).val = loopSubStateBase loopBase n m + 14 := by
    rw [r11_4, add_no_wrap]
    · rw [keep3 _ (by decide), r11_2, r12_3]; rfl
    · rw [keep3 _ (by decide), r11_2, r12_3]; change loopSubStateBase loopBase n m + 14 < 2 ^ bits; omega
  have hMemPtrs : s4.data[(reg s4 r11).val]? = some ⟨ownerForestPtrsBase loopBase n m, by omega⟩ := by
    rw [hAddr4, d4, d3, d2, d1]; exact mem_word_of_map hPtrsPtr _
  obtain ⟨s5, st4, pc5, r11_5, keep5, d5⟩ :=
    step16_loadData code input pc4 (at_small subCode h32 (i := 4) (by decide)) hMemPtrs (hPcLt 5 (by decide))
  have hdeq5 : (reg s5 r9).val = d := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hdVal]
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_small subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = 2 * d := by rw [r12_6, add_no_wrap] <;> rw [hdeq5] <;> omega
  obtain ⟨s7, st6, pc7, r13_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_small subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have r13v7 : (reg s7 r13).val = 4 * d := by rw [r13_7, add_no_wrap] <;> rw [r12v6] <;> omega
  obtain ⟨s8, st7, pc8, r12_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_small subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r12v8 : (reg s8 r12).val = 6 * d := by
    rw [r12_8, add_no_wrap] <;> rw [keep7 _ (by decide), r12v6, r13v7] <;> omega
  obtain ⟨s9, st8, pc9, r11_9, keep9, d9⟩ :=
    step16_add code input pc8 (at_small subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
  have r11eq8 : (reg s8 r11).val = ownerForestPtrsBase loopBase n m := by
    rw [keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), r11_5]
  have r11v9 : (reg s9 r11).val = ownerForestPtrsBase loopBase n m + 6 * d := by
    rw [r11_9, add_no_wrap] <;> rw [r11eq8, r12v8] <;> omega
  have hZero9 : (reg s9 rZero).val = 0 := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide),
      keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hZero]
  have h1eq9 : (reg s9 rOne).val = 1 := by
    rw [keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide),
      keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hOne]
  have hData9 : s9.data = s₀.data := by rw [d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hBnd9 : (reg s9 r11).val < s9.data.size := by rw [r11v9, hData9, hDataSz]; omega
  obtain ⟨s10, st9, pc10, regs10, d10⟩ :=
    step16_storeData code input pc9 (at_small subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide)) hBnd9
  have reg10 : ∀ r : Fin 16, reg s10 r = reg s9 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs10 r
  obtain ⟨s11, st10, pc11, r11_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_small subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have r11v11 : (reg s11 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 1 := by
    rw [r11_11, add_no_wrap] <;> rw [reg10, reg10, r11v9, h1eq9] <;> omega
  have hSteps : Steps code input 11 s₀ s11 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4
      (Steps.cons st5 (Steps.cons st6 (Steps.cons st7 (Steps.cons st8 (Steps.cons st9
        (Steps.cons st10 (Steps.zero s11)))))))))))
  refine ⟨s11, hSteps, pc11, by rw [d11, d10, Array.size_set, hData9, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, r11v11, fun addr => ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    rw [keep11 _ h11, reg10, keep9 _ h11, keep8 _ h12, keep7 _ h13, keep6 _ h12, keep5 _ h11,
      keep4 _ h11, keep3 _ h12, keep2 _ h11, keep1 _ h12]
  · rw [d11, d10]
    refine ⟨fun hk => ?_, fun hne => ?_⟩
    · rw [mem_set_same s9.data (r11v9.trans hk.symm) hBnd9, Option.map_some, hZero9]
    · rw [mem_set_ne s9.data hBnd9 (fun e => hne (e.trans r11v9)), hData9]

private theorem smallBranchB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hd : d < n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s11 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s11.pc = offSmall + 11) (hDataSz : s11.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s11)
    (hr11 : (reg s11 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 1) :
    ∃ s22, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 11 s11 s22 ∧
      s22.pc = offHdr ∧ s22.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d + 1) forestUsed s22 ∧
      (∀ j, 1 ≤ j → j < 6 → (s22.data[ownerForestPtrsBase loopBase n m + 6 * d + j]?).map Fin.val = some 0) ∧
      (∀ addr, (addr < ownerForestPtrsBase loopBase n m + 6 * d + 1 ∨
        ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr) → s22.data[addr]? = s11.data[addr]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 23 → offSmall + c < code.size := by intro c hc; rw [hSz]; unfold offSmall; omega
  have hHdrLt : offHdr < code.size := by rw [hSz]; unfold offHdr; omega
  have hZero : (reg s11 rZero).val = 0 := hRegs.entry.consts.zero
  have hOne : (reg s11 rOne).val = 1 := hRegs.entry.consts.one
  have hdVal : (reg s11 r9).val = d := hRegs.dVal
  have hPtrsBnd : ownerForestPtrsBase loopBase n m + 6 * n ≤ workCap := by
    unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
      loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hBnd1 : (reg s11 r11).val < s11.data.size := by rw [hr11, hDataSz]; omega
  obtain ⟨s12, st11, pc12, regs12, d12⟩ :=
    step16_storeData code input hpc (at_small subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide)) hBnd1
  have reg12 : ∀ r : Fin 16, reg s12 r = reg s11 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs12 r
  obtain ⟨s13, st12, pc13, r11_13, keep13, d13⟩ :=
    step16_add code input pc12 (at_small subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
  have r11v13 : (reg s13 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 2 := by
    rw [r11_13, add_no_wrap] <;> rw [reg12, reg12, hr11, hOne] <;> omega
  have hBnd13 : (reg s13 r11).val < s13.data.size := by
    rw [r11v13, d13, d12, Array.size_set, hDataSz]; omega
  obtain ⟨s14, st13, pc14, regs14, d14⟩ :=
    step16_storeData code input pc13 (at_small subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide)) hBnd13
  have reg14 : ∀ r : Fin 16, reg s14 r = reg s13 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs14 r
  obtain ⟨s15, st14, pc15, r11_15, keep15, d15⟩ :=
    step16_add code input pc14 (at_small subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have r11v15 : (reg s15 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 3 := by
    rw [r11_15, add_no_wrap] <;> rw [reg14, reg14, r11v13, keep13 _ (by decide), reg12, hOne] <;> omega
  have hBnd15 : (reg s15 r11).val < s15.data.size := by
    rw [r11v15, d15, d14, Array.size_set, d13, d12, Array.size_set, hDataSz]; omega
  obtain ⟨s16, st15, pc16, regs16, d16⟩ :=
    step16_storeData code input pc15 (at_small subCode h32 (i := 15) (by decide)) (hPcLt 16 (by decide)) hBnd15
  have reg16 : ∀ r : Fin 16, reg s16 r = reg s15 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs16 r
  obtain ⟨s17, st16, pc17, r11_17, keep17, d17⟩ :=
    step16_add code input pc16 (at_small subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have r11v17 : (reg s17 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 4 := by
    rw [r11_17, add_no_wrap] <;> rw [reg16, reg16, r11v15, keep15 _ (by decide), reg14, keep13 _ (by decide),
      reg12, hOne] <;> omega
  have hBnd17 : (reg s17 r11).val < s17.data.size := by
    rw [r11v17, d17, d16, Array.size_set, d15, d14, Array.size_set, d13, d12, Array.size_set, hDataSz]; omega
  obtain ⟨s18, st17, pc18, regs18, d18⟩ :=
    step16_storeData code input pc17 (at_small subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide)) hBnd17
  have reg18 : ∀ r : Fin 16, reg s18 r = reg s17 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs18 r
  obtain ⟨s19, st18, pc19, r11_19, keep19, d19⟩ :=
    step16_add code input pc18 (at_small subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  have r11v19 : (reg s19 r11).val = ownerForestPtrsBase loopBase n m + 6 * d + 5 := by
    rw [r11_19, add_no_wrap] <;> rw [reg18, reg18, r11v17, keep17 _ (by decide), reg16, keep15 _ (by decide),
      reg14, keep13 _ (by decide), reg12, hOne] <;> omega
  have hBnd19 : (reg s19 r11).val < s19.data.size := by
    rw [r11v19, d19, d18, Array.size_set, d17, d16, Array.size_set, d15, d14, Array.size_set,
      d13, d12, Array.size_set, hDataSz]; omega
  obtain ⟨s20, st19, pc20, regs20, d20⟩ :=
    step16_storeData code input pc19 (at_small subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide)) hBnd19
  have reg20 : ∀ r : Fin 16, reg s20 r = reg s19 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs20 r
  obtain ⟨s21, st20, pc21, r9_21, keep21, d21⟩ :=
    step16_add code input pc20 (at_small subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide))
  have h1eq20 : (reg s20 rOne).val = 1 := by
    rw [reg20, keep19 _ (by decide), reg18, keep17 _ (by decide), reg16, keep15 _ (by decide),
      reg14, keep13 _ (by decide), reg12, hOne]
  have hdeq20 : (reg s20 r9).val = d := by
    rw [reg20, keep19 _ (by decide), reg18, keep17 _ (by decide), reg16, keep15 _ (by decide),
      reg14, keep13 _ (by decide), reg12, hdVal]
  have r9v21 : (reg s21 r9).val = d + 1 := by
    rw [r9_21, add_no_wrap] <;> rw [hdeq20, h1eq20] <;> omega
  have st21 := step16_goto code input pc21 (at_small subCode h32 (i := 21) (by decide)) hHdrLt
  let s22 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s21.regs, data := s21.data, pc := offHdr,
      regs_size := s21.regs_size, data_size := s21.data_size }
  have hSteps : Steps code input 11 s11 s22 :=
    Steps.cons st11 (Steps.cons st12 (Steps.cons st13 (Steps.cons st14 (Steps.cons st15
      (Steps.cons st16 (Steps.cons st17 (Steps.cons st18 (Steps.cons st19 (Steps.cons st20
        (Steps.cons st21 (Steps.zero s22)))))))))))
  have hZero19 : (reg s19 rZero).val = 0 := by
    rw [keep19 _ (by decide), reg18, keep17 _ (by decide), reg16, keep15 _ (by decide),
      reg14, keep13 _ (by decide), reg12, hZero]
  have hZero17 : (reg s17 rZero).val = 0 := by
    rw [keep17 _ (by decide), reg16, keep15 _ (by decide), reg14, keep13 _ (by decide), reg12, hZero]
  have hZero15 : (reg s15 rZero).val = 0 := by
    rw [keep15 _ (by decide), reg14, keep13 _ (by decide), reg12, hZero]
  have hZero13 : (reg s13 rZero).val = 0 := by rw [keep13 _ (by decide), reg12, hZero]
  have hZero11 : (reg s11 rZero).val = 0 := hZero
  have hData22 : ∀ addr,
      (if addr = ownerForestPtrsBase loopBase n m + 6 * d + 5 then some ⟨0, by omega⟩
      else if addr = ownerForestPtrsBase loopBase n m + 6 * d + 4 then some ⟨0, by omega⟩
      else if addr = ownerForestPtrsBase loopBase n m + 6 * d + 3 then some ⟨0, by omega⟩
      else if addr = ownerForestPtrsBase loopBase n m + 6 * d + 2 then some ⟨0, by omega⟩
      else if addr = ownerForestPtrsBase loopBase n m + 6 * d + 1 then some ⟨0, by omega⟩
      else s11.data[addr]?) = s22.data[addr]? := by
    intro addr
    change _ = s21.data[addr]?
    rw [d21, d20]
    by_cases h5 : addr = ownerForestPtrsBase loopBase n m + 6 * d + 5
    · subst h5; rw [ite_eq_left rfl, mem_set_same s19.data r11v19 hBnd19]; exact congrArg some (Fin.ext hZero19.symm)
    · rw [ite_eq_right h5, mem_set_ne s19.data hBnd19 (fun e => h5 (e.trans r11v19)), d19, d18]
      by_cases h4 : addr = ownerForestPtrsBase loopBase n m + 6 * d + 4
      · subst h4; rw [ite_eq_left rfl, mem_set_same s17.data r11v17 hBnd17]; exact congrArg some (Fin.ext hZero17.symm)
      · rw [ite_eq_right h4, mem_set_ne s17.data hBnd17 (fun e => h4 (e.trans r11v17)), d17, d16]
        by_cases h3 : addr = ownerForestPtrsBase loopBase n m + 6 * d + 3
        · subst h3; rw [ite_eq_left rfl, mem_set_same s15.data r11v15 hBnd15]; exact congrArg some (Fin.ext hZero15.symm)
        · rw [ite_eq_right h3, mem_set_ne s15.data hBnd15 (fun e => h3 (e.trans r11v15)), d15, d14]
          by_cases h2 : addr = ownerForestPtrsBase loopBase n m + 6 * d + 2
          · subst h2; rw [ite_eq_left rfl, mem_set_same s13.data r11v13 hBnd13]; exact congrArg some (Fin.ext hZero13.symm)
          · rw [ite_eq_right h2, mem_set_ne s13.data hBnd13 (fun e => h2 (e.trans r11v13)), d13, d12]
            by_cases h1 : addr = ownerForestPtrsBase loopBase n m + 6 * d + 1
            · subst h1; rw [ite_eq_left rfl, mem_set_same s11.data hr11 hBnd1]; exact congrArg some (Fin.ext hZero11.symm)
            · rw [ite_eq_right h1, mem_set_ne s11.data hBnd1 (fun e => h1 (e.trans hr11))]
  refine ⟨s22, hSteps, rfl, ?_, ?_, ?_, ?_⟩
  · change s21.data.size = _
    rw [d21, d20, Array.size_set, d19, d18, Array.size_set, d17, d16, Array.size_set,
      d15, d14, Array.size_set, d13, d12, Array.size_set, hDataSz]
  · refine { entry := loopEntryRegs_of_keep hRegs.entry fun r hr => ?_, dVal := r9v21, usedVal := ?_ }
    · have hne9 : r ≠ r9 := fun e => absurd hr (by subst e; decide)
      have hne11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
      change reg s21 r = reg s11 r
      rw [keep21 _ hne9, reg20, keep19 _ hne11, reg18, keep17 _ hne11, reg16, keep15 _ hne11,
        reg14, keep13 _ hne11, reg12]
    · change (reg s21 r10).val = _
      rw [keep21 _ (by decide), reg20, keep19 _ (by decide), reg18, keep17 _ (by decide),
        reg16, keep15 _ (by decide), reg14, keep13 _ (by decide), reg12]; exact hRegs.usedVal
  · intro j hj1 hj6
    rw [← hData22 (ownerForestPtrsBase loopBase n m + 6 * d + j)]
    have hjCases : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
    rcases hjCases with rfl | rfl | rfl | rfl | rfl <;>
      simp [Option.map_some]
  · intro addr ha
    rw [← hData22 addr]
    rcases ha with hl | hr <;>
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem smallBranch_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hd : d < n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offSmall) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hPtrsPtr : (s₀.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m)) :
    ∃ s22, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 22 s₀ s22 ∧
      s22.pc = offHdr ∧ s22.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d + 1) forestUsed s22 ∧
      (∀ j < 6, (s22.data[ownerForestPtrsBase loopBase n m + 6 * d + j]?).map Fin.val = some 0) ∧
      (∀ addr, (addr < ownerForestPtrsBase loopBase n m + 6 * d ∨
        ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr) → s22.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨s11, hStA, pc11, sz11, hRg11, hr11, hMem11⟩ :=
    smallBranchA_steps subCode h32 input hd hFit hBits hpc hDataSz hRegs hStPtr hPtrsPtr
  obtain ⟨s22, hStB, pc22, sz22, hRg22, hZerosB, hMem22⟩ :=
    smallBranchB_steps subCode h32 input hd hFit hBits pc11 sz11 hRg11 hr11
  refine ⟨s22, hStA.append hStB, pc22, sz22, hRg22, ?_, ?_⟩
  · intro j hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [hMem22 _ (Or.inl (by omega))]
      exact (hMem11 _).1 (Nat.add_zero _)
    · exact hZerosB j (by omega) hj
  · intro addr ha
    have hB : addr < ownerForestPtrsBase loopBase n m + 6 * d + 1 ∨
        ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr := by omega
    have hA : addr ≠ ownerForestPtrsBase loopBase n m + 6 * d := by omega
    rw [hMem22 addr hB, (hMem11 addr).2 hA]

private theorem saveRegsA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offLarge) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m)) :
    ∃ s12, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 12 s₀ s12 ∧
      s12.pc = offLarge + 12 ∧ s12.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s12 ∧
      (reg s12 r12).val = loopSubStateBase loopBase n m + 5 ∧
      (∀ r : Fin 16, r.val ≤ 10 → reg s12 r = reg s₀ r) ∧
      (∀ r : Fin 16, r.val ≤ 4 → s12.data[loopSubStateBase loopBase n m + r.val]? = some (reg s₀ r)) ∧
      (∀ addr, (addr < loopSubStateBase loopBase n m ∨ loopSubStateBase loopBase n m + 5 ≤ addr) →
        s12.data[addr]? = s₀.data[addr]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 13 → offLarge + c < code.size := by intro c hc; rw [hSz]; unfold offLarge; omega
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hStLt : loopSubStateBase loopBase n m + 16 < 2 ^ bits := by omega
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_imm code input hpc (at_save subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hMemSt : s1.data[(reg s1 r11).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d1, show (reg s1 r11).val = statePtrAddr by rw [r11_1]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_save subCode h32 (i := 1) (by decide)) hMemSt (hPcLt 2 (by decide))
  have hBnd2 : (reg s2 r12).val < s2.data.size := by rw [r12_2, d2, d1, hDataSz]; dsimp only; omega
  obtain ⟨s3, st2, pc3, regs3, d3⟩ :=
    step16_storeData code input pc2 (at_save subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide)) hBnd2
  have reg3 : ∀ r : Fin 16, reg s3 r = reg s2 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs3 r
  have h1eq2 : (reg s2 r1).val = 1 := by rw [keep2 _ (by decide), keep1 _ (by decide)]; exact hOne
  have h1eq3 : (reg s3 rOne).val = 1 := by rw [reg3]; exact h1eq2
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_save subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have r12v4 : (reg s4 r12).val = loopSubStateBase loopBase n m + 1 := by
    rw [r12_4, add_no_wrap] <;> rw [reg3, reg3, r12_2, h1eq2] <;> dsimp only <;> omega
  have hBnd4 : (reg s4 r12).val < s4.data.size := by rw [r12v4, d4, d3, Array.size_set, d2, d1, hDataSz]; omega
  obtain ⟨s5, st4, pc5, regs5, d5⟩ :=
    step16_storeData code input pc4 (at_save subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide)) hBnd4
  have reg5 : ∀ r : Fin 16, reg s5 r = reg s4 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs5 r
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_save subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = loopSubStateBase loopBase n m + 2 := by
    rw [r12_6, add_no_wrap] <;> rw [reg5, reg5, r12v4, keep4 _ (by decide), h1eq3] <;> omega
  have hBnd6 : (reg s6 r12).val < s6.data.size := by
    rw [r12v6, d6, d5, Array.size_set, d4, d3, Array.size_set, d2, d1, hDataSz]; omega
  obtain ⟨s7, st6, pc7, regs7, d7⟩ :=
    step16_storeData code input pc6 (at_save subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide)) hBnd6
  have reg7 : ∀ r : Fin 16, reg s7 r = reg s6 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs7 r
  obtain ⟨s8, st7, pc8, r12_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_save subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r12v8 : (reg s8 r12).val = loopSubStateBase loopBase n m + 3 := by
    rw [r12_8, add_no_wrap] <;> rw [reg7, reg7, r12v6, keep6 _ (by decide), reg5, keep4 _ (by decide), h1eq3] <;> omega
  have hBnd8 : (reg s8 r12).val < s8.data.size := by
    rw [r12v8, d8, d7, Array.size_set, d6, d5, Array.size_set, d4, d3, Array.size_set, d2, d1, hDataSz]; omega
  obtain ⟨s9, st8, pc9, regs9, d9⟩ :=
    step16_storeData code input pc8 (at_save subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide)) hBnd8
  have reg9 : ∀ r : Fin 16, reg s9 r = reg s8 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs9 r
  obtain ⟨s10, st9, pc10, r12_10, keep10, d10⟩ :=
    step16_add code input pc9 (at_save subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  have r12v10 : (reg s10 r12).val = loopSubStateBase loopBase n m + 4 := by
    rw [r12_10, add_no_wrap] <;> rw [reg9, reg9, r12v8, keep8 _ (by decide), reg7, keep6 _ (by decide),
      reg5, keep4 _ (by decide), h1eq3] <;> omega
  have hBnd10 : (reg s10 r12).val < s10.data.size := by
    rw [r12v10, d10, d9, Array.size_set, d8, d7, Array.size_set, d6, d5, Array.size_set,
      d4, d3, Array.size_set, d2, d1, hDataSz]; omega
  obtain ⟨s11, st10, pc11, regs11, d11⟩ :=
    step16_storeData code input pc10 (at_save subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide)) hBnd10
  have reg11 : ∀ r : Fin 16, reg s11 r = reg s10 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs11 r
  obtain ⟨s12, st11, pc12, r12_12, keep12, d12⟩ :=
    step16_add code input pc11 (at_save subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
  have r12v12 : (reg s12 r12).val = loopSubStateBase loopBase n m + 5 := by
    rw [r12_12, add_no_wrap] <;> rw [reg11, reg11, r12v10, keep10 _ (by decide), reg9, keep8 _ (by decide),
      reg7, keep6 _ (by decide), reg5, keep4 _ (by decide), h1eq3] <;> omega
  have hKeepS0 : ∀ r : Fin 16, r.val ≤ 10 → reg s10 r = reg s₀ r := fun r hr => by
    have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    rw [keep10 _ h12, reg9, keep8 _ h12, reg7, keep6 _ h12, reg5, keep4 _ h12, reg3, keep2 _ h12, keep1 _ h11]
  have hSteps : Steps code input 12 s₀ s12 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4 (Steps.cons st5
      (Steps.cons st6 (Steps.cons st7 (Steps.cons st8 (Steps.cons st9 (Steps.cons st10
        (Steps.cons st11 (Steps.zero s12))))))))))))
  have hDataAt : ∀ addr,
      (if addr = loopSubStateBase loopBase n m + 4 then some (reg s₀ r4)
      else if addr = loopSubStateBase loopBase n m + 3 then some (reg s₀ r3)
      else if addr = loopSubStateBase loopBase n m + 2 then some (reg s₀ r2)
      else if addr = loopSubStateBase loopBase n m + 1 then some (reg s₀ r1)
      else if addr = loopSubStateBase loopBase n m then some (reg s₀ r0)
      else s₀.data[addr]?) = s12.data[addr]? := by
    intro addr; rw [d12, d11]
    by_cases h4 : addr = loopSubStateBase loopBase n m + 4
    · subst h4; rw [ite_eq_left rfl, mem_set_same s10.data r12v10 hBnd10, hKeepS0 r4 (by decide)]
    · rw [ite_eq_right h4, mem_set_ne s10.data hBnd10 (fun e => h4 (e.trans r12v10)), d10, d9]
      by_cases h3 : addr = loopSubStateBase loopBase n m + 3
      · subst h3; rw [ite_eq_left rfl, mem_set_same s8.data r12v8 hBnd8]
        exact congrArg some (by rw [keep8 _ (by decide), reg7, keep6 _ (by decide), reg5,
          keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide)])
      · rw [ite_eq_right h3, mem_set_ne s8.data hBnd8 (fun e => h3 (e.trans r12v8)), d8, d7]
        by_cases h2 : addr = loopSubStateBase loopBase n m + 2
        · subst h2; rw [ite_eq_left rfl, mem_set_same s6.data r12v6 hBnd6]
          exact congrArg some (by rw [keep6 _ (by decide), reg5, keep4 _ (by decide), reg3,
            keep2 _ (by decide), keep1 _ (by decide)])
        · rw [ite_eq_right h2, mem_set_ne s6.data hBnd6 (fun e => h2 (e.trans r12v6)), d6, d5]
          by_cases h1 : addr = loopSubStateBase loopBase n m + 1
          · subst h1; rw [ite_eq_left rfl, mem_set_same s4.data r12v4 hBnd4]
            exact congrArg some (by rw [keep4 _ (by decide), reg3, keep2 _ (by decide), keep1 _ (by decide)])
          · rw [ite_eq_right h1, mem_set_ne s4.data hBnd4 (fun e => h1 (e.trans r12v4)), d4, d3]
            by_cases h0 : addr = loopSubStateBase loopBase n m
            · subst h0; rw [ite_eq_left rfl, mem_set_same s2.data (congrArg Fin.val r12_2) hBnd2]
              exact congrArg some (by rw [keep2 _ (by decide), keep1 _ (by decide)])
            · rw [ite_eq_right h0, mem_set_ne s2.data hBnd2 (fun e => h0 (e.trans (congrArg Fin.val r12_2))), d2, d1]
  refine ⟨s12, hSteps, pc12,
    by rw [d12, d11, Array.size_set, d10, d9, Array.size_set, d8, d7, Array.size_set,
      d6, d5, Array.size_set, d4, d3, Array.size_set, d2, d1, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => by
      have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
      rw [keep12 _ h12, reg11, hKeepS0 r (by omega)],
    r12v12, fun r hr => by
      have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
      rw [keep12 _ h12, reg11, hKeepS0 r hr], ?_, ?_⟩
  · intro r hr
    rcases (by omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4) with h | h | h | h | h
    · have hF : r = r0 := Fin.ext h
      rw [show r.val = 0 from h, ← hDataAt (loopSubStateBase loopBase n m + 0), Nat.add_zero,
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r1 := Fin.ext h
      rw [show r.val = 1 from h, ← hDataAt (loopSubStateBase loopBase n m + 1),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r2 := Fin.ext h
      rw [show r.val = 2 from h, ← hDataAt (loopSubStateBase loopBase n m + 2),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r3 := Fin.ext h
      rw [show r.val = 3 from h, ← hDataAt (loopSubStateBase loopBase n m + 3),
        ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r4 := Fin.ext h
      rw [show r.val = 4 from h, ← hDataAt (loopSubStateBase loopBase n m + 4), ite_eq_left rfl]
      subst hF; rfl
  · intro addr ha
    rw [← hDataAt addr]
    rcases ha with hl | hr <;>
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem saveRegsB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s12 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s12.pc = offLarge + 12) (hDataSz : s12.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s12)
    (hr12 : (reg s12 r12).val = loopSubStateBase loopBase n m + 5) :
    ∃ s23, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 11 s12 s23 ∧
      s23.pc = offRaw ∧ s23.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s23 ∧
      (∀ r : Fin 16, 5 ≤ r.val → r.val ≤ 10 →
        s23.data[loopSubStateBase loopBase n m + r.val]? = some (reg s12 r)) ∧
      (∀ addr, (addr < loopSubStateBase loopBase n m + 5 ∨ loopSubStateBase loopBase n m + 11 ≤ addr) →
        s23.data[addr]? = s12.data[addr]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 24 → offLarge + c < code.size := by intro c hc; rw [hSz]; unfold offLarge; omega
  have hOne : (reg s12 rOne).val = 1 := hRegs.entry.consts.one
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hBnd12 : (reg s12 r12).val < s12.data.size := by rw [hr12, hDataSz]; omega
  obtain ⟨s13, st12, pc13, regs13, d13⟩ :=
    step16_storeData code input hpc (at_save subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide)) hBnd12
  have reg13 : ∀ r : Fin 16, reg s13 r = reg s12 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs13 r
  obtain ⟨s14, st13, pc14, r12_14, keep14, d14⟩ :=
    step16_add code input pc13 (at_save subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have r12v14 : (reg s14 r12).val = loopSubStateBase loopBase n m + 6 := by
    rw [r12_14, add_no_wrap] <;> rw [reg13, reg13, hr12, hOne] <;> omega
  have hBnd14 : (reg s14 r12).val < s14.data.size := by rw [r12v14, d14, d13, Array.size_set, hDataSz]; omega
  obtain ⟨s15, st14, pc15, regs15, d15⟩ :=
    step16_storeData code input pc14 (at_save subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide)) hBnd14
  have reg15 : ∀ r : Fin 16, reg s15 r = reg s14 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs15 r
  obtain ⟨s16, st15, pc16, r12_16, keep16, d16⟩ :=
    step16_add code input pc15 (at_save subCode h32 (i := 15) (by decide)) (hPcLt 16 (by decide))
  have r12v16 : (reg s16 r12).val = loopSubStateBase loopBase n m + 7 := by
    rw [r12_16, add_no_wrap] <;> rw [reg15, reg15, r12v14, keep14 _ (by decide), reg13, hOne] <;> omega
  have hBnd16 : (reg s16 r12).val < s16.data.size := by
    rw [r12v16, d16, d15, Array.size_set, d14, d13, Array.size_set, hDataSz]; omega
  obtain ⟨s17, st16, pc17, regs17, d17⟩ :=
    step16_storeData code input pc16 (at_save subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide)) hBnd16
  have reg17 : ∀ r : Fin 16, reg s17 r = reg s16 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs17 r
  obtain ⟨s18, st17, pc18, r12_18, keep18, d18⟩ :=
    step16_add code input pc17 (at_save subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide))
  have r12v18 : (reg s18 r12).val = loopSubStateBase loopBase n m + 8 := by
    rw [r12_18, add_no_wrap] <;> rw [reg17, reg17, r12v16, keep16 _ (by decide), reg15, keep14 _ (by decide),
      reg13, hOne] <;> omega
  have hBnd18 : (reg s18 r12).val < s18.data.size := by
    rw [r12v18, d18, d17, Array.size_set, d16, d15, Array.size_set, d14, d13, Array.size_set, hDataSz]; omega
  obtain ⟨s19, st18, pc19, regs19, d19⟩ :=
    step16_storeData code input pc18 (at_save subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide)) hBnd18
  have reg19 : ∀ r : Fin 16, reg s19 r = reg s18 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs19 r
  obtain ⟨s20, st19, pc20, r12_20, keep20, d20⟩ :=
    step16_add code input pc19 (at_save subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  have r12v20 : (reg s20 r12).val = loopSubStateBase loopBase n m + 9 := by
    rw [r12_20, add_no_wrap] <;> rw [reg19, reg19, r12v18, keep18 _ (by decide), reg17, keep16 _ (by decide),
      reg15, keep14 _ (by decide), reg13, hOne] <;> omega
  have hBnd20 : (reg s20 r12).val < s20.data.size := by
    rw [r12v20, d20, d19, Array.size_set, d18, d17, Array.size_set, d16, d15, Array.size_set,
      d14, d13, Array.size_set, hDataSz]; omega
  obtain ⟨s21, st20, pc21, regs21, d21⟩ :=
    step16_storeData code input pc20 (at_save subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide)) hBnd20
  have reg21 : ∀ r : Fin 16, reg s21 r = reg s20 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs21 r
  obtain ⟨s22, st21, pc22, r12_22, keep22, d22⟩ :=
    step16_add code input pc21 (at_save subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
  have r12v22 : (reg s22 r12).val = loopSubStateBase loopBase n m + 10 := by
    rw [r12_22, add_no_wrap] <;> rw [reg21, reg21, r12v20, keep20 _ (by decide), reg19, keep18 _ (by decide),
      reg17, keep16 _ (by decide), reg15, keep14 _ (by decide), reg13, hOne] <;> omega
  have hBnd22 : (reg s22 r12).val < s22.data.size := by
    rw [r12v22, d22, d21, Array.size_set, d20, d19, Array.size_set, d18, d17, Array.size_set,
      d16, d15, Array.size_set, d14, d13, Array.size_set, hDataSz]; omega
  obtain ⟨s23, st22, pc23, regs23, d23⟩ :=
    step16_storeData code input pc22 (at_save subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide)) hBnd22
  have reg23 : ∀ r : Fin 16, reg s23 r = reg s22 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs23 r
  have hSteps : Steps code input 11 s12 s23 :=
    Steps.cons st12 (Steps.cons st13 (Steps.cons st14 (Steps.cons st15 (Steps.cons st16
      (Steps.cons st17 (Steps.cons st18 (Steps.cons st19 (Steps.cons st20 (Steps.cons st21
        (Steps.cons st22 (Steps.zero s23)))))))))))
  have hDataAt : ∀ addr,
      (if addr = loopSubStateBase loopBase n m + 10 then some (reg s12 r10)
      else if addr = loopSubStateBase loopBase n m + 9 then some (reg s12 r9)
      else if addr = loopSubStateBase loopBase n m + 8 then some (reg s12 r8)
      else if addr = loopSubStateBase loopBase n m + 7 then some (reg s12 r7)
      else if addr = loopSubStateBase loopBase n m + 6 then some (reg s12 r6)
      else if addr = loopSubStateBase loopBase n m + 5 then some (reg s12 r5)
      else s12.data[addr]?) = s23.data[addr]? := by
    intro addr; rw [d23]
    by_cases h10 : addr = loopSubStateBase loopBase n m + 10
    · subst h10; rw [ite_eq_left rfl, mem_set_same s22.data r12v22 hBnd22]
      exact congrArg some (by rw [keep22 _ (by decide), reg21, keep20 _ (by decide), reg19,
        keep18 _ (by decide), reg17, keep16 _ (by decide), reg15, keep14 _ (by decide), reg13])
    · rw [ite_eq_right h10, mem_set_ne s22.data hBnd22 (fun e => h10 (e.trans r12v22)), d22, d21]
      by_cases h9 : addr = loopSubStateBase loopBase n m + 9
      · subst h9; rw [ite_eq_left rfl, mem_set_same s20.data r12v20 hBnd20]
        exact congrArg some (by rw [keep20 _ (by decide), reg19, keep18 _ (by decide), reg17,
          keep16 _ (by decide), reg15, keep14 _ (by decide), reg13])
      · rw [ite_eq_right h9, mem_set_ne s20.data hBnd20 (fun e => h9 (e.trans r12v20)), d20, d19]
        by_cases h8 : addr = loopSubStateBase loopBase n m + 8
        · subst h8; rw [ite_eq_left rfl, mem_set_same s18.data r12v18 hBnd18]
          exact congrArg some (by rw [keep18 _ (by decide), reg17, keep16 _ (by decide), reg15,
            keep14 _ (by decide), reg13])
        · rw [ite_eq_right h8, mem_set_ne s18.data hBnd18 (fun e => h8 (e.trans r12v18)), d18, d17]
          by_cases h7 : addr = loopSubStateBase loopBase n m + 7
          · subst h7; rw [ite_eq_left rfl, mem_set_same s16.data r12v16 hBnd16]
            exact congrArg some (by rw [keep16 _ (by decide), reg15, keep14 _ (by decide), reg13])
          · rw [ite_eq_right h7, mem_set_ne s16.data hBnd16 (fun e => h7 (e.trans r12v16)), d16, d15]
            by_cases h6 : addr = loopSubStateBase loopBase n m + 6
            · subst h6; rw [ite_eq_left rfl, mem_set_same s14.data r12v14 hBnd14]
              exact congrArg some (by rw [keep14 _ (by decide), reg13])
            · rw [ite_eq_right h6, mem_set_ne s14.data hBnd14 (fun e => h6 (e.trans r12v14)), d14, d13]
              by_cases h5 : addr = loopSubStateBase loopBase n m + 5
              · subst h5; rw [ite_eq_left rfl, mem_set_same s12.data hr12 hBnd12]
              · rw [ite_eq_right h5, mem_set_ne s12.data hBnd12 (fun e => h5 (e.trans hr12))]
  refine ⟨s23, hSteps, by rw [pc23]; unfold offLarge offRaw; omega,
    by rw [d23, Array.size_set, d22, d21, Array.size_set, d20, d19, Array.size_set,
      d18, d17, Array.size_set, d16, d15, Array.size_set, d14, d13, Array.size_set, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => by
      have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
      rw [reg23, keep22 _ h12, reg21, keep20 _ h12, reg19, keep18 _ h12, reg17,
        keep16 _ h12, reg15, keep14 _ h12, reg13],
    ?_, ?_⟩
  · intro r hr5 hr10
    rcases (by omega : r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10)
      with h | h | h | h | h | h
    · have hF : r = r5 := Fin.ext h
      rw [show r.val = 5 from h, ← hDataAt (loopSubStateBase loopBase n m + 5),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r6 := Fin.ext h
      rw [show r.val = 6 from h, ← hDataAt (loopSubStateBase loopBase n m + 6),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r7 := Fin.ext h
      rw [show r.val = 7 from h, ← hDataAt (loopSubStateBase loopBase n m + 7),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r8 := Fin.ext h
      rw [show r.val = 8 from h, ← hDataAt (loopSubStateBase loopBase n m + 8),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r9 := Fin.ext h
      rw [show r.val = 9 from h, ← hDataAt (loopSubStateBase loopBase n m + 9),
        ite_eq_right (by omega), ite_eq_left rfl]
      subst hF; rfl
    · have hF : r = r10 := Fin.ext h
      rw [show r.val = 10 from h, ← hDataAt (loopSubStateBase loopBase n m + 10), ite_eq_left rfl]
      subst hF; rfl
  · intro addr ha
    rw [← hDataAt addr]
    rcases ha with hl | hr <;>
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

private theorem saveRegs_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offLarge) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m)) :
    ∃ s23, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 23 s₀ s23 ∧
      s23.pc = offRaw ∧ s23.data.size = workCap ∧
      (∀ r : Fin 16, r.val ≤ 10 → s23.data[loopSubStateBase loopBase n m + r.val]? = some (reg s₀ r)) ∧
      (∀ addr, (addr < loopSubStateBase loopBase n m ∨ loopSubStateBase loopBase n m + 11 ≤ addr) →
        s23.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨s12, hStA, pc12, sz12, hRg12, hr12, hKeepA, hSaveA, hOutA⟩ :=
    saveRegsA_steps subCode h32 input hFit hBits hpc hDataSz hRegs hStPtr
  obtain ⟨s23, hStB, pc23, sz23, _, hSaveB, hOutB⟩ :=
    saveRegsB_steps subCode h32 input hFit hBits pc12 sz12 hRg12 hr12
  refine ⟨s23, hStA.append hStB, pc23, sz23, ?_, ?_⟩
  · intro r hr
    by_cases hr5 : r.val ≤ 4
    · rw [hOutB _ (Or.inl (by omega))]; exact hSaveA r hr5
    · rw [hSaveB r (by omega) hr, hKeepA r hr]
  · intro addr ha
    rw [hOutB addr (by omega), hOutA addr (by omega)]

private theorem restoreRegsA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m loopBase : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offPost subCode.size)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hSaved : ∀ r : Fin 16, r.val ≤ 10 → ∃ w, s₀.data[loopSubStateBase loopBase n m + r.val]? = some w) :
    ∃ s13, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 13 s₀ s13 ∧
      s13.pc = offPost subCode.size + 13 ∧ s13.data = s₀.data ∧
      (reg s13 r12).val = loopSubStateBase loopBase n m + 5 ∧
      (reg s13 r13).val = 1 ∧
      (∀ r : Fin 16, r.val ≤ 4 → some (reg s13 r) = s₀.data[loopSubStateBase loopBase n m + r.val]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 14 → offPost subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offPost; omega
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  obtain ⟨w0, hw0⟩ := hSaved r0 (by decide)
  obtain ⟨w1, hw1⟩ := hSaved r1 (by decide)
  obtain ⟨w2, hw2⟩ := hSaved r2 (by decide)
  obtain ⟨w3, hw3⟩ := hSaved r3 (by decide)
  obtain ⟨w4, hw4⟩ := hSaved r4 (by decide)
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_imm code input hpc (at_restore subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hMemSt : s1.data[(reg s1 r11).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d1, show (reg s1 r11).val = statePtrAddr by rw [r11_1]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_restore subCode h32 (i := 1) (by decide)) hMemSt (hPcLt 2 (by decide))
  obtain ⟨s3, st2, pc3, r13_3, keep3, d3⟩ :=
    step16_imm code input pc2 (at_restore subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  have r12eq3 : (reg s3 r12).val = loopSubStateBase loopBase n m := by
    rw [keep3 _ (by decide), r12_2]
  have h1eq3 : (reg s3 r13).val = 1 := by rw [r13_3]; rfl
  obtain ⟨s4, st3, pc4, r0_4, keep4, d4⟩ :=
    step16_loadData code input pc3 (at_restore subCode h32 (i := 3) (by decide))
      (by rw [r12eq3, d3, d2, d1]; exact hw0) (hPcLt 4 (by decide))
  obtain ⟨s5, st4, pc5, r12_5, keep5, d5⟩ :=
    step16_add code input pc4 (at_restore subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have r12v5 : (reg s5 r12).val = loopSubStateBase loopBase n m + 1 := by
    rw [r12_5, add_no_wrap] <;> rw [keep4 _ (by decide), r12eq3, keep4 _ (by decide), h1eq3] <;> omega
  obtain ⟨s6, st5, pc6, r1_6, keep6, d6⟩ :=
    step16_loadData code input pc5 (at_restore subCode h32 (i := 5) (by decide))
      (by rw [r12v5, d5, d4, d3, d2, d1]; exact hw1) (hPcLt 6 (by decide))
  obtain ⟨s7, st6, pc7, r12_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_restore subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have r12v7 : (reg s7 r12).val = loopSubStateBase loopBase n m + 2 := by
    rw [r12_7, add_no_wrap] <;> rw [keep6 _ (by decide), r12v5, keep6 _ (by decide), keep5 _ (by decide),
      keep4 _ (by decide), h1eq3] <;> omega
  obtain ⟨s8, st7, pc8, r2_8, keep8, d8⟩ :=
    step16_loadData code input pc7 (at_restore subCode h32 (i := 7) (by decide))
      (by rw [r12v7, d7, d6, d5, d4, d3, d2, d1]; exact hw2) (hPcLt 8 (by decide))
  obtain ⟨s9, st8, pc9, r12_9, keep9, d9⟩ :=
    step16_add code input pc8 (at_restore subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
  have r12v9 : (reg s9 r12).val = loopSubStateBase loopBase n m + 3 := by
    rw [r12_9, add_no_wrap] <;> rw [keep8 _ (by decide), r12v7, keep8 _ (by decide), keep7 _ (by decide),
      keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), h1eq3] <;> omega
  obtain ⟨s10, st9, pc10, r3_10, keep10, d10⟩ :=
    step16_loadData code input pc9 (at_restore subCode h32 (i := 9) (by decide))
      (by rw [r12v9, d9, d8, d7, d6, d5, d4, d3, d2, d1]; exact hw3) (hPcLt 10 (by decide))
  obtain ⟨s11, st10, pc11, r12_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_restore subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have r12v11 : (reg s11 r12).val = loopSubStateBase loopBase n m + 4 := by
    rw [r12_11, add_no_wrap] <;> rw [keep10 _ (by decide), r12v9, keep10 _ (by decide), keep9 _ (by decide),
      keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      h1eq3] <;> omega
  obtain ⟨s12, st11, pc12, r4_12, keep12, d12⟩ :=
    step16_loadData code input pc11 (at_restore subCode h32 (i := 11) (by decide))
      (by rw [r12v11, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]; exact hw4) (hPcLt 12 (by decide))
  obtain ⟨s13, st12, pc13, r12_13, keep13, d13⟩ :=
    step16_add code input pc12 (at_restore subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
  have h1eq12 : (reg s12 r13).val = 1 := by
    rw [keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide), keep9 _ (by decide),
      keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), h1eq3]
  have r12v13 : (reg s13 r12).val = loopSubStateBase loopBase n m + 5 := by
    rw [r12_13, add_no_wrap] <;> rw [keep12 _ (by decide), r12v11, h1eq12] <;> omega
  have hSteps : Steps code input 13 s₀ s13 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4 (Steps.cons st5
      (Steps.cons st6 (Steps.cons st7 (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11
        (Steps.cons st12 (Steps.zero s13)))))))))))))
  refine ⟨s13, hSteps, pc13, by rw [d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1],
    r12v13, by rw [keep13 _ (by decide), h1eq12], fun r hr => ?_⟩
  rcases (by omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4) with h | h | h | h | h
  · have hF : r = r0 := Fin.ext h; subst hF
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide),
      r0_4, hw0]
  · have hF : r = r1 := Fin.ext h; subst hF
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), r1_6, hw1]
  · have hF : r = r2 := Fin.ext h; subst hF
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), r2_8, hw2]
  · have hF : r = r3 := Fin.ext h; subst hF
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), r3_10, hw3]
  · have hF : r = r4 := Fin.ext h; subst hF
    rw [keep13 _ (by decide), r4_12, hw4]

private theorem restoreRegsB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m loopBase : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s13 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s13.pc = offPost subCode.size + 13)
    (hr12 : (reg s13 r12).val = loopSubStateBase loopBase n m + 5)
    (hr13 : (reg s13 r13).val = 1)
    (hSaved : ∀ r : Fin 16, 5 ≤ r.val → r.val ≤ 10 →
      ∃ w, s13.data[loopSubStateBase loopBase n m + r.val]? = some w) :
    ∃ s24, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 11 s13 s24 ∧
      s24.pc = offMax subCode.size ∧ s24.data = s13.data ∧
      (∀ r : Fin 16, r.val ≤ 4 → reg s24 r = reg s13 r) ∧
      (∀ r : Fin 16, 5 ≤ r.val → r.val ≤ 10 →
        some (reg s24 r) = s13.data[loopSubStateBase loopBase n m + r.val]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 25 → offPost subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offPost; omega
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  obtain ⟨w5, hw5⟩ := hSaved r5 (by decide) (by decide)
  obtain ⟨w6, hw6⟩ := hSaved r6 (by decide) (by decide)
  obtain ⟨w7, hw7⟩ := hSaved r7 (by decide) (by decide)
  obtain ⟨w8, hw8⟩ := hSaved r8 (by decide) (by decide)
  obtain ⟨w9, hw9⟩ := hSaved r9 (by decide) (by decide)
  obtain ⟨w10, hw10⟩ := hSaved r10 (by decide) (by decide)
  obtain ⟨s14, st13, pc14, r5_14, keep14, d14⟩ :=
    step16_loadData code input hpc (at_restore subCode h32 (i := 13) (by decide)) (by rw [hr12]; exact hw5) (hPcLt 14 (by decide))
  obtain ⟨s15, st14, pc15, r12_15, keep15, d15⟩ :=
    step16_add code input pc14 (at_restore subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have r12v15 : (reg s15 r12).val = loopSubStateBase loopBase n m + 6 := by
    rw [r12_15, add_no_wrap] <;> rw [keep14 _ (by decide), hr12, keep14 _ (by decide), hr13] <;> omega
  obtain ⟨s16, st15, pc16, r6_16, keep16, d16⟩ :=
    step16_loadData code input pc15 (at_restore subCode h32 (i := 15) (by decide))
      (by rw [r12v15, d15, d14]; exact hw6) (hPcLt 16 (by decide))
  obtain ⟨s17, st16, pc17, r12_17, keep17, d17⟩ :=
    step16_add code input pc16 (at_restore subCode h32 (i := 16) (by decide)) (hPcLt 17 (by decide))
  have r12v17 : (reg s17 r12).val = loopSubStateBase loopBase n m + 7 := by
    rw [r12_17, add_no_wrap] <;> rw [keep16 _ (by decide), r12v15, keep16 _ (by decide), keep15 _ (by decide),
      keep14 _ (by decide), hr13] <;> omega
  obtain ⟨s18, st17, pc18, r7_18, keep18, d18⟩ :=
    step16_loadData code input pc17 (at_restore subCode h32 (i := 17) (by decide))
      (by rw [r12v17, d17, d16, d15, d14]; exact hw7) (hPcLt 18 (by decide))
  obtain ⟨s19, st18, pc19, r12_19, keep19, d19⟩ :=
    step16_add code input pc18 (at_restore subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  have r12v19 : (reg s19 r12).val = loopSubStateBase loopBase n m + 8 := by
    rw [r12_19, add_no_wrap] <;> rw [keep18 _ (by decide), r12v17, keep18 _ (by decide), keep17 _ (by decide),
      keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), hr13] <;> omega
  obtain ⟨s20, st19, pc20, r8_20, keep20, d20⟩ :=
    step16_loadData code input pc19 (at_restore subCode h32 (i := 19) (by decide))
      (by rw [r12v19, d19, d18, d17, d16, d15, d14]; exact hw8) (hPcLt 20 (by decide))
  obtain ⟨s21, st20, pc21, r12_21, keep21, d21⟩ :=
    step16_add code input pc20 (at_restore subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide))
  have r12v21 : (reg s21 r12).val = loopSubStateBase loopBase n m + 9 := by
    rw [r12_21, add_no_wrap] <;> rw [keep20 _ (by decide), r12v19, keep20 _ (by decide), keep19 _ (by decide),
      keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide),
      keep14 _ (by decide), hr13] <;> omega
  obtain ⟨s22, st21, pc22, r9_22, keep22, d22⟩ :=
    step16_loadData code input pc21 (at_restore subCode h32 (i := 21) (by decide))
      (by rw [r12v21, d21, d20, d19, d18, d17, d16, d15, d14]; exact hw9) (hPcLt 22 (by decide))
  obtain ⟨s23, st22, pc23, r12_23, keep23, d23⟩ :=
    step16_add code input pc22 (at_restore subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide))
  have r12v23 : (reg s23 r12).val = loopSubStateBase loopBase n m + 10 := by
    rw [r12_23, add_no_wrap] <;> rw [keep22 _ (by decide), r12v21, keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide),
      keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), hr13] <;> omega
  obtain ⟨s24, st23, pc24, r10_24, keep24, d24⟩ :=
    step16_loadData code input pc23 (at_restore subCode h32 (i := 23) (by decide))
      (by rw [r12v23, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14]; exact hw10) (hPcLt 24 (by decide))
  have hSteps : Steps code input 11 s13 s24 :=
    Steps.cons st13 (Steps.cons st14 (Steps.cons st15 (Steps.cons st16 (Steps.cons st17
      (Steps.cons st18 (Steps.cons st19 (Steps.cons st20 (Steps.cons st21 (Steps.cons st22
        (Steps.cons st23 (Steps.zero s24)))))))))))
  refine ⟨s24, hSteps, by rw [pc24]; unfold offPost offMax; omega,
    by rw [d24, d23, d22, d21, d20, d19, d18, d17, d16, d15, d14],
    fun r hr => by
      have h5 : r ≠ r5 := fun e => absurd hr (by subst e; decide)
      have h6 : r ≠ r6 := fun e => absurd hr (by subst e; decide)
      have h7 : r ≠ r7 := fun e => absurd hr (by subst e; decide)
      have h8 : r ≠ r8 := fun e => absurd hr (by subst e; decide)
      have h9 : r ≠ r9 := fun e => absurd hr (by subst e; decide)
      have h10 : r ≠ r10 := fun e => absurd hr (by subst e; decide)
      have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
      rw [keep24 _ h10, keep23 _ h12, keep22 _ h9, keep21 _ h12, keep20 _ h8, keep19 _ h12,
        keep18 _ h7, keep17 _ h12, keep16 _ h6, keep15 _ h12, keep14 _ h5],
    fun r hr5 hr10 => ?_⟩
  rcases (by omega : r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10)
    with h | h | h | h | h | h
  · have hF : r = r5 := Fin.ext h; subst hF
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide),
      keep16 _ (by decide), keep15 _ (by decide), r5_14, hw5]
  · have hF : r = r6 := Fin.ext h; subst hF
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide),
      r6_16, hw6]
  · have hF : r = r7 := Fin.ext h; subst hF
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      keep20 _ (by decide), keep19 _ (by decide), r7_18, hw7]
  · have hF : r = r8 := Fin.ext h; subst hF
    rw [keep24 _ (by decide), keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide),
      r8_20, hw8]
  · have hF : r = r9 := Fin.ext h; subst hF
    rw [keep24 _ (by decide), keep23 _ (by decide), r9_22, hw9]
  · have hF : r = r10 := Fin.ext h; subst hF
    rw [r10_24, hw10]

private theorem restoreRegs_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m loopBase : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offPost subCode.size)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hSaved : ∀ r : Fin 16, r.val ≤ 10 → ∃ w, s₀.data[loopSubStateBase loopBase n m + r.val]? = some w) :
    ∃ s24, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 24 s₀ s24 ∧
      s24.pc = offMax subCode.size ∧ s24.data = s₀.data ∧
      (∀ r : Fin 16, r.val ≤ 10 → some (reg s24 r) = s₀.data[loopSubStateBase loopBase n m + r.val]?) := by
  obtain ⟨s13, hStA, pc13, hD13, hr12_13, hr13_13, hResA⟩ :=
    restoreRegsA_steps subCode h32 input hFit hBits hpc hStPtr hSaved
  obtain ⟨s24, hStB, pc24, hD24, hKeepB, hResB⟩ :=
    restoreRegsB_steps subCode h32 input hFit hBits pc13 hr12_13 hr13_13 fun r hr5 hr10 => by
      rw [hD13]; exact hSaved r (by omega)
  refine ⟨s24, hStA.append hStB, pc24, hD24.trans hD13, fun r hr => ?_⟩
  by_cases hr4 : r.val ≤ 4
  · rw [hKeepB r hr4]; exact hResA r hr4
  · rw [← hD13]; exact hResB r (by omega) hr

private theorem packedPayload_dict_at {bits : Nat} (w : WordColumns bits) {k : Nat}
    (hk : k < w.dictionary.size) : (packedPayload w)[k]? = w.dictionary[k]? := by
  unfold packedPayload packedPrefix
  simp only [Array.append_assoc]
  exact Array.getElem?_append_left hk

private theorem maxSlotPre_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed D n_d : Nat}
    (hD : 1 + 3 * D ≤ 19 * n_d) (hn_d : n_d ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offMax subCode.size) (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hDat0 : (s₀.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D) :
    ∃ s7, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 7 s₀ s7 ∧
      s7.pc = offMax subCode.size + 7 ∧ s7.data = s₀.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s7 ∧
      (reg s7 r13).val = loopSubWorkBase loopBase n m + 1 + 2 * D ∧
      (reg s7 r14).val = loopSubWorkBase loopBase n m + 1 + 3 * D ∧
      (reg s7 r15).val = 0 := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 8 → offMax subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offMax; omega
  have hZero : (reg s₀ rZero).val = 0 := hRegs.entry.consts.zero
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hWorkBnd : loopSubWorkBase loopBase n m + 1 + 3 * D < 2 ^ bits := by
    unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
  have hMemPtr : s₀.data[(reg s₀ r1).val]? = some ⟨loopSubWorkBase loopBase n m, by omega⟩ := by
    rw [hOne]; exact mem_word_of_map hDatPtr _
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_loadData code input hpc (at_max subCode h32 (i := 0) (by decide)) hMemPtr (hPcLt 1 (by decide))
  have hMemD : s1.data[(reg s1 r11).val]? = some ⟨D, by omega⟩ := by
    rw [d1, r11_1]; exact mem_word_of_map hDat0 _
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_max subCode h32 (i := 1) (by decide)) hMemD (hPcLt 2 (by decide))
  obtain ⟨s3, st2, pc3, r13_3, keep3, d3⟩ :=
    step16_add code input pc2 (at_max subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  have r13v3 : (reg s3 r13).val = 2 * D := by rw [r13_3, add_no_wrap] <;> rw [r12_2] <;> dsimp only <;> omega
  obtain ⟨s4, st3, pc4, r13_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_max subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have r11eq3 : (reg s3 r11).val = loopSubWorkBase loopBase n m := by
    rw [keep3 _ (by decide), keep2 _ (by decide), r11_1]
  have r13v4 : (reg s4 r13).val = loopSubWorkBase loopBase n m + 2 * D := by
    rw [r13_4, add_no_wrap] <;> rw [r11eq3, r13v3] <;> omega
  obtain ⟨s5, st4, pc5, r13_5, keep5, d5⟩ :=
    step16_add code input pc4 (at_max subCode h32 (i := 4) (by decide)) (hPcLt 5 (by decide))
  have h1eq4 : (reg s4 rOne).val = 1 := by
    rw [keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hOne]
  have r13v5 : (reg s5 r13).val = loopSubWorkBase loopBase n m + 1 + 2 * D := by
    rw [r13_5, add_no_wrap] <;> rw [r13v4, h1eq4] <;> omega
  obtain ⟨s6, st5, pc6, r14_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_max subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12eq5 : (reg s5 r12).val = D := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), r12_2]
  have r14v6 : (reg s6 r14).val = loopSubWorkBase loopBase n m + 1 + 3 * D := by
    rw [r14_6, add_no_wrap] <;> rw [r13v5, r12eq5] <;> omega
  obtain ⟨s7, st6, pc7, r15_7, keep7, d7⟩ :=
    step16_mov code input pc6 (at_max subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  refine ⟨s7, Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4
      (Steps.cons st5 (Steps.cons st6 (Steps.zero s7))))))),
    pc7, by rw [d7, d6, d5, d4, d3, d2, d1],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep7 _ h15, keep6 _ h14, keep5 _ h13, keep4 _ h13, keep3 _ h13, keep2 _ h12, keep1 _ h11]
  · rw [keep7 _ (by decide), keep6 _ (by decide), r13v5]
  · rw [keep7 _ (by decide), r14v6]
  · rw [r15_7, keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide),
      keep2 _ (by decide), keep1 _ (by decide), hZero]

private theorem maxSlotPostA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed maxSlot D n_d : Nat}
    (hD : 1 + 3 * D ≤ 19 * n_d) (hMax : maxSlot + 1 ≤ 19 * n_d) (hn_d : n_d ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s13 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s13.pc = offMax subCode.size + 13)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s13)
    (hr15 : (reg s13 r15).val = maxSlot)
    (hDatPtr : (s13.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hDat0 : (s13.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D)
    (hNdAt : (s13.data[loopBase]?).map Fin.val = some n_d) :
    ∃ s23, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 10 s13 s23 ∧
      s23.pc = offMax subCode.size + 23 ∧ s23.data = s13.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s23 ∧
      (reg s23 r13).val = n_d ∧ (reg s23 r14).val = 3 * D + 2 * n_d + 2 ∧
      (reg s23 r15).val = maxSlot + 1 := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 24 → offMax subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offMax; omega
  have hOne : (reg s13 rOne).val = 1 := hRegs.entry.consts.one
  have hL : (reg s13 r8).val = loopBase := hRegs.entry.loopBaseVal
  have hBndVal : 3 * D + 2 * n_d + 2 < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  have hWorkLt : loopSubWorkBase loopBase n m < 2 ^ bits := by
    unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
  obtain ⟨s14, st13, pc14, r15_14, keep14, d14⟩ :=
    step16_add code input hpc (at_max subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide))
  have r15v14 : (reg s14 r15).val = maxSlot + 1 := by
    rw [r15_14, add_no_wrap] <;> rw [hr15, hOne] <;> (try unfold loopWorkWords at hFit) <;> omega
  have hMemPtr : s14.data[(reg s14 r1).val]? = some ⟨loopSubWorkBase loopBase n m, hWorkLt⟩ := by
    rw [d14, keep14 _ (by decide), hOne]; exact mem_word_of_map hDatPtr hWorkLt
  obtain ⟨s15, st14, pc15, r11_15, keep15, d15⟩ :=
    step16_loadData code input pc14 (at_max subCode h32 (i := 14) (by decide)) hMemPtr (hPcLt 15 (by decide))
  have hMemD : s15.data[(reg s15 r11).val]? = some ⟨D, by omega⟩ := by
    rw [d15, d14, r11_15]; exact mem_word_of_map hDat0 _
  obtain ⟨s16, st15, pc16, r12_16, keep16, d16⟩ :=
    step16_loadData code input pc15 (at_max subCode h32 (i := 15) (by decide)) hMemD (hPcLt 16 (by decide))
  have hMemNd : s16.data[(reg s16 r8).val]? = some ⟨n_d, by omega⟩ := by
    rw [d16, d15, d14, keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), hL]
    exact mem_word_of_map hNdAt _
  obtain ⟨s17, st16, pc17, r13_17, keep17, d17⟩ :=
    step16_loadData code input pc16 (at_max subCode h32 (i := 16) (by decide)) hMemNd (hPcLt 17 (by decide))
  have r12eq17 : (reg s17 r12).val = D := by rw [keep17 _ (by decide), r12_16]
  have h1eq17 : (reg s17 rOne).val = 1 := by
    rw [keep17 _ (by decide), keep16 _ (by decide), keep15 _ (by decide), keep14 _ (by decide), hOne]
  obtain ⟨s18, st17, pc18, r14_18, keep18, d18⟩ :=
    step16_add code input pc17 (at_max subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide))
  have r14v18 : (reg s18 r14).val = 2 * D := by rw [r14_18, add_no_wrap] <;> rw [r12eq17] <;> omega
  obtain ⟨s19, st18, pc19, r14_19, keep19, d19⟩ :=
    step16_add code input pc18 (at_max subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  have r14v19 : (reg s19 r14).val = 3 * D := by
    rw [r14_19, add_no_wrap] <;> rw [r14v18, keep18 _ (by decide), r12eq17] <;> omega
  obtain ⟨s20, st19, pc20, r14_20, keep20, d20⟩ :=
    step16_add code input pc19 (at_max subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  have r14v20 : (reg s20 r14).val = 3 * D + 1 := by
    rw [r14_20, add_no_wrap] <;> rw [r14v19, keep19 _ (by decide), keep18 _ (by decide), h1eq17] <;> omega
  obtain ⟨s21, st20, pc21, r14_21, keep21, d21⟩ :=
    step16_add code input pc20 (at_max subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide))
  have r13eq20 : (reg s20 r13).val = n_d := by
    rw [keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), r13_17]
  have r14v21 : (reg s21 r14).val = 3 * D + 1 + n_d := by
    rw [r14_21, add_no_wrap] <;> rw [r14v20, r13eq20] <;> omega
  obtain ⟨s22, st21, pc22, r14_22, keep22, d22⟩ :=
    step16_add code input pc21 (at_max subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide))
  have r14v22 : (reg s22 r14).val = 3 * D + 2 + n_d := by
    rw [r14_22, add_no_wrap]
    · rw [r14v21, keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), h1eq17]; omega
    · rw [r14v21, keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), h1eq17]; omega
  obtain ⟨s23, st22, pc23, r14_23, keep23, d23⟩ :=
    step16_add code input pc22 (at_max subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide))
  have r14v23 : (reg s23 r14).val = 3 * D + 2 * n_d + 2 := by
    rw [r14_23, add_no_wrap]
    · rw [r14v22, keep22 _ (by decide), keep21 _ (by decide), r13eq20]; omega
    · rw [r14v22, keep22 _ (by decide), keep21 _ (by decide), r13eq20]; omega
  have hSteps : Steps code input 10 s13 s23 :=
    Steps.cons st13 (Steps.cons st14 (Steps.cons st15 (Steps.cons st16 (Steps.cons st17
      (Steps.cons st18 (Steps.cons st19 (Steps.cons st20 (Steps.cons st21 (Steps.cons st22 (Steps.zero s23))))))))))
  refine ⟨s23, hSteps, pc23,
    by rw [d23, d22, d21, d20, d19, d18, d17, d16, d15, d14],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, r14v23, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep23 _ h14, keep22 _ h14, keep21 _ h14, keep20 _ h14, keep19 _ h14, keep18 _ h14,
      keep17 _ h13, keep16 _ h12, keep15 _ h11, keep14 _ h15]
  · rw [keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide), r13eq20]
  · rw [keep23 _ (by decide), keep22 _ (by decide), keep21 _ (by decide), keep20 _ (by decide),
      keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide),
      keep15 _ (by decide), r15v14]

private theorem maxSlotPostB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed D n_d N_d : Nat}
    (hWc : 3 * D + 3 * n_d + 2 * N_d + 3 ≤ 19 * n_d) (hn_d : n_d ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s23 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s23.pc = offMax subCode.size + 23) (hDataSz : s23.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s23)
    (hr13 : (reg s23 r13).val = n_d) (hr14 : (reg s23 r14).val = 3 * D + 2 * n_d + 2)
    (hr15 : (reg s23 r15).val = N_d)
    (hStPtr : (s23.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m)) :
    let wc := 3 * D + 3 * n_d + 2 * N_d + 3
    ∃ s32, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 9 s23 s32 ∧
      s32.pc = offCopy subCode.size ∧ s32.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s32 ∧
      (reg s32 r14).val = wc ∧ (reg s32 r15).val = N_d ∧
      s32.data[loopSubStateBase loopBase n m]? = some ⟨N_d, by unfold loopWorkWords at hFit; omega⟩ ∧
      s32.data[loopSubStateBase loopBase n m + 1]? = some ⟨wc, by unfold loopWorkWords at hFit; omega⟩ ∧
      (∀ addr, (addr < loopSubStateBase loopBase n m ∨ loopSubStateBase loopBase n m + 2 ≤ addr) →
        s32.data[addr]? = s23.data[addr]?) := by
  intro wc
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 33 → offMax subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offMax; omega
  have hOne : (reg s23 rOne).val = 1 := hRegs.entry.consts.one
  have hStBnd : loopSubStateBase loopBase n m + 16 ≤ workCap := by
    unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hWcLt : wc < 2 ^ bits := by unfold loopWorkWords at hFit; omega
  obtain ⟨s24, st23, pc24, r14_24, keep24, d24⟩ :=
    step16_add code input hpc (at_max subCode h32 (i := 23) (by decide)) (hPcLt 24 (by decide))
  have r14v24 : (reg s24 r14).val = 3 * D + 2 * n_d + 3 := by
    rw [r14_24, add_no_wrap] <;> rw [hr14, hOne] <;> omega
  obtain ⟨s25, st24, pc25, r14_25, keep25, d25⟩ :=
    step16_add code input pc24 (at_max subCode h32 (i := 24) (by decide)) (hPcLt 25 (by decide))
  have r14v25 : (reg s25 r14).val = 3 * D + 3 * n_d + 3 := by
    rw [r14_25, add_no_wrap] <;> rw [r14v24, keep24 _ (by decide), hr13] <;> omega
  obtain ⟨s26, st25, pc26, r14_26, keep26, d26⟩ :=
    step16_add code input pc25 (at_max subCode h32 (i := 25) (by decide)) (hPcLt 26 (by decide))
  have r15eq25 : (reg s25 r15).val = N_d := by
    rw [keep25 _ (by decide), keep24 _ (by decide), hr15]
  have r14v26 : (reg s26 r14).val = 3 * D + 3 * n_d + N_d + 3 := by
    rw [r14_26, add_no_wrap] <;> rw [r14v25, r15eq25] <;> omega
  obtain ⟨s27, st26, pc27, r14_27, keep27, d27⟩ :=
    step16_add code input pc26 (at_max subCode h32 (i := 26) (by decide)) (hPcLt 27 (by decide))
  have r14v27 : (reg s27 r14).val = wc := by
    rw [r14_27, add_no_wrap]
    · rw [r14v26, keep26 _ (by decide), r15eq25]; dsimp only [wc]; omega
    · rw [r14v26, keep26 _ (by decide), r15eq25]; unfold loopWorkWords at hFit; omega
  obtain ⟨s28, st27, pc28, r11_28, keep28, d28⟩ :=
    step16_imm code input pc27 (at_max subCode h32 (i := 27) (by decide)) (hPcLt 28 (by decide))
  have hMemSt : s28.data[(reg s28 r11).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d28, d27, d26, d25, d24, show (reg s28 r11).val = statePtrAddr by rw [r11_28]; rfl]
    exact mem_word_of_map hStPtr _
  obtain ⟨s29, st28, pc29, r12_29, keep29, d29⟩ :=
    step16_loadData code input pc28 (at_max subCode h32 (i := 28) (by decide)) hMemSt (hPcLt 29 (by decide))
  have hData29 : s29.data = s23.data := by rw [d29, d28, d27, d26, d25, d24]
  have hBnd29 : (reg s29 r12).val < s29.data.size := by rw [r12_29, hData29, hDataSz]; dsimp only; omega
  obtain ⟨s30, st29, pc30, regs30, d30⟩ :=
    step16_storeData code input pc29 (at_max subCode h32 (i := 29) (by decide)) (hPcLt 30 (by decide)) hBnd29
  have reg30 : ∀ r : Fin 16, reg s30 r = reg s29 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs30 r
  have h1eq29 : (reg s29 r1).val = 1 := by
    rw [keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide),
      keep25 _ (by decide), keep24 _ (by decide)]; exact hOne
  have h1eq30 : (reg s30 rOne).val = 1 := by rw [reg30]; exact h1eq29
  obtain ⟨s31, st30, pc31, r12_31, keep31, d31⟩ :=
    step16_add code input pc30 (at_max subCode h32 (i := 30) (by decide)) (hPcLt 31 (by decide))
  have r12v31 : (reg s31 r12).val = loopSubStateBase loopBase n m + 1 := by
    rw [r12_31, add_no_wrap] <;> rw [reg30, reg30, r12_29, h1eq29] <;> dsimp only <;> omega
  have hBnd31 : (reg s31 r12).val < s31.data.size := by rw [r12v31, d31, d30, Array.size_set, hData29, hDataSz]; omega
  obtain ⟨s32, st31, pc32, regs32, d32⟩ :=
    step16_storeData code input pc31 (at_max subCode h32 (i := 31) (by decide)) (hPcLt 32 (by decide)) hBnd31
  have reg32 : ∀ r : Fin 16, reg s32 r = reg s31 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs32 r
  have hSteps : Steps code input 9 s23 s32 :=
    Steps.cons st23 (Steps.cons st24 (Steps.cons st25 (Steps.cons st26 (Steps.cons st27
      (Steps.cons st28 (Steps.cons st29 (Steps.cons st30 (Steps.cons st31 (Steps.zero s32)))))))))
  have r14eq31 : (reg s31 r14).val = wc := by
    rw [keep31 _ (by decide), reg30, keep29 _ (by decide), keep28 _ (by decide), r14v27]
  have r15eq29 : (reg s29 r15).val = N_d := by
    rw [keep29 _ (by decide), keep28 _ (by decide), keep27 _ (by decide), keep26 _ (by decide), r15eq25]
  refine ⟨s32, hSteps, by rw [pc32]; unfold offMax offCopy; omega,
    by rw [d32, Array.size_set, d31, d30, Array.size_set, hData29, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_, by rw [reg32, r14eq31],
    by rw [reg32, keep31 _ (by decide), reg30, r15eq29], ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    rw [reg32, keep31 _ h12, reg30, keep29 _ h12, keep28 _ h11, keep27 _ h14, keep26 _ h14,
      keep25 _ h14, keep24 _ h14]
  · rw [d32]; rw [mem_set_ne s31.data hBnd31 (by rw [r12v31]; omega), d31, d30,
      mem_set_same s29.data (congrArg Fin.val r12_29) hBnd29]
    exact congrArg some (Fin.ext r15eq29)
  · rw [d32, mem_set_same s31.data r12v31 hBnd31]
    exact congrArg some (Fin.ext r14eq31)
  · intro addr ha
    rw [d32]; rw [mem_set_ne s31.data hBnd31 (by rw [r12v31]; omega), d31, d30,
      mem_set_ne s29.data hBnd29 (by rw [r12_29]; dsimp only; omega), hData29]

private theorem maxSlotAndWordCount_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed n_d : Nat}
    (w : WordColumns bits)
    (hn_d : n_d ≤ n)
    (hWcLe : w.wordCount ≤ 19 * n_d)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {D N_d : Nat}
    (hDat0 : (w.dictionary[0]?).map Fin.val = some D)
    (hDictSz : w.dictionary.size = 1 + 3 * D)
    (hBack1 : w.back.tagAndFirst.size = n_d + 1)
    (hBack2 : w.back.second.size = n_d + 1)
    (hLabSz : w.labels.size = n_d)
    (hEntrySz : w.entry.size = N_d)
    (hStopSz : w.stop.size = N_d)
    (hND : N_d = 1 + (List.range D).foldl
      (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offMax subCode.size) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some n_d)
    (hPayload : s₀.data.extract (loopSubWorkBase loopBase n m)
        (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 6 * D + 27 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offCopy subCode.size ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t ∧
      (reg t r14).val = w.wordCount ∧ (reg t r15).val = N_d ∧
      t.data[loopSubStateBase loopBase n m]? = some ⟨N_d, by
          have := hWcLe; unfold WordColumns.wordCount at this; unfold loopWorkWords at hFit; omega⟩ ∧
      t.data[loopSubStateBase loopBase n m + 1]? = some ⟨w.wordCount, by
          unfold loopWorkWords at hFit; omega⟩ ∧
      (∀ addr, (addr < loopSubStateBase loopBase n m ∨ loopSubStateBase loopBase n m + 2 ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 14 → offMax subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offMax; omega
  have hDictLeWc : w.dictionary.size ≤ w.wordCount := by
    unfold WordColumns.wordCount; omega
  have hDictAt : ∀ k, k < w.dictionary.size →
      s₀.data[loopSubWorkBase loopBase n m + k]? = w.dictionary[k]? := by
    intro k hk
    have hkWc : k < w.wordCount := Nat.lt_of_lt_of_le hk hDictLeWc
    have hkExt : k < (s₀.data.extract (loopSubWorkBase loopBase n m)
        (loopSubWorkBase loopBase n m + w.wordCount)).size := by
      rw [hPayload, packedPayload_size]; exact hkWc
    have hSubBnd : loopSubWorkBase loopBase n m + k < s₀.data.size := by
      rw [hDataSz]; unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
    rw [← packedPayload_dict_at w hk, ← hPayload, Array.getElem?_eq_getElem hkExt, Array.getElem_extract,
      Array.getElem?_eq_getElem hSubBnd]
  have hDat0 : (s₀.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D := by
    simpa only [Nat.add_zero] using (congrArg (Option.map Fin.val) (hDictAt 0 (by omega))).trans hDat0
  have hWcEq : w.wordCount = 3 * D + 3 * n_d + 2 * N_d + 3 := by
    unfold WordColumns.wordCount
    rw [hDictSz, hBack1, hBack2, hLabSz, hEntrySz, hStopSz]
    omega
  obtain ⟨s7, hStPre, pc7, hD7, hRg7, hr13_7, hr14_7, hr15_7⟩ :=
    maxSlotPre_steps subCode h32 input (by omega : 1 + 3 * D ≤ 19 * n_d) hn_d hFit hBits hpc hRegs hDatPtr hDat0
  let foldSlot : Nat → Nat := fun j =>
    (List.range j).foldl (fun acc i => max acc (((w.dictionary[1 + 2 * D + i]?).map Fin.val).getD 0)) 0
  have hFoldBound : ∀ j ≤ D, foldSlot j ≤ N_d - 1 := by
    intro j hj
    have hD1 : N_d - 1 = foldSlot D := by rw [hND]; dsimp only [foldSlot]; omega
    rw [hD1]
    suffices ∀ rem, j + rem ≤ D → foldSlot j ≤ foldSlot (j + rem) by
      simpa only [Nat.add_sub_cancel' hj] using this (D - j) (by omega)
    intro rem
    induction rem with
    | zero => exact fun _ => Nat.le_refl _
    | succ k ih =>
      intro hk
      have hk1 := ih (by omega)
      have hStep : foldSlot (j + k) ≤ foldSlot (j + k + 1) := by
        dsimp only [foldSlot]
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
        exact Nat.le_max_left _ _
      exact Nat.le_trans hk1 (by simpa only [Nat.add_assoc] using hStep)
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun j s =>
    j ≤ D ∧ s.pc = offMax subCode.size + 7 ∧ s.data = s₀.data ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (reg s r13).val = loopSubWorkBase loopBase n m + 1 + 2 * D + j ∧
    (reg s r14).val = loopSubWorkBase loopBase n m + 1 + 3 * D ∧
    (reg s r15).val = foldSlot j
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offMax subCode.size + 13 ∧ s.data = s₀.data ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (reg s r15).val = foldSlot D
  have hLoop := loop_steps_budget inv (fun j => D - j) (fun j => 1 + 6 * (D - j)) post
    (fun j s ⟨hjLe, hpcS, hDS, hRgS, hr13S, hr14S, hr15S⟩ => by
      by_cases hjEq : j = D
      · subst hjEq
        have hGe : (reg s r14).val ≤ (reg s r13).val := by rw [hr13S, hr14S]; omega
        have stBr := step16_branchLt_false code input hpcS (at_max subCode h32 (i := 7) (by decide))
          (hPcLt 13 (by decide)) hGe
        exact Or.inl ⟨_, 1, by omega, steps_one stBr, rfl, hDS,
          loopIterRegs_of_keep hRgS (fun _ _ => rfl), hr15S⟩
      · have hjLt : j < D := Nat.lt_of_le_of_ne hjLe hjEq
        have hLtR : (reg s r13).val < (reg s r14).val := by rw [hr13S, hr14S]; omega
        have st7 := step16_branchLt_true code input hpcS (at_max subCode h32 (i := 7) (by decide))
          (hPcLt 8 (by decide)) hLtR
        let s8 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s.regs, data := s.data, pc := offMax subCode.size + 8,
            regs_size := s.regs_size, data_size := s.data_size }
        have hReg8 : ∀ r : Fin 16, reg s8 r = reg s r := fun _ => rfl
        let wSlot : Word bits := w.dictionary[1 + 2 * D + j]'(by omega)
        have hSlotEq : ((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0 = wSlot.val := by
          rw [Array.getElem?_eq_getElem (by omega)]; rfl
        have hMem8 : s8.data[(reg s8 r13).val]? = some wSlot := by
          have hAddrJ : (reg s8 r13).val = loopSubWorkBase loopBase n m + (1 + 2 * D + j) := by
            rw [hReg8, hr13S]; omega
          change s.data[(reg s8 r13).val]? = _
          rw [hDS, hAddrJ, hDictAt (1 + 2 * D + j) (by omega), Array.getElem?_eq_getElem (by omega)]
        obtain ⟨s9, st8, pc9, r11_9, keep9, d9⟩ :=
          step16_loadData code input (rfl : s8.pc = offMax subCode.size + 8)
            (at_max subCode h32 (i := 8) (by decide)) hMem8 (hPcLt 9 (by decide))
        have hOne11 : (reg s9 r1).val = 1 := by rw [keep9 _ (by decide), hReg8]; exact hRgS.entry.consts.one
        have hr13_9 : (reg s9 r13).val = loopSubWorkBase loopBase n m + 1 + 2 * D + j := by
          rw [keep9 _ (by decide), hReg8, hr13S]
        have hr14_9 : (reg s9 r14).val = loopSubWorkBase loopBase n m + 1 + 3 * D := by
          rw [keep9 _ (by decide), hReg8, hr14S]
        have hr15_9 : (reg s9 r15).val = foldSlot j := by
          rw [keep9 _ (by decide), hReg8, hr15S]
        have hStepFold : foldSlot (j + 1) = max (foldSlot j) wSlot.val := by
          dsimp only [foldSlot]
          rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, hSlotEq]
        by_cases hCmp : (reg s9 r15).val < (reg s9 r11).val
        · have st9 := step16_branchLt_true code input pc9 (at_max subCode h32 (i := 9) (by decide))
            (hPcLt 10 (by decide)) hCmp
          let s10 : State (layout16 bits inputCap workCap hi hw) :=
            { regs := s9.regs, data := s9.data, pc := offMax subCode.size + 10,
              regs_size := s9.regs_size, data_size := s9.data_size }
          obtain ⟨s11, st10, pc11, r15_11, keep11, d11⟩ :=
            step16_mov code input (rfl : s10.pc = offMax subCode.size + 10)
              (at_max subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
          obtain ⟨s12, st11, pc12, r13_12, keep12, d12⟩ :=
            step16_add code input pc11 (at_max subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
          have r13v12 : (reg s12 r13).val = loopSubWorkBase loopBase n m + 1 + 2 * D + (j + 1) := by
            rw [r13_12, add_no_wrap]
            · rw [keep11 _ (by decide), show reg s10 r13 = reg s9 r13 from rfl, hr13_9,
                keep11 _ (by decide), show reg s10 r1 = reg s9 r1 from rfl, hOne11]; omega
            · rw [keep11 _ (by decide), show reg s10 r13 = reg s9 r13 from rfl, hr13_9,
                keep11 _ (by decide), show reg s10 r1 = reg s9 r1 from rfl, hOne11]
              unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
          have st12 := step16_goto code input pc12 (at_max subCode h32 (i := 12) (by decide))
            (hPcLt 7 (by decide))
          let s13 : State (layout16 bits inputCap workCap hi hw) :=
            { regs := s12.regs, data := s12.data, pc := offMax subCode.size + 7,
              regs_size := s12.regs_size, data_size := s12.data_size }
          have hStIter : Steps code input 6 s s13 :=
            Steps.cons st7 (Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11
              (Steps.cons st12 (Steps.zero s13))))))
          have hr15_13 : (reg s13 r15).val = foldSlot (j + 1) := by
            change (reg s12 r15).val = _
            have hwLt : foldSlot j < wSlot.val := by
              rw [← hr15_9]; exact Nat.lt_of_lt_of_eq hCmp (congrArg Fin.val r11_9)
            rw [hStepFold, Nat.max_eq_right (Nat.le_of_lt hwLt), keep12 _ (by decide),
              r15_11, show reg s10 r11 = reg s9 r11 from rfl, r11_9]
          refine Or.inr ⟨j + 1, s13, 6, by omega, by omega, hStIter, by omega, rfl,
            by rw [show s13.data = s12.data from rfl, d12, d11, d9, hDS],
            loopIterRegs_of_keep hRgS (fun r hr => ?_), r13v12, ?_, hr15_13⟩
          · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
            have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
            have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
            exact (keep12 _ h13).trans ((keep11 _ h15).trans (keep9 _ h11))
          · exact (congrArg Fin.val ((keep12 _ (by decide)).trans (keep11 _ (by decide)))).trans hr14_9
        · have st9 := step16_branchLt_false code input pc9 (at_max subCode h32 (i := 9) (by decide))
            (hPcLt 11 (by decide)) (Nat.le_of_not_lt hCmp)
          let s11 : State (layout16 bits inputCap workCap hi hw) :=
            { regs := s9.regs, data := s9.data, pc := offMax subCode.size + 11,
              regs_size := s9.regs_size, data_size := s9.data_size }
          obtain ⟨s12, st11, pc12, r13_12, keep12, d12⟩ :=
            step16_add code input (rfl : s11.pc = offMax subCode.size + 11)
              (at_max subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
          have r13v12 : (reg s12 r13).val = loopSubWorkBase loopBase n m + 1 + 2 * D + (j + 1) := by
            rw [r13_12, add_no_wrap]
            · rw [show reg s11 r13 = reg s9 r13 from rfl, hr13_9,
                show reg s11 r1 = reg s9 r1 from rfl, hOne11]; omega
            · rw [show reg s11 r13 = reg s9 r13 from rfl, hr13_9,
                show reg s11 r1 = reg s9 r1 from rfl, hOne11]
              unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
          have st12 := step16_goto code input pc12 (at_max subCode h32 (i := 12) (by decide))
            (hPcLt 7 (by decide))
          let s13 : State (layout16 bits inputCap workCap hi hw) :=
            { regs := s12.regs, data := s12.data, pc := offMax subCode.size + 7,
              regs_size := s12.regs_size, data_size := s12.data_size }
          have hStIter : Steps code input 5 s s13 :=
            Steps.cons st7 (Steps.cons st8 (Steps.cons st9 (Steps.cons st11
              (Steps.cons st12 (Steps.zero s13)))))
          have hr15_13 : (reg s13 r15).val = foldSlot (j + 1) := by
            change (reg s12 r15).val = _
            have hwLe : wSlot.val ≤ foldSlot j := by
              rw [← hr15_9, ← congrArg Fin.val r11_9]; exact Nat.le_of_not_lt hCmp
            rw [hStepFold, Nat.max_eq_left hwLe, keep12 _ (by decide),
              show reg s11 r15 = reg s9 r15 from rfl, hr15_9]
          refine Or.inr ⟨j + 1, s13, 5, by omega, by omega, hStIter, by omega, rfl,
            by rw [show s13.data = s12.data from rfl, d12, d9, hDS],
            loopIterRegs_of_keep hRgS (fun r hr => ?_), r13v12, ?_, hr15_13⟩
          · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
            have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
            exact (keep12 _ h13).trans (keep9 _ h11)
          · exact (congrArg Fin.val (keep12 _ (by decide))).trans hr14_9)
    D 0 s7 (by omega)
    ⟨Nat.zero_le _, pc7, hD7, hRg7, by simpa only [Nat.add_zero] using hr13_7, hr14_7, hr15_7⟩
  obtain ⟨_, s13, kLoop, hkLoop, hStLoop, hPc13, hD13, hRg13, hr15_13⟩ := hLoop
  have hDatPtr13 : (s13.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    rw [hD13]; exact hDatPtr
  have hDat0_13 : (s13.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D := by
    rw [hD13]; exact hDat0
  have hNd13 : (s13.data[loopBase]?).map Fin.val = some n_d := by
    rw [hD13]; exact hNdAt
  have hDataSz13 : s13.data.size = workCap := by rw [hD13, hDataSz]
  have hFoldD : foldSlot D + 1 ≤ 19 * n_d := by
    have : N_d = 1 + foldSlot D := hND
    omega
  obtain ⟨s23, hStPostA, pc23, hD23, hRg23, hr13_23, hr14_23, hr15_23⟩ :=
    maxSlotPostA_steps subCode h32 input (D := D) (maxSlot := foldSlot D)
      (by omega) hFoldD hn_d hFit hBits hPc13 hRg13 hr15_13 hDatPtr13 hDat0_13 hNd13
  have hr15_23' : (reg s23 r15).val = N_d := by rw [hr15_23]; dsimp only [foldSlot] at *; omega
  have hStPtr23 : (s23.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hD23, hD13]; exact hStPtr
  obtain ⟨s32, hStPostB, pc32, hSz32, hRg32, hr14_32, hr15_32, hMemSt0, hMemSt1, hMemRest⟩ :=
    maxSlotPostB_steps subCode h32 input (D := D) (N_d := N_d) (by rw [← hWcEq]; exact hWcLe) hn_d hFit hBits
      pc23 (by rw [hD23, hDataSz13]) hRg23 hr13_23 hr14_23 hr15_23' hStPtr23
  refine ⟨s32, 7 + kLoop + 10 + 9, by omega,
    ((hStPre.append hStLoop).append hStPostA).append hStPostB,
    pc32, hSz32, hRg32, by rw [hr14_32, hWcEq], hr15_32, hMemSt0,
    by rw [hMemSt1]; exact congrArg some (Fin.ext hWcEq.symm), fun addr hAddr => ?_⟩
  rw [hMemRest addr hAddr, hD23, hD13]

private theorem arenaCopyPre_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed wc : Nat}
    (_hWcLe : wc ≤ 19 * n) (hArenaFit : forestUsed + wc ≤ 38 * n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offCopy subCode.size)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hr14 : (reg s₀ r14).val = wc)
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hArenaPtr : (s₀.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m)) :
    ∃ s8, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 8 s₀ s8 ∧
      s8.pc = offCopy subCode.size + 8 ∧ s8.data = s₀.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s8 ∧
      (reg s8 r11).val = loopSubWorkBase loopBase n m ∧
      (reg s8 r12).val = forestArenaBase loopBase n m + forestUsed ∧
      (reg s8 r14).val = wc ∧
      (reg s8 r15).val = loopSubWorkBase loopBase n m + wc := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 9 → offCopy subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offCopy; omega
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hUsed : (reg s₀ r10).val = forestUsed := hRegs.usedVal
  have hBnd : forestArenaBase loopBase n m + forestUsed + wc < 2 ^ bits ∧
      loopSubWorkBase loopBase n m + wc < 2 ^ bits ∧
      loopSubStateBase loopBase n m + 15 < 2 ^ bits := by
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *
    omega
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_imm code input hpc (at_copy subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hMemSt : s1.data[(reg s1 r11).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d1, show (reg s1 r11).val = statePtrAddr by rw [r11_1]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_copy subCode h32 (i := 1) (by decide)) hMemSt (hPcLt 2 (by decide))
  obtain ⟨s3, st2, pc3, r13_3, keep3, d3⟩ :=
    step16_imm code input pc2 (at_copy subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_copy subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have r12v4 : (reg s4 r12).val = loopSubStateBase loopBase n m + 15 := by
    rw [r12_4, add_no_wrap]
    · rw [keep3 _ (by decide), r12_2, r13_3]; rfl
    · rw [keep3 _ (by decide), r12_2, r13_3]; change loopSubStateBase loopBase n m + 15 < 2 ^ bits; omega
  have hMemAr : s4.data[(reg s4 r12).val]? = some ⟨forestArenaBase loopBase n m, by omega⟩ := by
    rw [r12v4, d4, d3, d2, d1]; exact mem_word_of_map hArenaPtr _
  obtain ⟨s5, st4, pc5, r12_5, keep5, d5⟩ :=
    step16_loadData code input pc4 (at_copy subCode h32 (i := 4) (by decide)) hMemAr (hPcLt 5 (by decide))
  have h10eq5 : (reg s5 r10).val = forestUsed := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide),
      keep1 _ (by decide), hUsed]
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_copy subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = forestArenaBase loopBase n m + forestUsed := by
    rw [r12_6, add_no_wrap] <;> rw [r12_5, h10eq5] <;> dsimp only <;> omega
  have hOne6 : (reg s6 rOne).val = 1 := by
    rw [keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide),
      keep2 _ (by decide), keep1 _ (by decide), hOne]
  have hMemDat : s6.data[(reg s6 r1).val]? = some ⟨loopSubWorkBase loopBase n m, by omega⟩ := by
    rw [d6, d5, d4, d3, d2, d1]; rw [show (reg s6 r1).val = dataPtrAddr from hOne6]; exact mem_word_of_map hDatPtr _
  obtain ⟨s7, st6, pc7, r11_7, keep7, d7⟩ :=
    step16_loadData code input pc6 (at_copy subCode h32 (i := 6) (by decide)) hMemDat (hPcLt 7 (by decide))
  have r14eq7 : (reg s7 r14).val = wc := by
    rw [keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide),
      keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hr14]
  obtain ⟨s8, st7, pc8, r15_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_copy subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r15v8 : (reg s8 r15).val = loopSubWorkBase loopBase n m + wc := by
    rw [r15_8, add_no_wrap] <;> rw [r11_7, r14eq7] <;> dsimp only <;> omega
  have hSteps : Steps code input 8 s₀ s8 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4
      (Steps.cons st5 (Steps.cons st6 (Steps.cons st7 (Steps.zero s8))))))))
  refine ⟨s8, hSteps, pc8, by rw [d8, d7, d6, d5, d4, d3, d2, d1],
    loopIterRegs_of_keep hRegs fun r hr => ?_, ?_, ?_, ?_, r15v8⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep8 _ h15, keep7 _ h11, keep6 _ h12, keep5 _ h12, keep4 _ h12, keep3 _ h13, keep2 _ h12, keep1 _ h11]
  · rw [keep8 _ (by decide), r11_7]
  · rw [keep8 _ (by decide), keep7 _ (by decide), r12v6]
  · rw [keep8 _ (by decide), r14eq7]

private theorem arenaCopy_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (w : WordColumns bits)
    (hWcLe : w.wordCount ≤ 19 * n) (hArenaFit : forestUsed + w.wordCount ≤ 38 * n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offCopy subCode.size) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hr14 : (reg s₀ r14).val = w.wordCount)
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hArenaPtr : (s₀.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m))
    (hPayload : s₀.data.extract (loopSubWorkBase loopBase n m)
        (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 6 * w.wordCount + 9 ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ t ∧
      t.pc = offRec subCode.size ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed t ∧
      (∀ j < w.wordCount,
        t.data[forestArenaBase loopBase n m + forestUsed + j]? = (packedPayload w)[j]?) ∧
      (∀ addr, (addr < forestArenaBase loopBase n m + forestUsed ∨
          forestArenaBase loopBase n m + forestUsed + w.wordCount ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 15 → offCopy subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offCopy; omega
  have hPayAt : ∀ k < w.wordCount,
      s₀.data[loopSubWorkBase loopBase n m + k]? = (packedPayload w)[k]? := by
    intro k hk
    have hkExt : k < (s₀.data.extract (loopSubWorkBase loopBase n m)
        (loopSubWorkBase loopBase n m + w.wordCount)).size := by
      rw [hPayload, packedPayload_size]; exact hk
    have hSubBnd : loopSubWorkBase loopBase n m + k < s₀.data.size := by
      rw [hDataSz]; unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
    rw [← hPayload, Array.getElem?_eq_getElem hkExt, Array.getElem_extract, Array.getElem?_eq_getElem hSubBnd]
  have hDisj : ∀ k < w.wordCount,
      loopSubWorkBase loopBase n m + k < forestArenaBase loopBase n m + forestUsed := by
    intro k hk
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *
    omega
  have hArenaBnd : forestArenaBase loopBase n m + forestUsed + w.wordCount ≤ workCap := by
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *
    omega
  obtain ⟨s8, hStPre, pc8, hD8, hRg8, hr11_8, hr12_8, hr14_8, hr15_8⟩ :=
    arenaCopyPre_steps subCode h32 input hWcLe hArenaFit hFit hBits hpc hRegs hr14 hDatPtr hStPtr hArenaPtr
  let inv : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun k s =>
    k ≤ w.wordCount ∧ s.pc = offCopy subCode.size + 8 ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (reg s r11).val = loopSubWorkBase loopBase n m + k ∧
    (reg s r12).val = forestArenaBase loopBase n m + forestUsed + k ∧
    (reg s r14).val = w.wordCount ∧
    (reg s r15).val = loopSubWorkBase loopBase n m + w.wordCount ∧
    (∀ j < k, s.data[forestArenaBase loopBase n m + forestUsed + j]? = (packedPayload w)[j]?) ∧
    (∀ addr, (addr < forestArenaBase loopBase n m + forestUsed ∨
        forestArenaBase loopBase n m + forestUsed + k ≤ addr) → s.data[addr]? = s₀.data[addr]?)
  let post : Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    s.pc = offRec subCode.size ∧ s.data.size = workCap ∧
    LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s ∧
    (∀ j < w.wordCount, s.data[forestArenaBase loopBase n m + forestUsed + j]? = (packedPayload w)[j]?) ∧
    (∀ addr, (addr < forestArenaBase loopBase n m + forestUsed ∨
        forestArenaBase loopBase n m + forestUsed + w.wordCount ≤ addr) → s.data[addr]? = s₀.data[addr]?)
  have hLoop := loop_steps_budget inv (fun k => w.wordCount - k) (fun k => 1 + 6 * (w.wordCount - k)) post
    (fun k s ⟨hkLe, hpcS, hSzS, hRgS, hr11S, hr12S, hr14S, hr15S, hWrtS, hOutS⟩ => by
      by_cases hkEq : k = w.wordCount
      · subst hkEq
        have hGe : (reg s r15).val ≤ (reg s r11).val := by rw [hr11S, hr15S]; omega
        have stBr := step16_branchLt_false code input hpcS (at_copy subCode h32 (i := 8) (by decide))
          (hPcLt 14 (by decide)) hGe
        exact Or.inl ⟨_, 1, by omega, steps_one stBr,
          by show offCopy subCode.size + 14 = offRec subCode.size; unfold offCopy offRec; omega, hSzS,
          loopIterRegs_of_keep hRgS (fun _ _ => rfl), hWrtS, hOutS⟩
      · have hkLt : k < w.wordCount := Nat.lt_of_le_of_ne hkLe hkEq
        have hLtR : (reg s r11).val < (reg s r15).val := by rw [hr11S, hr15S]; omega
        have st8 := step16_branchLt_true code input hpcS (at_copy subCode h32 (i := 8) (by decide))
          (hPcLt 9 (by decide)) hLtR
        let s9 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s.regs, data := s.data, pc := offCopy subCode.size + 9,
            regs_size := s.regs_size, data_size := s.data_size }
        have hkPay : k < (packedPayload w).size := by rw [packedPayload_size]; exact hkLt
        let wVal : Word bits := (packedPayload w)[k]'hkPay
        have hMem9 : s9.data[(reg s9 r11).val]? = some wVal := by
          change s.data[(reg s r11).val]? = _
          rw [hr11S, hOutS _ (Or.inl (hDisj k hkLt)), hPayAt k hkLt, Array.getElem?_eq_getElem hkPay]
        obtain ⟨s10, st9, pc10, r13_10, keep10, d10⟩ :=
          step16_loadData code input (rfl : s9.pc = offCopy subCode.size + 9)
            (at_copy subCode h32 (i := 9) (by decide)) hMem9 (hPcLt 10 (by decide))
        have hr12_10 : (reg s10 r12).val = forestArenaBase loopBase n m + forestUsed + k := by
          rw [keep10 _ (by decide), show reg s9 r12 = reg s r12 from rfl, hr12S]
        have hBnd10 : (reg s10 r12).val < s10.data.size := by rw [hr12_10, d10]; change _ < s.data.size; omega
        obtain ⟨s11, st10, pc11, regs11, d11⟩ :=
          step16_storeData code input pc10 (at_copy subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide)) hBnd10
        have reg11 : ∀ r : Fin 16, reg s11 r = reg s10 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs11 r
        have hOne10 : (reg s10 r1).val = 1 := by
          rw [keep10 _ (by decide)]; exact hRgS.entry.consts.one
        have hr11_10 : (reg s10 r11).val = loopSubWorkBase loopBase n m + k := by
          rw [keep10 _ (by decide), show reg s9 r11 = reg s r11 from rfl, hr11S]
        obtain ⟨s12, st11, pc12, r11_12, keep12, d12⟩ :=
          step16_add code input pc11 (at_copy subCode h32 (i := 11) (by decide)) (hPcLt 12 (by decide))
        have r11v12 : (reg s12 r11).val = loopSubWorkBase loopBase n m + (k + 1) := by
          rw [r11_12, add_no_wrap]
          · rw [reg11, reg11, hr11_10, hOne10]; omega
          · rw [reg11, reg11, hr11_10, hOne10]
            unfold loopSubWorkBase rawInputCap loopWorkWords at *; omega
        have hr12_12 : (reg s12 r12).val = forestArenaBase loopBase n m + forestUsed + k := by
          rw [keep12 _ (by decide), reg11, hr12_10]
        have hOne12 : (reg s12 r1).val = 1 := by
          rw [keep12 _ (by decide), reg11, hOne10]
        obtain ⟨s13, st12, pc13, r12_13, keep13, d13⟩ :=
          step16_add code input pc12 (at_copy subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
        have r12v13 : (reg s13 r12).val = forestArenaBase loopBase n m + forestUsed + (k + 1) := by
          rw [r12_13, add_no_wrap] <;> rw [hr12_12, hOne12] <;> omega
        have st13 := step16_goto code input pc13 (at_copy subCode h32 (i := 13) (by decide))
          (hPcLt 8 (by decide))
        let s14 : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s13.regs, data := s13.data, pc := offCopy subCode.size + 8,
            regs_size := s13.regs_size, data_size := s13.data_size }
        have hStIter : Steps code input 6 s s14 :=
          Steps.cons st8 (Steps.cons st9 (Steps.cons st10 (Steps.cons st11 (Steps.cons st12
            (Steps.cons st13 (Steps.zero s14))))))
        have hData14 : s14.data = s10.data.set (reg s10 r12).val (reg s10 r13) hBnd10 := by
          change s13.data = _; rw [d13, d12, d11]
        refine Or.inr ⟨k + 1, s14, 6, by omega, by omega, hStIter, by omega, rfl,
          by rw [hData14, Array.size_set, d10, hSzS],
          loopIterRegs_of_keep hRgS (fun r hr => ?_), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
          have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
          have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
          exact (keep13 _ h12).trans ((keep12 _ h11).trans ((reg11 r).trans (keep10 _ h13)))
        · exact (congrArg Fin.val (keep13 _ (by decide))).trans r11v12
        · exact r12v13
        · exact (congrArg Fin.val ((keep13 _ (by decide)).trans ((keep12 _ (by decide)).trans
            ((reg11 r14).trans (keep10 _ (by decide)))))).trans hr14S
        · exact (congrArg Fin.val ((keep13 _ (by decide)).trans ((keep12 _ (by decide)).trans
            ((reg11 r15).trans (keep10 _ (by decide)))))).trans hr15S
        · intro j hj
          rw [hData14]
          by_cases hjEq : j = k
          · subst hjEq
            rw [mem_set_same s10.data hr12_10 hBnd10, Array.getElem?_eq_getElem hkPay]
            exact congrArg some r13_10
          · rw [mem_set_ne s10.data hBnd10 (by rw [hr12_10]; omega), d10]
            change s.data[forestArenaBase loopBase n m + forestUsed + j]? = _
            exact hWrtS j (by omega)
        · intro addr ha
          rw [hData14, mem_set_ne s10.data hBnd10 (by rw [hr12_10]; omega), d10]
          change s.data[addr]? = s₀.data[addr]?
          exact hOutS addr (by omega))
    w.wordCount 0 s8 (by omega)
    ⟨Nat.zero_le _, pc8, by rw [hD8, hDataSz], hRg8,
      by simpa only [Nat.add_zero] using hr11_8,
      by simpa only [Nat.add_zero] using hr12_8, hr14_8, hr15_8,
      fun j hj => by omega, fun addr _ => by rw [hD8]⟩
  obtain ⟨_, t, kLoop, hkLoop, hStLoop, hPcT, hSzT, hRgT, hWrtT, hOutT⟩ := hLoop
  exact ⟨t, 8 + kLoop, by omega, hStPre.append hStLoop, hPcT, hSzT, hRgT, hWrtT, hOutT⟩

private theorem recordPtrsA_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed : Nat}
    (hd : d < n) (hArenaLe : forestUsed ≤ 38 * n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offRec subCode.size) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hPtrsPtr : (s₀.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m))
    (hArenaPtr : (s₀.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m)) :
    let dictPtr := forestArenaBase loopBase n m + forestUsed
    ∃ s15, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 15 s₀ s15 ∧
      s15.pc = offRec subCode.size + 15 ∧ s15.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s15 ∧
      (reg s15 r11).val = dictPtr ∧
      (reg s15 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 1 ∧
      (reg s15 r15).val = loopSubStateBase loopBase n m ∧
      (s15.data[ownerForestPtrsBase loopBase n m + 6 * d]?).map Fin.val = some dictPtr ∧
      (∀ addr, addr ≠ ownerForestPtrsBase loopBase n m + 6 * d → s15.data[addr]? = s₀.data[addr]?) := by
  intro dictPtr
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 16 → offRec subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offRec; omega
  have hOne : (reg s₀ rOne).val = 1 := hRegs.entry.consts.one
  have hdVal : (reg s₀ r9).val = d := hRegs.dVal
  have hUsed : (reg s₀ r10).val = forestUsed := hRegs.usedVal
  have hBnd : ownerForestPtrsBase loopBase n m + 6 * n ≤ workCap ∧
      forestArenaBase loopBase n m + forestUsed < 2 ^ bits ∧
      loopSubStateBase loopBase n m + 16 ≤ workCap ∧ 6 * n < 2 ^ bits := by
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *
    omega
  obtain ⟨s1, st0, pc1, r12_1, keep1, d1⟩ :=
    step16_imm code input hpc (at_rec subCode h32 (i := 0) (by decide)) (hPcLt 1 (by decide))
  have hMemSt : s1.data[(reg s1 r12).val]? = some ⟨loopSubStateBase loopBase n m, by omega⟩ := by
    rw [d1, show (reg s1 r12).val = statePtrAddr by rw [r12_1]; rfl]; exact mem_word_of_map hStPtr _
  obtain ⟨s2, st1, pc2, r15_2, keep2, d2⟩ :=
    step16_loadData code input pc1 (at_rec subCode h32 (i := 1) (by decide)) hMemSt (hPcLt 2 (by decide))
  obtain ⟨s3, st2, pc3, r12_3, keep3, d3⟩ :=
    step16_imm code input pc2 (at_rec subCode h32 (i := 2) (by decide)) (hPcLt 3 (by decide))
  obtain ⟨s4, st3, pc4, r12_4, keep4, d4⟩ :=
    step16_add code input pc3 (at_rec subCode h32 (i := 3) (by decide)) (hPcLt 4 (by decide))
  have r12v4 : (reg s4 r12).val = loopSubStateBase loopBase n m + 14 := by
    rw [r12_4, add_no_wrap]
    · rw [keep3 _ (by decide), r15_2, r12_3]; rfl
    · rw [keep3 _ (by decide), r15_2, r12_3]; change loopSubStateBase loopBase n m + 14 < 2 ^ bits; omega
  have hMemPtrs : s4.data[(reg s4 r12).val]? = some ⟨ownerForestPtrsBase loopBase n m, by omega⟩ := by
    rw [r12v4, d4, d3, d2, d1]; exact mem_word_of_map hPtrsPtr _
  obtain ⟨s5, st4, pc5, r14_5, keep5, d5⟩ :=
    step16_loadData code input pc4 (at_rec subCode h32 (i := 4) (by decide)) hMemPtrs (hPcLt 5 (by decide))
  have hdeq5 : (reg s5 r9).val = d := by
    rw [keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hdVal]
  obtain ⟨s6, st5, pc6, r12_6, keep6, d6⟩ :=
    step16_add code input pc5 (at_rec subCode h32 (i := 5) (by decide)) (hPcLt 6 (by decide))
  have r12v6 : (reg s6 r12).val = 2 * d := by rw [r12_6, add_no_wrap] <;> rw [hdeq5] <;> omega
  obtain ⟨s7, st6, pc7, r13_7, keep7, d7⟩ :=
    step16_add code input pc6 (at_rec subCode h32 (i := 6) (by decide)) (hPcLt 7 (by decide))
  have r13v7 : (reg s7 r13).val = 4 * d := by rw [r13_7, add_no_wrap] <;> rw [r12v6] <;> omega
  obtain ⟨s8, st7, pc8, r12_8, keep8, d8⟩ :=
    step16_add code input pc7 (at_rec subCode h32 (i := 7) (by decide)) (hPcLt 8 (by decide))
  have r12v8 : (reg s8 r12).val = 6 * d := by
    rw [r12_8, add_no_wrap] <;> rw [keep7 _ (by decide), r12v6, r13v7] <;> omega
  have r14eq8 : (reg s8 r14).val = ownerForestPtrsBase loopBase n m := by
    rw [keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), r14_5]
  obtain ⟨s9, st8, pc9, r14_9, keep9, d9⟩ :=
    step16_add code input pc8 (at_rec subCode h32 (i := 8) (by decide)) (hPcLt 9 (by decide))
  have r14v9 : (reg s9 r14).val = ownerForestPtrsBase loopBase n m + 6 * d := by
    rw [r14_9, add_no_wrap] <;> rw [r14eq8, r12v8] <;> omega
  obtain ⟨s10, st9, pc10, r12_10, keep10, d10⟩ :=
    step16_imm code input pc9 (at_rec subCode h32 (i := 9) (by decide)) (hPcLt 10 (by decide))
  have r15eq10 : (reg s10 r15).val = loopSubStateBase loopBase n m := by
    rw [keep10 _ (by decide), keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide),
      keep6 _ (by decide), keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), r15_2]
  obtain ⟨s11, st10, pc11, r12_11, keep11, d11⟩ :=
    step16_add code input pc10 (at_rec subCode h32 (i := 10) (by decide)) (hPcLt 11 (by decide))
  have r12v11 : (reg s11 r12).val = loopSubStateBase loopBase n m + 15 := by
    rw [r12_11, add_no_wrap]
    · rw [r15eq10, r12_10]; rfl
    · rw [r15eq10, r12_10]; change loopSubStateBase loopBase n m + 15 < 2 ^ bits; omega
  have hMemAr : s11.data[(reg s11 r12).val]? = some ⟨forestArenaBase loopBase n m, by omega⟩ := by
    rw [r12v11, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]; exact mem_word_of_map hArenaPtr _
  obtain ⟨s12, st11, pc12, r11_12, keep12, d12⟩ :=
    step16_loadData code input pc11 (at_rec subCode h32 (i := 11) (by decide)) hMemAr (hPcLt 12 (by decide))
  have hUsed12 : (reg s12 r10).val = forestUsed := by
    rw [keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide), keep9 _ (by decide),
      keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide), keep5 _ (by decide),
      keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide), keep1 _ (by decide), hUsed]
  obtain ⟨s13, st12, pc13, r11_13, keep13, d13⟩ :=
    step16_add code input pc12 (at_rec subCode h32 (i := 12) (by decide)) (hPcLt 13 (by decide))
  have r11v13 : (reg s13 r11).val = dictPtr := by
    rw [r11_13, add_no_wrap] <;> rw [r11_12, hUsed12] <;> dsimp only [dictPtr] <;> omega
  have r14eq13 : (reg s13 r14).val = ownerForestPtrsBase loopBase n m + 6 * d := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide), r14v9]
  have hData13 : s13.data = s₀.data := by
    rw [d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]
  have hBnd13 : (reg s13 r14).val < s13.data.size := by rw [r14eq13, hData13, hDataSz]; omega
  obtain ⟨s14, st13, pc14, regs14, d14⟩ :=
    step16_storeData code input pc13 (at_rec subCode h32 (i := 13) (by decide)) (hPcLt 14 (by decide)) hBnd13
  have reg14 : ∀ r : Fin 16, reg s14 r = reg s13 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs14 r
  have h1eq13 : (reg s13 r1).val = 1 := by
    rw [keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), keep10 _ (by decide),
      keep9 _ (by decide), keep8 _ (by decide), keep7 _ (by decide), keep6 _ (by decide),
      keep5 _ (by decide), keep4 _ (by decide), keep3 _ (by decide), keep2 _ (by decide),
      keep1 _ (by decide)]; exact hOne
  obtain ⟨s15, st14, pc15, r14_15, keep15, d15⟩ :=
    step16_add code input pc14 (at_rec subCode h32 (i := 14) (by decide)) (hPcLt 15 (by decide))
  have r14v15 : (reg s15 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 1 := by
    rw [r14_15, add_no_wrap] <;> rw [reg14, reg14, r14eq13, h1eq13] <;> omega
  have hSteps : Steps code input 15 s₀ s15 :=
    Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4
      (Steps.cons st5 (Steps.cons st6 (Steps.cons st7 (Steps.cons st8 (Steps.cons st9
        (Steps.cons st10 (Steps.cons st11 (Steps.cons st12 (Steps.cons st13
          (Steps.cons st14 (Steps.zero s15)))))))))))))))
  refine ⟨s15, hSteps, pc15, by rw [d15, d14, Array.size_set, hData13, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_,
    by rw [keep15 _ (by decide), reg14, r11v13], r14v15,
    by rw [keep15 _ (by decide), reg14, keep13 _ (by decide), keep12 _ (by decide), keep11 _ (by decide), r15eq10],
    ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    rw [keep15 _ h14, reg14, keep13 _ h11, keep12 _ h11, keep11 _ h12, keep10 _ h12,
      keep9 _ h14, keep8 _ h12, keep7 _ h13, keep6 _ h12, keep5 _ h14, keep4 _ h12,
      keep3 _ h12, keep2 _ h15, keep1 _ h12]
  · rw [d15, d14, mem_set_same s13.data r14eq13 hBnd13, Option.map_some, r11v13]
  · intro addr ha
    rw [d15, d14, mem_set_ne s13.data hBnd13 (by rw [r14eq13]; exact ha), hData13]

private theorem recordPtrsB_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed D n_d : Nat}
    (hd : d < n) (_hn_d : n_d ≤ n) (hD : 1 + 3 * D ≤ 19 * n_d)
    (hArenaLe : forestUsed + (1 + 3 * D + 2 * (n_d + 1)) ≤ 38 * n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s15 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s15.pc = offRec subCode.size + 15) (hDataSz : s15.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s15)
    (hr11 : (reg s15 r11).val = forestArenaBase loopBase n m + forestUsed)
    (hr14 : (reg s15 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 1)
    (hr15 : (reg s15 r15).val = loopSubStateBase loopBase n m)
    (hDatPtr : (s15.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hDat0 : (s15.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D)
    (hNdAt : (s15.data[loopBase]?).map Fin.val = some n_d) :
    let dictPtr := forestArenaBase loopBase n m + forestUsed
    let backFstPtr := dictPtr + (1 + 3 * D)
    let backSndPtr := backFstPtr + (n_d + 1)
    let labelsPtr := backSndPtr + (n_d + 1)
    ∃ s30, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 15 s15 s30 ∧
      s30.pc = offRec subCode.size + 30 ∧ s30.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s30 ∧
      (reg s30 r11).val = labelsPtr ∧ (reg s30 r12).val = n_d ∧
      (reg s30 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 3 ∧
      (reg s30 r15).val = loopSubStateBase loopBase n m ∧
      (s30.data[ownerForestPtrsBase loopBase n m + 6 * d + 1]?).map Fin.val = some backFstPtr ∧
      (s30.data[ownerForestPtrsBase loopBase n m + 6 * d + 2]?).map Fin.val = some backSndPtr ∧
      (s30.data[ownerForestPtrsBase loopBase n m + 6 * d + 3]?).map Fin.val = some labelsPtr ∧
      (∀ addr, (addr < ownerForestPtrsBase loopBase n m + 6 * d + 1 ∨
          ownerForestPtrsBase loopBase n m + 6 * d + 4 ≤ addr) →
        s30.data[addr]? = s15.data[addr]?) := by
  intro dictPtr backFstPtr backSndPtr labelsPtr
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 31 → offRec subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offRec; omega
  have hOne : (reg s15 rOne).val = 1 := hRegs.entry.consts.one
  have hL : (reg s15 r8).val = loopBase := hRegs.entry.loopBaseVal
  have hBnd : ownerForestPtrsBase loopBase n m + 6 * n ≤ workCap ∧
      labelsPtr < 2 ^ bits ∧ loopSubWorkBase loopBase n m < 2 ^ bits := by
    dsimp only [labelsPtr, backSndPtr, backFstPtr, dictPtr]
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *
    omega
  have hMemPtr : s15.data[(reg s15 r1).val]? = some ⟨loopSubWorkBase loopBase n m, by omega⟩ := by
    rw [show (reg s15 r1).val = dataPtrAddr from hOne]; exact mem_word_of_map hDatPtr _
  obtain ⟨s16, st15, pc16, r12_16, keep16, d16⟩ :=
    step16_loadData code input hpc (at_rec subCode h32 (i := 15) (by decide)) hMemPtr (hPcLt 16 (by decide))
  have hMemD : s16.data[(reg s16 r12).val]? = some ⟨D, by omega⟩ := by
    rw [d16, r12_16]; exact mem_word_of_map hDat0 _
  obtain ⟨s17, st16, pc17, r12_17, keep17, d17⟩ :=
    step16_loadData code input pc16 (at_rec subCode h32 (i := 16) (by decide)) hMemD (hPcLt 17 (by decide))
  obtain ⟨s18, st17, pc18, r13_18, keep18, d18⟩ :=
    step16_add code input pc17 (at_rec subCode h32 (i := 17) (by decide)) (hPcLt 18 (by decide))
  have r13v18 : (reg s18 r13).val = 2 * D := by rw [r13_18, add_no_wrap] <;> rw [r12_17] <;> dsimp only <;> omega
  obtain ⟨s19, st18, pc19, r13_19, keep19, d19⟩ :=
    step16_add code input pc18 (at_rec subCode h32 (i := 18) (by decide)) (hPcLt 19 (by decide))
  have r13v19 : (reg s19 r13).val = 3 * D := by
    rw [r13_19, add_no_wrap] <;> rw [r13v18, keep18 _ (by decide), r12_17] <;> dsimp only <;> omega
  have h1eq19 : (reg s19 r1).val = 1 := by
    rw [keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide)]; exact hOne
  obtain ⟨s20, st19, pc20, r13_20, keep20, d20⟩ :=
    step16_add code input pc19 (at_rec subCode h32 (i := 19) (by decide)) (hPcLt 20 (by decide))
  have r13v20 : (reg s20 r13).val = 3 * D + 1 := by
    rw [r13_20, add_no_wrap] <;> rw [r13v19, h1eq19] <;> omega
  have r11eq20 : (reg s20 r11).val = dictPtr := by
    rw [keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide),
      keep16 _ (by decide), hr11]
  obtain ⟨s21, st20, pc21, r11_21, keep21, d21⟩ :=
    step16_add code input pc20 (at_rec subCode h32 (i := 20) (by decide)) (hPcLt 21 (by decide))
  have r11v21 : (reg s21 r11).val = backFstPtr := by
    rw [r11_21, add_no_wrap]
    · rw [r11eq20, r13v20]; dsimp only [backFstPtr]; omega
    · rw [r11eq20, r13v20]; dsimp only [backFstPtr, dictPtr] at *; omega
  have r14eq21 : (reg s21 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 1 := by
    rw [keep21 _ (by decide), keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide),
      keep17 _ (by decide), keep16 _ (by decide), hr14]
  have hData21 : s21.data = s15.data := by rw [d21, d20, d19, d18, d17, d16]
  have hBnd21 : (reg s21 r14).val < s21.data.size := by rw [r14eq21, hData21, hDataSz]; omega
  obtain ⟨s22, st21, pc22, regs22, d22⟩ :=
    step16_storeData code input pc21 (at_rec subCode h32 (i := 21) (by decide)) (hPcLt 22 (by decide)) hBnd21
  have reg22 : ∀ r : Fin 16, reg s22 r = reg s21 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs22 r
  have h1eq21 : (reg s21 r1).val = 1 := by
    rw [keep21 _ (by decide), keep20 _ (by decide), h1eq19]
  obtain ⟨s23, st22, pc23, r14_23, keep23, d23⟩ :=
    step16_add code input pc22 (at_rec subCode h32 (i := 22) (by decide)) (hPcLt 23 (by decide))
  have r14v23 : (reg s23 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 2 := by
    rw [r14_23, add_no_wrap] <;> rw [reg22, reg22, r14eq21, h1eq21] <;> omega
  have hMemNd : s23.data[(reg s23 r8).val]? = some ⟨n_d, by omega⟩ := by
    rw [d23, d22, mem_set_ne s21.data hBnd21 (by
        rw [r14eq21, keep23 _ (by decide), reg22, keep21 _ (by decide), keep20 _ (by decide),
          keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), hL]
        unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
          loopSubWorkBase rawInputCap rawWorkCap at *; omega),
      hData21, keep23 _ (by decide), reg22, keep21 _ (by decide), keep20 _ (by decide),
      keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide), keep16 _ (by decide), hL]
    exact mem_word_of_map hNdAt _
  obtain ⟨s24, st23, pc24, r12_24, keep24, d24⟩ :=
    step16_loadData code input pc23 (at_rec subCode h32 (i := 23) (by decide)) hMemNd (hPcLt 24 (by decide))
  have h1eq24 : (reg s24 r1).val = 1 := by rw [keep24 _ (by decide), keep23 _ (by decide), reg22, h1eq21]
  obtain ⟨s25, st24, pc25, r13_25, keep25, d25⟩ :=
    step16_add code input pc24 (at_rec subCode h32 (i := 24) (by decide)) (hPcLt 25 (by decide))
  have r13v25 : (reg s25 r13).val = n_d + 1 := by
    rw [r13_25, add_no_wrap] <;> rw [r12_24, h1eq24] <;> dsimp only <;> omega
  have r11eq25 : (reg s25 r11).val = backFstPtr := by
    rw [keep25 _ (by decide), keep24 _ (by decide), keep23 _ (by decide), reg22, r11v21]
  obtain ⟨s26, st25, pc26, r11_26, keep26, d26⟩ :=
    step16_add code input pc25 (at_rec subCode h32 (i := 25) (by decide)) (hPcLt 26 (by decide))
  have r11v26 : (reg s26 r11).val = backSndPtr := by
    rw [r11_26, add_no_wrap] <;> rw [r11eq25, r13v25] <;> (try dsimp only [backSndPtr]) <;> omega
  have r14eq26 : (reg s26 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 2 := by
    rw [keep26 _ (by decide), keep25 _ (by decide), keep24 _ (by decide), r14v23]
  have hData26 : s26.data = s22.data := by rw [d26, d25, d24, d23]
  have hBnd26 : (reg s26 r14).val < s26.data.size := by
    rw [r14eq26, hData26, d22, Array.size_set, hData21, hDataSz]; omega
  obtain ⟨s27, st26, pc27, regs27, d27⟩ :=
    step16_storeData code input pc26 (at_rec subCode h32 (i := 26) (by decide)) (hPcLt 27 (by decide)) hBnd26
  have reg27 : ∀ r : Fin 16, reg s27 r = reg s26 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs27 r
  have h1eq26 : (reg s26 r1).val = 1 := by rw [keep26 _ (by decide), keep25 _ (by decide), h1eq24]
  obtain ⟨s28, st27, pc28, r14_28, keep28, d28⟩ :=
    step16_add code input pc27 (at_rec subCode h32 (i := 27) (by decide)) (hPcLt 28 (by decide))
  have r14v28 : (reg s28 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 3 := by
    rw [r14_28, add_no_wrap] <;> rw [reg27, reg27, r14eq26, h1eq26] <;> omega
  have r13eq28 : (reg s28 r13).val = n_d + 1 := by
    rw [keep28 _ (by decide), reg27, keep26 _ (by decide), r13v25]
  obtain ⟨s29, st28, pc29, r11_29, keep29, d29⟩ :=
    step16_add code input pc28 (at_rec subCode h32 (i := 28) (by decide)) (hPcLt 29 (by decide))
  have r11v29 : (reg s29 r11).val = labelsPtr := by
    rw [r11_29, add_no_wrap] <;> rw [keep28 _ (by decide), reg27, r11v26, r13eq28] <;>
      (try dsimp only [labelsPtr]) <;> omega
  have r14eq29 : (reg s29 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 3 := by
    rw [keep29 _ (by decide), r14v28]
  have hData29 : s29.data = s27.data := by rw [d29, d28]
  have hBnd29 : (reg s29 r14).val < s29.data.size := by
    rw [r14eq29, hData29, d27, Array.size_set, hData26, d22, Array.size_set, hData21, hDataSz]; omega
  obtain ⟨s30, st29, pc30, regs30, d30⟩ :=
    step16_storeData code input pc29 (at_rec subCode h32 (i := 29) (by decide)) (hPcLt 30 (by decide)) hBnd29
  have reg30 : ∀ r : Fin 16, reg s30 r = reg s29 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs30 r
  have hSteps : Steps code input 15 s15 s30 :=
    Steps.cons st15 (Steps.cons st16 (Steps.cons st17 (Steps.cons st18 (Steps.cons st19
      (Steps.cons st20 (Steps.cons st21 (Steps.cons st22 (Steps.cons st23 (Steps.cons st24
        (Steps.cons st25 (Steps.cons st26 (Steps.cons st27 (Steps.cons st28
          (Steps.cons st29 (Steps.zero s30)))))))))))))))
  refine ⟨s30, hSteps, pc30,
    by rw [d30, Array.size_set, hData29, d27, Array.size_set, hData26, d22, Array.size_set, hData21, hDataSz],
    loopIterRegs_of_keep hRegs fun r hr => ?_,
    by rw [reg30, r11v29],
    by rw [reg30, keep29 _ (by decide), keep28 _ (by decide), reg27, keep26 _ (by decide),
      keep25 _ (by decide), r12_24],
    by rw [reg30, r14eq29],
    by rw [reg30, keep29 _ (by decide), keep28 _ (by decide), reg27, keep26 _ (by decide),
      keep25 _ (by decide), keep24 _ (by decide), keep23 _ (by decide), reg22, keep21 _ (by decide),
      keep20 _ (by decide), keep19 _ (by decide), keep18 _ (by decide), keep17 _ (by decide),
      keep16 _ (by decide), hr15],
    ?_, ?_, ?_, ?_⟩
  · have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    rw [reg30, keep29 _ h11, keep28 _ h14, reg27, keep26 _ h11, keep25 _ h13, keep24 _ h12,
      keep23 _ h14, reg22, keep21 _ h11, keep20 _ h13, keep19 _ h13, keep18 _ h13,
      keep17 _ h12, keep16 _ h12]
  · rw [d30, mem_set_ne s29.data hBnd29 (by rw [r14eq29]; omega), hData29,
      d27, mem_set_ne s26.data hBnd26 (by rw [r14eq26]; omega), hData26,
      d22, mem_set_same s21.data r14eq21 hBnd21, Option.map_some, r11v21]
  · rw [d30, mem_set_ne s29.data hBnd29 (by rw [r14eq29]; omega), hData29,
      d27, mem_set_same s26.data r14eq26 hBnd26, Option.map_some, r11v26]
  · rw [d30, mem_set_same s29.data r14eq29 hBnd29, Option.map_some, r11v29]
  · intro addr ha
    rw [d30, mem_set_ne s29.data hBnd29 (by rw [r14eq29]; omega), hData29,
      d27, mem_set_ne s26.data hBnd26 (by rw [r14eq26]; omega), hData26,
      d22, mem_set_ne s21.data hBnd21 (by rw [r14eq21]; omega), hData21]

private theorem recordPtrsC_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed D n_d N_d wc : Nat}
    (hd : d < n) (hWcEq : wc = 3 * D + 3 * n_d + 2 * N_d + 3) (hArenaFit : forestUsed + wc ≤ 38 * n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s30 : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s30.pc = offRec subCode.size + 30) (hDataSz : s30.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s30)
    (hr11 : (reg s30 r11).val = forestArenaBase loopBase n m + forestUsed + (1 + 3 * D) + (n_d + 1) + (n_d + 1))
    (hr12 : (reg s30 r12).val = n_d)
    (hr14 : (reg s30 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 3)
    (hr15 : (reg s30 r15).val = loopSubStateBase loopBase n m)
    (hMemSt0 : s30.data[loopSubStateBase loopBase n m]? = some ⟨N_d, by
        unfold loopWorkWords at hFit; omega⟩)
    (hMemSt1 : s30.data[loopSubStateBase loopBase n m + 1]? = some ⟨wc, by
        unfold loopWorkWords at hFit; omega⟩) :
    let dictPtr := forestArenaBase loopBase n m + forestUsed
    let backFstPtr := dictPtr + (1 + 3 * D)
    let backSndPtr := backFstPtr + (n_d + 1)
    let labelsPtr := backSndPtr + (n_d + 1)
    let fEntryPtr := labelsPtr + n_d
    let fStopPtr := fEntryPtr + N_d
    ∃ s42, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 12 s30 s42 ∧
      s42.pc = offHdr ∧ s42.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d + 1) (forestUsed + wc) s42 ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 4]?).map Fin.val = some fEntryPtr ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 5]?).map Fin.val = some fStopPtr ∧
      (∀ addr, (addr < ownerForestPtrsBase loopBase n m + 6 * d + 4 ∨
          ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr) →
        s42.data[addr]? = s30.data[addr]?) := by
  intro dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 42 → offRec subCode.size + c < code.size := by
    intro c hc; rw [hSz]; unfold offRec; omega
  have hOne : (reg s30 rOne).val = 1 := hRegs.entry.consts.one
  have hdVal : (reg s30 r9).val = d := hRegs.dVal
  have hUsed : (reg s30 r10).val = forestUsed := hRegs.usedVal
  have hBnd : ownerForestPtrsBase loopBase n m + 6 * n ≤ workCap ∧
      fStopPtr < 2 ^ bits ∧ loopSubStateBase loopBase n m + 1 < 2 ^ bits ∧
      forestUsed + wc < 2 ^ bits := by
    dsimp only [fStopPtr, fEntryPtr, labelsPtr, backSndPtr, backFstPtr, dictPtr]
    unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *
    omega
  obtain ⟨s31, st30, pc31, r14_31, keep31, d31⟩ :=
    step16_add code input hpc (at_rec subCode h32 (i := 30) (by decide)) (hPcLt 31 (by decide))
  have r14v31 : (reg s31 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 4 := by
    rw [r14_31, add_no_wrap] <;> rw [hr14, hOne] <;> omega
  have r11eq31 : (reg s31 r11).val = labelsPtr := by rw [keep31 _ (by decide), hr11]
  have r12eq31 : (reg s31 r12).val = n_d := by rw [keep31 _ (by decide), hr12]
  obtain ⟨s32, st31, pc32, r11_32, keep32, d32⟩ :=
    step16_add code input pc31 (at_rec subCode h32 (i := 31) (by decide)) (hPcLt 32 (by decide))
  have r11v32 : (reg s32 r11).val = fEntryPtr := by
    rw [r11_32, add_no_wrap] <;> rw [r11eq31, r12eq31] <;> (try dsimp only [fEntryPtr]) <;> omega
  have r14eq32 : (reg s32 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 4 := by
    rw [keep32 _ (by decide), r14v31]
  have hData32 : s32.data = s30.data := by rw [d32, d31]
  have hBnd32 : (reg s32 r14).val < s32.data.size := by rw [r14eq32, hData32, hDataSz]; omega
  obtain ⟨s33, st32, pc33, regs33, d33⟩ :=
    step16_storeData code input pc32 (at_rec subCode h32 (i := 32) (by decide)) (hPcLt 33 (by decide)) hBnd32
  have reg33 : ∀ r : Fin 16, reg s33 r = reg s32 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs33 r
  have h1eq32 : (reg s32 r1).val = 1 := by
    rw [keep32 _ (by decide), keep31 _ (by decide)]; exact hOne
  obtain ⟨s34, st33, pc34, r14_34, keep34, d34⟩ :=
    step16_add code input pc33 (at_rec subCode h32 (i := 33) (by decide)) (hPcLt 34 (by decide))
  have r14v34 : (reg s34 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 5 := by
    rw [r14_34, add_no_wrap] <;> rw [reg33, reg33, r14eq32, h1eq32] <;> omega
  have r15eq34 : (reg s34 r15).val = loopSubStateBase loopBase n m := by
    rw [keep34 _ (by decide), reg33, keep32 _ (by decide), keep31 _ (by decide), hr15]
  have hMemSt0_34 : s34.data[(reg s34 r15).val]? = some ⟨N_d, by omega⟩ := by
    rw [r15eq34, d34, d33, mem_set_ne s32.data hBnd32 (by
        rw [r14eq32]
        unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
          loopSubWorkBase rawInputCap rawWorkCap at *; omega),
      hData32]
    exact hMemSt0
  obtain ⟨s35, st34, pc35, r13_35, keep35, d35⟩ :=
    step16_loadData code input pc34 (at_rec subCode h32 (i := 34) (by decide)) hMemSt0_34 (hPcLt 35 (by decide))
  have r11eq35 : (reg s35 r11).val = fEntryPtr := by
    rw [keep35 _ (by decide), keep34 _ (by decide), reg33, r11v32]
  obtain ⟨s36, st35, pc36, r11_36, keep36, d36⟩ :=
    step16_add code input pc35 (at_rec subCode h32 (i := 35) (by decide)) (hPcLt 36 (by decide))
  have r11v36 : (reg s36 r11).val = fStopPtr := by
    rw [r11_36, add_no_wrap] <;> rw [r11eq35, r13_35] <;> dsimp only [fStopPtr] <;> omega
  have r14eq36 : (reg s36 r14).val = ownerForestPtrsBase loopBase n m + 6 * d + 5 := by
    rw [keep36 _ (by decide), keep35 _ (by decide), r14v34]
  have hData36 : s36.data = s33.data := by rw [d36, d35, d34]
  have hBnd36 : (reg s36 r14).val < s36.data.size := by
    rw [r14eq36, hData36, d33, Array.size_set, hData32, hDataSz]; omega
  obtain ⟨s37, st36, pc37, regs37, d37⟩ :=
    step16_storeData code input pc36 (at_rec subCode h32 (i := 36) (by decide)) (hPcLt 37 (by decide)) hBnd36
  have reg37 : ∀ r : Fin 16, reg s37 r = reg s36 r := fun r => PaperB.RamDagReach.reg_eq_of_regs_eq regs37 r
  have h1eq36 : (reg s36 r1).val = 1 := by
    rw [keep36 _ (by decide), keep35 _ (by decide), keep34 _ (by decide), reg33, h1eq32]
  have r15eq37 : (reg s37 r15).val = loopSubStateBase loopBase n m := by
    rw [reg37, keep36 _ (by decide), keep35 _ (by decide), r15eq34]
  obtain ⟨s38, st37, pc38, r15_38, keep38, d38⟩ :=
    step16_add code input pc37 (at_rec subCode h32 (i := 37) (by decide)) (hPcLt 38 (by decide))
  have r15v38 : (reg s38 r15).val = loopSubStateBase loopBase n m + 1 := by
    rw [r15_38, add_no_wrap] <;> rw [r15eq37, reg37, h1eq36] <;> omega
  have hMemSt1_38 : s38.data[(reg s38 r15).val]? = some ⟨wc, by omega⟩ := by
    rw [r15v38, d38, d37, mem_set_ne s36.data hBnd36 (by
        rw [r14eq36]
        unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
          loopSubWorkBase rawInputCap rawWorkCap at *; omega),
      hData36, d33, mem_set_ne s32.data hBnd32 (by
        rw [r14eq32]
        unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase
          loopSubWorkBase rawInputCap rawWorkCap at *; omega),
      hData32]
    exact hMemSt1
  obtain ⟨s39, st38, pc39, r12_39, keep39, d39⟩ :=
    step16_loadData code input pc38 (at_rec subCode h32 (i := 38) (by decide)) hMemSt1_38 (hPcLt 39 (by decide))
  have hUsed39 : (reg s39 r10).val = forestUsed := by
    rw [keep39 _ (by decide), keep38 _ (by decide), reg37, keep36 _ (by decide), keep35 _ (by decide),
      keep34 _ (by decide), reg33, keep32 _ (by decide), keep31 _ (by decide), hUsed]
  obtain ⟨s40, st39, pc40, r10_40, keep40, d40⟩ :=
    step16_add code input pc39 (at_rec subCode h32 (i := 39) (by decide)) (hPcLt 40 (by decide))
  have r10v40 : (reg s40 r10).val = forestUsed + wc := by
    rw [r10_40, add_no_wrap] <;> rw [hUsed39, r12_39] <;> dsimp only <;> omega
  have hd40 : (reg s40 r9).val = d := by
    rw [keep40 _ (by decide), keep39 _ (by decide), keep38 _ (by decide), reg37, keep36 _ (by decide),
      keep35 _ (by decide), keep34 _ (by decide), reg33, keep32 _ (by decide), keep31 _ (by decide), hdVal]
  have h1eq40 : (reg s40 r1).val = 1 := by
    rw [keep40 _ (by decide), keep39 _ (by decide), keep38 _ (by decide), reg37, h1eq36]
  obtain ⟨s41, st40, pc41, r9_41, keep41, d41⟩ :=
    step16_add code input pc40 (at_rec subCode h32 (i := 40) (by decide)) (hPcLt 41 (by decide))
  have r9v41 : (reg s41 r9).val = d + 1 := by
    rw [r9_41, add_no_wrap] <;> rw [hd40, h1eq40] <;> omega
  have st41 := step16_goto code input pc41 (at_rec subCode h32 (i := 41) (by decide)) (by
    rw [hSz]; unfold offHdr; omega)
  let s42 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s41.regs, data := s41.data, pc := offHdr,
      regs_size := s41.regs_size, data_size := s41.data_size }
  have hSteps : Steps code input 12 s30 s42 :=
    Steps.cons st30 (Steps.cons st31 (Steps.cons st32 (Steps.cons st33 (Steps.cons st34
      (Steps.cons st35 (Steps.cons st36 (Steps.cons st37 (Steps.cons st38 (Steps.cons st39
        (Steps.cons st40 (Steps.cons st41 (Steps.zero s42))))))))))))
  have hData42 : s42.data = s37.data := by change s41.data = _; rw [d41, d40, d39, d38]
  refine ⟨s42, hSteps, rfl,
    by rw [hData42, d37, Array.size_set, hData36, d33, Array.size_set, hData32, hDataSz],
    { entry := loopEntryRegs_of_keep hRegs.entry fun r hr => ?_, dVal := ?_, usedVal := ?_ },
    ?_, ?_, ?_⟩
  · have h9 : r ≠ r9 := fun e => absurd hr (by subst e; decide)
    have h10 : r ≠ r10 := fun e => absurd hr (by subst e; decide)
    have h11 : r ≠ r11 := fun e => absurd hr (by subst e; decide)
    have h12 : r ≠ r12 := fun e => absurd hr (by subst e; decide)
    have h13 : r ≠ r13 := fun e => absurd hr (by subst e; decide)
    have h14 : r ≠ r14 := fun e => absurd hr (by subst e; decide)
    have h15 : r ≠ r15 := fun e => absurd hr (by subst e; decide)
    exact (keep41 _ h9).trans ((keep40 _ h10).trans ((keep39 _ h12).trans ((keep38 _ h15).trans
      ((reg37 r).trans ((keep36 _ h11).trans ((keep35 _ h13).trans ((keep34 _ h14).trans
        ((reg33 r).trans ((keep32 _ h11).trans (keep31 _ h14))))))))))
  · exact r9v41
  · rw [show reg s42 r10 = reg s41 r10 from rfl, keep41 _ (by decide), r10v40]
  · rw [hData42, d37, mem_set_ne s36.data hBnd36 (by rw [r14eq36]; omega), hData36,
      d33, mem_set_same s32.data r14eq32 hBnd32, Option.map_some, r11v32]
  · rw [hData42, d37, mem_set_same s36.data r14eq36 hBnd36, Option.map_some, r11v36]
  · intro addr ha
    rw [hData42, d37, mem_set_ne s36.data hBnd36 (by rw [r14eq36]; omega), hData36,
      d33, mem_set_ne s32.data hBnd32 (by rw [r14eq32]; omega), hData32]

private theorem recordPtrs_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed D n_d N_d wc : Nat}
    (hd : d < n) (hn_d : n_d ≤ n) (hD : 1 + 3 * D ≤ 19 * n_d)
    (hWcEq : wc = 3 * D + 3 * n_d + 2 * N_d + 3) (hArenaFit : forestUsed + wc ≤ 38 * n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offRec subCode.size) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hDat0 : (s₀.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D)
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some n_d)
    (hPtrsPtr : (s₀.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m))
    (hArenaPtr : (s₀.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m))
    (hMemSt0 : s₀.data[loopSubStateBase loopBase n m]? = some ⟨N_d, by
        unfold loopWorkWords at hFit; omega⟩)
    (hMemSt1 : s₀.data[loopSubStateBase loopBase n m + 1]? = some ⟨wc, by
        unfold loopWorkWords at hFit; omega⟩) :
    let dictPtr := forestArenaBase loopBase n m + forestUsed
    let backFstPtr := dictPtr + (1 + 3 * D)
    let backSndPtr := backFstPtr + (n_d + 1)
    let labelsPtr := backSndPtr + (n_d + 1)
    let fEntryPtr := labelsPtr + n_d
    let fStopPtr := fEntryPtr + N_d
    ∃ s42, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 42 s₀ s42 ∧
      s42.pc = offHdr ∧ s42.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d + 1) (forestUsed + wc) s42 ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d]?).map Fin.val = some dictPtr ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 1]?).map Fin.val = some backFstPtr ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 2]?).map Fin.val = some backSndPtr ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 3]?).map Fin.val = some labelsPtr ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 4]?).map Fin.val = some fEntryPtr ∧
      (s42.data[ownerForestPtrsBase loopBase n m + 6 * d + 5]?).map Fin.val = some fStopPtr ∧
      (∀ addr, (addr < ownerForestPtrsBase loopBase n m + 6 * d ∨
          ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr) →
        s42.data[addr]? = s₀.data[addr]?) := by
  intro dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
  have hDisjMeta : ∀ addr, (addr = dataPtrAddr ∨ addr = loopSubWorkBase loopBase n m ∨
      addr = loopBase ∨ addr = loopSubStateBase loopBase n m ∨
      addr = loopSubStateBase loopBase n m + 1) →
      addr < ownerForestPtrsBase loopBase n m + 6 * d := by
    intro addr h
    unfold dataPtrAddr ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
      loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *
    omega
  obtain ⟨s15, hStA, pc15, hSz15, hRg15, hr11_15, hr14_15, hr15_15, hP0, hOut15⟩ :=
    recordPtrsA_steps subCode h32 input hd (by omega) hFit hBits hpc hDataSz hRegs hStPtr hPtrsPtr hArenaPtr
  have hDatPtr15 : (s15.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    rw [hOut15 _ (Nat.ne_of_lt (hDisjMeta _ (Or.inl rfl)))]; exact hDatPtr
  have hDat0_15 : (s15.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D := by
    rw [hOut15 _ (Nat.ne_of_lt (hDisjMeta _ (Or.inr (Or.inl rfl))))]; exact hDat0
  have hNd15 : (s15.data[loopBase]?).map Fin.val = some n_d := by
    rw [hOut15 _ (Nat.ne_of_lt (hDisjMeta _ (Or.inr (Or.inr (Or.inl rfl)))))]; exact hNdAt
  obtain ⟨s30, hStB, pc30, hSz30, hRg30, hr11_30, hr12_30, hr14_30, hr15_30, hP1, hP2, hP3, hOut30⟩ :=
    recordPtrsB_steps subCode h32 input hd hn_d hD (by omega) hFit hBits pc15 hSz15 hRg15
      hr11_15 hr14_15 hr15_15 hDatPtr15 hDat0_15 hNd15
  have hMemSt0_30 : s30.data[loopSubStateBase loopBase n m]? = some ⟨N_d, by
      unfold loopWorkWords at hFit; omega⟩ := by
    rw [hOut30 _ (Or.inl (Nat.lt_trans (hDisjMeta _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) (by omega))),
      hOut15 _ (Nat.ne_of_lt (hDisjMeta _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]
    exact hMemSt0
  have hMemSt1_30 : s30.data[loopSubStateBase loopBase n m + 1]? = some ⟨wc, by
      unfold loopWorkWords at hFit; omega⟩ := by
    rw [hOut30 _ (Or.inl (Nat.lt_trans (hDisjMeta _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))) (by omega))),
      hOut15 _ (Nat.ne_of_lt (hDisjMeta _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))]
    exact hMemSt1
  obtain ⟨s42, hStC, pc42, hSz42, hRg42, hP4, hP5, hOut42⟩ :=
    recordPtrsC_steps subCode h32 input (D := D) (n_d := n_d) (N_d := N_d) (wc := wc)
      hd hWcEq hArenaFit hFit hBits pc30 hSz30 hRg30 hr11_30 hr12_30 hr14_30 hr15_30
      hMemSt0_30 hMemSt1_30
  refine ⟨s42, (hStA.append hStB).append hStC, pc42, hSz42, hRg42, ?_, ?_, ?_, ?_, hP4, hP5, fun addr ha => ?_⟩
  · rw [hOut42 _ (Or.inl (by omega)), hOut30 _ (Or.inl (by omega))]; exact hP0
  · rw [hOut42 _ (Or.inl (by omega))]; exact hP1
  · rw [hOut42 _ (Or.inl (by omega))]; exact hP2
  · rw [hOut42 _ (Or.inl (by omega))]; exact hP3
  · rw [hOut42 addr (by omega), hOut30 addr (by omega), hOut15 addr (by omega)]

private theorem L_le_of_le {a b : Nat} (hab : a ≤ b) :
    OracleContract.L a ≤ OracleContract.L b := by
  unfold OracleContract.L
  exact Nat.add_le_add_right ((Nat.le_log2 (by omega)).mpr
    (Nat.le_trans (Nat.log2_self_le (by omega)) (Nat.add_le_add_right hab 1))) 1

private theorem mem_le_sum_nat : ∀ {xs : List Nat} {x : Nat}, x ∈ xs → x ≤ xs.sum
  | [], _ => fun h => nomatch h
  | y :: ys, x => fun h => by
    simp only [List.mem_cons] at h
    rcases h with rfl | hmem
    · simp
    · exact Nat.le_trans (mem_le_sum_nat hmem) (by simp)

private theorem childSlice_succ_le_length {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    1 + (S.childSlice d).length ≤ dense.length := by
  have hSum := S.sum_childLengths
  have hMem : (S.childSlice d).length ∈ List.ofFn (fun j : Fin dense.length => (S.childSlice j).length) :=
    List.mem_ofFn.mpr ⟨d, rfl⟩
  have hLe : (S.childSlice d).length ≤ dense.length - 1 :=
    hSum ▸ mem_le_sum_nat hMem
  have hPos : 0 < dense.length := Nat.lt_of_le_of_lt (Nat.zero_le _) d.isLt
  omega

private theorem subInput_words_get {bits : Nat} (arr : Array (Word bits))
    {base cap j : Nat} (hj : j < cap) (hBnd : base + cap ≤ arr.size) :
    arr[base + j]? = (Array.ofFn (fun i : Fin cap => arr[base + i.val]?.getD 0))[j]? := by
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact hj),
    Array.getElem_ofFn, Array.getElem?_eq_getElem (by omega)]
  rfl

private theorem extract_get0 {α : Type _} (a : Array α) {start stop : Nat}
    (h : 0 < (a.extract start stop).size) (hb : start < a.size) :
    (a.extract start stop)[0]'h = a[start]'hb := by
  rw [Array.getElem_extract]; congr 1

private def mkSubInput {bits inCap workCap : Nat}
    (hsi : inCap ≤ 2 ^ bits) (hsw : workCap ≤ 2 ^ bits)
    (mem : Array (Word bits)) (base : Nat) :
    Input (RamForestProgram.layout bits inCap workCap hsi hsw) :=
  ⟨Array.ofFn (fun i : Fin inCap => mem[base + i.val]?.getD 0), Array.size_ofFn⟩

private theorem mkSubInput_getElem? {bits inCap workCap : Nat}
    (hsi : inCap ≤ 2 ^ bits) (hsw : workCap ≤ 2 ^ bits)
    (mem : Array (Word bits)) {base j : Nat} (hj : j < inCap) (hBnd : base + inCap ≤ mem.size) :
    mem[base + j]? = (mkSubInput hsi hsw mem base).words[j]? :=
  subInput_words_get mem hj hBnd

private def mkSubStart {bits inCap workCap bigInCap bigWorkCap : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : workCap ≤ 2 ^ bits}
    {hi : bigInCap ≤ 2 ^ bits} {hw : bigWorkCap ≤ 2 ^ bits}
    (s : State (layout16 bits bigInCap bigWorkCap hi hw)) (dataBase : Nat) :
    State (RamForestProgram.layout bits inCap workCap hsi hsw) :=
  { regs := Array.ofFn (fun i : Fin 15 => s.regs[i.val]?.getD 0)
    data := Array.ofFn (fun j : Fin workCap => s.data[dataBase + j.val]?.getD 0)
    pc := 0
    regs_size := Array.size_ofFn
    data_size := Array.size_ofFn }

private theorem mkSubStart_regs {bits inCap workCap bigInCap bigWorkCap : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : workCap ≤ 2 ^ bits}
    {hi : bigInCap ≤ 2 ^ bits} {hw : bigWorkCap ≤ 2 ^ bits}
    (s : State (layout16 bits bigInCap bigWorkCap hi hw)) (dataBase : Nat) (i : Fin 15) :
    s.regs[i.val]? = (Phase.initial (mkSubStart (hsi := hsi) (hsw := hsw) s dataBase)).regs[i.val]? := by
  have hi16 : i.val < s.regs.size := by rw [s.regs_size]; change i.val < 16; omega
  change s.regs[i.val]? = (Array.ofFn (fun i : Fin 15 => s.regs[i.val]?.getD 0))[i.val]?
  rw [Array.getElem?_eq_getElem hi16, Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact i.isLt),
    Array.getElem_ofFn, Array.getElem?_eq_getElem hi16]; rfl

private theorem mkSubStart_data {bits inCap workCap bigInCap bigWorkCap : Nat}
    {hsi : inCap ≤ 2 ^ bits} {hsw : workCap ≤ 2 ^ bits}
    {hi : bigInCap ≤ 2 ^ bits} {hw : bigWorkCap ≤ 2 ^ bits}
    (s : State (layout16 bits bigInCap bigWorkCap hi hw)) {dataBase j : Nat}
    (hj : j < workCap) (hBnd : dataBase + workCap ≤ s.data.size) :
    s.data[dataBase + j]? = (Phase.initial (mkSubStart (hsi := hsi) (hsw := hsw) s dataBase)).data[j]? :=
  subInput_words_get s.data hj hBnd

private theorem largeSubRun_lift_aux {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m Q treeBase loopBase : Nat}
    {hsi : rawInputCap m ≤ 2 ^ bits} {hsw : rawWorkCap n m ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (hq : Q = dense.length) (hQn : Q ≤ n) (hm_d : (S.emittedArcs d).length ≤ m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    (Extra : WordColumns bits → Prop)
    (hBuild : ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          Extra w ∧
          run subCode subInput work (Phase.initial subStart) = some ⟨t, work⟩)
    {s23 : State (layout16 bits inputCap workCap hi hw)}
    (pc23 : s23.pc = offRaw) (hSz23 : s23.data.size = workCap)
    (hInPtr : (s23.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase))
    (hDatPtr : (s23.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hSub0 : (s23.data[loopSubInBase loopBase]?).map Fin.val = some (1 + (S.childSlice d).length))
    (hSub1 : (s23.data[loopSubInBase loopBase + 1]?).map Fin.val = some (S.emittedArcs d).length)
    (hSub2 : (s23.data[loopSubInBase loopBase + 2]?).map Fin.val = some 0)
    (hSubArcs : ∀ (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (s23.data[loopSubInBase loopBase + 3 + p]?).map Fin.val = some ea.srcLocal ∧
      (s23.data[loopSubInBase loopBase + 3 + (S.emittedArcs d).length + p]?).map Fin.val = some ea.headLocal) :
    let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
    let n_d := 1 + (S.childSlice d).length
    let m_d := (S.emittedArcs d).length
    ∃ (w : WordColumns bits) (sPost : State (layout16 bits inputCap workCap hi hw)) (mSub : Nat),
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      mSub ≤ 46648 * ((n_d + m_d) * OracleContract.L n ^ 2) ∧
      w.wordCount ≤ rawWorkCap n m ∧
      w.wordCount ≤ 19 * n_d ∧
      1 ≤ w.entry.size ∧
      w.dictionary.size = 1 + 3 * D ∧
      w.back.tagAndFirst.size = n_d + 1 ∧
      w.back.second.size = n_d + 1 ∧
      w.labels.size = n_d ∧
      w.stop.size = w.entry.size ∧
      w.entry.size = 1 + (List.range D).foldl
        (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      Extra w ∧
      Steps code input mSub s23 sPost ∧
      sPost.pc = offPost subCode.size ∧
      sPost.data.extract (loopSubWorkBase loopBase n m)
        (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w ∧
      (∀ addr, (addr < loopSubWorkBase loopBase n m ∨ loopSubStateBase loopBase n m ≤ addr) →
        sPost.data[addr]? = s23.data[addr]?) := by
  intro code n_d m_d
  have hn_d : n_d ≤ n := Nat.le_trans (childSlice_succ_le_length S d) (hq ▸ hQn)
  have hL : OracleContract.L (S.ramQuotient d).vertexCount ≤ OracleContract.L n :=
    L_le_of_le hn_d
  have hCapIn : rawInputCap (S.ramQuotient d).arcCount ≤ rawInputCap m := by
    rw [ramQuotient_arcCount_eq S d]; unfold rawInputCap; omega
  have hInSubFit : loopSubInBase loopBase + rawInputCap m ≤ workCap := by
    unfold loopWorkWords at hFit; unfold loopSubInBase rawInputCap; omega
  have hWorkSubFit : loopSubWorkBase loopBase n m + rawWorkCap n m ≤ workCap := by
    unfold loopWorkWords at hFit; unfold loopSubWorkBase rawInputCap rawWorkCap; omega
  let subL := RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw
  let subInput : Input subL := mkSubInput hsi hsw s23.data (loopSubInBase loopBase)
  have hInSlice : ∀ j < rawInputCap m, s23.data[loopSubInBase loopBase + j]? = subInput.words[j]? :=
    fun j hj => mkSubInput_getElem? hsi hsw s23.data hj (by rw [hSz23]; exact hInSubFit)
  have hRaw : RawQuotientInput subInput (S.ramQuotient d) := by
    refine rawQuotientInput_of_countingSorted S d subInput hCapIn ?_ ?_ ?_ fun p hp => ?_
    · change (subInput.words[0]?).map Fin.val = some n_d
      rw [← hInSlice 0 (by unfold rawInputCap; omega)]; exact hSub0
    · rw [ramQuotient_arcCount_eq S d]
      change (subInput.words[1]?).map Fin.val = some m_d
      rw [← hInSlice 1 (by unfold rawInputCap; omega)]; exact hSub1
    · change (subInput.words[2]?).map Fin.val = some 0
      rw [← hInSlice 2 (by unfold rawInputCap; omega)]; exact hSub2
    · have hp1 : 3 + p < rawInputCap m := by unfold rawInputCap; omega
      have hp2 : 3 + m_d + p < rawInputCap m := by unfold rawInputCap; omega
      have ha := hSubArcs p hp
      constructor
      · rw [← hInSlice (3 + p) hp1, ← Nat.add_assoc]; exact ha.1
      · rw [← hInSlice (3 + m_d + p) hp2, ← Nat.add_assoc (loopSubInBase loopBase) (3 + m_d) p, ← Nat.add_assoc]
        exact ha.2
  let subStart0 : State subL := mkSubStart s23 (loopSubWorkBase loopBase n m)
  obtain ⟨w, tSub, workSub, hwSubLe, _, hwLe19, hEntryPos, hDictSz, hBack1, hBack2, hLabSz, hStopSz, hEntryEq,
      hExtSub, hWorkBndSub, hIdxSub, hExSub, hRunSub⟩ := hBuild subInput subStart0 hRaw
  have hInBaseLt : loopSubInBase loopBase < 2 ^ bits := by omega
  have hDataBaseLt : loopSubWorkBase loopBase n m < 2 ^ bits := by omega
  have hInPtrLt : inPtrAddr < workCap := by
    unfold inPtrAddr; unfold loopWorkWords at hFit; omega
  have hDatPtrLt : dataPtrAddr < workCap := by
    unfold dataPtrAddr; unfold loopWorkWords at hFit; omega
  have hCfg : SliceConfig subL (layout16 bits inputCap workCap hi hw)
      (w32 h32 inPtrAddr) (w32 h32 dataPtrAddr)
      (loopSubInBase loopBase) (loopSubWorkBase loopBase n m) subInput s23.data :=
    { inBaseLt := hInBaseLt
      dataBaseLt := hDataBaseLt
      inPtr_lt := hInPtrLt
      dataPtr_lt := hDatPtrLt
      inFit := hInSubFit
      dataFit := hWorkSubFit
      inPtr_at := mem_word_of_map hInPtr hInBaseLt
      dataPtr_at := mem_word_of_map hDatPtr hDataBaseLt
      inPtr_outside := Or.inl (by
        rw [show (w32 h32 inPtrAddr).val = inPtrAddr from rfl]
        unfold inPtrAddr loopSubWorkBase rawInputCap; omega)
      dataPtr_outside := Or.inl (by
        rw [show (w32 h32 dataPtrAddr).val = dataPtrAddr from rfl]
        unfold dataPtrAddr loopSubWorkBase rawInputCap; omega)
      slices_disjoint := Or.inl (by
        change loopSubInBase loopBase + rawInputCap m ≤ loopSubWorkBase loopBase n m
        unfold loopSubWorkBase loopSubInBase; omega)
      inSlice_eq := hInSlice }
  have hSim : SliceSim (bits := bits) (subL := subL) (bigL := layout16 bits inputCap workCap hi hw)
      rfl rfl (loopSubWorkBase loopBase n m) offRaw s23.data (Phase.initial subStart0) s23 :=
    { pc_eq := by rw [pc23]; rfl
      regs_eq := fun i => mkSubStart_regs s23 (loopSubWorkBase loopBase n m) i
      dataSlice_eq := fun j hj => mkSubStart_data s23 hj (by rw [hSz23]; exact hWorkSubFit)
      frame_eq := fun _ _ => rfl }
  have hExitLt : offRaw + 4 * subCode.size < code.size := by
    rw [familyForestLoopCode_size subCode h32]; unfold offRaw; omega
  obtain ⟨mSub, sPost, hmSubLe, hStSub, hPcPost, _, hDataPost, hFramePost⟩ :=
    liftProgram_relocated_steps (bits := bits) (subL := subL) (bigL := layout16 bits inputCap workCap hi hw)
      rfl rfl subCode subInput code input (w32 h32 inPtrAddr) (w32 h32 dataPtrAddr)
      (loopSubInBase loopBase) (loopSubWorkBase loopBase n m) offRaw
      workSub (Phase.initial subStart0) ⟨tSub, workSub⟩ s23
      hRunSub hCfg (liftedRaw_bodyRelocated subCode h32) hExitLt hSim
  have hPayPost : sPost.data.extract (loopSubWorkBase loopBase n m)
      (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w := by
    apply Array.ext
    · rw [Array.size_extract, packedPayload_size, sPost.data_size]
      change min (loopSubWorkBase loopBase n m + w.wordCount) workCap - loopSubWorkBase loopBase n m = w.wordCount
      rw [Nat.min_eq_left (by omega)]; omega
    · intro j hj1 hj2
      rw [Array.size_extract, sPost.data_size] at hj1
      have hjWc : j < w.wordCount := by omega
      have hjExtT : j < (tSub.data.extract 0 w.wordCount).size := by
        rw [hExtSub, packedPayload_size]; exact hjWc
      have hjT : j < tSub.data.size := by
        rw [tSub.data_size]; exact Nat.lt_of_lt_of_le hjWc hwSubLe
      have hGetT : (tSub.data.extract 0 w.wordCount)[j]'hjExtT = tSub.data[j]'hjT := by
        rw [Array.getElem_extract]; congr 1; exact Nat.zero_add j
      have hEqT : (packedPayload w)[j]? = tSub.data[j]? := by
        rw [← hExtSub, Array.getElem?_eq_getElem hjExtT, hGetT, Array.getElem?_eq_getElem hjT]
      have hBndS : loopSubWorkBase loopBase n m + j < sPost.data.size := by
        rw [sPost.data_size]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hjWc hwSubLe) _) hWorkSubFit
      have hEqS := hDataPost j (Nat.lt_of_lt_of_le hjWc hwSubLe)
      rw [← hEqT, Array.getElem?_eq_getElem hBndS,
        Array.getElem?_eq_getElem (by rw [packedPayload_size]; exact hjWc), Option.some.injEq] at hEqS
      rw [Array.getElem_extract]; exact hEqS
  have hLMonoSq : OracleContract.L (S.ramQuotient d).vertexCount ^ 2 ≤ OracleContract.L n ^ 2 := by
    rw [Nat.pow_two, Nat.pow_two]; exact Nat.mul_le_mul hL hL
  have hmSubBnd : mSub ≤ 46648 * ((n_d + m_d) * OracleContract.L n ^ 2) := by
    have hm2 : workSub ≤ 11662 * ((n_d + m_d) * OracleContract.L (S.ramQuotient d).vertexCount ^ 2) := by
      simpa only [ramQuotient_arcCount_eq S d] using hWorkBndSub
    have hm3 : (n_d + m_d) * OracleContract.L (S.ramQuotient d).vertexCount ^ 2 ≤
        (n_d + m_d) * OracleContract.L n ^ 2 := Nat.mul_le_mul_left _ hLMonoSq
    calc mSub ≤ 4 * workSub := hmSubLe
      _ ≤ 4 * (11662 * ((n_d + m_d) * OracleContract.L (S.ramQuotient d).vertexCount ^ 2)) :=
          Nat.mul_le_mul_left 4 hm2
      _ = 46648 * ((n_d + m_d) * OracleContract.L (S.ramQuotient d).vertexCount ^ 2) := by
          rw [← Nat.mul_assoc]
      _ ≤ 46648 * ((n_d + m_d) * OracleContract.L n ^ 2) := Nat.mul_le_mul_left _ hm3
  exact ⟨w, sPost, mSub, hmSubBnd, hwSubLe, hwLe19, hEntryPos, hDictSz, hBack1, hBack2,
    hLabSz, hStopSz, hEntryEq, hIdxSub, hExSub, hStSub, hPcPost, hPayPost,
    fun addr ha => hFramePost addr ha⟩

private theorem largeSubRun_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase forestUsed : Nat}
    {hsi : rawInputCap m ≤ 2 ^ bits} {hsw : rawWorkCap n m ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (hq : Q = dense.length) (hQn : Q ≤ n) (hm_d : (S.emittedArcs d).length ≤ m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    (Extra : WordColumns bits → Prop)
    (hBuild : ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          Extra w ∧
          run subCode subInput work (Phase.initial subStart) = some ⟨t, work⟩)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offLarge) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d.val forestUsed s₀)
    (hInPtr : (s₀.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase))
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hSub0 : (s₀.data[loopSubInBase loopBase]?).map Fin.val = some (1 + (S.childSlice d).length))
    (hSub1 : (s₀.data[loopSubInBase loopBase + 1]?).map Fin.val = some (S.emittedArcs d).length)
    (hSub2 : (s₀.data[loopSubInBase loopBase + 2]?).map Fin.val = some 0)
    (hSubArcs : ∀ (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (s₀.data[loopSubInBase loopBase + 3 + p]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[loopSubInBase loopBase + 3 + (S.emittedArcs d).length + p]?).map Fin.val = some ea.headLocal) :
    let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
    let n_d := 1 + (S.childSlice d).length
    let m_d := (S.emittedArcs d).length
    ∃ (w : WordColumns bits) (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      steps ≤ 47 + 46648 * ((n_d + m_d) * OracleContract.L n ^ 2) ∧
      w.wordCount ≤ rawWorkCap n m ∧
      w.wordCount ≤ 19 * n_d ∧
      1 ≤ w.entry.size ∧
      w.dictionary.size = 1 + 3 * D ∧
      w.back.tagAndFirst.size = n_d + 1 ∧
      w.back.second.size = n_d + 1 ∧
      w.labels.size = n_d ∧
      w.stop.size = w.entry.size ∧
      w.entry.size = 1 + (List.range D).foldl
        (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      Extra w ∧
      Steps code input steps s₀ t ∧
      t.pc = offMax subCode.size ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d.val forestUsed t ∧
      t.data.extract (loopSubWorkBase loopBase n m)
        (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w ∧
      (∀ addr, (addr < loopSubWorkBase loopBase n m ∨ loopSubStateBase loopBase n m + 11 ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code n_d m_d
  have hSubInBnd : ∀ k, k < rawInputCap m → loopSubInBase loopBase + k < loopSubStateBase loopBase n m := by
    intro k hk; unfold loopSubStateBase loopSubWorkBase loopSubInBase rawInputCap rawWorkCap at *; omega
  obtain ⟨s23, hStSave, pc23, hSz23, hSaved, hOut23⟩ :=
    saveRegs_steps subCode h32 input hFit hBits hpc hDataSz hRegs hStPtr
  have hSubInPre : ∀ addr, addr < loopSubStateBase loopBase n m → s23.data[addr]? = s₀.data[addr]? :=
    fun addr ha => hOut23 addr (Or.inl ha)
  have hInPtr23 : (s23.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase) := by
    rw [hSubInPre _ (by unfold inPtrAddr loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)]; exact hInPtr
  have hDatPtr23 : (s23.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    rw [hSubInPre _ (by unfold dataPtrAddr loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)]; exact hDatPtr
  have hSub0_23 : (s23.data[loopSubInBase loopBase]?).map Fin.val = some n_d := by
    rw [hSubInPre _ (by simpa only [Nat.add_zero] using hSubInBnd 0 (by unfold rawInputCap; omega))]; exact hSub0
  have hSub1_23 : (s23.data[loopSubInBase loopBase + 1]?).map Fin.val = some m_d := by
    rw [hSubInPre _ (hSubInBnd 1 (by unfold rawInputCap; omega))]; exact hSub1
  have hSub2_23 : (s23.data[loopSubInBase loopBase + 2]?).map Fin.val = some 0 := by
    rw [hSubInPre _ (hSubInBnd 2 (by unfold rawInputCap; omega))]; exact hSub2
  have hSubArcs23 : ∀ (p : Nat) (hp : p < m_d),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (s23.data[loopSubInBase loopBase + 3 + p]?).map Fin.val = some ea.srcLocal ∧
      (s23.data[loopSubInBase loopBase + 3 + m_d + p]?).map Fin.val = some ea.headLocal := by
    intro p hp
    have ha := hSubArcs p hp
    exact ⟨by rw [hSubInPre _ (by have := hSubInBnd (3 + p) (by unfold rawInputCap; omega); omega)]; exact ha.1,
      by rw [hSubInPre _ (by have := hSubInBnd (3 + m_d + p) (by unfold rawInputCap; omega); omega)]; exact ha.2⟩
  obtain ⟨w, sPost, mSub, hmSubBnd, hwSubLe, hwLe19, hEntryPos, hDictSz, hBack1, hBack2, hLabSz, hStopSz,
      hEntryEq, hIdxSub, hExSub, hStSub, hPcPost, hPayPost, hPreWork⟩ :=
    largeSubRun_lift_aux h32 input subCode S d hq hQn hm_d hFit hBits Extra hBuild pc23 hSz23
      hInPtr23 hDatPtr23 hSub0_23 hSub1_23 hSub2_23 hSubArcs23
  have hStPtrPost : (sPost.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hPreWork _ (Or.inl (by unfold statePtrAddr loopSubWorkBase rawInputCap; omega)),
      hOut23 _ (Or.inl (by unfold statePtrAddr loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hStPtr
  have hSavedPost : ∀ r : Fin 16, r.val ≤ 10 → ∃ w, sPost.data[loopSubStateBase loopBase n m + r.val]? = some w := by
    intro r hr
    refine ⟨reg s₀ r, ?_⟩
    rw [hPreWork _ (Or.inr (Nat.le_add_right _ _))]
    exact hSaved r hr
  obtain ⟨sPostR, hStRest, pcPostR, hDPostR, hResRegs⟩ :=
    restoreRegs_steps subCode h32 input hFit hBits hPcPost hStPtrPost hSavedPost
  have hRgPostR : LoopIterRegs n m root Q treeBase emitBase loopBase d.val forestUsed sPostR :=
    loopIterRegs_of_keep hRegs fun r hr => by
      have h1 : some (reg sPostR r) = sPost.data[loopSubStateBase loopBase n m + r.val]? :=
        hResRegs r (by omega)
      rw [hPreWork _ (Or.inr (Nat.le_add_right _ _)), hSaved r (by omega), Option.some.injEq] at h1
      exact h1
  refine ⟨w, sPostR, 23 + mSub + 24, by dsimp only [n_d, m_d]; omega, hwSubLe, hwLe19,
    hEntryPos, hDictSz, hBack1, hBack2,
    hLabSz, hStopSz, hEntryEq, hIdxSub, hExSub, (hStSave.append hStSub).append hStRest, pcPostR,
    by rw [hDPostR, sPost.data_size], hRgPostR, by rw [hDPostR]; exact hPayPost, fun addr ha => ?_⟩
  rw [hDPostR, hPreWork addr (by unfold loopSubStateBase at ha ⊢; omega),
    hOut23 addr (by unfold loopSubStateBase at ha ⊢; omega)]

private theorem largeFinish_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed n_d : Nat}
    (hdLt : d < n) (hn_d : n_d ≤ n)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hArenaFit : forestUsed + 19 * n_d ≤ 38 * n)
    (w : WordColumns bits)
    (hwSubLe : w.wordCount ≤ rawWorkCap n m) (hwLe19 : w.wordCount ≤ 19 * n_d)
    (hDictSz : w.dictionary.size = 1 + 3 * (((w.dictionary[0]?).map Fin.val).getD 0))
    (hBack1 : w.back.tagAndFirst.size = n_d + 1)
    (hBack2 : w.back.second.size = n_d + 1)
    (hLabSz : w.labels.size = n_d)
    (hStopSz : w.stop.size = w.entry.size)
    (hEntryEq : w.entry.size = 1 + (List.range (((w.dictionary[0]?).map Fin.val).getD 0)).foldl
      (fun acc j => max acc (((w.dictionary[1 + 2 * (((w.dictionary[0]?).map Fin.val).getD 0) + j]?).map Fin.val).getD 0)) 0)
    {sPostR : State (layout16 bits inputCap workCap hi hw)}
    (pcPostR : sPostR.pc = offMax subCode.size) (hDataPostR : sPostR.data.size = workCap)
    (hRgPostR : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed sPostR)
    (hStPtrPostR : (sPostR.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hDatPtrPostR : (sPostR.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hNdPostR : (sPostR.data[loopBase]?).map Fin.val = some n_d)
    (hPtrsPtr : (sPostR.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m))
    (hArenaPtr : (sPostR.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m))
    (hPayPostR : sPostR.data.extract (loopSubWorkBase loopBase n m)
      (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w) :
    let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
    let D := ((w.dictionary[0]?).map Fin.val).getD 0
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 152 * n_d + 78 ∧
      Steps code input steps sPostR t ∧
      t.pc = offHdr ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d + 1) (forestUsed + w.wordCount) t ∧
      (let dictPtr := forestArenaBase loopBase n m + forestUsed
       let backFstPtr := dictPtr + (1 + 3 * D)
       let backSndPtr := backFstPtr + (n_d + 1)
       let labelsPtr := backSndPtr + (n_d + 1)
       let fEntryPtr := labelsPtr + n_d
       let fStopPtr := fEntryPtr + w.entry.size
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d]?).map Fin.val = some dictPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d + 1]?).map Fin.val = some backFstPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d + 2]?).map Fin.val = some backSndPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d + 3]?).map Fin.val = some labelsPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d + 4]?).map Fin.val = some fEntryPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d + 5]?).map Fin.val = some fStopPtr) ∧
      (∀ j < w.wordCount,
        t.data[forestArenaBase loopBase n m + forestUsed + j]? = (packedPayload w)[j]?) ∧
      (∀ addr,
        (addr < loopSubStateBase loopBase n m ∨
          (loopSubStateBase loopBase n m + 2 ≤ addr ∧ addr < ownerForestPtrsBase loopBase n m + 6 * d) ∨
          (ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr ∧ addr < forestArenaBase loopBase n m + forestUsed) ∨
          forestArenaBase loopBase n m + forestUsed + w.wordCount ≤ addr) →
        t.data[addr]? = sPostR.data[addr]?) := by
  intro code D
  have hDictSz' : w.dictionary.size = 1 + 3 * D := hDictSz
  have hDict0Pos : 0 < w.dictionary.size := by omega
  have hDat0 : (w.dictionary[0]?).map Fin.val = some D := by
    rw [Array.getElem?_eq_getElem hDict0Pos, Option.map_some]
    dsimp only [D]; rw [Array.getElem?_eq_getElem hDict0Pos]; rfl
  have hEntryEq' : w.entry.size = 1 + (List.range D).foldl
      (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 := hEntryEq
  obtain ⟨sMax, kMax, hkMaxLe, hStMax, hPcMax, hSzMax, hRgMax, hr14_Max, _, hSt0Max, hSt1Max, hOutMax⟩ :=
    maxSlotAndWordCount_steps subCode h32 input w hn_d hwLe19 hFit hBits hDat0 hDictSz'
      hBack1 hBack2 hLabSz rfl hStopSz hEntryEq' pcPostR hDataPostR hRgPostR
      hStPtrPostR hDatPtrPostR hNdPostR hPayPostR
  have hDMax : 1 + 3 * D ≤ 19 * n_d := by
    have : w.dictionary.size ≤ w.wordCount := by unfold WordColumns.wordCount; omega
    omega
  have hWcMaxLe : w.wordCount ≤ 19 * n := by omega
  have hArenaFitW : forestUsed + w.wordCount ≤ 38 * n := by omega
  have hDatPtrMax : (sMax.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    rw [hOutMax _ (Or.inl (by unfold loopSubStateBase; unfold loopSubWorkBase dataPtrAddr rawInputCap rawWorkCap; omega))]
    exact hDatPtrPostR
  have hStPtrMax : (sMax.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutMax _ (Or.inl (by unfold loopSubStateBase; unfold loopSubWorkBase statePtrAddr rawInputCap rawWorkCap; omega))]
    exact hStPtrPostR
  have hArenaPtrMax : (sMax.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m) := by
    rw [hOutMax _ (Or.inr (by omega))]; exact hArenaPtr
  have hPayMax : sMax.data.extract (loopSubWorkBase loopBase n m)
      (loopSubWorkBase loopBase n m + w.wordCount) = packedPayload w := by
    rw [← hPayPostR]
    apply Array.ext
    · rw [Array.size_extract, Array.size_extract, hSzMax, hDataPostR]
    · intro j hj1 hj2
      rw [Array.size_extract, hSzMax] at hj1
      have hjWc : j < w.wordCount := by omega
      rw [Array.getElem_extract, Array.getElem_extract]
      have hSubBnd : loopSubWorkBase loopBase n m + j < loopSubStateBase loopBase n m := by
        unfold loopSubStateBase; exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hjWc hwSubLe) _
      have hEq := hOutMax (loopSubWorkBase loopBase n m + j) (Or.inl hSubBnd)
      rw [Array.getElem?_eq_getElem (by rw [hSzMax]; unfold loopWorkWords at hFit; unfold loopSubWorkBase rawInputCap; omega),
        Array.getElem?_eq_getElem (by rw [hDataPostR]; unfold loopWorkWords at hFit; unfold loopSubWorkBase rawInputCap; omega),
        Option.some.injEq] at hEq
      exact hEq
  obtain ⟨sCopy, kCopy, hkCopyLe, hStCopy, hPcCopy, hSzCopy, hRgCopy, hCopied, hOutCopy⟩ :=
    arenaCopy_steps subCode h32 input w hWcMaxLe hArenaFitW hFit hBits hPcMax hSzMax hRgMax
      hr14_Max hDatPtrMax hStPtrMax hArenaPtrMax hPayMax
  have hMetaBeforeArena : ∀ addr,
      (addr = statePtrAddr ∨ addr = dataPtrAddr ∨ addr = loopBase ∨
       addr = loopSubWorkBase loopBase n m ∨
       addr = loopSubStateBase loopBase n m ∨ addr = loopSubStateBase loopBase n m + 1 ∨
       addr = loopSubStateBase loopBase n m + 14 ∨ addr = loopSubStateBase loopBase n m + 15) →
      addr < forestArenaBase loopBase n m + forestUsed := by
    intro addr h
    unfold statePtrAddr dataPtrAddr forestArenaBase ownerForestPtrsBase loopSortEntryBase
      loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *
    omega
  have hStPtrCopy : (sCopy.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inl rfl)))]; exact hStPtrMax
  have hDatPtrCopy : (sCopy.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inl rfl))))]; exact hDatPtrMax
  have hNdCopy : (sCopy.data[loopBase]?).map Fin.val = some n_d := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inr (Or.inl rfl))))),
      hOutMax _ (Or.inl (by unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hNdPostR
  have hDat0Copy : (sCopy.data[loopSubWorkBase loopBase n m]?).map Fin.val = some D := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))]
    have hSzPos : 0 < w.dictionary.size := hDict0Pos
    have hWcPos : 0 < w.wordCount := by unfold WordColumns.wordCount; omega
    have hExt0 : sMax.data[loopSubWorkBase loopBase n m]? = (packedPayload w)[0]? := by
      have h0 : 0 < (sMax.data.extract (loopSubWorkBase loopBase n m)
          (loopSubWorkBase loopBase n m + w.wordCount)).size := by
        rw [hPayMax, packedPayload_size]; exact hWcPos
      have hBnd0 : loopSubWorkBase loopBase n m < sMax.data.size := by
        rw [hSzMax]; unfold loopWorkWords at hFit; unfold loopSubWorkBase rawInputCap; omega
      have hGet0 := extract_get0 sMax.data h0 hBnd0
      rw [Array.getElem?_eq_getElem hBnd0, ← hGet0, ← Array.getElem?_eq_getElem h0, hPayMax]
    rw [hExt0, packedPayload_dict_at w hSzPos]
    exact hDat0
  have hPtrsPtrCopy : (sCopy.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m) := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))),
      hOutMax _ (Or.inr (by omega))]
    exact hPtrsPtr
  have hArenaPtrCopy : (sCopy.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m) := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))]
    exact hArenaPtrMax
  have hMemSt0Copy : sCopy.data[loopSubStateBase loopBase n m]? = some ⟨w.entry.size, by
      unfold loopWorkWords at hFit; omega⟩ := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))]
    exact hSt0Max
  have hMemSt1Copy : sCopy.data[loopSubStateBase loopBase n m + 1]? = some ⟨w.wordCount, by
      unfold loopWorkWords at hFit; omega⟩ := by
    rw [hOutCopy _ (Or.inl (hMetaBeforeArena _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))))]
    exact hSt1Max
  have hWcEq : w.wordCount = 3 * D + 3 * n_d + 2 * w.entry.size + 3 := by
    unfold WordColumns.wordCount
    rw [hDictSz', hBack1, hBack2, hLabSz, hStopSz]; omega
  obtain ⟨s42, hStRec, pc42, hSz42, hRg42, hP0, hP1, hP2, hP3, hP4, hP5, hOut42⟩ :=
    recordPtrs_steps subCode h32 input (D := D) (n_d := n_d) (N_d := w.entry.size) (wc := w.wordCount)
      hdLt hn_d hDMax hWcEq hArenaFitW hFit hBits hPcCopy hSzCopy hRgCopy
      hStPtrCopy hDatPtrCopy hDat0Copy hNdCopy hPtrsPtrCopy hArenaPtrCopy hMemSt0Copy hMemSt1Copy
  have hStepBnd : kMax + kCopy + 42 ≤ 152 * n_d + 78 := by
    have : kMax ≤ 38 * n_d + 27 := by omega
    have : kCopy ≤ 114 * n_d + 9 := by omega
    omega
  refine ⟨s42, kMax + kCopy + 42, hStepBnd,
    (hStMax.append hStCopy).append hStRec, pc42, hSz42, hRg42, ⟨hP0, hP1, hP2, hP3, hP4, hP5⟩,
    fun j hj => ?_, fun addr ha => ?_⟩
  · have hLtAr : forestArenaBase loopBase n m + forestUsed + j <
        ownerForestPtrsBase loopBase n m + 6 * d ∨
        ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤
        forestArenaBase loopBase n m + forestUsed + j := by
      right; unfold forestArenaBase; omega
    rw [hOut42 _ hLtAr]; exact hCopied j hj
  · have hStep1 : s42.data[addr]? = sCopy.data[addr]? := by
      apply hOut42
      rcases ha with h | ⟨_, h2⟩ | ⟨h1, _⟩ | h
      · left; unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
          loopSubStateBase at *; omega
      · left; exact h2
      · right; exact h1
      · right; unfold forestArenaBase at h; omega
    have hStep2 : sCopy.data[addr]? = sMax.data[addr]? := by
      apply hOutCopy
      rcases ha with h | ⟨_, _⟩ | ⟨_, h2⟩ | h
      · left; unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
          loopSubStateBase at *; omega
      · left; unfold forestArenaBase; omega
      · left; exact h2
      · right; exact h
    have hStep3 : sMax.data[addr]? = sPostR.data[addr]? := by
      apply hOutMax
      rcases ha with h | ⟨h1, _⟩ | ⟨h1, _⟩ | h
      · left; exact h
      · right; exact h1
      · right; unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase at h1; omega
      · right; unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase at h; omega
    rw [hStep1, hStep2, hStep3]

private theorem largeBranch_steps_aux {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase forestUsed : Nat}
    {hsi : rawInputCap m ≤ 2 ^ bits} {hsw : rawWorkCap n m ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (hq : Q = dense.length) (hQn : Q ≤ n) (hm_d : (S.emittedArcs d).length ≤ m)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hArenaFit : forestUsed + 19 * (1 + (S.childSlice d).length) ≤ 38 * n)
    (Extra : WordColumns bits → Prop)
    (hBuild : ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          Extra w ∧
          run subCode subInput work (Phase.initial subStart) = some ⟨t, work⟩)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offLarge) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d.val forestUsed s₀)
    (hInPtr : (s₀.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase))
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some (1 + (S.childSlice d).length))
    (_hMdAt : (s₀.data[loopBase + 1]?).map Fin.val = some (S.emittedArcs d).length)
    (hPtrsPtr : (s₀.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m))
    (hArenaPtr : (s₀.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m))
    (hSub0 : (s₀.data[loopSubInBase loopBase]?).map Fin.val = some (1 + (S.childSlice d).length))
    (hSub1 : (s₀.data[loopSubInBase loopBase + 1]?).map Fin.val = some (S.emittedArcs d).length)
    (hSub2 : (s₀.data[loopSubInBase loopBase + 2]?).map Fin.val = some 0)
    (hSubArcs : ∀ (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (s₀.data[loopSubInBase loopBase + 3 + p]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[loopSubInBase loopBase + 3 + (S.emittedArcs d).length + p]?).map Fin.val = some ea.headLocal) :
    let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
    let n_d := 1 + (S.childSlice d).length
    let m_d := (S.emittedArcs d).length
    ∃ (w : WordColumns bits) (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 47000 * ((n_d + m_d) * OracleContract.L n ^ 2) ∧
      w.wordCount ≤ 19 * n_d ∧
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      Extra w ∧
      Steps code input steps s₀ t ∧
      t.pc = offHdr ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d.val + 1) (forestUsed + w.wordCount) t ∧
      (let dictPtr := forestArenaBase loopBase n m + forestUsed
       let D := ((w.dictionary[0]?).map Fin.val).getD 0
       let backFstPtr := dictPtr + (1 + 3 * D)
       let backSndPtr := backFstPtr + (n_d + 1)
       let labelsPtr := backSndPtr + (n_d + 1)
       let fEntryPtr := labelsPtr + n_d
       let fStopPtr := fEntryPtr + w.entry.size
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some dictPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some backFstPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some backSndPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some labelsPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some fEntryPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some fStopPtr) ∧
      (∀ j < w.wordCount,
        t.data[forestArenaBase loopBase n m + forestUsed + j]? = (packedPayload w)[j]?) ∧
      (∀ addr,
        (addr < loopSubWorkBase loopBase n m ∨
          (loopSubStateBase loopBase n m + 11 ≤ addr ∧ addr < ownerForestPtrsBase loopBase n m + 6 * d.val) ∨
          (ownerForestPtrsBase loopBase n m + 6 * d.val + 6 ≤ addr ∧ addr < forestArenaBase loopBase n m + forestUsed) ∨
          forestArenaBase loopBase n m + forestUsed + w.wordCount ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code n_d m_d
  have hdLt : d.val < n := Nat.lt_of_lt_of_le (hq ▸ d.isLt) hQn
  have hn_d : n_d ≤ n := Nat.le_trans (childSlice_succ_le_length S d) (hq ▸ hQn)
  obtain ⟨w, sPostR, kRun, hkRunBnd, hwSubLe, hwLe19, _, hDictSz, hBack1, hBack2, hLabSz, hStopSz, hEntryEq,
      hIdxSub, hExSub, hStRun, pcPostR, hDataPostR, hRgPostR, hPayPostR, hOutRun⟩ :=
    largeSubRun_steps h32 input subCode S d hq hQn hm_d hFit hBits Extra hBuild hpc hDataSz hRegs
      hInPtr hDatPtr hStPtr hSub0 hSub1 hSub2 hSubArcs
  have hStPtrPostR : (sPostR.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutRun _ (Or.inl (by unfold statePtrAddr loopSubWorkBase rawInputCap; omega))]; exact hStPtr
  have hDatPtrPostR : (sPostR.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    rw [hOutRun _ (Or.inl (by unfold dataPtrAddr loopSubWorkBase rawInputCap; omega))]; exact hDatPtr
  have hNdPostR : (sPostR.data[loopBase]?).map Fin.val = some n_d := by
    rw [hOutRun _ (Or.inl (by unfold loopSubWorkBase rawInputCap; omega))]; exact hNdAt
  have hPtrsPostR : (sPostR.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m) := by
    rw [hOutRun _ (Or.inr (by omega))]; exact hPtrsPtr
  have hArenaPostR : (sPostR.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m) := by
    rw [hOutRun _ (Or.inr (by omega))]; exact hArenaPtr
  obtain ⟨s42, kFin, hkFinBnd, hStFin, pc42, hSz42, hRg42, hPtrs42, hCopied42, hOutFin⟩ :=
    largeFinish_steps subCode h32 input hdLt hn_d hFit hBits hArenaFit w hwSubLe hwLe19
      hDictSz hBack1 hBack2 hLabSz hStopSz hEntryEq pcPostR hDataPostR hRgPostR
      hStPtrPostR hDatPtrPostR hNdPostR hPtrsPostR hArenaPostR hPayPostR
  have hLPos : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hLSq : 1 ≤ OracleContract.L n ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ OracleContract.L n * OracleContract.L n := Nat.mul_le_mul hLPos hLPos
      _ = OracleContract.L n ^ 2 := (Nat.pow_two _).symm
  have hNLe : n_d ≤ (n_d + m_d) * OracleContract.L n ^ 2 := by
    calc n_d = n_d * 1 := (Nat.mul_one _).symm
      _ ≤ (n_d + m_d) * OracleContract.L n ^ 2 := Nat.mul_le_mul (Nat.le_add_right _ _) hLSq
  have hTotal : kRun + kFin ≤ 47000 * ((n_d + m_d) * OracleContract.L n ^ 2) := by
    have hkRun' : kRun ≤ 47 + 46648 * ((n_d + m_d) * OracleContract.L n ^ 2) := hkRunBnd
    have h1 : kFin + 47 ≤ 352 * n_d := by omega
    have h2 : 352 * n_d ≤ 352 * ((n_d + m_d) * OracleContract.L n ^ 2) := Nat.mul_le_mul_left 352 hNLe
    omega
  refine ⟨w, s42, kRun + kFin, hTotal, hwLe19, hIdxSub, hExSub, hStRun.append hStFin, pc42, hSz42, hRg42,
    hPtrs42, hCopied42, fun addr ha => ?_⟩
  have hF1 : s42.data[addr]? = sPostR.data[addr]? := by
    apply hOutFin
    rcases ha with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · left; unfold loopSubStateBase; omega
    · right; left; exact ⟨by omega, h2⟩
    · right; right; left; exact ⟨h1, h2⟩
    · right; right; right; exact h
  have hF2 : sPostR.data[addr]? = s₀.data[addr]? := by
    apply hOutRun
    rcases ha with h | ⟨h1, _⟩ | ⟨h1, _⟩ | h
    · left; exact h
    · right; exact h1
    · right; unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase at h1; omega
    · right; unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase at h; omega
  rw [hF1, hF2]

private theorem largeBranch_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase forestUsed : Nat}
    {hsi : rawInputCap m ≤ 2 ^ bits} {hsw : rawWorkCap n m ≤ 2 ^ bits}
    {mem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (hq : Q = dense.length) (hQn : Q ≤ n) (hm_d : (S.emittedArcs d).length ≤ m)
    (hLarge : 3 ≤ 1 + (S.childSlice d).length)
    (hFlat : (S.ramQuotient d).IsFlat) (hAcyc : (S.ramQuotient d).IsAcyclic)
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hArenaFit : forestUsed + 19 * (1 + (S.childSlice d).length) ≤ 38 * n)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offLarge) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d.val forestUsed s₀)
    (hInPtr : (s₀.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase))
    (hDatPtr : (s₀.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m))
    (hStPtr : (s₀.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m))
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some (1 + (S.childSlice d).length))
    (hMdAt : (s₀.data[loopBase + 1]?).map Fin.val = some (S.emittedArcs d).length)
    (hPtrsPtr : (s₀.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m))
    (hArenaPtr : (s₀.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m))
    (hSub0 : (s₀.data[loopSubInBase loopBase]?).map Fin.val = some (1 + (S.childSlice d).length))
    (hSub1 : (s₀.data[loopSubInBase loopBase + 1]?).map Fin.val = some (S.emittedArcs d).length)
    (hSub2 : (s₀.data[loopSubInBase loopBase + 2]?).map Fin.val = some 0)
    (hSubArcs : ∀ (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (s₀.data[loopSubInBase loopBase + 3 + p]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[loopSubInBase loopBase + 3 + (S.emittedArcs d).length + p]?).map Fin.val = some ea.headLocal) :
    let subCode := largeBuildProgram hsi hsw (Nat.le_trans (by decide : 8 ≤ 32) h32)
    let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
    let n_d := 1 + (S.childSlice d).length
    let m_d := (S.emittedArcs d).length
    ∃ (w : WordColumns bits) (t : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps ≤ 47000 * ((n_d + m_d) * OracleContract.L n ^ 2) ∧
      w.wordCount ≤ 19 * n_d ∧
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      Steps code input steps s₀ t ∧
      t.pc = offHdr ∧ t.data.size = workCap ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase (d.val + 1) (forestUsed + w.wordCount) t ∧
      (let dictPtr := forestArenaBase loopBase n m + forestUsed
       let D := ((w.dictionary[0]?).map Fin.val).getD 0
       let backFstPtr := dictPtr + (1 + 3 * D)
       let backSndPtr := backFstPtr + (n_d + 1)
       let labelsPtr := backSndPtr + (n_d + 1)
       let fEntryPtr := labelsPtr + n_d
       let fStopPtr := fEntryPtr + w.entry.size
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some dictPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some backFstPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some backSndPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some labelsPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some fEntryPtr ∧
       (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some fStopPtr) ∧
      (∀ j < w.wordCount,
        t.data[forestArenaBase loopBase n m + forestUsed + j]? = (packedPayload w)[j]?) ∧
      (∀ addr,
        (addr < loopSubWorkBase loopBase n m ∨
          (loopSubStateBase loopBase n m + 11 ≤ addr ∧ addr < ownerForestPtrsBase loopBase n m + 6 * d.val) ∨
          (ownerForestPtrsBase loopBase n m + 6 * d.val + 6 ≤ addr ∧ addr < forestArenaBase loopBase n m + forestUsed) ∨
          forestArenaBase loopBase n m + forestUsed + w.wordCount ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  have h8 : 8 ≤ 2 ^ bits := Nat.le_trans (by decide : 8 ≤ 32) h32
  have hWorkBnd : rawWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤ rawWorkCap n m := by
    have hn_d : (S.ramQuotient d).vertexCount ≤ n := Nat.le_trans (childSlice_succ_le_length S d) (hq ▸ hQn)
    have hmEq : (S.ramQuotient d).arcCount = (S.emittedArcs d).length := ramQuotient_arcCount_eq S d
    change rawWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤ rawWorkCap n m
    rw [hmEq]; unfold rawWorkCap; omega
  have hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits := by
    have hn_d : (S.ramQuotient d).vertexCount ≤ n := Nat.le_trans (childSlice_succ_le_length S d) (hq ▸ hQn)
    unfold loopWorkWords at hFit; omega
  obtain ⟨w, t, steps, hs1, hs2, hs3, _, hs4, hs5, hs6, hs7, hs8, hs9, hs10⟩ :=
    largeBranch_steps_aux h32 input (largeBuildProgram hsi hsw h8) S d hq hQn hm_d hFit hBits hArenaFit
      (fun _ => True)
      (fun subInput subStart hRaw => by
        obtain ⟨w, t, work, h1, h2, h3, h4, h5, h6, h7, h8', h9, h10, h11, h12, h13, h14⟩ := by
          simpa only [ramQuotient_arcCount_eq S d] using
            run_large_build_exact h8 (S.ramQuotient d) hLarge hFlat hAcyc subInput hRaw hWorkBnd hWidth subStart
        exact ⟨w, t, work, h1, h2, h3, h4, h5, h6, h7, h8', h9, h10, h11, h12, h13, True.intro, h14⟩)
      hpc hDataSz hRegs hInPtr hDatPtr hStPtr hNdAt hMdAt hPtrsPtr hArenaPtr hSub0 hSub1 hSub2 hSubArcs
  exact ⟨w, t, steps, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10⟩

private theorem branchOwner_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase d forestUsed n_d : Nat}
    (hFit : loopBase + loopWorkWords n m ≤ workCap) (_hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hpc : s₀.pc = offBranch) (hDataSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s₀)
    (hNdAt : (s₀.data[loopBase]?).map Fin.val = some n_d) :
    ∃ s3, Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input 3 s₀ s3 ∧
      s3.pc = (if n_d < 3 then offSmall else offLarge) ∧
      s3.data = s₀.data ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s3 := by
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hPcLt : ∀ c, c < 3 → offBranch + c < code.size := by
    intro c hc; rw [hSz]; unfold offBranch; omega
  have hL : (reg s₀ r8).val = loopBase := hRegs.entry.loopBaseVal
  have hNdLt : n_d < 2 ^ bits := by
    have : loopBase < s₀.data.size := by rw [hDataSz]; unfold loopWorkWords at hFit; omega
    cases hm : s₀.data[loopBase]? with
    | none => rw [hm] at hNdAt; cases hNdAt
    | some w =>
      rw [hm, Option.map_some, Option.some.injEq] at hNdAt
      subst hNdAt; exact w.isLt
  have hMemNd : s₀.data[(reg s₀ r8).val]? = some ⟨n_d, hNdLt⟩ := by
    rw [hL]; exact mem_word_of_map hNdAt hNdLt
  obtain ⟨s1, st0, pc1, r11_1, keep1, d1⟩ :=
    step16_loadData code input hpc (at_branch subCode h32 (i := 0) (by decide)) hMemNd (hPcLt 1 (by decide))
  obtain ⟨s2, st1, pc2, r12_2, keep2, d2⟩ :=
    step16_imm code input pc1 (at_branch subCode h32 (i := 1) (by decide)) (hPcLt 2 (by decide))
  have h11 : (reg s2 r11).val = n_d := by rw [keep2 _ (by decide), r11_1]
  have h12 : (reg s2 r12).val = 3 := by rw [r12_2]; rfl
  have hRg2 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s2 :=
    loopIterRegs_of_keep hRegs fun r hr =>
      (keep2 r (fun e => absurd hr (by subst e; decide))).trans
        (keep1 r (fun e => absurd hr (by subst e; decide)))
  by_cases hLt3 : n_d < 3
  · have st2 := step16_branchLt_true code input pc2 (at_branch subCode h32 (i := 2) (by decide))
      (by rw [hSz]; unfold offSmall; omega) (by rw [h11, h12]; exact hLt3)
    let s3 : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s2.regs, data := s2.data, pc := offSmall,
        regs_size := s2.regs_size, data_size := s2.data_size }
    exact ⟨s3, Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.zero s3))),
      by rw [ite_eq_left hLt3], by change s2.data = s₀.data; rw [d2, d1],
      loopIterRegs_of_keep hRg2 (fun _ _ => rfl)⟩
  · have st2 := step16_branchLt_false code input pc2 (at_branch subCode h32 (i := 2) (by decide))
      (by rw [hSz]; unfold offLarge; omega) (by rw [h11, h12]; omega)
    let s3 : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s2.regs, data := s2.data, pc := offLarge,
        regs_size := s2.regs_size, data_size := s2.data_size }
    exact ⟨s3, Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.zero s3))),
      by rw [ite_eq_right hLt3], by change s2.data = s₀.data; rw [d2, d1],
      loopIterRegs_of_keep hRg2 (fun _ _ => rfl)⟩

private def ownerCounts {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) : List Nat :=
  List.ofFn (fun j : Fin dense.length => 1 + (S.childSlice j).length)

private theorem ownerCounts_length {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    (ownerCounts S).length = dense.length := by
  simp [ownerCounts]

private theorem ownerCounts_take_succ {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) {d : Nat} (hd : d < dense.length) :
    ((ownerCounts S).take (d + 1)).sum =
      ((ownerCounts S).take d).sum + (1 + (S.childSlice ⟨d, hd⟩).length) := by
  have hdLen : d < (ownerCounts S).length := by rw [ownerCounts_length]; exact hd
  rw [List.take_add_one, List.getElem?_eq_getElem hdLen, Option.toList_some, List.sum_append]
  simp [ownerCounts]

private theorem list_take_sum_le {xs : List Nat} (k : Nat) :
    (xs.take k).sum ≤ xs.sum := by
  calc (xs.take k).sum ≤ (xs.take k).sum + (xs.drop k).sum := Nat.le_add_right _ _
    _ = ((xs.take k) ++ (xs.drop k)).sum := List.sum_append.symm
    _ = xs.sum := by rw [List.take_append_drop]

private theorem ownerCounts_take_le {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Nat) :
    ((ownerCounts S).take d).sum ≤ 2 * dense.length - 1 := by
  calc ((ownerCounts S).take d).sum ≤ (ownerCounts S).sum := list_take_sum_le d
    _ = 2 * dense.length - 1 := S.sum_ownerVertexCounts

private theorem emittedArcs_length_le_arcCount {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    (S.emittedArcs d).length ≤ g.arcCount := by
  have h1 : qStartFn S (d.val + 1) = qStartFn S d.val + (S.emittedArcs d).length :=
    qStartFn_succ S d.isLt
  have h2 := qStartFn_le_arcCount S (d.val + 1)
  omega

private theorem qStartFn_mono {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense)
    (i j : Nat) (hij : i ≤ j) (hj : j ≤ dense.length) :
    qStartFn S i ≤ qStartFn S j := by
  induction j with
  | zero => have hi0 : i = 0 := by omega
            subst hi0; exact Nat.le_refl _
  | succ j ih =>
    by_cases hle : i ≤ j
    · have hPrev := ih hle (Nat.le_of_succ_le hj)
      have hSucc := qStartFn_succ S (Nat.lt_of_succ_le hj)
      omega
    · have hiEq : i = j + 1 := by omega
      subst hiEq; exact Nat.le_refl _

private def OwnerForestRecordAt {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (loopBase n m forestUsed : Nat) (data : Array (Word bits)) : Prop :=
  let n_d := 1 + (S.childSlice d).length
  if n_d < 3 then
    ∀ k < 6, (data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
  else
    ∃ (w : WordColumns bits) (ptrBase : Nat),
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      w.wordCount ≤ 19 * n_d ∧
      forestArenaBase loopBase n m ≤ ptrBase ∧
      ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
      (∀ k < w.wordCount, data[ptrBase + k]? = (packedPayload w)[k]?)

private def OwnerForestRecordWith {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (Extra : Fin dense.length → WordColumns bits → Prop)
    (d : Fin dense.length)
    (loopBase n m forestUsed : Nat) (data : Array (Word bits)) : Prop :=
  let n_d := 1 + (S.childSlice d).length
  if n_d < 3 then
    ∀ k < 6, (data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
  else
    ∃ (w : WordColumns bits) (ptrBase : Nat),
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      Extra d w ∧
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      w.wordCount ≤ 19 * n_d ∧
      forestArenaBase loopBase n m ≤ ptrBase ∧
      ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
      (∀ k < w.wordCount, data[ptrBase + k]? = (packedPayload w)[k]?)

private theorem ownerForestRecordAt_mono {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    {loopBase n m fu₁ fu₂ : Nat} {d₁ d₂ : Array (Word bits)}
    (hfu : fu₁ ≤ fu₂)
    (hRec : OwnerForestRecordAt S d loopBase n m fu₁ d₁)
    (hPtrsEq : ∀ k < 6, d₂[ownerForestPtrsBase loopBase n m + 6 * d.val + k]? =
      d₁[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?)
    (hArenaEq : ∀ addr, forestArenaBase loopBase n m ≤ addr →
      addr < forestArenaBase loopBase n m + fu₁ → d₂[addr]? = d₁[addr]?) :
    OwnerForestRecordAt S d loopBase n m fu₂ d₂ := by
  dsimp only [OwnerForestRecordAt] at hRec ⊢
  by_cases hlt : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hlt] at hRec ⊢
    intro k hk; rw [hPtrsEq k hk]; exact hRec k hk
  · rw [ite_eq_right hlt] at hRec ⊢
    rcases hRec with ⟨w, ptrBase, hIdx, hWc, hLb, hUb, h0, h1, h2, h3, h4, h5, hPay⟩
    refine ⟨w, ptrBase, hIdx, hWc, hLb, by omega,
      by have hp0 := hPtrsEq 0 (by decide); rw [Nat.add_zero] at hp0; rw [hp0]; exact h0,
      by rw [hPtrsEq 1 (by decide)]; exact h1,
      by rw [hPtrsEq 2 (by decide)]; exact h2,
      by rw [hPtrsEq 3 (by decide)]; exact h3,
      by rw [hPtrsEq 4 (by decide)]; exact h4,
      by rw [hPtrsEq 5 (by decide)]; exact h5,
      fun k hk => ?_⟩
    rw [hArenaEq (ptrBase + k) (by omega) (by omega)]; exact hPay k hk

private theorem ownerForestRecordWith_mono {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (Extra : Fin dense.length → WordColumns bits → Prop)
    (d : Fin dense.length)
    {loopBase n m fu₁ fu₂ : Nat} {d₁ d₂ : Array (Word bits)}
    (hfu : fu₁ ≤ fu₂)
    (hRec : OwnerForestRecordWith S Extra d loopBase n m fu₁ d₁)
    (hPtrsEq : ∀ k < 6, d₂[ownerForestPtrsBase loopBase n m + 6 * d.val + k]? =
      d₁[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?)
    (hArenaEq : ∀ addr, forestArenaBase loopBase n m ≤ addr →
      addr < forestArenaBase loopBase n m + fu₁ → d₂[addr]? = d₁[addr]?) :
    OwnerForestRecordWith S Extra d loopBase n m fu₂ d₂ := by
  dsimp only [OwnerForestRecordWith] at hRec ⊢
  by_cases hlt : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hlt] at hRec ⊢
    intro k hk; rw [hPtrsEq k hk]; exact hRec k hk
  · rw [ite_eq_right hlt] at hRec ⊢
    rcases hRec with ⟨w, ptrBase, hEx, hIdx, hWc, hLb, hUb, h0, h1, h2, h3, h4, h5, hPay⟩
    refine ⟨w, ptrBase, hEx, hIdx, hWc, hLb, by omega,
      by have hp0 := hPtrsEq 0 (by decide); rw [Nat.add_zero] at hp0; rw [hp0]; exact h0,
      by rw [hPtrsEq 1 (by decide)]; exact h1,
      by rw [hPtrsEq 2 (by decide)]; exact h2,
      by rw [hPtrsEq 3 (by decide)]; exact h3,
      by rw [hPtrsEq 4 (by decide)]; exact h4,
      by rw [hPtrsEq 5 (by decide)]; exact h5,
      fun k hk => ?_⟩
    rw [hArenaEq (ptrBase + k) (by omega) (by omega)]; exact hPay k hk

private structure LoopIterInv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {origMem : Array (Word bits)} {treeBase : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)} (S : StaticTreeSlice origMem treeBase g r dense)
    (Extra : Fin dense.length → WordColumns bits → Prop)
    (subCode : Array (Instr bits 15))
    (n m root Q emitBase loopBase d forestUsed : Nat)
    (initData : Array (Word bits))
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  dLe : d ≤ Q
  pcEq : s.pc = offHdr
  dataSz : s.data.size = workCap
  regs : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s
  usedLe : forestUsed ≤ 19 * ((ownerCounts S).take d).sum
  inPtr : (s.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase)
  datPtr : (s.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m)
  stPtr : (s.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m)
  degPtr : (s.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m)
  curPtr : (s.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m)
  entPtr : (s.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m)
  ptrsPtr : (s.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m)
  arenaPtr : (s.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m)
  treeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s.data[k]? = origMem[k]?
  qStarts : ∀ j ≤ Q, (s.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)
  arcsUnsorted : ∀ (j : Nat) (hj : j < dense.length), d ≤ j →
    ∀ (p : Nat) (hp : p < (S.emittedArcs ⟨j, hj⟩).length),
      let ea := (S.emittedArcs ⟨j, hj⟩)[p]'hp
      (s.data[emitBase + 3 * n + 1 + (qStartFn S j + p)]?).map Fin.val = some ea.srcLocal ∧
      (s.data[emitBase + 3 * n + m + 1 + (qStartFn S j + p)]?).map Fin.val = some ea.headLocal ∧
      (s.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S j + p)]?).map Fin.val = some ea.tailEntry
  arcsSorted : ∀ (j : Nat) (hj : j < dense.length), j < d →
    ∀ (p : Nat) (hp : p < (S.emittedArcs ⟨j, hj⟩).length),
      let ea := (countingSortedArcs (1 + (S.childSlice ⟨j, hj⟩).length) (S.emittedArcs ⟨j, hj⟩))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds ⟨j, hj⟩ hx).2.1)]; exact hp)
      (s.data[emitBase + 3 * n + 1 + (qStartFn S j + p)]?).map Fin.val = some ea.srcLocal ∧
      (s.data[emitBase + 3 * n + m + 1 + (qStartFn S j + p)]?).map Fin.val = some ea.headLocal ∧
      (s.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S j + p)]?).map Fin.val = some ea.tailEntry
  forests : ∀ (j : Nat) (hj : j < dense.length), j < d →
    OwnerForestRecordWith S Extra ⟨j, hj⟩ loopBase n m forestUsed s.data
  frame : ∀ addr,
    addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
    (addr < emitBase + 3 * n + 1 ∨ emitBase + emitterWorkWords n m ≤ addr) →
    (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) →
    s.data[addr]? = initData[addr]?

private theorem familyForestLoop_iter_steps_aux {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase : Nat}
    {hsi : rawInputCap m ≤ 2 ^ bits} {hsw : rawWorkCap n m ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    {origMem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origMem treeBase g r dense)
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (_hTree3 : 3 ≤ treeBase) (hEmit3 : 3 ≤ emitBase) (hLoop3 : 3 ≤ loopBase)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisjTE : treeBase + staticTreeWords Q ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ treeBase)
    (hDisjTL : treeBase + staticTreeWords Q ≤ loopBase ∨ loopBase + loopWorkWords n m ≤ treeBase)
    (hDisjLE : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    (Extra : Fin dense.length → WordColumns bits → Prop)
    (hBuild : ∀ (d : Fin dense.length), 3 ≤ 1 + (S.childSlice d).length →
      ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          Extra d w ∧
          run subCode subInput work (Phase.initial subStart) = some ⟨t, work⟩)
    {d forestUsed : Nat} (hd : d < Q)
    {initData : Array (Word bits)}
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hInv : LoopIterInv S Extra subCode n m root Q emitBase loopBase d forestUsed initData s₀) :
    let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
    let n_d := 1 + (S.childSlice dFin).length
    let m_d := (S.emittedArcs dFin).length
    ∃ (forestUsed' steps : Nat) (s' : State (layout16 bits inputCap workCap hi hw)),
      steps ≤ 47200 * ((n_d + m_d) * OracleContract.L n ^ 2) ∧
      Steps (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) input steps s₀ s' ∧
      LoopIterInv S Extra subCode n m root Q emitBase loopBase (d + 1) forestUsed' initData s' := by
  intro dFin n_d m_d
  let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hn_d : n_d ≤ n := Nat.le_trans (childSlice_succ_le_length S dFin) (hQ ▸ hQL)
  have hm_d : m_d ≤ m := hm ▸ emittedArcs_length_le_arcCount S dFin
  have hn_raw : 1 + (S.childSlice ⟨d, hQ ▸ hd⟩).length ≤ n := hn_d
  have hm_raw : (S.emittedArcs ⟨d, hQ ▸ hd⟩).length ≤ m := hm_d
  have hQendD : qStartFn S (d + 1) ≤ m := hm ▸ qStartFn_le_arcCount S (d + 1)
  have hQsuccD : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S dFin.isLt
  have hdLtN : d < n := Nat.lt_of_lt_of_le hd hQL
  have hArcsBnd : ∀ ea ∈ S.emittedArcs dFin, ea.srcLocal < n_d :=
    fun x hx => (S.emittedArc_bounds dFin hx).2.1
  have hLPos : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hLSq : 1 ≤ OracleContract.L n ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ OracleContract.L n * OracleContract.L n := Nat.mul_le_mul hLPos hLPos
      _ = OracleContract.L n ^ 2 := (Nat.pow_two _).symm
  -- Step 0: loopHdr branchLt_true (offHdr -> offPrep, 1 step)
  have st0 := step16_branchLt_true code input hInv.pcEq (at_hdr subCode h32)
    (by rw [hSz]; unfold offHdr; omega)
    (by rw [hInv.regs.dVal, hInv.regs.entry.qVal]; exact hd)
  let s1 : State (layout16 bits inputCap workCap hi hw) :=
    { regs := s₀.regs, data := s₀.data, pc := offPrep,
      regs_size := s₀.regs_size, data_size := s₀.data_size }
  have hD1 : s1.data = s₀.data := rfl
  have hRg1 : LoopIterRegs n m root Q treeBase emitBase loopBase d forestUsed s1 :=
    loopIterRegs_of_keep hInv.regs (fun _ _ => rfl)
  -- Step 1: prepOwner_steps (23 steps, offPrep -> offZeroDeg)
  obtain ⟨s2, hStPrep, pc2, sz2, hRg2, hNd2, hMd2, hZ2, hOutPrep⟩ :=
    prepOwner_steps subCode h32 input S hn hm hQ hd rfl hRg1 hInv.dataSz
      hInv.treeMem hInv.qStarts hFit hTreeFit hEmitFit hDisjLE hBits
  -- Step 2: zeroDeg_steps (offZeroDeg -> offCountDeg)
  have hStPtr2 : (s2.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutPrep _ (Or.inl (by unfold statePtrAddr; omega))]; exact hInv.stPtr
  have hDegPtr2 : (s2.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m) := by
    rw [hOutPrep _ (Or.inr (by unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hInv.degPtr
  obtain ⟨s3, kZero, hkZero, hStZero, pc3, sz3, hRg3, hDegsZero, hOutZero⟩ :=
    zeroDeg_steps subCode h32 input hn_d hFit hBits pc2 hRg2 sz2
      (by rw [hNd2]; rfl) hStPtr2 hDegPtr2
  -- Step 3: countDeg_steps (offCountDeg -> offPrefix)
  have hStPtr3 : (s3.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutZero _ (Or.inl (by unfold statePtrAddr loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hStPtr2
  have hDegPtr3 : (s3.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m) := by
    rw [hOutZero _ (Or.inl (by unfold loopDegBase; omega))]
    exact hDegPtr2
  have hQS3 : ∀ j ≤ Q, (s3.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j) := by
    intro j hj
    have hNoLoop : emitBase + 2 * n + j < loopBase ∨ loopBase + loopWorkWords n m ≤ emitBase + 2 * n + j := by
      rcases hDisjLE with hl | hr
      · right; unfold emitterWorkWords at *; omega
      · left; unfold emitterWorkWords at hr; omega
    have hNoDeg : emitBase + 2 * n + j < loopDegBase loopBase n m ∨
        loopDegBase loopBase n m + n_d ≤ emitBase + 2 * n + j := by
      rcases hNoLoop with h | h
      · left; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
      · right; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
    rw [hOutZero _ hNoDeg, hOutPrep _ (by rcases hNoLoop with h | h <;> unfold loopWorkWords at * <;> omega)]
    exact hInv.qStarts j hj
  have hSrcOrig3 : ∀ (p : Nat) (hp : p < m_d),
      (s3.data[emitBase + 3 * n + 1 + (qStartFn S d + p)]?).map Fin.val =
        some ((S.emittedArcs dFin)[p]'hp).srcLocal := by
    intro p hp
    have hQend := qStartFn_le_arcCount S (d + 1)
    have hQsucc := qStartFn_succ S dFin.isLt
    have hBndE : emitBase + 3 * n + 1 + (qStartFn S d + p) < emitBase + emitterWorkWords n m := by
      unfold emitterWorkWords; omega
    have hNoLoop : emitBase + 3 * n + 1 + (qStartFn S d + p) < loopBase ∨
        loopBase + loopWorkWords n m ≤ emitBase + 3 * n + 1 + (qStartFn S d + p) := by
      rcases hDisjLE with hl | hr
      · right; omega
      · left; omega
    have hNoDeg : emitBase + 3 * n + 1 + (qStartFn S d + p) < loopDegBase loopBase n m ∨
        loopDegBase loopBase n m + n_d ≤ emitBase + 3 * n + 1 + (qStartFn S d + p) := by
      rcases hNoLoop with h | h
      · left; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
      · right; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
    rw [hOutZero _ hNoDeg, hOutPrep _ (by rcases hNoLoop with h | h <;> unfold loopWorkWords at * <;> omega)]
    exact (hInv.arcsUnsorted d (hQ ▸ hd) (Nat.le_refl _) p hp).1
  obtain ⟨s4, kCount, hkCount, hStCount, pc4, sz4, hRg4, hDegs4, hOutCount⟩ :=
    countDeg_steps subCode h32 input S hn hm hQ hd hFit hEmitFit hDisjLE hBits
      pc3 hRg3 sz3 hStPtr3 hDegPtr3 hQS3 hSrcOrig3 hDegsZero
  -- Step 4: prefixCursor_steps (offPrefix -> offScatter)
  have hNd4 : (s4.data[loopBase]?).map Fin.val = some n_d := by
    rw [hOutCount _ (Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
      hOutZero _ (Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
      hNd2]; rfl
  have hStPtr4 : (s4.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutCount _ (Or.inl (by unfold statePtrAddr loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hStPtr3
  have hDegPtr4 : (s4.data[loopSubStateBase loopBase n m + 11]?).map Fin.val = some (loopDegBase loopBase n m) := by
    rw [hOutCount _ (Or.inl (by unfold loopDegBase; omega))]; exact hDegPtr3
  have hCurPtr4 : (s4.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m) := by
    rw [hOutCount _ (Or.inl (by unfold loopDegBase; omega)),
      hOutZero _ (Or.inl (by unfold loopDegBase; omega)),
      hOutPrep _ (Or.inr (by unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hInv.curPtr
  obtain ⟨s5, kPref, hkPref, hStPref, pc5, sz5, hRg5, hCurs5, hOutPref⟩ :=
    prefixCursor_steps subCode h32 input hn_d hArcsBnd hm_d hFit hBits pc4 hRg4 sz4
      hNd4 hStPtr4 hDegPtr4 hCurPtr4 hDegs4
  -- Step 5: scatterSort_steps (offScatter -> offWB)
  have hMd5 : (s5.data[loopBase + 1]?).map Fin.val = some m_d := by
    rw [hOutPref _ (Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
      hOutCount _ (Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
      hOutZero _ (Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
      hMd2]; rfl
  have hStPtr5 : (s5.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutPref _ (Or.inl (by unfold statePtrAddr loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hStPtr4
  have hCurPtr5 : (s5.data[loopSubStateBase loopBase n m + 12]?).map Fin.val = some (loopCursorBase loopBase n m) := by
    rw [hOutPref _ (Or.inl (by unfold loopCursorBase loopDegBase; omega))]; exact hCurPtr4
  have hEntPtr5 : (s5.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m) := by
    rw [hOutPref _ (Or.inl (by unfold loopCursorBase loopDegBase; omega)),
      hOutCount _ (Or.inl (by unfold loopDegBase; omega)),
      hOutZero _ (Or.inl (by unfold loopDegBase; omega)),
      hOutPrep _ (Or.inr (by unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hInv.entPtr
  have hQS5 : ∀ j ≤ Q, (s5.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j) := by
    intro j hj
    have hNoLoop : emitBase + 2 * n + j < loopBase ∨ loopBase + loopWorkWords n m ≤ emitBase + 2 * n + j := by
      rcases hDisjLE with hl | hr <;> unfold emitterWorkWords loopWorkWords at * <;> omega
    have hNoDeg : emitBase + 2 * n + j < loopDegBase loopBase n m ∨
        loopDegBase loopBase n m + n_d ≤ emitBase + 2 * n + j := by
      rcases hNoLoop with h | h <;> unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at * <;> omega
    have hNoCur : emitBase + 2 * n + j < loopCursorBase loopBase n m ∨
        loopCursorBase loopBase n m + n_d ≤ emitBase + 2 * n + j := by
      rcases hNoLoop with h | h <;> unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at * <;> omega
    rw [hOutPref _ hNoCur, hOutCount _ hNoDeg]
    exact hQS3 j hj
  have hArcsOrig5 : ∀ (p : Nat) (hp : p < m_d),
      let ea := (S.emittedArcs dFin)[p]'hp
      (s5.data[emitBase + 3 * n + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.srcLocal ∧
      (s5.data[emitBase + 3 * n + m + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.headLocal ∧
      (s5.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p)]?).map Fin.val = some ea.tailEntry := by
    intro p hp
    have hQend := qStartFn_le_arcCount S (d + 1)
    have hQsucc := qStartFn_succ S dFin.isLt
    have hBnd1 : emitBase + 3 * n + 1 + (qStartFn S d + p) < emitBase + emitterWorkWords n m := by
      unfold emitterWorkWords; omega
    have hBnd2 : emitBase + 3 * n + m + 1 + (qStartFn S d + p) < emitBase + emitterWorkWords n m := by
      unfold emitterWorkWords; omega
    have hBnd3 : emitBase + 3 * n + 2 * m + 1 + (qStartFn S d + p) < emitBase + emitterWorkWords n m := by
      unfold emitterWorkWords; omega
    have hDisjOf : ∀ addr, emitBase ≤ addr → addr < emitBase + emitterWorkWords n m →
        (addr < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ addr) ∧
        (addr < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ addr) ∧
        (addr < loopBase ∨ loopBase + 3 ≤ addr) := by
      intro addr ha1 ha2
      rcases hDisjLE with hl | hr
      · refine ⟨Or.inr ?_, Or.inr ?_, Or.inr ?_⟩ <;>
          unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at * <;> omega
      · refine ⟨Or.inl ?_, Or.inl ?_, Or.inl ?_⟩ <;>
          unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at * <;> omega
    have d1 := hDisjOf _ (by omega) hBnd1
    have d2 := hDisjOf _ (by omega) hBnd2
    have d3 := hDisjOf _ (by omega) hBnd3
    have hOrig := hInv.arcsUnsorted d (hQ ▸ hd) (Nat.le_refl _) p hp
    refine ⟨?_, ?_, ?_⟩
    · rw [hOutPref _ d1.2.1, hOutCount _ d1.1, hOutZero _ d1.1, hOutPrep _ d1.2.2]; exact hOrig.1
    · rw [hOutPref _ d2.2.1, hOutCount _ d2.1, hOutZero _ d2.1, hOutPrep _ d2.2.2]; exact hOrig.2.1
    · rw [hOutPref _ d3.2.1, hOutCount _ d3.1, hOutZero _ d3.1, hOutPrep _ d3.2.2]; exact hOrig.2.2
  obtain ⟨s6, kScat, hkScat, hStScat, pc6, sz6, hRg6, hBuf6, hOutScat⟩ :=
    scatterSort_steps subCode h32 input S hn hm hQ hd hFit hEmitFit hDisjLE hBits
      pc5 sz5 hRg5 hMd5 hStPtr5 hCurPtr5 hEntPtr5 hCurs5 hQS5 hArcsOrig5
  -- Step 6: writeBack_steps (offWB -> offBranch)
  have hMd6 : (s6.data[loopBase + 1]?).map Fin.val = some m_d := by
    rw [hOutScat _ (Or.inl (by omega)) (Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))
      (Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hMd5
  have hStPtr6 : (s6.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    rw [hOutScat _ (Or.inl (by unfold statePtrAddr; omega))
      (Or.inl (by unfold statePtrAddr loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))
      (Or.inl (by unfold statePtrAddr loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hStPtr5
  have hEntPtr6 : (s6.data[loopSubStateBase loopBase n m + 13]?).map Fin.val = some (loopSortEntryBase loopBase n m) := by
    rw [hOutScat _ (Or.inr (by unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))
      (Or.inl (by unfold loopCursorBase loopDegBase; omega))
      (Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase; omega))]
    exact hEntPtr5
  have hQS6 : ∀ j ≤ Q, (s6.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j) := by
    intro j hj
    have hNoLoop : emitBase + 2 * n + j < loopBase ∨ loopBase + loopWorkWords n m ≤ emitBase + 2 * n + j := by
      rcases hDisjLE with hl | hr <;> unfold emitterWorkWords loopWorkWords at * <;> omega
    rw [hOutScat _
      (by rcases hNoLoop with h | h <;> unfold loopWorkWords at * <;> omega)
      (by rcases hNoLoop with h | h <;> unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at * <;> omega)
      (by rcases hNoLoop with h | h <;> unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at * <;> omega)]
    exact hQS5 j hj
  obtain ⟨s7, kWB, hkWB, hStWB, pc7, sz7, hRg7, hSorted7, hOutWB⟩ :=
    writeBack_steps subCode h32 input S hn hm hQ hd hFit hEmitFit hDisjLE hBits
      pc6 sz6 hRg6 hMd6 hStPtr6 hEntPtr6 hQS6 hBuf6
  -- Common frame helper from s7 back to s₀ across steps 1..6 (inside loopBase or emitBase[qStart d..d+1))
  have hLoopDisjEmit : ∀ addr, loopBase ≤ addr → addr < loopBase + loopWorkWords n m →
      addr < emitBase + 3 * n + 1 + qStartFn S d ∨
      emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr := by
    intro addr ha1 ha2
    rcases hDisjLE with hl | hr
    · left; omega
    · right; unfold emitterWorkWords at hr
      have := qStartFn_le_arcCount S (d + 1); omega
  have hS7OfLoop : ∀ addr, loopBase ≤ addr → addr < loopBase + loopWorkWords n m →
      s7.data[addr]? = s6.data[addr]? := by
    intro addr ha1 ha2
    apply hOutWB
    rcases hLoopDisjEmit addr ha1 ha2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  have hNd7 : (s7.data[loopBase]?).map Fin.val = some n_d := by
    rw [hS7OfLoop loopBase (Nat.le_refl _) (by unfold loopWorkWords; omega),
      hOutScat loopBase (Or.inl (by omega))
        (Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))
        (Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
      hOutPref loopBase (Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))]
    exact hNd4
  -- Step 7: branchOwner_steps (3 steps, offBranch -> offSmall / offLarge)
  obtain ⟨s8, hStBr, hPc8, hD8, hRg8⟩ :=
    branchOwner_steps subCode h32 input hFit hBits pc7 sz7 hRg7 hNd7
  have hSz8 : s8.data.size = workCap := by rw [hD8, sz7]
  -- Helper: preserve pointer slots and external frame from s₀ to s8
  have hFrame0to8 : ∀ addr,
      (addr < emitBase + 3 * n + 1 + qStartFn S d ∨
        (emitBase + 3 * n + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + qStartFn S d) ∨
        (emitBase + 3 * n + m + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + qStartFn S d) ∨
        emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr) →
      (addr < loopBase ∨ loopBase + 3 + 2 * m_d ≤ addr) →
      (addr < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ addr) →
      (addr < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ addr) →
      (addr < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ addr) →
      s8.data[addr]? = s₀.data[addr]? := by
    intro addr haE haL haD haC haEnt
    rw [hD8, hOutWB addr haE,
      hOutScat addr (by rcases haL with h | h; exact Or.inl (by omega); exact Or.inr h) haC haEnt,
      hOutPref addr haC, hOutCount addr haD, hOutZero addr haD,
      hOutPrep addr (by rcases haL with h | h; exact Or.inl h; exact Or.inr (by omega))]
  have hNoSmallRegion : ∀ addr, (addr = inPtrAddr ∨ addr = dataPtrAddr ∨ addr = statePtrAddr ∨
      (loopSubStateBase loopBase n m + 11 ≤ addr ∧ addr < loopSubStateBase loopBase n m + 16)) →
      (addr < emitBase + 3 * n + 1 + qStartFn S d ∨
        (emitBase + 3 * n + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + qStartFn S d) ∨
        (emitBase + 3 * n + m + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + qStartFn S d) ∨
        emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr) ∧
      (addr < loopBase ∨ loopBase + 3 + 2 * m_d ≤ addr) ∧
      (addr < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ addr) ∧
      (addr < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ addr) ∧
      (addr < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ addr) := by
    intro addr ha
    rcases ha with rfl | rfl | rfl | ha
    · refine ⟨Or.inl (by unfold inPtrAddr; omega), Or.inl (by unfold inPtrAddr; omega),
        Or.inl (by unfold inPtrAddr loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega),
        Or.inl (by unfold inPtrAddr loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega),
        Or.inl (by unfold inPtrAddr loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)⟩
    · refine ⟨Or.inl (by unfold dataPtrAddr; omega), Or.inl (by unfold dataPtrAddr; omega),
        Or.inl (by unfold dataPtrAddr loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega),
        Or.inl (by unfold dataPtrAddr loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega),
        Or.inl (by unfold dataPtrAddr loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)⟩
    · refine ⟨Or.inl (by unfold statePtrAddr; omega), Or.inl (by unfold statePtrAddr; omega),
        Or.inl (by unfold statePtrAddr loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega),
        Or.inl (by unfold statePtrAddr loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega),
        Or.inl (by unfold statePtrAddr loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)⟩
    · refine ⟨?_, Or.inr (by unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega),
        Or.inl (by unfold loopDegBase; omega),
        Or.inl (by unfold loopCursorBase loopDegBase; omega),
        Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase; omega)⟩
      rcases hDisjLE with hl | hr
      · left; unfold loopWorkWords loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega
      · right; right; right; unfold emitterWorkWords loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *
        have := qStartFn_le_arcCount S (d + 1); omega
  have hInPtr8 : (s8.data[inPtrAddr]?).map Fin.val = some (loopSubInBase loopBase) := by
    have p := hNoSmallRegion inPtrAddr (Or.inl rfl)
    rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.inPtr
  have hDatPtr8 : (s8.data[dataPtrAddr]?).map Fin.val = some (loopSubWorkBase loopBase n m) := by
    have p := hNoSmallRegion dataPtrAddr (Or.inr (Or.inl rfl))
    rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.datPtr
  have hStPtr8 : (s8.data[statePtrAddr]?).map Fin.val = some (loopSubStateBase loopBase n m) := by
    have p := hNoSmallRegion statePtrAddr (Or.inr (Or.inr (Or.inl rfl)))
    rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.stPtr
  have hPtrsPtr8 : (s8.data[loopSubStateBase loopBase n m + 14]?).map Fin.val = some (ownerForestPtrsBase loopBase n m) := by
    have p := hNoSmallRegion (loopSubStateBase loopBase n m + 14) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.ptrsPtr
  have hArenaPtr8 : (s8.data[loopSubStateBase loopBase n m + 15]?).map Fin.val = some (forestArenaBase loopBase n m) := by
    have p := hNoSmallRegion (loopSubStateBase loopBase n m + 15) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
    rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.arenaPtr
  have hPreStep : Steps code input (1 + 23 + kZero + kCount + kPref + kScat + kWB + 3) s₀ s8 :=
    ((((((((Steps.cons st0 (Steps.zero s1)).append hStPrep).append hStZero).append hStCount).append hStPref).append hStScat).append hStWB).append hStBr)
  have hMkInv : ∀ {fu' : Nat} {s9 : State (layout16 bits inputCap workCap hi hw)},
      forestUsed ≤ fu' →
      fu' ≤ 19 * ((ownerCounts S).take (d + 1)).sum →
      s9.pc = offHdr → s9.data.size = workCap →
      LoopIterRegs n m root Q treeBase emitBase loopBase (d + 1) fu' s9 →
      OwnerForestRecordWith S Extra dFin loopBase n m fu' s9.data →
      (∀ addr,
        (addr < loopSubWorkBase loopBase n m ∨
          (loopSubStateBase loopBase n m + 11 ≤ addr ∧ addr < ownerForestPtrsBase loopBase n m + 6 * d) ∨
          (ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr ∧ addr < forestArenaBase loopBase n m + forestUsed) ∨
          forestArenaBase loopBase n m + fu' ≤ addr) →
        s9.data[addr]? = s8.data[addr]?) →
      LoopIterInv S Extra subCode n m root Q emitBase loopBase (d + 1) fu' initData s9 := by
    intro fu' s9 hFuGe hFuLe hPc9 hSz9 hRg9 hRec9 hOut9
    have hFuArena : forestArenaBase loopBase n m + fu' ≤ loopBase + loopWorkWords n m := by
      have := ownerCounts_take_le S (d + 1)
      have : ((ownerCounts S).take (d + 1)).sum ≤ 2 * n := by omega
      unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase
        loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
    have hOf9 : ∀ addr, (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) →
        (addr < loopSubWorkBase loopBase n m ∨
          (loopSubStateBase loopBase n m + 11 ≤ addr ∧ addr < ownerForestPtrsBase loopBase n m + 6 * d) ∨
          (ownerForestPtrsBase loopBase n m + 6 * d + 6 ≤ addr ∧ addr < forestArenaBase loopBase n m + forestUsed) ∨
          forestArenaBase loopBase n m + fu' ≤ addr) := by
      intro addr ha
      rcases ha with h | h
      · left; unfold loopSubWorkBase rawInputCap; omega
      · right; right; right; omega
    refine
      { dLe := hd
        pcEq := hPc9
        dataSz := hSz9
        regs := hRg9
        usedLe := hFuLe
        inPtr := by
          rw [hOut9 _ (Or.inl (by unfold inPtrAddr loopSubWorkBase rawInputCap; omega))]
          exact hInPtr8
        datPtr := by
          rw [hOut9 _ (Or.inl (by unfold dataPtrAddr loopSubWorkBase rawInputCap; omega))]
          exact hDatPtr8
        stPtr := by
          rw [hOut9 _ (Or.inl (by unfold statePtrAddr loopSubWorkBase rawInputCap; omega))]
          exact hStPtr8
        degPtr := by
          rw [hOut9 _ (Or.inr (Or.inl ⟨by omega, by unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega⟩))]
          have p := hNoSmallRegion (loopSubStateBase loopBase n m + 11) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
          rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.degPtr
        curPtr := by
          rw [hOut9 _ (Or.inr (Or.inl ⟨by omega, by unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega⟩))]
          have p := hNoSmallRegion (loopSubStateBase loopBase n m + 12) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
          rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.curPtr
        entPtr := by
          rw [hOut9 _ (Or.inr (Or.inl ⟨by omega, by unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega⟩))]
          have p := hNoSmallRegion (loopSubStateBase loopBase n m + 13) (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩)))
          rw [hFrame0to8 _ p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2]; exact hInv.entPtr
        ptrsPtr := by
          rw [hOut9 _ (Or.inr (Or.inl ⟨by omega, by unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega⟩))]
          exact hPtrsPtr8
        arenaPtr := by
          rw [hOut9 _ (Or.inr (Or.inl ⟨by omega, by unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega⟩))]
          exact hArenaPtr8
        treeMem := fun k hk1 hk2 => by
          have hkNoLoop : k < loopBase ∨ loopBase + loopWorkWords n m ≤ k := by
            rcases hDisjTL with h | h
            · left; omega
            · right; omega
          have hkNoEmit : k < emitBase + 3 * n + 1 + qStartFn S d ∨
              emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ k := by
            rcases hDisjTE with h | h
            · left; omega
            · right; unfold emitterWorkWords at h; have := qStartFn_le_arcCount S (d + 1); omega
          have hkNoL1 : k < loopBase ∨ loopBase + 3 + 2 * m_d ≤ k := by
            rcases hkNoLoop with h | h
            · left; omega
            · right; unfold loopWorkWords at h; omega
          have hkNoD : k < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ k := by
            rcases hkNoLoop with h | h
            · left; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
            · right; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
          have hkNoC : k < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ k := by
            rcases hkNoLoop with h | h
            · left; unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
            · right; unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
          have hkNoEnt : k < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ k := by
            rcases hkNoLoop with h | h
            · left; unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
            · right; unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
          rw [hOut9 k (hOf9 k hkNoLoop),
            hFrame0to8 k (by rcases hkNoEmit with h | h; exact Or.inl h; exact Or.inr (Or.inr (Or.inr h)))
              hkNoL1 hkNoD hkNoC hkNoEnt]
          exact hInv.treeMem k hk1 hk2
        qStarts := fun j hj => by
          have hkNoLoop : emitBase + 2 * n + j < loopBase ∨ loopBase + loopWorkWords n m ≤ emitBase + 2 * n + j := by
            rcases hDisjLE with h | h
            · right; unfold emitterWorkWords at *; omega
            · left; unfold emitterWorkWords at h; omega
          rw [hOut9 _ (hOf9 _ hkNoLoop), hD8, hOutWB _ (Or.inl (by omega))]
          exact hQS6 j hj
        arcsUnsorted := fun j hj hdj p hp => by
          have hDJ : d + 1 ≤ j := hdj
          have hQmono : qStartFn S (d + 1) ≤ qStartFn S j :=
            qStartFn_mono S (d + 1) j hDJ (Nat.le_of_lt hj)
          have hQj1 : qStartFn S (j + 1) = qStartFn S j + (S.emittedArcs ⟨j, hj⟩).length :=
            qStartFn_succ S hj
          have hQend := qStartFn_le_arcCount S (j + 1)
          have hBnd1 : emitBase + 3 * n + 1 + (qStartFn S j + p) < emitBase + emitterWorkWords n m := by
            unfold emitterWorkWords; omega
          have hBnd2 : emitBase + 3 * n + m + 1 + (qStartFn S j + p) < emitBase + emitterWorkWords n m := by
            unfold emitterWorkWords; omega
          have hBnd3 : emitBase + 3 * n + 2 * m + 1 + (qStartFn S j + p) < emitBase + emitterWorkWords n m := by
            unfold emitterWorkWords; omega
          have hNoL : ∀ addr, emitBase ≤ addr → addr < emitBase + emitterWorkWords n m →
              (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) ∧
              (addr < loopBase ∨ loopBase + 3 + 2 * m_d ≤ addr) ∧
              (addr < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ addr) ∧
              (addr < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ addr) ∧
              (addr < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ addr) := by
            intro addr ha1 ha2
            rcases hDisjLE with hl | hr
            · refine ⟨Or.inr (by omega), Or.inr (by unfold loopWorkWords at *; omega),
                Or.inr (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega),
                Or.inr (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega),
                Or.inr (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega)⟩
            · refine ⟨Or.inl (by omega), Or.inl (by omega),
                Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega),
                Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega),
                Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega)⟩
          have a1 := hNoL _ (by omega) hBnd1
          have a2 := hNoL _ (by omega) hBnd2
          have a3 := hNoL _ (by omega) hBnd3
          have hOrig := hInv.arcsUnsorted j hj (by omega) p hp
          refine ⟨?_, ?_, ?_⟩
          · rw [hOut9 _ (hOf9 _ a1.1), hFrame0to8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) a1.2.1 a1.2.2.1 a1.2.2.2.1 a1.2.2.2.2]
            exact hOrig.1
          · rw [hOut9 _ (hOf9 _ a2.1), hFrame0to8 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) a2.2.1 a2.2.2.1 a2.2.2.2.1 a2.2.2.2.2]
            exact hOrig.2.1
          · rw [hOut9 _ (hOf9 _ a3.1), hFrame0to8 _ (Or.inr (Or.inr (Or.inr (by omega)))) a3.2.1 a3.2.2.1 a3.2.2.2.1 a3.2.2.2.2]
            exact hOrig.2.2
        arcsSorted := fun j hj hjd p hp => by
          have hBnd1 : emitBase + 3 * n + 1 + (qStartFn S j + p) < emitBase + emitterWorkWords n m := by
            have := qStartFn_succ S hj; have := qStartFn_le_arcCount S (j + 1); unfold emitterWorkWords; omega
          have hBnd2 : emitBase + 3 * n + m + 1 + (qStartFn S j + p) < emitBase + emitterWorkWords n m := by
            have := qStartFn_succ S hj; have := qStartFn_le_arcCount S (j + 1); unfold emitterWorkWords; omega
          have hBnd3 : emitBase + 3 * n + 2 * m + 1 + (qStartFn S j + p) < emitBase + emitterWorkWords n m := by
            have := qStartFn_succ S hj; have := qStartFn_le_arcCount S (j + 1); unfold emitterWorkWords; omega
          have hNoL : ∀ addr, emitBase ≤ addr → addr < emitBase + emitterWorkWords n m →
              (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) ∧
              (addr < loopBase ∨ loopBase + 3 + 2 * m_d ≤ addr) ∧
              (addr < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ addr) ∧
              (addr < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ addr) ∧
              (addr < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ addr) := by
            intro addr ha1 ha2
            rcases hDisjLE with hl | hr
            · refine ⟨Or.inr (by omega), Or.inr (by unfold loopWorkWords at *; omega),
                Or.inr (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega),
                Or.inr (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega),
                Or.inr (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega)⟩
            · refine ⟨Or.inl (by omega), Or.inl (by omega),
                Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega),
                Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega),
                Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega)⟩
          have a1 := hNoL _ (by omega) hBnd1
          have a2 := hNoL _ (by omega) hBnd2
          have a3 := hNoL _ (by omega) hBnd3
          by_cases hjEq : j = d
          · subst hjEq
            have hs7 := hSorted7 p hp
            refine ⟨?_, ?_, ?_⟩
            · rw [hOut9 _ (hOf9 _ a1.1), hD8]; exact hs7.1
            · rw [hOut9 _ (hOf9 _ a2.1), hD8]; exact hs7.2.1
            · rw [hOut9 _ (hOf9 _ a3.1), hD8]; exact hs7.2.2
          · have hjLt : j < d := by omega
            have hQsuccJ := qStartFn_succ S hj
            have hQmono : qStartFn S (j + 1) ≤ qStartFn S d :=
              qStartFn_mono S (j + 1) d hjLt (hQ ▸ Nat.le_of_lt hd)
            have hPrev := hInv.arcsSorted j hj hjLt p hp
            refine ⟨?_, ?_, ?_⟩
            · rw [hOut9 _ (hOf9 _ a1.1), hFrame0to8 _ (Or.inl (by omega)) a1.2.1 a1.2.2.1 a1.2.2.2.1 a1.2.2.2.2]
              exact hPrev.1
            · rw [hOut9 _ (hOf9 _ a2.1), hFrame0to8 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)) a2.2.1 a2.2.2.1 a2.2.2.2.1 a2.2.2.2.2]
              exact hPrev.2.1
            · rw [hOut9 _ (hOf9 _ a3.1), hFrame0to8 _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩))) a3.2.1 a3.2.2.1 a3.2.2.2.1 a3.2.2.2.2]
              exact hPrev.2.2
        forests := fun j hj hjd => by
          by_cases hjEq : j = d
          · subst hjEq; exact hRec9
          · have hjLt : j < d := by omega
            have hPrev := hInv.forests j hj hjLt
            have h8Rec : OwnerForestRecordWith S Extra ⟨j, hj⟩ loopBase n m forestUsed s8.data := by
              refine ownerForestRecordWith_mono S Extra ⟨j, hj⟩ (Nat.le_refl _) hPrev (fun k hk => ?_) (fun addr ha1 ha2 => ?_)
              · have hB1 : ownerForestPtrsBase loopBase n m + 6 * j + k ≥ loopBase + 3 + 2 * m_d := by
                  unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
                have hB2 : ownerForestPtrsBase loopBase n m + 6 * j + k ≥ loopSortEntryBase loopBase n m + m_d := by
                  unfold ownerForestPtrsBase loopSortEntryBase; omega
                have hB3 : ownerForestPtrsBase loopBase n m + 6 * j + k ≥ loopCursorBase loopBase n m + n_d := by
                  unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase; omega
                have hB4 : ownerForestPtrsBase loopBase n m + 6 * j + k ≥ loopDegBase loopBase n m + n_d := by
                  unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega
                have hNoE : ownerForestPtrsBase loopBase n m + 6 * j + k < emitBase + 3 * n + 1 + qStartFn S d ∨
                    emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ ownerForestPtrsBase loopBase n m + 6 * j + k := by
                  rcases hDisjLE with hl | hr
                  · left; unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
                  · right; unfold emitterWorkWords ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *
                    have := qStartFn_le_arcCount S (d + 1); omega
                exact hFrame0to8 _ (by rcases hNoE with h | h; exact Or.inl h; exact Or.inr (Or.inr (Or.inr h)))
                  (Or.inr hB1) (Or.inr hB4) (Or.inr hB3) (Or.inr hB2)
              · have hB1 : addr ≥ loopBase + 3 + 2 * m_d := by
                  unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *; omega
                have hB2 : addr ≥ loopSortEntryBase loopBase n m + m_d := by
                  unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase at *; omega
                have hB3 : addr ≥ loopCursorBase loopBase n m + n_d := by
                  unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase at *; omega
                have hB4 : addr ≥ loopDegBase loopBase n m + n_d := by
                  unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase at *; omega
                have hNoE : addr < emitBase + 3 * n + 1 + qStartFn S d ∨
                    emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr := by
                  rcases hDisjLE with hl | hr
                  · left; unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
                  · right; unfold emitterWorkWords forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap at *
                    have := qStartFn_le_arcCount S (d + 1); omega
                exact hFrame0to8 addr (by rcases hNoE with h | h; exact Or.inl h; exact Or.inr (Or.inr (Or.inr h)))
                  (Or.inr hB1) (Or.inr hB4) (Or.inr hB3) (Or.inr hB2)
            refine ownerForestRecordWith_mono S Extra ⟨j, hj⟩ hFuGe h8Rec (fun k hk => ?_) (fun addr ha1 ha2 => ?_)
            · have hjVal : (⟨j, hj⟩ : Fin dense.length).val = j := rfl
              apply hOut9
              right; left
              refine ⟨by unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase; omega, by omega⟩
            · apply hOut9
              right; right; left
              refine ⟨by unfold forestArenaBase at ha1; omega, ha2⟩
        frame := fun addr ha0 ha1 ha2 haE haL => by
          have haE' : addr < emitBase + 3 * n + 1 + qStartFn S d ∨
              (emitBase + 3 * n + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + m + 1 + qStartFn S d) ∨
              (emitBase + 3 * n + m + 1 + qStartFn S (d + 1) ≤ addr ∧ addr < emitBase + 3 * n + 2 * m + 1 + qStartFn S d) ∨
              emitBase + 3 * n + 2 * m + 1 + qStartFn S (d + 1) ≤ addr := by
            rcases haE with h | h
            · left; omega
            · right; right; right; unfold emitterWorkWords at h
              have := qStartFn_le_arcCount S (d + 1); omega
          have haL1 : addr < loopBase ∨ loopBase + 3 + 2 * m_d ≤ addr := by
            rcases haL with h | h
            · left; omega
            · right; unfold loopWorkWords at h; omega
          have haD : addr < loopDegBase loopBase n m ∨ loopDegBase loopBase n m + n_d ≤ addr := by
            rcases haL with h | h
            · left; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
            · right; unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
          have haC : addr < loopCursorBase loopBase n m ∨ loopCursorBase loopBase n m + n_d ≤ addr := by
            rcases haL with h | h
            · left; unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
            · right; unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
          have haEnt : addr < loopSortEntryBase loopBase n m ∨ loopSortEntryBase loopBase n m + m_d ≤ addr := by
            rcases haL with h | h
            · left; unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega
            · right; unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
          rw [hOut9 addr (hOf9 addr haL), hFrame0to8 addr haE' haL1 haD haC haEnt]
          exact hInv.frame addr ha0 ha1 ha2 haE haL }
  by_cases hSmall : n_d < 3
  · rw [ite_eq_left hSmall] at hPc8
    obtain ⟨s9, hStSmall, pc9, sz9, hRg9, hZeros9, hOut9⟩ :=
      smallBranch_steps subCode h32 input hdLtN hFit hBits hPc8 hSz8 hRg8 hStPtr8 hPtrsPtr8
    have hUsedSucc : forestUsed ≤ 19 * ((ownerCounts S).take (d + 1)).sum := by
      rw [ownerCounts_take_succ S (hQ ▸ hd)]
      exact Nat.le_trans hInv.usedLe (Nat.mul_le_mul_left 19 (Nat.le_add_right _ _))
    have hIterStep : (1 + 23 + kZero + kCount + kPref + kScat + kWB + 3) + 22 ≤
        47200 * ((n_d + m_d) * OracleContract.L n ^ 2) := by
      have hc1 : kCount ≤ 8 * m_d + 18 := hkCount
      have hc2 : kScat ≤ 56 * m_d + 10 := hkScat
      have hc3 : kWB ≤ 48 * m_d + 8 := hkWB
      have h1 : 1 + 23 + kZero + kCount + kPref + kScat + kWB + 3 + 22 ≤ 12 * n_d + 112 * m_d + 105 := by omega
      have h2 : 12 * n_d + 112 * m_d + 105 ≤ 47200 * (n_d + m_d) := by omega
      have h3 : 47200 * (n_d + m_d) ≤ 47200 * ((n_d + m_d) * OracleContract.L n ^ 2) := by
        calc 47200 * (n_d + m_d) = 47200 * ((n_d + m_d) * 1) := by rw [Nat.mul_one]
          _ ≤ 47200 * ((n_d + m_d) * OracleContract.L n ^ 2) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLSq)
      omega
    have hRec9 : OwnerForestRecordWith S Extra dFin loopBase n m forestUsed s9.data := by
      dsimp only [OwnerForestRecordWith]
      rw [ite_eq_left hSmall]
      exact hZeros9
    refine ⟨forestUsed, _, s9, hIterStep, hPreStep.append hStSmall,
      hMkInv (Nat.le_refl _) hUsedSucc pc9 sz9 hRg9 hRec9 fun addr ha => ?_⟩
    apply hOut9
    rcases ha with h | ⟨_, h2⟩ | ⟨h1, _⟩ | h
    · left; unfold ownerForestPtrsBase loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase; omega
    · left; exact h2
    · right; exact h1
    · right; unfold forestArenaBase at h; omega
  · rw [ite_eq_right hSmall] at hPc8
    have hLarge : 3 ≤ n_d := by omega
    have hNd8 : (s8.data[loopBase]?).map Fin.val = some n_d := by rw [hD8]; exact hNd7
    have hMd8 : (s8.data[loopBase + 1]?).map Fin.val = some m_d := by
      rw [hD8, hS7OfLoop (loopBase + 1) (by omega) (by unfold loopWorkWords; omega)]; exact hMd6
    have hSub0_8 : (s8.data[loopSubInBase loopBase]?).map Fin.val = some n_d := hNd8
    have hSub1_8 : (s8.data[loopSubInBase loopBase + 1]?).map Fin.val = some m_d := hMd8
    have hSub2_8 : (s8.data[loopSubInBase loopBase + 2]?).map Fin.val = some 0 := by
      unfold loopSubInBase
      rw [hD8, hS7OfLoop (loopBase + 2) (by omega) (by unfold loopWorkWords; omega),
        hOutScat (loopBase + 2) (Or.inl (by omega))
          (Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega))
          (Or.inl (by unfold loopSortEntryBase loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
        hOutPref (loopBase + 2) (Or.inl (by unfold loopCursorBase loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
        hOutCount (loopBase + 2) (Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
        hOutZero (loopBase + 2) (Or.inl (by unfold loopDegBase loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap; omega)),
        hZ2]; rfl
    have hSubArcs8 : ∀ (p : Nat) (hp : p < m_d),
        let ea := (countingSortedArcs n_d (S.emittedArcs dFin))[p]'(by
          rw [countingSortedArcs_length _ hArcsBnd]; exact hp)
        (s8.data[loopSubInBase loopBase + 3 + p]?).map Fin.val = some ea.srcLocal ∧
        (s8.data[loopSubInBase loopBase + 3 + m_d + p]?).map Fin.val = some ea.headLocal := by
      intro p hp
      have hb := hBuf6 p hp
      refine ⟨?_, ?_⟩
      · rw [hD8, hS7OfLoop (loopSubInBase loopBase + 3 + p) (by unfold loopSubInBase; omega) (by unfold loopSubInBase loopWorkWords; omega)]
        exact hb.1
      · rw [hD8, hS7OfLoop (loopSubInBase loopBase + 3 + m_d + p) (by unfold loopSubInBase; omega) (by unfold loopSubInBase loopWorkWords; omega)]
        exact hb.2.1
    have hArenaFit8 : forestUsed + 19 * n_d ≤ 38 * n := by
      have h1 : forestUsed + 19 * n_d ≤ 19 * ((ownerCounts S).take (d + 1)).sum := by
        calc forestUsed + 19 * n_d
            ≤ 19 * ((ownerCounts S).take d).sum + 19 * n_d := Nat.add_le_add_right hInv.usedLe (19 * n_d)
          _ = 19 * (((ownerCounts S).take d).sum + n_d) := (Nat.mul_add 19 _ _).symm
          _ = 19 * ((ownerCounts S).take (d + 1)).sum := by rw [ownerCounts_take_succ S (hQ ▸ hd)]
      have h2 := ownerCounts_take_le S (d + 1)
      omega
    obtain ⟨w, s9, kLarge, hkLarge, hwLe9, hIdx9, hEx9, hStLarge, pc9, sz9, hRg9, hPtrs9, hCopied9, hOut9⟩ :=
      largeBranch_steps_aux h32 input subCode S dFin hQ hQL hm_d hFit hBits hArenaFit8
        (Extra dFin) (hBuild dFin hLarge) hPc8 hSz8 hRg8 hInPtr8 hDatPtr8 hStPtr8 hNd8 hMd8 hPtrsPtr8 hArenaPtr8
        hSub0_8 hSub1_8 hSub2_8 hSubArcs8
    have hUsedSucc : forestUsed + w.wordCount ≤ 19 * ((ownerCounts S).take (d + 1)).sum := by
      rw [ownerCounts_take_succ S (hQ ▸ hd), Nat.mul_add]
      exact Nat.add_le_add hInv.usedLe hwLe9
    have hIterStep : (1 + 23 + kZero + kCount + kPref + kScat + kWB + 3) + kLarge ≤
        47200 * ((n_d + m_d) * OracleContract.L n ^ 2) := by
      have hc1 : kCount ≤ 8 * m_d + 18 := hkCount
      have hc2 : kScat ≤ 56 * m_d + 10 := hkScat
      have hc3 : kWB ≤ 48 * m_d + 8 := hkWB
      have hc4 : kLarge ≤ 47000 * ((n_d + m_d) * OracleContract.L n ^ 2) := hkLarge
      have h1 : 1 + 23 + kZero + kCount + kPref + kScat + kWB + 3 ≤ 12 * n_d + 112 * m_d + 83 := by omega
      have h2 : 12 * n_d + 112 * m_d + 83 ≤ 200 * (n_d + m_d) := by omega
      have h3 : 200 * (n_d + m_d) ≤ 200 * ((n_d + m_d) * OracleContract.L n ^ 2) := by
        calc 200 * (n_d + m_d) = 200 * ((n_d + m_d) * 1) := by rw [Nat.mul_one]
          _ ≤ 200 * ((n_d + m_d) * OracleContract.L n ^ 2) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLSq)
      omega
    have hRec9 : OwnerForestRecordWith S Extra dFin loopBase n m (forestUsed + w.wordCount) s9.data := by
      dsimp only [OwnerForestRecordWith]
      rw [ite_eq_right hSmall]
      have hp3 : (s9.data[ownerForestPtrsBase loopBase n m + 6 * dFin.val + 3]?).map Fin.val =
          some (forestArenaBase loopBase n m + forestUsed +
            (1 + 3 * ((w.dictionary[0]?).map Fin.val).getD 0) + 2 * (n_d + 1)) := by
        have hp := hPtrs9.2.2.2.1
        rw [Nat.add_assoc _ (n_d + 1) (n_d + 1), ← Nat.two_mul (n_d + 1)] at hp; exact hp
      have hp4 : (s9.data[ownerForestPtrsBase loopBase n m + 6 * dFin.val + 4]?).map Fin.val =
          some (forestArenaBase loopBase n m + forestUsed +
            (1 + 3 * ((w.dictionary[0]?).map Fin.val).getD 0) + 2 * (n_d + 1) + n_d) := by
        have hp := hPtrs9.2.2.2.2.1
        rw [Nat.add_assoc _ (n_d + 1) (n_d + 1), ← Nat.two_mul (n_d + 1)] at hp; exact hp
      have hp5 : (s9.data[ownerForestPtrsBase loopBase n m + 6 * dFin.val + 5]?).map Fin.val =
          some (forestArenaBase loopBase n m + forestUsed +
            (1 + 3 * ((w.dictionary[0]?).map Fin.val).getD 0) + 2 * (n_d + 1) + n_d + w.entry.size) := by
        have hp := hPtrs9.2.2.2.2.2
        rw [Nat.add_assoc _ (n_d + 1) (n_d + 1), ← Nat.two_mul (n_d + 1)] at hp; exact hp
      exact ⟨w, forestArenaBase loopBase n m + forestUsed, hEx9, hIdx9, hwLe9,
        Nat.le_add_right (forestArenaBase loopBase n m) forestUsed,
        by omega, hPtrs9.1, hPtrs9.2.1, hPtrs9.2.2.1, hp3, hp4, hp5, fun k hk => hCopied9 k hk⟩
    refine ⟨forestUsed + w.wordCount, _, s9, hIterStep, hPreStep.append hStLarge,
      hMkInv (Nat.le_add_right _ _) hUsedSucc pc9 sz9 hRg9 hRec9 fun addr ha => ?_⟩
    exact hOut9 addr (by simpa only [Nat.add_assoc] using ha)

private theorem familyForestLoop_aux {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q treeBase emitBase loopBase : Nat}
    {hsi : rawInputCap m ≤ 2 ^ bits} {hsw : rawWorkCap n m ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15))
    {origMem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origMem treeBase g r dense)
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (_hTree3 : 3 ≤ treeBase) (hEmit3 : 3 ≤ emitBase) (hLoop3 : 3 ≤ loopBase)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisjTE : treeBase + staticTreeWords Q ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ treeBase)
    (hDisjTL : treeBase + staticTreeWords Q ≤ loopBase ∨ loopBase + loopWorkWords n m ≤ treeBase)
    (hDisjLE : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    (Extra : Fin dense.length → WordColumns bits → Prop)
    (hBuild : ∀ (d : Fin dense.length), 3 ≤ 1 + (S.childSlice d).length →
      ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          Extra d w ∧
          run subCode subInput work (Phase.initial subStart) = some ⟨t, work⟩)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hTreeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s₀.data[k]? = origMem[k]?)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcsOrig : ∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (S.emittedArcs d)[p]'hp
      (s₀.data[emitBase + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) :
    let code := familyForestLoopCode (hi := hi) (hw := hw) subCode h32
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (states : List (PaperB.RamProgram.State (layout16 bits inputCap workCap hi hw)))
      (steps forestUsed : Nat),
      steps ≤ 94500 * ((n + m + 1) * OracleContract.L n ^ 2) ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint (layout16 bits inputCap workCap hi hw) ∧
      t.pc = code.size - 1 ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase Q forestUsed t ∧
      forestUsed ≤ 38 * n ∧
      t.data.size = workCap ∧
      (∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → t.data[k]? = origMem[k]?) ∧
      (∀ j ≤ Q, (t.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)) ∧
      (∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
        let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
          rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
        (t.data[emitBase + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
        (t.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
        (t.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) ∧
      (∀ d : Fin dense.length, OwnerForestRecordWith S Extra d loopBase n m forestUsed t.data) ∧
      (∀ addr,
        addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
        (addr < emitBase + 3 * n + 1 ∨ emitBase + emitterWorkWords n m ≤ addr) →
        (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hInitRg : LoopEntryRegs n m root Q treeBase emitBase loopBase (Phase.initial s₀) :=
    loopEntryRegs_of_keep hRegs (fun _ _ => rfl)
  obtain ⟨s48, hStInit, pc48, sz48, hRg48, hIn48, hDat48, hSt48, hS11_48, hS12_48, hS13_48, hS14_48, hS15_48, hOut48⟩ :=
    loopInit_steps subCode h32 input rfl hInitRg s₀.data_size hFit hBits
  have hTree48 : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s48.data[k]? = origMem[k]? := by
    intro k hk1 hk2
    have hNe : k ≠ inPtrAddr ∧ k ≠ dataPtrAddr ∧ k ≠ statePtrAddr := by
      unfold inPtrAddr dataPtrAddr statePtrAddr; omega
    have hOut : k < loopSubStateBase loopBase n m + 11 ∨ loopSubStateBase loopBase n m + 16 ≤ k := by
      rcases hDisjTL with h | h
      · left; unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
      · right; unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
    rw [hOut48 k hNe.1 hNe.2.1 hNe.2.2 hOut]; exact hTreeMem k hk1 hk2
  have hNoInitTouch : ∀ addr,
      (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) →
      addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
      s48.data[addr]? = s₀.data[addr]? := by
    intro addr haL h0 h1 h2
    apply hOut48 addr h0 h1 h2
    rcases haL with h | h
    · left; unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
    · right; unfold loopSubStateBase loopSubWorkBase rawInputCap rawWorkCap loopWorkWords at *; omega
  have hInv0 : LoopIterInv S Extra subCode n m root Q emitBase loopBase 0 0 s₀.data s48 :=
    { dLe := Nat.zero_le Q
      pcEq := pc48
      dataSz := sz48
      regs := hRg48
      usedLe := by simp [ownerCounts]
      inPtr := by rw [hIn48]; rfl
      datPtr := by rw [hDat48]; rfl
      stPtr := by rw [hSt48]; rfl
      degPtr := by rw [hS11_48]; rfl
      curPtr := by rw [hS12_48]; rfl
      entPtr := by rw [hS13_48]; rfl
      ptrsPtr := by rw [hS14_48]; rfl
      arenaPtr := by rw [hS15_48]; rfl
      treeMem := hTree48
      qStarts := fun j hj => by
        have hNoLoop : emitBase + 2 * n + j < loopBase ∨ loopBase + loopWorkWords n m ≤ emitBase + 2 * n + j := by
          rcases hDisjLE with h | h
          · right; unfold emitterWorkWords at *; omega
          · left; unfold emitterWorkWords at h; omega
        rw [hNoInitTouch _ hNoLoop (by unfold inPtrAddr; omega)
          (by unfold dataPtrAddr; omega) (by unfold statePtrAddr; omega)]
        exact hQStarts j hj
      arcsUnsorted := fun j hj _ p hp => by
        have hQsucc := qStartFn_succ S hj
        have hQend := qStartFn_le_arcCount S (j + 1)
        have h1 : emitBase + 3 * n + 1 + (qStartFn S j + p) < loopBase ∨
            loopBase + loopWorkWords n m ≤ emitBase + 3 * n + 1 + (qStartFn S j + p) := by
          rcases hDisjLE with h | h
          · right; unfold emitterWorkWords at *; omega
          · left; unfold emitterWorkWords at h; omega
        have h2 : emitBase + 3 * n + m + 1 + (qStartFn S j + p) < loopBase ∨
            loopBase + loopWorkWords n m ≤ emitBase + 3 * n + m + 1 + (qStartFn S j + p) := by
          rcases hDisjLE with h | h
          · right; unfold emitterWorkWords at *; omega
          · left; unfold emitterWorkWords at h; omega
        have h3 : emitBase + 3 * n + 2 * m + 1 + (qStartFn S j + p) < loopBase ∨
            loopBase + loopWorkWords n m ≤ emitBase + 3 * n + 2 * m + 1 + (qStartFn S j + p) := by
          rcases hDisjLE with h | h
          · right; unfold emitterWorkWords at *; omega
          · left; unfold emitterWorkWords at h; omega
        have hOrig := hArcsOrig ⟨j, hj⟩ p hp
        refine ⟨?_, ?_, ?_⟩
        · rw [hNoInitTouch _ h1 (by unfold inPtrAddr; omega)
            (by unfold dataPtrAddr; omega) (by unfold statePtrAddr; omega)]
          exact hOrig.1
        · rw [hNoInitTouch _ h2 (by unfold inPtrAddr; omega)
            (by unfold dataPtrAddr; omega) (by unfold statePtrAddr; omega)]
          exact hOrig.2.1
        · rw [hNoInitTouch _ h3 (by unfold inPtrAddr; omega)
            (by unfold dataPtrAddr; omega) (by unfold statePtrAddr; omega)]
          exact hOrig.2.2
      arcsSorted := fun _ _ h0 => by omega
      forests := fun _ _ h0 => by omega
      frame := fun addr h0 h1 h2 _ haL => hNoInitTouch addr haL h0 h1 h2 }
  let L := OracleContract.L n
  let pot : Nat × Nat → Nat := fun st =>
    47200 * ((2 * n - ((ownerCounts S).take st.1).sum + (qStartFn S Q - qStartFn S st.1)) * L ^ 2) + 1
  let post : Nat × Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun _ s =>
    ∃ fu', LoopIterInv S Extra subCode n m root Q emitBase loopBase Q fu' s₀.data
        { regs := s.regs, data := s.data, pc := offHdr,
          regs_size := s.regs_size, data_size := s.data_size } ∧
      s.pc = offHalt subCode.size
  let inv : Nat × Nat → State (layout16 bits inputCap workCap hi hw) → Prop := fun st s =>
    LoopIterInv S Extra subCode n m root Q emitBase loopBase st.1 st.2 s₀.data s
  have hSz : code.size = 396 + 4 * subCode.size := familyForestLoopCode_size subCode h32
  have hLoop := loop_steps_budget inv (fun st => Q - st.1) pot post
    (fun ⟨d, fu⟩ s hInv => by
      by_cases hdEq : d = Q
      · have hGe : (reg s r5).val ≤ (reg s r9).val := by
          rw [hInv.regs.dVal, hInv.regs.entry.qVal, hdEq]; exact Nat.le_refl _
        have stEnd := step16_branchLt_false code input hInv.pcEq (at_hdr subCode h32)
          (by rw [hSz]; unfold offHalt; omega) hGe
        let sEnd : State (layout16 bits inputCap workCap hi hw) :=
          { regs := s.regs, data := s.data, pc := offHalt subCode.size,
            regs_size := s.regs_size, data_size := s.data_size }
        let sBack : State (layout16 bits inputCap workCap hi hw) :=
          { regs := sEnd.regs, data := sEnd.data, pc := offHdr,
            regs_size := sEnd.regs_size, data_size := sEnd.data_size }
        have hInvQ : LoopIterInv S Extra subCode n m root Q emitBase loopBase Q fu s₀.data s := by
          have h' := hInv; dsimp only [inv] at h'; rw [hdEq] at h'; exact h'
        have hS' : sBack = s := by
          cases s with
          | mk r_ d_ pc_ rs_ ds_ =>
            have hpc : pc_ = offHdr := hInv.pcEq
            dsimp only [sBack, sEnd]
            rw [hpc]
        exact Or.inl ⟨sEnd, 1, by dsimp only [pot]; omega, steps_one stEnd,
          ⟨fu, by change LoopIterInv S Extra subCode n m root Q emitBase loopBase Q fu s₀.data sBack; rw [hS']; exact hInvQ, rfl⟩⟩
      · have hd : d < Q := Nat.lt_of_le_of_ne hInv.dLe hdEq
        obtain ⟨fu', iterSteps, s', hIterBnd, hStIter, hInv'⟩ :=
          familyForestLoop_iter_steps_aux h32 input subCode S hn hm hQ _hTree3 hEmit3 hLoop3
            hFit hTreeFit hEmitFit hDisjTE hDisjTL hDisjLE hBits Extra hBuild hd hInv
        let dFin : Fin dense.length := ⟨d, hQ ▸ hd⟩
        let n_d := 1 + (S.childSlice dFin).length
        let m_d := (S.emittedArcs dFin).length
        have hOwnSucc : ((ownerCounts S).take (d + 1)).sum = ((ownerCounts S).take d).sum + n_d :=
          ownerCounts_take_succ S (hQ ▸ hd)
        have hOwnLe : ((ownerCounts S).take (d + 1)).sum ≤ 2 * n := by
          have := ownerCounts_take_le S (d + 1); omega
        have hQSucc : qStartFn S (d + 1) = qStartFn S d + m_d := qStartFn_succ S (hQ ▸ hd)
        have hQMono : qStartFn S (d + 1) ≤ qStartFn S Q :=
          qStartFn_mono S (d + 1) Q (by omega) (hQ ▸ Nat.le_refl _)
        have hPotEq : pot (d + 1, fu') + 47200 * ((n_d + m_d) * L ^ 2) = pot (d, fu) := by
          dsimp only [pot]
          rw [hOwnSucc, hQSucc]
          have hSplit1 : (2 * n - ((ownerCounts S).take d).sum) =
              (2 * n - (((ownerCounts S).take d).sum + n_d)) + n_d := by omega
          have hSplit2 : qStartFn S Q - qStartFn S d =
              (qStartFn S Q - (qStartFn S d + m_d)) + m_d := by omega
          rw [hSplit1, hSplit2]
          have hMulEq : ((2 * n - (((ownerCounts S).take d).sum + n_d) + n_d) +
              (qStartFn S Q - (qStartFn S d + m_d) + m_d)) * L ^ 2 =
            ((2 * n - (((ownerCounts S).take d).sum + n_d)) + (qStartFn S Q - (qStartFn S d + m_d))) * L ^ 2 +
              (n_d + m_d) * L ^ 2 := by
            rw [← Nat.add_mul]
            exact congrArg (· * L ^ 2) (by omega)
          calc 47200 * ((2 * n - (((ownerCounts S).take d).sum + n_d) +
                (qStartFn S Q - (qStartFn S d + m_d))) * L ^ 2) + 1 + 47200 * ((n_d + m_d) * L ^ 2)
              = 47200 * (((2 * n - (((ownerCounts S).take d).sum + n_d) +
                  (qStartFn S Q - (qStartFn S d + m_d))) * L ^ 2) + (n_d + m_d) * L ^ 2) + 1 := by
                  rw [Nat.mul_add]; omega
            _ = 47200 * (((2 * n - (((ownerCounts S).take d).sum + n_d) + n_d) +
                  (qStartFn S Q - (qStartFn S d + m_d) + m_d)) * L ^ 2) + 1 := by
                  rw [← hMulEq]
            _ = 47200 * (((2 * n - (((ownerCounts S).take d).sum + n_d) + n_d) +
                  (qStartFn S Q - (qStartFn S d + m_d) + m_d)) * L ^ 2) + 1 := rfl
        have hStepPot : iterSteps + pot (d + 1, fu') ≤ pot (d, fu) := by
          calc iterSteps + pot (d + 1, fu')
              ≤ 47200 * ((n_d + m_d) * L ^ 2) + pot (d + 1, fu') := Nat.add_le_add_right hIterBnd _
            _ = pot (d + 1, fu') + 47200 * ((n_d + m_d) * L ^ 2) := Nat.add_comm _ _
            _ = pot (d, fu) := hPotEq
        exact Or.inr ⟨(d + 1, fu'), s', iterSteps, by omega, hStepPot, hStIter, hInv'⟩)
    (Q + 1) (0, 0) s48 (by omega) hInv0
  obtain ⟨_, t, kLoop, hkLoop, hStLoop, fuFinal, hInvFinal, hPcHalt⟩ := hLoop
  have hStop : step code input t = some (.halted t) :=
    step_halt_at (by rw [hPcHalt]; exact at_halt subCode h32)
  have hExec : run code input (48 + kLoop + 1) (Phase.initial s₀) = some ⟨t, 48 + kLoop + 1⟩ :=
    (hStInit.append hStLoop).halts hStop
  obtain ⟨states, hTrace⟩ := run_has_successfulTrace hExec
  have hLPos : 1 ≤ L := OracleContract.one_le_L n
  have hLSq : 1 ≤ L ^ 2 := by
    calc 1 = 1 * 1 := rfl
      _ ≤ L * L := Nat.mul_le_mul hLPos hLPos
      _ = L ^ 2 := (Nat.pow_two _).symm
  have hTotalSteps : 48 + kLoop + 1 ≤ 94500 * ((n + m + 1) * L ^ 2) := by
    have hPot0 : pot (0, 0) ≤ 47200 * ((2 * n + m) * L ^ 2) + 1 := by
      dsimp only [pot]
      simp only [ownerCounts, List.take_zero, List.sum_nil, Nat.sub_zero, qStartFn_zero]
      have hQEnd : qStartFn S Q ≤ m := hm ▸ (hQ ▸ qStartFn_le_arcCount S dense.length)
      have h1 : 2 * n + qStartFn S Q ≤ 2 * n + m := Nat.add_le_add_left hQEnd _
      exact Nat.add_le_add_right (Nat.mul_le_mul_left 47200 (Nat.mul_le_mul_right _ h1)) 1
    have h2 : 47200 * ((2 * n + m) * L ^ 2) ≤ 94400 * ((n + m) * L ^ 2) := by
      have h2nm : 2 * n + m ≤ 2 * (n + m) := by omega
      calc 47200 * ((2 * n + m) * L ^ 2)
          ≤ 47200 * ((2 * (n + m)) * L ^ 2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h2nm)
        _ = (47200 * 2) * ((n + m) * L ^ 2) := by
            rw [← Nat.mul_assoc 47200 (2 * (n + m)) (L ^ 2),
              ← Nat.mul_assoc 47200 2 (n + m),
              Nat.mul_assoc (47200 * 2) (n + m) (L ^ 2)]
        _ = 94400 * ((n + m) * L ^ 2) := rfl
    have h50 : 50 ≤ 100 * (1 * L ^ 2) := by
      calc 50 ≤ 100 * 1 := by omega
        _ ≤ 100 * (1 * L ^ 2) := Nat.mul_le_mul_left 100 (by simpa only [Nat.one_mul] using hLSq)
    have h100 : 100 * ((n + m + 1) * L ^ 2) = 100 * ((n + m) * L ^ 2) + 100 * (1 * L ^ 2) := by
      rw [← Nat.mul_add, ← Nat.add_mul]
    have h944 : 94400 * ((n + m) * L ^ 2) ≤ 94400 * ((n + m + 1) * L ^ 2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    omega
  have hPcFinal : t.pc = code.size - 1 := by
    rw [hSz, hPcHalt]; unfold offHalt; omega
  have hFuBnd : fuFinal ≤ 38 * n := by
    have := ownerCounts_take_le S Q
    exact Nat.le_trans hInvFinal.usedLe (by omega)
  exact ⟨t, states, 48 + kLoop + 1, fuFinal, hTotalSteps, hExec, hTrace, hTrace.peak_eq, hPcFinal,
    loopIterRegs_of_keep hInvFinal.regs (fun _ _ => rfl),
    hFuBnd, hInvFinal.dataSz, hInvFinal.treeMem, hInvFinal.qStarts,
    fun d p hp => hInvFinal.arcsSorted d.val d.isLt (hQ ▸ d.isLt) p hp,
    fun d => hInvFinal.forests d.val d.isLt (hQ ▸ d.isLt),
    hInvFinal.frame⟩

end PhaseSimulations

/-- Main correctness, complexity, workspace-footprint, and frame theorem for
`familyForestLoopProgram`:
starting from `StaticTreeSlice` + `RamQuotientEmitter` output in `[treeBase .. treeBase + 11*Q)` and
`[emitBase .. emitBase + emitterWorkWords n m)`, `familyForestLoopProgram` halts in
`≤ 94500 * ((n + m + 1) * OracleContract.L n ^ 2)` steps with peak live memory
`footprint (layout16 bits inputCap workCap hi hw)`, sorts every owner's emitted arcs in
`emitBase` in place, writes zeros for every small owner (`n_d < 3`), and materializes a
verified `SerializedProperLossIndex (S.ramQuotient d) w_d` together with its 6 bank pointers
at `ownerForestPtrsBase loopBase n m + 6 * d` for every large owner (`3 ≤ n_d`), while
preserving all data outside `[emitBase + 3*n + 1 .. emitBase + emitterWorkWords n m)`,
`[loopBase .. loopBase + loopWorkWords n m)`, and the 3 scratch pointer slots `0, 1, 2`. -/
theorem run_family_forest_loop {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {n m root Q treeBase emitBase loopBase : Nat}
    (hsi : rawInputCap m ≤ 2 ^ bits) (hsw : rawWorkCap n m ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origMem treeBase g r dense)
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (acyc : g.IsAcyclic) (hFlat : ∀ d : Fin dense.length, (S.ramQuotient d).IsFlat)
    (hTree3 : 3 ≤ treeBase) (hEmit3 : 3 ≤ emitBase) (hLoop3 : 3 ≤ loopBase)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisjTE : treeBase + staticTreeWords Q ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ treeBase)
    (hDisjTL : treeBase + staticTreeWords Q ≤ loopBase ∨ loopBase + loopWorkWords n m ≤ treeBase)
    (hDisjLE : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hTreeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s₀.data[k]? = origMem[k]?)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcsOrig : ∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (S.emittedArcs d)[p]'hp
      (s₀.data[emitBase + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) :
    let code := familyForestLoopProgram (hi := hi) (hw := hw) hsi hsw h32
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (states : List (PaperB.RamProgram.State (layout16 bits inputCap workCap hi hw)))
      (steps forestUsed : Nat),
      steps ≤ 94500 * ((n + m + 1) * OracleContract.L n ^ 2) ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint (layout16 bits inputCap workCap hi hw) ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase Q forestUsed t ∧
      forestUsed ≤ 38 * n ∧
      t.data.size = workCap ∧
      (∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → t.data[k]? = origMem[k]?) ∧
      (∀ j ≤ Q, (t.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)) ∧
      (∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
        let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
          rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
        (t.data[emitBase + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
        (t.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
        (t.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) ∧
      (∀ d : Fin dense.length,
        let n_d := 1 + (S.childSlice d).length
        if n_d < 3 then
          ∀ k < 6, (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
        else
          ∃ (w : WordColumns bits) (ptrBase : Nat),
            let D := ((w.dictionary[0]?).map Fin.val).getD 0
            SerializedProperLossIndex (S.ramQuotient d) w ∧
            w.wordCount ≤ 19 * n_d ∧
            forestArenaBase loopBase n m ≤ ptrBase ∧
            ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
            (∀ k < w.wordCount, t.data[ptrBase + k]? = (packedPayload w)[k]?)) ∧
      (∀ addr,
        addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
        (addr < emitBase + 3 * n + 1 ∨ emitBase + emitterWorkWords n m ≤ addr) →
        (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  have h8 : 8 ≤ 2 ^ bits := Nat.le_trans (by decide : 8 ≤ 32) h32
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hBuild : ∀ (d : Fin dense.length), 3 ≤ 1 + (S.childSlice d).length →
      ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          True ∧
          run (largeBuildProgram (bits := bits) (inputCap := rawInputCap m) (workCap := rawWorkCap n m) hsi hsw h8)
            subInput work (Phase.initial subStart) = some ⟨t, work⟩ := by
    intro d hLarge subInput subStart hRaw
    have hn_d : (S.ramQuotient d).vertexCount ≤ n :=
      Nat.le_trans (childSlice_succ_le_length S d) (hQ ▸ hQL)
    have hWorkBnd : rawWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤ rawWorkCap n m := by
      have hmEq : (S.ramQuotient d).arcCount = (S.emittedArcs d).length := ramQuotient_arcCount_eq S d
      have hm_d : (S.emittedArcs d).length ≤ m := hm ▸ emittedArcs_length_le_arcCount S d
      change rawWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤ rawWorkCap n m
      rw [hmEq]; unfold rawWorkCap; omega
    have hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits := by
      unfold loopWorkWords at hFit; omega
    obtain ⟨w, t, work, h1, h2, h3, h4, h5, h6, h7, h8', h9, h10, h11, h12, h13, h14⟩ := by
      simpa only [ramQuotient_arcCount_eq S d] using
        run_large_build_exact h8 (S.ramQuotient d) hLarge (hFlat d)
          (S.ramQuotient_isAcyclic acyc d) subInput hRaw hWorkBnd hWidth subStart
    exact ⟨w, t, work, h1, h2, h3, h4, h5, h6, h7, h8', h9, h10, h11, h12, h13, True.intro, h14⟩
  obtain ⟨t, states, steps, forestUsed, hSteps, hExec, hTrace, hPeak, _hPc, hRegsOut, hFu,
      hSzOut, hTreeOut, hQSOut, hArcsOut, hRecsOut, hFrameOut⟩ :=
    familyForestLoop_aux (hsi := hsi) (hsw := hsw) h32 input
      (largeBuildProgram (bits := bits) (inputCap := rawInputCap m) (workCap := rawWorkCap n m) hsi hsw h8)
      S hn hm hQ hTree3 hEmit3 hLoop3 hFit hTreeFit hEmitFit hDisjTE hDisjTL hDisjLE hBits
      (fun _ _ => True) hBuild hRegs hTreeMem hQStarts hArcsOrig
  refine ⟨t, states, steps, forestUsed, hSteps, hExec, hTrace, hPeak, hRegsOut, hFu,
    hSzOut, hTreeOut, hQSOut, hArcsOut, ?_, hFrameOut⟩
  intro d
  have hR := hRecsOut d
  dsimp only [OwnerForestRecordWith] at hR
  dsimp only
  by_cases hSm : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hSm] at hR ⊢
    exact hR
  · rw [ite_eq_right hSm] at hR ⊢
    rcases hR with ⟨w, ptrBase, _, hRest⟩
    exact ⟨w, ptrBase, hRest⟩

/-- Packed-witness variant of `run_family_forest_loop` exposing `t.pc = code.size - 1`
and the packed `OrderedReaderResult` / `packWordColumns` witnesses for every large owner. -/
theorem run_family_forest_loop_packed {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {n m root Q treeBase emitBase loopBase : Nat}
    (hsi : rawInputCap m ≤ 2 ^ bits) (hsw : rawWorkCap n m ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits)
    (input : Input (layout16 bits inputCap workCap hi hw))
    {origMem : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origMem treeBase g r dense)
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (acyc : g.IsAcyclic) (hFlat : ∀ d : Fin dense.length, (S.ramQuotient d).IsFlat)
    (hTree3 : 3 ≤ treeBase) (hEmit3 : 3 ≤ emitBase) (hLoop3 : 3 ≤ loopBase)
    (hFit : loopBase + loopWorkWords n m ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hEmitFit : emitBase + emitterWorkWords n m ≤ workCap)
    (hDisjTE : treeBase + staticTreeWords Q ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ treeBase)
    (hDisjTL : treeBase + staticTreeWords Q ≤ loopBase ∨ loopBase + loopWorkWords n m ≤ treeBase)
    (hDisjLE : loopBase + loopWorkWords n m ≤ emitBase ∨ emitBase + emitterWorkWords n m ≤ loopBase)
    (hBits : workCap < 2 ^ bits)
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hRegs : LoopEntryRegs n m root Q treeBase emitBase loopBase s₀)
    (hTreeMem : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → s₀.data[k]? = origMem[k]?)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcsOrig : ∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (S.emittedArcs d)[p]'hp
      (s₀.data[emitBase + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) :
    let code := familyForestLoopProgram (hi := hi) (hw := hw) hsi hsw h32
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (states : List (PaperB.RamProgram.State (layout16 bits inputCap workCap hi hw)))
      (steps forestUsed : Nat),
      steps ≤ 94500 * ((n + m + 1) * OracleContract.L n ^ 2) ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint (layout16 bits inputCap workCap hi hw) ∧
      t.pc = code.size - 1 ∧
      LoopIterRegs n m root Q treeBase emitBase loopBase Q forestUsed t ∧
      forestUsed ≤ 38 * n ∧
      t.data.size = workCap ∧
      (∀ k, treeBase ≤ k → k < treeBase + staticTreeWords Q → t.data[k]? = origMem[k]?) ∧
      (∀ j ≤ Q, (t.data[emitBase + 2 * n + j]?).map Fin.val = some (qStartFn S j)) ∧
      (∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
        let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
          rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
        (t.data[emitBase + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
        (t.data[emitBase + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
        (t.data[emitBase + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) ∧
      (∀ d : Fin dense.length,
        let n_d := 1 + (S.childSlice d).length
        if n_d < 3 then
          ∀ k < 6, (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
        else
          ∃ (pH : PaperB.ForestDictionary.Rows (S.ramQuotient d))
            (dataH : Array (Vertex (S.ramQuotient d)))
            (sizeH : dataH.size = (S.ramQuotient d).vertexCount)
            (rankH : Vertex (S.ramQuotient d) → Nat)
            (hlarge : 3 ≤ (S.ramQuotient d).vertexCount)
            (incH : ∀ i j : Fin (S.ramQuotient d).vertexCount, i.val < j.val →
              rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i) <
                rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH j))
            (covH : ∀ v : Vertex (S.ramQuotient d), ∃ i : Fin (S.ramQuotient d).vertexCount,
              _root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i = v)
            (rArcH : ∀ u v : Vertex (S.ramQuotient d), (S.ramQuotient d).HasQuotientArc u v → rankH u < rankH v)
            (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
            (hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits)
            (ptrBase : Nat),
            let w := packWordColumns ordResH hWidth
            let D := ((w.dictionary[0]?).map Fin.val).getD 0
            SerializedProperLossIndex (S.ramQuotient d) w ∧
            w.wordCount ≤ 19 * n_d ∧
            forestArenaBase loopBase n m ≤ ptrBase ∧
            ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
            (t.data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
            (∀ k < w.wordCount, t.data[ptrBase + k]? = (packedPayload w)[k]?)) ∧
      (∀ addr,
        addr ≠ inPtrAddr → addr ≠ dataPtrAddr → addr ≠ statePtrAddr →
        (addr < emitBase + 3 * n + 1 ∨ emitBase + emitterWorkWords n m ≤ addr) →
        (addr < loopBase ∨ loopBase + loopWorkWords n m ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  have h8 : 8 ≤ 2 ^ bits := Nat.le_trans (by decide : 8 ≤ 32) h32
  have hQL : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  let PackedExtra : Fin dense.length → WordColumns bits → Prop := fun d w =>
    ∃ (pH : PaperB.ForestDictionary.Rows (S.ramQuotient d))
      (dataH : Array (Vertex (S.ramQuotient d)))
      (sizeH : dataH.size = (S.ramQuotient d).vertexCount)
      (rankH : Vertex (S.ramQuotient d) → Nat)
      (hlarge : 3 ≤ (S.ramQuotient d).vertexCount)
      (incH : ∀ i j : Fin (S.ramQuotient d).vertexCount, i.val < j.val →
        rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i) <
          rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH j))
      (covH : ∀ v : Vertex (S.ramQuotient d), ∃ i : Fin (S.ramQuotient d).vertexCount,
        _root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i = v)
      (rArcH : ∀ u v : Vertex (S.ramQuotient d), (S.ramQuotient d).HasQuotientArc u v → rankH u < rankH v)
      (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
      (hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits),
      w = packWordColumns ordResH hWidth
  have hBuild : ∀ (d : Fin dense.length), 3 ≤ 1 + (S.childSlice d).length →
      ∀ (subInput : Input (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw))
        (subStart : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)),
        RawQuotientInput subInput (S.ramQuotient d) →
        let n_d := 1 + (S.childSlice d).length
        let m_d := (S.emittedArcs d).length
        let L := OracleContract.L (S.ramQuotient d).vertexCount
        ∃ (w : WordColumns bits) (t : State (RamForestProgram.layout bits (rawInputCap m) (rawWorkCap n m) hsi hsw)) (work : Nat),
          let D := ((w.dictionary[0]?).map Fin.val).getD 0
          w.wordCount ≤ rawWorkCap n m ∧
          w.wordCount ≤ 1 + 18 * n_d ∧
          w.wordCount ≤ 19 * n_d ∧
          1 ≤ w.entry.size ∧
          w.dictionary.size = 1 + 3 * D ∧
          w.back.tagAndFirst.size = n_d + 1 ∧
          w.back.second.size = n_d + 1 ∧
          w.labels.size = n_d ∧
          w.stop.size = w.entry.size ∧
          w.entry.size = 1 + (List.range D).foldl
            (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
          t.data.extract 0 w.wordCount = packedPayload w ∧
          work ≤ 11662 * ((n_d + m_d) * L ^ 2) ∧
          SerializedProperLossIndex (S.ramQuotient d) w ∧
          PackedExtra d w ∧
          run (largeBuildProgram (bits := bits) (inputCap := rawInputCap m) (workCap := rawWorkCap n m) hsi hsw h8)
            subInput work (Phase.initial subStart) = some ⟨t, work⟩ := by
    intro d hLarge subInput subStart hRaw
    have hn_d : (S.ramQuotient d).vertexCount ≤ n :=
      Nat.le_trans (childSlice_succ_le_length S d) (hQ ▸ hQL)
    have hWorkBnd : rawWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤ rawWorkCap n m := by
      have hmEq : (S.ramQuotient d).arcCount = (S.emittedArcs d).length := ramQuotient_arcCount_eq S d
      have hm_d : (S.emittedArcs d).length ≤ m := hm ▸ emittedArcs_length_le_arcCount S d
      change rawWorkCap (S.ramQuotient d).vertexCount (S.ramQuotient d).arcCount ≤ rawWorkCap n m
      rw [hmEq]; unfold rawWorkCap; omega
    have hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits := by
      unfold loopWorkWords at hFit; omega
    obtain ⟨pH, dataH, sizeH, rankH, incH, covH, rArcH, ordResH, t, work,
      h1, h2, h3, h4, h5, h6, h7, h8', h9, h10, h11, h12, h13, h14⟩ := by
      simpa only [ramQuotient_arcCount_eq S d] using
        run_large_build_packed h8 (S.ramQuotient d) hLarge (hFlat d)
          (S.ramQuotient_isAcyclic acyc d) subInput hRaw hWorkBnd hWidth subStart
    exact ⟨packWordColumns ordResH hWidth, t, work, h1, h2, h3, h4, h5, h6, h7, h8', h9, h10, h11, h12, h13,
      ⟨pH, dataH, sizeH, rankH, hLarge, incH, covH, rArcH, ordResH, hWidth, rfl⟩, h14⟩
  obtain ⟨t, states, steps, forestUsed, hSteps, hExec, hTrace, hPeak, hPc, hRegsOut, hFu,
      hSzOut, hTreeOut, hQSOut, hArcsOut, hRecsOut, hFrameOut⟩ :=
    familyForestLoop_aux (hsi := hsi) (hsw := hsw) h32 input
      (largeBuildProgram (bits := bits) (inputCap := rawInputCap m) (workCap := rawWorkCap n m) hsi hsw h8)
      S hn hm hQ hTree3 hEmit3 hLoop3 hFit hTreeFit hEmitFit hDisjTE hDisjTL hDisjLE hBits
      PackedExtra hBuild hRegs hTreeMem hQStarts hArcsOrig
  refine ⟨t, states, steps, forestUsed, hSteps, hExec, hTrace, hPeak, hPc, hRegsOut, hFu,
    hSzOut, hTreeOut, hQSOut, hArcsOut, ?_, hFrameOut⟩
  intro d
  have hR := hRecsOut d
  dsimp only [OwnerForestRecordWith] at hR
  dsimp only
  by_cases hSm : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hSm] at hR ⊢
    exact hR
  · rw [ite_eq_right hSm] at hR ⊢
    rcases hR with ⟨w, ptrBase,
      ⟨pH, dataH, sizeH, rankH, hlarge, incH, covH, rArcH, ordResH, hWidth, rfl⟩,
      hIdx, hWc, hLb, hUb, h0, h1, h2, h3, h4, h5, hPay⟩
    exact ⟨pH, dataH, sizeH, rankH, hlarge, incH, covH, rArcH, ordResH, hWidth, ptrBase,
      hIdx, hWc, hLb, hUb, h0, h1, h2, h3, h4, h5, hPay⟩

end PaperB.RamFamilyForestLoop
