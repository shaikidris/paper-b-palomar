module

public import PaperB.RamExitFamilyRom

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 100000

/-!
EX5.1 Exit-Summary Family Loop Program and End-to-End Proof (`PaperB.RamExitFamilyLoop`):
Sections 3–5 constructing `exitFamilyLoopProgram` and proving `run_exit_family_loop`,
chaining from `prefixAndForestLoopProgram` into `sealedPackAndShiftProgram`.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
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

section ProgramCode

theorem sp_initA {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitInitACode h100) offInitA := by
  intro j hj
  have hLen : j < 25 := by simpa only [exitInitACode_size] using hj
  have hPrefix : offInitA + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offInitA; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offInitA]; omega)]
  rw [Array.getElem?_append_left (by simp only [sec0_size, offInitA]; omega)]
  rw [sec0]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, exitInitACode_size, exitInitBCode_size, offInitA]; omega)]
  rw [Array.getElem?_append_left (by simp only [exitInitACode_size, offInitA]; omega)]
  rw [show offInitA + j = j by unfold offInitA; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_initB {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitInitBCode workCap hw h100) offInitB := by
  intro j hj
  have hLen : j < 22 := by simpa only [exitInitBCode_size] using hj
  have hPrefix : offInitB + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offInitB; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offInitB]; omega)]
  rw [Array.getElem?_append_left (by simp only [sec0_size, offInitB]; omega)]
  rw [sec0]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, exitInitACode_size, exitInitBCode_size, offInitB]; omega)]
  rw [Array.getElem?_append_right (by simp only [exitInitACode_size, offInitB]; omega)]
  simp only [exitInitACode_size]
  rw [show offInitB + j - 25 = j by unfold offInitB; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_hdr {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitHdrCode bits subCode.size) offHdr := by
  intro j hj
  have hLen : j < 1 := by simpa only [exitHdrCode_size] using hj
  have hPrefix : offHdr + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offHdr; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offHdr]; omega)]
  rw [Array.getElem?_append_left (by simp only [sec0_size, offHdr]; omega)]
  rw [sec0]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitInitACode_size, exitInitBCode_size, offHdr]; omega)]
  simp only [Array.size_append, exitInitACode_size, exitInitBCode_size]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, exitHdrCode_size, exitPrepCode_size, offHdr]; omega)]
  rw [Array.getElem?_append_left (by simp only [exitHdrCode_size, offHdr]; omega)]
  rw [show offHdr + j - 47 = j by unfold offHdr; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_prep {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitPrepCode h100) offPrep := by
  intro j hj
  have hLen : j < 13 := by simpa only [exitPrepCode_size] using hj
  have hPrefix : offPrep + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offPrep; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offPrep]; omega)]
  rw [Array.getElem?_append_left (by simp only [sec0_size, offPrep]; omega)]
  rw [sec0]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitInitACode_size, exitInitBCode_size, offPrep]; omega)]
  simp only [Array.size_append, exitInitACode_size, exitInitBCode_size]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, exitHdrCode_size, exitPrepCode_size, offPrep]; omega)]
  rw [Array.getElem?_append_right (by simp only [exitHdrCode_size, offPrep]; omega)]
  simp only [exitHdrCode_size]
  rw [show offPrep + j - 47 - 1 = j by unfold offPrep; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_small {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitSmallCode h100) offSmall := by
  intro j hj
  have hLen : j < 15 := by simpa only [exitSmallCode_size] using hj
  have hPrefix : offSmall + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offSmall; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offSmall]; omega)]
  rw [Array.getElem?_append_left (by simp only [sec0_size, offSmall]; omega)]
  rw [sec0]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitInitACode_size, exitInitBCode_size, offSmall]; omega)]
  simp only [Array.size_append, exitInitACode_size, exitInitBCode_size]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitHdrCode_size, exitPrepCode_size, offSmall]; omega)]
  simp only [Array.size_append, exitHdrCode_size, exitPrepCode_size]
  rw [show offSmall + j - 47 - 14 = j by unfold offSmall; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_largeA {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitLargeACode h100) offLargeA := by
  intro j hj
  have hLen : j < 19 := by simpa only [exitLargeACode_size] using hj
  have hPrefix : offLargeA + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offLargeA; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offLargeA]; omega)]
  rw [Array.getElem?_append_right (by simp only [sec0_size, offLargeA]; omega)]
  simp only [sec0_size]
  rw [sec1]
  rw [Array.getElem?_append_left (by simp only [exitLargeACode_size, offLargeA]; omega)]
  rw [show offLargeA + j - 76 = j by unfold offLargeA; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_largeB {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitLargeBCode h100) offLargeB := by
  intro j hj
  have hLen : j < 28 := by simpa only [exitLargeBCode_size] using hj
  have hPrefix : offLargeB + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offLargeB; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, sec0_size, sec1_size, offLargeB]; omega)]
  rw [Array.getElem?_append_right (by simp only [sec0_size, offLargeB]; omega)]
  simp only [sec0_size]
  rw [sec1]
  rw [Array.getElem?_append_right (by simp only [exitLargeACode_size, offLargeB]; omega)]
  simp only [exitLargeACode_size]
  rw [show offLargeB + j - 76 - 19 = j by unfold offLargeB; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_fp0 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 0) 3 0) (offFp 0) := by
  intro j hj
  have hLen : j < 19 := by simpa only [copyFromFpBlock_size] using hj
  have hPrefix : offFp 0 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offFp; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offFp]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_left (by simp only [sec2_size, offFp]; omega)]
  rw [sec2]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  rw [Array.getElem?_append_left (by simp only [copyFromFpBlock_size, offFp]; omega)]
  rw [show offFp 0 + j - 123 = j by unfold offFp; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_fp1 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 1) 1 2) (offFp 1) := by
  intro j hj
  have hLen : j < 19 := by simpa only [copyFromFpBlock_size] using hj
  have hPrefix : offFp 1 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offFp; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offFp]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_left (by simp only [sec2_size, offFp]; omega)]
  rw [sec2]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  rw [Array.getElem?_append_right (by simp only [copyFromFpBlock_size, offFp]; omega)]
  simp only [copyFromFpBlock_size]
  rw [show offFp 1 + j - 123 - 19 = j by unfold offFp; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_fp2 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 2) 2 2) (offFp 2) := by
  intro j hj
  have hLen : j < 19 := by simpa only [copyFromFpBlock_size] using hj
  have hPrefix : offFp 2 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offFp; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offFp]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_left (by simp only [sec2_size, offFp]; omega)]
  rw [sec2]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  simp only [Array.size_append, copyFromFpBlock_size]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  rw [Array.getElem?_append_left (by simp only [copyFromFpBlock_size, offFp]; omega)]
  rw [show offFp 2 + j - 123 - 38 = j by unfold offFp; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_fp3 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 3) 4 2) (offFp 3) := by
  intro j hj
  have hLen : j < 19 := by simpa only [copyFromFpBlock_size] using hj
  have hPrefix : offFp 3 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offFp; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offFp]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_left (by simp only [sec2_size, offFp]; omega)]
  rw [sec2]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  simp only [Array.size_append, copyFromFpBlock_size]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  rw [Array.getElem?_append_right (by simp only [copyFromFpBlock_size, offFp]; omega)]
  simp only [copyFromFpBlock_size]
  rw [show offFp 3 + j - 123 - 38 - 19 = j by unfold offFp; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_fp4 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 4) 5 2) (offFp 4) := by
  intro j hj
  have hLen : j < 19 := by simpa only [copyFromFpBlock_size] using hj
  have hPrefix : offFp 4 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offFp; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offFp]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_left (by simp only [sec2_size, offFp]; omega)]
  rw [sec2]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  simp only [Array.size_append, copyFromFpBlock_size]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, copyFromFpBlock_size, offFp]; omega)]
  simp only [Array.size_append, copyFromFpBlock_size]
  rw [show offFp 4 + j - 123 - 38 - 38 = j by unfold offFp; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_emit0 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromEmitBlock (hi := hi) (hw := hw) (offEmit 0) ⟨0, by decide⟩) (offEmit 0) := by
  intro j hj
  have hLen : j < 21 := by simpa only [copyFromEmitBlock_size] using hj
  have hPrefix : offEmit 0 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offEmit; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offEmit]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_right (by simp only [sec2_size, offEmit]; omega)]
  simp only [sec2_size]
  rw [sec3]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromEmitBlock_size, offEmit]; omega)]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromEmitBlock_size, offEmit]; omega)]
  rw [Array.getElem?_append_left (by simp only [copyFromEmitBlock_size, offEmit]; omega)]
  rw [show offEmit 0 + j - 123 - 95 = j by unfold offEmit; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_emit1 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromEmitBlock (hi := hi) (hw := hw) (offEmit 1) ⟨1, by decide⟩) (offEmit 1) := by
  intro j hj
  have hLen : j < 21 := by simpa only [copyFromEmitBlock_size] using hj
  have hPrefix : offEmit 1 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offEmit; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offEmit]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_right (by simp only [sec2_size, offEmit]; omega)]
  simp only [sec2_size]
  rw [sec3]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromEmitBlock_size, offEmit]; omega)]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromEmitBlock_size, offEmit]; omega)]
  rw [Array.getElem?_append_right (by simp only [copyFromEmitBlock_size, offEmit]; omega)]
  simp only [copyFromEmitBlock_size]
  rw [show offEmit 1 + j - 123 - 95 - 21 = j by unfold offEmit; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_emit2 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyFromEmitBlock (hi := hi) (hw := hw) (offEmit 2) ⟨2, by decide⟩) (offEmit 2) := by
  intro j hj
  have hLen : j < 21 := by simpa only [copyFromEmitBlock_size] using hj
  have hPrefix : offEmit 2 + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offEmit; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offEmit]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_right (by simp only [sec2_size, offEmit]; omega)]
  simp only [sec2_size]
  rw [sec3]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, copyFromEmitBlock_size, offEmit]; omega)]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, copyFromEmitBlock_size, offEmit]; omega)]
  simp only [Array.size_append, copyFromEmitBlock_size]
  rw [show offEmit 2 + j - 123 - 95 - 42 = j by unfold offEmit; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_saveRegs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) (exitSaveRegsCode h100) offSave := by
  intro j hj
  have hLen : j < 23 := by simpa only [exitSaveRegsCode_size] using hj
  have hPrefix : offSave + j < (exitPrefixCode (hi := hi) (hw := hw) subCode.size h100).size := by
    rw [exitPrefixCode_size]; unfold offSave; omega
  rw [exitFamilyLoopCodeOf,
    Array.getElem?_append_left (Nat.lt_of_lt_of_le hPrefix (by rw [Array.size_append]; omega)),
    Array.getElem?_append_left hPrefix]
  rw [exitPrefixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, sec0_size, sec1_size, offSave]; omega)]
  simp only [Array.size_append, sec0_size, sec1_size]
  rw [Array.getElem?_append_right (by simp only [sec2_size, offSave]; omega)]
  simp only [sec2_size]
  rw [sec3]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, copyFromEmitBlock_size, offSave]; omega)]
  simp only [Array.size_append, copyFromEmitBlock_size]
  rw [show offSave + j - 123 - 95 - 63 = j by unfold offSave; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_restoreRegs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (exitRestoreRegsCode h100) (offRestore subCode.size) := by
  intro j hj
  have hLen : j < 24 := by simpa only [exitRestoreRegsCode_size] using hj
  rw [exitFamilyLoopCodeOf, Array.getElem?_append_right (by
    rw [Array.size_append, exitPrefixCode_size, liftedExitSlice_size]; unfold offRestore; omega),
    Array.size_append, exitPrefixCode_size, liftedExitSlice_size]
  rw [exitSuffixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size, offRestore]; omega)]
  rw [Array.getElem?_append_left (by simp only [exitRestoreRegsCode_size, offRestore]; omega)]
  rw [show offRestore subCode.size + j - (304 + 4 * subCode.size) = j by unfold offRestore; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_postSetup {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (exitPostSetupCode h100) (offPostSetup subCode.size) := by
  intro j hj
  have hLen : j < 43 := by simpa only [exitPostSetupCode_size] using hj
  rw [exitFamilyLoopCodeOf, Array.getElem?_append_right (by
    rw [Array.size_append, exitPrefixCode_size, liftedExitSlice_size]; unfold offPostSetup; omega),
    Array.size_append, exitPrefixCode_size, liftedExitSlice_size]
  rw [exitSuffixCode]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size, offPostSetup]; omega)]
  rw [Array.getElem?_append_right (by simp only [exitRestoreRegsCode_size, offPostSetup]; omega)]
  simp only [exitRestoreRegsCode_size]
  rw [show offPostSetup subCode.size + j - (304 + 4 * subCode.size) - 24 = j by unfold offPostSetup; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_postCopy {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (copyLoopCode (hi := hi) (hw := hw) (offPostCopy subCode.size) (offPostStep subCode.size))
      (offPostCopy subCode.size) := by
  intro j hj
  have hCopySize (p q : Nat) :
      (copyLoopCode (hi := hi) (hw := hw) p q).size = 6 := rfl
  have hLen : j < 6 := hj
  rw [exitFamilyLoopCodeOf, Array.getElem?_append_right (by
    rw [Array.size_append, exitPrefixCode_size, liftedExitSlice_size]; unfold offPostCopy; omega),
    Array.size_append, exitPrefixCode_size, liftedExitSlice_size]
  rw [exitSuffixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size, offPostCopy]; omega)]
  simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, hCopySize, exitPostStepCode_size, offPostCopy]; omega)]
  rw [Array.getElem?_append_left (by simp only [hCopySize, offPostCopy]; omega)]
  rw [show offPostCopy subCode.size + j - (304 + 4 * subCode.size) - 67 = j by unfold offPostCopy; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_postStep {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      exitPostStepCode (offPostStep subCode.size) := by
  intro j hj
  have hCopySize (p q : Nat) :
      (copyLoopCode (hi := hi) (hw := hw) p q).size = 6 := rfl
  have hLen : j < 3 := by simpa only [exitPostStepCode_size] using hj
  rw [exitFamilyLoopCodeOf, Array.getElem?_append_right (by
    rw [Array.size_append, exitPrefixCode_size, liftedExitSlice_size]; unfold offPostStep; omega),
    Array.size_append, exitPrefixCode_size, liftedExitSlice_size]
  rw [exitSuffixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size, offPostStep]; omega)]
  simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size]
  rw [Array.getElem?_append_left (by simp only [Array.size_append, hCopySize, exitPostStepCode_size, offPostStep]; omega)]
  rw [Array.getElem?_append_right (by simp only [hCopySize, offPostStep]; omega)]
  simp only [hCopySize]
  rw [show offPostStep subCode.size + j - (304 + 4 * subCode.size) - 67 - 6 = j by unfold offPostStep; omega]
  exact Array.getElem?_eq_getElem hj

theorem sp_finish {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    SlicePlaced (hi := hi) (hw := hw) (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100)
      (exitFinishCode h100) (offFinish subCode.size) := by
  intro j hj
  have hCopySize (p q : Nat) :
      (copyLoopCode (hi := hi) (hw := hw) p q).size = 6 := rfl
  have hLen : j < 17 := by simpa only [exitFinishCode_size] using hj
  rw [exitFamilyLoopCodeOf, Array.getElem?_append_right (by
    rw [Array.size_append, exitPrefixCode_size, liftedExitSlice_size]; unfold offFinish; omega),
    Array.size_append, exitPrefixCode_size, liftedExitSlice_size]
  rw [exitSuffixCode]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size, offFinish]; omega)]
  simp only [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size]
  rw [Array.getElem?_append_right (by simp only [Array.size_append, hCopySize, exitPostStepCode_size, offFinish]; omega)]
  simp only [Array.size_append, hCopySize, exitPostStepCode_size]
  rw [show offFinish subCode.size + j - (304 + 4 * subCode.size) - 67 - 9 = j by unfold offFinish; omega]
  exact Array.getElem?_eq_getElem hj

theorem bodyRelocated_exitSub {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    BodyRelocated (bits := bits) (bigL := layout16 bits inputCap workCap hi hw) rfl
      (w100 h100 inPtrAddr) (w100 h100 dataPtrAddr) subCode
      (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) offSub := by
  intro i hiLt op hop
  let σ := liftCode (w100 h100 inPtrAddr) (w100 h100 dataPtrAddr) subCode
  let cut := σ.extract 0 (4 * subCode.size)
  have hCutSz : cut.size = 4 * subCode.size := by
    simp only [cut, σ, Array.size_extract, liftCode_size, Nat.sub_zero]
    omega
  have hCutLt : i < cut.size := by rw [hCutSz]; exact hiLt
  have hLiftLt : i < σ.size := by simp only [σ, liftCode_size]; omega
  have hWord : σ[i]'hLiftLt = op :=
    Option.some.inj ((Array.getElem?_eq_getElem hLiftLt).symm.trans hop)
  have hCut : cut[i]'hCutLt = σ[i]'hLiftLt := by
    simp only [cut, Array.getElem_extract, Nat.zero_add]
  have hLift : (liftedExitSlice subCode h100)[i]? = some (relocateInstr offSub op) := by
    change (cut.map (relocateInstr offSub))[i]? = _
    rw [Array.getElem?_eq_getElem (by rw [Array.size_map]; exact hCutLt),
      Array.getElem_map, hCut, hWord]
  let a := exitPrefixCode (hi := hi) (hw := hw) subCode.size h100
  let b := liftedExitSlice subCode h100
  let c := exitSuffixCode (hi := hi) (hw := hw) subCode.size h100
  have hA : a.size = offSub := exitPrefixCode_size subCode.size h100
  have hB : i < b.size := by simp only [b, liftedExitSlice_size]; exact hiLt
  change ((a ++ b) ++ c)[offSub + i]? = some (relocateInstr offSub op)
  rw [Array.getElem?_append_left (by rw [Array.size_append, hA]; omega),
    Array.getElem?_append_right (by rw [hA]; omega), hA,
    show offSub + i - offSub = i by omega]
  exact hLift

end ProgramCode

end PaperB.RamExitFamilyLoop
