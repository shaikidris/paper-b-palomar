module

public import PaperB.RamExitFamilyLayout

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

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

open PaperB.RamProgram (Instr)

abbrev r0 : Fin 16 := rZero
abbrev r1 : Fin 16 := rOne
abbrev r2 : Fin 16 := rN
abbrev r3 : Fin 16 := rM
abbrev r4 : Fin 16 := rRoot

def w100 {bits : Nat} (h100 : 100 ≤ 2 ^ bits) (k : Nat) (hk : k < 100 := by decide) :
    Word bits :=
  ⟨k, Nat.lt_of_lt_of_le hk h100⟩

def offInitA : Nat := 0
def offInitB : Nat := 25
def offHdr : Nat := 47
def offPrep : Nat := 48
def offSmall : Nat := 61
def offLargeA : Nat := 76
def offLargeB : Nat := 95
def offFp (k : Nat) : Nat := 123 + 19 * k
def offEmit (k : Nat) : Nat := 218 + 21 * k
def offSave : Nat := 281
def offSub : Nat := 304
def offRestore (subLen : Nat) : Nat := 304 + 4 * subLen
def offPostSetup (subLen : Nat) : Nat := 328 + 4 * subLen
def offPostCopy (subLen : Nat) : Nat := 371 + 4 * subLen
def offPostStep (subLen : Nat) : Nat := 377 + 4 * subLen
def offFinish (subLen : Nat) : Nat := 380 + 4 * subLen

/-- `25` instructions: compute `r11 = exitPtrsBase`, `r12 = exitArenaBase`, `r13 = exitSubStateBase`. -/
def exitInitACode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.add r11 r2 r2,
    .add r12 r11 r11,
    .add r11 r11 r12,
    .add r12 r12 r12,
    .add r11 r11 r12,
    .add r12 r12 r12,
    .add r12 r12 r12,
    .add r12 r12 r12,
    .add r11 r11 r12,
    .add r12 r3 r3,
    .add r13 r12 r12,
    .add r13 r13 r13,
    .add r12 r12 r13,
    .add r11 r11 r12,
    .imm r12 (w100 h100 37),
    .add r11 r11 r12,
    .add r11 r8 r11,
    .add r13 r2 r2,
    .add r13 r13 r2,
    .add r12 r11 r13,
    .add r14 r13 r13,
    .add r14 r14 r14,
    .add r14 r14 r14,
    .add r14 r14 r14,
    .add r13 r12 r14]

/-- `22` instructions: store pointers in `mem[0..2]` and `mem[st + 11..14]`, zero `r9, r10`. -/
def exitInitBCode {bits : Nat} (workCap : Nat) (hw : workCap ≤ 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  let hSubInLt : workCap / 64 < 2 ^ bits := by
    have h64 : 64 * (workCap / 64) ≤ workCap := Nat.mul_div_le workCap 64
    omega
  #[.imm r14 (w100 h100 2),
    .storeData r14 r13,
    .imm r14 (w100 h100 11),
    .add r15 r13 r14,
    .storeData r15 r11,
    .imm r14 (w100 h100 12),
    .add r15 r13 r14,
    .storeData r15 r12,
    .imm r14 (w100 h100 16),
    .add r11 r13 r14,
    .storeData r0 r11,
    .imm r14 (w100 h100 13),
    .add r15 r13 r14,
    .storeData r15 r11,
    .imm r14 ⟨workCap / 64, hSubInLt⟩,
    .add r11 r11 r14,
    .storeData r1 r11,
    .imm r14 (w100 h100 14),
    .add r15 r13 r14,
    .storeData r15 r11,
    .mov r9 r0,
    .mov r10 r0]

def exitHdrCode (bits subLen : Nat) : Array (Instr bits 16) :=
  #[.branchLt r9 r5 (offHdr + 1) (offFinish subLen)]

/-- `13` instructions: compute `r11 = n_d = 1 + childSlice.length` and branch on `n_d < 3`. -/
def exitPrepCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.add r11 r5 r5,
    .add r12 r11 r11,
    .add r11 r11 r12,
    .add r11 r11 r5,
    .add r11 r6 r11,
    .add r11 r11 r9,
    .loadData r12 r11,
    .add r11 r11 r1,
    .loadData r13 r11,
    .sub r11 r13 r12,
    .add r11 r11 r1,
    .imm r12 (w100 h100 3),
    .branchLt r11 r12 offSmall offLargeA]

/-- `15` instructions: small branch (`n_d < 3`), write `[0, 0, 0]` to `exitPtrsBase + 3*d`, step `d`. -/
def exitSmallCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w100 h100 2),
    .loadData r11 r11,
    .imm r12 (w100 h100 11),
    .add r11 r11 r12,
    .loadData r11 r11,
    .add r12 r9 r9,
    .add r12 r12 r9,
    .add r11 r11 r12,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r9 r9 r1,
    .goto offHdr]

/-- `19` instructions: write `subIn[0] = n_d`, `subIn[1] = m_d`, save `subWork[0] = qStart`. -/
def exitLargeACode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r12 (w100 h100 2),
    .loadData r12 r12,
    .imm r13 (w100 h100 13),
    .add r13 r12 r13,
    .loadData r15 r13,
    .storeData r15 r11,
    .add r11 r2 r2,
    .add r11 r7 r11,
    .add r11 r11 r9,
    .loadData r13 r11,
    .add r11 r11 r1,
    .loadData r14 r11,
    .sub r14 r14 r13,
    .add r15 r15 r1,
    .storeData r15 r14,
    .imm r11 (w100 h100 14),
    .add r11 r12 r11,
    .loadData r11 r11,
    .storeData r11 r13]

/-- `28` instructions: compute `fpPtrBase` (`subWork[1]`), write `subIn[2] = N_d`, `subIn[3] = n`, set `r15 = subIn + 4`. -/
def exitLargeBCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r13 (w100 h100 11),
    .add r13 r12 r13,
    .loadData r13 r13,
    .add r12 r2 r2,
    .add r12 r12 r12,
    .add r14 r12 r12,
    .add r12 r12 r14,
    .add r14 r14 r14,
    .add r14 r14 r14,
    .add r14 r12 r14,
    .sub r13 r13 r14,
    .add r12 r9 r9,
    .add r14 r12 r12,
    .add r12 r12 r14,
    .add r13 r13 r12,
    .add r11 r11 r1,
    .storeData r11 r13,
    .imm r12 (w100 h100 4),
    .add r12 r13 r12,
    .loadData r14 r12,
    .add r12 r12 r1,
    .loadData r12 r12,
    .sub r14 r12 r14,
    .add r15 r15 r1,
    .storeData r15 r14,
    .add r15 r15 r1,
    .storeData r15 r2,
    .add r15 r15 r1]

/-- `19` instructions: copy slice `fp[idx]` of length `subIn[lenIdx]` to `r15`, advancing `r15`. -/
def copyFromFpBlock {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h100 : 100 ≤ 2 ^ bits) (base idx lenIdx : Nat)
    (hidx : idx < 100 := by decide) (hlen : lenIdx < 100 := by decide) :
    Array (Instr bits 16) :=
  let setup : Array (Instr bits 16) :=
    #[.loadData r11 r1,
      .add r11 r11 r1,
      .loadData r11 r11,
      .imm r12 (w100 h100 idx hidx),
      .add r11 r11 r12,
      .loadData r11 r11,
      .loadData r12 r0,
      .imm r13 (w100 h100 lenIdx hlen),
      .add r12 r12 r13,
      .loadData r13 r12,
      .add r13 r11 r13,
      .mov r12 r15]
  setup ++ copyLoopCode (hi := hi) (hw := hw) (base + 12) (base + 18) ++ #[.mov r15 r12]

/-- `21` instructions: copy arc column `col` (`0/1/2`) from `emitBase` of length `m_d` to `r15`, advancing `r15`. -/
def copyFromEmitBlock {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (base : Nat) (col : Fin 3) : Array (Instr bits 16) :=
  let colInstr : Instr bits 16 :=
    match col with
    | ⟨0, _⟩ => .add r12 r0 r0
    | ⟨1, _⟩ => .add r12 r0 r3
    | ⟨2, _⟩ => .add r12 r3 r3
  let setup : Array (Instr bits 16) :=
    #[.add r11 r2 r2,
      .add r11 r11 r2,
      .add r11 r7 r11,
      .add r11 r11 r1,
      colInstr,
      .add r11 r11 r12,
      .loadData r12 r1,
      .loadData r12 r12,
      .add r11 r11 r12,
      .loadData r12 r0,
      .add r12 r12 r1,
      .loadData r13 r12,
      .add r13 r11 r13,
      .mov r12 r15]
  setup ++ copyLoopCode (hi := hi) (hw := hw) (base + 14) (base + 20) ++ #[.mov r15 r12]

def exitSaveRegsCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w100 h100 2),
    .loadData r12 r11,
    .storeData r12 r0,
    .add r12 r12 r1,
    .storeData r12 r1,
    .add r12 r12 r1,
    .storeData r12 r2,
    .add r12 r12 r1,
    .storeData r12 r3,
    .add r12 r12 r1,
    .storeData r12 r4,
    .add r12 r12 r1,
    .storeData r12 r5,
    .add r12 r12 r1,
    .storeData r12 r6,
    .add r12 r12 r1,
    .storeData r12 r7,
    .add r12 r12 r1,
    .storeData r12 r8,
    .add r12 r12 r1,
    .storeData r12 r9,
    .add r12 r12 r1,
    .storeData r12 r10]

def liftedExitSlice {bits : Nat} (subCode : Array (Instr bits 15))
    (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  let lifted := liftCode (w100 h100 inPtrAddr) (w100 h100 dataPtrAddr) subCode
  (lifted.extract 0 (4 * subCode.size)).map (relocateInstr offSub)

def exitRestoreRegsCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w100 h100 2),
    .loadData r12 r11,
    .imm r13 (w100 h100 1),
    .loadData r0 r12,
    .add r12 r12 r13,
    .loadData r1 r12,
    .add r12 r12 r13,
    .loadData r2 r12,
    .add r12 r12 r13,
    .loadData r3 r12,
    .add r12 r12 r13,
    .loadData r4 r12,
    .add r12 r12 r13,
    .loadData r5 r12,
    .add r12 r12 r13,
    .loadData r6 r12,
    .add r12 r12 r13,
    .loadData r7 r12,
    .add r12 r12 r13,
    .loadData r8 r12,
    .add r12 r12 r13,
    .loadData r9 r12,
    .add r12 r12 r13,
    .loadData r10 r12]

/-- `43` instructions: write `ep0, ep1, ep2` into `exitPtrsBase + 3*d` and set up copy `r11..r13, r15`. -/
def exitPostSetupCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w100 h100 2),
    .loadData r14 r11,
    .imm r11 (w100 h100 11),
    .add r11 r14 r11,
    .loadData r11 r11,
    .add r13 r9 r9,
    .add r13 r13 r9,
    .add r11 r11 r13,
    .imm r12 (w100 h100 12),
    .add r12 r14 r12,
    .loadData r12 r12,
    .add r12 r12 r10,
    .loadData r13 r0,
    .imm r15 (w100 h100 2),
    .add r15 r13 r15,
    .loadData r15 r15,
    .storeData r11 r12,
    .add r11 r11 r1,
    .add r12 r12 r15,
    .storeData r11 r12,
    .add r11 r11 r1,
    .add r13 r15 r15,
    .add r14 r13 r13,
    .add r14 r14 r14,
    .add r14 r14 r14,
    .add r13 r13 r14,
    .add r12 r12 r13,
    .storeData r11 r12,
    .add r13 r13 r15,
    .loadData r14 r0,
    .loadData r14 r14,
    .add r15 r14 r14,
    .add r14 r15 r15,
    .add r14 r14 r15,
    .add r15 r13 r14,
    .imm r12 (w100 h100 2),
    .loadData r12 r12,
    .imm r13 (w100 h100 12),
    .add r12 r12 r13,
    .loadData r12 r12,
    .add r12 r12 r10,
    .loadData r11 r1,
    .add r13 r11 r15]

/-- `3` instructions: advance `exitUsed += r15`, `d += 1`, jump to `offHdr`. -/
def exitPostStepCode {bits : Nat} : Array (Instr bits 16) :=
  #[.add r10 r10 r15,
    .add r9 r9 r1,
    .goto offHdr]

/-- `17` instructions: set `r8 = exitPtrsBase`, `r7 = ownerForestPtrsBase`, `r9 = 5*n`, `.halt`. -/
def exitFinishCode {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w100 h100 2),
    .loadData r11 r11,
    .imm r12 (w100 h100 11),
    .add r11 r11 r12,
    .loadData r8 r11,
    .add r11 r2 r2,
    .add r11 r11 r11,
    .add r12 r11 r11,
    .add r11 r11 r12,
    .add r12 r12 r12,
    .add r12 r12 r12,
    .add r11 r11 r12,
    .sub r7 r8 r11,
    .add r11 r2 r2,
    .add r11 r11 r11,
    .add r9 r11 r2,
    .halt]

def sec0 {bits : Nat} (workCap subLen : Nat) (hw : workCap ≤ 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  (exitInitACode h100 ++ exitInitBCode workCap hw h100) ++
    (exitHdrCode bits subLen ++ exitPrepCode h100 ++ exitSmallCode h100)

def sec1 {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  exitLargeACode h100 ++ exitLargeBCode h100

def sec2 {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 0) 3 0 ++
    copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 1) 1 2) ++
  (copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 2) 2 2 ++
    copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 3) 4 2 ++
    copyFromFpBlock (hi := hi) (hw := hw) h100 (offFp 4) 5 2)

def sec3 {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  copyFromEmitBlock (hi := hi) (hw := hw) (offEmit 0) ⟨0, by decide⟩ ++
  copyFromEmitBlock (hi := hi) (hw := hw) (offEmit 1) ⟨1, by decide⟩ ++
  copyFromEmitBlock (hi := hi) (hw := hw) (offEmit 2) ⟨2, by decide⟩ ++
  exitSaveRegsCode h100

def exitPrefixCode {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (subLen : Nat) (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  (sec0 workCap subLen hw h100 ++ sec1 h100) ++
    (sec2 (hi := hi) (hw := hw) h100 ++ sec3 (hi := hi) (hw := hw) h100)

def exitSuffixCode {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (subLen : Nat) (h100 : 100 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  (exitRestoreRegsCode h100 ++ exitPostSetupCode h100) ++
    (copyLoopCode (hi := hi) (hw := hw) (offPostCopy subLen) (offPostStep subLen) ++
      exitPostStepCode ++ exitFinishCode h100)

def exitFamilyLoopCodeOf {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  exitPrefixCode (hi := hi) (hw := hw) subCode.size h100 ++
    liftedExitSlice subCode h100 ++
    exitSuffixCode (hi := hi) (hw := hw) subCode.size h100

def exitSubProgram {bits workCap : Nat} (hw : workCap ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    Program (RamForestProgram.layout bits (exitFamilySubInCap workCap) (exitFamilySubWorkCap workCap)
      (by unfold exitFamilySubInCap; have := Nat.div_le_self workCap 64; omega)
      (by unfold exitFamilySubWorkCap; have := Nat.div_le_self workCap 16; omega)) :=
  exitSummaryBuildProgram h100

/-- Complete 16-register fixed word-RAM program for the EX5.1 exit-summary family loop. -/
def exitFamilyLoopProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  exitFamilyLoopCodeOf (hi := hi) (hw := hw) (exitSubProgram hw h100) h100

theorem exitInitACode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitInitACode h100).size = 25 := rfl
theorem exitInitBCode_size {bits : Nat} (workCap : Nat) (hw : workCap ≤ 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : (exitInitBCode workCap hw h100).size = 22 := rfl
theorem exitHdrCode_size (bits subLen : Nat) : (exitHdrCode bits subLen).size = 1 := rfl
theorem exitPrepCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitPrepCode h100).size = 13 := rfl
theorem exitSmallCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitSmallCode h100).size = 15 := rfl
theorem exitLargeACode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitLargeACode h100).size = 19 := rfl
theorem exitLargeBCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitLargeBCode h100).size = 28 := rfl
theorem copyFromFpBlock_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h100 : 100 ≤ 2 ^ bits) (base idx lenIdx : Nat) (hidx : idx < 100) (hlen : lenIdx < 100) :
    (copyFromFpBlock (hi := hi) (hw := hw) h100 base idx lenIdx hidx hlen).size = 19 := by
  unfold copyFromFpBlock copyLoopCode
  simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
theorem copyFromEmitBlock_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (base : Nat) (col : Fin 3) :
    (copyFromEmitBlock (bits := bits) (hi := hi) (hw := hw) base col).size = 21 := by
  unfold copyFromEmitBlock copyLoopCode
  simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
theorem exitSaveRegsCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitSaveRegsCode h100).size = 23 := rfl
theorem liftedExitSlice_size {bits : Nat} (subCode : Array (Instr bits 15))
    (h100 : 100 ≤ 2 ^ bits) : (liftedExitSlice subCode h100).size = 4 * subCode.size := by
  unfold liftedExitSlice
  rw [Array.size_map, Array.size_extract, liftCode_size]
  omega
theorem exitRestoreRegsCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitRestoreRegsCode h100).size = 24 := rfl
theorem exitPostSetupCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitPostSetupCode h100).size = 43 := rfl
theorem copyLoopCode16_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (lp ex : Nat) :
    (copyLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) lp ex).size = 6 := rfl
theorem exitPostStepCode_size {bits : Nat} :
    (exitPostStepCode (bits := bits)).size = 3 := rfl
theorem exitFinishCode_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) :
    (exitFinishCode h100).size = 17 := rfl

theorem sec0_size {bits : Nat} (workCap subLen : Nat) (hw : workCap ≤ 2 ^ bits)
    (h100 : 100 ≤ 2 ^ bits) : (sec0 workCap subLen hw h100).size = 76 := by
  rw [sec0, Array.size_append, Array.size_append, Array.size_append, Array.size_append,
    exitInitACode_size, exitInitBCode_size, exitHdrCode_size, exitPrepCode_size, exitSmallCode_size]
theorem sec1_size {bits : Nat} (h100 : 100 ≤ 2 ^ bits) : (sec1 h100).size = 47 := by
  rw [sec1, Array.size_append, exitLargeACode_size, exitLargeBCode_size]
theorem sec2_size {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (h100 : 100 ≤ 2 ^ bits) :
    (sec2 (hi := hi) (hw := hw) h100).size = 95 := by
  rw [sec2, Array.size_append, Array.size_append, Array.size_append, Array.size_append,
    copyFromFpBlock_size, copyFromFpBlock_size, copyFromFpBlock_size, copyFromFpBlock_size,
    copyFromFpBlock_size]
theorem sec3_size {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (h100 : 100 ≤ 2 ^ bits) :
    (sec3 (hi := hi) (hw := hw) h100).size = 86 := by
  rw [sec3, Array.size_append, Array.size_append, Array.size_append,
    copyFromEmitBlock_size, copyFromEmitBlock_size, copyFromEmitBlock_size, exitSaveRegsCode_size]
theorem exitPrefixCode_size {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (subLen : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (exitPrefixCode (hi := hi) (hw := hw) subLen h100).size = 304 := by
  rw [exitPrefixCode, Array.size_append, Array.size_append, Array.size_append,
    sec0_size, sec1_size, sec2_size, sec3_size]
theorem exitSuffixCode_size {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits}
    {hw : workCap ≤ 2 ^ bits} (subLen : Nat) (h100 : 100 ≤ 2 ^ bits) :
    (exitSuffixCode (hi := hi) (hw := hw) subLen h100).size = 93 := by
  rw [exitSuffixCode, Array.size_append, Array.size_append, Array.size_append, Array.size_append,
    exitRestoreRegsCode_size, exitPostSetupCode_size, copyLoopCode16_size, exitPostStepCode_size,
    exitFinishCode_size]

theorem exitFamilyLoopCodeOf_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h100 : 100 ≤ 2 ^ bits) :
    (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100).size = 397 + 4 * subCode.size := by
  rw [exitFamilyLoopCodeOf, Array.size_append, Array.size_append, exitPrefixCode_size,
    liftedExitSlice_size, exitSuffixCode_size]
  omega

theorem exitFamilyLoopProgram_pos {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    0 < (exitFamilyLoopProgram hi hw h100).size := by
  rw [exitFamilyLoopProgram, exitFamilyLoopCodeOf_size]
  omega

theorem exitFamilyLoopProgram_last_lt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    (exitFamilyLoopProgram hi hw h100).size - 1 < (exitFamilyLoopProgram hi hw h100).size :=
  Nat.sub_lt (exitFamilyLoopProgram_pos hi hw h100) (by decide)

theorem exitFamilyLoopProgram_last_halt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    (exitFamilyLoopProgram hi hw h100)[(exitFamilyLoopProgram hi hw h100).size - 1]? = some .halt := by
  let sub := exitSubProgram hw h100
  change (exitPrefixCode (hi := hi) (hw := hw) sub.size h100 ++ liftedExitSlice sub h100 ++
      exitSuffixCode (hi := hi) (hw := hw) sub.size h100)[
      (exitFamilyLoopCodeOf (hi := hi) (hw := hw) sub h100).size - 1]? = some .halt
  rw [exitFamilyLoopCodeOf_size,
    Array.getElem?_append_right (by rw [Array.size_append, exitPrefixCode_size, liftedExitSlice_size]; omega),
    Array.size_append, exitPrefixCode_size, liftedExitSlice_size,
    show 397 + 4 * sub.size - 1 - (304 + 4 * sub.size) = 92 by omega]
  unfold exitSuffixCode
  rw [Array.getElem?_append_right (by rw [Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size]; omega),
    Array.size_append, exitRestoreRegsCode_size, exitPostSetupCode_size,
    Array.getElem?_append_right (by rw [Array.size_append, copyLoopCode16_size, exitPostStepCode_size]; omega),
    Array.size_append, copyLoopCode16_size, exitPostStepCode_size]
  rfl

/-! #### Fast Slice-Fetch & `BodyRelocated` Lemmas -/

def SlicePlaced {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code sub : Array (Instr bits 16)) (base : Nat) : Prop :=
  ∀ (k : Nat) (hk : k < sub.size), code[base + k]? = some (sub[k]'hk)

private theorem SlicePlaced.getElem? {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code sub : Array (Instr bits 16)} {base pc : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code sub base)
    (hLo : base ≤ pc) (hHi : pc < base + sub.size) :
    code[pc]? = some (sub[pc - base]'(by omega)) := by
  have h := hPl (pc - base) (by omega)
  rwa [Nat.add_sub_of_le hLo] at h

theorem SlicePlaced.at {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code sub : Array (Instr bits 16)} {base : Nat}
    (hPl : SlicePlaced (hi := hi) (hw := hw) code sub base) (k : Nat) (hk : k < sub.size)
    {pc : Nat} (hpc : pc = base + k) :
    code[pc]? = some (sub[k]'hk) :=
  hpc ▸ hPl k hk

end ProgramCode

end PaperB.RamExitFamilyLoop
