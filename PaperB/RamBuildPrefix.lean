module

public import PaperB.RamDagReachKahn
public import PaperB.RamDomAndStaticTree
public import PaperB.RamDataSliceAdapter
public import PaperB.RamForestPhaseLink

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.1 Unified Prefix ROM (`buildPrefixProgram`, `run_build_prefix`):

Single fixed 16-register Word-RAM program (`buildPrefixProgram hi hw hTen`),
depending ONLY on `(bits, inputCap, workCap)`, that executes in ONE machine run:
1. Phase 1 (`dagReachKahnPhase`): Kahn topological sort + reachability compaction +
   dense incoming-CSR construction on `[0 .. rawDagWorkCap n m)`.
2. Phase 2 (`copyDenseInPhase`): Copies `[Q, mReach, inStart[0..Q], inSrc[0..mReach-1]]`
   to `denseInBase := 3 * (workCap / 4)`, sets pointer slots `data[0] := denseInBase`
   and `data[1] := treeBase` (`treeBase := workCap / 4`), while preserving
   `[3 * n .. 5 * n)` (`origToDensePlusOne`, `denseToOrig`).
3. Phase 3 (`liftCode` of `domAndStaticTreeProgram` on fixed slice layout
   `(subInCap := workCap / 4, subWorkCap := 2 * (workCap / 4))`) + 8-instruction epilogue:
   runs `domAndStaticTreeProgram` inside `[treeBase .. treeBase + 2 * (workCap / 4))`
   reading from `[denseInBase .. denseInBase + workCap / 4)`, and loads
   `r5 = Q`, `r6 = treeBase`, `r8 = mReach` before halting.

Linear workspace requirement: `64 * (n + m + 1) ≤ workCap` (note `prefixWorkCap n m :=
25 * n + 2 * m + 16 ≤ 64 * (n + m + 1)`), total steps `≤ 4326 * (n + m + 1) * (L n)^2`,
peak live words `inputCap + workCap + 16`.
-/

namespace PaperB.RamBuildPrefix

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph
open PaperB.RamDagReach

section FixedPrefixProgram

/-- Linear tight workspace watermark for the EX5.1 prefix phases (`25*n + 2*m + 16 ≤ 64*(n+m+1)`). -/
def prefixWorkCap (n m : Nat) : Nat := 25 * n + 2 * m + 16

theorem prefixWorkCap_le (n m : Nat) : prefixWorkCap n m ≤ 64 * (n + m + 1) := by
  unfold prefixWorkCap
  omega

/-- Quarter of `workCap`, fixing the disjoint prefix slices purely from `(bits, inputCap, workCap)`. -/
def prefixQuarter (workCap : Nat) : Nat := workCap / 4
def prefixTreeBase (workCap : Nat) : Nat := prefixQuarter workCap
def prefixSubWorkCap (workCap : Nat) : Nat := 2 * prefixQuarter workCap
def prefixDenseInBase (workCap : Nat) : Nat := 3 * prefixQuarter workCap
def prefixSubInCap (workCap : Nat) : Nat := prefixQuarter workCap

theorem quarter_lt_pow2 {bits workCap : Nat} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    prefixQuarter workCap < 2 ^ bits := by
  unfold prefixQuarter
  omega

theorem three_quarter_lt_pow2 {bits workCap : Nat} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    prefixDenseInBase workCap < 2 ^ bits := by
  unfold prefixDenseInBase prefixQuarter
  omega

theorem prefixSubInCap_le {bits workCap : Nat} (hw : workCap ≤ 2 ^ bits) :
    prefixSubInCap workCap ≤ 2 ^ bits := by
  unfold prefixSubInCap prefixQuarter
  omega

theorem prefixSubWorkCap_le {bits workCap : Nat} (hw : workCap ≤ 2 ^ bits) :
    prefixSubWorkCap workCap ≤ 2 ^ bits := by
  unfold prefixSubWorkCap prefixQuarter
  omega

/-- Phase 2 (`size = 33`): writes `data[0] := 3 * quarter`, `data[1] := quarter`,
copies `[Q, mReach, inStart[0..Q], inSrc[0..mReach-1]]` to `[3 * quarter .. )`. -/
def copyDenseInCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[-- 0..3: set pointer slots `data[0] := denseInBase`, `data[1] := treeBase`
    .imm r7 ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩,
    .storeData rZero r7,
    .imm r8 ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩,
    .storeData rOne r8,
    -- 4..6: store `Q` (`r5`) at `denseInBase + 0`, `mReach` (`r6`) at `denseInBase + 1`
    .storeData r7 r5,
    .add r7 r7 rOne,
    .storeData r7 r6,
    -- 7..13: `r9 := 6 * n`, `r10 := Q + 1`, `r7 := denseInBase + 2`, `r11 := 0`
    .add r9 rN rN,
    .add r9 r9 r9,
    .add r9 r9 rN,
    .add r9 r9 rN,
    .add r10 r5 rOne,
    .add r7 r7 rOne,
    .mov r11 rZero,
    -- 14..20: copy `inStart[0..Q]` from `data[6 * n + i]` to `data[denseInBase + 2 + i]`
    .branchLt r11 r10 15 21,
    .add r12 r9 r11,
    .loadData r13 r12,
    .add r12 r7 r11,
    .storeData r12 r13,
    .add r11 r11 rOne,
    .goto 14,
    -- 21..24: `r9 := 7 * n + 1`, `r7 := denseInBase + 3 + Q`, `r11 := 0`
    .add r9 r9 rN,
    .add r9 r9 rOne,
    .add r7 r7 r10,
    .mov r11 rZero,
    -- 25..31: copy `inSrc[0..mReach-1]` from `data[7*n+1+i]` to `data[denseInBase+3+Q+i]`
    .branchLt r11 r6 26 32,
    .add r12 r9 r11,
    .loadData r13 r12,
    .add r12 r7 r11,
    .storeData r12 r13,
    .add r11 r11 rOne,
    .goto 25,
    -- 32: halt
    .halt]

def copyDenseInPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast (copyDenseInCode hw hTen) 32 rfl rfl rfl

theorem copyDenseInPhase_code {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (copyDenseInPhase (hi := hi) hw hTen).code = copyDenseInCode hw hTen :=
  rfl

/-- Epilogue (`size = 8`): recovers `r5 = Q`, `r6 = treeBase`, `r8 = mReach` from
`data[0]`, `data[1]`, and `data[denseInBase + 0..1]` after `domAndStaticTreeProgram` finishes. -/
def epilogueCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (hTen : 10 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[.imm r15 ⟨0, by omega⟩,
    .loadData r15 r15,
    .loadData r5 r15,
    .imm r7 ⟨1, by omega⟩,
    .add r15 r15 r7,
    .loadData r8 r15,
    .loadData r6 r7,
    .halt]

/-- Fixed 15-register sublayout `(workCap / 4, 2 * (workCap / 4))` for Phase 3. -/
abbrev prefixSubLayout (bits workCap : Nat) (hw : workCap ≤ 2 ^ bits) : Layout bits :=
  RamForestProgram.layout bits (prefixSubInCap workCap) (prefixSubWorkCap workCap)
    (prefixSubInCap_le hw) (prefixSubWorkCap_le hw)

/-- Fixed Phase 1 + Phase 2 composite `Phase L16`. -/
def buildPrefixPhase12 {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Phase (layout16 bits inputCap workCap hi hw) :=
  (dagReachKahnPhase (by omega)).link (copyDenseInPhase hw hTen)

/-- Fixed Phase 3 (`liftCode` body of `domAndStaticTreeProgram` without trailing `.halt`)
followed immediately by `epilogueCode`. -/
def prefixRightCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
    (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
  let lifted := RamDataSliceAdapter.liftCode
    ⟨0, by omega⟩ ⟨1, by omega⟩ subCode
  lifted.extract 0 (4 * subCode.size) ++
    epilogueCode (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw) hTen

theorem prefixRightCode_pos {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    0 < (prefixRightCode (hi := hi) hw hTen).size := by
  unfold prefixRightCode
  rw [Array.size_append]
  have hEp : (epilogueCode (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) hTen).size = 8 := rfl
  omega

/-- **EX5.1 Unified Prefix ROM**: single fixed 16-register RAM program depending ONLY on
`(bits, inputCap, workCap)`, executing Kahn DAG reachability + dense incoming CSR copy +
dominator/static tree construction + register epilogue in one contiguous trace. -/
def buildPrefixProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  let p12 := buildPrefixPhase12 hi hw hTen
  join p12.code (prefixRightCode hw hTen) p12.haltPC p12.haltFits

end FixedPrefixProgram

section Helpers

private theorem nat_log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  by_cases hb0 : b = 0
  · have ha0 : a = 0 := by omega
    subst ha0; subst hb0; exact Nat.le_refl 0
  · by_cases ha0 : a = 0
    · subst ha0
      have h0 : Nat.log2 0 = 0 := by decide
      rw [h0]; exact Nat.zero_le _
    · rw [Nat.le_log2 hb0]
      exact Nat.le_trans ((Nat.le_log2 ha0).mp (Nat.le_refl _)) h

private theorem L_mono {a b : Nat} (h : a ≤ b) : OracleContract.L a ≤ OracleContract.L b := by
  change Nat.log2 (a + 1) + 1 ≤ Nat.log2 (b + 1) + 1
  exact Nat.succ_le_succ (nat_log2_mono (Nat.succ_le_succ h))

private theorem reg_set_ne_array {bits : Nat} {L : Layout bits}
    (s : State L) (addr : Nat) (w : Word bits) (h : addr < s.data.size) :
    { s with data := s.data.set addr w h, data_size := by simp [s.data_size], pc := s.pc + 1 }.regs =
      s.regs :=
  rfl

private theorem placed_extract_left {bits k : Nat}
    (xs : Array (Instr bits k)) (n : Nat) (hn : n ≤ xs.size) (i : Nat) (hi : i < n) :
    (xs.extract 0 n)[i]? = xs[i]? := by
  have hsz : (xs.extract 0 n).size = n := by rw [Array.size_extract]; omega
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega), Array.getElem_extract]
  simp only [Nat.zero_add]

private theorem prefixRightCode_bodyRelocated {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
    RamDataSliceAdapter.BodyRelocated (bigL := layout16 bits inputCap workCap hi hw) rfl
      ⟨0, by omega⟩ ⟨1, by omega⟩ subCode (prefixRightCode hw hTen) 0 := by
  intro subCode i hiLt op hop
  have hrel : relocateInstr 0 op = op := by cases op <;> simp [relocateInstr]
  have hExt : ((RamDataSliceAdapter.liftCode ⟨0, by omega⟩ ⟨1, by omega⟩ subCode).extract 0
      (4 * subCode.size)).size = 4 * subCode.size := by
    rw [Array.size_extract, RamDataSliceAdapter.liftCode_size]; omega
  rw [prefixRightCode, Nat.zero_add, cast_eq, hrel]
  rw [Array.getElem?_append_left (by rw [hExt]; exact hiLt)]
  change ((RamDataSliceAdapter.liftCode ⟨0, by omega⟩ ⟨1, by omega⟩ subCode).extract 0
      (4 * subCode.size))[i]? = some op
  rw [placed_extract_left _ _ (by rw [RamDataSliceAdapter.liftCode_size]; omega) i hiLt]
  exact hop

private theorem prefixRightCode_epilogue_placed {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
    Placed (prefixRightCode (hi := hi) hw hTen) (4 * subCode.size)
      (epilogueCode (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw) hTen).toList := by
  intro subCode i op hop
  have hExt : ((RamDataSliceAdapter.liftCode ⟨0, by omega⟩ ⟨1, by omega⟩ subCode).extract 0
      (4 * subCode.size)).size = 4 * subCode.size := by
    rw [Array.size_extract, RamDataSliceAdapter.liftCode_size]; omega
  unfold prefixRightCode
  rw [Array.getElem?_append_right (by rw [hExt]; omega), hExt, Nat.add_sub_cancel_left]
  rw [← Array.getElem?_toList]
  exact hop

private theorem prefixRightCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
    (prefixRightCode (hi := hi) hw hTen).size = 4 * subCode.size + 8 := by
  intro subCode
  unfold prefixRightCode
  rw [Array.size_append, Array.size_extract, RamDataSliceAdapter.liftCode_size]
  have hEp : (epilogueCode (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) hTen).size = 8 := rfl
  have hMin : min (4 * subCode.size) (4 * subCode.size + 1) = 4 * subCode.size :=
    Nat.min_eq_left (Nat.le_succ _)
  rw [Nat.sub_zero, hMin, hEp]

end Helpers

section CopyDenseInProof

private theorem copyBankLoop_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    (loopPC exitPC : Nat) (limitReg srcBaseReg dstBaseReg : Fin 16)
    (srcBase dstBase limit : Nat)
    (hlFit : limit < 2 ^ bits)
    (hDiff1 : r11 ≠ r12) (hDiff2 : r11 ≠ r13) (hDiff3 : r12 ≠ r13)
    (hKeepLimit : limitReg ≠ r11 ∧ limitReg ≠ r12 ∧ limitReg ≠ r13)
    (hKeepOne : rOne ≠ r11 ∧ rOne ≠ r12 ∧ rOne ≠ r13)
    (hKeepSrc : srcBaseReg ≠ r11 ∧ srcBaseReg ≠ r12 ∧ srcBaseReg ≠ r13)
    (hKeepDst : dstBaseReg ≠ r11 ∧ dstBaseReg ≠ r12 ∧ dstBaseReg ≠ r13)
    (hSz : loopPC + 7 ≤ code.size) (hExitSz : exitPC < code.size)
    (hPl : Placed code loopPC
      [ .branchLt r11 limitReg (loopPC + 1) exitPC,
        .add r12 srcBaseReg r11,
        .loadData r13 r12,
        .add r12 dstBaseReg r11,
        .storeData r12 r13,
        .add r11 r11 rOne,
        .goto loopPC ])
    (hSrcBound : srcBase + limit ≤ workCap)
    (hDstBound : dstBase + limit ≤ workCap)
    (hDisj : srcBase + limit ≤ dstBase ∨ dstBase + limit ≤ srcBase)
    (srcFn : Nat → Nat) :
    ∀ (rem i : Nat) (s : State (layout16 bits inputCap workCap hi hw)),
      i + rem = limit →
      s.pc = loopPC →
      s.data.size = workCap →
      (reg s rOne).val = 1 →
      (reg s limitReg).val = limit →
      (reg s srcBaseReg).val = srcBase →
      (reg s dstBaseReg).val = dstBase →
      (reg s r11).val = i →
      (∀ k, k < limit → (s.data[srcBase + k]?).map Fin.val = some (srcFn k)) →
      (∀ k, k < i → (s.data[dstBase + k]?).map Fin.val = some (srcFn k)) →
      ∃ t : State (layout16 bits inputCap workCap hi hw),
        Steps code input (7 * rem + 1) s t ∧
        t.pc = exitPC ∧
        t.data.size = workCap ∧
        reg t rZero = reg s rZero ∧
        reg t rOne = reg s rOne ∧
        reg t rN = reg s rN ∧
        reg t rM = reg s rM ∧
        reg t r5 = reg s r5 ∧
        reg t r6 = reg s r6 ∧
        reg t r7 = reg s r7 ∧
        reg t r9 = reg s r9 ∧
        reg t r10 = reg s r10 ∧
        (∀ k, k < limit → (t.data[dstBase + k]?).map Fin.val = some (srcFn k)) ∧
        (∀ w : Nat, (w < dstBase ∨ dstBase + limit ≤ w) → t.data[w]? = s.data[w]?) := by
  intro rem
  induction rem with
  | zero =>
    intro i s hiEq hpc hDsz h1 hLim hSrc hDst hI hSrcData hDstData
    have hiLim : i = limit := by omega
    subst hiLim
    have hf0 : code[s.pc]? = some (.branchLt r11 limitReg (loopPC + 1) exitPC) := by
      rw [hpc]; exact hPl 0 _ rfl
    have hCmp : WordOps.ltb (reg s r11) (reg s limitReg) = false :=
      branchLt_false (by rw [hI, hLim]; exact Nat.le_refl _)
    have ht0 : (if WordOps.ltb (reg s r11) (reg s limitReg) then loopPC + 1 else exitPC) < code.size := by
      rw [hCmp]; exact hExitSz
    have hs1 := step_branchLt_at (input := input) hf0 ht0
    rw [hCmp] at hs1
    refine ⟨{ s with pc := exitPC }, Steps.cons hs1 (Steps.zero _), rfl, hDsz,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hDstData, fun _ _ => rfl⟩
  | succ rem ih =>
    intro i s hiEq hpc hDsz h1 hLim hSrc hDst hI hSrcData hDstData
    have hiLt : i < limit := by omega
    -- step 0: branchLt taken
    have hf0 : code[s.pc]? = some (.branchLt r11 limitReg (loopPC + 1) exitPC) := by
      rw [hpc]; exact hPl 0 _ rfl
    have hCmp : WordOps.ltb (reg s r11) (reg s limitReg) = true :=
      branchLt_true (by rw [hI, hLim]; exact hiLt)
    have hs1 := step_branchLt_at (input := input) hf0 (by rw [hCmp]; simp only [↓reduceIte]; omega)
    rw [hCmp] at hs1
    let s1 : State (layout16 bits inputCap workCap hi hw) := { s with pc := loopPC + 1 }
    have h1pc : s1.pc = loopPC + 1 := rfl
    -- step 1: add r12 srcBaseReg r11
    have hf1 : code[s1.pc]? = some (.add r12 srcBaseReg r11) := hPl 1 _ rfl
    obtain ⟨s2, hs2, h2pc, h2r12, h2keep, h2data⟩ := step_add16 (input := input) hf1 (by rw [h1pc]; omega)
    have h2srcAddr : (reg s2 r12).val = srcBase + i := by
      have hFit : srcBase + i < 2 ^ bits := by
        have := hw; omega
      rw [h2r12, WordOps.add_no_wrap _ _ (by change (reg s srcBaseReg).val + (reg s r11).val < 2 ^ bits; rw [hSrc, hI]; exact hFit)]
      change (reg s srcBaseReg).val + (reg s r11).val = srcBase + i
      rw [hSrc, hI]
    -- step 2: loadData r13 r12
    obtain ⟨wVal, hwVal, hwValEq⟩ : ∃ w, s2.data[(reg s2 r12).val]? = some w ∧ w.val = srcFn i := by
      rw [h2srcAddr, h2data]
      have hGet := hSrcData i hiLt
      cases hq : s.data[srcBase + i]? with
      | none => simp [hq] at hGet
      | some w => exact ⟨w, rfl, by simpa [hq] using hGet⟩
    have hf2 : code[s2.pc]? = some (.loadData r13 r12) := by
      rw [h2pc]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, h3pc, h3r13, h3keep, h3data⟩ :=
      step_loadData16 (input := input) hf2 hwVal (by rw [h2pc, h1pc]; omega)
    -- step 3: add r12 dstBaseReg r11
    have hf3 : code[s3.pc]? = some (.add r12 dstBaseReg r11) := by
      rw [h3pc, h2pc]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, h4pc, h4r12, h4keep, h4data⟩ :=
      step_add16 (input := input) hf3 (by rw [h3pc, h2pc, h1pc]; omega)
    have h3dstBase : (reg s3 dstBaseReg).val = dstBase := by
      rw [h3keep dstBaseReg hKeepDst.2.2, h2keep dstBaseReg hKeepDst.2.1]; exact hDst
    have h3i : (reg s3 r11).val = i := by
      rw [h3keep r11 hDiff2, h2keep r11 hDiff1]; exact hI
    have h4dstAddr : (reg s4 r12).val = dstBase + i := by
      have hFit : dstBase + i < 2 ^ bits := by
        have := hw; omega
      rw [h4r12, WordOps.add_no_wrap _ _ (by rw [h3dstBase, h3i]; exact hFit), h3dstBase, h3i]
    have h4r13 : (reg s4 r13).val = srcFn i := by
      rw [h4keep r13 hDiff3.symm, h3r13]; exact hwValEq
    -- step 4: storeData r12 r13
    have h4bound : (reg s4 r12).val < s4.data.size := by
      rw [h4dstAddr, h4data, h3data, h2data, hDsz]; omega
    have hf4 : code[s4.pc]? = some (.storeData r12 r13) := by
      rw [h4pc, h3pc, h2pc]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, h5pc, h5regs, h5data⟩ :=
      step_storeData16 (input := input) hf4 (by rw [h4pc, h3pc, h2pc, h1pc]; omega) h4bound
    -- step 5: add r11 r11 rOne
    have hf5 : code[s5.pc]? = some (.add r11 r11 rOne) := by
      rw [h5pc, h4pc, h3pc, h2pc]; exact hPl 5 _ rfl
    obtain ⟨s6, hs6, h6pc, h6r11, h6keep, h6data⟩ :=
      step_add16 (input := input) hf5 (by rw [h5pc, h4pc, h3pc, h2pc, h1pc]; omega)
    have h5r11 : (reg s5 r11).val = i := by
      rw [reg_eq_of_regs_eq h5regs, h4keep r11 hDiff1]; exact h3i
    have h5one : (reg s5 rOne).val = 1 := by
      rw [reg_eq_of_regs_eq h5regs, h4keep rOne hKeepOne.2.1, h3keep rOne hKeepOne.2.2,
          h2keep rOne hKeepOne.2.1]; exact h1
    have h6i : (reg s6 r11).val = i + 1 := by
      have hFit : i + 1 < 2 ^ bits := by omega
      rw [h6r11, WordOps.add_no_wrap _ _ (by rw [h5r11, h5one]; exact hFit), h5r11, h5one]
    -- step 6: goto loopPC
    have hf6 : code[s6.pc]? = some (.goto loopPC) := by
      rw [h6pc, h5pc, h4pc, h3pc, h2pc]; exact hPl 6 _ rfl
    have hs7 := step_goto_at (input := input) hf6 (by omega)
    let s7 : State (layout16 bits inputCap workCap hi hw) := { s6 with pc := loopPC }
    have h7data : s7.data = s.data.set (dstBase + i) (reg s4 r13) (by rw [hDsz]; omega) := by
      change s6.data = _
      have h4d : s4.data = s.data := by rw [h4data, h3data, h2data]
      simp only [h6data, h5data, h4d, h4dstAddr]
    have hKeepReg : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → reg s7 r = reg s r := by
      intro r hr11 hr12 hr13
      change reg s6 r = reg s r
      rw [h6keep r hr11, reg_eq_of_regs_eq h5regs, h4keep r hr12, h3keep r hr13, h2keep r hr12]
      rfl
    have h7Dsz : s7.data.size = workCap := by rw [h7data, Array.size_set, hDsz]
    have h7srcData : ∀ k, k < limit → (s7.data[srcBase + k]?).map Fin.val = some (srcFn k) := by
      intro k hk
      have hNe : dstBase + i ≠ srcBase + k := by
        rcases hDisj with hL | hR <;> omega
      rw [h7data, Array.getElem?_set_ne _ hNe]
      exact hSrcData k hk
    have h7dstData : ∀ k, k < i + 1 → (s7.data[dstBase + k]?).map Fin.val = some (srcFn k) := by
      intro k hk
      by_cases hEq : k = i
      · subst hEq
        rw [h7data, getElem?_pos _ _ (by rw [Array.size_set, hDsz]; omega)]
        simp only [Array.getElem_set_self, Option.map_some]
        exact congrArg some h4r13
      · have hk' : k < i := by omega
        rw [h7data, Array.getElem?_set_ne _ (by omega)]
        exact hDstData k hk'
    have hLoop7 : Steps code input 7 s s7 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
        (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero _)))))))
    obtain ⟨t, hRest, htpc, htDsz, ht0, ht1, htN, htM, ht5, ht6, ht7, ht9, ht10, htDst, htFrame⟩ :=
      ih (i + 1) s7 (by omega) rfl h7Dsz
        (by rw [hKeepReg rOne hKeepOne.1 hKeepOne.2.1 hKeepOne.2.2]; exact h1)
        (by rw [hKeepReg limitReg hKeepLimit.1 hKeepLimit.2.1 hKeepLimit.2.2]; exact hLim)
        (by rw [hKeepReg srcBaseReg hKeepSrc.1 hKeepSrc.2.1 hKeepSrc.2.2]; exact hSrc)
        (by rw [hKeepReg dstBaseReg hKeepDst.1 hKeepDst.2.1 hKeepDst.2.2]; exact hDst)
        h6i h7srcData h7dstData
    have hStepsEq : 7 * (rem + 1) + 1 = 7 + (7 * rem + 1) := by omega
    rw [hStepsEq]
    refine ⟨t, hLoop7.append hRest, htpc, htDsz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htDst, ?_⟩
    · exact ht0.trans (hKeepReg rZero (by decide) (by decide) (by decide))
    · exact ht1.trans (hKeepReg rOne (by decide) (by decide) (by decide))
    · exact htN.trans (hKeepReg rN (by decide) (by decide) (by decide))
    · exact htM.trans (hKeepReg rM (by decide) (by decide) (by decide))
    · exact ht5.trans (hKeepReg r5 (by decide) (by decide) (by decide))
    · exact ht6.trans (hKeepReg r6 (by decide) (by decide) (by decide))
    · exact ht7.trans (hKeepReg r7 (by decide) (by decide) (by decide))
    · exact ht9.trans (hKeepReg r9 (by decide) (by decide) (by decide))
    · exact ht10.trans (hKeepReg r10 (by decide) (by decide) (by decide))
    · intro w hw
      rw [htFrame w hw, h7data, Array.getElem?_set_ne _ (by omega)]

private theorem run_copyDenseIn_pre14 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q mReach : Nat}
    (hnPos : 1 ≤ n) (hQPos : 1 ≤ Q) (hQLe : Q ≤ n) (hmLe : mReach ≤ m)
    (hCap : 64 * (n + m + 1) ≤ workCap)
    (s1 : State (layout16 bits inputCap workCap hi hw))
    (hConst : ConstRegs n m root s1)
    (hr5 : (reg s1 r5).val = Q)
    (hr6 : (reg s1 r6).val = mReach) :
    let quarter := prefixQuarter workCap
    let denseInBase := prefixDenseInBase workCap
    let code := (copyDenseInPhase (hi := hi) hw hTen).code
    ∃ st14 : State (layout16 bits inputCap workCap hi hw),
      Steps code input 14 (Phase.initial s1) st14 ∧
      st14.pc = 14 ∧
      st14.data.size = workCap ∧
      (∀ idx, 2 ≤ idx → idx < denseInBase → st14.data[idx]? = s1.data[idx]?) ∧
      (reg st14 rZero).val = 0 ∧
      (reg st14 rOne).val = 1 ∧
      (reg st14 rN).val = n ∧
      (reg st14 r5).val = Q ∧
      (reg st14 r6).val = mReach ∧
      (reg st14 r7).val = denseInBase + 2 ∧
      (reg st14 r9).val = 6 * n ∧
      (reg st14 r10).val = Q + 1 ∧
      (reg st14 r11).val = 0 ∧
      st14.data[0]? = some ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩ ∧
      st14.data[1]? = some ⟨quarter, quarter_lt_pow2 hw hTen⟩ ∧
      (st14.data[denseInBase]?).map Fin.val = some Q ∧
      (st14.data[denseInBase + 1]?).map Fin.val = some mReach := by
  intro quarter denseInBase code
  have hQuarterGe : 16 * (n + m + 1) ≤ quarter := by
    unfold quarter prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hInBaseGe : 48 * (n + m + 1) ≤ denseInBase := by
    unfold denseInBase prefixDenseInBase
    omega
  have hDenseInEnd : denseInBase + 3 + Q + mReach ≤ workCap := by
    unfold denseInBase prefixDenseInBase prefixQuarter
    omega
  have hLtPow : workCap ≤ 2 ^ bits := hw
  have hFit7n1 : 7 * n + 1 + mReach ≤ workCap := by omega
  let st0 := Phase.initial s1
  have hst0pc : st0.pc = 0 := rfl
  have hDsz0 : st0.data.size = workCap := s1.data_size
  have hCodeSz : code.size = 33 := rfl
  -- Step 0..3: set data[0] := denseInBase, data[1] := treeBase
  have hf0 : code[st0.pc]? = some (.imm r7 ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩) := by
    rw [hst0pc]; rfl
  obtain ⟨st1, hs1, hpc1, h1r7, h1keep, h1data⟩ :=
    step_imm16 (input := input) hf0 (by rw [hst0pc, hCodeSz]; omega)
  have h1r0 : (reg st1 rZero).val = 0 := by
    rw [h1keep rZero (by decide)]; exact hConst.zero
  have hf1 : code[st1.pc]? = some (.storeData rZero r7) := by rw [hpc1, hst0pc]; rfl
  obtain ⟨st2, hs2, hpc2, h2regs, h2data⟩ :=
    step_storeData16 (input := input) hf1 (by rw [hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h1r0, h1data, hDsz0]; omega)
  have h2r7 : (reg st2 r7).val = denseInBase := by
    rw [reg_eq_of_regs_eq h2regs, h1r7]
  have hf2 : code[st2.pc]? = some (.imm r8 ⟨quarter, quarter_lt_pow2 hw hTen⟩) := by
    rw [hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st3, hs3, hpc3, h3r8, h3keep, h3data⟩ :=
    step_imm16 (input := input) (s := st2) (d := r8)
      (w := ⟨quarter, quarter_lt_pow2 hw hTen⟩) hf2 (by rw [hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h3r1 : (reg st3 rOne).val = 1 := by
    rw [h3keep rOne (by decide), reg_eq_of_regs_eq h2regs, h1keep rOne (by decide)]; exact hConst.one
  have hf3 : code[st3.pc]? = some (.storeData rOne r8) := by rw [hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st4, hs4, hpc4, h4regs, h4data⟩ :=
    step_storeData16 (input := input) hf3 (by rw [hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h3r1, h3data, h2data, Array.size_set, h1data, hDsz0]; omega)
  -- Step 4..6: store Q at denseInBase + 0, mReach at denseInBase + 1
  have h4r7 : (reg st4 r7).val = denseInBase := by
    rw [reg_eq_of_regs_eq h4regs, h3keep r7 (by decide)]; exact h2r7
  have h4r1 : (reg st4 rOne).val = 1 := by rw [reg_eq_of_regs_eq h4regs]; exact h3r1
  have h4Dsz : st4.data.size = workCap := by
    rw [h4data, Array.size_set, h3data, h2data, Array.size_set, h1data, hDsz0]
  have hf4 : code[st4.pc]? = some (.storeData r7 r5) := by rw [hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st5, hs5, hpc5, h5regs, h5data⟩ :=
    step_storeData16 (input := input) hf4 (by rw [hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h4r7, h4Dsz]; omega)
  have h5r7 : (reg st5 r7).val = denseInBase := by rw [reg_eq_of_regs_eq h5regs]; exact h4r7
  have h5r1 : (reg st5 rOne).val = 1 := by rw [reg_eq_of_regs_eq h5regs]; exact h4r1
  have hf5 : code[st5.pc]? = some (.add r7 r7 rOne) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st6, hs6, hpc6, h6r7, h6keep, h6data⟩ :=
    step_add16 (input := input) hf5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h6r7v : (reg st6 r7).val = denseInBase + 1 := by
    rw [h6r7, WordOps.add_no_wrap _ _ (by rw [h5r7, h5r1]; omega), h5r7, h5r1]
  have h6Dsz : st6.data.size = workCap := by
    rw [h6data, h5data, Array.size_set, h4Dsz]
  have hf6 : code[st6.pc]? = some (.storeData r7 r6) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st7, hs7, hpc7, h7regs, h7data⟩ :=
    step_storeData16 (input := input) hf6
      (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h6r7v, h6Dsz]; omega)
  -- Helper tracking constants up to st7
  have h7const : ∀ r : Fin 16, r = rZero ∨ r = rOne ∨ r = rN ∨ r = rM ∨ r = r5 ∨ r = r6 →
      reg st7 r = reg s1 r := by
    intro r hr
    have hNe7 : r ≠ r7 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe8 : r ≠ r8 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [reg_eq_of_regs_eq h7regs, h6keep r hNe7, reg_eq_of_regs_eq h5regs, reg_eq_of_regs_eq h4regs,
        h3keep r hNe8, reg_eq_of_regs_eq h2regs, h1keep r hNe7]
    rfl
  -- Step 7..13: r9 := 6*n, r10 := Q+1, r7 := denseInBase+2, r11 := 0
  have h7rN : (reg st7 rN).val = n := by rw [h7const rN (Or.inr (Or.inr (Or.inl rfl)))]; exact hConst.nVal
  have h7r5 : (reg st7 r5).val = Q := by rw [h7const r5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hr5
  have h7r1 : (reg st7 rOne).val = 1 := by rw [h7const rOne (Or.inr (Or.inl rfl))]; exact hConst.one
  have h7r0 : (reg st7 rZero).val = 0 := by rw [h7const rZero (Or.inl rfl)]; exact hConst.zero
  have h7r7 : (reg st7 r7).val = denseInBase + 1 := by rw [reg_eq_of_regs_eq h7regs]; exact h6r7v
  have hf7 : code[st7.pc]? = some (.add r9 rN rN) := by
    rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st8, hs8, hpc8, h8r9, h8keep, h8data⟩ :=
    step_add16 (input := input) hf7
      (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h8r9v : (reg st8 r9).val = 2 * n := by
    rw [h8r9, WordOps.add_no_wrap _ _ (by rw [h7rN]; omega), h7rN]; omega
  have hf8 : code[st8.pc]? = some (.add r9 r9 r9) := by
    rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st9, hs9, hpc9, h9r9, h9keep, h9data⟩ :=
    step_add16 (input := input) hf8
      (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h9r9v : (reg st9 r9).val = 4 * n := by
    rw [h9r9, WordOps.add_no_wrap _ _ (by rw [h8r9v]; omega), h8r9v]; omega
  have h9rN : (reg st9 rN).val = n := by rw [h9keep rN (by decide), h8keep rN (by decide)]; exact h7rN
  have hf9 : code[st9.pc]? = some (.add r9 r9 rN) := by
    rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st10, hs10, hpc10, h10r9, h10keep, h10data⟩ :=
    step_add16 (input := input) hf9
      (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h10r9v : (reg st10 r9).val = 5 * n := by
    rw [h10r9, WordOps.add_no_wrap _ _ (by rw [h9r9v, h9rN]; omega), h9r9v, h9rN]; omega
  have h10rN : (reg st10 rN).val = n := by rw [h10keep rN (by decide)]; exact h9rN
  have hf10 : code[st10.pc]? = some (.add r9 r9 rN) := by
    rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st11, hs11, hpc11, h11r9, h11keep, h11data⟩ :=
    step_add16 (input := input) hf10
      (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h11r9v : (reg st11 r9).val = 6 * n := by
    rw [h11r9, WordOps.add_no_wrap _ _ (by rw [h10r9v, h10rN]; omega), h10r9v, h10rN]; omega
  have h11r5 : (reg st11 r5).val = Q := by
    rw [h11keep r5 (by decide), h10keep r5 (by decide), h9keep r5 (by decide), h8keep r5 (by decide)]; exact h7r5
  have h11r1 : (reg st11 rOne).val = 1 := by
    rw [h11keep rOne (by decide), h10keep rOne (by decide), h9keep rOne (by decide), h8keep rOne (by decide)]; exact h7r1
  have hf11 : code[st11.pc]? = some (.add r10 r5 rOne) := by
    rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st12, hs12, hpc12, h12r10, h12keep, h12data⟩ :=
    step_add16 (input := input) hf11
      (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h12r10v : (reg st12 r10).val = Q + 1 := by
    rw [h12r10, WordOps.add_no_wrap _ _ (by rw [h11r5, h11r1]; omega), h11r5, h11r1]
  have h12r7 : (reg st12 r7).val = denseInBase + 1 := by
    rw [h12keep r7 (by decide), h11keep r7 (by decide), h10keep r7 (by decide),
        h9keep r7 (by decide), h8keep r7 (by decide)]; exact h7r7
  have h12r1 : (reg st12 rOne).val = 1 := by rw [h12keep rOne (by decide)]; exact h11r1
  have hf12 : code[st12.pc]? = some (.add r7 r7 rOne) := by
    rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st13, hs13, hpc13, h13r7, h13keep, h13data⟩ :=
    step_add16 (input := input) hf12
      (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h13r7v : (reg st13 r7).val = denseInBase + 2 := by
    rw [h13r7, WordOps.add_no_wrap _ _ (by rw [h12r7, h12r1]; omega), h12r7, h12r1]
  have h13r0 : (reg st13 rZero).val = 0 := by
    rw [h13keep rZero (by decide), h12keep rZero (by decide), h11keep rZero (by decide),
        h10keep rZero (by decide), h9keep rZero (by decide), h8keep rZero (by decide)]; exact h7r0
  have hf13 : code[st13.pc]? = some (.mov r11 rZero) := by
    rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st14, hs14, hpc14, h14r11, h14keep, h14data⟩ :=
    step_mov16 (input := input) hf13
      (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h14pc : st14.pc = 14 := by
    rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]
  have hPre14 : Steps code input 14 st0 st14 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.zero _))))))))))))))
  have h14Dsz : st14.data.size = workCap := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data, Array.size_set, h6Dsz]
  have h14dataEq : ∀ idx, 2 ≤ idx → idx < denseInBase → st14.data[idx]? = s1.data[idx]? := by
    intro idx hLo hHi
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data,
        h7data, Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data, Array.getElem?_set_ne _ (by rw [h4r7]; omega),
        h4data, Array.getElem?_set_ne _ (by rw [h3r1]; omega),
        h3data, h2data, Array.getElem?_set_ne _ (by rw [h1r0]; omega), h1data]
    rfl
  have h14keepConst : ∀ r : Fin 16, r = rZero ∨ r = rOne ∨ r = rN ∨ r = rM ∨ r = r5 ∨ r = r6 →
      reg st14 r = reg s1 r := by
    intro r hr
    have hNe7 : r ≠ r7 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe9 : r ≠ r9 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe10 : r ≠ r10 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe11 : r ≠ r11 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h14keep r hNe11, h13keep r hNe7, h12keep r hNe10, h11keep r hNe9,
        h10keep r hNe9, h9keep r hNe9, h8keep r hNe9]
    exact h7const r hr
  have h14_0 : st14.data[0]? = some ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩ := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data,
        Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data, Array.getElem?_set_ne _ (by rw [h4r7]; omega),
        h4data, Array.getElem?_set_ne _ (by rw [h3r1]; omega),
        h3data, h2data]
    simp only [h1r0, Array.getElem?_set_self, h1r7]
  have h14_1 : st14.data[1]? = some ⟨quarter, quarter_lt_pow2 hw hTen⟩ := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data,
        Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data, Array.getElem?_set_ne _ (by rw [h4r7]; omega),
        h4data]
    simp only [h3r1, Array.getElem?_set_self, h3r8]
  have h14_d0 : (st14.data[denseInBase]?).map Fin.val = some Q := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data,
        Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data]
    simp only [h4r7, Array.getElem?_set_self, Option.map_some]
    exact congrArg some (by rw [reg_eq_of_regs_eq h4regs, h3keep r5 (by decide),
      reg_eq_of_regs_eq h2regs, h1keep r5 (by decide)]; exact hr5)
  have h14_d1 : (st14.data[denseInBase + 1]?).map Fin.val = some mReach := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data]
    simp only [h6r7v, Array.getElem?_set_self, Option.map_some]
    exact congrArg some (by rw [h6keep r6 (by decide), reg_eq_of_regs_eq h5regs,
      reg_eq_of_regs_eq h4regs, h3keep r6 (by decide), reg_eq_of_regs_eq h2regs,
      h1keep r6 (by decide)]; exact hr6)
  have h14r10v : (reg st14 r10).val = Q + 1 := by
    rw [h14keep r10 (by decide), h13keep r10 (by decide)]; exact h12r10v
  have h14r9v : (reg st14 r9).val = 6 * n := by
    rw [h14keep r9 (by decide), h13keep r9 (by decide), h12keep r9 (by decide)]; exact h11r9v
  have h14r7v : (reg st14 r7).val = denseInBase + 2 := by
    rw [h14keep r7 (by decide)]; exact h13r7v
  have h14r11v : (reg st14 r11).val = 0 := by
    rw [h14r11]; exact h13r0
  exact ⟨st14, hPre14, h14pc, h14Dsz, h14dataEq,
    by rw [h14keepConst rZero (Or.inl rfl)]; exact hConst.zero,
    by rw [h14keepConst rOne (Or.inr (Or.inl rfl))]; exact hConst.one,
    by rw [h14keepConst rN (Or.inr (Or.inr (Or.inl rfl)))]; exact hConst.nVal,
    by rw [h14keepConst r5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hr5,
    by rw [h14keepConst r6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]; exact hr6,
    h14r7v, h14r9v, h14r10v, h14r11v, h14_0, h14_1, h14_d0, h14_d1⟩

private theorem run_copyDenseIn {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q mReach : Nat}
    (hnPos : 1 ≤ n) (hQPos : 1 ≤ Q) (hQLe : Q ≤ n) (hmLe : mReach ≤ m)
    (hCap : 64 * (n + m + 1) ≤ workCap)
    (inStart inSrc : Nat → Nat)
    (s1 : State (layout16 bits inputCap workCap hi hw))
    (hConst : ConstRegs n m root s1)
    (hr5 : (reg s1 r5).val = Q)
    (hr6 : (reg s1 r6).val = mReach)
    (hStart1 : ∀ i, i ≤ Q → (s1.data[6 * n + i]?).map Fin.val = some (inStart i))
    (hSrc1 : ∀ k, k < mReach → (s1.data[7 * n + 1 + k]?).map Fin.val = some (inSrc k)) :
    let quarter := prefixQuarter workCap
    let denseInBase := prefixDenseInBase workCap
    ∃ (s2 : State (layout16 bits inputCap workCap hi hw)) (steps2 : Nat),
      steps2 ≤ 7 * Q + 7 * mReach + 28 ∧
      run (copyDenseInPhase (hi := hi) hw hTen).code input steps2 (Phase.initial s1) =
        some ⟨s2, steps2⟩ ∧
      s2.data.size = workCap ∧
      s2.data[0]? = some ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩ ∧
      s2.data[1]? = some ⟨quarter, quarter_lt_pow2 hw hTen⟩ ∧
      (s2.data[denseInBase]?).map Fin.val = some Q ∧
      (s2.data[denseInBase + 1]?).map Fin.val = some mReach ∧
      (∀ i, i ≤ Q → (s2.data[denseInBase + 2 + i]?).map Fin.val = some (inStart i)) ∧
      (∀ k, k < mReach → (s2.data[denseInBase + 3 + Q + k]?).map Fin.val = some (inSrc k)) ∧
      (∀ idx, 3 * n ≤ idx → idx < 5 * n → s2.data[idx]? = s1.data[idx]?) := by
  intro quarter denseInBase
  let code := (copyDenseInPhase (hi := hi) hw hTen).code
  let st0 := Phase.initial s1
  have hCodeSz : code.size = 33 := rfl
  have hQuarterGe : 16 * (n + m + 1) ≤ quarter := by
    unfold quarter prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hInBaseGe : 48 * (n + m + 1) ≤ denseInBase := by
    unfold denseInBase prefixDenseInBase
    omega
  have hDenseInEnd : denseInBase + 3 + Q + mReach ≤ workCap := by
    unfold denseInBase prefixDenseInBase prefixQuarter
    omega
  have hFit7n1 : 7 * n + 1 + mReach ≤ workCap := by omega
  obtain ⟨st14, hPre14, h14pc, h14Dsz, h14dataEq, h14r0v, h14r1v, h14rNv, h14r5v, h14r6v,
      h14r7v, h14r9v, h14r10v, h14r11v, h14_0, h14_1, h14_d0, h14_d1⟩ :=
    run_copyDenseIn_pre14 input hnPos hQPos hQLe hmLe hCap s1 hConst hr5 hr6
  -- Loop 1: copy inStart[0..Q]
  have hPl1 : Placed code 14
      [ .branchLt r11 r10 15 21, .add r12 r9 r11, .loadData r13 r12, .add r12 r7 r11,
        .storeData r12 r13, .add r11 r11 rOne, .goto 14 ] := by
    intro j op hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp at hj <;> subst hj <;> rfl
  obtain ⟨st21, hLoop1, h21pc, h21Dsz, h21_0, h21_1, h21_N, h21_M, h21_5, h21_6, h21_7, h21_9, h21_10,
      h21_inStart, h21_frame⟩ :=
    copyBankLoop_steps (input := input) 14 21 r10 r9 r7 (6 * n) (denseInBase + 2) (Q + 1)
      (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) hPl1 (by omega) (by omega) (Or.inl (by omega)) inStart
      (Q + 1) 0 st14 (Nat.zero_add _) h14pc h14Dsz
      h14r1v h14r10v h14r9v h14r7v h14r11v
      (fun k hk => by
        have hlt : 6 * n + k < denseInBase := by omega
        have hlo : 2 ≤ 6 * n + k := by omega
        rw [h14dataEq _ hlo hlt]; exact hStart1 k (by omega))
      (fun k hk => by omega)
  -- Step 21..24: r9 := 7*n+1, r7 := denseInBase + 3 + Q, r11 := 0
  have hf21 : code[st21.pc]? = some (.add r9 r9 rN) := by rw [h21pc]; rfl
  obtain ⟨st22, hs22, hpc22, h22r9, h22keep, h22data⟩ :=
    step_add16 (input := input) hf21 (by rw [h21pc, hCodeSz]; omega)
  have h21_9v : (reg st21 r9).val = 6 * n := by rw [h21_9]; exact h14r9v
  have h21_Nv : (reg st21 rN).val = n := by rw [h21_N]; exact h14rNv
  have h22r9v : (reg st22 r9).val = 7 * n := by
    rw [h22r9, WordOps.add_no_wrap _ _ (by rw [h21_9v, h21_Nv]; omega), h21_9v, h21_Nv]; omega
  have h22r1 : (reg st22 rOne).val = 1 := by
    rw [h22keep rOne (by decide), h21_1]; exact h14r1v
  have hf22 : code[st22.pc]? = some (.add r9 r9 rOne) := by rw [hpc22, h21pc]; rfl
  obtain ⟨st23, hs23, hpc23, h23r9, h23keep, h23data⟩ :=
    step_add16 (input := input) hf22 (by rw [hpc22, h21pc, hCodeSz]; omega)
  have h23r9v : (reg st23 r9).val = 7 * n + 1 := by
    rw [h23r9, WordOps.add_no_wrap _ _ (by rw [h22r9v, h22r1]; omega), h22r9v, h22r1]
  have h23r7v : (reg st23 r7).val = denseInBase + 2 := by
    rw [h23keep r7 (by decide), h22keep r7 (by decide), h21_7]; exact h14r7v
  have h23r10v : (reg st23 r10).val = Q + 1 := by
    rw [h23keep r10 (by decide), h22keep r10 (by decide), h21_10]; exact h14r10v
  have hf23 : code[st23.pc]? = some (.add r7 r7 r10) := by rw [hpc23, hpc22, h21pc]; rfl
  obtain ⟨st24, hs24, hpc24, h24r7, h24keep, h24data⟩ :=
    step_add16 (input := input) hf23 (by rw [hpc23, hpc22, h21pc, hCodeSz]; omega)
  have hDenseInLt : denseInBase + 3 + Q < workCap := by
    unfold denseInBase prefixDenseInBase prefixQuarter
    omega
  have h24r7v : (reg st24 r7).val = denseInBase + 3 + Q := by
    rw [h24r7, WordOps.add_no_wrap _ _ (by rw [h23r7v, h23r10v]; omega), h23r7v, h23r10v]; omega
  have h24r0v : (reg st24 rZero).val = 0 := by
    rw [h24keep rZero (by decide), h23keep rZero (by decide), h22keep rZero (by decide), h21_0]
    exact h14r0v
  have hf24 : code[st24.pc]? = some (.mov r11 rZero) := by rw [hpc24, hpc23, hpc22, h21pc]; rfl
  obtain ⟨st25, hs25, hpc25, h25r11, h25keep, h25data⟩ :=
    step_mov16 (input := input) hf24 (by rw [hpc24, hpc23, hpc22, h21pc, hCodeSz]; omega)
  have h25pc : st25.pc = 25 := by rw [hpc25, hpc24, hpc23, hpc22, h21pc]
  have hMid4 : Steps code input 4 st21 st25 :=
    Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24 (Steps.cons hs25 (Steps.zero _))))
  have h25Dsz : st25.data.size = workCap := by
    rw [h25data, h24data, h23data, h22data, h21Dsz]
  have h25dataEq : st25.data = st21.data := by
    rw [h25data, h24data, h23data, h22data]
  -- Loop 2: copy inSrc[0..mReach-1]
  have hPl2 : Placed code 25
      [ .branchLt r11 r6 26 32, .add r12 r9 r11, .loadData r13 r12, .add r12 r7 r11,
        .storeData r12 r13, .add r11 r11 rOne, .goto 25 ] := by
    intro j op hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp at hj <;> subst hj <;> rfl
  have h25_6 : (reg st25 r6).val = mReach := by
    rw [h25keep r6 (by decide), h24keep r6 (by decide), h23keep r6 (by decide),
        h22keep r6 (by decide), h21_6]; exact h14r6v
  have h25_1 : (reg st25 rOne).val = 1 := by
    rw [h25keep rOne (by decide), h24keep rOne (by decide), h23keep rOne (by decide)]; exact h22r1
  have h25_9 : (reg st25 r9).val = 7 * n + 1 := by
    rw [h25keep r9 (by decide), h24keep r9 (by decide)]; exact h23r9v
  have h25_7 : (reg st25 r7).val = denseInBase + 3 + Q := by
    rw [h25keep r7 (by decide)]; exact h24r7v
  obtain ⟨st32, hLoop2, h32pc, h32Dsz, _, _, _, _, _, _, _, _, _, h32_inSrc, h32_frame⟩ :=
    copyBankLoop_steps (input := input) 25 32 r6 r9 r7 (7 * n + 1) (denseInBase + 3 + Q) mReach
      (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) hPl2 (by omega) (by omega) (Or.inl (by omega)) inSrc
      mReach 0 st25 (Nat.zero_add _) h25pc h25Dsz h25_1 h25_6 h25_9 h25_7
      (by rw [h25r11]; exact h24r0v)
      (fun k hk => by
        have hlt : 7 * n + 1 + k < denseInBase := by omega
        have hlo : 2 ≤ 7 * n + 1 + k := by omega
        rw [h25dataEq, h21_frame _ (Or.inl (by omega)), h14dataEq _ hlo hlt]
        exact hSrc1 k hk)
      (fun k hk => by omega)
  have hf32 : code[st32.pc]? = some .halt := by rw [h32pc]; rfl
  have hTotalSteps : Steps code input (14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1)) st0 st32 := by
    simpa only [Nat.add_assoc] using (hPre14.append (hLoop1.append (hMid4.append hLoop2)))
  have hRun : run code input (14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1) + 1) st0 =
      some ⟨st32, 14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1) + 1⟩ :=
    hTotalSteps.halts (step_halt_at hf32)
  refine ⟨st32, 14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1) + 1, by omega, hRun, h32Dsz,
    ?_, ?_, ?_, ?_, ?_, h32_inSrc, ?_⟩
  · rw [h32_frame 0 (Or.inl (by omega)), h25dataEq, h21_frame 0 (Or.inl (by omega))]; exact h14_0
  · rw [h32_frame 1 (Or.inl (by omega)), h25dataEq, h21_frame 1 (Or.inl (by omega))]; exact h14_1
  · rw [h32_frame denseInBase (Or.inl (by omega)), h25dataEq, h21_frame denseInBase (Or.inl (by omega))]
    exact h14_d0
  · rw [h32_frame (denseInBase + 1) (Or.inl (by omega)), h25dataEq,
        h21_frame (denseInBase + 1) (Or.inl (by omega))]
    exact h14_d1
  · intro i hi
    rw [h32_frame (denseInBase + 2 + i) (Or.inl (by omega)), h25dataEq]
    exact h21_inStart i (by omega)
  · intro idx h3n h5n
    have hGe2 : 2 ≤ idx := by omega
    have hLtQ : idx < denseInBase := by omega
    rw [h32_frame idx (Or.inl (by omega)), h25dataEq, h21_frame idx (Or.inl (by omega))]
    exact h14dataEq idx hGe2 hLtQ

end CopyDenseInProof

section EpilogueProof

private theorem run_epilogue {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    {linkedCode : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    (base Q mReach : Nat)
    (hPl : Placed linkedCode base (epilogueCode (hi := hi) (hw := hw) hTen).toList)
    (hSz : base + 8 ≤ linkedCode.size)
    (s : State (layout16 bits inputCap workCap hi hw))
    (hpc : s.pc = base)
    (hPtr0 : s.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩)
    (hPtr1 : s.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩)
    (hQ : (s.data[prefixDenseInBase workCap]?).map Fin.val = some Q)
    (hM : (s.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach)
    (hFit : prefixDenseInBase workCap + 1 < 2 ^ bits) :
    ∃ (u : State (layout16 bits inputCap workCap hi hw)) (steps : Nat),
      steps = 8 ∧
      run linkedCode input steps s = some ⟨u, steps⟩ ∧
      u.data = s.data ∧
      (reg u r5).val = Q ∧
      (reg u r6).val = prefixTreeBase workCap ∧
      (reg u r8).val = mReach := by
  have hf0 : linkedCode[s.pc]? = some (.imm r15 ⟨0, by omega⟩) := by rw [hpc]; exact hPl 0 _ rfl
  obtain ⟨s1, hs1, hpc1, h1r15, h1keep, h1data⟩ := step_imm16 (input := input) hf0 (by omega)
  have h1r15v : (reg s1 r15).val = 0 := by rw [h1r15]
  have hf1 : linkedCode[s1.pc]? = some (.loadData r15 r15) := by rw [hpc1, hpc]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, h2r15, h2keep, h2data⟩ :=
    step_loadData16 (input := input) hf1 (by rw [h1r15v, h1data]; exact hPtr0) (by omega)
  have h2r15v : (reg s2 r15).val = prefixDenseInBase workCap := by rw [h2r15]
  obtain ⟨wQ, hwQ, hwQv⟩ : ∃ w, s2.data[(reg s2 r15).val]? = some w ∧ w.val = Q := by
    rw [h2r15v, h2data, h1data]
    cases hq : s.data[prefixDenseInBase workCap]? with
    | none => simp [hq] at hQ
    | some w => exact ⟨w, rfl, by simpa [hq] using hQ⟩
  have hf2 : linkedCode[s2.pc]? = some (.loadData r5 r15) := by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, h3r5, h3keep, h3data⟩ := step_loadData16 (input := input) hf2 hwQ (by omega)
  have hf3 : linkedCode[s3.pc]? = some (.imm r7 ⟨1, by omega⟩) := by
    rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl
  obtain ⟨s4, hs4, hpc4, h4r7, h4keep, h4data⟩ := step_imm16 (input := input) hf3 (by omega)
  have h4r15v : (reg s4 r15).val = prefixDenseInBase workCap := by
    rw [h4keep r15 (by decide), h3keep r15 (by decide)]; exact h2r15v
  have h4r7v : (reg s4 r7).val = 1 := by rw [h4r7]
  have hf4 : linkedCode[s4.pc]? = some (.add r15 r15 r7) := by
    rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl
  obtain ⟨s5, hs5, hpc5, h5r15, h5keep, h5data⟩ := step_add16 (input := input) hf4 (by omega)
  have h5r15v : (reg s5 r15).val = prefixDenseInBase workCap + 1 := by
    rw [h5r15, WordOps.add_no_wrap _ _ (by rw [h4r15v, h4r7v]; exact hFit), h4r15v, h4r7v]
  obtain ⟨wM, hwM, hwMv⟩ : ∃ w, s5.data[(reg s5 r15).val]? = some w ∧ w.val = mReach := by
    rw [h5r15v, h5data, h4data, h3data, h2data, h1data]
    cases hm : s.data[prefixDenseInBase workCap + 1]? with
    | none => simp [hm] at hM
    | some w => exact ⟨w, rfl, by simpa [hm] using hM⟩
  have hf5 : linkedCode[s5.pc]? = some (.loadData r8 r15) := by
    rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl
  obtain ⟨s6, hs6, hpc6, h6r8, h6keep, h6data⟩ := step_loadData16 (input := input) hf5 hwM (by omega)
  have h6r7v : (reg s6 r7).val = 1 := by rw [h6keep r7 (by decide), h5keep r7 (by decide)]; exact h4r7v
  have hf6 : linkedCode[s6.pc]? = some (.loadData r6 r7) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl
  obtain ⟨s7, hs7, hpc7, h7r6, h7keep, h7data⟩ :=
    step_loadData16 (input := input) hf6
      (by rw [h6r7v, h6data, h5data, h4data, h3data, h2data, h1data]; exact hPtr1) (by omega)
  have hf7 : linkedCode[s7.pc]? = some .halt := by
    rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 7 _ rfl
  have hSteps7 : Steps linkedCode input 7 s s7 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
      (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero _)))))))
  have hRun8 : run linkedCode input 8 s = some ⟨s7, 8⟩ := hSteps7.halts (step_halt_at hf7)
  refine ⟨s7, 8, rfl, hRun8, ?_, ?_, ?_, ?_⟩
  · rw [h7data, h6data, h5data, h4data, h3data, h2data, h1data]
  · rw [h7keep r5 (by decide), h6keep r5 (by decide), h5keep r5 (by decide),
        h4keep r5 (by decide), h3r5]; exact hwQv
  · rw [h7r6]
  · rw [h7keep r8 (by decide), h6r8]; exact hwMv

end EpilogueProof

section EndToEndSpec

/-- **EX5.1 Unified Prefix Execution Specification**:
From raw CSR input `RawDagInput input g r` on any acyclic `g` with source `r` and linear
workspace `64 * (n + m + 1) ≤ workCap` (which comfortably includes `prefixWorkCap n m =
25 * n + 2 * m + 16`), the single fixed program `buildPrefixProgram hi hw hTen` halts cleanly in
`steps ≤ 4326 * (n + m + 1) * (OracleContract.L n)^2` operations with peak live words
`inputCap + workCap + 16`, preserving `origToDensePlusOne` & `denseToOrig` at `[3*n..5*n)`,
writing `domAndStaticTreeProgram`'s `[0..11*Q)` static tree layout at `[treeBase..treeBase + 11*Q)`
(`treeBase = workCap / 4`), and returning `r5 = Q`, `r6 = treeBase`, `r8 = mReach`. -/
private theorem build_denseSpec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {g : Digraph} {r : Fin g.vertexCount}
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order)
    (hCap : 64 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (s1 s12 : State (layout16 bits inputCap workCap hi hw))
    (h2Dsz : s12.data.size = workCap)
    (h2_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val =
      some (denseVertices g r order hTopo).length)
    (h2_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val =
      some (denseReachArcCount g (denseVertices g r order hTopo)))
    (h2_start : ∀ i ≤ (denseVertices g r order hTopo).length,
      (s12.data[prefixDenseInBase workCap + 2 + i]?).map Fin.val =
        some (denseInPrefix g (denseVertices g r order hTopo) i))
    (inSrc : Nat → Nat)
    (h2_src : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s12.data[prefixDenseInBase workCap + 3 + (denseVertices g r order hTopo).length + k]?).map Fin.val =
        some (inSrc k))
    (hQPos : 1 ≤ (denseVertices g r order hTopo).length)
    (hQLe : (denseVertices g r order hTopo).length ≤ g.vertexCount)
    (hmLe : denseReachArcCount g (denseVertices g r order hTopo) ≤ g.arcCount)
    (hHead : (denseVertices g r order hTopo)[0]'(denseVertices_length_pos g r order hTopo) = r)
    (hReach : ∀ i (hi₁ : i < (denseVertices g r order hTopo).length),
      g.InitiallyReachable r ((denseVertices g r order hTopo)[i]'hi₁))
    (hArcOrder : ∀ u v : Fin (denseVertices g r order hTopo).length,
      g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
        ((denseVertices g r order hTopo)[v.val]'v.isLt) → u.val < v.val)
    (hStartBounds : denseInPrefix g (denseVertices g r order hTopo) 0 = 0 ∧
      denseInPrefix g (denseVertices g r order hTopo) (denseVertices g r order hTopo).length =
        denseReachArcCount g (denseVertices g r order hTopo))
    (hSrcFin1 : ∀ (v : Fin (denseVertices g r order hTopo).length) (k : Nat),
      denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k →
      k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) →
      ∃ u : Fin (denseVertices g r order hTopo).length,
        (s1.data[inSrcBase g.vertexCount g.arcCount + k]?).map Fin.val = some u.val)
    (hDenseIff1 : ∀ u v : Fin (denseVertices g r order hTopo).length,
      g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
        ((denseVertices g r order hTopo)[v.val]'v.isLt) ↔
        ∃ k, denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k ∧
          k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) ∧
          (s1.data[inSrcBase g.vertexCount g.arcCount + k]?).map Fin.val = some u.val)
    (hSrcRead1 : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s1.data[7 * g.vertexCount + 1 + k]?).map Fin.val = some (inSrc k)) :
    let subL := prefixSubLayout bits workCap hw
    let subInput : Input subL :=
      ⟨Array.ofFn (fun j : Fin (prefixSubInCap workCap) =>
        s12.data[prefixDenseInBase workCap + j.val]'(by
          rw [h2Dsz]
          unfold prefixDenseInBase prefixSubInCap prefixQuarter
          omega)),
       Array.size_ofFn⟩
    (∀ j : Nat, j < prefixSubInCap workCap →
      s12.data[prefixDenseInBase workCap + j]? = subInput.words[j]?) ∧
    RamDomBuild.DenseIncomingSpec subInput (denseVertices g r order hTopo).length
      (denseReachArcCount g (denseVertices g r order hTopo))
      (denseInPrefix g (denseVertices g r order hTopo)) inSrc := by
  intro subL subInput
  have hQuarterGe : 16 * (g.vertexCount + g.arcCount + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hSubInRead : ∀ j : Nat, j < prefixSubInCap workCap →
      s12.data[prefixDenseInBase workCap + j]? = subInput.words[j]? := by
    intro j hj
    have hjDom : prefixDenseInBase workCap + j < s12.data.size := by
      rw [h2Dsz]; unfold prefixDenseInBase prefixSubInCap prefixQuarter at *; omega
    rw [Array.getElem?_eq_getElem hjDom]
    have hjSub : j < subInput.words.size := by simpa only [subInput.size_eq] using hj
    rw [Array.getElem?_eq_getElem hjSub]
    simp only [subInput, Array.getElem_ofFn]
  refine ⟨hSubInRead, hQPos, ?_, ?_, ?_, ?_, hStartBounds.1, hStartBounds.2, ?_, ?_, ?_, ?_, ?_⟩
  · change 3 + (denseVertices g r order hTopo).length +
      denseReachArcCount g (denseVertices g r order hTopo) ≤ prefixSubInCap workCap
    unfold prefixSubInCap prefixQuarter at *
    omega
  · change 5 * (denseVertices g r order hTopo).length + 10 ≤ prefixSubWorkCap workCap
    unfold prefixSubWorkCap prefixQuarter at *
    omega
  · rw [← hSubInRead 0 (by unfold prefixSubInCap prefixQuarter at *; omega)]; exact h2_d0
  · rw [← hSubInRead 1 (by unfold prefixSubInCap prefixQuarter at *; omega)]; exact h2_d1
  · intro v _
    exact denseInPrefix_mono g (denseVertices g r order hTopo) (Nat.le_succ v)
  · intro v hv1 hvQ
    obtain ⟨d0, hd0⟩ : ∃ x, x = (denseVertices g r order hTopo)[v]'hvQ := ⟨_, rfl⟩
    have hR := hReach v hvQ
    rw [← hd0] at hR
    rcases AvoidPath.eq_or_exists_last_arc hR with hEq | ⟨u, huReach, huArc⟩
    · exfalso
      have hNd := denseVertices_nodup g r order hTopo
      have hPair := (List.pairwise_iff_getElem.mp hNd) 0 v
        (denseVertices_length_pos g r order hTopo) hvQ hv1
      exact hPair (hHead.trans (hEq.trans hd0))
    · have huMem : u ∈ denseVertices g r order hTopo :=
        (denseVertices_mem_iff g r order hTopo u).mpr huReach
      obtain ⟨ui, huiLt, huiEq⟩ := List.mem_iff_getElem.mp huMem
      have hArcD : g.HasArc ((denseVertices g r order hTopo)[ui]'huiLt)
          ((denseVertices g r order hTopo)[v]'hvQ) := by
        simpa only [huiEq, ← hd0] using huArc
      obtain ⟨pos, hpLo, hpHi, _⟩ := (hDenseIff1 ⟨ui, huiLt⟩ ⟨v, hvQ⟩).mp hArcD
      dsimp only at hpLo hpHi
      omega
  · intro v k hv1 hvQ hkLo hkHi
    obtain ⟨u, hu⟩ := hSrcFin1 ⟨v, hvQ⟩ k hkLo hkHi
    have hkLt : k < denseReachArcCount g (denseVertices g r order hTopo) :=
      Nat.lt_of_lt_of_le hkHi (by
        rw [← hStartBounds.2]
        exact denseInPrefix_mono g (denseVertices g r order hTopo) (Nat.succ_le_of_lt hvQ))
    have hRead := hSrcRead1 k hkLt
    have hu' : (s1.data[7 * g.vertexCount + 1 + k]?).map Fin.val = some u.val := by
      simpa only [inSrcBase_eq] using hu
    have hInSrcK : inSrc k = u.val := Option.some.inj (hRead.symm.trans hu')
    have hArcD : g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
        ((denseVertices g r order hTopo)[v]'hvQ) :=
      (hDenseIff1 u ⟨v, hvQ⟩).mpr ⟨k, hkLo, hkHi, hu⟩
    rw [hInSrcK]
    exact hArcOrder u ⟨v, hvQ⟩ hArcD
  · intro i hi
    rw [← hSubInRead (2 + i) (by unfold prefixSubInCap prefixQuarter at *; omega)]
    simpa only [Nat.add_assoc] using h2_start i hi
  · intro k hk
    rw [← hSubInRead (3 + (denseVertices g r order hTopo).length + k)
      (by unfold prefixSubInCap prefixQuarter at *; omega)]
    simpa only [Nat.add_assoc] using h2_src k hk

private theorem run_phase3_lift_epilogue {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {Q mReach : Nat}
    (s12 : State (layout16 bits inputCap workCap hi hw))
    (h12_0 : s12.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩)
    (h12_1 : s12.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩)
    (h12_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val = some Q)
    (h12_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach)
    (hDenseFit : prefixDenseInBase workCap + 1 < 2 ^ bits)
    (subInput : Input (prefixSubLayout bits workCap hw))
    (subCode : Program (prefixSubLayout bits workCap hw))
    (right : Program (layout16 bits inputCap workCap hi hw))
    (subS0 tSub : State (prefixSubLayout bits workCap hw))
    (work3 : Nat)
    (hRun3 : run subCode subInput work3 (Phase.initial subS0) = some ⟨tSub, work3⟩)
    (hCfg3 : RamDataSliceAdapter.SliceConfig (prefixSubLayout bits workCap hw)
      (layout16 bits inputCap workCap hi hw)
      ⟨0, by omega⟩ ⟨1, by omega⟩ (prefixDenseInBase workCap) (prefixTreeBase workCap)
      subInput (Phase.initial s12).data)
    (hBody3 : RamDataSliceAdapter.BodyRelocated
      (bigL := layout16 bits inputCap workCap hi hw) rfl
      ⟨0, by omega⟩ ⟨1, by omega⟩ subCode right 0)
    (hPlEp : Placed right (4 * subCode.size)
      (epilogueCode (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw) hTen).toList)
    (hRightSz : right.size = 4 * subCode.size + 8)
    (hSim3 : RamDataSliceAdapter.SliceSim (subL := prefixSubLayout bits workCap hw)
      (bigL := layout16 bits inputCap workCap hi hw) rfl rfl (prefixTreeBase workCap) 0
      (Phase.initial s12).data (Phase.initial subS0) (Phase.initial s12))
    (hTreeGt1 : 1 < prefixTreeBase workCap)
    (hSubDenseLo : prefixTreeBase workCap + prefixSubWorkCap workCap ≤ prefixDenseInBase workCap) :
    ∃ (sEndRight : State (layout16 bits inputCap workCap hi hw)) (m3 : Nat),
      m3 ≤ 4 * work3 ∧
      run right input (m3 + 8) (Phase.initial s12) = some ⟨sEndRight, m3 + 8⟩ ∧
      (reg sEndRight r5).val = Q ∧
      (reg sEndRight r6).val = prefixTreeBase workCap ∧
      (reg sEndRight r8).val = mReach ∧
      (∀ addr, addr < prefixTreeBase workCap → sEndRight.data[addr]? = s12.data[addr]?) ∧
      (∀ j : Nat, j < prefixSubWorkCap workCap →
        sEndRight.data[prefixTreeBase workCap + j]? = tSub.data[j]?) := by
  have hExitLt3 : 0 + 4 * subCode.size < right.size := by omega
  obtain ⟨m3, sMid3, hm3Le, hSteps3, hpcMid3, _, hMid3Data, hMid3Frame⟩ :=
    RamDataSliceAdapter.liftProgram_relocated_steps
      (subL := prefixSubLayout bits workCap hw)
      (bigL := layout16 bits inputCap workCap hi hw) rfl rfl subCode subInput right input
      ⟨0, by omega⟩ ⟨1, by omega⟩ (prefixDenseInBase workCap) (prefixTreeBase workCap) 0
      work3 (Phase.initial subS0) ⟨tSub, work3⟩ (Phase.initial s12)
      hRun3 hCfg3 hBody3 hExitLt3 hSim3
  have hMid3_0 : sMid3.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩ := by
    rw [hMid3Frame 0 (Or.inl (by omega))]; exact h12_0
  have hMid3_1 : sMid3.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩ := by
    rw [hMid3Frame 1 (Or.inl hTreeGt1)]; exact h12_1
  have hMid3_d0 : (sMid3.data[prefixDenseInBase workCap]?).map Fin.val = some Q := by
    rw [hMid3Frame (prefixDenseInBase workCap) (Or.inr (by dsimp only [prefixSubLayout]; exact hSubDenseLo))]
    exact h12_d0
  have hMid3_d1 : (sMid3.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach := by
    rw [hMid3Frame (prefixDenseInBase workCap + 1) (Or.inr (by dsimp only [prefixSubLayout]; omega))]
    exact h12_d1
  obtain ⟨sEndRight, kEp, hkEp, hRunEp, hEpData, hEpR5, hEpR6, hEpR8⟩ :=
    run_epilogue (4 * subCode.size) Q mReach hPlEp (Nat.le_of_eq hRightSz.symm)
      sMid3 (by simpa only [Nat.zero_add] using hpcMid3)
      hMid3_0 hMid3_1 hMid3_d0 hMid3_d1 hDenseFit
  have hRunRight : run right input (m3 + 8) (Phase.initial s12) =
      some ⟨sEndRight, m3 + 8⟩ := by
    obtain ⟨kEp0, lastEp, stEp, haltEp, costEp⟩ := run_has_steps_then_halt hRunEp
    obtain ⟨atHaltEp, sameEp⟩ := halted_fetch_and_state haltEp
    have termEp : step right input lastEp = some (.halted sEndRight) := by
      change sEndRight = lastEp at sameEp
      rw [sameEp]
      exact step_halt_at atHaltEp
    have hTot := (hSteps3.append stEp).halts termEp
    have hCostEq : kEp = kEp0 + 1 := costEp
    rw [Nat.add_assoc, ← hCostEq, hkEp] at hTot
    exact hTot
  refine ⟨sEndRight, m3, hm3Le, hRunRight, hEpR5, hEpR6, hEpR8, ?_, ?_⟩
  · intro addr hLt
    rw [hEpData, hMid3Frame addr (Or.inl hLt)]; rfl
  · intro j hj
    rw [hEpData]
    exact hMid3Data j hj

private theorem run_phase3_and_epilogue {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m Q mReach : Nat}
    (hnPos : 1 ≤ n) (hQPos : 1 ≤ Q) (hQLe : Q ≤ n) (_hmLe : mReach ≤ m)
    (hCap : 64 * (n + m + 1) ≤ workCap)
    {inStart inSrc : Nat → Nat}
    (s12 : State (layout16 bits inputCap workCap hi hw))
    (h12Dsz : s12.data.size = workCap)
    (h12_0 : s12.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩)
    (h12_1 : s12.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩)
    (h12_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val = some Q)
    (h12_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach)
    (subInput : Input (prefixSubLayout bits workCap hw))
    (hSubInRead : ∀ j : Nat, j < prefixSubInCap workCap →
      s12.data[prefixDenseInBase workCap + j]? = subInput.words[j]?)
    (hSp : RamDomBuild.DenseIncomingSpec subInput Q mReach inStart inSrc) :
    let right := prefixRightCode (hi := hi) hw hTen
    ∃ (tSub : State (prefixSubLayout bits workCap hw))
      (sEndRight : State (layout16 bits inputCap workCap hi hw))
      (work3 m3 : Nat) (parent : Fin Q → Fin Q) (depth : Fin Q → Nat),
      let x := RamDomAndStaticTree.staticInput hQPos parent depth
      let built := PackedStaticLayout.build x
      let tables := StaticHeadSweep.tables built.packed
      work3 ≤ 1050 * (Q + mReach) * OracleContract.L Q ^ 2 ∧
      m3 ≤ 4 * work3 ∧
      run right input (m3 + 8) (Phase.initial s12) = some ⟨sEndRight, m3 + 8⟩ ∧
      (reg sEndRight r5).val = Q ∧
      (reg sEndRight r6).val = prefixTreeBase workCap ∧
      (reg sEndRight r8).val = mReach ∧
      (∀ addr, addr < prefixTreeBase workCap → sEndRight.data[addr]? = s12.data[addr]?) ∧
      (∀ j : Nat, j < prefixSubWorkCap workCap →
        sEndRight.data[prefixTreeBase workCap + j]? = tSub.data[j]?) ∧
      ParentSpec (RamDomBuild.denseDigraph Q inStart inSrc) ⟨0, hQPos⟩ parent ∧
      LabelledQuotient.ValidDepthTree ⟨0, hQPos⟩ parent depth ∧
      EX16.Valid tables ∧
      (∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val) ∧
      (∀ v : Fin Q, (tSub.data[v.val]?).map Fin.val = some (parent v).val) ∧
      (∀ v : Fin Q, (tSub.data[Q + v.val]?).map Fin.val = some (depth v)) ∧
      (∀ u : Fin Q, (tSub.data[2 * Q + u.val]?).map Fin.val =
        some (match built.packed.heavy.read u with | none => Q | some h => h.val)) ∧
      (∀ v : Fin Q, (tSub.data[3 * Q + v.val]?).map Fin.val = some (tables.head v).val) ∧
      (∀ v : Fin Q, (tSub.data[4 * Q + v.val]?).map Fin.val = some (built.endpoints.entry.read v)) ∧
      (∀ v : Fin Q, (tSub.data[5 * Q + v.val]?).map Fin.val = some (built.endpoints.stop.read v)) ∧
      (∀ v : Fin Q,
        built.endpoints.entry.read v < built.endpoints.stop.read v ∧
        built.endpoints.stop.read v ≤ Q ∧
        (tSub.data[6 * Q + built.endpoints.entry.read v]?).map Fin.val = some v.val) ∧
      (tSub.data[7 * Q]?).map Fin.val = some 0 ∧
      (tSub.data[8 * Q]?).map Fin.val = some (Q - 1) ∧
      (∀ u : Fin Q,
        ∃ lo hiB : Nat,
          (tSub.data[7 * Q + u.val]?).map Fin.val = some lo ∧
          (tSub.data[7 * Q + u.val + 1]?).map Fin.val = some hiB ∧
          hiB = lo + (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length ∧
          hiB ≤ Q - 1 ∧
          (∀ j : Nat, ∀ hj : j < (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length,
            let c := (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u)[j]'hj
            (tSub.data[10 * Q + 1 + lo + j]?).map Fin.val = some c.val ∧
            (tSub.data[8 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.entry.read c) ∧
            (tSub.data[9 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.stop.read c)) ∧
          (∀ i j : Nat, i < j → j < hiB - lo →
            ∃ ei ej : Nat,
              (tSub.data[8 * Q + 1 + lo + i]?).map Fin.val = some ei ∧
              (tSub.data[8 * Q + 1 + lo + j]?).map Fin.val = some ej ∧
              ei < ej)) := by
  intro right
  have hQuarterGe : 16 * (n + m + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  let subL := prefixSubLayout bits workCap hw
  let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
    (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
  let subS0 : State subL :=
    { regs := Array.ofFn fun i : Fin 15 =>
        s12.regs[i.val]'(by rw [s12.regs_size]; exact Nat.lt_succ_of_lt i.isLt)
      data := Array.ofFn fun j : Fin (prefixSubWorkCap workCap) =>
        s12.data[prefixTreeBase workCap + j.val]'(by
          rw [h12Dsz]; unfold prefixTreeBase prefixSubWorkCap prefixQuarter; omega)
      pc := 0
      regs_size := Array.size_ofFn
      data_size := Array.size_ofFn }
  have hSubDataCap : 17 * Q ≤ prefixSubWorkCap workCap := by
    unfold prefixSubWorkCap; omega
  have hSubWordCap : 17 * Q < 2 ^ bits := by
    have : 17 * Q ≤ 2 * prefixQuarter workCap := hSubDataCap
    unfold prefixQuarter at this
    omega
  obtain ⟨tSub, _, work3, parent, depth, hWork3Le, hRun3, _, _, hParSpec, hTree, hValidTables,
      hParLt, hSubPar, hSubDep, hSubHeavy, hSubHead, hSubEnt, hSubStop, hSubDofE,
      hSubCsr0, hSubCsrLast, hSubBuckets⟩ :=
    RamDomAndStaticTree.run_domAndStaticTree (input := subInput) hSp hSubDataCap hSubWordCap subS0
  have hCfg3 : RamDataSliceAdapter.SliceConfig subL (layout16 bits inputCap workCap hi hw)
      ⟨0, by omega⟩ ⟨1, by omega⟩ (prefixDenseInBase workCap) (prefixTreeBase workCap)
      subInput (Phase.initial s12).data := by
    refine ⟨three_quarter_lt_pow2 hw hTen, quarter_lt_pow2 hw hTen, ?_, ?_, ?_, ?_,
      h12_0, h12_1, Or.inl ?_, Or.inl ?_, Or.inr ?_, hSubInRead⟩
    · change 0 < workCap; omega
    · change 1 < workCap; omega
    · change prefixDenseInBase workCap + prefixSubInCap workCap ≤ workCap
      unfold prefixDenseInBase prefixSubInCap prefixQuarter; omega
    · change prefixTreeBase workCap + prefixSubWorkCap workCap ≤ workCap
      unfold prefixTreeBase prefixSubWorkCap prefixQuarter; omega
    · change 0 < prefixTreeBase workCap
      unfold prefixTreeBase prefixQuarter at *; omega
    · change 1 < prefixTreeBase workCap
      unfold prefixTreeBase prefixQuarter at *; omega
    · change prefixTreeBase workCap + prefixSubWorkCap workCap ≤ prefixDenseInBase workCap
      unfold prefixTreeBase prefixSubWorkCap prefixDenseInBase prefixQuarter; omega
  have hSim3 : RamDataSliceAdapter.SliceSim (subL := subL)
      (bigL := layout16 bits inputCap workCap hi hw) rfl rfl (prefixTreeBase workCap) 0
      (Phase.initial s12).data (Phase.initial subS0) (Phase.initial s12) := by
    refine ⟨rfl, ?_, ?_, fun _ _ => rfl⟩
    · intro i
      have hi16 : i.val < (Phase.initial s12).regs.size := by
        rw [(Phase.initial s12).regs_size]; exact Nat.lt_succ_of_lt i.isLt
      have hi15 : i.val < (Phase.initial subS0).regs.size := by
        rw [(Phase.initial subS0).regs_size]; exact i.isLt
      rw [Array.getElem?_eq_getElem hi16, Array.getElem?_eq_getElem hi15]
      simp only [Phase.initial, subS0, Array.getElem_ofFn]
    · intro j hj
      have hjWork : prefixTreeBase workCap + j < (Phase.initial s12).data.size := by
        rw [Phase.initial_data, h12Dsz]
        dsimp only [subL, prefixSubLayout] at hj
        unfold prefixTreeBase prefixSubWorkCap prefixQuarter at *; omega
      have hjSub : j < (Phase.initial subS0).data.size := by
        simpa only [Phase.initial_data, subS0.data_size] using hj
      rw [Array.getElem?_eq_getElem hjWork, Array.getElem?_eq_getElem hjSub]
      simp only [Phase.initial, subS0, Array.getElem_ofFn]
  have hBody3 := prefixRightCode_bodyRelocated (hi := hi) hw hTen
  have hRightSz : right.size = 4 * subCode.size + 8 :=
    prefixRightCode_size (hi := hi) hw hTen
  have hTenSubEq :
      RamDomAndStaticTree.domAndStaticTreeProgram
        (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) (by have := hSp.qPos; omega) = subCode :=
    congrArg (RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw)) (Subsingleton.elim _ hTen)
  have hRun3' : run subCode subInput work3 (Phase.initial subS0) = some ⟨tSub, work3⟩ := by
    rw [← hTenSubEq]; exact hRun3
  obtain ⟨sEndRight, m3, hm3Le, hRunRight, hEpR5, hEpR6, hEpR8, hEndPre, hEndTree⟩ :=
    run_phase3_lift_epilogue input s12 h12_0 h12_1 h12_d0 h12_d1
      (by unfold prefixDenseInBase prefixQuarter; omega)
      subInput subCode right subS0 tSub work3 hRun3' hCfg3 hBody3
      (prefixRightCode_epilogue_placed (hi := hi) hw hTen) hRightSz hSim3
      (by unfold prefixTreeBase prefixQuarter at *; omega)
      (by unfold prefixTreeBase prefixSubWorkCap prefixDenseInBase prefixQuarter; omega)
  exact ⟨tSub, sEndRight, work3, m3, parent, depth, hWork3Le, hm3Le, hRunRight, hEpR5, hEpR6, hEpR8,
    hEndPre, hEndTree, hParSpec, hTree, hValidTables, hParLt,
    hSubPar, hSubDep, hSubHeavy, hSubHead, hSubEnt, hSubStop, hSubDofE,
    hSubCsr0, hSubCsrLast, hSubBuckets⟩

private theorem extract_staticTree_props {bits workCap Q : Nat}
    (hQPos : 1 ≤ Q) (hQCap : 11 * Q ≤ prefixSubWorkCap workCap)
    (parent : Fin Q → Fin Q) (depth : Fin Q → Nat)
    (tData tSubData : Array (Word bits))
    (hTreeEq : ∀ j : Nat, j < prefixSubWorkCap workCap →
      tData[prefixTreeBase workCap + j]? = tSubData[j]?)
    (hSubPar : ∀ v : Fin Q, (tSubData[v.val]?).map Fin.val = some (parent v).val)
    (hSubDep : ∀ v : Fin Q, (tSubData[Q + v.val]?).map Fin.val = some (depth v))
    (hSubHeavy : ∀ u : Fin Q, (tSubData[2 * Q + u.val]?).map Fin.val =
      some (match (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed.heavy.read u with
        | none => Q | some h => h.val))
    (hSubHead : ∀ v : Fin Q, (tSubData[3 * Q + v.val]?).map Fin.val =
      some ((StaticHeadSweep.tables (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed).head v).val)
    (hSubEnt : ∀ v : Fin Q, (tSubData[4 * Q + v.val]?).map Fin.val =
      some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v))
    (hSubStop : ∀ v : Fin Q, (tSubData[5 * Q + v.val]?).map Fin.val =
      some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v))
    (hSubDofE : ∀ v : Fin Q,
      (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v <
        (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v ∧
      (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v ≤ Q ∧
      (tSubData[6 * Q + (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v]?).map Fin.val =
        some v.val)
    (hSubCsr0 : (tSubData[7 * Q]?).map Fin.val = some 0)
    (hSubCsrLast : (tSubData[8 * Q]?).map Fin.val = some (Q - 1))
    (hSubBuckets : ∀ u : Fin Q,
      ∃ lo hiB : Nat,
        (tSubData[7 * Q + u.val]?).map Fin.val = some lo ∧
        (tSubData[7 * Q + u.val + 1]?).map Fin.val = some hiB ∧
        hiB = lo + (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length ∧
        hiB ≤ Q - 1 ∧
        (∀ j : Nat, ∀ hj : j < (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length,
          let c := (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u)[j]'hj
          (tSubData[10 * Q + 1 + lo + j]?).map Fin.val = some c.val ∧
          (tSubData[8 * Q + 1 + lo + j]?).map Fin.val =
            some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read c) ∧
          (tSubData[9 * Q + 1 + lo + j]?).map Fin.val =
            some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read c)) ∧
        (∀ i j : Nat, i < j → j < hiB - lo →
          ∃ ei ej : Nat,
            (tSubData[8 * Q + 1 + lo + i]?).map Fin.val = some ei ∧
            (tSubData[8 * Q + 1 + lo + j]?).map Fin.val = some ej ∧
            ei < ej)) :
    let treeBase := prefixTreeBase workCap
    let x := RamDomAndStaticTree.staticInput hQPos parent depth
    let built := PackedStaticLayout.build x
    let tables := StaticHeadSweep.tables built.packed
    (∀ v : Fin Q, (tData[treeBase + v.val]?).map Fin.val = some (parent v).val) ∧
    (∀ v : Fin Q, (tData[treeBase + Q + v.val]?).map Fin.val = some (depth v)) ∧
    (∀ u : Fin Q, (tData[treeBase + 2 * Q + u.val]?).map Fin.val =
      some (match built.packed.heavy.read u with | none => Q | some h => h.val)) ∧
    (∀ v : Fin Q, (tData[treeBase + 3 * Q + v.val]?).map Fin.val = some (tables.head v).val) ∧
    (∀ v : Fin Q, (tData[treeBase + 4 * Q + v.val]?).map Fin.val = some (built.endpoints.entry.read v)) ∧
    (∀ v : Fin Q, (tData[treeBase + 5 * Q + v.val]?).map Fin.val = some (built.endpoints.stop.read v)) ∧
    (∀ v : Fin Q,
      built.endpoints.entry.read v < built.endpoints.stop.read v ∧
      built.endpoints.stop.read v ≤ Q ∧
      (tData[treeBase + 6 * Q + built.endpoints.entry.read v]?).map Fin.val = some v.val) ∧
    (tData[treeBase + 7 * Q]?).map Fin.val = some 0 ∧
    (tData[treeBase + 8 * Q]?).map Fin.val = some (Q - 1) ∧
    (∀ u : Fin Q,
      ∃ lo hiB : Nat,
        (tData[treeBase + 7 * Q + u.val]?).map Fin.val = some lo ∧
        (tData[treeBase + 7 * Q + u.val + 1]?).map Fin.val = some hiB ∧
        hiB = lo + (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length ∧
        hiB ≤ Q - 1 ∧
        (∀ j : Nat, ∀ hj : j < (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length,
          let c := (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u)[j]'hj
          (tData[treeBase + 10 * Q + 1 + lo + j]?).map Fin.val = some c.val ∧
          (tData[treeBase + 8 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.entry.read c) ∧
          (tData[treeBase + 9 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.stop.read c)) ∧
        (∀ i j : Nat, i < j → j < hiB - lo →
          ∃ ei ej : Nat,
            (tData[treeBase + 8 * Q + 1 + lo + i]?).map Fin.val = some ei ∧
            (tData[treeBase + 8 * Q + 1 + lo + j]?).map Fin.val = some ej ∧
            ei < ej)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v; rw [hTreeEq v.val (by omega)]; exact hSubPar v
  · intro v; rw [Nat.add_assoc, hTreeEq (Q + v.val) (by omega)]; exact hSubDep v
  · intro u; rw [Nat.add_assoc, hTreeEq (2 * Q + u.val) (by omega)]; exact hSubHeavy u
  · intro v; rw [Nat.add_assoc, hTreeEq (3 * Q + v.val) (by omega)]; exact hSubHead v
  · intro v; rw [Nat.add_assoc, hTreeEq (4 * Q + v.val) (by omega)]; exact hSubEnt v
  · intro v; rw [Nat.add_assoc, hTreeEq (5 * Q + v.val) (by omega)]; exact hSubStop v
  · intro v
    obtain ⟨h1, h2, h3⟩ := hSubDofE v
    refine ⟨h1, h2, ?_⟩
    rw [Nat.add_assoc, hTreeEq _ (by omega)]
    exact h3
  · rw [hTreeEq (7 * Q) (by omega)]; exact hSubCsr0
  · rw [hTreeEq (8 * Q) (by omega)]; exact hSubCsrLast
  · intro u
    obtain ⟨lo, hiB, hLo, hHi, hLen, hHiLe, hKids, hMon⟩ := hSubBuckets u
    refine ⟨lo, hiB, ?_, ?_, hLen, hHiLe, ?_, ?_⟩
    · rw [Nat.add_assoc, hTreeEq (7 * Q + u.val) (by omega)]; exact hLo
    · rw [Nat.add_assoc (prefixTreeBase workCap), Nat.add_assoc (prefixTreeBase workCap),
          hTreeEq (7 * Q + u.val + 1) (by omega)]
      exact hHi
    · intro j hj
      obtain ⟨hId, hEn, hSt⟩ := hKids j hj
      refine ⟨?_, ?_, ?_⟩
      · simp only [Nat.add_assoc] at hId ⊢
        rw [hTreeEq _ (by omega)]; exact hId
      · simp only [Nat.add_assoc] at hEn ⊢
        rw [hTreeEq _ (by omega)]; exact hEn
      · simp only [Nat.add_assoc] at hSt ⊢
        rw [hTreeEq _ (by omega)]; exact hSt
    · intro i j hij hjLt
      obtain ⟨ei, ej, hei, hej, hlt⟩ := hMon i j hij hjLt
      refine ⟨ei, ej, ?_, ?_, hlt⟩
      · simp only [Nat.add_assoc] at hei ⊢
        rw [hTreeEq _ (by omega)]; exact hei
      · simp only [Nat.add_assoc] at hej ⊢
        rw [hTreeEq _ (by omega)]; exact hej

/-- **EX5.1 Unified Prefix Execution Specification**:
From raw CSR input `RawDagInput input g r` on any acyclic `g` with source `r` and linear
workspace `64 * (n + m + 1) ≤ workCap` (which comfortably includes `prefixWorkCap n m =
25 * n + 2 * m + 16`), the single fixed program `buildPrefixProgram hi hw hTen` halts cleanly in
`steps ≤ 4326 * (n + m + 1) * (OracleContract.L n)^2` operations with peak live words
`inputCap + workCap + 16`, preserving `origToDensePlusOne` & `denseToOrig` at `[3*n..5*n)`,
writing `domAndStaticTreeProgram`'s `[0..11*Q)` static tree layout at `[treeBase..treeBase + 11*Q)`
(`treeBase = workCap / 4`), and returning `r5 = Q`, `r6 = treeBase`, `r8 = mReach`. -/
theorem run_build_prefix {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (hCap : 64 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (s₀ : State (layout16 bits inputCap workCap hi hw)) :
    let n := g.vertexCount
    let m := g.arcCount
    let hTen : 10 ≤ 2 ^ bits := by
      have := Fin.pos r
      omega
    let treeBase := prefixTreeBase workCap
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (trace : List (State (layout16 bits inputCap workCap hi hw)))
      (steps : Nat)
      (order : List (Fin n)) (hlen : order.length = n) (hTopo : g.IsTopologicalList order),
      let dense := denseVertices g r order hTopo
      let Q := dense.length
      let mReach := denseReachArcCount g dense
      let inStart := denseInPrefix g dense
      ∃ (inSrc : Nat → Nat) (parent : Fin Q → Fin Q) (depth : Fin Q → Nat)
        (hQPos : 1 ≤ Q),
        let x := RamDomAndStaticTree.staticInput hQPos parent depth
        let built := PackedStaticLayout.build x
        let tables := StaticHeadSweep.tables built.packed
        steps ≤ 4326 * (n + m + 1) * OracleContract.L n ^ 2 ∧
        run (buildPrefixProgram hi hw hTen) input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
        SuccessfulTrace (buildPrefixProgram hi hw hTen) input (Phase.initial s₀) trace ⟨t, steps⟩ ∧
        tracePeakWords input trace = inputCap + workCap + 16 ∧
        (reg t r5).val = Q ∧
        (reg t r6).val = treeBase ∧
        (reg t r8).val = mReach ∧
        Q ≤ n ∧
        mReach ≤ m ∧
        (dense[0]'(denseVertices_length_pos g r order hTopo)) = r ∧
        (∀ i : Nat, (hi_1 : i < Q) → g.InitiallyReachable r (dense[i]'hi_1)) ∧
        (∀ i : Nat, (hi_1 : i < Q) →
          (t.data[denseToOrigBase n m + i]?).map Fin.val = some (dense[i]'hi_1).val) ∧
        (∀ i : Nat, (hi_1 : i < Q) →
          (t.data[origToDensePlusOneBase n m + (dense[i]'hi_1).val]?).map Fin.val = some (i + 1)) ∧
        (∀ v : Fin n, ¬ g.InitiallyReachable r v →
          (t.data[origToDensePlusOneBase n m + v.val]?).map Fin.val = some 0) ∧
        (∀ u v : Fin Q,
          (RamDomBuild.denseDigraph Q inStart inSrc).HasArc u v ↔
            g.HasArc (dense[u.val]'u.isLt) (dense[v.val]'v.isLt)) ∧
        ParentSpec (RamDomBuild.denseDigraph Q inStart inSrc) ⟨0, hQPos⟩ parent ∧
        LabelledQuotient.ValidDepthTree ⟨0, hQPos⟩ parent depth ∧
        EX16.Valid tables ∧
        (∀ v : Fin Q, 1 ≤ v.val → (parent v).val < v.val) ∧
        (∀ v : Fin Q, (t.data[treeBase + v.val]?).map Fin.val = some (parent v).val) ∧
        (∀ v : Fin Q, (t.data[treeBase + Q + v.val]?).map Fin.val = some (depth v)) ∧
        (∀ u : Fin Q, (t.data[treeBase + 2 * Q + u.val]?).map Fin.val =
          some (match built.packed.heavy.read u with | none => Q | some h => h.val)) ∧
        (∀ v : Fin Q, (t.data[treeBase + 3 * Q + v.val]?).map Fin.val = some (tables.head v).val) ∧
        (∀ v : Fin Q, (t.data[treeBase + 4 * Q + v.val]?).map Fin.val = some (built.endpoints.entry.read v)) ∧
        (∀ v : Fin Q, (t.data[treeBase + 5 * Q + v.val]?).map Fin.val = some (built.endpoints.stop.read v)) ∧
        (∀ v : Fin Q,
          built.endpoints.entry.read v < built.endpoints.stop.read v ∧
          built.endpoints.stop.read v ≤ Q ∧
          (t.data[treeBase + 6 * Q + built.endpoints.entry.read v]?).map Fin.val = some v.val) ∧
        (t.data[treeBase + 7 * Q]?).map Fin.val = some 0 ∧
        (t.data[treeBase + 8 * Q]?).map Fin.val = some (Q - 1) ∧
        (∀ u : Fin Q,
          ∃ lo hi : Nat,
            (t.data[treeBase + 7 * Q + u.val]?).map Fin.val = some lo ∧
            (t.data[treeBase + 7 * Q + u.val + 1]?).map Fin.val = some hi ∧
            hi = lo + (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length ∧
            hi ≤ Q - 1 ∧
            (∀ j : Nat, ∀ hj : j < (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u).length,
              let c := (LabelledQuotient.bucketChildren ⟨0, hQPos⟩ parent u)[j]'hj
              (t.data[treeBase + 10 * Q + 1 + lo + j]?).map Fin.val = some c.val ∧
              (t.data[treeBase + 8 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.entry.read c) ∧
              (t.data[treeBase + 9 * Q + 1 + lo + j]?).map Fin.val = some (built.endpoints.stop.read c)) ∧
            (∀ i j : Nat, i < j → j < hi - lo →
              ∃ ei ej : Nat,
                (t.data[treeBase + 8 * Q + 1 + lo + i]?).map Fin.val = some ei ∧
                (t.data[treeBase + 8 * Q + 1 + lo + j]?).map Fin.val = some ej ∧
                ei < ej)) := by
  intro n m hTen treeBase
  have hnPos : 1 ≤ n := Fin.pos r
  have h5 : 5 ≤ 2 ^ bits := by omega
  have hWorkRoom : rawDagWorkCap n m ≤ workCap := by unfold rawDagWorkCap; omega
  have hQuarterGe : 16 * (n + m + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  obtain ⟨s1, _, steps1, order, hlen, hTopo, hSteps1Le, hRun1, _, _, hConst1, hr5_1, hr6_1,
      hQPos, hQLe, hmLe, hHead, _, _, _, hReach, hDenseToOrig1, hOrigToDense1, hZero1,
      hArcOrder, hStart1, hStartBounds, _, hSrcFin1, _, hDenseIff1⟩ :=
    run_dag_reach_kahn input raw acyc hWorkRoom s₀
  let inSrc : Nat → Nat := fun k => ((s1.data[inSrcBase n m + k]?).map Fin.val).getD 0
  have hSrcRead1 : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s1.data[7 * n + 1 + k]?).map Fin.val = some (inSrc k) := by
    intro k hk
    have hIn : ∃ v : Fin (denseVertices g r order hTopo).length,
        denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k ∧
        k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) := by
      have aux : ∀ bound : Nat, bound ≤ (denseVertices g r order hTopo).length →
          k < denseInPrefix g (denseVertices g r order hTopo) bound →
          ∃ v : Fin (denseVertices g r order hTopo).length,
            denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k ∧
            k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) := by
        intro bound
        induction bound with
        | zero => intro _ h0; rw [hStartBounds.1] at h0; omega
        | succ b ih =>
          intro hb hSb
          by_cases hkPrev : k < denseInPrefix g (denseVertices g r order hTopo) b
          · exact ih (by omega) hkPrev
          · exact ⟨⟨b, by omega⟩, by dsimp only; omega, by simpa only using hSb⟩
      exact aux (denseVertices g r order hTopo).length (Nat.le_refl _) (by rw [hStartBounds.2]; exact hk)
    obtain ⟨v, hvLo, hvHi⟩ := hIn
    obtain ⟨u, hu⟩ := hSrcFin1 v k hvLo hvHi
    dsimp only [inSrc]
    rw [inSrcBase_eq] at hu ⊢
    rw [hu]
    rfl
  obtain ⟨s2, steps2, hSteps2Le, hRun2, h2Dsz, h2_0, h2_1, h2_d0, h2_d1, h2_start, h2_src, h2_pres35⟩ :=
    run_copyDenseIn input hnPos hQPos hQLe hmLe hCap
      (denseInPrefix g (denseVertices g r order hTopo)) inSrc s1 hConst1 hr5_1 hr6_1
      (fun i hi => by simpa [inStartBase] using hStart1 i hi) hSrcRead1
  have hRun1' : run (dagReachKahnPhase h5).code input steps1 (Phase.initial s₀) = some ⟨s1, steps1⟩ := by
    rw [dagReachKahnPhase_code]; exact hRun1
  obtain ⟨s12, _, h12Regs, h12Data, hRun12, _, _⟩ :=
    run_linked_pair (dagReachKahnPhase h5) (copyDenseInPhase hw hTen).code
      (by rw [copyDenseInPhase_code]; simp [copyDenseInCode]) hRun1' hRun2
  have h12Dsz : s12.data.size = workCap := by rw [h12Data, h2Dsz]
  have h12_0 : s12.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩ := by
    rw [h12Data]; exact h2_0
  have h12_1 : s12.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩ := by
    rw [h12Data]; exact h2_1
  have h12_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val =
      some (denseVertices g r order hTopo).length := by
    rw [h12Data]; exact h2_d0
  have h12_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val =
      some (denseReachArcCount g (denseVertices g r order hTopo)) := by
    rw [h12Data]; exact h2_d1
  have h12_start : ∀ i ≤ (denseVertices g r order hTopo).length,
      (s12.data[prefixDenseInBase workCap + 2 + i]?).map Fin.val =
        some (denseInPrefix g (denseVertices g r order hTopo) i) := by
    intro i hi; rw [h12Data]; exact h2_start i hi
  have h12_src : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s12.data[prefixDenseInBase workCap + 3 + (denseVertices g r order hTopo).length + k]?).map Fin.val =
        some (inSrc k) := by
    intro k hk; rw [h12Data]; exact h2_src k hk
  obtain ⟨hSubInRead, hSp⟩ := build_denseSpec (hi := hi) (hw := hw) order hTopo hCap
    s1 s12 h12Dsz h12_d0 h12_d1 h12_start inSrc h12_src
    hQPos hQLe hmLe hHead hReach hArcOrder hStartBounds hSrcFin1 hDenseIff1 hSrcRead1
  obtain ⟨tSub, sEndRight, work3, m3, parent, depth, hWork3Le, hm3Le, hRunRight,
      hEpR5, hEpR6, hEpR8, hEndPre, hEndTree, hParSpec, hTree, hValidTables, hParLt,
      hSubPar, hSubDep, hSubHeavy, hSubHead, hSubEnt, hSubStop, hSubDofE,
      hSubCsr0, hSubCsrLast, hSubBuckets⟩ :=
    run_phase3_and_epilogue input hnPos hQPos hQLe hmLe hCap s12 h12Dsz
      h12_0 h12_1 h12_d0 h12_d1 _ hSubInRead hSp
  obtain ⟨tFinal, traceFinal, htRegs, htData, hRunFinal, hTraceFinal, hPeakFinal⟩ :=
    run_linked_pair (buildPrefixPhase12 hi hw hTen) (prefixRightCode hw hTen)
      (prefixRightCode_pos hw hTen) hRun12 hRunRight
  have hLPos : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hLSqPos : 1 ≤ OracleContract.L n ^ 2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul hLPos hLPos
  have hLMono : OracleContract.L (denseVertices g r order hTopo).length ≤ OracleContract.L n :=
    L_mono hQLe
  have hLSqMono : OracleContract.L (denseVertices g r order hTopo).length ^ 2 ≤ OracleContract.L n ^ 2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul hLMono hLMono
  have hWork3N : work3 ≤ 1050 * (n + m + 1) * OracleContract.L n ^ 2 :=
    Nat.le_trans hWork3Le (Nat.mul_le_mul (Nat.mul_le_mul_left 1050 (by omega)) hLSqMono)
  have hm3N : m3 ≤ 4200 * (n + m + 1) * OracleContract.L n ^ 2 := by
    have h4 := Nat.mul_le_mul_left 4 hWork3N
    have hEq : 4 * (1050 * (n + m + 1) * OracleContract.L n ^ 2) =
        4200 * (n + m + 1) * OracleContract.L n ^ 2 := by
      simp only [← Nat.mul_assoc]
    exact Nat.le_trans hm3Le (hEq ▸ h4)
  have hSteps1N : steps1 ≤ 90 * (n + m + 1) * OracleContract.L n ^ 2 := by
    have h1 := Nat.mul_le_mul hSteps1Le hLSqPos
    simpa only [Nat.mul_one] using h1
  have hSteps2N : steps2 ≤ 28 * (n + m + 1) * OracleContract.L n ^ 2 := by
    have h2' : steps2 ≤ 28 * (n + m + 1) := by omega
    exact Nat.le_trans h2' (Nat.le_mul_of_pos_right _ hLSqPos)
  have hEpN : (8 : Nat) ≤ 8 * (n + m + 1) * OracleContract.L n ^ 2 := by
    have h1 : 1 ≤ (n + m + 1) * OracleContract.L n ^ 2 := Nat.mul_pos (by omega) hLSqPos
    have h8 := Nat.mul_le_mul_left 8 h1
    simpa only [Nat.mul_assoc, Nat.mul_one] using h8
  have hTotalStepsBound : steps1 + steps2 + (m3 + 8) ≤
      4326 * (n + m + 1) * OracleContract.L n ^ 2 := by
    have hSum : steps1 + steps2 + (m3 + 8) ≤
        (90 + 28 + 4200 + 8) * (n + m + 1) * OracleContract.L n ^ 2 := by
      have h1 := Nat.add_le_add (Nat.add_le_add hSteps1N hSteps2N) (Nat.add_le_add hm3N hEpN)
      simpa only [← Nat.add_mul] using h1
    exact Nat.le_trans hSum (by
      show (90 + 28 + 4200 + 8) * (n + m + 1) * OracleContract.L n ^ 2 ≤
          4326 * (n + m + 1) * OracleContract.L n ^ 2
      exact Nat.le_refl _)
  have h5nLtTree : 5 * n ≤ prefixTreeBase workCap := by
    unfold prefixTreeBase; omega
  have htDataPres35 : ∀ idx, 3 * n ≤ idx → idx < 5 * n → tFinal.data[idx]? = s1.data[idx]? := by
    intro idx hLo hHi
    have hLtTree : idx < prefixTreeBase workCap := Nat.lt_of_lt_of_le hHi h5nLtTree
    rw [htData, hEndPre idx hLtTree, h12Data, h2_pres35 idx hLo hHi]
  have htTreeEq : ∀ j : Nat, j < prefixSubWorkCap workCap →
      tFinal.data[prefixTreeBase workCap + j]? = tSub.data[j]? := by
    intro j hj
    rw [htData]
    exact hEndTree j hj
  have hQCap : 11 * (denseVertices g r order hTopo).length ≤ prefixSubWorkCap workCap := by
    unfold prefixSubWorkCap; omega
  obtain ⟨htPar, htDep, htHeavy, htHead, htEnt, htStop, htDofE, htCsr0, htCsrLast, htBuckets⟩ :=
    extract_staticTree_props hQPos hQCap parent depth tFinal.data tSub.data htTreeEq
      hSubPar hSubDep hSubHeavy hSubHead hSubEnt hSubStop hSubDofE hSubCsr0 hSubCsrLast hSubBuckets
  refine ⟨tFinal, traceFinal, steps1 + steps2 + (m3 + 8), order, hlen, hTopo, inSrc, parent, depth, hQPos,
    hTotalStepsBound, hRunFinal, hTraceFinal, ?_,
    ?_, ?_, ?_, hQLe, hmLe, hHead, hReach, ?_, ?_, ?_, ?_,
    hParSpec, hTree, hValidTables, hParLt,
    htPar, htDep, htHeavy, htHead, htEnt, htStop, htDofE, htCsr0, htCsrLast, htBuckets⟩
  · simpa [footprint, layout16] using hPeakFinal
  · rw [reg_eq_of_regs_eq htRegs]; exact hEpR5
  · rw [reg_eq_of_regs_eq htRegs]; exact hEpR6
  · rw [reg_eq_of_regs_eq htRegs]; exact hEpR8
  · intro i hi
    have hLo : 3 * n ≤ denseToOrigBase n m + i := by
      rw [denseToOrigBase_eq]; omega
    have hHi : denseToOrigBase n m + i < 5 * n := by
      rw [denseToOrigBase_eq]; have : i < n := Nat.lt_of_lt_of_le hi hQLe; omega
    rw [htDataPres35 _ hLo hHi]
    exact hDenseToOrig1 i hi
  · intro i hi
    have hlt : ((denseVertices g r order hTopo)[i]'hi).val < n :=
      ((denseVertices g r order hTopo)[i]'hi).isLt
    have hLo : 3 * n ≤ origToDensePlusOneBase n m + ((denseVertices g r order hTopo)[i]'hi).val := by
      rw [origToDensePlusOneBase_eq]; omega
    have hHi : origToDensePlusOneBase n m + ((denseVertices g r order hTopo)[i]'hi).val < 5 * n := by
      rw [origToDensePlusOneBase_eq]; omega
    rw [htDataPres35 _ hLo hHi]
    exact hOrigToDense1 i hi
  · intro v hv
    have hlt : v.val < n := v.isLt
    have hLo : 3 * n ≤ origToDensePlusOneBase n m + v.val := by
      rw [origToDensePlusOneBase_eq]; omega
    have hHi : origToDensePlusOneBase n m + v.val < 5 * n := by
      rw [origToDensePlusOneBase_eq]; omega
    rw [htDataPres35 _ hLo hHi]
    exact hZero1 v hv
  · intro u v
    rw [RamDomBuild.denseDigraph_hasArc_iff, hDenseIff1 u v]
    constructor
    · rintro ⟨_, k, hkLo, hkHi, hSrcEq⟩
      refine ⟨k, hkLo, hkHi, ?_⟩
      have hVlt : v.val < (denseVertices g r order hTopo).length := v.isLt
      have hkLt : k < denseReachArcCount g (denseVertices g r order hTopo) :=
        Nat.lt_of_lt_of_le hkHi (by
          rw [← hStartBounds.2]
          exact denseInPrefix_mono g (denseVertices g r order hTopo) (Nat.succ_le_of_lt hVlt))
      have hk1 := hSrcRead1 k hkLt
      rw [← inSrcBase_eq n m] at hk1
      rw [hk1, hSrcEq]
    · rintro ⟨k, hkLo, hkHi, hkEq⟩
      refine ⟨?_, k, hkLo, hkHi, ?_⟩
      · have hOrd := hArcOrder u v ((hDenseIff1 u v).mpr ⟨k, hkLo, hkHi, hkEq⟩)
        omega
      · dsimp only [inSrc]
        have hEq : s1.data[inSrcBase n m + k]? = s1.data[inSrcBase g.vertexCount g.arcCount + k]? := rfl
        rw [hEq, hkEq]; rfl

end EndToEndSpec

end PaperB.RamBuildPrefix
