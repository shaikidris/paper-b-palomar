module

public import PaperB.RamForestSweepBase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.Sweep

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.DepthSeek
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.ForestHead (Vertex TestSpec)
open PaperB.ForestDictionary (Rows packedDictionary packedDictionary_spec dictionary dictionary_spec)
open PaperB.ForestSlimIndex
open PaperB.PairLookup (Key)
open PaperB.RetainedProperLoss (WordColumns packWordColumns BackWords packBackWords encodeBackPair)
open PaperB.EX24.FinalDFS (packedInput nodeCount nodeCount_eq_next packedInput_parent packedInput_root)
open _root_.EX24 (Config Grounded)
open _root_.EX24.PreStep (climb Embedding)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedPairCode orderedConfig orderedRows)
open PaperB.ForestHead (preparedKey)
open PaperB.ForestDictionary (packedDictionary_eq)
open _root_.EX24 (initial initial_grounded)
open _root_.EX24.PreStep (initialUp initial_embedding boundedJumpParent)
open PaperB.Machine

section SweepLoopProgram

private def sweepBSHeader {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcBS pcAfterBS : Nat) : List (Instr bits 15) :=
  let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
  let b0a := loadScratch h8 rStack slLoBS ++ loadScratch h8 rRem slHiBS ++ [.add rTmp rStack rOne]
  let b0b : List (Instr bits 15) := [.branchLt rTmp rRem (pcBS + b0a.length + 1) pcAfterBS]
  let b0c : List (Instr bits 15) := [.sub rTmp rRem rStack, .shr1 rTmp rTmp, .add rCmd rStack rTmp]
  let b0d := sweepInitStoreScratch h8 slMidBS rCmd
  let b0e := loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase ++
    [.add rTout rTin rOne, .add rOff rTout rOne]
  let pcDL1 := pcBS + b0a.length + 1 + 3 + b0d.length + b0e.length
  let pcAfterDL1 := pcDL1 + dlProg.toList.length
  let b1 := relocatedSubroutine dlProg pcDL1 pcAfterDL1
  let b2 :=
    [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] ++
    sweepInitStoreScratch h8 slAncNode rPtr ++
    loadScratch h8 rClk slRowLo ++
    sweepInitStoreScratch h8 slPredJ rClk
  b0a ++ b0b ++ b0c ++ b0d ++ b0e ++ b1 ++ b2

private def bsProbePr0 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rClk slPredJ ++ loadScratch h8 rRem slRowHi

private def bsProbePr2 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rTmp slPredBuf ++
  [.add rTmp rTmp rClk, .loadData rStack rTmp] ++
  loadScratch h8 rChild slAncNode

private def bsProbePr3 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rTmp slBackFst ++ [.add rTmp rTmp rChild, .loadData rVal rTmp, .add rTmp rStack rOne]

private def bsProbePr5 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rTmp slBackSnd ++ [.add rTmp rTmp rChild, .loadData rVal rTmp]

private def bsProbePr7 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rTmp slLabels ++
  [.add rTmp rTmp rStack, .loadData rPtr rTmp] ++
  loadScratch h8 rTin slJumpBase ++
  [ .add rTmp rTin rChild, .add rTmp rTmp rChild, .add rTmp rTmp rChild, .add rTmp rTmp rOne,
    .loadData rCmd rTmp,
    .add rTmp rTin rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
    .loadData rVal rTmp ]

private def bsProbePr9Head {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] ++ loadScratch h8 rChild slAncNode

private def bsProbePrNext {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (pcProbe : Nat) : List (Instr bits 15) :=
  loadScratch h8 rClk slPredJ ++ [.add rClk rClk rOne] ++
  sweepInitStoreScratch h8 slPredJ rClk ++ [.goto pcProbe]

private theorem bsProbePr0_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (bsProbePr0 h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePr0, loadScratch_nonHalt]

private theorem bsProbePr2_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (bsProbePr2 h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePr2, loadScratch_nonHalt, nonHalt]

private theorem bsProbePr3_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (bsProbePr3 h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePr3, loadScratch_nonHalt, nonHalt]

private theorem bsProbePr5_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (bsProbePr5 h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePr5, loadScratch_nonHalt, nonHalt]

private theorem bsProbePr7_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (bsProbePr7 h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePr7, loadScratch_nonHalt, nonHalt]

private theorem bsProbePr9Head_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (bsProbePr9Head h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePr9Head, loadScratch_nonHalt, nonHalt]

private theorem bsProbePrNext_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) (pcProbe : Nat) :
    (bsProbePrNext h8 pcProbe).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp [bsProbePrNext, loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, nonHalt]

private def sweepBSProbe {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcProbe pcProbeOk pcProbeFail : Nat) : List (Instr bits 15) :=
  let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
  let pr0 := bsProbePr0 h8
  let pr2 := bsProbePr2 h8
  let pr3 := bsProbePr3 h8
  let pcChkBS := pcProbe + pr0.length + 1 + pr2.length + pr3.length + 2
  let pr5 := bsProbePr5 h8
  let pcChkAnc := pcChkBS + pr5.length + 2
  let pr7 := bsProbePr7 h8
  let pcDL2 := pcChkAnc + pr7.length + 3
  let pcAfterDL2 := pcDL2 + dlProg.toList.length
  let pr8 := relocatedSubroutine dlProg pcDL2 pcAfterDL2
  let pr9Head := bsProbePr9Head h8
  let pcNextU := pcAfterDL2 + pr9Head.length + 2
  let pr1 : List (Instr bits 15) := [.branchLt rClk rRem (pcProbe + pr0.length + 1) pcProbeOk]
  let pr4 : List (Instr bits 15) :=
    [.branchLt rTmp rVal pcChkBS (pcChkBS - 1), .branchLt rVal rTmp pcChkBS pcNextU]
  let pr6 : List (Instr bits 15) :=
    [.branchLt rStack rVal pcChkAnc (pcChkAnc - 1), .branchLt rVal rStack pcChkAnc pcNextU]
  let pr7b : List (Instr bits 15) :=
    [.branchLt rVal rCmd pcProbeFail (pcChkAnc + pr7.length + 1), .add rTout rTin rOne, .add rOff rTout rOne]
  let pr9 : List (Instr bits 15) := pr9Head ++
    [.branchLt rPtr rChild pcProbeFail (pcNextU - 1), .branchLt rChild rPtr pcProbeFail pcNextU]
  let prNext := bsProbePrNext h8 pcProbe
  pr0 ++ pr1 ++ pr2 ++ pr3 ++ pr4 ++ pr5 ++ pr6 ++ pr7 ++ pr7b ++ pr8 ++ pr9 ++ prNext

def sweepBSBlock {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcBS pcAfterBS : Nat) : List (Instr bits 15) :=
  let hdr := sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS
  let pcProbe := pcBS + hdr.length
  let prDummy := (sweepBSProbe (hi := hi) (hw := hw) h8 0 0 0).length
  let pcProbeOk := pcProbe + prDummy
  let prOk := loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slLoBS rVal ++ [.goto pcBS]
  let pcProbeFail := pcProbeOk + prOk.length
  let prFail := loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slHiBS rVal ++ [.goto pcBS]
  hdr ++ sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail ++ prOk ++ prFail

private theorem sweepBSHeader_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcBS pcAfterBS : Nat) :
    (sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepBSHeader
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, relocatedSubroutine_nonHalt, nonHalt, Bool.and_self]

private theorem sweepBSProbe_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcProbe pcProbeOk pcProbeFail : Nat) :
    (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepBSProbe
  simp only [List.all_append, List.all_cons, List.all_nil,
    bsProbePr0_nonHalt, bsProbePr2_nonHalt, bsProbePr3_nonHalt, bsProbePr5_nonHalt,
    bsProbePr7_nonHalt, bsProbePr9Head_nonHalt, bsProbePrNext_nonHalt,
    relocatedSubroutine_nonHalt, nonHalt, Bool.and_self]

theorem sweepBSBlock_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcBS pcAfterBS : Nat) :
    (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcAfterBS).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepBSBlock
  simp only [List.all_append, List.all_cons, List.all_nil,
    sweepBSHeader_nonHalt, sweepBSProbe_nonHalt, loadScratch_nonHalt, sweepInitStoreScratch_nonHalt,
    nonHalt, Bool.and_self]

def sweepFinalParentBlock {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcInstall : Nat) : List (Instr bits 15) :=
  let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
  let f0 := loadScratch h8 rCmd slLoBS
  let f2 := sweepInitStoreScratch h8 slAncNode rZero ++ [.goto pcInstall]
  let f1 : List (Instr bits 15) :=
    [.branchLt rZero rCmd (pcStart + f0.length + 1 + f2.length) (pcStart + f0.length + 1)]
  let f3 := loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase ++
    [.add rTout rTin rOne, .add rOff rTout rOne]
  let pcDL3 := pcStart + f0.length + 1 + f2.length + f3.length
  let pcAfterDL3 := pcDL3 + dlProg.toList.length
  let f4 := relocatedSubroutine dlProg pcDL3 pcAfterDL3
  let f5 := [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] ++
    sweepInitStoreScratch h8 slAncNode rPtr
  f0 ++ f1 ++ f2 ++ f3 ++ f4 ++ f5

theorem sweepFinalParentBlock_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcInstall : Nat) :
    (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcStart pcInstall).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepFinalParentBlock
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, relocatedSubroutine_nonHalt, nonHalt, Bool.and_self]

def sweepPairAndDictBS {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcKeepP pcWriteZero pcWriteLabel : Nat) : List (Instr bits 15) :=
  let i0 := loadScratch h8 rStack slRowLo ++ loadScratch h8 rRem slRowHi ++
    [.sub rRem rRem rStack, .add rTmp rOne rOne]
  let pcPair := pcStart + i0.length + 2
  let i1 : List (Instr bits 15) :=
    [.branchLt rRem rTmp pcKeepP (pcStart + i0.length + 1), .branchLt rTmp rRem pcKeepP pcPair]
  let i2 := loadScratch h8 rTmp slPredBuf ++ [.add rTmp rTmp rStack, .loadData rVal rTmp,
    .add rTmp rTmp rOne, .loadData rClk rTmp]
  let i3a := sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal
  let i4 := sweepInitStoreScratch h8 slKeyFst rVal ++ sweepInitStoreScratch h8 slKeySnd rClk
  let pcALtB := pcPair + i2.length + 1 + i3a.length + 1
  let pcDictBSInit := pcALtB + i4.length
  let i3 : List (Instr bits 15) := [.branchLt rVal rClk pcALtB (pcPair + i2.length + 1)] ++
    i3a ++ [.goto pcDictBSInit]
  let i5 := [.mov rClk rZero] ++ loadScratch h8 rRem slDictCnt ++ loadScratch h8 rChild slDictBase ++
    [.add rChild rChild rOne] ++ loadScratch h8 rCnt slDictSnd ++
    loadScratch h8 rStack slKeyFst ++ loadScratch h8 rVal slKeySnd
  let pcDictBS := pcDictBSInit + i5.length
  i0 ++ i1 ++ i2 ++ i3 ++ i4 ++ i5 ++
    [ .branchLt rClk rRem (pcDictBS + 1) pcWriteZero,
      .sub rTmp rRem rClk,
      .shr1 rTmp rTmp,
      .add rPtr rClk rTmp,
      .add rTmp rChild rPtr,
      .loadData rTin rTmp,
      .branchLt rTin rStack (pcDictBS + 13) (pcDictBS + 7),
      .branchLt rStack rTin (pcDictBS + 15) (pcDictBS + 8),
      .add rTmp rCnt rPtr,
      .loadData rTin rTmp,
      .branchLt rTin rVal (pcDictBS + 13) (pcDictBS + 11),
      .branchLt rVal rTin (pcDictBS + 15) (pcDictBS + 12),
      .goto (pcDictBS + 17),
      .add rClk rPtr rOne, .goto pcDictBS,
      .mov rRem rPtr, .goto pcDictBS ] ++
    loadScratch h8 rTmp slDictSlots ++
    [.add rTmp rTmp rPtr, .loadData rVal rTmp,
     .branchLt rZero rVal pcWriteLabel (pcDictBS + 17 + (loadScratch h8 rTmp slDictSlots).length + 3)]


theorem sweepPairAndDictBS_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (a b c d : Nat) :
    (sweepPairAndDictBS h8 a b c d).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepPairAndDictBS
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, nonHalt, Bool.and_self]

private theorem sweepBSHeader_length {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepBSHeader (hi := hi) (hw := hw) h8 s a).length =
      (sweepBSHeader (hi := hi) (hw := hw) h8 0 0).length := by
  unfold sweepBSHeader relocatedSubroutine
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]

private theorem sweepBSProbe_length {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) (s a b : Nat) :
    (sweepBSProbe (hi := hi) (hw := hw) h8 s a b).length =
      (sweepBSProbe (hi := hi) (hw := hw) h8 0 0 0).length := by
  unfold sweepBSProbe bsProbePrNext relocatedSubroutine
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]

theorem sweepBSBlock_length {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepBSBlock (hi := hi) (hw := hw) h8 s a).length =
      (sweepBSBlock (hi := hi) (hw := hw) h8 0 0).length := by
  unfold sweepBSBlock
  simp only [List.length_append, List.length_singleton]
  rw [sweepBSHeader_length h8 s a, sweepBSProbe_length h8]
  symm
  rw [sweepBSProbe_length h8]

theorem sweepFinalParentBlock_length {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepFinalParentBlock (hi := hi) (hw := hw) h8 s a).length =
      (sweepFinalParentBlock (hi := hi) (hw := hw) h8 0 0).length := by
  unfold sweepFinalParentBlock relocatedSubroutine
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map]

theorem sweepPairAndDictBS_length {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (s a b c : Nat) :
    (sweepPairAndDictBS h8 s a b c).length = (sweepPairAndDictBS h8 0 0 0 0).length := by
  unfold sweepPairAndDictBS; simp only [List.length_append, List.length_cons, List.length_nil]


end SweepLoopProgram

section SweepLoopExec

open PaperB.ForestHead _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

private theorem ancestor_iff_depth_atDepth {F : JumpForest} (hF : ValidJumpForest F)
    {anc u : Nat} (hanc : anc < F.size) (hu : u < F.size) :
    F.decideAncestor anc u = true ↔
      F.depthOf anc ≤ F.depthOf u ∧ F.ancestorAtDepth u (F.depthOf anc) = anc := by
  rw [hF.decideAncestor_eq_true_iff hanc hu]
  constructor
  · rintro ⟨k, hk⟩
    have hdep : F.depthOf anc = F.depthOf u - k := by
      rw [← hk]; exact hF.depth_iterParent hu k
    have hle : F.depthOf anc ≤ F.depthOf u := by omega
    have heq : anc = F.ancestorAtDepth u (F.depthOf anc) :=
      (hF.ancestorAtDepth_unique hu hle).mp ⟨⟨k, hk⟩, rfl⟩
    exact ⟨hle, heq.symm⟩
  · rintro ⟨hle, heq⟩
    have hspec := (hF.ancestorAtDepth_spec hu hle).2.1
    rwa [heq] at hspec

private theorem probe_ok_iff_ram {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    {y m_y : Vertex H} {mid : Nat}
    (hmidPos : 0 < mid) (hmidLe : mid ≤ F.depthOf (sRef.labelAt m_y.val)) :
    let c := orderedConfig dictRows large
    let S := selectors c sRef
    let mNode := sRef.labelAt m_y.val
    let ancNode := F.ancestorAtDepth mNode mid
    0 < ancNode ∧ ancNode < F.size ∧ F.depthOf ancNode = mid ∧
      ∃ q : CutPair H,
        sRef.tables.back[ancNode]? = some (some q) ∧
        (s.data[backFstBase H.vertexCount H.arcCount + ancNode]?).map Fin.val = some (q.fst.val + 1) ∧
        (s.data[backSndBase H.vertexCount H.arcCount + ancNode]?).map Fin.val = some q.snd.val ∧
        ((probe S (rows.row y) m_y mid).ok = true ↔
          ∀ u ∈ rows.row y, u = q.fst ∨ u = q.snd ∨
            (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
             F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode)) := by
  dsimp only
  let c := orderedConfig dictRows large
  let S := selectors c sRef
  let mNode := sRef.labelAt m_y.val
  let ancNode := F.ancestorAtDepth mNode mid
  have hmF : mNode < F.size := inv.grounded.size_eq ▸ inv.labelsLt m_y
  have hspec := inv.records.valid.ancestorAtDepth_spec hmF hmidLe
  have hancF : ancNode < F.size := hspec.1
  have hancDep : F.depthOf ancNode = mid := hspec.2.2
  have hancPos : 0 < ancNode := by
    by_cases h0 : ancNode = 0
    · obtain ⟨_, hFI⟩ := inv.records.valid.exists_forestInvariant
      have hroot : F.depthOf 0 = 0 := hFI.root_depth
      rw [h0, hroot] at hancDep
      omega
    · omega
  have hancNext : ancNode < sRef.tables.next := inv.grounded.size_eq ▸ hancF
  have hancLeN : ancNode ≤ H.vertexCount := by
    have h1 := inv.idxLe
    have h2 := inv.sRefNextLe
    change sRef.tables.next ≤ idx + 1 at h2
    omega
  obtain ⟨q, hq⟩ := inv.backPos ancNode hancPos hancNext
  have hBM := inv.backMem ancNode hancLeN
  have hJoin : sRef.tables.back[ancNode]?.join = some q := by rw [hq]; rfl
  rw [hJoin] at hBM
  dsimp only [encodeBackPair, RetainedProperLoss.backPairFields, OptionalFinPair.encode] at hBM
  have hBF : (s.data[backFstBase H.vertexCount H.arcCount + ancNode]?).map Fin.val = some (q.fst.val + 1) :=
    hBM.1
  have hBS : (s.data[backSndBase H.vertexCount H.arcCount + ancNode]?).map Fin.val = some q.snd.val :=
    hBM.2
  refine ⟨hancPos, hancF, hancDep, q, hq, hBF, hBS, ?_⟩
  have hcUse : c.usePackedWords = c := rfl
  have hmDep : S.depth mNode = F.depthOf mNode := by
    simpa only [S, hcUse] using packedSelector_depth c sRef inv.grounded.layout ⟨mNode, hmF⟩
  have hmAt : S.atDepth mNode mid = ancNode := by
    simpa only [S, hcUse] using packedSelector_atDepth c sRef inv.grounded.layout ⟨mNode, hmF⟩ mid
  have hKey : S.key ancNode = q := by simp [S, selectors, hq]
  have hmidNe : mid ≠ 0 := by omega
  have hLabEq : S.label m_y = mNode := rfl
  have hmidS : mid ≤ S.depth (S.label m_y) := by rw [hLabEq, hmDep]; exact hmidLe
  rw [probe, ite_eq_right hmidNe, ite_eq_left hmidS]
  dsimp only
  rw [hLabEq, hmAt, hKey, scan_ok]
  constructor <;> intro h u hu
  · have hraw := (raw_ok S ancNode q u).mp (h u hu)
    rcases hraw with hmem | hanc
    · rcases hmem with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Or.inl h2)
    · have huF : sRef.labelAt u.val < F.size := inv.grounded.size_eq ▸ inv.labelsLt u
      have hanc' : S.ancestor ancNode (sRef.labelAt u.val) = true := hanc
      have hdec : F.decideAncestor ancNode (sRef.labelAt u.val) = true := by
        have hp := packedSelector_ancestor c sRef inv.grounded.layout ⟨ancNode, hancF⟩ ⟨sRef.labelAt u.val, huF⟩
        simpa only [S, hcUse] using hp.symm.trans hanc'
      exact Or.inr (Or.inr ((ancestor_iff_depth_atDepth inv.records.valid hancF huF).mp hdec))
  · rw [raw_ok]
    rcases h u hu with h1 | h2 | hanc
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h2)
    · right
      have huF : sRef.labelAt u.val < F.size := inv.grounded.size_eq ▸ inv.labelsLt u
      have hdec : F.decideAncestor ancNode (sRef.labelAt u.val) = true :=
        (ancestor_iff_depth_atDepth inv.records.valid hancF huF).mpr hanc
      have hp := packedSelector_ancestor c sRef inv.grounded.layout ⟨ancNode, hancF⟩ ⟨sRef.labelAt u.val, huF⟩
      change S.ancestor ancNode (sRef.labelAt u.val) = true
      rw [← hcUse] at hp
      exact hp.trans hdec

private theorem sweepBSHeader_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hidx : idx < H.vertexCount)
    {pcBS pcAfterBS : Nat}
    (hAfterBnd : pcAfterBS < code.size)
    (hSz : pcBS + (sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS).length < code.size)
    (hpl : Placed code pcBS (sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS))
    (m_y : Vertex H) {lo hi' rowLo : Nat}
    (hLoLt : lo < hi')
    (hHiLe : hi' ≤ F.depthOf (sRef.labelAt m_y.val) + 1)
    (hRLFit : rowLo ≤ H.arcCount)
    (hpc : s.pc = pcBS)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlLo : (s.data[slLoBS]?).map Fin.val = some lo)
    (hSlHi : (s.data[slHiBS]?).map Fin.val = some hi')
    (hSlM : (s.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val))
    (hSlRL : (s.data[slRowLo]?).map Fin.val = some rowLo) :
    if hi' ≤ lo + 1 then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 35 ∧ Steps code input k s t ∧ t.pc = pcAfterBS ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data
    else
      let mid := lo + (hi' - lo) / 2
      let ancNode := F.ancestorAtDepth (sRef.labelAt m_y.val) mid
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 120 + 60 * (OracleContract.L H.vertexCount + 1) ∧
        Steps code input k s t ∧
        t.pc = pcBS + (sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS).length ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rClk).val = rowLo ∧
        (t.data[slMidBS]?).map Fin.val = some mid ∧
        (t.data[slAncNode]?).map Fin.val = some ancNode ∧
        (t.data[slPredJ]?).map Fin.val = some rowLo ∧
        ∀ j, j = slMidBS ∨ j = slAncNode ∨ j = slPredJ ∨ t.data[j]? = s.data[j]? := by
  let n := H.vertexCount
  let m := H.arcCount
  let mNode := sRef.labelAt m_y.val
  let b0a := loadScratch h8 rStack slLoBS ++ loadScratch h8 rRem slHiBS ++ [.add rTmp rStack rOne]
  let b0b : List (Instr bits 15) := [.branchLt rTmp rRem (pcBS + b0a.length + 1) pcAfterBS]
  let b0c : List (Instr bits 15) := [.sub rTmp rRem rStack, .shr1 rTmp rTmp, .add rCmd rStack rTmp]
  let b0d := sweepInitStoreScratch h8 slMidBS rCmd
  let b0e := loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase ++
    [.add rTout rTin rOne, .add rOff rTout rOne]
  let pcDL1 := pcBS + b0a.length + 1 + 3 + b0d.length + b0e.length
  let pcAfterDL1 := pcDL1 + (PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)).toList.length
  let b1 := relocatedSubroutine (PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)) pcDL1 pcAfterDL1
  let b2 :=
    [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] ++
    sweepInitStoreScratch h8 slAncNode rPtr ++
    loadScratch h8 rClk slRowLo ++
    sweepInitStoreScratch h8 slPredJ rClk
  have hLenHdr : (sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS).length =
      b0a.length + 1 + 3 + b0d.length + b0e.length + b1.length + b2.length := by
    unfold sweepBSHeader
    dsimp only [b0a, b0b, b0c, b0d, b0e, b1, b2]
    simp only [relocatedSubroutine, List.length_append, List.length_cons, List.length_nil, List.length_map]
  have hSzTot : pcBS + (b0a.length + 1 + 3 + b0d.length + b0e.length + b1.length + b2.length) < code.size := by
    rw [← hLenHdr]; exact hSz
  have hB0cBnd : pcBS + b0a.length + 1 + 3 < code.size := by omega
  have hB0dBnd : pcBS + b0a.length + 1 + 3 + b0d.length < code.size := by omega
  have hB0eBnd : pcDL1 < code.size := by dsimp only [pcDL1]; omega
  have hDL1Bnd : pcAfterDL1 < code.size := by
    dsimp only [pcAfterDL1, pcDL1]
    have : b1.length = (PaperB.RamForestProgram.DepthSeek.depthLookupProgram
      (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)).toList.length := by
      simp [b1, relocatedSubroutine]
    omega
  have hb0eLen : b0e.length = (loadScratch h8 rPtr slMNode).length +
      (loadScratch h8 rTin slJumpBase).length + 2 := by
    simp only [b0e, List.length_append, List.length_cons, List.length_nil]
  have hB0e1Bnd : pcBS + b0a.length + 1 + 3 + b0d.length + (loadScratch h8 rPtr slMNode).length < code.size := by
    dsimp only [pcDL1] at hB0eBnd; omega
  have hB0e2Bnd : pcBS + b0a.length + 1 + 3 + b0d.length + (loadScratch h8 rPtr slMNode).length +
      (loadScratch h8 rTin slJumpBase).length < code.size := by
    dsimp only [pcDL1] at hB0eBnd; omega
  have hB0eStep0 : pcBS + b0a.length + 1 + 3 + b0d.length +
      (loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase).length + 1 < code.size := by
    dsimp only [pcDL1] at hB0eBnd
    have : (loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase).length + 2 = b0e.length := by
      rw [List.length_append, hb0eLen]
    omega
  have hB0eStep1 : pcBS + b0a.length + 1 + 3 + b0d.length +
      (loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase).length + 2 < code.size := by
    dsimp only [pcDL1] at hB0eBnd
    have : (loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase).length + 2 = b0e.length := by
      rw [List.length_append, hb0eLen]
    omega
  have hb1Len : b1.length = (PaperB.RamForestProgram.DepthSeek.depthLookupProgram
      (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)).toList.length := by
    simp [b1, relocatedSubroutine]
  have hb2Bnd0 : pcAfterDL1 + 1 < code.size := by
    dsimp only [pcAfterDL1, pcDL1]
    have hL : b2.length = 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length +
        (loadScratch h8 rClk slRowLo).length + (sweepInitStoreScratch h8 slPredJ rClk).length := by
      simp only [b2, List.length_append, List.length_cons, List.length_nil]
    omega
  have hb2Bnd1 : pcAfterDL1 + 2 < code.size := by
    have : 2 ≤ b2.length := by simp only [b2, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hb2Bnd2 : pcAfterDL1 + 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length < code.size := by
    have : 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length ≤ b2.length := by
      simp only [b2, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hb2Bnd3 : pcAfterDL1 + 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length +
      (loadScratch h8 rClk slRowLo).length < code.size := by
    have : 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length + (loadScratch h8 rClk slRowLo).length ≤ b2.length := by
      simp only [b2, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hb2Bnd4 : pcAfterDL1 + 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length +
      (loadScratch h8 rClk slRowLo).length + (sweepInitStoreScratch h8 slPredJ rClk).length < code.size := by
    have : 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length + (loadScratch h8 rClk slRowLo).length +
        (sweepInitStoreScratch h8 slPredJ rClk).length ≤ b2.length := by
      simp only [b2, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hb0dLe : b0d.length ≤ 12 := sweepInitStoreScratch_length_le h8 slMidBS rCmd
  have hb0eLe : b0e.length ≤ 26 := by
    have := loadScratch_length_le h8 rPtr slMNode
    have := loadScratch_length_le h8 rTin slJumpBase
    rw [hb0eLen]; omega
  have hb2Le : b2.length ≤ 38 := by
    have := sweepInitStoreScratch_length_le h8 slAncNode rPtr
    have := loadScratch_length_le h8 rClk slRowLo
    have := sweepInitStoreScratch_length_le h8 slPredJ rClk
    simp only [b2, List.length_append, List.length_cons, List.length_nil]; omega
  have hmNodeNext : mNode < sRef.tables.next := inv.labelsLt m_y
  have hmF : mNode < F.size := inv.grounded.size_eq ▸ hmNodeNext
  have hdMLe : F.depthOf mNode ≤ mNode := by
    have hStep : ∀ {F0 : JumpForest}, ValidJumpForest F0 → ∀ u < F0.size, F0.depthOf u ≤ u := by
      intro F0 hF0
      induction hF0 with
      | init =>
        intro u hu
        have hu0 : u = 0 := by simp [JumpForest.init, JumpForest.size] at hu; omega
        subst hu0; decide
      | @appendLeaf F1 p _ hp ih =>
        intro u hu
        by_cases hOld : u < F1.size
        · rw [depthOf_appendLeaf_old F1 p hOld]; exact ih u hOld
        · have hSzApp : (F1.appendLeaf p).size = F1.size + 1 := by
            simp [JumpForest.appendLeaf, JumpForest.size]
          have huEq : u = F1.size := by omega
          subst huEq
          have hpLe := ih p hp
          have hRec : (F1.appendLeaf p).depthOf F1.size = F1.depthOf p + 1 := by
            simp [JumpForest.depthOf, recordAt_appendLeaf_new]; rfl
          omega
    exact hStep inv.records.valid mNode hmF
  have hmLeN : mNode ≤ n := Nat.le_trans (Nat.le_of_lt hmNodeNext) (Nat.le_trans inv.sRefNextLe (by omega))
  have hHiFit : hi' < 2 ^ bits := by
    change hi' ≤ F.depthOf mNode + 1 at hHiLe
    have : hi' ≤ n + 1 := by omega
    have : n + 1 < workCap := by
      unfold rawWorkCap at hWork; omega
    exact Nat.lt_of_lt_of_le (by omega) hw
  have hWorkJump2 : jumpBase n m + 2 < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords,
      rawWorkCap] at hWork ⊢
    omega
  have hSlLoW : slLoBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlHiW : slHiBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlMidW : slMidBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlMW : slMNode < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlJW : slJumpBase < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlAncW : slAncNode < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlRLW : slRowLo < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlPJW : slPredJ < workCap := scratch_lt_workCap30 hWork large (by decide)
  have h0ab : Placed code pcBS (b0a ++ b0b) := by
    have h0 := placed_append_left hpl
    have h1 := placed_append_left h0
    have h2 := placed_append_left h1
    have h3 := placed_append_left h2
    have h4 := placed_append_left h3
    exact h4
  have hpl0a : Placed code pcBS b0a := placed_append_left h0ab
  have hpl0b : Placed code (pcBS + b0a.length) b0b := placed_right_eq h0ab rfl
  have h0a12 : Placed code pcBS (loadScratch h8 rStack slLoBS ++ loadScratch h8 rRem slHiBS) :=
    placed_append_left hpl0a
  have hpl0a1 : Placed code pcBS (loadScratch h8 rStack slLoBS) := placed_append_left h0a12
  have hpl0a2 : Placed code (pcBS + (loadScratch h8 rStack slLoBS).length) (loadScratch h8 rRem slHiBS) :=
    placed_right_eq h0a12 rfl
  have hpl0a3 : Placed code (pcBS + (loadScratch h8 rStack slLoBS ++ loadScratch h8 rRem slHiBS).length)
      ([.add rTmp rStack rOne] : List (Instr bits 15)) :=
    placed_right_eq hpl0a rfl
  have hLen0a : b0a.length = (loadScratch h8 rStack slLoBS).length + (loadScratch h8 rRem slHiBS).length + 1 := by
    simp only [b0a, List.length_append, List.length_cons, List.length_nil]
  have hb0aLe : b0a.length ≤ 25 := by
    have := loadScratch_length_le h8 rStack slLoBS
    have := loadScratch_length_le h8 rRem slHiBS
    omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 rStack slLoBS hSlLoW (by decide)
    hpc hpl0a1 (by omega) ho hSlLo
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ := loadScratch_val_steps h8 rRem slHiBS hSlHiW (by decide)
    pc1 hpl0a2 (by omega) ho1 (by rw [d1]; exact hSlHi)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hz1]
  have hstk2 : (reg s2 rStack).val = lo := by rw [k2 _ (by decide) (by decide), r1]
  have hpc2 : s2.pc = pcBS + (loadScratch h8 rStack slLoBS ++ loadScratch h8 rRem slHiBS).length := by
    rw [pc2, List.length_append, Nat.add_assoc]
  obtain ⟨s3, st3, pc3, r3, k3, d3⟩ := step_add15_at (input := input)
    (placed_fetch hpl0a3 (i := 0) rfl hpc2) (by rw [hpc2]; simp only [List.length_append]; omega)
  have htmp3 : (reg s3 rTmp).val = lo + 1 := by
    rw [r3, WordOps.add_val]; rw [hstk2, ho2]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (by omega) hHiFit)
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide), ho2]
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide), hz2]
  have hstk3 : (reg s3 rStack).val = lo := by rw [k3 _ (by decide), hstk2]
  have hrem3 : (reg s3 rRem).val = hi' := by rw [k3 _ (by decide), r2]
  have hd3 : s3.data = s.data := d3.trans (d2.trans d1)
  have hpc3 : s3.pc = pcBS + b0a.length := by rw [pc3, hpc2, hLen0a]; simp only [List.length_append]; omega
  have hf4 : code[s3.pc]? = some (.branchLt rTmp rRem (pcBS + b0a.length + 1) pcAfterBS) :=
    placed_fetch hpl0b (i := 0) rfl hpc3
  have hPre3 : Steps code input b0a.length s s3 := by
    rw [hLen0a]
    exact (st1.append st2).append (Steps.cons st3 (Steps.zero _))
  by_cases hStop : hi' ≤ lo + 1
  · refine ite_true_branch hStop ?_
    obtain ⟨s4, st4, pc4, k4, d4⟩ := step_branchLt_false hf4 (by rw [hrem3, htmp3]; exact hStop) hAfterBnd
    exact ⟨s4, b0a.length + 1, by omega, hPre3.append (Steps.cons st4 (Steps.zero _)),
      pc4, by rw [k4, hz3], by rw [k4, ho3], d4.trans hd3⟩
  · refine ite_false_branch hStop ?_
    have hGt : lo + 1 < hi' := by omega
    obtain ⟨s4, st4, pc4, k4, d4⟩ := step_branchLt_true hf4 (by rw [htmp3, hrem3]; exact hGt)
      (by rw [hLenHdr] at hSz; omega)
    have ho4 : (reg s4 rOne).val = 1 := by rw [k4, ho3]
    have hz4 : (reg s4 rZero).val = 0 := by rw [k4, hz3]
    have hstk4 : (reg s4 rStack).val = lo := by rw [k4, hstk3]
    have hrem4 : (reg s4 rRem).val = hi' := by rw [k4, hrem3]
    have hd4 : s4.data = s.data := d4.trans hd3
    have h0abcd : Placed code pcBS ((((b0a ++ b0b) ++ b0c) ++ b0d) ++ b0e) := by
      have h0 := placed_append_left hpl
      exact placed_append_left h0
    have h0abc : Placed code pcBS (((b0a ++ b0b) ++ b0c) ++ b0d) := placed_append_left h0abcd
    have h0ab_c : Placed code pcBS ((b0a ++ b0b) ++ b0c) := placed_append_left h0abc
    have hpl0c : Placed code (pcBS + b0a.length + 1) b0c :=
      placed_right_eq h0ab_c (by simp only [b0b, List.length_append, List.length_cons, List.length_nil]; omega)
    have hpl0d : Placed code (pcBS + b0a.length + 1 + 3) b0d :=
      placed_right_eq h0abc (by
        simp only [b0b, b0c, List.length_append, List.length_cons, List.length_nil]; omega)
    have hpl0e : Placed code (pcBS + b0a.length + 1 + 3 + b0d.length) b0e :=
      placed_right_eq h0abcd (by
        simp only [b0b, b0c, List.length_append, List.length_cons, List.length_nil]; omega)
    have hplB1 : Placed code pcDL1 b1 :=
      placed_right_eq (placed_append_left hpl) (by
        dsimp only [pcDL1, b0a, b0b, b0c, b0d, b0e]
        simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    have hplB2 : Placed code pcAfterDL1 b2 :=
      placed_right_eq hpl (by
        dsimp only [pcAfterDL1, pcDL1, b0a, b0b, b0c, b0d, b0e, b1]
        simp only [relocatedSubroutine, List.length_append, List.length_cons, List.length_nil, List.length_map]
        omega)
    -- b0c: sub, shr1, add
    obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_sub15_at (input := input)
      (placed_fetch hpl0c (i := 0) rfl pc4) (by rw [pc4]; omega)
    have htmp5 : (reg s5 rTmp).val = hi' - lo := by
      rw [r5, sub_val_exact (by rw [hstk4, hrem4]; omega), hrem4, hstk4]
    obtain ⟨s6, st6, pc6, r6, k6, d6⟩ := step_shr15_at (input := input)
      (placed_fetch hpl0c (i := 1) rfl (by rw [pc5, pc4])) (by rw [pc5, pc4]; omega)
    have htmp6 : (reg s6 rTmp).val = (hi' - lo) / 2 := by rw [r6, htmp5]
    have hstk6 : (reg s6 rStack).val = lo := by
      rw [k6 _ (by decide), k5 _ (by decide), hstk4]
    obtain ⟨s7, st7, pc7, r7, k7, d7⟩ := step_add15_at (input := input)
      (placed_fetch hpl0c (i := 2) rfl (by rw [pc6, pc5, pc4]))
      (by rw [pc6, pc5, pc4]; omega)
    let mid := lo + (hi' - lo) / 2
    have hmidLt : mid < 2 ^ bits := Nat.lt_of_le_of_lt (by dsimp only [mid]; omega) hHiFit
    have hcmd7 : (reg s7 rCmd).val = mid := by
      rw [r7, WordOps.add_val, hstk6, htmp6]
      exact Nat.mod_eq_of_lt hmidLt
    have ho7 : (reg s7 rOne).val = 1 := by
      rw [k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), ho4]
    have hz7 : (reg s7 rZero).val = 0 := by
      rw [k7 _ (by decide), k6 _ (by decide), k5 _ (by decide), hz4]
    have hd7 : s7.data = s.data := d7.trans (d6.trans (d5.trans hd4))
    have hpc7 : s7.pc = pcBS + b0a.length + 1 + 3 := by rw [pc7, pc6, pc5, pc4]
    -- b0d: storeScratch slMidBS rCmd
    obtain ⟨s8, st8, pc8, hMidW, hFr8, k8⟩ := storeScratch_val_steps h8 slMidBS rCmd (by decide) (by decide)
      hSlMidW hpc7 hpl0d hB0dBnd ho7
    have ho8 : (reg s8 rOne).val = 1 := by rw [k8 _ (by decide), ho7]
    have hz8 : (reg s8 rZero).val = 0 := by rw [k8 _ (by decide), hz7]
    have hcmd8 : (reg s8 rCmd).val = mid := by rw [k8 _ (by decide), hcmd7]
    have hSlMid8 : (s8.data[slMidBS]?).map Fin.val = some mid := by rw [hMidW, hcmd7]
    have hFrS8 : ∀ j, j ≠ slMidBS → s8.data[j]? = s.data[j]? := fun j hj => by rw [hFr8 j hj, hd7]
    -- b0e: load mNode, load jumpBase, add rTout, add rOff
    have hpl0e1 : Placed code (pcBS + b0a.length + 1 + 3 + b0d.length) (loadScratch h8 rPtr slMNode) :=
      placed_append_left (placed_append_left hpl0e)
    have hpl0e2 : Placed code (pcBS + b0a.length + 1 + 3 + b0d.length + (loadScratch h8 rPtr slMNode).length)
        (loadScratch h8 rTin slJumpBase) :=
      placed_right_eq (placed_append_left hpl0e) rfl
    have hpl0e3 : Placed code (pcBS + b0a.length + 1 + 3 + b0d.length +
        (loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase).length)
        ([.add rTout rTin rOne, .add rOff rTout rOne] : List (Instr bits 15)) :=
      placed_right_eq hpl0e rfl
    obtain ⟨s9, st9, pc9, r9, d9, k9⟩ := loadScratch_val_steps h8 rPtr slMNode hSlMW (by decide)
      pc8 hpl0e1 hB0e1Bnd ho8 (by rw [hFrS8 _ (by decide)]; exact hSlM)
    have ho9 : (reg s9 rOne).val = 1 := by rw [k9 _ (by decide) (by decide), ho8]
    have hz9 : (reg s9 rZero).val = 0 := by rw [k9 _ (by decide) (by decide), hz8]
    have hcmd9 : (reg s9 rCmd).val = mid := by rw [k9 _ (by decide) (by decide), hcmd8]
    have hptr9 : (reg s9 rPtr).val = mNode := r9
    obtain ⟨s10, st10, pc10, r10, d10, k10⟩ := loadScratch_val_steps h8 rTin slJumpBase hSlJW (by decide)
      pc9 hpl0e2 hB0e2Bnd ho9
      (by rw [d9, hFrS8 _ (by decide)]; exact inv.slJumpVal)
    have ho10 : (reg s10 rOne).val = 1 := by rw [k10 _ (by decide) (by decide), ho9]
    have hz10 : (reg s10 rZero).val = 0 := by rw [k10 _ (by decide) (by decide), hz9]
    have hcmd10 : (reg s10 rCmd).val = mid := by rw [k10 _ (by decide) (by decide), hcmd9]
    have hptr10 : (reg s10 rPtr).val = mNode := by rw [k10 _ (by decide) (by decide), hptr9]
    have htin10 : (reg s10 rTin).val = jumpBase n m := r10
    have hpc10 : s10.pc = pcBS + b0a.length + 1 + 3 + b0d.length +
        (loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase).length := by
      have hb0dLen' : (sweepInitStoreScratch h8 slMidBS rCmd).length = b0d.length := rfl
      rw [pc10, List.length_append, hb0dLen']; exact Nat.add_assoc _ _ _
    obtain ⟨s11, st11, pc11, r11, k11, d11⟩ := step_add15_at (input := input)
      (placed_fetch hpl0e3 (i := 0) rfl hpc10) (by rw [hpc10]; exact hB0eStep0)
    have htout11 : (reg s11 rTout).val = jumpBase n m + 1 := by
      rw [r11, WordOps.add_val, htin10, ho10]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
    obtain ⟨s12, st12, pc12, r12, k12, d12⟩ := step_add15_at (input := input)
      (placed_fetch hpl0e3 (i := 1) rfl (by rw [pc11, hpc10]))
      (by rw [pc11, hpc10]; exact hB0eStep1)
    have hoff12 : (reg s12 rOff).val = jumpBase n m + 2 := by
      rw [r12, WordOps.add_val, htout11, k11 _ (by decide), ho10]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
    have htin12 : (reg s12 rTin).val = jumpBase n m := by
      rw [k12 _ (by decide), k11 _ (by decide), htin10]
    have htout12 : (reg s12 rTout).val = jumpBase n m + 1 := by
      rw [k12 _ (by decide), htout11]
    have hcmd12 : (reg s12 rCmd).val = mid := by
      rw [k12 _ (by decide), k11 _ (by decide), hcmd10]
    have hz12 : (reg s12 rZero).val = 0 := by
      rw [k12 _ (by decide), k11 _ (by decide), hz10]
    have hptr12 : (reg s12 rPtr).val = mNode := by
      rw [k12 _ (by decide), k11 _ (by decide), hptr10]
    have hd12 : s12.data = s8.data := d12.trans (d11.trans (d10.trans d9))
    have hpc12 : s12.pc = pcDL1 := by
      have hAssoc : ∀ a b : Nat, a + b + 1 + 1 = a + (b + 2) := fun a b => by omega
      rw [pc12, pc11, hpc10]; dsimp only [pcDL1]; rw [hb0eLen, List.length_append]
      exact hAssoc _ _
    -- b1: depthLookup
    have hRec12 : PaperB.RamForestProgram.DepthSeek.Records (jumpBase n m) F s12.data := by
      have hf := inv.records
      have hjb := scratch_lt_orderBase (n := n) (m := m) (sl := slMidBS) large (by decide)
      have hOrd : orderBase n m ≤ jumpBase n m := by
        simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
      have hEqJ : ∀ j, jumpBase n m ≤ j → s12.data[j]? = s.data[j]? := fun j hj => by
        rw [hd12]; exact hFrS8 j (by omega)
      refine ⟨hf.valid, ?_, fun u hu => ?_, fun u hu => ?_, fun u hu => ?_⟩
      · rw [s12.data_size, ← s.data_size]; exact hf.fit
      · rw [hEqJ _ (by omega)]; exact hf.parent u hu
      · rw [hEqJ _ (by omega)]; exact hf.depth u hu
      · rw [hEqJ _ (by omega)]; exact hf.jump u hu
    have hFIns : F.numInserted ≤ n := by
      have hSzF : F.size = sRef.tables.next := inv.grounded.size_eq
      have hSRefN : sRef.tables.next ≤ n := Nat.le_trans inv.sRefNextLe (by omega)
      change F.records.length - 1 ≤ n
      change F.records.length = sRef.tables.next at hSzF
      omega
    obtain ⟨s13, kDL, hkDL, stDL, pc13, r13, hd13⟩ := relocate_depthLookup input s12 hpc12 hDL1Bnd
      hplB1 ⟨htin12, htout12, hoff12, hcmd12, hz12⟩ hRec12 hmF hptr12 hFIns
      (vertexCount_add2_le_two_pow_L_succ n)
    -- b2: imm rZero 0, imm rOne 1, store slAncNode rPtr, load rClk slRowLo, store slPredJ rClk
    let ancNode := F.ancestorAtDepth mNode mid
    have hanc13 : (reg s13 rPtr).val = ancNode := r13
    have hd13' : s13.data = s8.data := hd13.trans hd12
    have hb2_01 : Placed code pcAfterDL1 ([.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] : List (Instr bits 15)) :=
      placed_append_left (placed_append_left (placed_append_left hplB2))
    have hb2_2 : Placed code (pcAfterDL1 + 2) (sweepInitStoreScratch h8 slAncNode rPtr) :=
      placed_right_eq (placed_append_left (placed_append_left hplB2)) rfl
    have hb2_3 : Placed code (pcAfterDL1 + 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length)
        (loadScratch h8 rClk slRowLo) :=
      placed_right_eq (placed_append_left hplB2) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    have hb2_4 : Placed code (pcAfterDL1 + 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length +
        (loadScratch h8 rClk slRowLo).length) (sweepInitStoreScratch h8 slPredJ rClk) :=
      placed_right_eq hplB2 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    have hb2Len : b2.length = 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length +
        (loadScratch h8 rClk slRowLo).length + (sweepInitStoreScratch h8 slPredJ rClk).length := by
      simp only [b2, List.length_append, List.length_cons, List.length_nil]
    obtain ⟨s14, st14, pc14, r14, k14, d14⟩ := step_imm_at (input := input)
      (placed_fetch hb2_01 (i := 0) rfl pc13) (by rw [pc13]; exact hb2Bnd0)
    obtain ⟨s15, st15, pc15, r15, k15, d15⟩ := step_imm_at (input := input)
      (placed_fetch hb2_01 (i := 1) rfl (by rw [pc14, pc13]))
      (by rw [pc14, pc13]; exact hb2Bnd1)
    have ho15 : (reg s15 rOne).val = 1 := congrArg Fin.val r15
    have hz15 : (reg s15 rZero).val = 0 := by rw [k15 _ (by decide), r14]
    have hptr15 : (reg s15 rPtr).val = ancNode := by
      rw [k15 _ (by decide), k14 _ (by decide), hanc13]
    have hd15 : s15.data = s8.data := d15.trans (d14.trans hd13')
    obtain ⟨s16, st16, pc16, hAncW, hFr16, k16⟩ := storeScratch_val_steps h8 slAncNode rPtr (by decide) (by decide)
      hSlAncW (by rw [pc15, pc14, pc13]) hb2_2 hb2Bnd2 ho15
    have ho16 : (reg s16 rOne).val = 1 := by rw [k16 _ (by decide), ho15]
    have hz16 : (reg s16 rZero).val = 0 := by rw [k16 _ (by decide), hz15]
    have hSlRL16 : (s16.data[slRowLo]?).map Fin.val = some rowLo := by
      rw [hFr16 _ (by decide), hd15, hFrS8 _ (by decide)]; exact hSlRL
    obtain ⟨s17, st17, pc17, r17, d17, k17⟩ := loadScratch_val_steps h8 rClk slRowLo hSlRLW (by decide)
      pc16 hb2_3 hb2Bnd3 ho16 hSlRL16
    have ho17 : (reg s17 rOne).val = 1 := by rw [k17 _ (by decide) (by decide), ho16]
    have hz17 : (reg s17 rZero).val = 0 := by rw [k17 _ (by decide) (by decide), hz16]
    have hclk17 : (reg s17 rClk).val = rowLo := r17
    obtain ⟨s18, st18, pc18, hPJW, hFr18, k18⟩ := storeScratch_val_steps h8 slPredJ rClk (by decide) (by decide)
      hSlPJW pc17 hb2_4 hb2Bnd4 ho17
    have hTotalSteps :
        Steps code input (b0a.length + 1 + 3 + b0d.length + b0e.length + kDL + b2.length) s s18 := by
      have h12 : Steps code input (b0a.length + 1) s s4 := hPre3.append (.cons st4 (.zero _))
      have h57 : Steps code input 3 s4 s7 := .cons st5 (.cons st6 (.cons st7 (.zero _)))
      have h8 : Steps code input b0d.length s7 s8 := st8
      have h912 : Steps code input b0e.length s8 s12 := by
        rw [hb0eLen]; exact (st9.append st10).append (.cons st11 (.cons st12 (.zero _)))
      have hb2St : Steps code input b2.length s13 s18 := by
        rw [hb2Len]
        exact ((Steps.cons st14 (.cons st15 (.zero _))).append st16).append (st17.append st18)
      exact ((((h12.append h57).append h8).append h912).append stDL).append hb2St
    have hkTotal : b0a.length + 1 + 3 + b0d.length + b0e.length + kDL + b2.length ≤
        120 + 60 * (OracleContract.L H.vertexCount + 1) := by
      have h1 : b0a.length + 1 + 3 + b0d.length + b0e.length + kDL + b2.length ≤
          25 + 1 + 3 + 12 + 26 + (60 * (OracleContract.L H.vertexCount + 1) + 7) + 38 := by
        refine Nat.add_le_add ?_ hb2Le
        refine Nat.add_le_add ?_ hkDL
        refine Nat.add_le_add ?_ hb0eLe
        refine Nat.add_le_add ?_ hb0dLe
        refine Nat.add_le_add ?_ (Nat.le_refl 3)
        exact Nat.add_le_add hb0aLe (Nat.le_refl 1)
      have hNum : ∀ x : Nat, 25 + 1 + 3 + 12 + 26 + (60 * x + 7) + 38 ≤ 120 + 60 * x :=
        fun x => by omega
      exact Nat.le_trans h1 (hNum (OracleContract.L H.vertexCount + 1))
    refine ⟨s18, b0a.length + 1 + 3 + b0d.length + b0e.length + kDL + b2.length, hkTotal,
      hTotalSteps, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [pc18, hLenHdr, hb2Len]; dsimp only [pcAfterDL1, pcDL1]; simp only [Nat.add_assoc, hb1Len]
    · rw [k18 _ (by decide), hz17]
    · rw [k18 _ (by decide), ho17]
    · rw [k18 _ (by decide), hclk17]
    · rw [hFr18 _ (by decide), d17, hFr16 _ (by decide), hd15]; exact hSlMid8
    · rw [hFr18 _ (by decide), d17, hAncW, hptr15]
    · rw [hPJW, hclk17]
    · intro j
      by_cases hPJ : j = slPredJ
      · exact Or.inr (Or.inr (Or.inl hPJ))
      by_cases hAnc : j = slAncNode
      · exact Or.inr (Or.inl hAnc)
      by_cases hMid : j = slMidBS
      · exact Or.inl hMid
      exact Or.inr (Or.inr (Or.inr (by rw [hFr18 j hPJ, d17, hFr16 j hAnc, hd15, hFrS8 j hMid])))

private theorem bsProbePrNext_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {pcNextU pcProbe j : Nat}
    (hSlPJW : slPredJ < workCap)
    (hj1Lt : j + 1 < 2 ^ bits)
    (hplNext : Placed code pcNextU (bsProbePrNext h8 pcProbe))
    (hSzNext : pcNextU + (bsProbePrNext h8 pcProbe).length < code.size)
    (hProbeBnd : pcProbe < code.size)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = pcNextU)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlPJ : (s.data[slPredJ]?).map Fin.val = some j) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (bsProbePrNext h8 pcProbe).length s t ∧
      t.pc = pcProbe ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[slPredJ]?).map Fin.val = some (j + 1) ∧
      ∀ w, w = slPredJ ∨ t.data[w]? = s.data[w]? := by
  have hpl123 : Placed code pcNextU
      ((loadScratch h8 rClk slPredJ ++ [.add rClk rClk rOne]) ++ sweepInitStoreScratch h8 slPredJ rClk) :=
    placed_append_left hplNext
  have hpl12 : Placed code pcNextU (loadScratch h8 rClk slPredJ ++ [.add rClk rClk rOne]) :=
    placed_append_left hpl123
  have hplN1 : Placed code pcNextU (loadScratch h8 rClk slPredJ) := placed_append_left hpl12
  have hplN2 : Placed code (pcNextU + (loadScratch h8 rClk slPredJ).length)
      ([.add rClk rClk rOne] : List (Instr bits 15)) := placed_right_eq hpl12 rfl
  have hplN3 : Placed code (pcNextU + (loadScratch h8 rClk slPredJ).length + 1)
      (sweepInitStoreScratch h8 slPredJ rClk) :=
    placed_right_eq hpl123 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hplN4 : Placed code (pcNextU + (loadScratch h8 rClk slPredJ).length + 1 +
      (sweepInitStoreScratch h8 slPredJ rClk).length) ([.goto pcProbe] : List (Instr bits 15)) :=
    placed_right_eq hplNext (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hLen : (bsProbePrNext h8 pcProbe).length =
      (loadScratch h8 rClk slPredJ).length + 1 + (sweepInitStoreScratch h8 slPredJ rClk).length + 1 := by
    simp only [bsProbePrNext, List.length_append, List.length_cons, List.length_nil]
  obtain ⟨t1, stt1, pct1, rt1, dt1, kt1⟩ := loadScratch_val_steps h8 rClk slPredJ hSlPJW (by decide)
    hpc hplN1 (by omega) ho hSlPJ
  have hot1 : (reg t1 rOne).val = 1 := by rw [kt1 _ (by decide) (by decide), ho]
  have hzt1 : (reg t1 rZero).val = 0 := by rw [kt1 _ (by decide) (by decide), hz]
  obtain ⟨t2, stt2, pct2, rt2, kt2, dt2⟩ := step_add15_at (input := input)
    (placed_fetch hplN2 (i := 0) rfl pct1) (by rw [pct1]; omega)
  have hclkt2 : (reg t2 rClk).val = j + 1 := by
    rw [rt2, WordOps.add_val, rt1, hot1]; exact Nat.mod_eq_of_lt hj1Lt
  have hot2 : (reg t2 rOne).val = 1 := by rw [kt2 _ (by decide), hot1]
  have hzt2 : (reg t2 rZero).val = 0 := by rw [kt2 _ (by decide), hzt1]
  obtain ⟨t3, stt3, pct3, hPJ3, hFr3, kt3⟩ := storeScratch_val_steps h8 slPredJ rClk (by decide) (by decide)
    hSlPJW (by rw [pct2, pct1]) hplN3 (by omega) hot2
  have hot3 : (reg t3 rOne).val = 1 := by rw [kt3 _ (by decide), hot2]
  have hzt3 : (reg t3 rZero).val = 0 := by rw [kt3 _ (by decide), hzt2]
  have hgt4 := step_goto_at (input := input) (placed_fetch hplN4 (i := 0) rfl pct3) hProbeBnd
  refine ⟨{ t3 with pc := pcProbe }, ?_, rfl, hzt3, hot3, ?_, ?_⟩
  · rw [hLen]; exact ((stt1.append (.cons stt2 (.zero _))).append stt3).append (.cons hgt4 (.zero _))
  · change (t3.data[slPredJ]?).map Fin.val = some (j + 1); rw [hPJ3, hclkt2]
  · intro w
    by_cases hw' : w = slPredJ
    · exact Or.inl hw'
    · exact Or.inr (by change t3.data[w]? = s.data[w]?; rw [hFr3 w hw', dt2, dt1])

private theorem bsProbePr23_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m j ancNode qFst uVal : Nat}
    (hSlPBW : slPredBuf < workCap) (hSlAncW : slAncNode < workCap) (hSlBFW : slBackFst < workCap)
    (hPBAddrW : predBufBase n m + j < workCap)
    (hBFAddrW : backFstBase n m + ancNode < workCap)
    (hu1Lt : uVal + 1 < 2 ^ bits)
    {pc3 : Nat} {s3 : State (layout bits inputCap workCap hi hw)}
    (hpl2 : Placed code pc3 (bsProbePr2 h8))
    (hpl3 : Placed code (pc3 + (bsProbePr2 h8).length) (bsProbePr3 h8))
    (hPr2Bnd : pc3 + (bsProbePr2 h8).length < code.size)
    (hPr3Bnd : pc3 + (bsProbePr2 h8).length + (bsProbePr3 h8).length < code.size)
    (hpc3 : s3.pc = pc3) (hz3 : (reg s3 rZero).val = 0) (ho3 : (reg s3 rOne).val = 1)
    (hclk3 : (reg s3 rClk).val = j)
    (hSlPB : (s3.data[slPredBuf]?).map Fin.val = some (predBufBase n m))
    (hSlAnc : (s3.data[slAncNode]?).map Fin.val = some ancNode)
    (hSlBF : (s3.data[slBackFst]?).map Fin.val = some (backFstBase n m))
    (hPBu : (s3.data[predBufBase n m + j]?).map Fin.val = some uVal)
    (hBFq : (s3.data[backFstBase n m + ancNode]?).map Fin.val = some (qFst + 1)) :
    ∃ s11 : State (layout bits inputCap workCap hi hw),
      Steps code input ((bsProbePr2 h8).length + (bsProbePr3 h8).length) s3 s11 ∧
      s11.pc = pc3 + (bsProbePr2 h8).length + (bsProbePr3 h8).length ∧
      (reg s11 rZero).val = 0 ∧ (reg s11 rOne).val = 1 ∧
      (reg s11 rStack).val = uVal ∧ (reg s11 rChild).val = ancNode ∧
      (reg s11 rTmp).val = uVal + 1 ∧ (reg s11 rVal).val = qFst + 1 ∧
      s11.data = s3.data := by
  have hpr2Len : (bsProbePr2 h8).length =
      (loadScratch h8 rTmp slPredBuf).length + 2 + (loadScratch h8 rChild slAncNode).length := by
    simp only [bsProbePr2, List.length_append, List.length_cons, List.length_nil]
  have hpr3Len : (bsProbePr3 h8).length = (loadScratch h8 rTmp slBackFst).length + 3 := by
    simp only [bsProbePr3, List.length_append, List.length_cons, List.length_nil]
  have h2ab : Placed code pc3
      (loadScratch h8 rTmp slPredBuf ++ [.add rTmp rTmp rClk, .loadData rStack rTmp]) := placed_append_left hpl2
  have hpl2a : Placed code pc3 (loadScratch h8 rTmp slPredBuf) := placed_append_left h2ab
  have hpl2b : Placed code (pc3 + (loadScratch h8 rTmp slPredBuf).length)
      ([.add rTmp rTmp rClk, .loadData rStack rTmp] : List (Instr bits 15)) := placed_right_eq h2ab rfl
  have hpl2c : Placed code (pc3 + (loadScratch h8 rTmp slPredBuf).length + 2)
      (loadScratch h8 rChild slAncNode) :=
    placed_right_eq hpl2 (by simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc])
  obtain ⟨s4, st4, pc4, r4, d4, k4⟩ := loadScratch_val_steps h8 (input := input) rTmp slPredBuf hSlPBW (by decide)
    hpc3 hpl2a (by omega) ho3 hSlPB
  have ho4 : (reg s4 rOne).val = 1 := by rw [k4 _ (by decide) (by decide), ho3]
  have hz4 : (reg s4 rZero).val = 0 := by rw [k4 _ (by decide) (by decide), hz3]
  have hclk4 : (reg s4 rClk).val = j := by rw [k4 _ (by decide) (by decide), hclk3]
  obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_add15_at (input := input) (s := s4)
    (placed_fetch hpl2b (i := 0) rfl pc4) (by rw [pc4]; omega)
  have htmp5 : (reg s5 rTmp).val = predBufBase n m + j := by
    rw [r5, WordOps.add_val, r4, hclk4]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hPBAddrW hw)
  obtain ⟨s6, st6, pc6, r6, k6, d6⟩ := step_loadData_reg (s := s5)
    (placed_fetch hpl2b (i := 1) rfl (by rw [pc5, pc4]))
    (by rw [pc5, pc4]; omega) (by rw [htmp5]; exact hPBAddrW) (by rw [htmp5, d5, d4]; exact hPBu)
  have ho6 : (reg s6 rOne).val = 1 := by rw [k6 _ (by decide), k5 _ (by decide), ho4]
  have hz6 : (reg s6 rZero).val = 0 := by rw [k6 _ (by decide), k5 _ (by decide), hz4]
  have hstk6 : (reg s6 rStack).val = uVal := r6
  have hd6 : s6.data = s3.data := d6.trans (d5.trans d4)
  obtain ⟨s7, st7, pc7, r7, d7, k7⟩ := loadScratch_val_steps h8 (input := input) rChild slAncNode hSlAncW (by decide)
    (by rw [pc6, pc5, pc4]) hpl2c (by omega) ho6 (by rw [hd6]; exact hSlAnc)
  have ho7 : (reg s7 rOne).val = 1 := by rw [k7 _ (by decide) (by decide), ho6]
  have hz7 : (reg s7 rZero).val = 0 := by rw [k7 _ (by decide) (by decide), hz6]
  have hstk7 : (reg s7 rStack).val = uVal := by rw [k7 _ (by decide) (by decide), hstk6]
  have hch7 : (reg s7 rChild).val = ancNode := r7
  have hd7 : s7.data = s3.data := d7.trans hd6
  have hpc7 : s7.pc = pc3 + (bsProbePr2 h8).length := by rw [pc7, hpr2Len]; omega
  have h3ab : Placed code (pc3 + (bsProbePr2 h8).length)
      (loadScratch h8 rTmp slBackFst ++ [.add rTmp rTmp rChild, .loadData rVal rTmp]) := by
    have h' : bsProbePr3 h8 = (loadScratch h8 rTmp slBackFst ++ [.add rTmp rTmp rChild, .loadData rVal rTmp]) ++
        [.add rTmp rStack rOne] := by
      simp only [bsProbePr3, List.append_assoc, List.cons_append, List.nil_append]
    rw [h'] at hpl3; exact placed_append_left hpl3
  have hpl3a : Placed code (pc3 + (bsProbePr2 h8).length) (loadScratch h8 rTmp slBackFst) := placed_append_left h3ab
  have hpl3b : Placed code (pc3 + (bsProbePr2 h8).length + (loadScratch h8 rTmp slBackFst).length)
      ([.add rTmp rTmp rChild, .loadData rVal rTmp, .add rTmp rStack rOne] : List (Instr bits 15)) :=
    placed_right_eq hpl3 rfl
  obtain ⟨s8, st8, pc8, r8, d8, k8⟩ := loadScratch_val_steps h8 (input := input) rTmp slBackFst hSlBFW (by decide)
    hpc7 hpl3a (by omega) ho7 (by rw [hd7]; exact hSlBF)
  have ho8 : (reg s8 rOne).val = 1 := by rw [k8 _ (by decide) (by decide), ho7]
  have hz8 : (reg s8 rZero).val = 0 := by rw [k8 _ (by decide) (by decide), hz7]
  have hstk8 : (reg s8 rStack).val = uVal := by rw [k8 _ (by decide) (by decide), hstk7]
  have hch8 : (reg s8 rChild).val = ancNode := by rw [k8 _ (by decide) (by decide), hch7]
  obtain ⟨s9, st9, pc9, r9, k9, d9⟩ := step_add15_at (input := input) (s := s8)
    (placed_fetch hpl3b (i := 0) rfl (s := s8) pc8) (by rw [pc8]; omega)
  have htmp9 : (reg s9 rTmp).val = backFstBase n m + ancNode := by
    rw [r9, WordOps.add_val, r8, hch8]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hBFAddrW hw)
  have hpc9' : s9.pc = pc3 + (bsProbePr2 h8).length + (loadScratch h8 rTmp slBackFst).length + 1 := by rw [pc9, pc8]
  obtain ⟨s10, st10, pc10, r10, k10, d10⟩ := step_loadData_reg (s := s9)
    (placed_fetch hpl3b (i := 1) rfl (s := s9) hpc9')
    (by rw [hpc9']; omega) (by rw [htmp9]; exact hBFAddrW) (by rw [htmp9, d9, d8, hd7]; exact hBFq)
  have hstk10 : (reg s10 rStack).val = uVal := by rw [k10 _ (by decide), k9 _ (by decide), hstk8]
  have ho10 : (reg s10 rOne).val = 1 := by rw [k10 _ (by decide), k9 _ (by decide), ho8]
  have hz10 : (reg s10 rZero).val = 0 := by rw [k10 _ (by decide), k9 _ (by decide), hz8]
  have hch10 : (reg s10 rChild).val = ancNode := by rw [k10 _ (by decide), k9 _ (by decide), hch8]
  have hpc10' : s10.pc = pc3 + (bsProbePr2 h8).length + (loadScratch h8 rTmp slBackFst).length + 2 := by rw [pc10, hpc9']
  obtain ⟨s11, st11, pc11, r11, k11, d11⟩ := step_add15_at (input := input) (s := s10)
    (placed_fetch hpl3b (i := 2) rfl (s := s10) hpc10') (by rw [hpc10']; omega)
  have htmp11 : (reg s11 rTmp).val = uVal + 1 := by
    rw [r11, WordOps.add_val, hstk10, ho10]; exact Nat.mod_eq_of_lt hu1Lt
  have hval11 : (reg s11 rVal).val = qFst + 1 := by rw [k11 _ (by decide), r10]
  have ho11 : (reg s11 rOne).val = 1 := by rw [k11 _ (by decide), ho10]
  have hz11 : (reg s11 rZero).val = 0 := by rw [k11 _ (by decide), hz10]
  have hstk11 : (reg s11 rStack).val = uVal := by rw [k11 _ (by decide), hstk10]
  have hch11 : (reg s11 rChild).val = ancNode := by rw [k11 _ (by decide), hch10]
  have hd11 : s11.data = s3.data := d11.trans (d10.trans (d9.trans (d8.trans hd7)))
  have hpc11 : s11.pc = pc3 + (bsProbePr2 h8).length + (bsProbePr3 h8).length := by rw [pc11, hpc10', hpr3Len]; omega
  have hst23 : Steps code input ((bsProbePr2 h8).length + (bsProbePr3 h8).length) s3 s11 := by
    have hst2 : Steps code input (bsProbePr2 h8).length s3 s7 := by
      rw [hpr2Len]; exact (st4.append (.cons st5 (.cons st6 (.zero _)))).append st7
    have hst3 : Steps code input (bsProbePr3 h8).length s7 s11 := by
      rw [hpr3Len]; exact st8.append (.cons st9 (.cons st10 (.cons st11 (.zero _))))
    exact hst2.append hst3
  exact ⟨s11, hst23, hpc11, hz11, ho11, hstk11, hch11, htmp11, hval11, hd11⟩

private theorem bsProbePr7_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {F : JumpForest}
    {n m ancNode uVal uNode : Nat}
    (hSlLabW : slLabels < workCap) (hSlJW : slJumpBase < workCap)
    (hLabAddrW : labelsBase n m + uVal < workCap)
    (hAncJmpW : jumpBase n m + 3 * ancNode + 1 < workCap)
    (hUJmpW : jumpBase n m + 3 * uNode + 1 < workCap)
    (_hancF : ancNode < F.size) (_huF : uNode < F.size)
    {pcChkAnc : Nat} {s16 : State (layout bits inputCap workCap hi hw)}
    (hpl7 : Placed code pcChkAnc (bsProbePr7 h8))
    (hPr7Bnd : pcChkAnc + (bsProbePr7 h8).length < code.size)
    (hpc16 : s16.pc = pcChkAnc)
    (hz16 : (reg s16 rZero).val = 0) (ho16 : (reg s16 rOne).val = 1)
    (hstk16 : (reg s16 rStack).val = uVal) (hch16 : (reg s16 rChild).val = ancNode)
    (hSlLab : (s16.data[slLabels]?).map Fin.val = some (labelsBase n m))
    (hSlJ : (s16.data[slJumpBase]?).map Fin.val = some (jumpBase n m))
    (hLabU : (s16.data[labelsBase n m + uVal]?).map Fin.val = some uNode)
    (hDepAnc : (s16.data[jumpBase n m + 1 + 3 * ancNode]?).map Fin.val = some (F.depthOf ancNode))
    (hDepU : (s16.data[jumpBase n m + 1 + 3 * uNode]?).map Fin.val = some (F.depthOf uNode)) :
    ∃ s30 : State (layout bits inputCap workCap hi hw),
      Steps code input (bsProbePr7 h8).length s16 s30 ∧
      s30.pc = pcChkAnc + (bsProbePr7 h8).length ∧
      (reg s30 rZero).val = 0 ∧ (reg s30 rOne).val = 1 ∧
      (reg s30 rTin).val = jumpBase n m ∧ (reg s30 rPtr).val = uNode ∧
      (reg s30 rChild).val = ancNode ∧
      (reg s30 rCmd).val = F.depthOf ancNode ∧ (reg s30 rVal).val = F.depthOf uNode ∧
      s30.data = s16.data := by
  let p7b : List (Instr bits 15) := [.add rTmp rTmp rStack, .loadData rPtr rTmp]
  let p7d : List (Instr bits 15) :=
    [ .add rTmp rTin rChild, .add rTmp rTmp rChild, .add rTmp rTmp rChild, .add rTmp rTmp rOne,
      .loadData rCmd rTmp,
      .add rTmp rTin rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
      .loadData rVal rTmp ]
  have h7abc : Placed code pcChkAnc
      ((loadScratch h8 rTmp slLabels ++ p7b) ++ loadScratch h8 rTin slJumpBase) :=
    placed_append_left hpl7
  have h7ab : Placed code pcChkAnc (loadScratch h8 rTmp slLabels ++ p7b) := placed_append_left h7abc
  have hpl7a : Placed code pcChkAnc (loadScratch h8 rTmp slLabels) := placed_append_left h7ab
  have hpl7b' : Placed code (pcChkAnc + (loadScratch h8 rTmp slLabels).length) p7b := placed_right_eq h7ab rfl
  have hpl7c : Placed code (pcChkAnc + (loadScratch h8 rTmp slLabels).length + 2)
      (loadScratch h8 rTin slJumpBase) :=
    placed_right_eq h7abc (by simp only [p7b, List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl7d : Placed code
      (pcChkAnc + (loadScratch h8 rTmp slLabels).length + 2 + (loadScratch h8 rTin slJumpBase).length) p7d :=
    placed_right_eq hpl7 (by
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]; rfl)
  have hpr7Len : (bsProbePr7 h8).length =
      (loadScratch h8 rTmp slLabels).length + 2 + (loadScratch h8 rTin slJumpBase).length + 10 := by
    simp only [bsProbePr7, List.length_append, List.length_cons, List.length_nil]
  rw [hpr7Len] at hPr7Bnd
  obtain ⟨s17, st17, pc17, r17, d17, k17⟩ := loadScratch_val_steps h8 (input := input) rTmp slLabels hSlLabW
    (by decide) hpc16 hpl7a (by omega) ho16 hSlLab
  have ho17 : (reg s17 rOne).val = 1 := by rw [k17 _ (by decide) (by decide), ho16]
  have hz17 : (reg s17 rZero).val = 0 := by rw [k17 _ (by decide) (by decide), hz16]
  have hstk17 : (reg s17 rStack).val = uVal := by rw [k17 _ (by decide) (by decide), hstk16]
  have hch17 : (reg s17 rChild).val = ancNode := by rw [k17 _ (by decide) (by decide), hch16]
  obtain ⟨s18, st18, pc18, r18, k18, d18⟩ := step_add15_at (input := input) (s := s17)
    (placed_fetch hpl7b' (i := 0) rfl pc17) (by rw [pc17]; omega)
  have htmp18 : (reg s18 rTmp).val = labelsBase n m + uVal := by
    rw [r18, WordOps.add_val, r17, hstk17]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLabAddrW hw)
  obtain ⟨s19, st19, pc19, r19, k19, d19⟩ := step_loadData_reg (s := s18)
    (placed_fetch hpl7b' (i := 1) rfl (by rw [pc18, pc17]))
    (by rw [pc18, pc17]; omega) (by rw [htmp18]; exact hLabAddrW) (by rw [htmp18, d18, d17]; exact hLabU)
  have hptr19 : (reg s19 rPtr).val = uNode := r19
  have ho19 : (reg s19 rOne).val = 1 := by rw [k19 _ (by decide), k18 _ (by decide), ho17]
  have hz19 : (reg s19 rZero).val = 0 := by rw [k19 _ (by decide), k18 _ (by decide), hz17]
  have hch19 : (reg s19 rChild).val = ancNode := by rw [k19 _ (by decide), k18 _ (by decide), hch17]
  obtain ⟨s20, st20, pc20, r20, d20, k20⟩ := loadScratch_val_steps h8 (input := input) rTin slJumpBase hSlJW
    (by decide) (by rw [pc19, pc18, pc17]) hpl7c (by omega) ho19 (by rw [d19, d18, d17]; exact hSlJ)
  have ho20 : (reg s20 rOne).val = 1 := by rw [k20 _ (by decide) (by decide), ho19]
  have hz20 : (reg s20 rZero).val = 0 := by rw [k20 _ (by decide) (by decide), hz19]
  have hch20 : (reg s20 rChild).val = ancNode := by rw [k20 _ (by decide) (by decide), hch19]
  have hptr20 : (reg s20 rPtr).val = uNode := by rw [k20 _ (by decide) (by decide), hptr19]
  have htin20 : (reg s20 rTin).val = jumpBase n m := r20
  have hd20 : s20.data = s16.data := d20.trans (d19.trans (d18.trans d17))
  obtain ⟨s21, st21, pc21, r21, k21, d21⟩ := step_add15_at (input := input) (s := s20)
    (placed_fetch hpl7d (i := 0) rfl pc20) (by rw [pc20]; omega)
  have htmp21 : (reg s21 rTmp).val = jumpBase n m + ancNode := by
    rw [r21, WordOps.add_val, htin20, hch20]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
  obtain ⟨s22, st22, pc22, r22, k22, d22⟩ := step_add15_at (input := input) (s := s21)
    (placed_fetch hpl7d (i := 1) rfl (by rw [pc21, pc20])) (by rw [pc21, pc20]; omega)
  have htmp22 : (reg s22 rTmp).val = jumpBase n m + 2 * ancNode := by
    rw [r22, WordOps.add_val, htmp21, k21 _ (by decide), hch20,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)]; omega
  obtain ⟨s23, st23, pc23, r23, k23, d23⟩ := step_add15_at (input := input) (s := s22)
    (placed_fetch hpl7d (i := 2) rfl (by rw [pc22, pc21, pc20])) (by rw [pc22, pc21, pc20]; omega)
  have htmp23 : (reg s23 rTmp).val = jumpBase n m + 3 * ancNode := by
    rw [r23, WordOps.add_val, htmp22, k22 _ (by decide), k21 _ (by decide), hch20,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)]; omega
  obtain ⟨s24, st24, pc24, r24, k24, d24⟩ := step_add15_at (input := input) (s := s23)
    (placed_fetch hpl7d (i := 3) rfl (by rw [pc23, pc22, pc21, pc20]))
    (by rw [pc23, pc22, pc21, pc20]; omega)
  have htmp24 : (reg s24 rTmp).val = jumpBase n m + 1 + 3 * ancNode := by
    rw [r24, WordOps.add_val, htmp23, k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), ho20,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)]; omega
  obtain ⟨s25, st25, pc25, r25, k25, d25⟩ := step_loadData_reg (s := s24)
    (placed_fetch hpl7d (i := 4) rfl (by rw [pc24, pc23, pc22, pc21, pc20]))
    (by rw [pc24, pc23, pc22, pc21, pc20]; omega)
    (by rw [htmp24]; omega) (by rw [htmp24, d24, d23, d22, d21, hd20]; exact hDepAnc)
  have hcmd25 : (reg s25 rCmd).val = F.depthOf ancNode := r25
  have htin25 : (reg s25 rTin).val = jumpBase n m := by
    rw [k25 _ (by decide), k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), htin20]
  have hptr25 : (reg s25 rPtr).val = uNode := by
    rw [k25 _ (by decide), k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), hptr20]
  have ho25 : (reg s25 rOne).val = 1 := by
    rw [k25 _ (by decide), k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), ho20]
  have hz25 : (reg s25 rZero).val = 0 := by
    rw [k25 _ (by decide), k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), hz20]
  have hd25 : s25.data = s16.data := d25.trans (d24.trans (d23.trans (d22.trans (d21.trans hd20))))
  obtain ⟨s26, st26, pc26, r26, k26, d26⟩ := step_add15_at (input := input) (s := s25)
    (placed_fetch hpl7d (i := 5) rfl (by rw [pc25, pc24, pc23, pc22, pc21, pc20]))
    (by rw [pc25, pc24, pc23, pc22, pc21, pc20]; omega)
  have htmp26 : (reg s26 rTmp).val = jumpBase n m + uNode := by
    rw [r26, WordOps.add_val, htin25, hptr25]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
  obtain ⟨s27, st27, pc27, r27, k27, d27⟩ := step_add15_at (input := input) (s := s26)
    (placed_fetch hpl7d (i := 6) rfl (by rw [pc26, pc25, pc24, pc23, pc22, pc21, pc20]))
    (by rw [pc26, pc25, pc24, pc23, pc22, pc21, pc20]; omega)
  have htmp27 : (reg s27 rTmp).val = jumpBase n m + 2 * uNode := by
    rw [r27, WordOps.add_val, htmp26, k26 _ (by decide), hptr25,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)]; omega
  obtain ⟨s28, st28, pc28, r28, k28, d28⟩ := step_add15_at (input := input) (s := s27)
    (placed_fetch hpl7d (i := 7) rfl (by rw [pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20]))
    (by rw [pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20]; omega)
  have htmp28 : (reg s28 rTmp).val = jumpBase n m + 3 * uNode := by
    rw [r28, WordOps.add_val, htmp27, k27 _ (by decide), k26 _ (by decide), hptr25,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)]; omega
  obtain ⟨s29, st29, pc29, r29, k29, d29⟩ := step_add15_at (input := input) (s := s28)
    (placed_fetch hpl7d (i := 8) rfl (by rw [pc28, pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20]))
    (by rw [pc28, pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20]; omega)
  have htmp29 : (reg s29 rTmp).val = jumpBase n m + 1 + 3 * uNode := by
    rw [r29, WordOps.add_val, htmp28, k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), ho25,
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)]; omega
  obtain ⟨s30, st30, pc30, r30, k30, d30⟩ := step_loadData_reg (s := s29)
    (placed_fetch hpl7d (i := 9) rfl (by rw [pc29, pc28, pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20]))
    (by rw [pc29, pc28, pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20]; omega)
    (by rw [htmp29]; omega) (by rw [htmp29, d29, d28, d27, d26, hd25]; exact hDepU)
  have hval30 : (reg s30 rVal).val = F.depthOf uNode := r30
  have hcmd30 : (reg s30 rCmd).val = F.depthOf ancNode := by
    rw [k30 _ (by decide), k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), hcmd25]
  have htin30 : (reg s30 rTin).val = jumpBase n m := by
    rw [k30 _ (by decide), k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), htin25]
  have hptr30 : (reg s30 rPtr).val = uNode := by
    rw [k30 _ (by decide), k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), hptr25]
  have ho30 : (reg s30 rOne).val = 1 := by
    rw [k30 _ (by decide), k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), ho25]
  have hz30 : (reg s30 rZero).val = 0 := by
    rw [k30 _ (by decide), k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), k26 _ (by decide), hz25]
  have hch30 : (reg s30 rChild).val = ancNode := by
    rw [k30 _ (by decide), k29 _ (by decide), k28 _ (by decide), k27 _ (by decide), k26 _ (by decide),
      k25 _ (by decide), k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), hch20]
  have hd30 : s30.data = s16.data := d30.trans (d29.trans (d28.trans (d27.trans (d26.trans hd25))))
  have hpc30 : s30.pc = pcChkAnc + (bsProbePr7 h8).length := by
    rw [pc30, pc29, pc28, pc27, pc26, pc25, pc24, pc23, pc22, pc21, pc20, hpr7Len]; omega
  have hst7d : Steps code input 10 s20 s30 :=
    .cons st21 (.cons st22 (.cons st23 (.cons st24 (.cons st25
      (.cons st26 (.cons st27 (.cons st28 (.cons st29 (.cons st30 (.zero _))))))))))
  have hst7 : Steps code input (bsProbePr7 h8).length s16 s30 := by
    rw [hpr7Len]; exact ((st17.append (.cons st18 (.cons st19 (.zero _)))).append st20).append hst7d
  exact ⟨s30, hst7, hpc30, hz30, ho30, htin30, hptr30, hch30, hcmd30, hval30, hd30⟩

private theorem bsProbeChkAnc_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} [DecidableEq (CutPair H)] {F : JumpForest} {sRef : _root_.EX24.State H}
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount} {idx : Nat}
    {s0 s16 : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s0)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hidx : idx < H.vertexCount)
    {u : Vertex H} {ancNode j kPrefix : Nat} {q : CutPair H}
    (huFst : u ≠ q.fst) (huSnd : u ≠ q.snd)
    (hancF : ancNode < F.size) (hancLeN : ancNode ≤ H.vertexCount)
    (hj1Lt : j + 1 < 2 ^ bits)
    (hSlLabW : slLabels < workCap) (hSlJW : slJumpBase < workCap)
    (hSlAncW : slAncNode < workCap) (hSlPJW : slPredJ < workCap)
    {pcProbe pcProbeFail pcChkAnc pcDL2 pcAfterDL2 pcNextU : Nat}
    (hpcDL2 : pcDL2 = pcChkAnc + (bsProbePr7 h8).length + 3)
    (hpcNextU : pcNextU = pcAfterDL2 + (bsProbePr9Head h8).length + 2)
    (hFailBnd : pcProbeFail < code.size) (hProbeBnd : pcProbe < code.size)
    (hPr7Bnd : pcChkAnc + (bsProbePr7 h8).length + 3 < code.size)
    (hAfterDL2Bnd : pcAfterDL2 < code.size) (hNextUBnd : pcNextU < code.size)
    (hNextBnd : pcNextU + (bsProbePrNext h8 pcProbe).length < code.size)
    (hPr7Le : (bsProbePr7 h8).length ≤ 36)
    (hPr9HLe : (bsProbePr9Head h8).length ≤ 14)
    (hPrNextLe : (bsProbePrNext h8 pcProbe).length ≤ 26)
    (hpl7 : Placed code pcChkAnc (bsProbePr7 h8))
    (hpl7b : Placed code (pcChkAnc + (bsProbePr7 h8).length)
      [.branchLt rVal rCmd pcProbeFail (pcChkAnc + (bsProbePr7 h8).length + 1),
       .add rTout rTin rOne, .add rOff rTout rOne])
    (hpl8 : Placed code pcDL2 (relocatedSubroutine (PaperB.RamForestProgram.DepthSeek.depthLookupProgram
      (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)) pcDL2 pcAfterDL2))
    (hpl9 : Placed code pcAfterDL2 (bsProbePr9Head h8 ++
      [.branchLt rPtr rChild pcProbeFail (pcNextU - 1), .branchLt rChild rPtr pcProbeFail pcNextU]))
    (hplNext : Placed code pcNextU (bsProbePrNext h8 pcProbe))
    (hkPrefix : kPrefix ≤ 85) (hPre : Steps code input kPrefix s0 s16)
    (hs16d : s16.data = s0.data) (hpc16 : s16.pc = pcChkAnc)
    (hz16 : (reg s16 rZero).val = 0) (ho16 : (reg s16 rOne).val = 1)
    (hstk16 : (reg s16 rStack).val = u.val) (hch16 : (reg s16 rChild).val = ancNode)
    (hSlPJ : (s0.data[slPredJ]?).map Fin.val = some j)
    (hSlAnc : (s0.data[slAncNode]?).map Fin.val = some ancNode) :
    if u = q.fst ∨ u = q.snd ∨
        (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
         F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode) then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 175 + 60 * (OracleContract.L H.vertexCount + 1) ∧
        Steps code input k s0 t ∧ t.pc = pcProbe ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (t.data[slPredJ]?).map Fin.val = some (j + 1) ∧
        ∀ w, w = slPredJ ∨ t.data[w]? = s0.data[w]?
    else
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 150 + 60 * (OracleContract.L H.vertexCount + 1) ∧
        Steps code input k s0 t ∧ t.pc = pcProbeFail ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s0.data := by
  let n := H.vertexCount
  let m := H.arcCount
  let uNode := sRef.labelAt u.val
  have huF : uNode < F.size := inv.grounded.size_eq ▸ inv.labelsLt u
  have huLeN : uNode ≤ n := by have := inv.labelsLt u; have := inv.sRefNextLe; omega
  have hLabAddrW : labelsBase n m + u.val < workCap := by
    have := u.isLt
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
      stampsBase, indegBase, csrArenaWords] at *
    unfold rawWorkCap at hWork; omega
  have hAncJmpW : jumpBase n m + 3 * ancNode + 1 < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *
    unfold rawWorkCap at hWork; omega
  have hUJmpW : jumpBase n m + 3 * uNode + 1 < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *
    unfold rawWorkCap at hWork; omega
  have hJmp2W : jumpBase n m + 2 < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *
    unfold rawWorkCap at hWork; omega
  have hPr7Step1 : pcChkAnc + (bsProbePr7 h8).length + 1 < code.size := by omega
  have hPr7Step2 : pcChkAnc + (bsProbePr7 h8).length + 1 + 1 < code.size := by omega
  have hPr7Step3 : pcChkAnc + (bsProbePr7 h8).length + 1 + 1 + 1 < code.size := by omega
  have h9H0 : pcAfterDL2 + 1 < code.size := by omega
  have h9H1 : pcAfterDL2 + 1 + 1 < code.size := by omega
  have h9H2 : pcAfterDL2 + 2 + (loadScratch h8 rChild slAncNode).length < code.size := by
    have : (bsProbePr9Head h8).length = 2 + (loadScratch h8 rChild slAncNode).length := rfl
    omega
  have h9B0 : pcNextU - 2 + 1 < code.size := by omega
  have h9B1 : pcNextU - 1 < code.size := by omega
  have hFIns : F.numInserted ≤ n := by
    have hSzF : F.size = sRef.tables.next := inv.grounded.size_eq
    have hSRefN : sRef.tables.next ≤ n := Nat.le_trans inv.sRefNextLe (by omega)
    change F.records.length - 1 ≤ n; change F.records.length = sRef.tables.next at hSzF; omega
  obtain ⟨s30, hst7, hpc30, hz30, ho30, htin30, hptr30, hch30, hcmd30, hval30, hd30⟩ :=
    bsProbePr7_steps h8 input hSlLabW hSlJW hLabAddrW hAncJmpW hUJmpW hancF huF
      hpl7 (by omega) hpc16 hz16 ho16 hstk16 hch16
      (by rw [hs16d]; exact inv.slLabelsVal) (by rw [hs16d]; exact inv.slJumpVal)
      (by rw [hs16d]; exact inv.labelsMem u)
      (by rw [hs16d]; exact inv.records.depth ancNode hancF)
      (by rw [hs16d]; exact inv.records.depth uNode huF)
  have hd30' : s30.data = s0.data := hd30.trans hs16d
  have hPre30 : Steps code input (kPrefix + (bsProbePr7 h8).length) s0 s30 := hPre.append hst7
  by_cases hDepLt : F.depthOf uNode < F.depthOf ancNode
  · have hCondFalse : ¬ (u = q.fst ∨ u = q.snd ∨
        (F.depthOf ancNode ≤ F.depthOf uNode ∧ F.ancestorAtDepth uNode (F.depthOf ancNode) = ancNode)) := by
      rintro (h1 | h2 | ⟨h3, _⟩)
      · exact huFst h1
      · exact huSnd h2
      · omega
    rw [ite_eq_right hCondFalse]
    obtain ⟨s31, st31, pc31, k31, d31⟩ := step_branchLt_true (s := s30)
      (placed_fetch hpl7b (i := 0) rfl hpc30) (by rw [hval30, hcmd30]; exact hDepLt) hFailBnd
    have hkTot : kPrefix + (bsProbePr7 h8).length + 1 ≤ 150 + 60 * (OracleContract.L H.vertexCount + 1) := by
      omega
    exact ⟨s31, kPrefix + (bsProbePr7 h8).length + 1, hkTot, hPre30.append (.cons st31 (.zero _)), pc31,
      by rw [k31, hz30], by rw [k31, ho30], d31.trans hd30'⟩
  · have hDepLe : F.depthOf ancNode ≤ F.depthOf uNode := by omega
    obtain ⟨s31, st31, pc31, k31, d31⟩ := step_branchLt_false (s := s30)
      (placed_fetch hpl7b (i := 0) rfl hpc30) (by rw [hcmd30, hval30]; exact hDepLe) hPr7Step1
    obtain ⟨s32, st32, pc32, r32, k32, d32⟩ := step_add15_at (input := input) (s := s31)
      (placed_fetch hpl7b (i := 1) rfl pc31) (by rw [pc31]; exact hPr7Step2)
    have htout32 : (reg s32 rTout).val = jumpBase n m + 1 := by
      rw [r32, WordOps.add_val, k31, htin30, k31, ho30]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
    obtain ⟨s33, st33, pc33, r33, k33, d33⟩ := step_add15_at (input := input) (s := s32)
      (placed_fetch hpl7b (i := 2) rfl (by rw [pc32, pc31])) (by rw [pc32, pc31]; exact hPr7Step3)
    have hoff33 : (reg s33 rOff).val = jumpBase n m + 2 := by
      rw [r33, WordOps.add_val, htout32, k32 _ (by decide), k31, ho30]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
    have htin33 : (reg s33 rTin).val = jumpBase n m := by rw [k33 _ (by decide), k32 _ (by decide), k31, htin30]
    have htout33 : (reg s33 rTout).val = jumpBase n m + 1 := by rw [k33 _ (by decide), htout32]
    have hcmd33 : (reg s33 rCmd).val = F.depthOf ancNode := by rw [k33 _ (by decide), k32 _ (by decide), k31, hcmd30]
    have hz33 : (reg s33 rZero).val = 0 := by rw [k33 _ (by decide), k32 _ (by decide), k31, hz30]
    have hptr33 : (reg s33 rPtr).val = uNode := by rw [k33 _ (by decide), k32 _ (by decide), k31, hptr30]
    have hd33 : s33.data = s0.data := d33.trans (d32.trans (d31.trans hd30'))
    have hpc33 : s33.pc = pcDL2 := by rw [pc33, pc32, pc31, hpcDL2]
    have hRec33 : PaperB.RamForestProgram.DepthSeek.Records (jumpBase n m) F s33.data := by
      rw [hd33]; exact inv.records
    obtain ⟨s34, kDL2, hkDL2, stDL2, pc34, r34, hd34⟩ := relocate_depthLookup input s33 hpc33
      hAfterDL2Bnd hpl8 ⟨htin33, htout33, hoff33, hcmd33, hz33⟩ hRec33 huF hptr33 hFIns
      (vertexCount_add2_le_two_pow_L_succ n)
    have hd34' : s34.data = s0.data := hd34.trans hd33
    have hpl9H : Placed code pcAfterDL2 ([.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] : List (Instr bits 15)) :=
      placed_append_left (placed_append_left hpl9)
    have hpl9C : Placed code (pcAfterDL2 + 2) (loadScratch h8 rChild slAncNode) :=
      placed_right_eq (placed_append_left hpl9) rfl
    have hpl9B : Placed code (pcNextU - 2)
        ([.branchLt rPtr rChild pcProbeFail (pcNextU - 1), .branchLt rChild rPtr pcProbeFail pcNextU] :
          List (Instr bits 15)) :=
      placed_right_eq hpl9 (by
        have : (bsProbePr9Head h8).length = 2 + (loadScratch h8 rChild slAncNode).length := rfl
        omega)
    have hPr9H : (bsProbePr9Head h8).length = 2 + (loadScratch h8 rChild slAncNode).length := rfl
    obtain ⟨s35, st35, pc35, r35, k35, d35⟩ := step_imm_at (input := input) (s := s34)
      (placed_fetch hpl9H (i := 0) rfl pc34) (by rw [pc34]; exact h9H0)
    obtain ⟨s36, st36, pc36, r36, k36, d36⟩ := step_imm_at (input := input) (s := s35)
      (placed_fetch hpl9H (i := 1) rfl (by rw [pc35, pc34])) (by rw [pc35, pc34]; exact h9H1)
    have ho36 : (reg s36 rOne).val = 1 := congrArg Fin.val r36
    have hz36 : (reg s36 rZero).val = 0 := by rw [k36 _ (by decide), r35]
    have hptr36 : (reg s36 rPtr).val = F.ancestorAtDepth uNode (F.depthOf ancNode) := by
      rw [k36 _ (by decide), k35 _ (by decide), r34]
    obtain ⟨s37, st37, pc37, r37, d37, k37⟩ := loadScratch_val_steps h8 (input := input) rChild slAncNode hSlAncW
      (by decide) (by rw [pc36, pc35, pc34]) hpl9C h9H2 ho36 (by rw [d36, d35, hd34']; exact hSlAnc)
    have ho37 : (reg s37 rOne).val = 1 := by rw [k37 _ (by decide) (by decide), ho36]
    have hz37 : (reg s37 rZero).val = 0 := by rw [k37 _ (by decide) (by decide), hz36]
    have hptr37 : (reg s37 rPtr).val = F.ancestorAtDepth uNode (F.depthOf ancNode) := by
      rw [k37 _ (by decide) (by decide), hptr36]
    have hch37 : (reg s37 rChild).val = ancNode := r37
    have hd37 : s37.data = s0.data := d37.trans (d36.trans (d35.trans hd34'))
    have hpc37 : s37.pc = pcNextU - 2 := by
      rw [pc37, hpcNextU, hPr9H]; omega
    have hPre37 : Steps code input
        (kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length) s0 s37 := by
      have h7bSt : Steps code input 3 s30 s33 := .cons st31 (.cons st32 (.cons st33 (.zero _)))
      have h9HSt : Steps code input (bsProbePr9Head h8).length s34 s37 := by
        rw [hPr9H]; exact (Steps.cons st35 (Steps.cons st36 (Steps.zero _))).append st37
      exact (((hPre30.append h7bSt).append stDL2).append h9HSt)
    by_cases hAncEq : F.ancestorAtDepth uNode (F.depthOf ancNode) = ancNode
    · have hCond : u = q.fst ∨ u = q.snd ∨
          (F.depthOf ancNode ≤ F.depthOf uNode ∧ F.ancestorAtDepth uNode (F.depthOf ancNode) = ancNode) :=
        Or.inr (Or.inr ⟨hDepLe, hAncEq⟩)
      rw [ite_eq_left hCond]
      have hle1 : (reg s37 rChild).val ≤ (reg s37 rPtr).val := by
        rw [hch37, hptr37, hAncEq]; exact Nat.le_refl _
      obtain ⟨s38, st38, pc38, k38, d38⟩ := step_branchLt_false (s := s37)
        (placed_fetch hpl9B (i := 0) rfl hpc37) hle1 h9B1
      have hle2 : (reg s38 rPtr).val ≤ (reg s38 rChild).val := by
        rw [k38, k38, hptr37, hch37, hAncEq]; exact Nat.le_refl _
      obtain ⟨s39, st39, pc39, k39, d39⟩ := step_branchLt_false (s := s38)
        (placed_fetch hpl9B (i := 1) rfl (by rw [pc38]; omega)) hle2 hNextUBnd
      obtain ⟨t, stTail, htpc, htz, hto, htPJ, htFr⟩ := bsProbePrNext_steps h8 input hSlPJW hj1Lt hplNext
        hNextBnd hProbeBnd pc39 (by rw [k39, k38, hz37]) (by rw [k39, k38, ho37])
        (by rw [d39.trans (d38.trans hd37)]; exact hSlPJ)
      have hkTot : kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length + 2 +
          (bsProbePrNext h8 pcProbe).length ≤ 175 + 60 * (OracleContract.L H.vertexCount + 1) := by
        have hkDL2' : kDL2 ≤ 60 * (OracleContract.L H.vertexCount + 1) + 7 := hkDL2
        omega
      exact ⟨t, kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length + 2 +
          (bsProbePrNext h8 pcProbe).length, hkTot,
        (hPre37.append (.cons st38 (.cons st39 (.zero _)))).append stTail,
        htpc, htz, hto, htPJ, fun w => (htFr w).elim Or.inl (fun h => Or.inr (by rw [h, d39, d38, hd37]))⟩
    · have hCondFalse : ¬ (u = q.fst ∨ u = q.snd ∨
          (F.depthOf ancNode ≤ F.depthOf uNode ∧ F.ancestorAtDepth uNode (F.depthOf ancNode) = ancNode)) := by
        rintro (h1 | h2 | ⟨_, h4⟩)
        · exact huFst h1
        · exact huSnd h2
        · exact hAncEq h4
      rw [ite_eq_right hCondFalse]
      by_cases hlt1 : F.ancestorAtDepth uNode (F.depthOf ancNode) < ancNode
      · obtain ⟨s38, st38, pc38, k38, d38⟩ := step_branchLt_true (s := s37)
          (placed_fetch hpl9B (i := 0) rfl hpc37) (by rw [hptr37, hch37]; exact hlt1) hFailBnd
        have hkTot : kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length + 1 ≤
            150 + 60 * (OracleContract.L H.vertexCount + 1) := by
          have hkDL2' : kDL2 ≤ 60 * (OracleContract.L H.vertexCount + 1) + 7 := hkDL2
          omega
        exact ⟨s38, kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length + 1, hkTot,
          hPre37.append (.cons st38 (.zero _)), pc38,
          by rw [k38, hz37], by rw [k38, ho37], d38.trans hd37⟩
      · have hle1 : (reg s37 rChild).val ≤ (reg s37 rPtr).val := by rw [hch37, hptr37]; omega
        have hlt2 : ancNode < F.ancestorAtDepth uNode (F.depthOf ancNode) := by omega
        obtain ⟨s38, st38, pc38, k38, d38⟩ := step_branchLt_false (s := s37)
          (placed_fetch hpl9B (i := 0) rfl hpc37) hle1 h9B1
        obtain ⟨s39, st39, pc39, k39, d39⟩ := step_branchLt_true (s := s38)
          (placed_fetch hpl9B (i := 1) rfl (by rw [pc38]; omega))
          (by rw [k38, k38, hch37, hptr37]; exact hlt2) hFailBnd
        have hkTot : kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length + 2 ≤
            150 + 60 * (OracleContract.L H.vertexCount + 1) := by
          have hkDL2' : kDL2 ≤ 60 * (OracleContract.L H.vertexCount + 1) + 7 := hkDL2
          omega
        exact ⟨s39, kPrefix + (bsProbePr7 h8).length + 3 + kDL2 + (bsProbePr9Head h8).length + 2, hkTot,
          hPre37.append (.cons st38 (.cons st39 (.zero _))), pc39,
          by rw [k39, k38, hz37], by rw [k39, k38, ho37], d39.trans (d38.trans hd37)⟩

private theorem bsProbePr456_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} {u : Vertex H} {q : CutPair H}
    {ancNode bsAddr pcChkBS pcChkAnc pcNextU : Nat}
    (hPr5Le : (bsProbePr5 h8).length ≤ 14)
    (hChk2 : 2 ≤ pcChkBS)
    (hChkAncEq : pcChkAnc = pcChkBS + (bsProbePr5 h8).length + 2)
    (hPr4Step1 : pcChkBS - 1 < code.size) (hChkBSBnd : pcChkBS < code.size)
    (hPr5aBnd : pcChkBS + (loadScratch h8 rTmp slBackSnd).length < code.size)
    (hPr5Step0 : pcChkBS + (loadScratch h8 rTmp slBackSnd).length + 1 < code.size)
    (hPr5Step1 : pcChkBS + (loadScratch h8 rTmp slBackSnd).length + 2 < code.size)
    (hPr6Step1 : pcChkAnc - 1 < code.size) (hChkAncBnd : pcChkAnc < code.size) (hNextUBnd : pcNextU < code.size)
    (hSlBSW : slBackSnd < workCap) (hBSAddrW : bsAddr + ancNode < workCap)
    (hpl4 : Placed code (pcChkBS - 2) [.branchLt rTmp rVal pcChkBS (pcChkBS - 1), .branchLt rVal rTmp pcChkBS pcNextU])
    (hpl5 : Placed code pcChkBS (bsProbePr5 h8))
    (hpl6 : Placed code (pcChkAnc - 2) [.branchLt rStack rVal pcChkAnc (pcChkAnc - 1), .branchLt rVal rStack pcChkAnc pcNextU])
    {s11 : State (layout bits inputCap workCap hi hw)}
    (hpc11 : s11.pc = pcChkBS - 2) (hz11 : (reg s11 rZero).val = 0) (ho11 : (reg s11 rOne).val = 1)
    (hstk11 : (reg s11 rStack).val = u.val) (hch11 : (reg s11 rChild).val = ancNode)
    (htmp11 : (reg s11 rTmp).val = u.val + 1) (hval11 : (reg s11 rVal).val = q.fst.val + 1)
    (hSlBSVal : (s11.data[slBackSnd]?).map Fin.val = some bsAddr)
    (hBSq : (s11.data[bsAddr + ancNode]?).map Fin.val = some q.snd.val) :
    if u = q.fst ∨ u = q.snd then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 18 ∧ Steps code input k s11 t ∧
        t.pc = pcNextU ∧ (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s11.data
    else
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 18 ∧ Steps code input k s11 t ∧
        t.pc = pcChkAnc ∧ (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (reg t rStack).val = u.val ∧ (reg t rChild).val = ancNode ∧ t.data = s11.data := by
  have hf4_0 : code[s11.pc]? = some (.branchLt rTmp rVal pcChkBS (pcChkBS - 1)) :=
    placed_fetch hpl4 (i := 0) rfl hpc11
  by_cases huFst : u = q.fst
  · have hCond : u = q.fst ∨ u = q.snd := Or.inl huFst
    rw [ite_eq_left hCond]
    have hEq1 : (reg s11 rVal).val ≤ (reg s11 rTmp).val := by rw [hval11, htmp11, huFst]; exact Nat.le_refl _
    obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_false (input := input) (s := s11) hf4_0 hEq1 hPr4Step1
    have hEq2 : (reg s12 rTmp).val ≤ (reg s12 rVal).val := by rw [k12, k12, htmp11, hval11, huFst]; exact Nat.le_refl _
    have hf4_1 : code[s12.pc]? = some (.branchLt rVal rTmp pcChkBS pcNextU) :=
      placed_fetch hpl4 (i := 1) rfl (by rw [pc12]; omega)
    obtain ⟨s13, st13, pc13, k13, d13⟩ := step_branchLt_false (input := input) (s := s12) hf4_1 hEq2 hNextUBnd
    exact ⟨s13, 2, by omega, Steps.cons st12 (Steps.cons st13 (Steps.zero _)), pc13,
      by rw [k13, k12, hz11], by rw [k13, k12, ho11], d13.trans d12⟩
  · have hBr5 : ∃ s12 : State (layout bits inputCap workCap hi hw), ∃ k12 : Nat,
        k12 ≤ 2 ∧ Steps code input k12 s11 s12 ∧ s12.pc = pcChkBS ∧
        (reg s12 rZero).val = 0 ∧ (reg s12 rOne).val = 1 ∧
        (reg s12 rStack).val = u.val ∧ (reg s12 rChild).val = ancNode ∧ s12.data = s11.data := by
      by_cases hlt1 : u.val + 1 < q.fst.val + 1
      · obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_true (input := input) (s := s11)
          hf4_0 (by rw [htmp11, hval11]; exact hlt1) hChkBSBnd
        exact ⟨s12, 1, by omega, Steps.cons st12 (Steps.zero _), pc12,
          by rw [k12, hz11], by rw [k12, ho11], by rw [k12, hstk11], by rw [k12, hch11], d12⟩
      · have hle1 : (reg s11 rVal).val ≤ (reg s11 rTmp).val := by rw [hval11, htmp11]; omega
        have hlt2 : q.fst.val + 1 < u.val + 1 := by
          have : u.val ≠ q.fst.val := fun h => huFst (Fin.ext h)
          omega
        obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_false (input := input) (s := s11) hf4_0 hle1 hPr4Step1
        have hf4_1 : code[s12.pc]? = some (.branchLt rVal rTmp pcChkBS pcNextU) :=
          placed_fetch hpl4 (i := 1) rfl (by rw [pc12]; omega)
        obtain ⟨s13, st13, pc13, k13, d13⟩ := step_branchLt_true (input := input) (s := s12)
          hf4_1 (by rw [k12, k12, hval11, htmp11]; exact hlt2) hChkBSBnd
        exact ⟨s13, 2, by omega, Steps.cons st12 (Steps.cons st13 (Steps.zero _)), pc13,
          by rw [k13, k12, hz11], by rw [k13, k12, ho11],
          by rw [k13, k12, hstk11], by rw [k13, k12, hch11], d13.trans d12⟩
    obtain ⟨s12, k12, hk12, st12, pc12, hz12, ho12, hstk12, hch12, hd12⟩ := hBr5
    have hpl5' : Placed code pcChkBS (loadScratch h8 rTmp slBackSnd ++
        [.add rTmp rTmp rChild, .loadData rVal rTmp]) := by
      unfold bsProbePr5 at hpl5; exact hpl5
    have hpl5a : Placed code pcChkBS (loadScratch h8 rTmp slBackSnd) := placed_append_left hpl5'
    have hpl5b : Placed code (pcChkBS + (loadScratch h8 rTmp slBackSnd).length)
        ([.add rTmp rTmp rChild, .loadData rVal rTmp] : List (Instr bits 15)) := placed_right_eq hpl5' rfl
    have hpr5Len : (bsProbePr5 h8).length = (loadScratch h8 rTmp slBackSnd).length + 2 := by
      simp only [bsProbePr5, List.length_append, List.length_cons, List.length_nil]
    obtain ⟨s13, st13, pc13, r13, d13, k13⟩ := loadScratch_val_steps h8 (input := input) rTmp slBackSnd hSlBSW
      (by decide) pc12 hpl5a hPr5aBnd ho12 (by rw [hd12]; exact hSlBSVal)
    have ho13 : (reg s13 rOne).val = 1 := by rw [k13 _ (by decide) (by decide), ho12]
    have hz13 : (reg s13 rZero).val = 0 := by rw [k13 _ (by decide) (by decide), hz12]
    have hstk13 : (reg s13 rStack).val = u.val := by rw [k13 _ (by decide) (by decide), hstk12]
    have hch13 : (reg s13 rChild).val = ancNode := by rw [k13 _ (by decide) (by decide), hch12]
    obtain ⟨s14, st14, pc14, r14, k14, d14⟩ := step_add15_at (input := input) (s := s13)
      (placed_fetch hpl5b (i := 0) rfl pc13) (by rw [pc13]; exact hPr5Step0)
    have htmp14 : (reg s14 rTmp).val = bsAddr + ancNode := by
      rw [r14, WordOps.add_val, r13, hch13]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hBSAddrW hw)
    obtain ⟨s15, st15, pc15, r15, k15, d15⟩ := step_loadData_reg (s := s14)
      (placed_fetch hpl5b (i := 1) rfl (by rw [pc14, pc13]))
      (by rw [pc14, pc13]; exact hPr5Step1) (by rw [htmp14]; exact hBSAddrW)
      (by rw [htmp14, d14, d13, hd12]; exact hBSq)
    have hval15 : (reg s15 rVal).val = q.snd.val := r15
    have ho15 : (reg s15 rOne).val = 1 := by rw [k15 _ (by decide), k14 _ (by decide), ho13]
    have hz15 : (reg s15 rZero).val = 0 := by rw [k15 _ (by decide), k14 _ (by decide), hz13]
    have hstk15 : (reg s15 rStack).val = u.val := by rw [k15 _ (by decide), k14 _ (by decide), hstk13]
    have hch15 : (reg s15 rChild).val = ancNode := by rw [k15 _ (by decide), k14 _ (by decide), hch13]
    have hd15 : s15.data = s11.data := d15.trans (d14.trans (d13.trans hd12))
    have hpc15 : s15.pc = pcChkAnc - 2 := by rw [pc15, pc14, pc13, hChkAncEq, hpr5Len]; omega
    have hst15 : Steps code input (k12 + (bsProbePr5 h8).length) s11 s15 := by
      have hst5 : Steps code input (bsProbePr5 h8).length s12 s15 := by
        rw [hpr5Len]; exact st13.append (Steps.cons st14 (Steps.cons st15 (Steps.zero _)))
      exact st12.append hst5
    have hf6_0 : code[s15.pc]? = some (.branchLt rStack rVal pcChkAnc (pcChkAnc - 1)) :=
      placed_fetch hpl6 (i := 0) rfl hpc15
    by_cases huSnd : u = q.snd
    · have hCond : u = q.fst ∨ u = q.snd := Or.inr huSnd
      rw [ite_eq_left hCond]
      have hEq1 : (reg s15 rVal).val ≤ (reg s15 rStack).val := by rw [hval15, hstk15, huSnd]; exact Nat.le_refl _
      obtain ⟨s16, st16, pc16, k16, d16⟩ := step_branchLt_false (input := input) (s := s15) hf6_0 hEq1 hPr6Step1
      have hEq2 : (reg s16 rStack).val ≤ (reg s16 rVal).val := by rw [k16, k16, hstk15, hval15, huSnd]; exact Nat.le_refl _
      have hf6_1 : code[s16.pc]? = some (.branchLt rVal rStack pcChkAnc pcNextU) :=
        placed_fetch hpl6 (i := 1) rfl (by rw [pc16]; omega)
      obtain ⟨s17, st17, pc17, k17, d17⟩ := step_branchLt_false (input := input) (s := s16) hf6_1 hEq2 hNextUBnd
      exact ⟨s17, k12 + (bsProbePr5 h8).length + 2, by omega,
        hst15.append (Steps.cons st16 (Steps.cons st17 (Steps.zero _))), pc17,
        by rw [k17, k16, hz15], by rw [k17, k16, ho15], d17.trans (d16.trans hd15)⟩
    · have hNot : ¬ (u = q.fst ∨ u = q.snd) := fun h => h.elim huFst huSnd
      rw [ite_eq_right hNot]
      by_cases hlt1 : u.val < q.snd.val
      · obtain ⟨s16, st16, pc16, k16, d16⟩ := step_branchLt_true (input := input) (s := s15)
          hf6_0 (by rw [hstk15, hval15]; exact hlt1) hChkAncBnd
        exact ⟨s16, k12 + (bsProbePr5 h8).length + 1, by omega,
          hst15.append (Steps.cons st16 (Steps.zero _)), pc16,
          by rw [k16, hz15], by rw [k16, ho15], by rw [k16, hstk15], by rw [k16, hch15], d16.trans hd15⟩
      · have hle1 : (reg s15 rVal).val ≤ (reg s15 rStack).val := by rw [hval15, hstk15]; omega
        have hlt2 : q.snd.val < u.val := by
          have : u.val ≠ q.snd.val := fun h => huSnd (Fin.ext h)
          omega
        obtain ⟨s16, st16, pc16, k16, d16⟩ := step_branchLt_false (input := input) (s := s15) hf6_0 hle1 hPr6Step1
        have hf6_1 : code[s16.pc]? = some (.branchLt rVal rStack pcChkAnc pcNextU) :=
          placed_fetch hpl6 (i := 1) rfl (by rw [pc16]; omega)
        obtain ⟨s17, st17, pc17, k17, d17⟩ := step_branchLt_true (input := input) (s := s16)
          hf6_1 (by rw [k16, k16, hval15, hstk15]; exact hlt2) hChkAncBnd
        exact ⟨s17, k12 + (bsProbePr5 h8).length + 2, by omega,
          hst15.append (Steps.cons st16 (Steps.cons st17 (Steps.zero _))), pc17,
          by rw [k17, k16, hz15], by rw [k17, k16, ho15],
          by rw [k17, k16, hstk15], by rw [k17, k16, hch15], d17.trans (d16.trans hd15)⟩

private theorem sweepBSProbe_slice {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {pcProbe pcProbeOk pcProbeFail : Nat}
    (hSz : pcProbe + (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length < code.size)
    (hpl : Placed code pcProbe (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail)) :
    let pr0 := bsProbePr0 h8
    let pr2 := bsProbePr2 h8
    let pr3 := bsProbePr3 h8
    let pr5 := bsProbePr5 h8
    let pr7 := bsProbePr7 h8
    let pr9Head := bsProbePr9Head h8
    let prNext := bsProbePrNext h8 pcProbe
    let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
      (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
    let pcChkBS := pcProbe + pr0.length + 1 + pr2.length + pr3.length + 2
    let pcChkAnc := pcChkBS + pr5.length + 2
    let pcDL2 := pcChkAnc + pr7.length + 3
    let pcAfterDL2 := pcDL2 + dlProg.toList.length
    let pcNextU := pcAfterDL2 + pr9Head.length + 2
    pcProbe < code.size ∧ pcNextU < code.size ∧
    pcProbe + pr0.length < code.size ∧
    pcProbe + (loadScratch h8 rClk slPredJ).length < code.size ∧
    pcProbe + pr0.length + 1 < code.size ∧
    pcProbe + pr0.length + 1 + pr2.length < code.size ∧
    pcProbe + pr0.length + 1 + pr2.length + pr3.length < code.size ∧
    pcChkBS < code.size ∧ pcChkBS - 1 < code.size ∧
    pcChkBS + pr5.length < code.size ∧
    pcChkBS + (loadScratch h8 rTmp slBackSnd).length < code.size ∧
    pcChkBS + (loadScratch h8 rTmp slBackSnd).length + 1 < code.size ∧
    pcChkBS + (loadScratch h8 rTmp slBackSnd).length + 2 < code.size ∧
    pcChkAnc < code.size ∧ pcChkAnc - 1 < code.size ∧
    pcChkAnc + pr7.length + 3 < code.size ∧
    pcAfterDL2 < code.size ∧ pcNextU + prNext.length < code.size ∧
    Placed code pcProbe pr0 ∧
    Placed code (pcProbe + pr0.length) [.branchLt rClk rRem (pcProbe + pr0.length + 1) pcProbeOk] ∧
    Placed code (pcProbe + pr0.length + 1) pr2 ∧
    Placed code (pcProbe + pr0.length + 1 + pr2.length) pr3 ∧
    Placed code (pcChkBS - 2) [.branchLt rTmp rVal pcChkBS (pcChkBS - 1), .branchLt rVal rTmp pcChkBS pcNextU] ∧
    Placed code pcChkBS pr5 ∧
    Placed code (pcChkAnc - 2) [.branchLt rStack rVal pcChkAnc (pcChkAnc - 1), .branchLt rVal rStack pcChkAnc pcNextU] ∧
    Placed code pcChkAnc pr7 ∧
    Placed code (pcChkAnc + pr7.length)
      [.branchLt rVal rCmd pcProbeFail (pcChkAnc + pr7.length + 1), .add rTout rTin rOne, .add rOff rTout rOne] ∧
    Placed code pcDL2 (relocatedSubroutine dlProg pcDL2 pcAfterDL2) ∧
    Placed code pcAfterDL2
      (pr9Head ++ [.branchLt rPtr rChild pcProbeFail (pcNextU - 1), .branchLt rChild rPtr pcProbeFail pcNextU]) ∧
    Placed code pcNextU prNext := by
  let pr0 := bsProbePr0 h8
  let pr2 := bsProbePr2 h8
  let pr3 := bsProbePr3 h8
  let pr5 := bsProbePr5 h8
  let pr7 := bsProbePr7 h8
  let pr9Head := bsProbePr9Head h8
  let prNext := bsProbePrNext h8 pcProbe
  let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
  let pcChkBS := pcProbe + pr0.length + 1 + pr2.length + pr3.length + 2
  let pcChkAnc := pcChkBS + pr5.length + 2
  let pcDL2 := pcChkAnc + pr7.length + 3
  let pcAfterDL2 := pcDL2 + dlProg.toList.length
  let pr8 := relocatedSubroutine dlProg pcDL2 pcAfterDL2
  let pcNextU := pcAfterDL2 + pr9Head.length + 2
  let pr1 : List (Instr bits 15) := [.branchLt rClk rRem (pcProbe + pr0.length + 1) pcProbeOk]
  let pr4 : List (Instr bits 15) :=
    [.branchLt rTmp rVal pcChkBS (pcChkBS - 1), .branchLt rVal rTmp pcChkBS pcNextU]
  let pr6 : List (Instr bits 15) :=
    [.branchLt rStack rVal pcChkAnc (pcChkAnc - 1), .branchLt rVal rStack pcChkAnc pcNextU]
  let pr7b : List (Instr bits 15) :=
    [.branchLt rVal rCmd pcProbeFail (pcChkAnc + pr7.length + 1), .add rTout rTin rOne, .add rOff rTout rOne]
  let pr9 : List (Instr bits 15) := pr9Head ++
    [.branchLt rPtr rChild pcProbeFail (pcNextU - 1), .branchLt rChild rPtr pcProbeFail pcNextU]
  have hLenProbe : (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length =
      pr0.length + 1 + pr2.length + pr3.length + 2 + pr5.length + 2 + pr7.length + 3 +
      pr8.length + pr9.length + prNext.length := by
    unfold sweepBSProbe
    dsimp only [dlProg, pr0, pr1, pr2, pr3, pr4, pr5, pr6, pr7, pr7b, pr8, pr9Head, pr9, prNext]
    simp only [relocatedSubroutine, List.length_append, List.length_cons, List.length_nil, List.length_map]
  have hPr9Len : pr9.length = pr9Head.length + 2 := by
    simp only [pr9, List.length_append, List.length_cons, List.length_nil]
  have hSzTot : pcNextU + prNext.length < code.size := by
    rw [hLenProbe] at hSz
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS]
    have hPr8Len : pr8.length = dlProg.toList.length := by simp [pr8, relocatedSubroutine]
    omega
  have hProbeBnd : pcProbe < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS] at hSzTot; omega
  have hNextUBnd : pcNextU < code.size := by omega
  have hPr0Bnd : pcProbe + pr0.length < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS] at hSzTot; omega
  have hPr0aBnd : pcProbe + (loadScratch h8 rClk slPredJ).length < code.size := by
    have : (loadScratch h8 rClk slPredJ).length ≤ pr0.length := by
      simp only [pr0, bsProbePr0, List.length_append]; omega
    omega
  have hPr1Bnd : pcProbe + pr0.length + 1 < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS] at hSzTot; omega
  have hPr2Bnd : pcProbe + pr0.length + 1 + pr2.length < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS] at hSzTot; omega
  have hPr3Bnd : pcProbe + pr0.length + 1 + pr2.length + pr3.length < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS] at hSzTot; omega
  have hChkBSBnd : pcChkBS < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc] at hSzTot; omega
  have hPr4Step1 : pcChkBS - 1 < code.size := by
    dsimp only [pcChkBS] at hChkBSBnd ⊢; omega
  have hPr5Bnd : pcChkBS + pr5.length < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc] at hSzTot; omega
  have hPr5aBnd : pcChkBS + (loadScratch h8 rTmp slBackSnd).length < code.size := by
    have : (loadScratch h8 rTmp slBackSnd).length ≤ pr5.length := by
      simp only [pr5, bsProbePr5, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hPr5Step0 : pcChkBS + (loadScratch h8 rTmp slBackSnd).length + 1 < code.size := by
    have : (loadScratch h8 rTmp slBackSnd).length + 1 ≤ pr5.length := by
      simp only [pr5, bsProbePr5, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hPr5Step1 : pcChkBS + (loadScratch h8 rTmp slBackSnd).length + 2 < code.size := by
    have : (loadScratch h8 rTmp slBackSnd).length + 2 ≤ pr5.length := by
      simp only [pr5, bsProbePr5, List.length_append, List.length_cons, List.length_nil]; omega
    omega
  have hChkAncBnd : pcChkAnc < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2] at hSzTot; omega
  have hPr6Step1 : pcChkAnc - 1 < code.size := by
    dsimp only [pcChkAnc] at hChkAncBnd ⊢; omega
  have hPr7Bnd : pcChkAnc + pr7.length + 3 < code.size := by
    dsimp only [pcNextU, pcAfterDL2, pcDL2] at hSzTot; omega
  have hAfterDL2Bnd : pcAfterDL2 < code.size := by
    dsimp only [pcNextU] at hSzTot; omega
  clear hSz
  unfold sweepBSProbe at hpl
  dsimp only at hpl
  have h11 := placed_append_left hpl
  have h10 := placed_append_left h11
  have h9 := placed_append_left h10
  have h8p := placed_append_left h9
  have h7p := placed_append_left h8p
  have h6p := placed_append_left h7p
  have h5p := placed_append_left h6p
  have h4p := placed_append_left h5p
  have h3p := placed_append_left h4p
  have h2p := placed_append_left h3p
  have hpl0 : Placed code pcProbe pr0 := placed_append_left h2p
  have hpl1 : Placed code (pcProbe + pr0.length) pr1 := placed_right_eq h2p rfl
  have hpl2 : Placed code (pcProbe + pr0.length + 1) pr2 :=
    placed_right_eq h3p (Nat.add_assoc _ _ 1)
  have hpl3 : Placed code (pcProbe + pr0.length + 1 + pr2.length) pr3 :=
    placed_right_eq h4p (by dsimp only [pr0, pr2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl4 : Placed code (pcChkBS - 2) pr4 :=
    placed_right_eq h5p (by
      dsimp only [pcChkBS, pr0, pr2, pr3]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5 : Placed code pcChkBS pr5 :=
    placed_right_eq h6p (by
      dsimp only [pcChkBS, pr0, pr2, pr3]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl6 : Placed code (pcChkAnc - 2) pr6 :=
    placed_right_eq h7p (by
      dsimp only [pcChkAnc, pcChkBS, pr0, pr2, pr3, pr5]
      try simp only [List.length_append, List.length_cons, List.length_nil]
      omega)
  have hpl7 : Placed code pcChkAnc pr7 :=
    placed_right_eq h8p (by
      dsimp only [pcChkAnc, pcChkBS, pr0, pr2, pr3, pr5]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl7b : Placed code (pcChkAnc + pr7.length) pr7b :=
    placed_right_eq h9 (by
      dsimp only [pcChkAnc, pcChkBS, pr0, pr2, pr3, pr5, pr7]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl8 : Placed code pcDL2 pr8 :=
    placed_right_eq h10 (by
      dsimp only [pcDL2, pcChkAnc, pcChkBS, pr0, pr2, pr3, pr5, pr7]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl9 : Placed code pcAfterDL2 pr9 :=
    placed_right_eq h11 (by
      dsimp only [pcAfterDL2, pcDL2, pcChkAnc, pcChkBS, dlProg, pr0, pr2, pr3, pr5, pr7]
      simp only [relocatedSubroutine, List.length_append, List.length_cons,
        List.length_nil, List.length_map]; omega)
  have hplNext : Placed code pcNextU prNext :=
    placed_right_eq hpl (by
      dsimp only [pcNextU, pcAfterDL2, pcDL2, pcChkAnc, pcChkBS, dlProg, pr0, pr2, pr3, pr5, pr7, pr9Head]
      simp only [relocatedSubroutine, List.length_append, List.length_cons,
        List.length_nil, List.length_map]; omega)
  exact ⟨hProbeBnd, hNextUBnd, hPr0Bnd, hPr0aBnd, hPr1Bnd, hPr2Bnd, hPr3Bnd, hChkBSBnd, hPr4Step1,
    hPr5Bnd, hPr5aBnd, hPr5Step0, hPr5Step1, hChkAncBnd, hPr6Step1, hPr7Bnd, hAfterDL2Bnd, hSzTot,
    hpl0, hpl1, hpl2, hpl3, hpl4, hpl5, hpl6, hpl7, hpl7b, hpl8, hpl9, hplNext⟩

private theorem sweepBSProbe_iter_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hidx : idx < H.vertexCount)
    {pcProbe pcProbeOk pcProbeFail : Nat}
    (hOkBnd : pcProbeOk < code.size) (hFailBnd : pcProbeFail < code.size)
    (hSz : pcProbe + (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length < code.size)
    (hpl : Placed code pcProbe (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail))
    {y m_y : Vertex H} {mid ancNode : Nat} {q : CutPair H} {rowLo rowHi j : Nat}
    (hmidPos : 0 < mid) (hmidLe : mid ≤ F.depthOf (sRef.labelAt m_y.val))
    (hancEq : ancNode = F.ancestorAtDepth (sRef.labelAt m_y.val) mid)
    (hq : sRef.tables.back[ancNode]? = some (some q))
    (hRLleJ : rowLo ≤ j) (_hjLeRH : j ≤ rowHi) (hRHm : rowHi ≤ H.arcCount)
    (hDiff : rowHi - rowLo = (rows.row y).length)
    (hPB : ∀ t' : Fin (rows.row y).length,
      (s.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
        some ((rows.row y)[t'.val]'t'.isLt).val)
    (hpc : s.pc = pcProbe)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlPJ : (s.data[slPredJ]?).map Fin.val = some j)
    (hSlRH : (s.data[slRowHi]?).map Fin.val = some rowHi)
    (hSlAnc : (s.data[slAncNode]?).map Fin.val = some ancNode) :
    if hlt : j < rowHi then
      let u := (rows.row y)[j - rowLo]'(by omega)
      if u = q.fst ∨ u = q.snd ∨
          (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
           F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode) then
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
          k ≤ 175 + 60 * (OracleContract.L H.vertexCount + 1) ∧
          Steps code input k s t ∧ t.pc = pcProbe ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
          (t.data[slPredJ]?).map Fin.val = some (j + 1) ∧
          ∀ w, w = slPredJ ∨ t.data[w]? = s.data[w]?
      else
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
          k ≤ 150 + 60 * (OracleContract.L H.vertexCount + 1) ∧
          Steps code input k s t ∧ t.pc = pcProbeFail ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data
    else
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 30 ∧ Steps code input k s t ∧ t.pc = pcProbeOk ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data := by
  let n := H.vertexCount
  let m := H.arcCount
  have hN1LtWork : n + 1 < workCap := by unfold rawWorkCap at hWork; omega
  have hArcLtWork : H.arcCount < workCap := by unfold rawWorkCap at hWork; omega
  have hBFAddrW_fn : ∀ a, a ≤ n → backFstBase n m + a < workCap := fun a ha => by
    simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords,
      rawWorkCap] at hWork ⊢; omega
  have hBSAddrW_fn : ∀ a, a ≤ n → backSndBase n m + a < workCap := fun a ha => by
    simp only [backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords,
      rawWorkCap] at hWork ⊢; omega
  have hPBAddrW_fn : ∀ j', j' < H.arcCount → predBufBase n m + j' < workCap := fun j' hj' => by
    simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords,
      rawWorkCap] at hWork ⊢; omega
  have hSlPJW : slPredJ < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlRHW : slRowHi < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlPBW : slPredBuf < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlAncW : slAncNode < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlBFW : slBackFst < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlBSW : slBackSnd < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlLabW : slLabels < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlJW : slJumpBase < workCap := scratch_lt_workCap30 hWork large (by decide)
  let pr0 := bsProbePr0 h8
  let pr2 := bsProbePr2 h8
  let pr3 := bsProbePr3 h8
  let pr5 := bsProbePr5 h8
  let pr7 := bsProbePr7 h8
  let pr9Head := bsProbePr9Head h8
  let prNext := bsProbePrNext h8 pcProbe
  have hPr0Le : pr0.length ≤ 24 := by
    unfold pr0 bsProbePr0
    have := loadScratch_length_le h8 rClk slPredJ
    have := loadScratch_length_le h8 rRem slRowHi
    simp only [List.length_append]; omega
  have hPr2Le : pr2.length ≤ 26 := by
    unfold pr2 bsProbePr2
    have := loadScratch_length_le h8 rTmp slPredBuf
    have := loadScratch_length_le h8 rChild slAncNode
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hPr3Le : pr3.length ≤ 15 := by
    unfold pr3 bsProbePr3
    have := loadScratch_length_le h8 rTmp slBackFst
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hPr5Le : pr5.length ≤ 14 := by
    unfold pr5 bsProbePr5
    have := loadScratch_length_le h8 rTmp slBackSnd
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hPr7Le : pr7.length ≤ 36 := by
    unfold pr7 bsProbePr7
    have := loadScratch_length_le h8 rTmp slLabels
    have := loadScratch_length_le h8 rTin slJumpBase
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hPr9HLe : pr9Head.length ≤ 14 := by
    unfold pr9Head bsProbePr9Head
    have := loadScratch_length_le h8 rChild slAncNode
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hPrNextLe : prNext.length ≤ 26 := by
    unfold prNext bsProbePrNext
    have := loadScratch_length_le h8 rClk slPredJ
    have := sweepInitStoreScratch_length_le h8 slPredJ rClk
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
  let pcChkBS := pcProbe + pr0.length + 1 + pr2.length + pr3.length + 2
  let pcChkAnc := pcChkBS + pr5.length + 2
  let pcDL2 := pcChkAnc + pr7.length + 3
  let pcAfterDL2 := pcDL2 + dlProg.toList.length
  let pcNextU := pcAfterDL2 + pr9Head.length + 2
  have hpcDL2Eq : pcDL2 = pcChkAnc + pr7.length + 3 := rfl
  have hpcNextUEq : pcNextU = pcAfterDL2 + pr9Head.length + 2 := rfl
  obtain ⟨hProbeBnd, hNextUBnd, hPr0Bnd, hPr0aBnd, hPr1Bnd, hPr2Bnd, hPr3Bnd, hChkBSBnd, hPr4Step1,
    _, hPr5aBnd, hPr5Step0, hPr5Step1, hChkAncBnd, hPr6Step1, hPr7Bnd, hAfterDL2Bnd, hNextBnd,
    hpl0, hpl1, hpl2, hpl3, hpl4, hpl5, hpl6, hpl7, hpl7b, hpl8, hpl9, hplNext⟩ :=
    sweepBSProbe_slice h8 hSz hpl
  clear hpl hSz
  -- Execute pr0
  have hpl0a : Placed code pcProbe (loadScratch h8 rClk slPredJ) := placed_append_left hpl0
  have hpl0b : Placed code (pcProbe + (loadScratch h8 rClk slPredJ).length) (loadScratch h8 rRem slRowHi) :=
    placed_right_eq hpl0 rfl
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rClk slPredJ hSlPJW (by decide)
    hpc hpl0a hPr0aBnd ho hSlPJ
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ := loadScratch_val_steps h8 (input := input) rRem slRowHi hSlRHW (by decide)
    pc1 hpl0b (by rw [Nat.add_assoc]; exact hPr0Bnd) ho1 (by rw [d1]; exact hSlRH)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hz1]
  have hclk2 : (reg s2 rClk).val = j := by rw [k2 _ (by decide) (by decide), r1]
  have hd2 : s2.data = s.data := d2.trans d1
  have hPr0Len : pr0.length = (loadScratch h8 rClk slPredJ).length + (loadScratch h8 rRem slRowHi).length := by
    simp [pr0, bsProbePr0]
  have hpc2 : s2.pc = pcProbe + pr0.length := by rw [pc2, Nat.add_assoc, ← hPr0Len]
  have hPre2 : Steps code input pr0.length s s2 := by
    have : pr0.length = (loadScratch h8 rClk slPredJ).length + (loadScratch h8 rRem slRowHi).length := rfl
    rw [this]; exact st1.append st2
  have hf1 : code[s2.pc]? = some (.branchLt rClk rRem (pcProbe + pr0.length + 1) pcProbeOk) :=
    placed_fetch hpl1 (i := 0) rfl hpc2
  by_cases hlt : j < rowHi
  · refine dite_eq_left hlt |>.mpr ?_
    obtain ⟨s3, st3, pc3, k3, d3⟩ := step_branchLt_true hf1 (by rw [hclk2, r2]; exact hlt) hPr1Bnd
    have ho3 : (reg s3 rOne).val = 1 := by rw [k3, ho2]
    have hz3 : (reg s3 rZero).val = 0 := by rw [k3, hz2]
    have hclk3 : (reg s3 rClk).val = j := by rw [k3, hclk2]
    have hd3 : s3.data = s.data := d3.trans hd2
    have hPre3 : Steps code input (pr0.length + 1) s s3 := hPre2.append (.cons st3 (.zero _))
    let u := (rows.row y)[j - rowLo]'(by omega)
    have hPBAddrW : predBufBase n m + j < workCap := hPBAddrW_fn j (Nat.lt_of_lt_of_le hlt hRHm)
    have hPBu : (s3.data[predBufBase n m + j]?).map Fin.val = some u.val := by
      have hp' := hPB ⟨j - rowLo, by omega⟩
      have hjEq : predBufBase H.vertexCount H.arcCount + rowLo + (j - rowLo) =
          predBufBase H.vertexCount H.arcCount + j := by omega
      change (s3.data[predBufBase H.vertexCount H.arcCount + j]?).map Fin.val = some u.val
      rw [hd3, ← hjEq]; exact hp'
    obtain ⟨hancPos, hancF, hancDep, q', hq', hBFq, hBSq, -⟩ := probe_ok_iff_ram inv (y := y) hmidPos hmidLe
    rw [← hancEq] at hancPos hancF hancDep hq' hBFq hBSq
    have hqEq : q' = q := by rw [hq] at hq'; cases hq'; rfl
    subst q'
    have hancLeN : ancNode ≤ n := by
      have h1 : ancNode < F.size := hancF
      rw [inv.grounded.size_eq] at h1
      exact Nat.le_trans (Nat.le_of_lt h1) (Nat.le_trans inv.sRefNextLe (by omega))
    have hBFAddrW : backFstBase n m + ancNode < workCap := hBFAddrW_fn ancNode hancLeN
    have hu1Lt : u.val + 1 < 2 ^ bits :=
      Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.add_lt_add_right u.isLt 1) hN1LtWork) hw
    have hj1Lt : j + 1 < 2 ^ bits :=
      Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt (Nat.le_trans hlt hRHm) hArcLtWork) hw
    obtain ⟨s11, hst23, pc11, hz11, ho11, hstk11, hch11, htmp11, hval11, hd11⟩ :=
      bsProbePr23_steps h8 input hSlPBW hSlAncW hSlBFW hPBAddrW hBFAddrW hu1Lt hpl2 hpl3
        hPr2Bnd hPr3Bnd pc3 hz3 ho3 hclk3
        (by rw [hd3]; exact inv.slPredBufVal) (by rw [hd3]; exact hSlAnc)
        (by rw [hd3]; exact inv.slBackFstVal) hPBu (by rw [hd3]; exact hBFq)
    have hd11' : s11.data = s.data := hd11.trans hd3
    have hpc11 : s11.pc = pcChkBS - 2 := by
      rw [pc11]; dsimp only [pcChkBS, pr0, pr2, pr3]; omega
    have hPre11 : Steps code input (pr0.length + 1 + pr2.length + pr3.length) s s11 := by
      rw [Nat.add_assoc (pr0.length + 1)]; exact hPre3.append hst23
    have finishNextU : ∀ {sx : State (layout bits inputCap workCap hi hw)} {kx : Nat},
        kx ≤ 145 + 60 * (OracleContract.L n + 1) →
        Steps code input kx s sx → sx.pc = pcNextU →
        (reg sx rZero).val = 0 → (reg sx rOne).val = 1 → sx.data = s.data →
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
          k ≤ 175 + 60 * (OracleContract.L n + 1) ∧
          Steps code input k s t ∧ t.pc = pcProbe ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
          (t.data[slPredJ]?).map Fin.val = some (j + 1) ∧
          ∀ w, w = slPredJ ∨ t.data[w]? = s.data[w]? := by
      intro sx kx hkx hstx hpcx hzx hox hdx
      obtain ⟨t, stTail, htpc, htz, hto, htPJ, htFr⟩ := bsProbePrNext_steps h8 input hSlPJW hj1Lt hplNext
        hNextBnd hProbeBnd hpcx hzx hox (by rw [hdx]; exact hSlPJ)
      have hkTot : kx + (bsProbePrNext h8 pcProbe).length ≤ 175 + 60 * (OracleContract.L n + 1) := by
        dsimp only [prNext] at hPrNextLe; omega
      exact ⟨t, kx + (bsProbePrNext h8 pcProbe).length, hkTot,
        hstx.append stTail, htpc, htz, hto, htPJ,
        fun w => (htFr w).elim Or.inl (fun h => Or.inr (by rw [h, hdx]))⟩
    have hBSAddrW : backSndBase n m + ancNode < workCap := hBSAddrW_fn ancNode hancLeN
    have hSlBS11 : (s11.data[slBackSnd]?).map Fin.val = some (backSndBase n m) := by
      rw [hd11']; exact inv.slBackSndVal
    have hBSq11 : (s11.data[backSndBase n m + ancNode]?).map Fin.val = some q.snd.val := by
      rw [hd11']; exact hBSq
    have hChk2 : 2 ≤ pcChkBS := by dsimp only [pcChkBS]; omega
    have hkx_base : pr0.length + 1 + pr2.length + pr3.length ≤ 66 := by omega
    have h456 := bsProbePr456_steps h8 input hPr5Le hChk2 rfl hPr4Step1 hChkBSBnd hPr5aBnd hPr5Step0 hPr5Step1
      hPr6Step1 hChkAncBnd hNextUBnd hSlBSW hBSAddrW hpl4 hpl5 hpl6 hpc11 hz11 ho11 hstk11 hch11
      htmp11 hval11 hSlBS11 hBSq11
    by_cases huPair : u = q.fst ∨ u = q.snd
    · have hCond : u = q.fst ∨ u = q.snd ∨
          (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
           F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode) :=
        huPair.elim Or.inl (fun h => Or.inr (Or.inl h))
      rw [ite_eq_left hCond]
      obtain ⟨s17, k456, hk456, st456, pc17, hz17, ho17, hd17⟩ := ite_elim_true huPair h456
      have hkx : pr0.length + 1 + pr2.length + pr3.length + k456 ≤ 145 + 60 * (OracleContract.L n + 1) :=
        Nat.le_trans (Nat.add_le_add hkx_base hk456)
          (Nat.le_trans (by decide : 66 + 18 ≤ 145) (Nat.le_add_right _ _))
      exact finishNextU hkx (hPre11.append st456) pc17 hz17 ho17 (hd17.trans hd11')
    · have huFst : u ≠ q.fst := fun h => huPair (Or.inl h)
      have huSnd : u ≠ q.snd := fun h => huPair (Or.inr h)
      obtain ⟨s16, k456, hk456, st456, pc16, hz16, ho16, hstk16, hch16, hd16⟩ := ite_elim_false huPair h456
      have hkPre : pr0.length + 1 + pr2.length + pr3.length + k456 ≤ 85 :=
        Nat.le_trans (Nat.add_le_add hkx_base hk456) (by decide : 66 + 18 ≤ 85)
      exact bsProbeChkAnc_steps h8 input inv hWork hidx huFst huSnd hancF hancLeN hj1Lt
        hSlLabW hSlJW hSlAncW hSlPJW hpcDL2Eq hpcNextUEq hFailBnd hProbeBnd hPr7Bnd
        hAfterDL2Bnd hNextUBnd hNextBnd hPr7Le hPr9HLe hPrNextLe
        hpl7 hpl7b hpl8 hpl9 hplNext hkPre (hPre11.append st456) (hd16.trans hd11') pc16 hz16 ho16 hstk16 hch16
        hSlPJ hSlAnc
  · refine dite_eq_right hlt |>.mpr ?_
    have hge : rowHi ≤ j := Nat.le_of_not_lt hlt
    obtain ⟨s3, st3, pc3, k3, d3⟩ := step_branchLt_false hf1 (by rw [r2, hclk2]; exact hge) hOkBnd
    have hkx : pr0.length + 1 ≤ 30 := Nat.le_trans (Nat.add_le_add_right hPr0Le 1) (by decide)
    exact ⟨s3, pr0.length + 1, hkx, hPre2.append (.cons st3 (.zero _)), pc3,
      by rw [k3, hz2], by rw [k3, ho2], d3.trans hd2⟩

private theorem sweepBSProbe_loop_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcProbe pcProbeOk pcProbeFail : Nat}
    (hOkBnd : pcProbeOk < code.size) (hFailBnd : pcProbeFail < code.size)
    (hSz : pcProbe + (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length < code.size)
    (hpl : Placed code pcProbe (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail))
    {y m_y : Vertex H} {mid ancNode : Nat} {q : CutPair H} {rowLo rowHi : Nat}
    (hmidPos : 0 < mid) (hmidLe : mid ≤ F.depthOf (sRef.labelAt m_y.val))
    (hancEq : ancNode = F.ancestorAtDepth (sRef.labelAt m_y.val) mid)
    (hq : sRef.tables.back[ancNode]? = some (some q))
    (hRHm : rowHi ≤ H.arcCount) (hDiff : rowHi - rowLo = (rows.row y).length) :
    ∀ rem j : Nat, ∀ s : State (layout bits inputCap workCap hi hw),
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s →
      idx < H.vertexCount →
      rowLo ≤ j → j ≤ rowHi → rowHi - j = rem →
      (∀ t' : Fin (rows.row y).length,
        (s.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
          some ((rows.row y)[t'.val]'t'.isLt).val) →
      s.pc = pcProbe →
      (reg s rZero).val = 0 → (reg s rOne).val = 1 →
      (s.data[slPredJ]?).map Fin.val = some j →
      (s.data[slRowHi]?).map Fin.val = some rowHi →
      (s.data[slAncNode]?).map Fin.val = some ancNode →
      let tailOk := ∀ t' : Fin (rows.row y).length, j - rowLo ≤ t'.val →
        let u := (rows.row y)[t'.val]'t'.isLt
        u = q.fst ∨ u = q.snd ∨
          (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
           F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode)
      if tailOk then
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
          k ≤ 30 + rem * (175 + 60 * (OracleContract.L H.vertexCount + 1)) ∧
          Steps code input k s t ∧ t.pc = pcProbeOk ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
          ∀ w, w = slPredJ ∨ t.data[w]? = s.data[w]?
      else
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
          k ≤ 30 + rem * (175 + 60 * (OracleContract.L H.vertexCount + 1)) ∧
          Steps code input k s t ∧ t.pc = pcProbeFail ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
          ∀ w, w = slPredJ ∨ t.data[w]? = s.data[w]? := by
  intro rem
  induction rem with
  | zero =>
    intro j s inv hidx hRLleJ hjLeRH hRemEq hPB hpc hz ho hSlPJ hSlRH hSlAnc
    have hjEq : j = rowHi := by omega
    have hltFalse : ¬ j < rowHi := by omega
    have hTailOk : ∀ t' : Fin (rows.row y).length, j - rowLo ≤ t'.val →
        let u := (rows.row y)[t'.val]'t'.isLt
        u = q.fst ∨ u = q.snd ∨
          (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
           F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode) := by
      intro t' ht'; have := t'.isLt; omega
    have hIt := sweepBSProbe_iter_step h8 (input := input) inv hWork hidx hOkBnd hFailBnd hSz hpl hmidPos hmidLe hancEq hq
      hRLleJ hjLeRH hRHm hDiff hPB hpc hz ho hSlPJ hSlRH hSlAnc
    rw [dite_eq_right hltFalse] at hIt
    obtain ⟨t, k, hk, hst, htpc, htz, hto, htd⟩ := hIt
    refine ite_true_branch hTailOk ⟨t, k, by omega, hst, htpc, htz, hto, fun w => Or.inr (by rw [htd])⟩
  | succ rem' ih =>
    intro j s inv hidx hRLleJ hjLeRH hRemEq hPB hpc hz ho hSlPJ hSlRH hSlAnc
    have hlt : j < rowHi := by omega
    have hIt := sweepBSProbe_iter_step h8 (input := input) inv hWork hidx hOkBnd hFailBnd hSz hpl hmidPos hmidLe hancEq hq
      hRLleJ hjLeRH hRHm hDiff hPB hpc hz ho hSlPJ hSlRH hSlAnc
    rw [dite_eq_left hlt] at hIt
    let u := (rows.row y)[j - rowLo]'(by omega)
    by_cases huOk : u = q.fst ∨ u = q.snd ∨
        (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
         F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode)
    · rw [ite_eq_left huOk] at hIt
      obtain ⟨s1, k1, hk1, st1, pc1, hz1, ho1, hSlPJ1, hFr1⟩ := hIt
      have hScrNe : ∀ sl, sl < 27 → s1.data[sl]? = s.data[sl]? := fun sl hsl =>
        (hFr1 sl).elim (fun h => by unfold slPredJ at h; omega) id
      have hGe30 : ∀ w, 30 ≤ w → s1.data[w]? = s.data[w]? := fun w hw' =>
        (hFr1 w).elim (fun h => by unfold slPredJ at h; omega) id
      have hInv1 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
          (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s1 := by
        have hOrd : 30 ≤ orderBase H.vertexCount H.arcCount := by
          have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide); omega
        have h19 : ∀ sl, sl < 19 → s1.data[sl]? = s.data[sl]? := fun sl hsl => hScrNe sl (by omega)
        have hHi : ∀ w, orderBase H.vertexCount H.arcCount ≤ w → s1.data[w]? = s.data[w]? :=
          fun w hw' => hGe30 w (by omega)
        have hSt1 : Stage1Output H s1 order size_order rank rows :=
          { inv.stage1 with
            order_mem := fun i => by rw [hHi _ (by omega)]; exact inv.stage1.order_mem i
            ranks_mem := fun v => by
              rw [hHi _ (by simp only [ranksBase, orderBase]; omega)]; exact inv.stage1.ranks_mem v
            rows_mem := fun v => by
              obtain ⟨lo', hi'', hS, hE, hLoLe, hHiArc, hL', hP'⟩ := inv.stage1.rows_mem v
              refine ⟨lo', hi'', ?_, ?_, hLoLe, hHiArc, hL', fun t' => ?_⟩
              · rw [hHi _ (by simp only [rowStartBase, ranksBase, orderBase]; omega)]; exact hS
              · rw [hHi _ (by simp only [rowEndBase, rowStartBase, ranksBase, orderBase]; omega)]; exact hE
              · rw [hHi _ (by simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega)]; exact hP' t' }
        exact
          { idxLe := inv.idxLe, sRefLabelsSize := inv.sRefLabelsSize, sRefNextLe := inv.sRefNextLe,
            labelsLt := inv.labelsLt, backPos := inv.backPos, grounded := inv.grounded, stage1 := hSt1,
            slNVal := by rw [h19 _ (by decide)]; exact inv.slNVal,
            slRootVal := by rw [h19 _ (by decide)]; exact inv.slRootVal,
            slNextVal := by rw [h19 _ (by decide)]; exact inv.slNextVal,
            slDictBaseVal := by rw [h19 _ (by decide)]; exact inv.slDictBaseVal,
            slDictCntVal := by rw [h19 _ (by decide)]; exact inv.slDictCntVal,
            slDictSndVal := by rw [h19 _ (by decide)]; exact inv.slDictSndVal,
            slDictSlotsVal := by rw [h19 _ (by decide)]; exact inv.slDictSlotsVal,
            slJumpVal := by rw [h19 _ (by decide)]; exact inv.slJumpVal,
            slBackFstVal := by rw [h19 _ (by decide)]; exact inv.slBackFstVal,
            slBackSndVal := by rw [h19 _ (by decide)]; exact inv.slBackSndVal,
            slLabelsVal := by rw [h19 _ (by decide)]; exact inv.slLabelsVal,
            slParentsVal := by rw [h19 _ (by decide)]; exact inv.slParentsVal,
            slOrderVal := by rw [h19 _ (by decide)]; exact inv.slOrderVal,
            slRanksVal := by rw [h19 _ (by decide)]; exact inv.slRanksVal,
            slRowStartVal := by rw [h19 _ (by decide)]; exact inv.slRowStartVal,
            slRowEndVal := by rw [h19 _ (by decide)]; exact inv.slRowEndVal,
            slPredBufVal := by rw [h19 _ (by decide)]; exact inv.slPredBufVal,
            slSourceVal := by rw [h19 _ (by decide)]; exact inv.slSourceVal,
            slIdxVal := by rw [h19 _ (by decide)]; exact inv.slIdxVal,
            records := by
              have hr := inv.records
              have hEqJ : ∀ w, jumpBase H.vertexCount H.arcCount ≤ w → s1.data[w]? = s.data[w]? := fun w hw' => by
                apply hGe30; have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
                simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
                  predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
              exact ⟨hr.valid, by rw [s1.data_size, ← s.data_size]; exact hr.fit,
                fun v hv => by rw [hEqJ _ (by omega)]; exact hr.parent v hv,
                fun v hv => by rw [hEqJ _ (by omega)]; exact hr.depth v hv,
                fun v hv => by rw [hEqJ _ (by omega)]; exact hr.jump v hv⟩,
            dictHeader := by
              rw [hHi _ (by simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
                predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega)]; exact inv.dictHeader,
            dictKeys := fun i hi' => by
              have hb : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount + 1 + i := by
                simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
                  predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
              have hb2 : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount + 1 +
                  (orderedConfig dictRows large).dict.size + i := by omega
              rw [hHi _ hb, hHi _ hb2]; exact inv.dictKeys i hi',
            dictSlots := fun i hi' => by
              have hb : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount + 1 +
                  2 * (orderedConfig dictRows large).dict.size + i := by
                simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
                  predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
              rw [hHi _ hb]; exact inv.dictSlots i hi',
            backMem := fun k hk => by
              have hO : orderBase H.vertexCount H.arcCount ≤ backFstBase H.vertexCount H.arcCount := by
                simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
                  predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
              have hO2 : backFstBase H.vertexCount H.arcCount ≤ backSndBase H.vertexCount H.arcCount := by
                simp only [backSndBase]; omega
              rw [hHi _ (by omega), hHi _ (by omega)]; exact inv.backMem k hk,
            labelsMem := fun v => by
              have hO : orderBase H.vertexCount H.arcCount ≤ labelsBase H.vertexCount H.arcCount := by
                simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
                  candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
              rw [hHi _ (by omega)]; exact inv.labelsMem v,
            parentsMem := fun v hv => by
              have hO : orderBase H.vertexCount H.arcCount ≤ parentsBase H.vertexCount H.arcCount := by
                simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
                  candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
              rw [hHi _ (by omega)]; exact inv.parentsMem v hv }
      have hPB1 : ∀ t' : Fin (rows.row y).length,
          (s1.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
            some ((rows.row y)[t'.val]'t'.isLt).val := by
        intro t'
        have h30 : 30 ≤ predBufBase H.vertexCount H.arcCount + rowLo + t'.val := by
          have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
          simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
        rw [hGe30 _ h30]; exact hPB t'
      have hRec := ih (j + 1) s1 hInv1 hidx (by omega) (by omega) (by omega) hPB1 pc1 hz1 ho1
        hSlPJ1 (by rw [hScrNe _ (by decide)]; exact hSlRH) (by rw [hScrNe _ (by decide)]; exact hSlAnc)
      have hTailIff : (∀ t' : Fin (rows.row y).length, j - rowLo ≤ t'.val →
            let u' := (rows.row y)[t'.val]'t'.isLt
            u' = q.fst ∨ u' = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u'.val) ∧
               F.ancestorAtDepth (sRef.labelAt u'.val) (F.depthOf ancNode) = ancNode)) ↔
          (∀ t' : Fin (rows.row y).length, j + 1 - rowLo ≤ t'.val →
            let u' := (rows.row y)[t'.val]'t'.isLt
            u' = q.fst ∨ u' = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u'.val) ∧
               F.ancestorAtDepth (sRef.labelAt u'.val) (F.depthOf ancNode) = ancNode)) := by
        constructor
        · intro h t' ht'; exact h t' (by omega)
        · intro h t' ht'
          by_cases hEq : t'.val = j - rowLo
          · have huEq : (rows.row y)[t'.val]'t'.isLt = u := by dsimp only [u]; simp only [hEq]
            rw [huEq]; exact huOk
          · exact h t' (by omega)
      by_cases hTail1 : ∀ t' : Fin (rows.row y).length, j + 1 - rowLo ≤ t'.val →
          let u' := (rows.row y)[t'.val]'t'.isLt
          u' = q.fst ∨ u' = q.snd ∨
            (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u'.val) ∧
             F.ancestorAtDepth (sRef.labelAt u'.val) (F.depthOf ancNode) = ancNode)
      · obtain ⟨t, k2, hk2, st2, pct, hzt, hot, hFr2⟩ := ite_elim_true hTail1 hRec
        refine ite_true_branch (hTailIff.mpr hTail1)
          ⟨t, k1 + k2, by simp only [Nat.succ_mul] at hk2 ⊢; omega, st1.append st2, pct, hzt, hot,
            fun w => (hFr2 w).elim Or.inl (fun h => by rw [h]; exact hFr1 w)⟩
      · obtain ⟨t, k2, hk2, st2, pct, hzt, hot, hFr2⟩ := ite_elim_false hTail1 hRec
        have hNot : ¬ ∀ t' : Fin (rows.row y).length, j + 1 - rowLo ≤ t'.val →
            let u' := (rows.row y)[t'.val]'t'.isLt
            u' = q.fst ∨ u' = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u'.val) ∧
               F.ancestorAtDepth (sRef.labelAt u'.val) (F.depthOf ancNode) = ancNode) := hTail1
        have hNot' : ¬ ∀ t' : Fin (rows.row y).length, j - rowLo ≤ t'.val →
            let u' := (rows.row y)[t'.val]'t'.isLt
            u' = q.fst ∨ u' = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u'.val) ∧
               F.ancestorAtDepth (sRef.labelAt u'.val) (F.depthOf ancNode) = ancNode) :=
          fun h => hNot (hTailIff.mp h)
        refine ite_false_branch hNot'
          ⟨t, k1 + k2, by simp only [Nat.succ_mul] at hk2 ⊢; omega, st1.append st2, pct, hzt, hot,
            fun w => (hFr2 w).elim Or.inl (fun h => by rw [h]; exact hFr1 w)⟩
    · rw [ite_eq_right huOk] at hIt
      obtain ⟨t, k1, hk1, st1, pct, hzt, hot, hdt⟩ := hIt
      have hNot : ¬ ∀ t' : Fin (rows.row y).length, j - rowLo ≤ t'.val →
          let u' := (rows.row y)[t'.val]'t'.isLt
          u' = q.fst ∨ u' = q.snd ∨
            (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u'.val) ∧
             F.ancestorAtDepth (sRef.labelAt u'.val) (F.depthOf ancNode) = ancNode) := by
        intro h
        exact huOk (h ⟨j - rowLo, by omega⟩ (Nat.le_refl _))
      refine ite_false_branch hNot
        ⟨t, k1, by simp only [Nat.succ_mul] at hk1 ⊢; omega, st1, pct, hzt, hot,
          fun w => Or.inr (by rw [hdt])⟩

private theorem measuredSearch_cut_eq_of_le
    (p : Nat → PaperB.ForestHead.Probe) :
    ∀ f1 f2 lo hi : Nat,
      lo < hi → hi - lo ≤ 2 ^ f1 → hi - lo ≤ 2 ^ f2 →
      (PaperB.ForestHead.measuredSearch p f1 lo hi).cut =
        (PaperB.ForestHead.measuredSearch p f2 lo hi).cut := by
  intro f1
  induction f1 with
  | zero =>
    intro f2 lo hi hlt h1 h2
    have hle1 : hi ≤ lo + 1 := by simp at h1; omega
    rw [measuredSearch_while p 0 lo hi hlt h1, measuredSearch_while p f2 lo hi hlt h2]
    simp [hle1]
  | succ f1' ih =>
    intro f2 lo hi hlt h1 h2
    by_cases hle1 : hi ≤ lo + 1
    · rw [measuredSearch_while p (f1' + 1) lo hi hlt h1, measuredSearch_while p f2 lo hi hlt h2]
      simp [hle1]
    · have hf2Pos : 0 < f2 := by
        rcases Nat.eq_zero_or_pos f2 with rfl | hPos
        · simp at h2; omega
        · exact hPos
      obtain ⟨f2', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : f2 ≠ 0)
      rw [measuredSearch_while p (f1' + 1) lo hi hlt h1, measuredSearch_while p (f2' + 1) lo hi hlt h2]
      simp only [hle1, ↓reduceIte, Nat.add_sub_cancel]
      let mid := lo + (hi - lo) / 2
      have h1L : mid - lo ≤ 2 ^ f1' := by rw [Nat.pow_succ] at h1; dsimp only [mid]; omega
      have h1R : hi - mid ≤ 2 ^ f1' := by rw [Nat.pow_succ] at h1; dsimp only [mid]; omega
      have h2L : mid - lo ≤ 2 ^ f2' := by rw [Nat.pow_succ] at h2; dsimp only [mid]; omega
      have h2R : hi - mid ≤ 2 ^ f2' := by rw [Nat.pow_succ] at h2; dsimp only [mid]; omega
      by_cases hok : (p (lo + (hi - lo) / 2)).ok = true
      · simp only [hok, ↓reduceIte]; exact ih f2' mid hi (by dsimp only [mid]; omega) h1R h2R
      · simp only [hok, Bool.false_eq_true, ↓reduceIte]; exact ih f2' lo mid (by dsimp only [mid]; omega) h1L h2L

private theorem sweepInv_update_bs23_27 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)] {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s t : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (h19 : ∀ sl, sl < 19 → t.data[sl]? = s.data[sl]?)
    (h30 : ∀ w, 30 ≤ w → t.data[w]? = s.data[w]?) :
    SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx t := by
  have hOrd : 30 ≤ orderBase H.vertexCount H.arcCount := by
    have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide); omega
  have hHi : ∀ w, orderBase H.vertexCount H.arcCount ≤ w → t.data[w]? = s.data[w]? :=
    fun w hw' => h30 w (by omega)
  have hSt1 : Stage1Output H t order size_order rank rows :=
    { inv.stage1 with
      order_mem := fun i => by rw [hHi _ (by omega)]; exact inv.stage1.order_mem i
      ranks_mem := fun v => by
        rw [hHi _ (by simp only [ranksBase, orderBase]; omega)]; exact inv.stage1.ranks_mem v
      rows_mem := fun v => by
        obtain ⟨lo', hi'', hS, hE, hLoLe, hHiArc, hL', hP'⟩ := inv.stage1.rows_mem v
        refine ⟨lo', hi'', ?_, ?_, hLoLe, hHiArc, hL', fun t' => ?_⟩
        · rw [hHi _ (by simp only [rowStartBase, ranksBase, orderBase]; omega)]; exact hS
        · rw [hHi _ (by simp only [rowEndBase, rowStartBase, ranksBase, orderBase]; omega)]; exact hE
        · rw [hHi _ (by simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega)]; exact hP' t' }
  exact
    { idxLe := inv.idxLe, sRefLabelsSize := inv.sRefLabelsSize, sRefNextLe := inv.sRefNextLe,
      labelsLt := inv.labelsLt, backPos := inv.backPos, grounded := inv.grounded, stage1 := hSt1,
      slNVal := by rw [h19 _ (by decide)]; exact inv.slNVal,
      slRootVal := by rw [h19 _ (by decide)]; exact inv.slRootVal,
      slNextVal := by rw [h19 _ (by decide)]; exact inv.slNextVal,
      slDictBaseVal := by rw [h19 _ (by decide)]; exact inv.slDictBaseVal,
      slDictCntVal := by rw [h19 _ (by decide)]; exact inv.slDictCntVal,
      slDictSndVal := by rw [h19 _ (by decide)]; exact inv.slDictSndVal,
      slDictSlotsVal := by rw [h19 _ (by decide)]; exact inv.slDictSlotsVal,
      slJumpVal := by rw [h19 _ (by decide)]; exact inv.slJumpVal,
      slBackFstVal := by rw [h19 _ (by decide)]; exact inv.slBackFstVal,
      slBackSndVal := by rw [h19 _ (by decide)]; exact inv.slBackSndVal,
      slLabelsVal := by rw [h19 _ (by decide)]; exact inv.slLabelsVal,
      slParentsVal := by rw [h19 _ (by decide)]; exact inv.slParentsVal,
      slOrderVal := by rw [h19 _ (by decide)]; exact inv.slOrderVal,
      slRanksVal := by rw [h19 _ (by decide)]; exact inv.slRanksVal,
      slRowStartVal := by rw [h19 _ (by decide)]; exact inv.slRowStartVal,
      slRowEndVal := by rw [h19 _ (by decide)]; exact inv.slRowEndVal,
      slPredBufVal := by rw [h19 _ (by decide)]; exact inv.slPredBufVal,
      slSourceVal := by rw [h19 _ (by decide)]; exact inv.slSourceVal,
      slIdxVal := by rw [h19 _ (by decide)]; exact inv.slIdxVal,
      records := by
        have hr := inv.records
        have hEqJ : ∀ w, jumpBase H.vertexCount H.arcCount ≤ w → t.data[w]? = s.data[w]? := fun w hw' => by
          apply h30; have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
          simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
            predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
        exact ⟨hr.valid, by rw [t.data_size, ← s.data_size]; exact hr.fit,
          fun v hv => by rw [hEqJ _ (by omega)]; exact hr.parent v hv,
          fun v hv => by rw [hEqJ _ (by omega)]; exact hr.depth v hv,
          fun v hv => by rw [hEqJ _ (by omega)]; exact hr.jump v hv⟩,
      dictHeader := by
        rw [hHi _ (by simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega)]; exact inv.dictHeader,
      dictKeys := fun i hi' => by
        have hb : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount + 1 + i := by
          simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
            predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
        have hb2 : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount + 1 +
            (orderedConfig dictRows large).dict.size + i := by omega
        rw [hHi _ hb, hHi _ hb2]; exact inv.dictKeys i hi',
      dictSlots := fun i hi' => by
        have hb : orderBase H.vertexCount H.arcCount ≤ dictBase H.vertexCount H.arcCount + 1 +
            2 * (orderedConfig dictRows large).dict.size + i := by
          simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
            predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
        rw [hHi _ hb]; exact inv.dictSlots i hi',
      backMem := fun k hk => by
        have hO : orderBase H.vertexCount H.arcCount ≤ backFstBase H.vertexCount H.arcCount := by
          simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
            predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
        have hO2 : backFstBase H.vertexCount H.arcCount ≤ backSndBase H.vertexCount H.arcCount := by
          simp only [backSndBase]; omega
        rw [hHi _ (by omega), hHi _ (by omega)]; exact inv.backMem k hk,
      labelsMem := fun v => by
        have hO : orderBase H.vertexCount H.arcCount ≤ labelsBase H.vertexCount H.arcCount := by
          simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
            candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
        rw [hHi _ (by omega)]; exact inv.labelsMem v,
      parentsMem := fun v hv => by
        have hO : orderBase H.vertexCount H.arcCount ≤ parentsBase H.vertexCount H.arcCount := by
          simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
            candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
        rw [hHi _ (by omega)]; exact inv.parentsMem v hv }

private theorem sweepBSUpdateBound_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {slBound pcEntry pcBS mid : Nat}
    (hSlMidW : slMidBS < workCap) (hSlBW : slBound < workCap) (hSlBFit : slBound < 256)
    (hBSBnd : pcBS < code.size)
    (hEndBnd : pcEntry + (loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slBound rVal ++ [Instr.goto pcBS]).length < code.size)
    (hpl : Placed code pcEntry (loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slBound rVal ++ [Instr.goto pcBS]))
    {s2 : State (layout bits inputCap workCap hi hw)}
    (pc2 : s2.pc = pcEntry) (hz2 : (reg s2 rZero).val = 0) (ho2 : (reg s2 rOne).val = 1)
    (hMid2 : (s2.data[slMidBS]?).map Fin.val = some mid) :
    ∃ s3 : State (layout bits inputCap workCap hi hw),
      Steps code input (loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slBound rVal ++ [Instr.goto pcBS]).length s2 s3 ∧
      s3.pc = pcBS ∧ (reg s3 rZero).val = 0 ∧ (reg s3 rOne).val = 1 ∧
      (s3.data[slBound]?).map Fin.val = some mid ∧
      ∀ j, j ≠ slBound → s3.data[j]? = s2.data[j]? := by
  let p1 := loadScratch h8 rVal slMidBS
  let p2 := sweepInitStoreScratch h8 slBound rVal
  have hLen : (p1 ++ p2 ++ [Instr.goto pcBS]).length = p1.length + p2.length + 1 := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hpl12 := placed_append_left hpl
  have hpl1 : Placed code pcEntry p1 := placed_append_left hpl12
  have hpl2 : Placed code (pcEntry + p1.length) p2 := placed_right_eq hpl12 rfl
  have hpl3 : Placed code (pcEntry + p1.length + p2.length) ([Instr.goto pcBS] : List (Instr bits 15)) :=
    placed_right_eq hpl (by simp only [p1, p2, List.length_append, Nat.add_assoc])
  obtain ⟨s3a, st3a, pc3a, r3a, d3a, k3a⟩ := loadScratch_val_steps h8 (input := input) rVal slMidBS
    hSlMidW (by decide) pc2 hpl1 (by
      change pcEntry + (p1 ++ p2 ++ [Instr.goto pcBS]).length < code.size at hEndBnd
      rw [hLen] at hEndBnd; dsimp only [p1] at hEndBnd; omega)
    ho2 hMid2
  have ho3a : (reg s3a rOne).val = 1 := by rw [k3a _ (by decide) (by decide), ho2]
  have hz3a : (reg s3a rZero).val = 0 := by rw [k3a _ (by decide) (by decide), hz2]
  obtain ⟨s3b, st3b, pc3b, hB3b, hFr3b, k3b⟩ := storeScratch_val_steps h8 (input := input) slBound rVal
    hSlBFit (by decide) hSlBW pc3a hpl2 (by
      change pcEntry + (p1 ++ p2 ++ [Instr.goto pcBS]).length < code.size at hEndBnd
      rw [hLen] at hEndBnd; dsimp only [p1, p2] at hEndBnd; omega)
    ho3a
  have ho3b : (reg s3b rOne).val = 1 := by rw [k3b _ (by decide), ho3a]
  have hz3b : (reg s3b rZero).val = 0 := by rw [k3b _ (by decide), hz3a]
  have hgf : code[s3b.pc]? = some (Instr.goto pcBS) := placed_fetch hpl3 (i := 0) rfl pc3b
  let s3 : State (layout bits inputCap workCap hi hw) := { s3b with pc := pcBS }
  have hgt3c : step code input s3b = some (.next s3) := step_goto_at hgf hBSBnd
  refine ⟨s3, ?_, rfl, hz3b, ho3b, ?_, fun j hj => ?_⟩
  · change Steps code input (p1 ++ p2 ++ [Instr.goto pcBS]).length s2 s3
    rw [hLen]; exact (st3a.append st3b).append (Steps.cons hgt3c (Steps.zero _))
  · change (s3b.data[slBound]?).map Fin.val = some mid; rw [hB3b, r3a]
  · change s3b.data[j]? = s2.data[j]?; rw [hFr3b j hj, d3a]

theorem sweepBSBlock_while {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hidx : idx < H.vertexCount)
    {pcBS pcAfterBS : Nat}
    (hAfterBnd : pcAfterBS < code.size)
    (hSz : pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcAfterBS).length < code.size)
    (hpl : Placed code pcBS (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcAfterBS))
    {y m_y : Vertex H} {rowLo rowHi : Nat}
    (hRLleRH : rowLo ≤ rowHi) (hRHm : rowHi ≤ H.arcCount)
    (hDiff : rowHi - rowLo = (rows.row y).length) :
    ∀ fuel lo hi' : Nat, ∀ s : State (layout bits inputCap workCap hi hw),
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s →
      lo < hi' → hi' ≤ F.depthOf (sRef.labelAt m_y.val) + 1 → hi' - lo ≤ 2 ^ fuel →
      (∀ t' : Fin (rows.row y).length,
        (s.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
          some ((rows.row y)[t'.val]'t'.isLt).val) →
      s.pc = pcBS → (reg s rZero).val = 0 → (reg s rOne).val = 1 →
      (s.data[slLoBS]?).map Fin.val = some lo →
      (s.data[slHiBS]?).map Fin.val = some hi' →
      (s.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val) →
      (s.data[slRowLo]?).map Fin.val = some rowLo →
      (s.data[slRowHi]?).map Fin.val = some rowHi →
      let c := orderedConfig dictRows large
      let p : Nat → PaperB.ForestHead.Probe :=
        fun d => PaperB.ForestHead.probe (selectors c sRef) (rows.row y) m_y d
      let cut := (PaperB.ForestHead.measuredSearch p fuel lo hi').cut
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 35 + fuel * ((rows.row y).length + 1) * (175 + 60 * (OracleContract.L H.vertexCount + 1)) ∧
        Steps code input k s t ∧ t.pc = pcAfterBS ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (t.data[slLoBS]?).map Fin.val = some cut ∧
        ∀ w, w = slLoBS ∨ w = slHiBS ∨ w = slMidBS ∨ w = slAncNode ∨ w = slPredJ ∨ t.data[w]? = s.data[w]? := by
  intro fuel
  let hdr := sweepBSHeader (hi := hi) (hw := hw) h8 pcBS pcAfterBS
  let pcProbe := pcBS + hdr.length
  let prDummy := (sweepBSProbe (hi := hi) (hw := hw) h8 0 0 0).length
  let pcProbeOk := pcProbe + prDummy
  let prOk := loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slLoBS rVal ++ [.goto pcBS]
  let pcProbeFail := pcProbeOk + prOk.length
  let prFail := loadScratch h8 rVal slMidBS ++ sweepInitStoreScratch h8 slHiBS rVal ++ [.goto pcBS]
  have hLenBlk : (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcAfterBS).length =
      hdr.length + (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length +
        prOk.length + prFail.length := by
    unfold sweepBSBlock
    dsimp only [hdr, pcProbe, prDummy, pcProbeOk, pcProbeFail, prOk, prFail]
    simp only [List.length_append]
  have hSzTot : pcBS + (hdr.length +
      (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length +
        prOk.length + prFail.length) < code.size := by
    rw [← hLenBlk]; exact hSz
  have hBSBnd : pcBS < code.size := by omega
  have hHdrBnd : pcBS + hdr.length < code.size := by omega
  have hPrBnd : pcProbe + (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail).length <
      code.size := by dsimp only [pcProbe] at hSzTot ⊢; omega
  have hOkBnd : pcProbeOk < code.size := by
    dsimp only [pcProbeOk, pcProbe, prDummy]
    rw [← sweepBSProbe_length h8 pcProbe pcProbeOk pcProbeFail]; exact hPrBnd
  have hFailBnd : pcProbeFail < code.size := by
    dsimp only [pcProbeFail, pcProbeOk, pcProbe, prDummy]
    rw [← sweepBSProbe_length h8 pcProbe pcProbeOk pcProbeFail]; omega
  have hOkEndBnd : pcProbeOk + prOk.length < code.size := by
    dsimp only [pcProbeOk, pcProbe, prDummy]
    rw [← sweepBSProbe_length h8 pcProbe pcProbeOk pcProbeFail]; omega
  have hFailEndBnd : pcProbeFail + prFail.length < code.size := by
    dsimp only [pcProbeFail, pcProbeOk, pcProbe, prDummy]
    rw [← sweepBSProbe_length h8 pcProbe pcProbeOk pcProbeFail]; omega
  have hOkLe : prOk.length ≤ 25 := by
    have := loadScratch_length_le h8 rVal slMidBS
    have := sweepInitStoreScratch_length_le h8 slLoBS rVal
    dsimp only [prOk]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hFailLe : prFail.length ≤ 25 := by
    have := loadScratch_length_le h8 rVal slMidBS
    have := sweepInitStoreScratch_length_le h8 slHiBS rVal
    dsimp only [prFail]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hSlMidW : slMidBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlLoW : slLoBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlHiW : slHiBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  unfold sweepBSBlock at hpl
  dsimp only at hpl
  have h012 := placed_append_left hpl
  have h01 := placed_append_left h012
  have hplHdr : Placed code pcBS hdr := placed_append_left h01
  have hplProbe : Placed code pcProbe (sweepBSProbe (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail) :=
    placed_right_eq h01 rfl
  have hLenPr := sweepBSProbe_length (hi := hi) (hw := hw) h8 pcProbe pcProbeOk pcProbeFail
  have hplOk : Placed code pcProbeOk prOk :=
    placed_right_eq h012 (by
      dsimp only [pcProbeOk, pcProbe, prDummy, hdr]
      rw [List.length_append, hLenPr]
      omega)
  have hplFail : Placed code pcProbeFail prFail :=
    placed_right_eq hpl (by
      have hLenPr' := hLenPr
      dsimp only [pcProbeFail, pcProbeOk, pcProbe, prDummy, hdr, prOk] at hLenPr' ⊢
      simp only [List.length_append] at hLenPr' ⊢
      rw [hLenPr']
      omega)
  clear hpl h012 h01
  let stepCost := ((rows.row y).length + 1) * (175 + 60 * (OracleContract.L H.vertexCount + 1))
  have hCostGe : 175 + 60 * (OracleContract.L H.vertexCount + 1) ≤ stepCost :=
    Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  induction fuel with
  | zero =>
    intro lo hi' s inv hLoLt hHiLe hSpan hPB hpc hz ho hSlLo hSlHi hSlM hSlRL hSlRH
    have hle1 : hi' ≤ lo + 1 := by simp at hSpan; omega
    have hHdr := sweepBSHeader_steps h8 (input := input) inv hWork hidx hAfterBnd hHdrBnd hplHdr m_y hLoLt hHiLe
      (Nat.le_trans hRLleRH hRHm) hpc hz ho hSlLo hSlHi hSlM hSlRL
    rw [ite_eq_left hle1] at hHdr
    obtain ⟨t, k, hk, st, pct, zt, ot, dt⟩ := hHdr
    refine ⟨t, k, by omega, st, pct, zt, ot, ?_, fun w => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [dt])))))⟩
    rw [measuredSearch_while _ 0 lo hi' hLoLt hSpan]; simp only [hle1, ↓reduceIte]
    rw [dt]; exact hSlLo
  | succ f ih =>
    intro lo hi' s inv hLoLt hHiLe hSpan hPB hpc hz ho hSlLo hSlHi hSlM hSlRL hSlRH
    have hHdr := sweepBSHeader_steps h8 (input := input) inv hWork hidx hAfterBnd hHdrBnd hplHdr m_y hLoLt hHiLe
      (Nat.le_trans hRLleRH hRHm) hpc hz ho hSlLo hSlHi hSlM hSlRL
    by_cases hle1 : hi' ≤ lo + 1
    · rw [ite_eq_left hle1] at hHdr
      obtain ⟨t, k, hk, st, pct, zt, ot, dt⟩ := hHdr
      refine ⟨t, k, by omega, st, pct, zt, ot, ?_, fun w => Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [dt])))))⟩
      rw [measuredSearch_while _ (f + 1) lo hi' hLoLt hSpan]; simp only [hle1, ↓reduceIte]
      rw [dt]; exact hSlLo
    · rw [ite_eq_right hle1] at hHdr
      obtain ⟨s1, k1, hk1, st1, pc1, hz1, ho1, _, hMid1, hAnc1, hPJ1, hFr1⟩ := hHdr
      let mid := lo + (hi' - lo) / 2
      let ancNode := F.ancestorAtDepth (sRef.labelAt m_y.val) mid
      have hmidPos : 0 < mid := by dsimp only [mid]; omega
      have hmidLe : mid ≤ F.depthOf (sRef.labelAt m_y.val) := by dsimp only [mid]; omega
      have hScr1 : ∀ sl, sl < 25 → s1.data[sl]? = s.data[sl]? := fun sl hsl =>
        (hFr1 sl).elim (fun h => by unfold slMidBS at h; omega)
          (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
            (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id))
      have hGe28 : ∀ w, 28 ≤ w → s1.data[w]? = s.data[w]? := fun w hw' =>
        (hFr1 w).elim (fun h => by unfold slMidBS at h; omega)
          (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
            (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id))
      have hInv1 := sweepInv_update_bs23_27 inv (fun sl hsl => hScr1 sl (by omega)) (fun w hw' => hGe28 w (by omega))
      have hPB1 : ∀ t' : Fin (rows.row y).length,
          (s1.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
            some ((rows.row y)[t'.val]'t'.isLt).val := fun t' => by
        have h28 : 28 ≤ predBufBase H.vertexCount H.arcCount + rowLo + t'.val := by
          have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
          simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
        rw [hGe28 _ h28]; exact hPB t'
      have hSlRH1 : (s1.data[slRowHi]?).map Fin.val = some rowHi := by rw [hScr1 _ (by decide)]; exact hSlRH
      obtain ⟨_, _, _, q, hq, _, _, hProbeIff⟩ := probe_ok_iff_ram inv (y := y) hmidPos hmidLe
      have hLoop := sweepBSProbe_loop_steps h8 (input := input) hWork hOkBnd hFailBnd hPrBnd hplProbe
        hmidPos hmidLe rfl hq hRHm hDiff (rows.row y).length rowLo s1 hInv1 hidx (Nat.le_refl rowLo) hRLleRH
        hDiff hPB1 pc1 hz1 ho1 hPJ1 hSlRH1 hAnc1
      let c := orderedConfig dictRows large
      let p : Nat → PaperB.ForestHead.Probe := fun d => PaperB.ForestHead.probe (selectors c sRef) (rows.row y) m_y d
      have hTailIff : (∀ t' : Fin (rows.row y).length, rowLo - rowLo ≤ t'.val →
            let u := (rows.row y)[t'.val]'t'.isLt
            u = q.fst ∨ u = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
               F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode)) ↔
          (p mid).ok = true := by
        rw [hProbeIff]
        constructor
        · intro h u hu
          obtain ⟨i, hi_lt, rfl⟩ := List.getElem_of_mem hu
          exact h ⟨i, hi_lt⟩ (by omega : rowLo - rowLo ≤ i)
        · intro h t' _
          exact h _ (List.getElem_mem _)
      by_cases hOk : (p mid).ok = true
      · have hTailTrue : ∀ t' : Fin (rows.row y).length, rowLo - rowLo ≤ t'.val →
            let u := (rows.row y)[t'.val]'t'.isLt
            u = q.fst ∨ u = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
               F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode) :=
          hTailIff.mpr hOk
        obtain ⟨s2, k2, hk2, st2, pc2, hz2, ho2, hFr2⟩ := ite_elim_true hTailTrue hLoop
        have hMid2 : (s2.data[slMidBS]?).map Fin.val = some mid := by
          rw [(hFr2 slMidBS).elim (fun h => by unfold slMidBS slPredJ at h; omega) id]; exact hMid1
        obtain ⟨s3, hStOk, pc3, hz3b, ho3b, hLo3b, hFr3b⟩ :=
          sweepBSUpdateBound_steps h8 input hSlMidW hSlLoW (by decide) hBSBnd hOkEndBnd hplOk
            pc2 hz2 ho2 hMid2
        have hScr123 : ∀ w, w = slLoBS ∨ w = slMidBS ∨ w = slAncNode ∨ w = slPredJ ∨ s3.data[w]? = s.data[w]? := by
          intro w
          by_cases hwLo : w = slLoBS
          · exact Or.inl hwLo
          by_cases hwMid : w = slMidBS
          · exact Or.inr (Or.inl hwMid)
          by_cases hwAnc : w = slAncNode
          · exact Or.inr (Or.inr (Or.inl hwAnc))
          by_cases hwPJ : w = slPredJ
          · exact Or.inr (Or.inr (Or.inr (Or.inl hwPJ)))
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          rw [hFr3b w hwLo]
          rw [(hFr2 w).elim (fun h => absurd h hwPJ) id]
          exact (hFr1 w).elim (fun h => absurd h hwMid)
            (fun h => h.elim (fun h => absurd h hwAnc) (fun h => h.elim (fun h => absurd h hwPJ) id))
        have hInv3 := sweepInv_update_bs23_27 inv
          (fun sl hsl => (hScr123 sl).elim (fun h => by unfold slLoBS at h; omega)
            (fun h => h.elim (fun h => by unfold slMidBS at h; omega)
              (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
                (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id))))
          (fun w hw' => (hScr123 w).elim (fun h => by unfold slLoBS at h; omega)
            (fun h => h.elim (fun h => by unfold slMidBS at h; omega)
              (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
                (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id))))
        have hPB3 : ∀ t' : Fin (rows.row y).length,
            (s3.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
              some ((rows.row y)[t'.val]'t'.isLt).val := fun t' => by
          have h30 : 30 ≤ predBufBase H.vertexCount H.arcCount + rowLo + t'.val := by
            have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
            simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
          rw [(hScr123 _).elim (fun h => by unfold slLoBS at h; omega)
            (fun h => h.elim (fun h => by unfold slMidBS at h; omega)
              (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
                (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id)))]
          exact hPB t'
        have hLo3 : (s3.data[slLoBS]?).map Fin.val = some mid := hLo3b
        have hHi3 : (s3.data[slHiBS]?).map Fin.val = some hi' := by
          rw [(hScr123 slHiBS).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlHi
        have hM3 : (s3.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val) := by
          rw [(hScr123 slMNode).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlM
        have hRL3 : (s3.data[slRowLo]?).map Fin.val = some rowLo := by
          rw [(hScr123 slRowLo).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlRL
        have hRH3 : (s3.data[slRowHi]?).map Fin.val = some rowHi := by
          rw [(hScr123 slRowHi).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlRH
        have hSpan' : hi' - mid ≤ 2 ^ f := by rw [Nat.pow_succ] at hSpan; dsimp only [mid]; omega
        obtain ⟨t, kRec, hkRec, stRec, pct, zt, ot, hLoT, hFrT⟩ :=
          ih mid hi' s3 hInv3 (by dsimp only [mid]; omega) hHiLe hSpan' hPB3 pc3 hz3b ho3b
            hLo3 hHi3 hM3 hRL3 hRH3
        have hkRec' : kRec ≤ 35 + f * stepCost := by
          dsimp only [stepCost]; rw [← Nat.mul_assoc]; exact hkRec
        have hkFull : k1 + k2 + prOk.length + kRec ≤ 35 + (f + 1) * stepCost := by
          have h12 : k1 + k2 + prOk.length ≤ stepCost := by
            dsimp only [stepCost]; simp only [Nat.succ_mul] at hk2 ⊢; omega
          rw [Nat.succ_mul]; omega
        refine ⟨t, k1 + k2 + prOk.length + kRec,
          by dsimp only [stepCost] at hkFull; rw [← Nat.mul_assoc] at hkFull; exact hkFull,
          ((st1.append st2).append hStOk).append stRec, pct, zt, ot, ?_, ?_⟩
        · rw [measuredSearch_while _ (f + 1) lo hi' hLoLt hSpan]
          simp only [hle1, ↓reduceIte, Nat.add_sub_cancel]
          rw [ite_eq_left (by simpa only [p, mid] using hOk)]; exact hLoT
        · intro w
          rcases hFrT w with rfl | rfl | rfl | rfl | rfl | hw3
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · rcases hScr123 w with rfl | rfl | rfl | rfl | hw0
            · exact Or.inl rfl
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hw3.trans hw0)))))
      · have hTailFalse : ¬ ∀ t' : Fin (rows.row y).length, rowLo - rowLo ≤ t'.val →
            let u := (rows.row y)[t'.val]'t'.isLt
            u = q.fst ∨ u = q.snd ∨
              (F.depthOf ancNode ≤ F.depthOf (sRef.labelAt u.val) ∧
               F.ancestorAtDepth (sRef.labelAt u.val) (F.depthOf ancNode) = ancNode) :=
          fun h => hOk (hTailIff.mp h)
        obtain ⟨s2, k2, hk2, st2, pc2, hz2, ho2, hFr2⟩ := ite_elim_false hTailFalse hLoop
        have hMid2 : (s2.data[slMidBS]?).map Fin.val = some mid := by
          rw [(hFr2 slMidBS).elim (fun h => by unfold slMidBS slPredJ at h; omega) id]; exact hMid1
        obtain ⟨s3, hStFail, pc3, hz3b, ho3b, hHi3b, hFr3b⟩ :=
          sweepBSUpdateBound_steps h8 input hSlMidW hSlHiW (by decide) hBSBnd hFailEndBnd hplFail
            pc2 hz2 ho2 hMid2
        have hScr123 : ∀ w, w = slHiBS ∨ w = slMidBS ∨ w = slAncNode ∨ w = slPredJ ∨ s3.data[w]? = s.data[w]? := by
          intro w
          by_cases hwHi : w = slHiBS
          · exact Or.inl hwHi
          by_cases hwMid : w = slMidBS
          · exact Or.inr (Or.inl hwMid)
          by_cases hwAnc : w = slAncNode
          · exact Or.inr (Or.inr (Or.inl hwAnc))
          by_cases hwPJ : w = slPredJ
          · exact Or.inr (Or.inr (Or.inr (Or.inl hwPJ)))
          refine Or.inr (Or.inr (Or.inr (Or.inr ?_)))
          rw [hFr3b w hwHi]
          rw [(hFr2 w).elim (fun h => absurd h hwPJ) id]
          exact (hFr1 w).elim (fun h => absurd h hwMid)
            (fun h => h.elim (fun h => absurd h hwAnc) (fun h => h.elim (fun h => absurd h hwPJ) id))
        have hInv3 := sweepInv_update_bs23_27 inv
          (fun sl hsl => (hScr123 sl).elim (fun h => by unfold slHiBS at h; omega)
            (fun h => h.elim (fun h => by unfold slMidBS at h; omega)
              (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
                (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id))))
          (fun w hw' => (hScr123 w).elim (fun h => by unfold slHiBS at h; omega)
            (fun h => h.elim (fun h => by unfold slMidBS at h; omega)
              (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
                (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id))))
        have hPB3 : ∀ t' : Fin (rows.row y).length,
            (s3.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
              some ((rows.row y)[t'.val]'t'.isLt).val := fun t' => by
          have h30 : 30 ≤ predBufBase H.vertexCount H.arcCount + rowLo + t'.val := by
            have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
            simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
          rw [(hScr123 _).elim (fun h => by unfold slHiBS at h; omega)
            (fun h => h.elim (fun h => by unfold slMidBS at h; omega)
              (fun h => h.elim (fun h => by unfold slAncNode at h; omega)
                (fun h => h.elim (fun h => by unfold slPredJ at h; omega) id)))]
          exact hPB t'
        have hLo3 : (s3.data[slLoBS]?).map Fin.val = some lo := by
          rw [(hScr123 slLoBS).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlLo
        have hHi3 : (s3.data[slHiBS]?).map Fin.val = some mid := hHi3b
        have hM3 : (s3.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val) := by
          rw [(hScr123 slMNode).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlM
        have hRL3 : (s3.data[slRowLo]?).map Fin.val = some rowLo := by
          rw [(hScr123 slRowLo).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlRL
        have hRH3 : (s3.data[slRowHi]?).map Fin.val = some rowHi := by
          rw [(hScr123 slRowHi).elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide))
            (fun h => h.elim (fun h => absurd h (by decide)) (fun h => h.elim (fun h => absurd h (by decide)) id)))]; exact hSlRH
        have hSpan' : mid - lo ≤ 2 ^ f := by rw [Nat.pow_succ] at hSpan; dsimp only [mid]; omega
        obtain ⟨t, kRec, hkRec, stRec, pct, zt, ot, hLoT, hFrT⟩ :=
          ih lo mid s3 hInv3 (by dsimp only [mid]; omega) (by dsimp only [mid]; omega) hSpan' hPB3 pc3 hz3b ho3b
            hLo3 hHi3 hM3 hRL3 hRH3
        have hkRec' : kRec ≤ 35 + f * stepCost := by
          dsimp only [stepCost]; rw [← Nat.mul_assoc]; exact hkRec
        have hkFull : k1 + k2 + prFail.length + kRec ≤ 35 + (f + 1) * stepCost := by
          have h12 : k1 + k2 + prFail.length ≤ stepCost := by
            dsimp only [stepCost]; simp only [Nat.succ_mul] at hk2 ⊢; omega
          rw [Nat.succ_mul]; omega
        refine ⟨t, k1 + k2 + prFail.length + kRec,
          by dsimp only [stepCost] at hkFull; rw [← Nat.mul_assoc] at hkFull; exact hkFull,
          ((st1.append st2).append hStFail).append stRec, pct, zt, ot, ?_, ?_⟩
        · rw [measuredSearch_while _ (f + 1) lo hi' hLoLt hSpan]
          simp only [hle1, ↓reduceIte, Nat.add_sub_cancel]
          rw [ite_eq_right (by simpa only [p, mid] using hOk)]; exact hLoT
        · intro w
          rcases hFrT w with rfl | rfl | rfl | rfl | rfl | hw3
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
          · rcases hScr123 w with rfl | rfl | rfl | rfl | hw0
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inl rfl))
            · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hw3.trans hw0)))))

theorem sweepBSBlock_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hidx : idx < H.vertexCount)
    {pcBS pcAfterBS : Nat}
    (hAfterBnd : pcAfterBS < code.size)
    (hSz : pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcAfterBS).length < code.size)
    (hpl : Placed code pcBS (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcAfterBS))
    {y m_y : Vertex H} {rowLo rowHi : Nat}
    (hRLleRH : rowLo ≤ rowHi) (hRHm : rowHi ≤ H.arcCount)
    (hDiff : rowHi - rowLo = (rows.row y).length)
    (hPB : ∀ t' : Fin (rows.row y).length,
      (s.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
        some ((rows.row y)[t'.val]'t'.isLt).val)
    (hpc : s.pc = pcBS) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlLo : (s.data[slLoBS]?).map Fin.val = some 0)
    (hSlHi : (s.data[slHiBS]?).map Fin.val = some (F.depthOf (sRef.labelAt m_y.val) + 1))
    (hSlM : (s.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val))
    (hSlRL : (s.data[slRowLo]?).map Fin.val = some rowLo)
    (hSlRH : (s.data[slRowHi]?).map Fin.val = some rowHi) :
    let c := orderedConfig dictRows large
    let p : Nat → PaperB.ForestHead.Probe := fun d => PaperB.ForestHead.probe (selectors c sRef) (rows.row y) m_y d
    let cut := (PaperB.ForestHead.measuredLog p (F.depthOf (sRef.labelAt m_y.val) + 1)).cut
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 35 + OracleContract.L H.vertexCount * ((rows.row y).length + 1) * (175 + 60 * (OracleContract.L H.vertexCount + 1)) ∧
      Steps code input k s t ∧ t.pc = pcAfterBS ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[slLoBS]?).map Fin.val = some cut ∧
      ∀ w, w = slLoBS ∨ w = slHiBS ∨ w = slMidBS ∨ w = slAncNode ∨ w = slPredJ ∨ t.data[w]? = s.data[w]? := by
  have hmF : sRef.labelAt m_y.val < F.size := inv.grounded.size_eq ▸ inv.labelsLt m_y
  have hmLeN : sRef.labelAt m_y.val ≤ H.vertexCount :=
    Nat.le_trans (Nat.le_of_lt (inv.labelsLt m_y)) (Nat.le_trans inv.sRefNextLe (by omega))
  have hdLe : F.depthOf (sRef.labelAt m_y.val) ≤ H.vertexCount := by
    have hStep : ∀ {F0 : JumpForest}, ValidJumpForest F0 → ∀ u < F0.size, F0.depthOf u ≤ u := by
      intro F0 hF0; induction hF0 with
      | init => intro u hu; simp [JumpForest.init, JumpForest.size] at hu; subst hu; exact Nat.le_refl _
      | @appendLeaf F1 p _ hp ih =>
        intro u hu
        by_cases hOld : u < F1.size
        · rw [depthOf_appendLeaf_old F1 p hOld]; exact ih u hOld
        · have hSzApp : (F1.appendLeaf p).size = F1.size + 1 := by simp [JumpForest.appendLeaf, JumpForest.size]
          have huEq : u = F1.size := by omega
          subst huEq
          have hRec : (F1.appendLeaf p).depthOf F1.size = F1.depthOf p + 1 := by
            simp [JumpForest.depthOf, recordAt_appendLeaf_new]; rfl
          have := ih p hp; omega
    exact Nat.le_trans (hStep inv.records.valid _ hmF) hmLeN
  have hSpanL : F.depthOf (sRef.labelAt m_y.val) + 1 - 0 ≤ 2 ^ OracleContract.L H.vertexCount := by
    have := vertexCount_lt_two_pow_L H.vertexCount; omega
  have hSpanLog : F.depthOf (sRef.labelAt m_y.val) + 1 - 0 ≤
      2 ^ (Nat.log2 (F.depthOf (sRef.labelAt m_y.val) + 1) + 1) := by
    exact Nat.le_of_lt ((Nat.log2_lt (by omega)).mp (Nat.lt_succ_self _))
  have hRes := sweepBSBlock_while (input := input) h8 hWork hidx hAfterBnd hSz hpl hRLleRH hRHm hDiff
    (OracleContract.L H.vertexCount) 0 (F.depthOf (sRef.labelAt m_y.val) + 1) s inv
    (Nat.zero_lt_succ _) (Nat.le_refl _) hSpanL hPB hpc hz ho hSlLo hSlHi hSlM hSlRL hSlRH
  have hCutEq := measuredSearch_cut_eq_of_le (fun d => PaperB.ForestHead.probe (selectors (orderedConfig dictRows large) sRef) (rows.row y) m_y d)
    (OracleContract.L H.vertexCount) (Nat.log2 (F.depthOf (sRef.labelAt m_y.val) + 1) + 1)
    0 (F.depthOf (sRef.labelAt m_y.val) + 1) (Nat.zero_lt_succ _) hSpanL hSpanLog
  simpa only [PaperB.ForestHead.measuredLog, hCutEq] using hRes

theorem sweepFinalParentBlock_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hidx : idx < H.vertexCount)
    {pcStart pcInstall : Nat}
    (hInstEq : pcInstall = pcStart + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcStart pcInstall).length)
    (hSz : pcStart + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcStart pcInstall).length < code.size)
    (hpl : Placed code pcStart (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcStart pcInstall))
    {m_y : Vertex H} {cut : Nat}
    (_hcut : cut ≤ F.depthOf (sRef.labelAt m_y.val))
    (hpc : s.pc = pcStart) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlLo : (s.data[slLoBS]?).map Fin.val = some cut)
    (hSlM : (s.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val)) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 80 + 60 * (OracleContract.L H.vertexCount + 1) ∧
      Steps code input k s t ∧
      t.pc = pcInstall ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[slAncNode]?).map Fin.val = some (F.ancestorAtDepth (sRef.labelAt m_y.val) cut) ∧
      ∀ w, w = slAncNode ∨ t.data[w]? = s.data[w]? := by
  let n := H.vertexCount
  let m := H.arcCount
  have hWork' : 32 * n + 7 * m + 17 ≤ workCap := hWork
  have hSlLoW : slLoBS < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlMW : slMNode < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlJW : slJumpBase < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlAncW : slAncNode < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hJB2 : jumpBase n m + 2 < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at hWork' ⊢; omega
  have hmF : sRef.labelAt m_y.val < F.size := inv.grounded.size_eq ▸ inv.labelsLt m_y
  have hFIns : F.numInserted ≤ n := by
    have hSzF : F.size = sRef.tables.next := inv.grounded.size_eq
    have hSRefN : sRef.tables.next ≤ n := Nat.le_trans inv.sRefNextLe (by omega)
    change F.records.length - 1 ≤ n
    change F.records.length = sRef.tables.next at hSzF
    omega
  let f0 := loadScratch h8 rCmd slLoBS
  let f2 := sweepInitStoreScratch h8 slAncNode rZero ++ [.goto pcInstall]
  let f1 : List (Instr bits 15) :=
    [.branchLt rZero rCmd (pcStart + f0.length + 1 + f2.length) (pcStart + f0.length + 1)]
  let f3 := loadScratch h8 rPtr slMNode ++ loadScratch h8 rTin slJumpBase ++
    [.add rTout rTin rOne, .add rOff rTout rOne]
  let f5 := [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] ++
    sweepInitStoreScratch h8 slAncNode rPtr
  have hf0Le : f0.length ≤ 12 := loadScratch_length_le h8 rCmd slLoBS
  have hf2aLe : (sweepInitStoreScratch h8 slAncNode rZero).length ≤ 12 :=
    sweepInitStoreScratch_length_le h8 slAncNode rZero
  have hf2Len : f2.length = (sweepInitStoreScratch h8 slAncNode rZero).length + 1 := by
    dsimp only [f2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hf3aLe : (loadScratch h8 rPtr slMNode).length ≤ 12 := loadScratch_length_le h8 rPtr slMNode
  have hf3bLe : (loadScratch h8 rTin slJumpBase).length ≤ 12 := loadScratch_length_le h8 rTin slJumpBase
  have hf3Len : f3.length =
      (loadScratch h8 rPtr slMNode).length + (loadScratch h8 rTin slJumpBase).length + 2 := by
    dsimp only [f3]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hf5aLe : (sweepInitStoreScratch h8 slAncNode rPtr).length ≤ 12 :=
    sweepInitStoreScratch_length_le h8 slAncNode rPtr
  have hf5Len : f5.length = 2 + (sweepInitStoreScratch h8 slAncNode rPtr).length := by
    dsimp only [f5]; simp only [List.length_append, List.length_cons, List.length_nil]
  let dlProg := PaperB.RamForestProgram.DepthSeek.depthLookupProgram
    (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
  let pcDL3 := pcStart + f0.length + 1 + f2.length + f3.length
  let pcAfterDL3 := pcDL3 + dlProg.toList.length
  let f4 := relocatedSubroutine dlProg pcDL3 pcAfterDL3
  have hLenBlk : (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcStart pcInstall).length =
      f0.length + 1 + f2.length + f3.length + dlProg.toList.length + f5.length := by
    unfold sweepFinalParentBlock
    dsimp only [dlProg, f0, f1, f2, f3, f4, f5, pcAfterDL3, pcDL3]
    simp only [relocatedSubroutine, List.length_append, List.length_cons, List.length_nil, List.length_map]
  have hInstBnd : pcInstall < code.size := by rw [hInstEq]; exact hSz
  have hSzTot : pcStart + (f0.length + 1 + f2.length + f3.length + dlProg.toList.length + f5.length) <
      code.size := by rw [← hLenBlk]; exact hSz
  have hInstEq' : pcInstall = pcAfterDL3 + f5.length := by
    rw [hInstEq, hLenBlk]; dsimp only [pcAfterDL3, pcDL3]; omega
  unfold sweepFinalParentBlock at hpl
  dsimp only at hpl
  have h01234 := placed_append_left hpl
  have h0123 := placed_append_left h01234
  have h012 := placed_append_left h0123
  have h01 := placed_append_left h012
  have hpl0 : Placed code pcStart f0 := placed_append_left h01
  have hpl1 : Placed code (pcStart + f0.length) f1 := placed_right_eq h01 rfl
  have hpl2 : Placed code (pcStart + f0.length + 1) f2 :=
    placed_right_eq h012 (by dsimp only [f0, f1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl3 : Placed code (pcStart + f0.length + 1 + f2.length) f3 :=
    placed_right_eq h0123 (by dsimp only [f0, f1, f2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl4 : Placed code pcDL3 f4 :=
    placed_right_eq h01234 (by dsimp only [pcDL3, f0, f1, f2, f3]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5 : Placed code pcAfterDL3 f5 :=
    placed_right_eq hpl (by
      dsimp only [pcAfterDL3, pcDL3, f0, f1, f2, f3, f4]
      simp only [relocatedSubroutine, List.length_append, List.length_cons, List.length_nil, List.length_map]
      dsimp only [dlProg]
      omega)
  clear hpl h01234 h0123 h012 h01
  -- Execute f0: load cut into rCmd
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rCmd slLoBS
    hSlLoW (by decide) hpc hpl0 (by dsimp only [f0] at *; omega) ho hSlLo
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  by_cases hCutZ : cut = 0
  · have hLe : (reg s1 rCmd).val ≤ (reg s1 rZero).val := by rw [r1, hz1, hCutZ]; exact Nat.le_refl 0
    obtain ⟨s2, st2, pc2, k2, d2⟩ := step_branchLt_false (input := input) (s := s1)
      (placed_fetch hpl1 (i := 0) rfl pc1) hLe (by omega)
    have ho2 : (reg s2 rOne).val = 1 := by rw [k2, ho1]
    have hz2 : (reg s2 rZero).val = 0 := by rw [k2, hz1]
    have hpl2a : Placed code (pcStart + f0.length + 1) (sweepInitStoreScratch h8 slAncNode rZero) :=
      placed_append_left hpl2
    have hpl2b : Placed code (pcStart + f0.length + 1 + (sweepInitStoreScratch h8 slAncNode rZero).length)
        ([.goto pcInstall] : List (Instr bits 15)) := placed_right_eq hpl2 rfl
    obtain ⟨s3, st3, pc3, hAnc3, hFr3, k3⟩ := storeScratch_val_steps h8 (input := input) slAncNode rZero
      (by decide) (by decide) hSlAncW pc2 hpl2a (by omega) ho2
    let s4 : State (layout bits inputCap workCap hi hw) := { s3 with pc := pcInstall }
    have st4 : step code input s3 = some (.next s4) :=
      step_goto_at (placed_fetch hpl2b (i := 0) rfl pc3) hInstBnd
    have hAncEq : F.ancestorAtDepth (sRef.labelAt m_y.val) cut = 0 := by
      rw [hCutZ]; exact inv.records.valid.ancestorAtDepth_zero hmF
    refine ⟨s4, f0.length + 1 + f2.length, by omega, ?_, rfl,
      by change (reg s3 rZero).val = 0; rw [k3 _ (by decide), hz2],
      by change (reg s3 rOne).val = 1; rw [k3 _ (by decide), ho2], ?_, ?_⟩
    · rw [hf2Len]
      exact (st1.append (Steps.cons st2 (Steps.zero _))).append (st3.append (Steps.cons st4 (Steps.zero _)))
    · change (s3.data[slAncNode]?).map Fin.val = _; rw [hAncEq, hAnc3, hz2]
    · intro w
      by_cases hwA : w = slAncNode
      · exact Or.inl hwA
      · exact Or.inr (by change s3.data[w]? = s.data[w]?; rw [hFr3 w hwA, d2, d1])
  · have hLt : (reg s1 rZero).val < (reg s1 rCmd).val := by rw [hz1, r1]; omega
    obtain ⟨s2, st2, pc2, k2, d2⟩ := step_branchLt_true (input := input) (s := s1)
      (placed_fetch hpl1 (i := 0) rfl pc1) hLt (by omega)
    have hz2 : (reg s2 rZero).val = 0 := by rw [k2, hz1]
    have ho2 : (reg s2 rOne).val = 1 := by rw [k2, ho1]
    have hcmd2 : (reg s2 rCmd).val = cut := by rw [k2, r1]
    have hSlM2 : (s2.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val) := by rw [d2, d1]; exact hSlM
    have hSlJ2 : (s2.data[slJumpBase]?).map Fin.val = some (jumpBase n m) := by rw [d2, d1]; exact inv.slJumpVal
    let p3 : Nat := pcStart + f0.length + 1 + f2.length
    have hpl3_012 := placed_append_left hpl3
    have hpl3_0 := placed_append_left hpl3_012
    have hpl3_1 : Placed code (p3 + (loadScratch h8 rPtr slMNode).length) (loadScratch h8 rTin slJumpBase) :=
      placed_right_eq hpl3_012 rfl
    have hpl3_23 : Placed code (p3 + (loadScratch h8 rPtr slMNode).length +
        (loadScratch h8 rTin slJumpBase).length) ([.add rTout rTin rOne, .add rOff rTout rOne] : List (Instr bits 15)) :=
      placed_right_eq hpl3 (by simp only [List.length_append]; omega)
    obtain ⟨s3, st3, pc3, r3, d3, k3⟩ := loadScratch_val_steps h8 (input := input) rPtr slMNode hSlMW (by decide)
      pc2 hpl3_0 (by dsimp only [p3] at *; omega) ho2 hSlM2
    have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide) (by decide), hz2]
    have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide) (by decide), ho2]
    have hcmd3 : (reg s3 rCmd).val = cut := by rw [k3 _ (by decide) (by decide), hcmd2]
    have hSlJ3 : (s3.data[slJumpBase]?).map Fin.val = some (jumpBase n m) := by rw [d3]; exact hSlJ2
    obtain ⟨s4, st4, pc4, r4, d4, k4⟩ := loadScratch_val_steps h8 (input := input) rTin slJumpBase hSlJW (by decide)
      pc3 hpl3_1 (by dsimp only [p3] at *; omega) ho3 hSlJ3
    have hz4 : (reg s4 rZero).val = 0 := by rw [k4 _ (by decide) (by decide), hz3]
    have ho4 : (reg s4 rOne).val = 1 := by rw [k4 _ (by decide) (by decide), ho3]
    have hcmd4 : (reg s4 rCmd).val = cut := by rw [k4 _ (by decide) (by decide), hcmd3]
    have hptr4 : (reg s4 rPtr).val = sRef.labelAt m_y.val := by rw [k4 _ (by decide) (by decide), r3]
    obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_add15_at (input := input) (s := s4)
      (placed_fetch hpl3_23 (i := 0) rfl pc4) (by dsimp only [p3] at *; omega)
    have htout5 : (reg s5 rTout).val = jumpBase n m + 1 := by
      rw [r5, WordOps.add_val, r4, ho4]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
    obtain ⟨s6, st6, pc6, r6, k6, d6⟩ := step_add15_at (input := input) (s := s5)
      (placed_fetch hpl3_23 (i := 1) rfl (by rw [pc5, pc4])) (by rw [pc5]; dsimp only [p3] at *; omega)
    have hoff6 : (reg s6 rOff).val = jumpBase n m + 2 := by
      rw [r6, WordOps.add_val, htout5, k5 _ (by decide), ho4]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hJB2 hw)
    have htin6 : (reg s6 rTin).val = jumpBase n m := by rw [k6 _ (by decide), k5 _ (by decide), r4]
    have htout6 : (reg s6 rTout).val = jumpBase n m + 1 := by rw [k6 _ (by decide), htout5]
    have hcmd6 : (reg s6 rCmd).val = cut := by rw [k6 _ (by decide), k5 _ (by decide), hcmd4]
    have hz6 : (reg s6 rZero).val = 0 := by rw [k6 _ (by decide), k5 _ (by decide), hz4]
    have hptr6 : (reg s6 rPtr).val = sRef.labelAt m_y.val := by rw [k6 _ (by decide), k5 _ (by decide), hptr4]
    have hd6 : s6.data = s.data := d6.trans (d5.trans (d4.trans (d3.trans (d2.trans d1))))
    have hpc6 : s6.pc = pcDL3 := by rw [pc6, pc5]; dsimp only [p3, pcDL3]; omega
    have hRec6 : PaperB.RamForestProgram.DepthSeek.Records (jumpBase n m) F s6.data := by
      rw [hd6]; exact inv.records
    obtain ⟨s7, kDL, hkDL, stDL, pc7, r7, hd7⟩ := relocate_depthLookup input s6 hpc6 (by omega) hpl4
      ⟨htin6, htout6, hoff6, hcmd6, hz6⟩ hRec6 hmF hptr6 hFIns (vertexCount_add2_le_two_pow_L_succ n)
    have hd7' : s7.data = s.data := hd7.trans hd6
    have hpl5a : Placed code pcAfterDL3 ([.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] : List (Instr bits 15)) :=
      placed_append_left hpl5
    have hpl5b : Placed code (pcAfterDL3 + 2) (sweepInitStoreScratch h8 slAncNode rPtr) :=
      placed_right_eq hpl5 rfl
    obtain ⟨s8, st8, pc8, r8, k8, d8⟩ := step_imm_at (input := input)
      (placed_fetch hpl5a (i := 0) rfl pc7) (by rw [pc7]; omega)
    obtain ⟨s9, st9, pc9, r9, k9, d9⟩ := step_imm_at (input := input)
      (placed_fetch hpl5a (i := 1) rfl (by rw [pc8, pc7])) (by rw [pc8, pc7]; omega)
    have ho9 : (reg s9 rOne).val = 1 := congrArg Fin.val r9
    have hz9 : (reg s9 rZero).val = 0 := by rw [k9 _ (by decide), r8]
    have hptr9 : (reg s9 rPtr).val = F.ancestorAtDepth (sRef.labelAt m_y.val) cut := by
      rw [k9 _ (by decide), k8 _ (by decide), r7]
    obtain ⟨s10, st10, pc10, hAnc10, hFr10, k10⟩ := storeScratch_val_steps h8 (input := input) slAncNode rPtr
      (by decide) (by decide) hSlAncW (by rw [pc9, pc8, pc7]) hpl5b (by omega) ho9
    have hf3St : Steps code input f3.length s2 s6 := by
      rw [hf3Len]
      exact (st3.append st4).append (.cons st5 (.cons st6 (.zero _)))
    have hf5St : Steps code input f5.length s7 s10 := by
      rw [hf5Len]
      exact (Steps.cons st8 (Steps.cons st9 (Steps.zero _))).append st10
    have hkTot : f0.length + 1 + f3.length + kDL + f5.length ≤ 80 + 60 * (OracleContract.L H.vertexCount + 1) := by
      have hk1 : f0.length + 1 + f3.length + kDL + f5.length ≤
          12 + 1 + 26 + (60 * (OracleContract.L n + 1) + 7) + 14 := by omega
      have hNum : ∀ x : Nat, 12 + 1 + 26 + (60 * x + 7) + 14 ≤ 80 + 60 * x := fun x => by omega
      exact Nat.le_trans hk1 (hNum (OracleContract.L H.vertexCount + 1))
    refine ⟨s10, f0.length + 1 + f3.length + kDL + f5.length, hkTot, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (((st1.append (.cons st2 (.zero _))).append hf3St).append stDL).append hf5St
    · rw [pc10, hInstEq', hf5Len, Nat.add_assoc]
    · rw [k10 _ (by decide), hz9]
    · rw [k10 _ (by decide), ho9]
    · rw [hAnc10, hptr9]
    · intro w
      by_cases hwA : w = slAncNode
      · exact Or.inl hwA
      · exact Or.inr (by rw [hFr10 w hwA, d9, d8, hd7'])

private theorem dictBSLoop_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {d : Array PaperB.PairLookup.Key}
    (hSorted : PaperB.PairLookup.StrictSorted d)
    {slotIdx kFst kSnd dFstBase dSndBase pcDictBS pcWriteZero : Nat}
    (hSlotLt : slotIdx < d.size)
    (hTarget : d[slotIdx]'hSlotLt = (kFst, kSnd))
    (hDFstW : ∀ i < d.size, dFstBase + i < workCap)
    (hDSndW : ∀ i < d.size, dSndBase + i < workCap)
    (hDSizeW : d.size < workCap)
    (_hWZBnd : pcWriteZero < code.size)
    (hSzBS : pcDictBS + 17 < code.size)
    (hpl : Placed code pcDictBS
      [ .branchLt rClk rRem (pcDictBS + 1) pcWriteZero,
        .sub rTmp rRem rClk,
        .shr1 rTmp rTmp,
        .add rPtr rClk rTmp,
        .add rTmp rChild rPtr,
        .loadData rTin rTmp,
        .branchLt rTin rStack (pcDictBS + 13) (pcDictBS + 7),
        .branchLt rStack rTin (pcDictBS + 15) (pcDictBS + 8),
        .add rTmp rCnt rPtr,
        .loadData rTin rTmp,
        .branchLt rTin rVal (pcDictBS + 13) (pcDictBS + 11),
        .branchLt rVal rTin (pcDictBS + 15) (pcDictBS + 12),
        .goto (pcDictBS + 17),
        .add rClk rPtr rOne, .goto pcDictBS,
        .mov rRem rPtr, .goto pcDictBS ]) :
    ∀ fuel lo hi' : Nat, ∀ s : State (layout bits inputCap workCap hi hw),
      lo ≤ slotIdx → slotIdx < hi' → hi' ≤ d.size → hi' - lo ≤ 2 ^ fuel →
      (∀ i (hi_lt : i < d.size),
        (s.data[dFstBase + i]?).map Fin.val = some (d[i]'hi_lt).1 ∧
        (s.data[dSndBase + i]?).map Fin.val = some (d[i]'hi_lt).2) →
      s.pc = pcDictBS → (reg s rZero).val = 0 → (reg s rOne).val = 1 →
      (reg s rClk).val = lo → (reg s rRem).val = hi' →
      (reg s rChild).val = dFstBase → (reg s rCnt).val = dSndBase →
      (reg s rStack).val = kFst → (reg s rVal).val = kSnd →
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 17 * (fuel + 1) ∧
        Steps code input k s t ∧
        t.pc = pcDictBS + 17 ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (reg t rPtr).val = slotIdx ∧ t.data = s.data := by
  have goRight : ∀ {sX : State (layout bits inputCap workCap hi hw)} {mid hi' : Nat},
      mid < hi' →
      ∀ (hhi : hi' ≤ d.size) (hpcX : sX.pc = pcDictBS + 13) (hptrX : (reg sX rPtr).val = mid)
        (honeX : (reg sX rOne).val = 1),
      ∃ sN : State (layout bits inputCap workCap hi hw),
        Steps code input 2 sX sN ∧ sN.pc = pcDictBS ∧
        (reg sN rClk).val = mid + 1 ∧ (∀ r, r ≠ rClk → reg sN r = reg sX r) ∧ sN.data = sX.data := by
    intro sX mid hi' hmh hhi hpcX hptrX honeX
    have hf13 : code[sX.pc]? = some (.add rClk rPtr rOne) :=
      placed_fetch hpl (i := 13) rfl hpcX
    obtain ⟨sA, stA, pcA, rA, kA, dA⟩ := step_add15_at (input := input) hf13 (by rw [hpcX]; omega)
    have hclkA : (reg sA rClk).val = mid + 1 := by
      have hmid1 : mid + 1 ≤ d.size := Nat.lt_of_lt_of_le hmh hhi
      rw [rA, WordOps.add_val, hptrX, honeX]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hmid1 (Nat.lt_of_lt_of_le hDSizeW hw))
    have hf14 : code[sA.pc]? = some (.goto pcDictBS) :=
      placed_fetch hpl (i := 14) rfl (by rw [pcA, hpcX])
    let sB : State (layout bits inputCap workCap hi hw) := { sA with pc := pcDictBS }
    have stB : step code input sA = some (.next sB) := step_goto_at hf14 (by omega)
    exact ⟨sB, Steps.cons stA (Steps.cons stB (Steps.zero _)), rfl, hclkA, kA, dA⟩
  have goLeft : ∀ {sX : State (layout bits inputCap workCap hi hw)} {mid : Nat},
      sX.pc = pcDictBS + 15 → (reg sX rPtr).val = mid →
      ∃ sN : State (layout bits inputCap workCap hi hw),
        Steps code input 2 sX sN ∧ sN.pc = pcDictBS ∧
        (reg sN rRem).val = mid ∧ (∀ r, r ≠ rRem → reg sN r = reg sX r) ∧ sN.data = sX.data := by
    intro sX mid hpcX hptrX
    have hf15 : code[sX.pc]? = some (.mov rRem rPtr) :=
      placed_fetch hpl (i := 15) rfl hpcX
    obtain ⟨sA, stA, pcA, rA, kA, dA⟩ := step_mov_at (input := input) hf15 (by rw [hpcX]; omega)
    have hremA : (reg sA rRem).val = mid := by rw [rA, hptrX]
    have hf16 : code[sA.pc]? = some (.goto pcDictBS) :=
      placed_fetch hpl (i := 16) rfl (by rw [pcA, hpcX])
    let sB : State (layout bits inputCap workCap hi hw) := { sA with pc := pcDictBS }
    have stB : step code input sA = some (.next sB) := step_goto_at hf16 (by omega)
    exact ⟨sB, Steps.cons stA (Steps.cons stB (Steps.zero _)), rfl, hremA, kA, dA⟩
  have stepCommon : ∀ {lo hi' : Nat} {s : State (layout bits inputCap workCap hi hw)},
      lo ≤ slotIdx → slotIdx < hi' → hi' ≤ d.size →
      (∀ i (hi_lt : i < d.size),
        (s.data[dFstBase + i]?).map Fin.val = some (d[i]'hi_lt).1 ∧
        (s.data[dSndBase + i]?).map Fin.val = some (d[i]'hi_lt).2) →
      s.pc = pcDictBS → (reg s rZero).val = 0 → (reg s rOne).val = 1 →
      (reg s rClk).val = lo → (reg s rRem).val = hi' →
      (reg s rChild).val = dFstBase → (reg s rCnt).val = dSndBase →
      (reg s rStack).val = kFst → (reg s rVal).val = kSnd →
      let mid := lo + (hi' - lo) / 2
      ∃ hm : mid < d.size,
        ∃ s6 : State (layout bits inputCap workCap hi hw),
          Steps code input 6 s s6 ∧ s6.pc = pcDictBS + 6 ∧
          (reg s6 rZero).val = 0 ∧ (reg s6 rOne).val = 1 ∧
          (reg s6 rClk).val = lo ∧ (reg s6 rRem).val = hi' ∧
          (reg s6 rChild).val = dFstBase ∧ (reg s6 rCnt).val = dSndBase ∧
          (reg s6 rStack).val = kFst ∧ (reg s6 rVal).val = kSnd ∧
          (reg s6 rPtr).val = mid ∧ (reg s6 rTin).val = (d[mid]'hm).1 ∧
          s6.data = s.data := by
    intro lo hi' s hlo hhi hds hKeys hpc hz ho hclk hrem hch hcnt hstk hval
    let mid := lo + (hi' - lo) / 2
    have hlt : lo < hi' := by omega
    have hmidLt : mid < hi' := by dsimp only [mid]; omega
    have hm : mid < d.size := Nat.lt_of_lt_of_le hmidLt hds
    refine ⟨hm, ?_⟩
    have hf0 : code[s.pc]? = some (.branchLt rClk rRem (pcDictBS + 1) pcWriteZero) :=
      placed_fetch hpl (i := 0) rfl hpc
    obtain ⟨s1, st1, pc1, k1, d1⟩ := step_branchLt_true (input := input) hf0 (by rw [hclk, hrem]; exact hlt) (by omega)
    have hf1 : code[s1.pc]? = some (.sub rTmp rRem rClk) := placed_fetch hpl (i := 1) rfl pc1
    obtain ⟨s2, st2, pc2, r2, k2, d2⟩ := step_sub15_at (input := input) hf1 (by rw [pc1]; omega)
    have htmp2 : (reg s2 rTmp).val = hi' - lo := by
      rw [r2, sub_val_exact (by rw [k1, k1, hclk, hrem]; exact Nat.le_of_lt hlt), k1, k1, hrem, hclk]
    have hf2 : code[s2.pc]? = some (.shr1 rTmp rTmp) := placed_fetch hpl (i := 2) rfl (by rw [pc2, pc1])
    obtain ⟨s3, st3, pc3, r3, k3, d3⟩ := step_shr15_at (input := input) hf2 (by rw [pc2, pc1]; omega)
    have htmp3 : (reg s3 rTmp).val = (hi' - lo) / 2 := by rw [r3, htmp2]
    have hf3 : code[s3.pc]? = some (.add rPtr rClk rTmp) := placed_fetch hpl (i := 3) rfl (by rw [pc3, pc2, pc1])
    obtain ⟨s4, st4, pc4, r4, k4, d4⟩ := step_add15_at (input := input) hf3 (by rw [pc3, pc2, pc1]; omega)
    have hptr4 : (reg s4 rPtr).val = mid := by
      rw [r4, WordOps.add_val, k3 _ (by decide), k2 _ (by decide), k1, hclk, htmp3]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hm (Nat.le_trans (Nat.le_of_lt hDSizeW) hw))
    have hf4 : code[s4.pc]? = some (.add rTmp rChild rPtr) := placed_fetch hpl (i := 4) rfl (by rw [pc4, pc3, pc2, pc1])
    obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_add15_at (input := input) hf4 (by rw [pc4, pc3, pc2, pc1]; omega)
    have htmp5 : (reg s5 rTmp).val = dFstBase + mid := by
      rw [r5, WordOps.add_val, k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hch, hptr4]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (hDFstW mid hm) hw)
    have hf5 : code[s5.pc]? = some (.loadData rTin rTmp) :=
      placed_fetch hpl (i := 5) rfl (by rw [pc5, pc4, pc3, pc2, pc1])
    have hd5 : s5.data = s.data := d5.trans (d4.trans (d3.trans (d2.trans d1)))
    obtain ⟨s6, st6, pc6, r6, k6, d6⟩ := step_loadData_reg hf5 (by rw [pc5, pc4, pc3, pc2, pc1]; omega)
      (by rw [htmp5]; exact hDFstW mid hm) (by rw [htmp5, hd5]; exact (hKeys mid hm).1)
    refine ⟨s6, Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.zero _)))))),
      by rw [pc6, pc5, pc4, pc3, pc2, pc1],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hz],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, ho],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hclk],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hrem],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hch],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hcnt],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hstk],
      by rw [k6 _ (by decide), k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2 _ (by decide), k1, hval],
      by rw [k6 _ (by decide), k5 _ (by decide), hptr4], r6, d6.trans hd5⟩
  intro fuel
  induction fuel with
  | zero =>
    intro lo hi' s hlo hhi hds hSpan hKeys hpc hz ho hclk hrem hch hcnt hstk hval
    have hSpan1 : hi' - lo ≤ 1 := by simpa using hSpan
    have hloEq : lo = slotIdx := by omega
    have hhiEq : hi' = slotIdx + 1 := by omega
    have hmidEq : lo + (hi' - lo) / 2 = slotIdx := by omega
    obtain ⟨hm, s6, st6, pc6, hz6, ho6, _, _, _, hcnt6, hstk6, hval6, hptr6, htin6, hd6⟩ :=
      stepCommon hlo hhi hds hKeys hpc hz ho hclk hrem hch hcnt hstk hval
    have htinV : (reg s6 rTin).val = kFst := by
      have := hTarget; simp only [hmidEq] at htin6; rw [htin6, this]
    have hf6 : code[s6.pc]? = some (.branchLt rTin rStack (pcDictBS + 13) (pcDictBS + 7)) :=
      placed_fetch hpl (i := 6) rfl pc6
    obtain ⟨s7, st7, pc7, k7, d7⟩ := step_branchLt_false (input := input) hf6 (by rw [hstk6, htinV]; exact Nat.le_refl _) (by omega)
    have hf7 : code[s7.pc]? = some (.branchLt rStack rTin (pcDictBS + 15) (pcDictBS + 8)) :=
      placed_fetch hpl (i := 7) rfl pc7
    obtain ⟨s8, st8, pc8, k8, d8⟩ := step_branchLt_false (input := input) hf7 (by rw [k7, k7, htinV, hstk6]; exact Nat.le_refl _) (by omega)
    have hf8 : code[s8.pc]? = some (.add rTmp rCnt rPtr) := placed_fetch hpl (i := 8) rfl pc8
    obtain ⟨s9, st9, pc9, r9, k9, d9⟩ := step_add15_at (input := input) hf8 (by rw [pc8]; omega)
    have htmp9 : (reg s9 rTmp).val = dSndBase + slotIdx := by
      rw [r9, WordOps.add_val, k8, k7, hcnt6, k8, k7, hptr6, hmidEq]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (hDSndW slotIdx hSlotLt) hw)
    have hf9 : code[s9.pc]? = some (.loadData rTin rTmp) := placed_fetch hpl (i := 9) rfl (by rw [pc9, pc8])
    have hd9 : s9.data = s.data := d9.trans (d8.trans (d7.trans hd6))
    obtain ⟨s10, st10, pc10, r10, k10, d10⟩ := step_loadData_reg hf9 (by rw [pc9, pc8]; omega)
      (by rw [htmp9]; exact hDSndW slotIdx hSlotLt) (by rw [htmp9, hd9]; exact (hKeys slotIdx hSlotLt).2)
    have htin10 : (reg s10 rTin).val = kSnd := by rw [r10, hTarget]
    have hval10 : (reg s10 rVal).val = kSnd := by rw [k10 _ (by decide), k9 _ (by decide), k8, k7, hval6]
    have hf10 : code[s10.pc]? = some (.branchLt rTin rVal (pcDictBS + 13) (pcDictBS + 11)) :=
      placed_fetch hpl (i := 10) rfl (by rw [pc10, pc9, pc8])
    obtain ⟨s11, st11, pc11, k11, d11⟩ := step_branchLt_false (input := input) hf10 (by rw [hval10, htin10]; exact Nat.le_refl _) (by omega)
    have hf11 : code[s11.pc]? = some (.branchLt rVal rTin (pcDictBS + 15) (pcDictBS + 12)) :=
      placed_fetch hpl (i := 11) rfl pc11
    obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_false (input := input) hf11 (by rw [k11, k11, htin10, hval10]; exact Nat.le_refl _) (by omega)
    have hf12 : code[s12.pc]? = some (.goto (pcDictBS + 17)) := placed_fetch hpl (i := 12) rfl pc12
    let s13 : State (layout bits inputCap workCap hi hw) := { s12 with pc := pcDictBS + 17 }
    have st13 : step code input s12 = some (.next s13) := step_goto_at hf12 hSzBS
    refine ⟨s13, 13, by omega, ?_, rfl,
      by change (reg s12 rZero).val = 0; rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hz6],
      by change (reg s12 rOne).val = 1; rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, ho6],
      by change (reg s12 rPtr).val = slotIdx; rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hptr6, hmidEq],
      d12.trans (d11.trans (d10.trans hd9))⟩
    exact st6.append (Steps.cons st7 (Steps.cons st8 (Steps.cons st9
      (Steps.cons st10 (Steps.cons st11 (Steps.cons st12 (Steps.cons st13 (Steps.zero _))))))))
  | succ f ih =>
    intro lo hi' s hlo hhi hds hSpan hKeys hpc hz ho hclk hrem hch hcnt hstk hval
    let mid := lo + (hi' - lo) / 2
    have hmidLtHi : mid < hi' := by dsimp only [mid]; omega
    obtain ⟨hm, s6, st6, pc6, hz6, ho6, hclk6, hrem6, hch6, hcnt6, hstk6, hval6, hptr6, htin6, hd6⟩ :=
      stepCommon hlo hhi hds hKeys hpc hz ho hclk hrem hch hcnt hstk hval
    have hKeys6 : ∀ i (hi_lt : i < d.size),
        (s6.data[dFstBase + i]?).map Fin.val = some (d[i]'hi_lt).1 ∧
        (s6.data[dSndBase + i]?).map Fin.val = some (d[i]'hi_lt).2 := fun i hi_lt => by
      rw [hd6]; exact hKeys i hi_lt
    have hf6 : code[s6.pc]? = some (.branchLt rTin rStack (pcDictBS + 13) (pcDictBS + 7)) :=
      placed_fetch hpl (i := 6) rfl pc6
    by_cases h1Lt : (d[mid]'hm).1 < kFst
    · have hMidLtSlot : mid < slotIdx := by
        by_cases hle : slotIdx ≤ mid
        · by_cases heq : slotIdx = mid
          · subst heq; rw [hTarget] at h1Lt; omega
          · have hLex := hSorted slotIdx mid hSlotLt hm (by omega)
            rw [hTarget] at hLex; cases hLex with
            | inl h => omega
            | inr h => omega
        · omega
      obtain ⟨s7, st7, pc7, k7, d7⟩ := step_branchLt_true (input := input) hf6 (by rw [htin6, hstk6]; exact h1Lt) (by omega)
      obtain ⟨sN, stN, pcN, clkN, kN, dN⟩ := goRight (sX := s7) hmidLtHi hds pc7 (by rw [k7, hptr6]) (by rw [k7, ho6])
      have hSpan' : hi' - (mid + 1) ≤ 2 ^ f := by rw [Nat.pow_succ] at hSpan; dsimp only [mid]; omega
      obtain ⟨t, kRec, hkRec, stRec, pct, zt, ot, pt, dt⟩ :=
        ih (mid + 1) hi' sN (by omega) hhi hds hSpan'
          (fun i hi_lt => by rw [dN, d7]; exact hKeys6 i hi_lt) pcN
          (by rw [kN _ (by decide), k7, hz6]) (by rw [kN _ (by decide), k7, ho6]) clkN
          (by rw [kN _ (by decide), k7, hrem6]) (by rw [kN _ (by decide), k7, hch6])
          (by rw [kN _ (by decide), k7, hcnt6]) (by rw [kN _ (by decide), k7, hstk6])
          (by rw [kN _ (by decide), k7, hval6])
      exact ⟨t, 9 + kRec, by omega,
        ((st6.append (Steps.cons st7 (Steps.zero _))).append stN).append stRec,
        pct, zt, ot, pt, dt.trans (dN.trans (d7.trans hd6))⟩
    · have hle1 : kFst ≤ (d[mid]'hm).1 := by omega
      obtain ⟨s7, st7, pc7, k7, d7⟩ := step_branchLt_false (input := input) hf6 (by rw [hstk6, htin6]; exact hle1) (by omega)
      have hf7 : code[s7.pc]? = some (.branchLt rStack rTin (pcDictBS + 15) (pcDictBS + 8)) :=
        placed_fetch hpl (i := 7) rfl pc7
      by_cases h1Gt : kFst < (d[mid]'hm).1
      · have hSlotLtMid : slotIdx < mid := by
          by_cases hle : mid ≤ slotIdx
          · by_cases heq : mid = slotIdx
            · subst heq; rw [hTarget] at h1Gt; omega
            · have hLex := hSorted mid slotIdx hm hSlotLt (by omega)
              rw [hTarget] at hLex; cases hLex with
              | inl h => omega
              | inr h => omega
          · omega
        obtain ⟨s8, st8, pc8, k8, d8⟩ := step_branchLt_true (input := input) hf7 (by rw [k7, k7, hstk6, htin6]; exact h1Gt) (by omega)
        obtain ⟨sN, stN, pcN, remN, kN, dN⟩ := goLeft (sX := s8) pc8 (by rw [k8, k7, hptr6])
        have hSpan' : mid - lo ≤ 2 ^ f := by rw [Nat.pow_succ] at hSpan; dsimp only [mid]; omega
        obtain ⟨t, kRec, hkRec, stRec, pct, zt, ot, pt, dt⟩ :=
          ih lo mid sN hlo hSlotLtMid (by omega) hSpan'
            (fun i hi_lt => by rw [dN, d8, d7]; exact hKeys6 i hi_lt) pcN
            (by rw [kN _ (by decide), k8, k7, hz6]) (by rw [kN _ (by decide), k8, k7, ho6])
            (by rw [kN _ (by decide), k8, k7, hclk6]) remN
            (by rw [kN _ (by decide), k8, k7, hch6]) (by rw [kN _ (by decide), k8, k7, hcnt6])
            (by rw [kN _ (by decide), k8, k7, hstk6]) (by rw [kN _ (by decide), k8, k7, hval6])
        exact ⟨t, 10 + kRec, by omega,
          ((st6.append (Steps.cons st7 (Steps.cons st8 (Steps.zero _)))).append stN).append stRec,
          pct, zt, ot, pt, dt.trans (dN.trans (d8.trans (d7.trans hd6)))⟩
      · have h1Eq : (d[mid]'hm).1 = kFst := by omega
        obtain ⟨s8, st8, pc8, k8, d8⟩ := step_branchLt_false (input := input) hf7
          (by rw [k7, k7, htin6, hstk6]; exact Nat.le_of_eq h1Eq) (by omega)
        have hf8 : code[s8.pc]? = some (.add rTmp rCnt rPtr) := placed_fetch hpl (i := 8) rfl pc8
        obtain ⟨s9, st9, pc9, r9, k9, d9⟩ := step_add15_at (input := input) hf8 (by rw [pc8]; omega)
        have htmp9 : (reg s9 rTmp).val = dSndBase + mid := by
          rw [r9, WordOps.add_val, k8, k7, hcnt6, k8, k7, hptr6]
          exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (hDSndW mid hm) hw)
        have hf9 : code[s9.pc]? = some (.loadData rTin rTmp) := placed_fetch hpl (i := 9) rfl (by rw [pc9, pc8])
        have hd9 : s9.data = s.data := d9.trans (d8.trans (d7.trans hd6))
        obtain ⟨s10, st10, pc10, r10, k10, d10⟩ := step_loadData_reg hf9 (by rw [pc9, pc8]; omega)
          (by rw [htmp9]; exact hDSndW mid hm) (by rw [htmp9, hd9]; exact (hKeys mid hm).2)
        have htin10 : (reg s10 rTin).val = (d[mid]'hm).2 := r10
        have hval10 : (reg s10 rVal).val = kSnd := by rw [k10 _ (by decide), k9 _ (by decide), k8, k7, hval6]
        have hf10 : code[s10.pc]? = some (.branchLt rTin rVal (pcDictBS + 13) (pcDictBS + 11)) :=
          placed_fetch hpl (i := 10) rfl (by rw [pc10, pc9, pc8])
        by_cases h2Lt : (d[mid]'hm).2 < kSnd
        · have hMidLtSlot : mid < slotIdx := by
            by_cases hle : slotIdx ≤ mid
            · by_cases heq : slotIdx = mid
              · subst heq; rw [hTarget] at h2Lt; omega
              · have hLex := hSorted slotIdx mid hSlotLt hm (by omega)
                rw [hTarget] at hLex; cases hLex with
                | inl h => omega
                | inr h => omega
            · omega
          obtain ⟨s11, st11, pc11, k11, d11⟩ := step_branchLt_true (input := input) hf10 (by rw [htin10, hval10]; exact h2Lt) (by omega)
          obtain ⟨sN, stN, pcN, clkN, kN, dN⟩ := goRight (sX := s11) hmidLtHi hds pc11
            (by rw [k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hptr6])
            (by rw [k11, k10 _ (by decide), k9 _ (by decide), k8, k7, ho6])
          have hSpan' : hi' - (mid + 1) ≤ 2 ^ f := by rw [Nat.pow_succ] at hSpan; dsimp only [mid]; omega
          obtain ⟨t, kRec, hkRec, stRec, pct, zt, ot, pt, dt⟩ :=
            ih (mid + 1) hi' sN (by omega) hhi hds hSpan'
              (fun i hi_lt => by rw [dN, d11, d10, hd9]; exact hKeys i hi_lt) pcN
              (by rw [kN _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hz6])
              (by rw [kN _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8, k7, ho6])
              clkN
              (by rw [kN _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hrem6])
              (by rw [kN _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hch6])
              (by rw [kN _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hcnt6])
              (by rw [kN _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hstk6])
              (by rw [kN _ (by decide), k11, hval10])
          exact ⟨t, 13 + kRec, by omega,
            ((st6.append (Steps.cons st7 (Steps.cons st8 (Steps.cons st9
              (Steps.cons st10 (Steps.cons st11 (Steps.zero _))))))).append stN).append stRec,
            pct, zt, ot, pt, dt.trans (dN.trans (d11.trans (d10.trans hd9)))⟩
        · have hle2 : kSnd ≤ (d[mid]'hm).2 := by omega
          obtain ⟨s11, st11, pc11, k11, d11⟩ := step_branchLt_false (input := input) hf10 (by rw [hval10, htin10]; exact hle2) (by omega)
          have hf11 : code[s11.pc]? = some (.branchLt rVal rTin (pcDictBS + 15) (pcDictBS + 12)) :=
            placed_fetch hpl (i := 11) rfl pc11
          by_cases h2Gt : kSnd < (d[mid]'hm).2
          · have hSlotLtMid : slotIdx < mid := by
              by_cases hle : mid ≤ slotIdx
              · by_cases heq : mid = slotIdx
                · subst heq; rw [hTarget] at h2Gt; omega
                · have hLex := hSorted mid slotIdx hm hSlotLt (by omega)
                  rw [hTarget] at hLex; cases hLex with
                  | inl h => omega
                  | inr h => omega
              · omega
            obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_true (input := input) hf11
              (by rw [k11, k11, hval10, htin10]; exact h2Gt) (by omega)
            obtain ⟨sN, stN, pcN, remN, kN, dN⟩ := goLeft (sX := s12) pc12
              (by rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hptr6])
            have hSpan' : mid - lo ≤ 2 ^ f := by rw [Nat.pow_succ] at hSpan; dsimp only [mid]; omega
            obtain ⟨t, kRec, hkRec, stRec, pct, zt, ot, pt, dt⟩ :=
              ih lo mid sN hlo hSlotLtMid (by omega) hSpan'
                (fun i hi_lt => by rw [dN, d12, d11, d10, hd9]; exact hKeys i hi_lt) pcN
                (by rw [kN _ (by decide), k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hz6])
                (by rw [kN _ (by decide), k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, ho6])
                (by rw [kN _ (by decide), k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hclk6])
                remN
                (by rw [kN _ (by decide), k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hch6])
                (by rw [kN _ (by decide), k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hcnt6])
                (by rw [kN _ (by decide), k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hstk6])
                (by rw [kN _ (by decide), k12, k11, hval10])
            exact ⟨t, 14 + kRec, by omega,
              ((st6.append (Steps.cons st7 (Steps.cons st8 (Steps.cons st9
                (Steps.cons st10 (Steps.cons st11 (Steps.cons st12 (Steps.zero _)))))))).append stN).append stRec,
              pct, zt, ot, pt, dt.trans (dN.trans (d12.trans (d11.trans (d10.trans hd9))))⟩
          · have h2Eq : (d[mid]'hm).2 = kSnd := by omega
            have hMidEq : mid = slotIdx := by
              by_cases hlt : mid < slotIdx
              · have hLex := hSorted mid slotIdx hm hSlotLt hlt
                rw [hTarget] at hLex; cases hLex with
                | inl h => omega
                | inr h => omega
              · by_cases hgt : slotIdx < mid
                · have hLex := hSorted slotIdx mid hSlotLt hm hgt
                  rw [hTarget] at hLex; cases hLex with
                  | inl h => omega
                  | inr h => omega
                · omega
            obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_false (input := input) hf11
              (by rw [k11, k11, htin10, hval10]; exact Nat.le_of_eq h2Eq) (by omega)
            have hf12 : code[s12.pc]? = some (.goto (pcDictBS + 17)) := placed_fetch hpl (i := 12) rfl pc12
            let s13 : State (layout bits inputCap workCap hi hw) := { s12 with pc := pcDictBS + 17 }
            have st13 : step code input s12 = some (.next s13) := step_goto_at hf12 hSzBS
            refine ⟨s13, 13, by omega, ?_, rfl,
              by change (reg s12 rZero).val = 0; rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hz6],
              by change (reg s12 rOne).val = 1; rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, ho6],
              by change (reg s12 rPtr).val = slotIdx
                 rw [k12, k11, k10 _ (by decide), k9 _ (by decide), k8, k7, hptr6]; dsimp only [mid] at hMidEq; exact hMidEq,
              d12.trans (d11.trans (d10.trans hd9))⟩
            exact st6.append (Steps.cons st7 (Steps.cons st8 (Steps.cons st9
              (Steps.cons st10 (Steps.cons st11 (Steps.cons st12 (Steps.cons st13 (Steps.zero _))))))))

private theorem sweepStoreSortedPair_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} (hWork30 : 30 ≤ workCap)
    {pcBranch pcBSInit : Nat} {a b : Vertex H}
    (hne : a ≠ b) (haNotRoot : a ≠ H.root) (hbNotRoot : b ≠ H.root)
    (hBSBnd : pcBSInit < code.size)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcBranch) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hval : (reg s rVal).val = a.val) (hclk : (reg s rClk).val = b.val)
    (hpl3 : Placed code pcBranch
      ([.branchLt rVal rClk (pcBranch + 1 +
          (sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal).length + 1)
          (pcBranch + 1)] ++
        (sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal) ++
        [.goto pcBSInit]))
    (hpl4 : Placed code (pcBranch + 1 +
        (sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal).length + 1)
      (sweepInitStoreScratch h8 slKeyFst rVal ++ sweepInitStoreScratch h8 slKeySnd rClk))
    (hEndBnd : pcBranch + 1 +
        (sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal).length + 1 +
        (sweepInitStoreScratch h8 slKeyFst rVal ++ sweepInitStoreScratch h8 slKeySnd rClk).length = pcBSInit) :
    let q : CutPair H := if _hab : a < b then
      ⟨a, b, haNotRoot, hbNotRoot, fun h => hne h⟩
      else ⟨b, a, hbNotRoot, haNotRoot, fun h => hne h.symm⟩
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 26 ∧ Steps code input k s t ∧ t.pc = pcBSInit ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[slKeyFst]?).map Fin.val = some q.fst.val ∧
      (t.data[slKeySnd]?).map Fin.val = some q.snd.val ∧
      ∀ w, w = slKeyFst ∨ w = slKeySnd ∨ t.data[w]? = s.data[w]? := by
  let i3a := sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal
  let i4 := sweepInitStoreScratch h8 slKeyFst rVal ++ sweepInitStoreScratch h8 slKeySnd rClk
  let pcALtB := pcBranch + 1 + i3a.length + 1
  have hSlKFW : slKeyFst < workCap := by unfold slKeyFst; omega
  have hSlKSW : slKeySnd < workCap := by unfold slKeySnd; omega
  have hi3aLen : i3a.length = (sweepInitStoreScratch h8 slKeyFst rClk).length +
      (sweepInitStoreScratch h8 slKeySnd rVal).length := by
    dsimp only [i3a]; simp only [List.length_append]
  have hi3aLe : i3a.length ≤ 24 := by
    have := sweepInitStoreScratch_length_le h8 slKeyFst rClk
    have := sweepInitStoreScratch_length_le h8 slKeySnd rVal
    omega
  have hi4Len : i4.length = (sweepInitStoreScratch h8 slKeyFst rVal).length +
      (sweepInitStoreScratch h8 slKeySnd rClk).length := by
    dsimp only [i4]; simp only [List.length_append]
  have hi4Le : i4.length ≤ 24 := by
    have := sweepInitStoreScratch_length_le h8 slKeyFst rVal
    have := sweepInitStoreScratch_length_le h8 slKeySnd rClk
    omega
  have hEnd' : pcALtB + i4.length = pcBSInit := hEndBnd
  have hpl3_0 := placed_append_left (placed_append_left hpl3)
  have hpl3_a : Placed code (pcBranch + 1) i3a :=
    placed_right_eq (placed_append_left hpl3) (by simp only [List.length_cons, List.length_nil])
  have hpl3_g : Placed code (pcBranch + 1 + i3a.length) ([.goto pcBSInit] : List (Instr bits 15)) :=
    placed_right_eq hpl3 (by
      dsimp only [i3a]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hf3 : code[s.pc]? = some (.branchLt rVal rClk pcALtB (pcBranch + 1)) :=
    placed_fetch hpl3_0 (i := 0) rfl hpc
  by_cases hab : a < b
  · have hqFst : (if hab' : a < b then (⟨a, b, haNotRoot, hbNotRoot, fun h => hne h⟩ : CutPair H)
        else ⟨b, a, hbNotRoot, haNotRoot, fun h => hne h.symm⟩).fst = a := by simp [hab]
    have hqSnd : (if hab' : a < b then (⟨a, b, haNotRoot, hbNotRoot, fun h => hne h⟩ : CutPair H)
        else ⟨b, a, hbNotRoot, haNotRoot, fun h => hne h.symm⟩).snd = b := by simp [hab]
    obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_true (input := input) hf3
      (by rw [hval, hclk]; exact hab) (by omega)
    have hpl4a : Placed code pcALtB (sweepInitStoreScratch h8 slKeyFst rVal) := placed_append_left hpl4
    have hpl4b : Placed code (pcALtB + (sweepInitStoreScratch h8 slKeyFst rVal).length)
        (sweepInitStoreScratch h8 slKeySnd rClk) := placed_right_eq hpl4 rfl
    have ho12 : (reg s12 rOne).val = 1 := by rw [k12, ho]
    have hz12 : (reg s12 rZero).val = 0 := by rw [k12, hz]
    have hval12 : (reg s12 rVal).val = a.val := by rw [k12, hval]
    have hclk12 : (reg s12 rClk).val = b.val := by rw [k12, hclk]
    obtain ⟨s13, st13, pc13, hKF13, hFr13, k13⟩ := storeScratch_val_steps h8 (input := input) slKeyFst rVal
      (by decide) (by decide) hSlKFW pc12 hpl4a (by omega) ho12
    have ho13 : (reg s13 rOne).val = 1 := by rw [k13 _ (by decide), ho12]
    have hz13 : (reg s13 rZero).val = 0 := by rw [k13 _ (by decide), hz12]
    have hclk13 : (reg s13 rClk).val = b.val := by rw [k13 _ (by decide), hclk12]
    obtain ⟨s14, st14, pc14, hKS14, hFr14, k14⟩ := storeScratch_val_steps h8 (input := input) slKeySnd rClk
      (by decide) (by decide) hSlKSW pc13 hpl4b (by omega) ho13
    refine ⟨s14, 1 + i4.length, by omega, ?_,
      by rw [pc14, Nat.add_assoc, ← hi4Len]; exact hEnd',
      by rw [k14 _ (by decide), hz13], by rw [k14 _ (by decide), ho13], ?_, ?_, ?_⟩
    · rw [hi4Len]; exact Steps.cons st12 (st13.append st14)
    · rw [hFr14 _ (by decide), hKF13, hval12, hqFst]
    · rw [hKS14, hclk13, hqSnd]
    · intro w
      by_cases hw1 : w = slKeyFst
      · exact Or.inl hw1
      by_cases hw2 : w = slKeySnd
      · exact Or.inr (Or.inl hw2)
      exact Or.inr (Or.inr (by rw [hFr14 w hw2, hFr13 w hw1, d12]))
  · have hle : b.val ≤ a.val := by change ¬ (a.val < b.val) at hab; omega
    have hqFst : (if hab' : a < b then (⟨a, b, haNotRoot, hbNotRoot, fun h => hne h⟩ : CutPair H)
        else ⟨b, a, hbNotRoot, haNotRoot, fun h => hne h.symm⟩).fst = b := by simp [hab]
    have hqSnd : (if hab' : a < b then (⟨a, b, haNotRoot, hbNotRoot, fun h => hne h⟩ : CutPair H)
        else ⟨b, a, hbNotRoot, haNotRoot, fun h => hne h.symm⟩).snd = a := by simp [hab]
    obtain ⟨s12, st12, pc12, k12, d12⟩ := step_branchLt_false (input := input) hf3
      (by rw [hclk, hval]; exact hle) (by omega)
    have hpl3a : Placed code (pcBranch + 1) (sweepInitStoreScratch h8 slKeyFst rClk) := placed_append_left hpl3_a
    have hpl3b : Placed code (pcBranch + 1 + (sweepInitStoreScratch h8 slKeyFst rClk).length)
        (sweepInitStoreScratch h8 slKeySnd rVal) := placed_right_eq hpl3_a rfl
    have ho12 : (reg s12 rOne).val = 1 := by rw [k12, ho]
    have hz12 : (reg s12 rZero).val = 0 := by rw [k12, hz]
    have hval12 : (reg s12 rVal).val = a.val := by rw [k12, hval]
    have hclk12 : (reg s12 rClk).val = b.val := by rw [k12, hclk]
    obtain ⟨s13, st13, pc13, hKF13, hFr13, k13⟩ := storeScratch_val_steps h8 (input := input) slKeyFst rClk
      (by decide) (by decide) hSlKFW pc12 hpl3a (by omega) ho12
    have ho13 : (reg s13 rOne).val = 1 := by rw [k13 _ (by decide), ho12]
    have hz13 : (reg s13 rZero).val = 0 := by rw [k13 _ (by decide), hz12]
    have hval13 : (reg s13 rVal).val = a.val := by rw [k13 _ (by decide), hval12]
    obtain ⟨s14, st14, pc14, hKS14, hFr14, k14⟩ := storeScratch_val_steps h8 (input := input) slKeySnd rVal
      (by decide) (by decide) hSlKSW pc13 hpl3b (by omega) ho13
    have hgf14 : code[s14.pc]? = some (.goto pcBSInit) :=
      placed_fetch hpl3_g (i := 0) rfl (by rw [pc14, hi3aLen]; omega)
    have st15 : step code input s14 = some (.next { s14 with pc := pcBSInit }) :=
      step_goto_at hgf14 hBSBnd
    refine ⟨{ s14 with pc := pcBSInit }, 1 + i3a.length + 1, by omega, ?_, rfl,
      by change (reg s14 rZero).val = 0; rw [k14 _ (by decide), hz13],
      by change (reg s14 rOne).val = 1; rw [k14 _ (by decide), ho13],
      ?_, ?_, ?_⟩
    · rw [Nat.add_assoc 1 i3a.length 1, hi3aLen]
      exact Steps.cons st12 ((st13.append st14).append (Steps.cons st15 (Steps.zero _)))
    · change (s14.data[slKeyFst]?).map Fin.val = _; rw [hFr14 _ (by decide), hKF13, hclk12, hqFst]
    · change (s14.data[slKeySnd]?).map Fin.val = _; rw [hKS14, hval13, hqSnd]
    · intro w
      by_cases hw1 : w = slKeyFst
      · exact Or.inl hw1
      by_cases hw2 : w = slKeySnd
      · exact Or.inr (Or.inl hw2)
      exact Or.inr (Or.inr (by change s14.data[w]? = s.data[w]?; rw [hFr14 w hw2, hFr13 w hw1, d12]))

private theorem sweepLoadDictBSArgs_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    (hWork30 : 30 ≤ workCap)
    {pcDictBSInit dictSize dictB dictSndB kf ks : Nat}
    (hDB1 : dictB + 1 < 2 ^ bits)
    (hBnd : pcDictBSInit + ([Instr.mov rClk rZero] ++ loadScratch h8 rRem slDictCnt ++
        loadScratch h8 rChild slDictBase ++ [Instr.add rChild rChild rOne] ++
        loadScratch h8 rCnt slDictSnd ++ loadScratch h8 rStack slKeyFst ++
        loadScratch h8 rVal slKeySnd).length < code.size)
    (hpl : Placed code pcDictBSInit
      ([Instr.mov rClk rZero] ++ loadScratch h8 rRem slDictCnt ++
        loadScratch h8 rChild slDictBase ++ [Instr.add rChild rChild rOne] ++
        loadScratch h8 rCnt slDictSnd ++ loadScratch h8 rStack slKeyFst ++
        loadScratch h8 rVal slKeySnd))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcDictBSInit) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hDC : (s.data[slDictCnt]?).map Fin.val = some dictSize)
    (hDB : (s.data[slDictBase]?).map Fin.val = some dictB)
    (hDS : (s.data[slDictSnd]?).map Fin.val = some dictSndB)
    (hKF : (s.data[slKeyFst]?).map Fin.val = some kf)
    (hKS : (s.data[slKeySnd]?).map Fin.val = some ks) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 62 ∧ Steps code input k s t ∧
      t.pc = pcDictBSInit + ([Instr.mov rClk rZero] ++ loadScratch h8 rRem slDictCnt ++
        loadScratch h8 rChild slDictBase ++ [Instr.add rChild rChild rOne] ++
        loadScratch h8 rCnt slDictSnd ++ loadScratch h8 rStack slKeyFst ++
        loadScratch h8 rVal slKeySnd).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rClk).val = 0 ∧ (reg t rRem).val = dictSize ∧
      (reg t rChild).val = dictB + 1 ∧ (reg t rCnt).val = dictSndB ∧
      (reg t rStack).val = kf ∧ (reg t rVal).val = ks ∧ t.data = s.data := by
  let i5 := [.mov rClk rZero] ++ loadScratch h8 rRem slDictCnt ++ loadScratch h8 rChild slDictBase ++
    [.add rChild rChild rOne] ++ loadScratch h8 rCnt slDictSnd ++
    loadScratch h8 rStack slKeyFst ++ loadScratch h8 rVal slKeySnd
  have hi5Len : i5.length = 1 + (loadScratch h8 rRem slDictCnt).length +
      (loadScratch h8 rChild slDictBase).length + 1 + (loadScratch h8 rCnt slDictSnd).length +
      (loadScratch h8 rStack slKeyFst).length + (loadScratch h8 rVal slKeySnd).length := by
    dsimp only [i5]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hi5Le : i5.length ≤ 62 := by
    have := loadScratch_length_le h8 rRem slDictCnt
    have := loadScratch_length_le h8 rChild slDictBase
    have := loadScratch_length_le h8 rCnt slDictSnd
    have := loadScratch_length_le h8 rStack slKeyFst
    have := loadScratch_length_le h8 rVal slKeySnd
    omega
  have hi5Bnd : pcDictBSInit + i5.length < code.size := hBnd
  have hSlDCW : slDictCnt < workCap := by unfold slDictCnt; omega
  have hSlDBW : slDictBase < workCap := by unfold slDictBase; omega
  have hSlDSW : slDictSnd < workCap := by unfold slDictSnd; omega
  have hSlKFW : slKeyFst < workCap := by unfold slKeyFst; omega
  have hSlKSW : slKeySnd < workCap := by unfold slKeySnd; omega
  have h5_012345 := placed_append_left hpl
  have h5_01234 := placed_append_left h5_012345
  have h5_0123 := placed_append_left h5_01234
  have h5_012 := placed_append_left h5_0123
  have h5_01 := placed_append_left h5_012
  have hpl5_0 : Placed code pcDictBSInit [.mov rClk rZero] := placed_append_left h5_01
  have hpl5_1 : Placed code (pcDictBSInit + 1) (loadScratch h8 rRem slDictCnt) := placed_right_eq h5_01 rfl
  have hpl5_2 : Placed code (pcDictBSInit + 1 + (loadScratch h8 rRem slDictCnt).length)
      (loadScratch h8 rChild slDictBase) :=
    placed_right_eq h5_012 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5_3 : Placed code (pcDictBSInit + 1 + (loadScratch h8 rRem slDictCnt).length +
      (loadScratch h8 rChild slDictBase).length) [.add rChild rChild rOne] :=
    placed_right_eq h5_0123 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5_4 : Placed code (pcDictBSInit + 1 + (loadScratch h8 rRem slDictCnt).length +
      (loadScratch h8 rChild slDictBase).length + 1) (loadScratch h8 rCnt slDictSnd) :=
    placed_right_eq h5_01234 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5_5 : Placed code (pcDictBSInit + 1 + (loadScratch h8 rRem slDictCnt).length +
      (loadScratch h8 rChild slDictBase).length + 1 + (loadScratch h8 rCnt slDictSnd).length)
      (loadScratch h8 rStack slKeyFst) :=
    placed_right_eq h5_012345 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5_6 : Placed code (pcDictBSInit + 1 + (loadScratch h8 rRem slDictCnt).length +
      (loadScratch h8 rChild slDictBase).length + 1 + (loadScratch h8 rCnt slDictSnd).length +
      (loadScratch h8 rStack slKeyFst).length) (loadScratch h8 rVal slKeySnd) :=
    placed_right_eq hpl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  obtain ⟨s16, st16, pc16, r16, k16, d16⟩ := step_mov_at (input := input)
    (placed_fetch hpl5_0 (i := 0) rfl hpc) (by rw [hpc]; omega)
  have hclk16 : (reg s16 rClk).val = 0 := by rw [r16, hz]
  have ho16 : (reg s16 rOne).val = 1 := by rw [k16 _ (by decide), ho]
  have hz16 : (reg s16 rZero).val = 0 := by rw [k16 _ (by decide), hz]
  obtain ⟨s17, st17, pc17, r17, d17, k17⟩ := loadScratch_val_steps h8 (input := input) rRem slDictCnt hSlDCW (by decide)
    (by rw [pc16, hpc]) hpl5_1 (by omega) ho16 (by rw [d16]; exact hDC)
  have ho17 : (reg s17 rOne).val = 1 := by rw [k17 _ (by decide) (by decide), ho16]
  have hz17 : (reg s17 rZero).val = 0 := by rw [k17 _ (by decide) (by decide), hz16]
  have hclk17 : (reg s17 rClk).val = 0 := by rw [k17 _ (by decide) (by decide), hclk16]
  obtain ⟨s18, st18, pc18, r18, d18, k18⟩ := loadScratch_val_steps h8 (input := input) rChild slDictBase hSlDBW (by decide)
    pc17 hpl5_2 (by omega) ho17 (by rw [d17, d16]; exact hDB)
  have ho18 : (reg s18 rOne).val = 1 := by rw [k18 _ (by decide) (by decide), ho17]
  have hz18 : (reg s18 rZero).val = 0 := by rw [k18 _ (by decide) (by decide), hz17]
  have hclk18 : (reg s18 rClk).val = 0 := by rw [k18 _ (by decide) (by decide), hclk17]
  have hrem18 : (reg s18 rRem).val = dictSize := by rw [k18 _ (by decide) (by decide), r17]
  obtain ⟨s19, st19, pc19, r19, k19, d19⟩ := step_add15_at (input := input) (s := s18)
    (placed_fetch hpl5_3 (i := 0) rfl pc18) (by rw [pc18]; omega)
  have hch19 : (reg s19 rChild).val = dictB + 1 := by
    rw [r19, WordOps.add_val, r18, ho18]
    exact Nat.mod_eq_of_lt hDB1
  have ho19 : (reg s19 rOne).val = 1 := by rw [k19 _ (by decide), ho18]
  have hz19 : (reg s19 rZero).val = 0 := by rw [k19 _ (by decide), hz18]
  have hclk19 : (reg s19 rClk).val = 0 := by rw [k19 _ (by decide), hclk18]
  have hrem19 : (reg s19 rRem).val = dictSize := by rw [k19 _ (by decide), hrem18]
  obtain ⟨s20, st20, pc20, r20, d20, k20⟩ := loadScratch_val_steps h8 (input := input) rCnt slDictSnd hSlDSW (by decide)
    (by rw [pc19, pc18]) hpl5_4 (by omega) ho19 (by rw [d19, d18, d17, d16]; exact hDS)
  have ho20 : (reg s20 rOne).val = 1 := by rw [k20 _ (by decide) (by decide), ho19]
  have hz20 : (reg s20 rZero).val = 0 := by rw [k20 _ (by decide) (by decide), hz19]
  have hclk20 : (reg s20 rClk).val = 0 := by rw [k20 _ (by decide) (by decide), hclk19]
  have hrem20 : (reg s20 rRem).val = dictSize := by rw [k20 _ (by decide) (by decide), hrem19]
  have hch20 : (reg s20 rChild).val = dictB + 1 := by rw [k20 _ (by decide) (by decide), hch19]
  have hd20 : s20.data = s.data := d20.trans (d19.trans (d18.trans (d17.trans d16)))
  obtain ⟨s21, st21, pc21, r21, d21, k21⟩ := loadScratch_val_steps h8 (input := input) rStack slKeyFst hSlKFW (by decide)
    pc20 hpl5_5 (by omega) ho20 (by rw [hd20]; exact hKF)
  have ho21 : (reg s21 rOne).val = 1 := by rw [k21 _ (by decide) (by decide), ho20]
  have hz21 : (reg s21 rZero).val = 0 := by rw [k21 _ (by decide) (by decide), hz20]
  have hclk21 : (reg s21 rClk).val = 0 := by rw [k21 _ (by decide) (by decide), hclk20]
  have hrem21 : (reg s21 rRem).val = dictSize := by rw [k21 _ (by decide) (by decide), hrem20]
  have hch21 : (reg s21 rChild).val = dictB + 1 := by rw [k21 _ (by decide) (by decide), hch20]
  have hcnt21 : (reg s21 rCnt).val = dictSndB := by rw [k21 _ (by decide) (by decide), r20]
  obtain ⟨s22, st22, pc22, r22, d22, k22⟩ := loadScratch_val_steps h8 (input := input) rVal slKeySnd hSlKSW (by decide)
    pc21 hpl5_6 (by omega) ho21 (by rw [d21, hd20]; exact hKS)
  refine ⟨s22, i5.length, hi5Le, ?_, by rw [pc22, hi5Len]; omega,
    by rw [k22 _ (by decide) (by decide), hz21],
    by rw [k22 _ (by decide) (by decide), ho21],
    by rw [k22 _ (by decide) (by decide), hclk21],
    by rw [k22 _ (by decide) (by decide), hrem21],
    by rw [k22 _ (by decide) (by decide), hch21],
    by rw [k22 _ (by decide) (by decide), hcnt21],
    by rw [k22 _ (by decide) (by decide), r21],
    r22, d22.trans (d21.trans hd20)⟩
  rw [hi5Len]
  exact (((((Steps.cons st16 (Steps.zero _)).append st17).append st18).append
    (Steps.cons st19 (Steps.zero _))).append st20).append (st21.append st22)
private theorem sweepDictBSTail_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    (hWork30 : 30 ≤ workCap)
    {pcTail pcWriteLabel dictSlotsB slotIdx slotVal : Nat}
    (hSlotFit : dictSlotsB + slotIdx < workCap)
    (hWL : pcWriteLabel < code.size)
    (hBnd : pcTail + (loadScratch h8 rTmp slDictSlots).length + 3 < code.size)
    (hpl1 : Placed code pcTail (loadScratch h8 rTmp slDictSlots))
    (hpl2 : Placed code (pcTail + (loadScratch h8 rTmp slDictSlots).length)
      [Instr.add rTmp rTmp rPtr, Instr.loadData rVal rTmp,
       Instr.branchLt rZero rVal pcWriteLabel (pcTail + (loadScratch h8 rTmp slDictSlots).length + 3)])
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcTail) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hPtr : (reg s rPtr).val = slotIdx)
    (hSlSlots : (s.data[slDictSlots]?).map Fin.val = some dictSlotsB)
    (hSlotMem : (s.data[dictSlotsB + slotIdx]?).map Fin.val = some slotVal) :
    if slotVal = 0 then
      ∃ t : State (layout bits inputCap workCap hi hw),
        Steps code input ((loadScratch h8 rTmp slDictSlots).length + 3) s t ∧
        t.pc = pcTail + (loadScratch h8 rTmp slDictSlots).length + 3 ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rPtr).val = slotIdx ∧ t.data = s.data
    else
      ∃ t : State (layout bits inputCap workCap hi hw),
        Steps code input ((loadScratch h8 rTmp slDictSlots).length + 3) s t ∧
        t.pc = pcWriteLabel ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rVal).val = slotVal ∧ t.data = s.data := by
  have hSlDSlW : slDictSlots < workCap := by unfold slDictSlots; omega
  obtain ⟨s24, st24, pc24, r24, d24, k24⟩ := loadScratch_val_steps h8 (input := input) rTmp slDictSlots
    hSlDSlW (by decide) hpc hpl1 (by omega) ho hSlSlots
  have hz24 : (reg s24 rZero).val = 0 := by rw [k24 _ (by decide) (by decide), hz]
  have ho24 : (reg s24 rOne).val = 1 := by rw [k24 _ (by decide) (by decide), ho]
  have hptr24 : (reg s24 rPtr).val = slotIdx := by rw [k24 _ (by decide) (by decide), hPtr]
  obtain ⟨s25, st25, pc25, r25, k25, d25⟩ := step_add15_at (input := input) (s := s24)
    (placed_fetch hpl2 (i := 0) rfl pc24) (by rw [pc24]; omega)
  have htmp25 : (reg s25 rTmp).val = dictSlotsB + slotIdx := by
    rw [r25, WordOps.add_val, r24, hptr24]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hSlotFit hw)
  obtain ⟨s26, st26, pc26, r26, k26, d26⟩ := step_loadData_reg (s := s25)
    (placed_fetch hpl2 (i := 1) rfl (by rw [pc25, pc24])) (by rw [pc25, pc24]; omega)
    (by rw [htmp25]; exact hSlotFit) (by rw [htmp25, d25, d24]; exact hSlotMem)
  have hz26 : (reg s26 rZero).val = 0 := by rw [k26 _ (by decide), k25 _ (by decide), hz24]
  have ho26 : (reg s26 rOne).val = 1 := by rw [k26 _ (by decide), k25 _ (by decide), ho24]
  have hptr26 : (reg s26 rPtr).val = slotIdx := by rw [k26 _ (by decide), k25 _ (by decide), hptr24]
  have hd26 : s26.data = s.data := d26.trans (d25.trans d24)
  have hfTail : code[s26.pc]? = some (.branchLt rZero rVal pcWriteLabel
      (pcTail + (loadScratch h8 rTmp slDictSlots).length + 3)) :=
    placed_fetch hpl2 (i := 2) rfl (by rw [pc26, pc25, pc24])
  have hPre26 : Steps code input ((loadScratch h8 rTmp slDictSlots).length + 2) s s26 :=
    st24.append (.cons st25 (.cons st26 (.zero _)))
  by_cases hSlotZ : slotVal = 0
  · rw [ite_eq_left hSlotZ]
    obtain ⟨s27, st27, pc27, k27, d27⟩ := step_branchLt_false (input := input) hfTail
      (by rw [r26, hz26, hSlotZ]; exact Nat.le_refl 0) hBnd
    exact ⟨s27, hPre26.append (.cons st27 (.zero _)), pc27,
      by rw [k27, hz26], by rw [k27, ho26], by rw [k27, hptr26], d27.trans hd26⟩
  · rw [ite_eq_right hSlotZ]
    obtain ⟨s27, st27, pc27, k27, d27⟩ := step_branchLt_true (input := input) hfTail
      (by rw [hz26, r26]; omega) hWL
    exact ⟨s27, hPre26.append (.cons st27 (.zero _)), pc27,
      by rw [k27, hz26], by rw [k27, ho26], by rw [k27, r26], d27.trans hd26⟩

theorem sweepPairAndDictBS_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcStart pcKeepP pcWriteZero pcWriteLabel : Nat}
    (hKP : pcKeepP < code.size) (hWZ : pcWriteZero < code.size) (hWL : pcWriteLabel < code.size)
    (hSz : pcStart + (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length < code.size)
    (hpl : Placed code pcStart (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel))
    {y : Vertex H} (hNoRoot : H.hasQuotientArcBool H.root y = false)
    {rowLo rowHi : Nat} (hLoHi : rowLo < rowHi) (hRHm : rowHi ≤ H.arcCount)
    (hDiff : rowHi - rowLo = (rows.row y).length)
    (hPB : ∀ t' : Fin (rows.row y).length,
      (s.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
        some ((rows.row y)[t'.val]'t'.isLt).val)
    (hpc : s.pc = pcStart) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlRL : (s.data[slRowLo]?).map Fin.val = some rowLo)
    (hSlRH : (s.data[slRowHi]?).map Fin.val = some rowHi) :
    let c := orderedConfig dictRows large
    if (rows.row y).length = 2 then
      ∃ q : CutPair H, ∃ slotIdx : Nat, ∃ hit : slotIdx < c.dict.size,
        preparedKey H (rows.row y) = some q ∧ preparedKey H (dictRows.row y) = some q ∧
        (PairLookup.lookup c.dict (c.code q)).1 = some slotIdx ∧ c.dict[slotIdx]'hit = c.code q ∧
        if sRef.tables.slotAt slotIdx = 0 then
          ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
            k ≤ 150 + 17 * (OracleContract.L H.vertexCount + 1) ∧
            Steps code input k s t ∧
            t.pc = pcStart + (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length ∧
            (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rPtr).val = slotIdx ∧
            (t.data[slKeyFst]?).map Fin.val = some q.fst.val ∧
            (t.data[slKeySnd]?).map Fin.val = some q.snd.val ∧
            ∀ w, w = slKeyFst ∨ w = slKeySnd ∨ t.data[w]? = s.data[w]?
        else
          ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
            k ≤ 150 + 17 * (OracleContract.L H.vertexCount + 1) ∧
            Steps code input k s t ∧ t.pc = pcWriteLabel ∧
            (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
            (reg t rVal).val = sRef.tables.slotAt slotIdx ∧
            ∀ w, w = slKeyFst ∨ w = slKeySnd ∨ t.data[w]? = s.data[w]?
    else
      preparedKey H (rows.row y) = none ∧
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 30 ∧ Steps code input k s t ∧ t.pc = pcKeepP ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data := by
  let n := H.vertexCount
  let m := H.arcCount
  let c := orderedConfig dictRows large
  have hWork' : 32 * n + 7 * m + 17 ≤ workCap := hWork
  have hDictLe : c.dict.size ≤ n := dict_size_le H dictRows large
  have hNWork : n < workCap := by omega
  have hDictW : c.dict.size < workCap := Nat.lt_of_le_of_lt hDictLe hNWork
  have hDFstW : ∀ i < c.dict.size, dictBase n m + 1 + i < workCap := fun i hi' => by
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at hWork' ⊢; omega
  have hDSndW : ∀ i < c.dict.size, dictBase n m + 1 + c.dict.size + i < workCap := fun i hi' => by
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at hWork' ⊢; omega
  have hSlotsW : ∀ i < c.dict.size, dictBase n m + 1 + 2 * c.dict.size + i < workCap := fun i hi' => by
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at hWork' ⊢; omega
  have hSlRLW : slRowLo < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlRHW : slRowHi < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlPBW : slPredBuf < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlKFW : slKeyFst < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlKSW : slKeySnd < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlDCW : slDictCnt < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlDBW : slDictBase < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlDSW : slDictSnd < workCap := scratch_lt_workCap30 hWork large (by decide)
  have hSlDSlW : slDictSlots < workCap := scratch_lt_workCap30 hWork large (by decide)
  let i0 := loadScratch h8 rStack slRowLo ++ loadScratch h8 rRem slRowHi ++
    [.sub rRem rRem rStack, .add rTmp rOne rOne]
  let pcPair := pcStart + i0.length + 2
  let i1 : List (Instr bits 15) :=
    [.branchLt rRem rTmp pcKeepP (pcStart + i0.length + 1), .branchLt rTmp rRem pcKeepP pcPair]
  let i2 := loadScratch h8 rTmp slPredBuf ++ [.add rTmp rTmp rStack, .loadData rVal rTmp,
    .add rTmp rTmp rOne, .loadData rClk rTmp]
  let i3a := sweepInitStoreScratch h8 slKeyFst rClk ++ sweepInitStoreScratch h8 slKeySnd rVal
  let i4 := sweepInitStoreScratch h8 slKeyFst rVal ++ sweepInitStoreScratch h8 slKeySnd rClk
  let pcALtB := pcPair + i2.length + 1 + i3a.length + 1
  let pcDictBSInit := pcALtB + i4.length
  let i3 : List (Instr bits 15) := [.branchLt rVal rClk pcALtB (pcPair + i2.length + 1)] ++
    i3a ++ [.goto pcDictBSInit]
  let i5 := [.mov rClk rZero] ++ loadScratch h8 rRem slDictCnt ++ loadScratch h8 rChild slDictBase ++
    [.add rChild rChild rOne] ++ loadScratch h8 rCnt slDictSnd ++
    loadScratch h8 rStack slKeyFst ++ loadScratch h8 rVal slKeySnd
  let pcDictBS := pcDictBSInit + i5.length
  let bsCode : List (Instr bits 15) :=
    [ .branchLt rClk rRem (pcDictBS + 1) pcWriteZero,
      .sub rTmp rRem rClk,
      .shr1 rTmp rTmp,
      .add rPtr rClk rTmp,
      .add rTmp rChild rPtr,
      .loadData rTin rTmp,
      .branchLt rTin rStack (pcDictBS + 13) (pcDictBS + 7),
      .branchLt rStack rTin (pcDictBS + 15) (pcDictBS + 8),
      .add rTmp rCnt rPtr,
      .loadData rTin rTmp,
      .branchLt rTin rVal (pcDictBS + 13) (pcDictBS + 11),
      .branchLt rVal rTin (pcDictBS + 15) (pcDictBS + 12),
      .goto (pcDictBS + 17),
      .add rClk rPtr rOne, .goto pcDictBS,
      .mov rRem rPtr, .goto pcDictBS ]
  let iTail := loadScratch h8 rTmp slDictSlots ++
    [.add rTmp rTmp rPtr, .loadData rVal rTmp,
     .branchLt rZero rVal pcWriteLabel (pcDictBS + 17 + (loadScratch h8 rTmp slDictSlots).length + 3)]
  have hi0Len : i0.length = (loadScratch h8 rStack slRowLo).length + (loadScratch h8 rRem slRowHi).length + 2 := by
    dsimp only [i0]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hi0Le : i0.length ≤ 26 := by
    have := loadScratch_length_le h8 rStack slRowLo
    have := loadScratch_length_le h8 rRem slRowHi
    omega
  have hi2Len : i2.length = (loadScratch h8 rTmp slPredBuf).length + 4 := by
    dsimp only [i2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hi2Le : i2.length ≤ 16 := by
    have := loadScratch_length_le h8 rTmp slPredBuf; omega
  have hi3aLen : i3a.length = (sweepInitStoreScratch h8 slKeyFst rClk).length +
      (sweepInitStoreScratch h8 slKeySnd rVal).length := by
    dsimp only [i3a]; simp only [List.length_append]
  have hi3aLe : i3a.length ≤ 24 := by
    have := sweepInitStoreScratch_length_le h8 slKeyFst rClk
    have := sweepInitStoreScratch_length_le h8 slKeySnd rVal
    omega
  have hi3Len : i3.length = 1 + i3a.length + 1 := by
    dsimp only [i3]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hi4Len : i4.length = (sweepInitStoreScratch h8 slKeyFst rVal).length +
      (sweepInitStoreScratch h8 slKeySnd rClk).length := by
    dsimp only [i4]; simp only [List.length_append]
  have hi4Le : i4.length ≤ 24 := by
    have := sweepInitStoreScratch_length_le h8 slKeyFst rVal
    have := sweepInitStoreScratch_length_le h8 slKeySnd rClk
    omega
  have hi5Le : i5.length ≤ 62 := by
    have := loadScratch_length_le h8 rRem slDictCnt
    have := loadScratch_length_le h8 rChild slDictBase
    have := loadScratch_length_le h8 rCnt slDictSnd
    have := loadScratch_length_le h8 rStack slKeyFst
    have := loadScratch_length_le h8 rVal slKeySnd
    dsimp only [i5]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hiTailLen : iTail.length = (loadScratch h8 rTmp slDictSlots).length + 3 := by
    dsimp only [iTail]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hiTailLe : iTail.length ≤ 15 := by
    have := loadScratch_length_le h8 rTmp slDictSlots; omega
  have hbsLen : bsCode.length = 17 := rfl
  have hLenBlk : (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length =
      i0.length + 2 + i2.length + i3.length + i4.length + i5.length + 17 + iTail.length := by
    unfold sweepPairAndDictBS
    dsimp only [i0, pcPair, i1, i2, i3a, i4, pcALtB, pcDictBSInit, i3, i5, pcDictBS, iTail]
    simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hSzTot : pcDictBS + 17 + iTail.length < code.size := by
    rw [hLenBlk] at hSz
    dsimp only [pcDictBS, pcDictBSInit, pcALtB, pcPair] at hSz ⊢; omega
  have hAfterBlkBnd : pcStart + (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length <
      code.size := hSz
  have hAfterEq : pcStart + (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length =
      pcDictBS + 17 + iTail.length := by
    rw [hLenBlk]; dsimp only [pcDictBS, pcDictBSInit, pcALtB, pcPair]; omega
  unfold sweepPairAndDictBS at hpl
  dsimp only at hpl
  have h012345bst := placed_append_left hpl
  have h012345bs := placed_append_left h012345bst
  have h012345 := placed_append_left h012345bs
  have h01234 := placed_append_left h012345
  have h0123 := placed_append_left h01234
  have h012 := placed_append_left h0123
  have h01 := placed_append_left h012
  have hpl0 : Placed code pcStart i0 := placed_append_left h01
  have hpl1 : Placed code (pcStart + i0.length) i1 := placed_right_eq h01 rfl
  have hpl2 : Placed code pcPair i2 :=
    placed_right_eq h012 (by dsimp only [pcPair, i0, i1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl3 : Placed code (pcPair + i2.length) i3 :=
    placed_right_eq h0123 (by dsimp only [pcPair, i0, i1, i2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl4 : Placed code pcALtB i4 :=
    placed_right_eq h01234 (by
      dsimp only [pcALtB, pcPair, i0, i1, i2, i3, i3a]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5 : Placed code pcDictBSInit i5 :=
    placed_right_eq h012345 (by
      dsimp only [pcDictBSInit, pcALtB, pcPair, i0, i1, i2, i3, i3a, i4]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hplBS : Placed code pcDictBS bsCode :=
    placed_right_eq h012345bs (by
      dsimp only [pcDictBS, pcDictBSInit, pcALtB, pcPair, i0, i1, i2, i3, i3a, i4, i5]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hplT1 : Placed code (pcDictBS + 17) (loadScratch h8 rTmp slDictSlots) :=
    placed_right_eq h012345bst (by
      dsimp only [pcDictBS, pcDictBSInit, pcALtB, pcPair, i0, i1, i2, i3, i3a, i4, i5, bsCode]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hplT2 : Placed code (pcDictBS + 17 + (loadScratch h8 rTmp slDictSlots).length)
      ([.add rTmp rTmp rPtr, .loadData rVal rTmp,
        .branchLt rZero rVal pcWriteLabel (pcDictBS + 17 + (loadScratch h8 rTmp slDictSlots).length + 3)] :
        List (Instr bits 15)) :=
    placed_right_eq hpl (by
      dsimp only [pcDictBS, pcDictBSInit, pcALtB, pcPair, i0, i1, i2, i3, i3a, i4, i5, bsCode, iTail]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  clear hpl h012345bst h012345bs h012345 h01234 h0123 h012 h01
  -- Execute i0
  have hpl0_012 := placed_append_left hpl0
  have hpl0_0 := placed_append_left hpl0_012
  have hpl0_1 : Placed code (pcStart + (loadScratch h8 rStack slRowLo).length) (loadScratch h8 rRem slRowHi) :=
    placed_right_eq hpl0_012 rfl
  have hpl0_23 : Placed code (pcStart + (loadScratch h8 rStack slRowLo).length + (loadScratch h8 rRem slRowHi).length)
      ([.sub rRem rRem rStack, .add rTmp rOne rOne] : List (Instr bits 15)) :=
    placed_right_eq hpl0 (by simp only [List.length_append]; omega)
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rStack slRowLo hSlRLW (by decide)
    hpc hpl0_0 (by omega) ho hSlRL
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ := loadScratch_val_steps h8 (input := input) rRem slRowHi hSlRHW (by decide)
    pc1 hpl0_1 (by omega) ho1 (by rw [d1]; exact hSlRH)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hz1]
  have hstk2 : (reg s2 rStack).val = rowLo := by rw [k2 _ (by decide) (by decide), r1]
  obtain ⟨s3, st3, pc3, r3, k3, d3⟩ := step_sub15_at (input := input) (s := s2)
    (placed_fetch hpl0_23 (i := 0) rfl pc2) (by rw [pc2]; omega)
  have hrem3 : (reg s3 rRem).val = (rows.row y).length := by
    rw [r3, sub_val_exact (by rw [r2, hstk2]; exact Nat.le_of_lt hLoHi), r2, hstk2, hDiff]
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide), ho2]
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide), hz2]
  have hstk3 : (reg s3 rStack).val = rowLo := by rw [k3 _ (by decide), hstk2]
  obtain ⟨s4, st4, pc4, r4, k4, d4⟩ := step_add15_at (input := input) (s := s3)
    (placed_fetch hpl0_23 (i := 1) rfl (by rw [pc3, pc2])) (by rw [pc3, pc2]; omega)
  have htmp4 : (reg s4 rTmp).val = 2 := by
    rw [r4, WordOps.add_val, ho3]; exact Nat.mod_eq_of_lt (by omega)
  have ho4 : (reg s4 rOne).val = 1 := by rw [k4 _ (by decide), ho3]
  have hz4 : (reg s4 rZero).val = 0 := by rw [k4 _ (by decide), hz3]
  have hstk4 : (reg s4 rStack).val = rowLo := by rw [k4 _ (by decide), hstk3]
  have hrem4 : (reg s4 rRem).val = (rows.row y).length := by rw [k4 _ (by decide), hrem3]
  have hd4 : s4.data = s.data := d4.trans (d3.trans (d2.trans d1))
  have hpc4 : s4.pc = pcStart + i0.length := by rw [pc4, pc3, pc2, hi0Len]; omega
  have hPre4 : Steps code input i0.length s s4 := by
    rw [hi0Len]; exact (st1.append st2).append (.cons st3 (.cons st4 (.zero _)))
  have hf1_0 : code[s4.pc]? = some (.branchLt rRem rTmp pcKeepP (pcStart + i0.length + 1)) :=
    placed_fetch hpl1 (i := 0) rfl hpc4
  by_cases hTwo : (rows.row y).length = 2
  · rw [ite_eq_left hTwo]
    obtain ⟨s5, st5, pc5, k5, d5⟩ := step_branchLt_false (input := input) hf1_0
      (by rw [htmp4, hrem4, hTwo]; exact Nat.le_refl 2) (by omega)
    have hf1_1 : code[s5.pc]? = some (.branchLt rTmp rRem pcKeepP pcPair) :=
      placed_fetch hpl1 (i := 1) rfl pc5
    obtain ⟨s6, st6, pc6, k6, d6⟩ := step_branchLt_false (input := input) hf1_1
      (by rw [k5, k5, hrem4, htmp4, hTwo]; exact Nat.le_refl 2) (by omega)
    have ho6 : (reg s6 rOne).val = 1 := by rw [k6, k5, ho4]
    have hz6 : (reg s6 rZero).val = 0 := by rw [k6, k5, hz4]
    have hstk6 : (reg s6 rStack).val = rowLo := by rw [k6, k5, hstk4]
    have hd6 : s6.data = s.data := d6.trans (d5.trans hd4)
    have hPre6 : Steps code input (i0.length + 2) s s6 :=
      hPre4.append (.cons st5 (.cons st6 (.zero _)))
    -- Unpack rows.row y = [a, b]
    obtain ⟨a, b, hRowEq⟩ : ∃ a b : Vertex H, rows.row y = [a, b] := by
      cases hR : rows.row y with
      | nil => simp [hR] at hTwo
      | cons a rest =>
        cases rest with
        | nil => simp [hR] at hTwo
        | cons b rest2 =>
          cases rest2 with
          | nil => exact ⟨a, b, rfl⟩
          | cons _ _ => simp [hR] at hTwo
    have hne : a ≠ b := by
      have nd := (rows.spec y).nodup
      rw [hRowEq] at nd
      exact (List.pairwise_cons.mp (show ([a, b] : List (Vertex H)).Pairwise (fun u v => u ≠ v) from nd)).1
        b (by simp)
    have haNotRoot : a ≠ H.root := by
      intro haR
      have hArc : H.HasQuotientArc H.root y := (rows.spec y).cover H.root |>.mp (by rw [hRowEq, haR]; simp)
      have hBool : H.hasQuotientArcBool H.root y = true := (hasQuotientArcBool_eq_true_iff H H.root y).mpr hArc
      rw [hBool] at hNoRoot; contradiction
    have hbNotRoot : b ≠ H.root := by
      intro hbR
      have hArc : H.HasQuotientArc H.root y := (rows.spec y).cover H.root |>.mp (by rw [hRowEq, hbR]; simp)
      have hBool : H.hasQuotientArcBool H.root y = true := (hasQuotientArcBool_eq_true_iff H H.root y).mpr hArc
      rw [hBool] at hNoRoot; contradiction
    have hPBa : (s6.data[predBufBase n m + rowLo]?).map Fin.val = some a.val := by
      have := hPB ⟨0, by rw [hTwo]; omega⟩
      rw [hd6]; simpa [hRowEq] using this
    have hPBb : (s6.data[predBufBase n m + (rowLo + 1)]?).map Fin.val = some b.val := by
      have h1 := hPB ⟨1, by rw [hTwo]; omega⟩
      change (s.data[predBufBase n m + rowLo + 1]?).map Fin.val =
        some ((rows.row y)[1]'(by rw [hRowEq]; simp)).val at h1
      rw [show predBufBase n m + rowLo + 1 = predBufBase n m + (rowLo + 1) by omega] at h1
      rw [hd6]; simpa [hRowEq] using h1
    have hPBAddr0 : predBufBase n m + rowLo < workCap := by
      simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
        csrArenaWords] at hWork' ⊢; omega
    have hPBAddr1 : predBufBase n m + (rowLo + 1) < workCap := by
      simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
        csrArenaWords] at hWork' ⊢; omega
    -- Execute i2: load a into rVal, b into rClk
    have hpl2a : Placed code pcPair (loadScratch h8 rTmp slPredBuf) := placed_append_left hpl2
    have hpl2b : Placed code (pcPair + (loadScratch h8 rTmp slPredBuf).length)
        ([.add rTmp rTmp rStack, .loadData rVal rTmp, .add rTmp rTmp rOne, .loadData rClk rTmp] : List (Instr bits 15)) :=
      placed_right_eq hpl2 rfl
    obtain ⟨s7, st7, pc7, r7, d7, k7⟩ := loadScratch_val_steps h8 (input := input) rTmp slPredBuf hSlPBW (by decide)
      pc6 hpl2a (by omega) ho6 (by rw [hd6]; exact inv.slPredBufVal)
    have ho7 : (reg s7 rOne).val = 1 := by rw [k7 _ (by decide) (by decide), ho6]
    have hz7 : (reg s7 rZero).val = 0 := by rw [k7 _ (by decide) (by decide), hz6]
    have hstk7 : (reg s7 rStack).val = rowLo := by rw [k7 _ (by decide) (by decide), hstk6]
    obtain ⟨s8, st8, pc8, r8, k8, d8⟩ := step_add15_at (input := input) (s := s7)
      (placed_fetch hpl2b (i := 0) rfl pc7) (by rw [pc7]; omega)
    have htmp8 : (reg s8 rTmp).val = predBufBase n m + rowLo := by
      rw [r8, WordOps.add_val, r7, hstk7]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hPBAddr0 hw)
    obtain ⟨s9, st9, pc9, r9, k9, d9⟩ := step_loadData_reg (s := s8)
      (placed_fetch hpl2b (i := 1) rfl (by rw [pc8, pc7])) (by rw [pc8, pc7]; omega)
      (by rw [htmp8]; exact hPBAddr0) (by rw [htmp8, d8, d7]; exact hPBa)
    obtain ⟨s10, st10, pc10, r10, k10, d10⟩ := step_add15_at (input := input) (s := s9)
      (placed_fetch hpl2b (i := 2) rfl (by rw [pc9, pc8, pc7])) (by rw [pc9, pc8, pc7]; omega)
    have htmp10 : (reg s10 rTmp).val = predBufBase n m + (rowLo + 1) := by
      rw [r10, WordOps.add_val, k9 _ (by decide), htmp8, k9 _ (by decide), k8 _ (by decide), ho7]
      exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hPBAddr1 hw)
    obtain ⟨s11, st11, pc11, r11, k11, d11⟩ := step_loadData_reg (s := s10)
      (placed_fetch hpl2b (i := 3) rfl (by rw [pc10, pc9, pc8, pc7])) (by rw [pc10, pc9, pc8, pc7]; omega)
      (by rw [htmp10]; exact hPBAddr1) (by rw [htmp10, d10, d9, d8, d7]; exact hPBb)
    have hval11 : (reg s11 rVal).val = a.val := by
      rw [k11 _ (by decide), k10 _ (by decide), r9]
    have hclk11 : (reg s11 rClk).val = b.val := r11
    have ho11 : (reg s11 rOne).val = 1 := by
      rw [k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), ho7]
    have hz11 : (reg s11 rZero).val = 0 := by
      rw [k11 _ (by decide), k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), hz7]
    have hd11 : s11.data = s.data := d11.trans (d10.trans (d9.trans (d8.trans (d7.trans hd6))))
    have hpc11 : s11.pc = pcPair + i2.length := by rw [pc11, pc10, pc9, pc8, pc7, hi2Len]; omega
    have hPre11 : Steps code input (i0.length + 2 + i2.length) s s11 := by
      have hi2St : Steps code input i2.length s6 s11 := by
        rw [hi2Len]; exact st7.append (.cons st8 (.cons st9 (.cons st10 (.cons st11 (.zero _)))))
      exact hPre6.append hi2St
    -- Canonical pair q
    let q : CutPair H := if _hab : a < b then
      ⟨a, b, haNotRoot, hbNotRoot, fun h => hne h⟩
      else ⟨b, a, hbNotRoot, haNotRoot, fun h => hne h.symm⟩
    have hPrepRow : preparedKey H (rows.row y) = some q := by
      rw [hRowEq]
      by_cases hab : a < b
      · simp [preparedKey, candidatePairOfPreds, q, hab, haNotRoot, hbNotRoot]
      · have hba : b < a := by
          change b.val < a.val
          have : a.val ≠ b.val := fun h => hne (Fin.ext h)
          change ¬ (a.val < b.val) at hab; omega
        simp [preparedKey, candidatePairOfPreds, q, hab, hba, haNotRoot, hbNotRoot]
    have hPrepDict : preparedKey H (dictRows.row y) = some q := by
      have h1 := preparedKey_eq_candidate y (dictRows.row y) (dictRows.spec y)
      have h2 := preparedKey_eq_candidate y (rows.row y) (rows.spec y)
      rw [h1, ← h2, hPrepRow]
    have hMemDict : c.code q ∈ c.dict.toList := by
      have hs := (ForestDictionary.dictionary_spec dictRows orderedPairCode).2.1 (c.code q)
      exact hs.mpr ⟨y, q, hPrepDict, rfl⟩
    obtain ⟨slotIdx, hLookupSome⟩ := PairLookup.lookup_member_iff c.dict (c.code q) c.sorted |>.mpr
      (by
        obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hMemDict
        exact ⟨k, by simpa using hk, by simpa using hget⟩)
    obtain ⟨hit, hAtSlot⟩ := (PairLookup.lookup_eq_some_iff c.dict (c.code q) c.sorted slotIdx).mp hLookupSome
    have hCodeQ : c.code q = (q.fst.val, q.snd.val) := by
      cases q; rfl
    -- Execute i3/i4 to store (q.fst, q.snd) in slKeyFst, slKeySnd
    obtain ⟨s15, k34, hk34, st34, pc15, hz15, ho15, hKF15, hKS15, hFr15⟩ :=
      sweepStoreSortedPair_steps h8 input (by omega) hne haNotRoot hbNotRoot
        (by dsimp only [pcDictBS, pcDictBSInit, pcALtB, pcPair] at hSzTot ⊢; omega)
        s11 hpc11 hz11 ho11 hval11 hclk11
        hpl3 hpl4 rfl
    have hPresGe30_15 : ∀ w, 30 ≤ w → s15.data[w]? = s.data[w]? := fun w hw30 => by
      rw [← hd11]
      exact (hFr15 w).elim (fun h => by unfold slKeyFst at h; omega)
        (fun h => h.elim (fun h => by unfold slKeySnd at h; omega) id)
    have hPresLt28_15 : ∀ sl, sl < 28 → s15.data[sl]? = s.data[sl]? := fun sl hsl => by
      rw [← hd11]
      exact (hFr15 sl).elim (fun h => by unfold slKeyFst at h; omega)
        (fun h => h.elim (fun h => by unfold slKeySnd at h; omega) id)
    -- Execute i5
    have hDB1 : dictBase n m + 1 < 2 ^ bits := Nat.lt_of_lt_of_le (by
      simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
        rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at hWork' ⊢; omega) hw
    have hi5Bnd : pcDictBSInit + i5.length < code.size := by
      dsimp only [pcDictBS] at hSzTot; omega
    obtain ⟨s22, k5, hk5, st5, pc22, hz22, ho22, hclk22, hrem22, hch22, hcnt22, hstk22, hval22, hd22⟩ :=
      sweepLoadDictBSArgs_steps h8 input (by omega) hDB1 hi5Bnd hpl5 s15 pc15 hz15 ho15
        (by rw [hPresLt28_15 _ (by decide)]; exact inv.slDictCntVal)
        (by rw [hPresLt28_15 _ (by decide)]; exact inv.slDictBaseVal)
        (by rw [hPresLt28_15 _ (by decide)]; exact inv.slDictSndVal)
        hKF15 hKS15
    have hKeys22 : ∀ i (hi_lt : i < c.dict.size),
        (s22.data[dictBase n m + 1 + i]?).map Fin.val = some (c.dict[i]'hi_lt).1 ∧
        (s22.data[dictBase n m + 1 + c.dict.size + i]?).map Fin.val = some (c.dict[i]'hi_lt).2 := fun i hi_lt => by
      have h30a : 30 ≤ dictBase n m + 1 + i := by
        have := scratch_lt_orderBase (n := n) (m := m) (sl := 29) large (by decide)
        simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
      have h30b : 30 ≤ dictBase n m + 1 + c.dict.size + i := by omega
      rw [hd22, hPresGe30_15 _ h30a, hPresGe30_15 _ h30b]
      exact inv.dictKeys i hi_lt
    have hSpanL : c.dict.size - 0 ≤ 2 ^ OracleContract.L H.vertexCount := by
      have := vertexCount_lt_two_pow_L H.vertexCount; omega
    obtain ⟨s23, kBS, hkBS, stBS, pc23, hz23, ho23, hptr23, hd23⟩ :=
      dictBSLoop_steps input c.sorted hit (hAtSlot.trans hCodeQ) hDFstW hDSndW hDictW hWZ
        (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hSzTot) hplBS
        (OracleContract.L H.vertexCount) 0 c.dict.size s22 (Nat.zero_le _) hit (Nat.le_refl _) hSpanL
        hKeys22 pc22 hz22 ho22 hclk22 hrem22 hch22 hcnt22 hstk22 hval22
    -- Execute iTail: load slots[slotIdx], branch if > 0 to pcWriteLabel
    have hSlotAddrW : dictBase n m + 1 + 2 * c.dict.size + slotIdx < workCap := hSlotsW slotIdx hit
    have hd23' : s23.data = s15.data := hd23.trans hd22
    have hSlSlotVal23 : (s23.data[slDictSlots]?).map Fin.val =
        some (dictBase n m + 1 + 2 * c.dict.size) := by
      rw [hd23', hPresLt28_15 _ (by decide)]; exact inv.slDictSlotsVal
    have hSlotMem23 : (s23.data[dictBase n m + 1 + 2 * c.dict.size + slotIdx]?).map Fin.val =
        some (sRef.tables.slotAt slotIdx) := by
      have h30 : 30 ≤ dictBase n m + 1 + 2 * c.dict.size + slotIdx := by
        have := scratch_lt_orderBase (n := n) (m := m) (sl := 29) large (by decide)
        simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; omega
      rw [hd23', hPresGe30_15 _ h30]; exact inv.dictSlots slotIdx hit
    have hTailBnd : pcDictBS + 17 + (loadScratch h8 rTmp slDictSlots).length + 3 < code.size := by
      rw [Nat.add_assoc (pcDictBS + 17), ← hiTailLen]; exact hSzTot
    have hFr15' : ∀ w, w = slKeyFst ∨ w = slKeySnd ∨ s15.data[w]? = s.data[w]? := fun w =>
      (hFr15 w).elim Or.inl
        (fun h => h.elim (fun h2 => Or.inr (Or.inl h2))
          (fun hEq => Or.inr (Or.inr (hEq.trans (congrArg (·[w]?) hd11)))))
    have hTailRes := sweepDictBSTail_steps h8 input (by omega) hSlotAddrW hWL hTailBnd hplT1 hplT2
      s23 pc23 hz23 ho23 hptr23 hSlSlotVal23 hSlotMem23
    have hPre23 : Steps code input (i0.length + 2 + i2.length + k34 + k5 + kBS) s s23 :=
      (((hPre11.append st34).append st5).append stBS)
    have hCostTail : i0.length + 2 + i2.length + k34 + k5 + kBS +
        ((loadScratch h8 rTmp slDictSlots).length + 3) ≤
        150 + 17 * (OracleContract.L H.vertexCount + 1) := by
      have := loadScratch_length_le h8 rTmp slDictSlots
      clear hpl0 hpl1 hpl2 hpl3 hpl4 hpl5 hplBS hplT1 hplT2 hPre11 hPre23 hTailRes st34 st5 stBS
        hKeys22 inv hPB hDFstW hDSndW hSlotsW hMemDict hLookupSome hAtSlot hSpanL
      omega
    refine ⟨q, slotIdx, hit, hPrepRow, hPrepDict, hLookupSome, hAtSlot, ?_⟩
    by_cases hSlotZ : sRef.tables.slotAt slotIdx = 0
    · rw [ite_eq_left hSlotZ]
      obtain ⟨s27, stT, pc27, hz27, ho27, hptr27, hd27⟩ := ite_elim_true hSlotZ hTailRes
      have hd27' : s27.data = s15.data := hd27.trans hd23'
      refine ⟨s27, i0.length + 2 + i2.length + k34 + k5 + kBS +
          ((loadScratch h8 rTmp slDictSlots).length + 3), hCostTail,
        hPre23.append stT, ?_, hz27, ho27, hptr27,
        by rw [hd27']; exact hKF15, by rw [hd27']; exact hKS15,
        fun w => by rw [hd27']; exact hFr15' w⟩
      rw [pc27, hAfterEq, hiTailLen, Nat.add_assoc (pcDictBS + 17)]
    · rw [ite_eq_right hSlotZ]
      obtain ⟨s27, stT, pc27, hz27, ho27, hval27, hd27⟩ := ite_elim_false hSlotZ hTailRes
      have hd27' : s27.data = s15.data := hd27.trans hd23'
      refine ⟨s27, i0.length + 2 + i2.length + k34 + k5 + kBS +
          ((loadScratch h8 rTmp slDictSlots).length + 3), hCostTail,
        hPre23.append stT, pc27, hz27, ho27, hval27, fun w => by rw [hd27']; exact hFr15' w⟩
  · rw [ite_eq_right hTwo]
    have hPrepNone : preparedKey H (rows.row y) = none := by
      cases hR : rows.row y with
      | nil => rfl
      | cons a rest =>
        cases rest with
        | nil => rfl
        | cons b rest2 =>
          cases rest2 with
          | nil => simp [hR] at hTwo
          | cons _ _ => rfl
    refine ⟨hPrepNone, ?_⟩
    by_cases hLt2 : (rows.row y).length < 2
    · obtain ⟨s5, st5, pc5, k5, d5⟩ := step_branchLt_true (input := input) hf1_0
        (by rw [hrem4, htmp4]; exact hLt2) hKP
      exact ⟨s5, i0.length + 1, by omega, hPre4.append (.cons st5 (.zero _)), pc5,
        by rw [k5, hz4], by rw [k5, ho4], d5.trans hd4⟩
    · have hle2 : 2 ≤ (rows.row y).length := by omega
      have hgt2 : 2 < (rows.row y).length := by omega
      obtain ⟨s5, st5, pc5, k5, d5⟩ := step_branchLt_false (input := input) hf1_0
        (by rw [htmp4, hrem4]; exact hle2) (by omega)
      have hf1_1 : code[s5.pc]? = some (.branchLt rTmp rRem pcKeepP pcPair) :=
        placed_fetch hpl1 (i := 1) rfl pc5
      obtain ⟨s6, st6, pc6, k6, d6⟩ := step_branchLt_true (input := input) hf1_1
        (by rw [k5, htmp4, k5, hrem4]; exact hgt2) hKP
      exact ⟨s6, i0.length + 2, by omega, hPre4.append (.cons st5 (.cons st6 (.zero _))), pc6,
        by rw [k6, k5, hz4], by rw [k6, k5, ho4], d6.trans (d5.trans hd4)⟩


end SweepLoopExec

end PaperB.RamForestProgram.Sweep
