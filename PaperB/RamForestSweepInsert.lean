module

public import PaperB.RamForestSweepProbe

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

def sweepSkewInsert {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcWriteLabel : Nat) : List (Instr bits 15) :=
  let i10Read :=
    loadScratch h8 rStack slAncNode ++
    loadScratch h8 rClk slNext ++
    loadScratch h8 rTin slJumpBase ++
    [ .add rRem rTin rStack, .add rRem rRem rStack, .add rRem rRem rStack,
      .add rTmp rRem rOne, .loadData rVal rTmp, .add rTmp rTmp rOne, .loadData rChild rTmp,
      .add rRem rTin rChild, .add rRem rRem rChild, .add rRem rRem rChild,
      .add rTmp rRem rOne, .loadData rCnt rTmp, .add rTmp rTmp rOne, .loadData rCmd rTmp,
      .add rRem rTin rCmd, .add rRem rRem rCmd, .add rRem rRem rCmd,
      .add rTmp rRem rOne, .loadData rTout rTmp,
      .sub rRem rVal rCnt, .sub rOff rCnt rTout ]
  let pcCmp := pcStart + i10Read.length
  let pcUseP := pcCmp + 3
  let pcHaveJump := pcUseP + 1
  let i10Cmp : List (Instr bits 15) :=
    [ .branchLt rZero rRem (pcCmp + 1) pcUseP,
      .branchLt rRem rOff pcUseP (pcCmp + 2),
      .branchLt rOff rRem pcUseP pcHaveJump,
      .mov rCmd rStack ]
  let i10Write :=
    [ .add rRem rTin rClk, .add rRem rRem rClk, .add rRem rRem rClk,
      .storeData rRem rStack,
      .add rRem rRem rOne, .add rVal rVal rOne, .storeData rRem rVal,
      .add rRem rRem rOne, .storeData rRem rCmd ] ++
    loadScratch h8 rTmp slDictSlots ++ [.add rTmp rTmp rPtr, .storeData rTmp rClk] ++
    loadScratch h8 rVal slKeyFst ++ [.add rVal rVal rOne] ++
    loadScratch h8 rTmp slBackFst ++ [.add rTmp rTmp rClk, .storeData rTmp rVal] ++
    loadScratch h8 rVal slKeySnd ++
    loadScratch h8 rTmp slBackSnd ++ [.add rTmp rTmp rClk, .storeData rTmp rVal] ++
    loadScratch h8 rTmp slParents ++ [.add rTmp rTmp rClk, .storeData rTmp rStack] ++
    [.add rVal rClk rOne] ++ sweepInitStoreScratch h8 slNext rVal ++
    [.mov rVal rClk, .goto pcWriteLabel]
  i10Read ++ i10Cmp ++ i10Write

def sweepInstallTail {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcWriteLabel pcLoopTop : Nat) : List (Instr bits 15) :=
  let keepB := loadScratch h8 rVal slAncNode ++ [.goto pcWriteLabel]
  let zeroB : List (Instr bits 15) := [.mov rVal rZero]
  let writeLabB :=
    loadScratch h8 rClk slY ++
    loadScratch h8 rTmp slLabels ++
    [.add rTmp rTmp rClk, .storeData rTmp rVal] ++
    loadScratch h8 rClk slIdx ++
    [.add rClk rClk rOne] ++
    sweepInitStoreScratch h8 slIdx rClk ++
    [.goto pcLoopTop]
  keepB ++ zeroB ++ writeLabB

def sweepInstallKeepLen {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : Nat :=
  (loadScratch h8 rVal slAncNode).length + 1

def sweepInstallBlock {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcLoopTop : Nat) : List (Instr bits 15) :=
  let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
  let d2 := (sweepSkewInsert h8 0 0).length
  let pcKeepP := pcStart + d1 + d2
  let pcWriteZero := pcKeepP + sweepInstallKeepLen h8
  let pcWriteLabel := pcWriteZero + 1
  sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel ++
  sweepSkewInsert h8 (pcStart + d1) pcWriteLabel ++
  sweepInstallTail h8 pcWriteLabel pcLoopTop


theorem sweepSkewInsert_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (a b : Nat) :
    (sweepSkewInsert h8 a b).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepSkewInsert
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, nonHalt, Bool.and_self]

theorem sweepInstallTail_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (a b : Nat) :
    (sweepInstallTail h8 a b).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepInstallTail
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, nonHalt, Bool.and_self]

theorem sweepInstallBlock_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcLoopTop : Nat) :
    (sweepInstallBlock h8 pcStart pcLoopTop).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepInstallBlock
  simp only [List.all_append, sweepPairAndDictBS_nonHalt, sweepSkewInsert_nonHalt,
    sweepInstallTail_nonHalt, Bool.and_self]


theorem sweepSkewInsert_length {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepSkewInsert h8 s a).length = (sweepSkewInsert h8 0 0).length := by
  unfold sweepSkewInsert; simp only [List.length_append, List.length_cons, List.length_nil]

theorem sweepInstallTail_length {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepInstallTail h8 s a).length = (sweepInstallTail h8 0 0).length := by
  unfold sweepInstallTail; simp only [List.length_append, List.length_cons, List.length_nil]

theorem sweepInstallBlock_length {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepInstallBlock h8 s a).length = (sweepInstallBlock h8 0 0).length := by
  unfold sweepInstallBlock
  simp only [List.length_append]
  rw [sweepPairAndDictBS_length h8, sweepSkewInsert_length h8, sweepInstallTail_length h8]
  symm
  rw [sweepPairAndDictBS_length h8, sweepSkewInsert_length h8, sweepInstallTail_length h8]


end SweepLoopProgram

section SweepLoopExec

open PaperB.ForestHead _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

private theorem validJumpForest_depthOf_jump_le_zero {F : JumpForest} (hF : ValidJumpForest F)
    {u : Nat} (hu : u < F.size) :
    F.depthOf (F.jumpOf u) ≤ F.depthOf u ∧
      (F.depthOf (F.jumpOf u) = F.depthOf u → u = 0 ∧ F.jumpOf u = 0) := by
  obtain ⟨exps, inv⟩ := hF.exists_forestInvariant
  by_cases hu0 : u = 0
  · subst hu0
    rw [inv.root_jump]
    exact ⟨Nat.le_refl _, fun _ => ⟨rfl, rfl⟩⟩
  · have hPos : 0 < u := Nat.pos_of_ne_zero hu0
    have hlt : F.depthOf (F.jumpOf u) < F.depthOf u := inv.depth_jump_lt hPos hu
    exact ⟨Nat.le_of_lt hlt, fun he => False.elim (by omega)⟩

private theorem validJumpForest_depthOf_le_pred {F : JumpForest} (hF : ValidJumpForest F) :
    ∀ u < F.size, F.depthOf u ≤ u := by
  induction hF with
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


private theorem sweepReadJumpRecord_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {pcE n m u : Nat} {src dstD dstJ : Fin 15}
    (hSrcNe : src ≠ rRem ∧ src ≠ rTmp ∧ src ≠ dstD ∧ src ≠ dstJ)
    (_hTinNe : rTin ≠ rRem ∧ rTin ≠ rTmp ∧ rTin ≠ dstD ∧ rTin ≠ dstJ)
    (hOneNe : rOne ≠ rRem ∧ rOne ≠ rTmp ∧ rOne ≠ dstD ∧ rOne ≠ dstJ)
    (hDJNe : dstD ≠ rRem ∧ dstD ≠ rTmp ∧ dstD ≠ dstJ)
    (_hJNe : dstJ ≠ rRem ∧ dstJ ≠ rTmp)
    (hFit : jumpBase n m + 3 * u + 2 < workCap)
    (hBnd : pcE + 7 < code.size)
    (hpl : Placed code pcE
      [ Instr.add rRem rTin src, Instr.add rRem rRem src, Instr.add rRem rRem src,
        Instr.add rTmp rRem rOne, Instr.loadData dstD rTmp, Instr.add rTmp rTmp rOne, Instr.loadData dstJ rTmp ])
    {F : JumpForest} {s : State (layout bits inputCap workCap hi hw)}
    (hRecs : Records (jumpBase n m) F s.data) (hu : u < F.size)
    (hpc : s.pc = pcE) (hTin : (reg s rTin).val = jumpBase n m) (hOne : (reg s rOne).val = 1)
    (hSrc : (reg s src).val = u) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input 7 s t ∧ t.pc = pcE + 7 ∧
      (reg t dstD).val = F.depthOf u ∧ (reg t dstJ).val = F.jumpOf u ∧
      (∀ r : Fin 15, r ≠ rRem → r ≠ rTmp → r ≠ dstD → r ≠ dstJ → reg t r = reg s r) ∧
      t.data = s.data := by
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ := step_add15_at (input := input) (placed_fetch hpl (i := 0) rfl hpc) (by rw [hpc]; omega)
  have hrem1 : (reg s1 rRem).val = jumpBase n m + u := by
    rw [r1, WordOps.add_val, hTin, hSrc]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + u < workCap) hw)
  have hsrc1 : (reg s1 src).val = u := by rw [k1 _ hSrcNe.1, hSrc]
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ := step_add15_at (input := input) (placed_fetch hpl (i := 1) rfl (by rw [pc1, hpc])) (by rw [pc1, hpc]; omega)
  have hrem2 : (reg s2 rRem).val = jumpBase n m + 2 * u := by
    rw [r2, WordOps.add_val, hrem1, hsrc1, show jumpBase n m + u + u = jumpBase n m + 2 * u by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 2 * u < workCap) hw)
  have hsrc2 : (reg s2 src).val = u := by rw [k2 _ hSrcNe.1, hsrc1]
  obtain ⟨s3, st3, pc3, r3, k3, d3⟩ := step_add15_at (input := input) (placed_fetch hpl (i := 2) rfl (by rw [pc2, pc1, hpc])) (by rw [pc2, pc1, hpc]; omega)
  have hrem3 : (reg s3 rRem).val = jumpBase n m + 3 * u := by
    rw [r3, WordOps.add_val, hrem2, hsrc2, show jumpBase n m + 2 * u + u = jumpBase n m + 3 * u by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * u < workCap) hw)
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ hOneNe.1, k2 _ hOneNe.1, k1 _ hOneNe.1, hOne]
  obtain ⟨s4, st4, pc4, r4, k4, d4⟩ := step_add15_at (input := input) (placed_fetch hpl (i := 3) rfl (by rw [pc3, pc2, pc1, hpc])) (by rw [pc3, pc2, pc1, hpc]; omega)
  have htmp4 : (reg s4 rTmp).val = jumpBase n m + 3 * u + 1 := by
    rw [r4, WordOps.add_val, hrem3, ho3]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * u + 1 < workCap) hw)
  have hd4 : s4.data = s.data := d4.trans (d3.trans (d2.trans d1))
  obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_loadData_reg (placed_fetch hpl (i := 4) rfl (by rw [pc4, pc3, pc2, pc1, hpc]))
    (by rw [pc4, pc3, pc2, pc1, hpc]; omega) (by rw [htmp4]; omega)
    (by rw [htmp4, hd4, show jumpBase n m + 3 * u + 1 = jumpBase n m + 1 + 3 * u by omega]; exact hRecs.depth u hu)
  have ho5 : (reg s5 rOne).val = 1 := by rw [k5 _ hOneNe.2.2.1, k4 _ hOneNe.2.1, ho3]
  obtain ⟨s6, st6, pc6, r6, k6, d6⟩ := step_add15_at (input := input) (placed_fetch hpl (i := 5) rfl (by rw [pc5, pc4, pc3, pc2, pc1, hpc])) (by rw [pc5, pc4, pc3, pc2, pc1, hpc]; omega)
  have htmp6 : (reg s6 rTmp).val = jumpBase n m + 3 * u + 2 := by
    rw [r6, WordOps.add_val, k5 _ hDJNe.2.1.symm, htmp4, ho5]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * u + 2 < workCap) hw)
  have hd6 : s6.data = s.data := d6.trans (d5.trans hd4)
  obtain ⟨s7, st7, pc7, r7, k7, d7⟩ := step_loadData_reg (placed_fetch hpl (i := 6) rfl (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hpc]))
    (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hpc]; omega) (by rw [htmp6]; omega)
    (by rw [htmp6, hd6, show jumpBase n m + 3 * u + 2 = jumpBase n m + 2 + 3 * u by omega]; exact hRecs.jump u hu)
  refine ⟨s7, .cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 (.zero _))))))),
    by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, hpc],
    by rw [k7 _ hDJNe.2.2, k6 _ hDJNe.2.1, r5], r7, fun r h1 h2 h3 h4 => ?_, d7.trans hd6⟩
  rw [k7 _ h4, k6 _ h2, k5 _ h3, k4 _ h2, k3 _ h1, k2 _ h1, k1 _ h1]

theorem sweepSkewInsert_readCore_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap)
    {s3 : State (layout bits inputCap workCap hi hw)}
    {F : JumpForest} (hRecs : Records (jumpBase n m) F s3.data) (_hFLe : F.size ≤ n)
    {pcCore ancNode slotIdx : Nat}
    (hCoreBnd : pcCore + 21 + 4 < code.size)
    (hplCore : Placed code pcCore
      [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
        Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
        Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
        Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
        Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
        Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
        Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ])
    (hAncLt : ancNode < F.size)
    (pc3 : s3.pc = pcCore) (hz3 : (reg s3 rZero).val = 0) (ho3 : (reg s3 rOne).val = 1)
    (hptr3 : (reg s3 rPtr).val = slotIdx) (hstk3 : (reg s3 rStack).val = ancNode)
    (hclk3 : (reg s3 rClk).val = F.size) (r3 : (reg s3 rTin).val = jumpBase n m) :
    let jp := F.jumpOf ancNode
    let jjp := F.jumpOf jp
    ∃ s24 : State (layout bits inputCap workCap hi hw),
      Steps code input 21 s3 s24 ∧ s24.pc = pcCore + 21 ∧
      (reg s24 rZero).val = 0 ∧ (reg s24 rOne).val = 1 ∧ (reg s24 rPtr).val = slotIdx ∧
      (reg s24 rStack).val = ancNode ∧ (reg s24 rClk).val = F.size ∧
      (reg s24 rTin).val = jumpBase n m ∧ (reg s24 rVal).val = F.depthOf ancNode ∧
      (reg s24 rCmd).val = jjp ∧
      (reg s24 rRem).val = F.depthOf ancNode - F.depthOf jp ∧
      (reg s24 rOff).val = F.depthOf jp - F.depthOf jjp ∧
      s24.data = s3.data := by
  let jp := F.jumpOf ancNode
  let jjp := F.jumpOf jp
  have hJpLt : jp < F.size := hRecs.valid.jumpOf_lt_size hAncLt
  have hJjpLt : jjp < F.size := hRecs.valid.jumpOf_lt_size hJpLt
  have hDJp := validJumpForest_depthOf_jump_le_zero hRecs.valid hAncLt
  have hDJjp := validJumpForest_depthOf_jump_le_zero hRecs.valid hJpLt
  have hJBnd : ∀ u < F.size, jumpBase n m + 3 * u + 2 < workCap := fun u hu => by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at hWork32 ⊢; omega
  have hJBndA := hJBnd ancNode hAncLt
  have hJBndJ := hJBnd jp hJpLt
  have hJBndJJ := hJBnd jjp hJjpLt
  have hplC_07 : Placed code pcCore
      [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
        Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp ] :=
    placed_append_left (placed_append_left (show Placed code pcCore (([Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
      Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp] ++
      [Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
       Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp]) ++
      [Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
       Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp, Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout]) from hplCore))
  have hplC_714 : Placed code (pcCore + 7)
      [ Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
        Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp ] :=
    placed_right_eq (placed_append_left (show Placed code pcCore (([Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
      Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp] ++
      [Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
       Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp]) ++
      [Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
       Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp, Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout]) from hplCore)) rfl
  have hplC_1421 : Placed code (pcCore + 14)
      [ Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
        Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
        Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ] :=
    placed_right_eq (show Placed code pcCore (([Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
      Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp] ++
      [Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
       Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp]) ++
      [Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
       Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp, Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout]) from hplCore) rfl
  obtain ⟨s10, st0_7, pc10, hval10, r10, k10, hd10⟩ := sweepReadJumpRecord_steps input
    (src := rStack) (dstD := rVal) (dstJ := rChild)
    (by decide) (by decide) (by decide) (by decide) (by decide) hJBndA (by omega)
    hplC_07 hRecs hAncLt pc3 r3 ho3 hstk3
  have hKeep3_10 : ∀ r : Fin 15, r = rZero ∨ r = rOne ∨ r = rPtr ∨ r = rStack ∨ r = rClk ∨ r = rTin → reg s10 r = reg s3 r := by
    intro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact k10 _ (by decide) (by decide) (by decide) (by decide)
  obtain ⟨s17, st7_14, pc17, hcnt17, r17, k17, hd17⟩ := sweepReadJumpRecord_steps input
    (src := rChild) (dstD := rCnt) (dstJ := rCmd)
    (by decide) (by decide) (by decide) (by decide) (by decide) hJBndJ (by omega)
    hplC_714 (by rw [hd10]; exact hRecs) hJpLt pc10
    (by rw [hKeep3_10 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), r3])
    (by rw [hKeep3_10 _ (Or.inr (Or.inl rfl)), ho3]) r10
  have hKeep10_17 : ∀ r : Fin 15, r = rZero ∨ r = rOne ∨ r = rPtr ∨ r = rStack ∨ r = rClk ∨ r = rTin ∨ r = rVal →
      reg s17 r = reg s10 r := by
    intro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact k17 _ (by decide) (by decide) (by decide) (by decide)
  have htin17 : (reg s17 rTin).val = jumpBase n m := by
    rw [hKeep10_17 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))),
        hKeep3_10 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), r3]
  have ho17 : (reg s17 rOne).val = 1 := by
    rw [hKeep10_17 _ (Or.inr (Or.inl rfl)), hKeep3_10 _ (Or.inr (Or.inl rfl)), ho3]
  have hval17 : (reg s17 rVal).val = F.depthOf ancNode := by
    rw [hKeep10_17 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), hval10]
  have hpc17 : s17.pc = pcCore + 14 := by rw [pc17]
  obtain ⟨s18, st18, pc18, r18, k18, d18⟩ := step_add15_at (input := input) (placed_fetch hplC_1421 (i := 0) rfl hpc17) (by rw [hpc17]; omega)
  have hrem18 : (reg s18 rRem).val = jumpBase n m + jjp := by
    rw [r18, WordOps.add_val, htin17, r17]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + jjp < workCap) hw)
  have hcmd18 : (reg s18 rCmd).val = jjp := by rw [k18 _ (by decide), r17]
  obtain ⟨s19, st19, pc19, r19, k19, d19⟩ := step_add15_at (input := input) (placed_fetch hplC_1421 (i := 1) rfl (by rw [pc18, hpc17])) (by rw [pc18, hpc17]; omega)
  have hrem19 : (reg s19 rRem).val = jumpBase n m + 2 * jjp := by
    rw [r19, WordOps.add_val, hrem18, hcmd18, show jumpBase n m + jjp + jjp = jumpBase n m + 2 * jjp by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 2 * jjp < workCap) hw)
  have hcmd19 : (reg s19 rCmd).val = jjp := by rw [k19 _ (by decide), hcmd18]
  obtain ⟨s20, st20, pc20, r20, k20, d20⟩ := step_add15_at (input := input) (placed_fetch hplC_1421 (i := 2) rfl (by rw [pc19, pc18, hpc17])) (by rw [pc19, pc18, hpc17]; omega)
  have hrem20 : (reg s20 rRem).val = jumpBase n m + 3 * jjp := by
    rw [r20, WordOps.add_val, hrem19, hcmd19, show jumpBase n m + 2 * jjp + jjp = jumpBase n m + 3 * jjp by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * jjp < workCap) hw)
  have ho20 : (reg s20 rOne).val = 1 := by rw [k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), ho17]
  have hcmd20 : (reg s20 rCmd).val = jjp := by rw [k20 _ (by decide), hcmd19]
  obtain ⟨s21, st21, pc21, r21, k21, d21⟩ := step_add15_at (input := input) (placed_fetch hplC_1421 (i := 3) rfl (by rw [pc20, pc19, pc18, hpc17])) (by rw [pc20, pc19, pc18, hpc17]; omega)
  have htmp21 : (reg s21 rTmp).val = jumpBase n m + 3 * jjp + 1 := by
    rw [r21, WordOps.add_val, hrem20, ho20]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * jjp + 1 < workCap) hw)
  have hd21 : s21.data = s3.data := d21.trans (d20.trans (d19.trans (d18.trans (hd17.trans hd10))))
  obtain ⟨s22, st22, pc22, r22, k22, d22⟩ := step_loadData_reg (placed_fetch hplC_1421 (i := 4) rfl (by rw [pc21, pc20, pc19, pc18, hpc17]))
    (by rw [pc21, pc20, pc19, pc18, hpc17]; omega) (by rw [htmp21]; omega)
    (by rw [htmp21, hd21, show jumpBase n m + 3 * jjp + 1 = jumpBase n m + 1 + 3 * jjp by omega]; exact hRecs.depth jjp hJjpLt)
  have hval22 : (reg s22 rVal).val = F.depthOf ancNode := by
    rw [k22 _ (by decide), k21 _ (by decide), k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), hval17]
  have hcnt22 : (reg s22 rCnt).val = F.depthOf jp := by
    rw [k22 _ (by decide), k21 _ (by decide), k20 _ (by decide), k19 _ (by decide), k18 _ (by decide), hcnt17]
  obtain ⟨s23, st23, pc23, r23, k23, d23⟩ := step_sub15_at (input := input) (placed_fetch hplC_1421 (i := 5) rfl (by rw [pc22, pc21, pc20, pc19, pc18, hpc17]))
    (by rw [pc22, pc21, pc20, pc19, pc18, hpc17]; omega)
  have hrem23 : (reg s23 rRem).val = F.depthOf ancNode - F.depthOf jp := by
    rw [r23, sub_val_exact (by rw [hcnt22, hval22]; exact hDJp.1), hval22, hcnt22]
  have hcnt23 : (reg s23 rCnt).val = F.depthOf jp := by rw [k23 _ (by decide), hcnt22]
  have htout23 : (reg s23 rTout).val = F.depthOf jjp := by rw [k23 _ (by decide), r22]
  obtain ⟨s24, st24, pc24, r24, k24, d24⟩ := step_sub15_at (input := input) (placed_fetch hplC_1421 (i := 6) rfl (by rw [pc23, pc22, pc21, pc20, pc19, pc18, hpc17]))
    (by rw [pc23, pc22, pc21, pc20, pc19, pc18, hpc17]; omega)
  have hKeepFrom17 : ∀ r : Fin 15, r = rZero ∨ r = rOne ∨ r = rPtr ∨ r = rStack ∨ r = rClk ∨ r = rTin → reg s24 r = reg s17 r := by
    intro r hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), k20 _ (by decide), k19 _ (by decide), k18 _ (by decide)]
  have hKeepFrom3 : ∀ r : Fin 15, r = rZero ∨ r = rOne ∨ r = rPtr ∨ r = rStack ∨ r = rClk ∨ r = rTin → reg s24 r = reg s3 r := by
    intro r hr
    exact (hKeepFrom17 r hr).trans ((hKeep10_17 r (by rcases hr with h | h | h | h | h | h <;> simp [h])).trans (hKeep3_10 r hr))
  have h14_21 : Steps code input 7 s17 s24 :=
    .cons st18 (.cons st19 (.cons st20 (.cons st21 (.cons st22 (.cons st23 (.cons st24 (.zero _)))))))
  refine ⟨s24, (st0_7.append st7_14).append h14_21, by rw [pc24, pc23, pc22, pc21, pc20, pc19, pc18, hpc17],
    by rw [hKeepFrom3 _ (Or.inl rfl), hz3], by rw [hKeepFrom3 _ (Or.inr (Or.inl rfl)), ho3],
    by rw [hKeepFrom3 _ (Or.inr (Or.inr (Or.inl rfl))), hptr3],
    by rw [hKeepFrom3 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hstk3],
    by rw [hKeepFrom3 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hclk3],
    by rw [hKeepFrom3 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))), r3],
    by rw [k24 _ (by decide), k23 _ (by decide), hval22],
    by rw [k24 _ (by decide), k23 _ (by decide), k22 _ (by decide), k21 _ (by decide), hcmd20],
    by rw [k24 _ (by decide), hrem23],
    by rw [r24, sub_val_exact (by rw [htout23, hcnt23]; exact hDJjp.1), hcnt23, htout23],
    d24.trans (d23.trans (d22.trans hd21))⟩

theorem sweepSkewInsert_readCmp_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (_hLarge : 3 ≤ n)
    {s : State (layout bits inputCap workCap hi hw)}
    {F : JumpForest} (hRecs : Records (jumpBase n m) F s.data) (hFLe : F.size ≤ n)
    {pcStart : Nat}
    (hBnd : pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
        loadScratch h8 rTin slJumpBase ++
        [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
          Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
          Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
          Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
          Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
          Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
          Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 4 < code.size)
    (hplR : Placed code pcStart
      (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
        loadScratch h8 rTin slJumpBase ++
        [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
          Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
          Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
          Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
          Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
          Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
          Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]))
    (hplC : Placed code (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
        loadScratch h8 rTin slJumpBase ++
        [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
          Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
          Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
          Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
          Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
          Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
          Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length)
      [ Instr.branchLt rZero rRem (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
          loadScratch h8 rTin slJumpBase ++
          [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
            Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
            Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
            Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
            Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
            Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
            Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 1)
          (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
          loadScratch h8 rTin slJumpBase ++
          [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
            Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
            Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
            Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
            Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
            Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
            Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 3),
        Instr.branchLt rRem rOff (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
          loadScratch h8 rTin slJumpBase ++
          [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
            Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
            Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
            Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
            Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
            Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
            Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 3)
          (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
          loadScratch h8 rTin slJumpBase ++
          [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
            Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
            Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
            Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
            Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
            Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
            Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 2),
        Instr.branchLt rOff rRem (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
          loadScratch h8 rTin slJumpBase ++
          [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
            Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
            Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
            Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
            Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
            Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
            Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 3)
          (pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
          loadScratch h8 rTin slJumpBase ++
          [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
            Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
            Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
            Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
            Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
            Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
            Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 4),
        Instr.mov rCmd rStack ])
    {ancNode slotIdx : Nat}
    (hAncLt : ancNode < F.size)
    (hpc : s.pc = pcStart) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hPtr : (reg s rPtr).val = slotIdx)
    (hSlAnc : (s.data[slAncNode]?).map Fin.val = some ancNode)
    (hSlNext : (s.data[slNext]?).map Fin.val = some F.size)
    (hSlJump : (s.data[slJumpBase]?).map Fin.val = some (jumpBase n m)) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 65 ∧ Steps code input k s t ∧
      t.pc = pcStart + (loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
        loadScratch h8 rTin slJumpBase ++
        [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
          Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
          Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
          Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
          Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
          Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
          Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]).length + 4 ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rPtr).val = slotIdx ∧
      (reg t rStack).val = ancNode ∧ (reg t rClk).val = F.size ∧
      (reg t rTin).val = jumpBase n m ∧ (reg t rVal).val = F.depthOf ancNode ∧
      (reg t rCmd).val = (F.mkAppendedRecord ancNode).jump ∧ t.data = s.data := by
  let iCore : List (Instr bits 15) :=
    [ .add rRem rTin rStack, .add rRem rRem rStack, .add rRem rRem rStack,
      .add rTmp rRem rOne, .loadData rVal rTmp, .add rTmp rTmp rOne, .loadData rChild rTmp,
      .add rRem rTin rChild, .add rRem rRem rChild, .add rRem rRem rChild,
      .add rTmp rRem rOne, .loadData rCnt rTmp, .add rTmp rTmp rOne, .loadData rCmd rTmp,
      .add rRem rTin rCmd, .add rRem rRem rCmd, .add rRem rRem rCmd,
      .add rTmp rRem rOne, .loadData rTout rTmp,
      .sub rRem rVal rCnt, .sub rOff rCnt rTout ]
  let iRead := loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++
    loadScratch h8 rTin slJumpBase ++ iCore
  have hiReadLen : iRead.length = (loadScratch h8 rStack slAncNode).length +
      (loadScratch h8 rClk slNext).length + (loadScratch h8 rTin slJumpBase).length + 21 := by
    dsimp only [iRead, iCore]; simp only [List.length_append]; rfl
  have hiReadLe : iRead.length ≤ 57 := by
    have := loadScratch_length_le h8 rStack slAncNode
    have := loadScratch_length_le h8 rClk slNext
    have := loadScratch_length_le h8 rTin slJumpBase
    omega
  have hiReadBnd : pcStart + iRead.length + 4 < code.size := hBnd
  have hSlAW : slAncNode < workCap := by unfold slAncNode; omega
  have hSlNW : slNext < workCap := by unfold slNext; omega
  have hSlJW : slJumpBase < workCap := by unfold slJumpBase; omega
  have hr012 := placed_append_left hplR
  have hr01 := placed_append_left hr012
  have hplR0 : Placed code pcStart (loadScratch h8 rStack slAncNode) := placed_append_left hr01
  have hplR1 : Placed code (pcStart + (loadScratch h8 rStack slAncNode).length)
      (loadScratch h8 rClk slNext) := placed_right_eq hr01 rfl
  have hplR2 : Placed code (pcStart + (loadScratch h8 rStack slAncNode).length +
      (loadScratch h8 rClk slNext).length) (loadScratch h8 rTin slJumpBase) :=
    placed_right_eq hr012 (by simp only [List.length_append]; omega)
  let pcCore := pcStart + (loadScratch h8 rStack slAncNode).length +
    (loadScratch h8 rClk slNext).length + (loadScratch h8 rTin slJumpBase).length
  have hplCore : Placed code pcCore iCore := placed_right_eq hplR (by simp only [List.length_append]; omega)
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rStack slAncNode hSlAW (by decide)
    hpc hplR0 (by omega) ho hSlAnc
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have hptr1 : (reg s1 rPtr).val = slotIdx := by rw [k1 _ (by decide) (by decide), hPtr]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ := loadScratch_val_steps h8 (input := input) rClk slNext hSlNW (by decide)
    pc1 hplR1 (by omega) ho1 (by rw [d1]; exact hSlNext)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hz1]
  have hptr2 : (reg s2 rPtr).val = slotIdx := by rw [k2 _ (by decide) (by decide), hptr1]
  have hstk2 : (reg s2 rStack).val = ancNode := by rw [k2 _ (by decide) (by decide), r1]
  obtain ⟨s3, st3, pc3, r3, d3, k3⟩ := loadScratch_val_steps h8 (input := input) rTin slJumpBase hSlJW (by decide)
    pc2 hplR2 (by omega) ho2 (by rw [d2, d1]; exact hSlJump)
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide) (by decide), ho2]
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide) (by decide), hz2]
  have hptr3 : (reg s3 rPtr).val = slotIdx := by rw [k3 _ (by decide) (by decide), hptr2]
  have hstk3 : (reg s3 rStack).val = ancNode := by rw [k3 _ (by decide) (by decide), hstk2]
  have hclk3 : (reg s3 rClk).val = F.size := by rw [k3 _ (by decide) (by decide), r2]
  have hd3 : s3.data = s.data := d3.trans (d2.trans d1)
  have hCoreBnd : pcCore + 21 + 4 < code.size := by dsimp only [pcCore]; rw [hiReadLen] at hiReadBnd; omega
  obtain ⟨s24, stCore, pc24, hz24, ho24, hptr24, hstk24, hclk24, htin24, hval24, hcmd24, hrem24, hoff24, hd24_3⟩ :=
    sweepSkewInsert_readCore_steps input hWork32 (by rw [hd3]; exact hRecs) hFLe hCoreBnd hplCore hAncLt
      (by rw [pc3]) hz3 ho3 hptr3 hstk3 hclk3 r3
  let jp := F.jumpOf ancNode
  let jjp := F.jumpOf jp
  have hd24 : s24.data = s.data := hd24_3.trans hd3
  have hpc24 : s24.pc = pcStart + iRead.length := by rw [pc24, hiReadLen]; dsimp only [pcCore]; omega
  have hPre24 : Steps code input iRead.length s s24 := by
    rw [hiReadLen]; exact ((st1.append st2).append st3).append stCore
  -- Execute i10Cmp: compare (F.depthOf ancNode - F.depthOf jp) vs (F.depthOf jp - F.depthOf jjp)
  have hpcCmp : s24.pc = pcStart + iRead.length := hpc24
  have hfC0 : code[s24.pc]? = some (.branchLt rZero rRem (pcStart + iRead.length + 1) (pcStart + iRead.length + 3)) :=
    placed_fetch hplC (i := 0) rfl hpcCmp
  have hMkJ : (F.mkAppendedRecord ancNode).jump =
      if 0 < F.depthOf ancNode - F.depthOf jp ∧
          F.depthOf ancNode - F.depthOf jp = F.depthOf jp - F.depthOf jjp then jjp else ancNode := rfl
  by_cases hD1Z : F.depthOf ancNode - F.depthOf jp = 0
  · have hMkZero : (F.mkAppendedRecord ancNode).jump = ancNode := by
      rw [hMkJ, ite_eq_right (by omega)]
    obtain ⟨s25, st25, pc25, k25, d25⟩ := step_branchLt_false (input := input) hfC0
      (by rw [hrem24, hz24, hD1Z]; exact Nat.le_refl 0) (by omega)
    have hfC3 : code[s25.pc]? = some (.mov rCmd rStack) := placed_fetch hplC (i := 3) rfl pc25
    obtain ⟨s26, st26, pc26, r26, k26, d26⟩ := step_mov_at (input := input) hfC3 (by rw [pc25]; omega)
    refine ⟨s26, iRead.length + 2, by omega,
      hPre24.append (.cons st25 (.cons st26 (.zero _))), by rw [pc26, pc25],
      by rw [k26 _ (by decide), k25, hz24], by rw [k26 _ (by decide), k25, ho24],
      by rw [k26 _ (by decide), k25, hptr24], by rw [k26 _ (by decide), k25, hstk24],
      by rw [k26 _ (by decide), k25, hclk24], by rw [k26 _ (by decide), k25, htin24],
      by rw [k26 _ (by decide), k25, hval24], by rw [r26, k25, hstk24, hMkZero],
      d26.trans (d25.trans hd24)⟩
  · have hD1Pos : 0 < F.depthOf ancNode - F.depthOf jp := Nat.pos_of_ne_zero hD1Z
    obtain ⟨s25, st25, pc25, k25, d25⟩ := step_branchLt_true (input := input) hfC0
      (by rw [hz24, hrem24]; exact hD1Pos) (by omega)
    have hfC1 : code[s25.pc]? = some (.branchLt rRem rOff (pcStart + iRead.length + 3) (pcStart + iRead.length + 2)) :=
      placed_fetch hplC (i := 1) rfl pc25
    by_cases hLt : F.depthOf ancNode - F.depthOf jp < F.depthOf jp - F.depthOf jjp
    · have hMkP : (F.mkAppendedRecord ancNode).jump = ancNode := by rw [hMkJ, ite_eq_right (by omega)]
      obtain ⟨s26, st26, pc26, k26, d26⟩ := step_branchLt_true (input := input) hfC1
        (by rw [k25, k25, hrem24, hoff24]; exact hLt) (by omega)
      have hfC3 : code[s26.pc]? = some (.mov rCmd rStack) := placed_fetch hplC (i := 3) rfl pc26
      obtain ⟨s27, st27, pc27, r27, k27, d27⟩ := step_mov_at (input := input) hfC3 (by rw [pc26]; omega)
      refine ⟨s27, iRead.length + 3, by omega,
        hPre24.append (.cons st25 (.cons st26 (.cons st27 (.zero _)))),
        by rw [pc27, pc26],
        by rw [k27 _ (by decide), k26, k25, hz24], by rw [k27 _ (by decide), k26, k25, ho24],
        by rw [k27 _ (by decide), k26, k25, hptr24], by rw [k27 _ (by decide), k26, k25, hstk24],
        by rw [k27 _ (by decide), k26, k25, hclk24], by rw [k27 _ (by decide), k26, k25, htin24],
        by rw [k27 _ (by decide), k26, k25, hval24], by rw [r27, k26, k25, hstk24, hMkP],
        d27.trans (d26.trans (d25.trans hd24))⟩
    · have hGe : F.depthOf jp - F.depthOf jjp ≤ F.depthOf ancNode - F.depthOf jp := by omega
      obtain ⟨s26, st26, pc26, k26, d26⟩ := step_branchLt_false (input := input) hfC1
        (by rw [k25, k25, hrem24, hoff24]; exact hGe) (by omega)
      have hfC2 : code[s26.pc]? = some (.branchLt rOff rRem (pcStart + iRead.length + 3) (pcStart + iRead.length + 4)) :=
        placed_fetch hplC (i := 2) rfl pc26
      by_cases hGt : F.depthOf jp - F.depthOf jjp < F.depthOf ancNode - F.depthOf jp
      · have hMkP : (F.mkAppendedRecord ancNode).jump = ancNode := by rw [hMkJ, ite_eq_right (by omega)]
        obtain ⟨s27, st27, pc27, k27, d27⟩ := step_branchLt_true (input := input) hfC2
          (by rw [k26, k26, k25, k25, hoff24, hrem24]; exact hGt) (by omega)
        have hfC3 : code[s27.pc]? = some (.mov rCmd rStack) := placed_fetch hplC (i := 3) rfl pc27
        obtain ⟨s28, st28, pc28, r28, k28, d28⟩ := step_mov_at (input := input) hfC3 (by rw [pc27]; omega)
        refine ⟨s28, iRead.length + 4, by omega,
          hPre24.append (.cons st25 (.cons st26 (.cons st27 (.cons st28 (.zero _))))),
          by rw [pc28, pc27],
          by rw [k28 _ (by decide), k27, k26, k25, hz24], by rw [k28 _ (by decide), k27, k26, k25, ho24],
          by rw [k28 _ (by decide), k27, k26, k25, hptr24], by rw [k28 _ (by decide), k27, k26, k25, hstk24],
          by rw [k28 _ (by decide), k27, k26, k25, hclk24], by rw [k28 _ (by decide), k27, k26, k25, htin24],
          by rw [k28 _ (by decide), k27, k26, k25, hval24], by rw [r28, k27, k26, k25, hstk24, hMkP],
          d28.trans (d27.trans (d26.trans (d25.trans hd24)))⟩
      · have hEq : F.depthOf ancNode - F.depthOf jp = F.depthOf jp - F.depthOf jjp := by omega
        have hMkJJ : (F.mkAppendedRecord ancNode).jump = jjp := by rw [hMkJ, ite_eq_left ⟨hD1Pos, hEq⟩]
        obtain ⟨s27, st27, pc27, k27, d27⟩ := step_branchLt_false (input := input) hfC2
          (by rw [k26, k26, k25, k25, hoff24, hrem24]; exact Nat.le_of_eq hEq) (by omega)
        have hKeep27 : ∀ r : Fin 15, reg s27 r = reg s24 r := fun r => (k27 r).trans ((k26 r).trans (k25 r))
        have hSt27 : Steps code input (iRead.length + 3) s s27 :=
          hPre24.append (.cons st25 (.cons st26 (.cons st27 (.zero _))))
        have hD27 : s27.data = s.data := d27.trans (d26.trans (d25.trans hd24))
        have hPC27 : s27.pc = pcStart + iRead.length + 4 := pc27
        refine ⟨s27, iRead.length + 3, by omega, hSt27, hPC27,
          (congrArg Fin.val (hKeep27 rZero)).trans hz24,
          (congrArg Fin.val (hKeep27 rOne)).trans ho24,
          (congrArg Fin.val (hKeep27 rPtr)).trans hptr24,
          (congrArg Fin.val (hKeep27 rStack)).trans hstk24,
          (congrArg Fin.val (hKeep27 rClk)).trans hclk24,
          (congrArg Fin.val (hKeep27 rTin)).trans htin24,
          (congrArg Fin.val (hKeep27 rVal)).trans hval24,
          (congrArg Fin.val (hKeep27 rCmd)).trans (hcmd24.trans hMkJJ.symm),
          hD27⟩

theorem sweepSkewInsert_writeJumpsRec_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap)
    {pcW : Nat} {ancNode next dep jVal : Nat}
    (hNextLe : next ≤ n) (hDepLe : dep ≤ n)
    (hBnd : pcW + 9 < code.size)
    (hpl0 : Placed code pcW
      [ Instr.add rRem rTin rClk, Instr.add rRem rRem rClk, Instr.add rRem rRem rClk,
        Instr.storeData rRem rStack,
        Instr.add rRem rRem rOne, Instr.add rVal rVal rOne, Instr.storeData rRem rVal,
        Instr.add rRem rRem rOne, Instr.storeData rRem rCmd ])
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcW) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hStk : (reg s rStack).val = ancNode)
    (hClk : (reg s rClk).val = next) (hTin : (reg s rTin).val = jumpBase n m)
    (hVal : (reg s rVal).val = dep) (hCmd : (reg s rCmd).val = jVal) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input 9 s t ∧ t.pc = pcW + 9 ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ reg t rPtr = reg s rPtr ∧
      (reg t rStack).val = ancNode ∧ (reg t rClk).val = next ∧
      (t.data[jumpBase n m + 3 * next + 0]?).map Fin.val = some ancNode ∧
      (t.data[jumpBase n m + 3 * next + 1]?).map Fin.val = some (dep + 1) ∧
      (t.data[jumpBase n m + 3 * next + 2]?).map Fin.val = some jVal ∧
      ∀ w, w = jumpBase n m + 3 * next + 0 ∨ w = jumpBase n m + 3 * next + 1 ∨
        w = jumpBase n m + 3 * next + 2 ∨ t.data[w]? = s.data[w]? := by
  have hJBnd : jumpBase n m + 3 * next + 2 < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at hWork32 ⊢; omega
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ := step_add15_at (input := input) (placed_fetch hpl0 (i := 0) rfl hpc) (by rw [hpc]; omega)
  have hrem1 : (reg s1 rRem).val = jumpBase n m + next := by
    rw [r1, WordOps.add_val, hTin, hClk]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ := step_add15_at (input := input) (placed_fetch hpl0 (i := 1) rfl (by rw [pc1, hpc])) (by rw [pc1, hpc]; omega)
  have hrem2 : (reg s2 rRem).val = jumpBase n m + 2 * next := by
    rw [r2, WordOps.add_val, hrem1, k1 _ (by decide), hClk,
      show jumpBase n m + next + next = jumpBase n m + 2 * next by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 2 * next < workCap) hw)
  obtain ⟨s3, st3, pc3, r3, k3, d3⟩ := step_add15_at (input := input) (placed_fetch hpl0 (i := 2) rfl (by rw [pc2, pc1, hpc])) (by rw [pc2, pc1, hpc]; omega)
  have hrem3 : (reg s3 rRem).val = jumpBase n m + 3 * next := by
    rw [r3, WordOps.add_val, hrem2, k2 _ (by decide), k1 _ (by decide), hClk,
      show jumpBase n m + 2 * next + next = jumpBase n m + 3 * next by omega]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * next < workCap) hw)
  have hj0Fit : (reg s3 rRem).val < workCap := by rw [hrem3]; omega
  obtain ⟨s4, st4, pc4, d4, k4⟩ := step_storeData_at (input := input) (placed_fetch hpl0 (i := 3) rfl (by rw [pc3, pc2, pc1, hpc]))
    (by rw [pc3, pc2, pc1, hpc]; omega) hj0Fit
  have hD4_0 : (s4.data[jumpBase n m + 3 * next + 0]?).map Fin.val = some ancNode := by
    rw [d4, show jumpBase n m + 3 * next + 0 = (reg s3 rRem).val from hrem3.symm,
      Array.getElem?_set_self, Option.map_some, k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hStk]
  have ho4 : (reg s4 rOne).val = 1 := by rw [k4, k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), ho]
  have hrem4 : (reg s4 rRem).val = jumpBase n m + 3 * next := by rw [k4, hrem3]
  have hval4 : (reg s4 rVal).val = dep := by rw [k4, k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hVal]
  obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_add15_at (input := input) (placed_fetch hpl0 (i := 4) rfl (by rw [pc4, pc3, pc2, pc1, hpc])) (by rw [pc4, pc3, pc2, pc1, hpc]; omega)
  have hrem5 : (reg s5 rRem).val = jumpBase n m + 3 * next + 1 := by
    rw [r5, WordOps.add_val, hrem4, ho4]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * next + 1 < workCap) hw)
  have ho5 : (reg s5 rOne).val = 1 := by rw [k5 _ (by decide), ho4]
  have hval5 : (reg s5 rVal).val = dep := by rw [k5 _ (by decide), hval4]
  obtain ⟨s6, st6, pc6, r6, k6, d6⟩ := step_add15_at (input := input) (placed_fetch hpl0 (i := 5) rfl (by rw [pc5, pc4, pc3, pc2, pc1, hpc])) (by rw [pc5, pc4, pc3, pc2, pc1, hpc]; omega)
  have hval6 : (reg s6 rVal).val = dep + 1 := by
    rw [r6, WordOps.add_val, hval5, ho5]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : dep + 1 < workCap) hw)
  have hrem6 : (reg s6 rRem).val = jumpBase n m + 3 * next + 1 := by rw [k6 _ (by decide), hrem5]
  have hj1Fit : (reg s6 rRem).val < workCap := by rw [hrem6]; omega
  obtain ⟨s7, st7, pc7, d7, k7⟩ := step_storeData_at (input := input) (placed_fetch hpl0 (i := 6) rfl (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hpc]))
    (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hpc]; omega) hj1Fit
  have hD7_1 : (s7.data[jumpBase n m + 3 * next + 1]?).map Fin.val = some (dep + 1) := by
    rw [d7, show jumpBase n m + 3 * next + 1 = (reg s6 rRem).val from hrem6.symm, Array.getElem?_set_self]
    exact congrArg some hval6
  have ho7 : (reg s7 rOne).val = 1 := by rw [k7, k6 _ (by decide), ho5]
  have hrem7 : (reg s7 rRem).val = jumpBase n m + 3 * next + 1 := by rw [k7, hrem6]
  obtain ⟨s8, st8, pc8, r8, k8, d8⟩ := step_add15_at (input := input) (placed_fetch hpl0 (i := 7) rfl (by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, hpc])) (by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, hpc]; omega)
  have hrem8 : (reg s8 rRem).val = jumpBase n m + 3 * next + 2 := by
    rw [r8, WordOps.add_val, hrem7, ho7]
    exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : jumpBase n m + 3 * next + 2 < workCap) hw)
  have hj2Fit : (reg s8 rRem).val < workCap := by rw [hrem8]; omega
  obtain ⟨s9, st9, pc9, d9, k9⟩ := step_storeData_at (input := input) (placed_fetch hpl0 (i := 8) rfl (by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hpc]))
    (by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hpc]; omega) hj2Fit
  have hKeep9 : ∀ r : Fin 15, r = rZero ∨ r = rOne ∨ r = rPtr ∨ r = rStack ∨ r = rClk ∨ r = rCmd → reg s9 r = reg s r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [k9, k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4, k3 _ (by decide), k2 _ (by decide), k1 _ (by decide)]
  refine ⟨s9,
    .cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7 (.cons st8 (.cons st9 (.zero _))))))))),
    by rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hpc],
    by rw [hKeep9 _ (Or.inl rfl), hz], by rw [hKeep9 _ (Or.inr (Or.inl rfl)), ho],
    hKeep9 _ (Or.inr (Or.inr (Or.inl rfl))), by rw [hKeep9 _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), hStk],
    by rw [hKeep9 _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), hClk],
    by rw [storeData_getElem?_ne _ d9 (by rw [hrem8]; omega), d8,
      storeData_getElem?_ne _ d7 (by rw [hrem6]; omega), d6, d5, hD4_0],
    by rw [storeData_getElem?_ne _ d9 (by rw [hrem8]; omega), d8, hD7_1],
    by rw [d9, show jumpBase n m + 3 * next + 2 = (reg s8 rRem).val from hrem8.symm,
      Array.getElem?_set_self, Option.map_some, k8 _ (by decide), k7, k6 _ (by decide),
      k5 _ (by decide), k4, k3 _ (by decide), k2 _ (by decide), k1 _ (by decide), hCmd],
    fun w => ?_⟩
  by_cases h0 : w = jumpBase n m + 3 * next + 0
  · exact Or.inl h0
  by_cases h1 : w = jumpBase n m + 3 * next + 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : w = jumpBase n m + 3 * next + 2
  · exact Or.inr (Or.inr (Or.inl h2))
  exact Or.inr (Or.inr (Or.inr (by
    rw [storeData_getElem?_ne _ d9 (by rw [hrem8]; omega), d8,
      storeData_getElem?_ne _ d7 (by rw [hrem6]; omega), d6, d5,
      storeData_getElem?_ne _ d4 (by rw [hrem3]; omega), d3, d2, d1])))

theorem sweepSkewInsert_writeJumps_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (hLarge : 3 ≤ n)
    {pcW : Nat} {ancNode next dep jVal dictSlotsB slotIdx : Nat}
    (hNextLe : next ≤ n) (hDepLe : dep ≤ n) (hDSB : dictSlotsB + slotIdx < jumpBase n m)
    (hBnd : pcW + 9 + (loadScratch h8 rTmp slDictSlots).length + 2 < code.size)
    (hpl0 : Placed code pcW
      [ Instr.add rRem rTin rClk, Instr.add rRem rRem rClk, Instr.add rRem rRem rClk,
        Instr.storeData rRem rStack,
        Instr.add rRem rRem rOne, Instr.add rVal rVal rOne, Instr.storeData rRem rVal,
        Instr.add rRem rRem rOne, Instr.storeData rRem rCmd ])
    (hpl1 : Placed code (pcW + 9) (loadScratch h8 rTmp slDictSlots))
    (hpl2 : Placed code (pcW + 9 + (loadScratch h8 rTmp slDictSlots).length)
      [ Instr.add rTmp rTmp rPtr, Instr.storeData rTmp rClk ])
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcW) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hPtr : (reg s rPtr).val = slotIdx) (hStk : (reg s rStack).val = ancNode)
    (hClk : (reg s rClk).val = next) (hTin : (reg s rTin).val = jumpBase n m)
    (hVal : (reg s rVal).val = dep) (hCmd : (reg s rCmd).val = jVal)
    (hSlSlots : (s.data[slDictSlots]?).map Fin.val = some dictSlotsB) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (9 + (loadScratch h8 rTmp slDictSlots).length + 2) s t ∧
      t.pc = pcW + 9 + (loadScratch h8 rTmp slDictSlots).length + 2 ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rStack).val = ancNode ∧
      (reg t rClk).val = next ∧
      (t.data[jumpBase n m + 3 * next + 0]?).map Fin.val = some ancNode ∧
      (t.data[jumpBase n m + 3 * next + 1]?).map Fin.val = some (dep + 1) ∧
      (t.data[jumpBase n m + 3 * next + 2]?).map Fin.val = some jVal ∧
      (t.data[dictSlotsB + slotIdx]?).map Fin.val = some next ∧
      ∀ w, w = jumpBase n m + 3 * next + 0 ∨ w = jumpBase n m + 3 * next + 1 ∨
        w = jumpBase n m + 3 * next + 2 ∨ w = dictSlotsB + slotIdx ∨
        t.data[w]? = s.data[w]? := by
  have h29 := scratch_lt_orderBase (n := n) (m := m) (sl := 29) hLarge (by decide)
  have hOrdLtJ : orderBase n m < jumpBase n m := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
  have hDSl : slDictSlots < orderBase n m := by unfold slDictSlots; omega
  have hSlDSlW : slDictSlots < workCap := by unfold slDictSlots; omega
  have hDSBW : dictSlotsB + slotIdx < workCap := by
    have hJLe : jumpBase n m < workCap := by
      simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
        csrArenaWords] at hWork32 ⊢; omega
    omega
  obtain ⟨s9, st0_9, pc9, hz9, ho9, hptr9_eq, hstk9, hclk9, hJ0_9, hJ1_9, hJ2_9, hPres9⟩ :=
    sweepSkewInsert_writeJumpsRec_steps input hWork32 hNextLe hDepLe (by omega) hpl0 s hpc hz ho hStk hClk hTin hVal hCmd
  have hSl9 : (s9.data[slDictSlots]?).map Fin.val = some dictSlotsB := by
    rcases hPres9 slDictSlots with h | h | h | h
    · omega
    · omega
    · omega
    · rw [h]; exact hSlSlots
  obtain ⟨s10, st10, pc10, r10, d10, k10⟩ := loadScratch_val_steps h8 (input := input) rTmp slDictSlots
    hSlDSlW (by decide) pc9 hpl1 (by omega) ho9 hSl9
  have hptr10 : (reg s10 rPtr).val = slotIdx := by rw [k10 _ (by decide) (by decide), hptr9_eq, hPtr]
  have hclk10 : (reg s10 rClk).val = next := by rw [k10 _ (by decide) (by decide), hclk9]
  obtain ⟨s11, st11, pc11, r11, k11, d11⟩ := step_add15_at (input := input)
    (placed_fetch hpl2 (i := 0) rfl pc10) (by rw [pc10]; omega)
  have htmp11 : (reg s11 rTmp).val = dictSlotsB + slotIdx := by
    rw [r11, WordOps.add_val, r10, hptr10]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hDSBW hw)
  have hclk11 : (reg s11 rClk).val = next := by rw [k11 _ (by decide), hclk10]
  have hd11Fit : (reg s11 rTmp).val < workCap := by rw [htmp11]; exact hDSBW
  obtain ⟨s12, st12, pc12, d12, k12⟩ := step_storeData_at (input := input)
    (placed_fetch hpl2 (i := 1) rfl (by rw [pc11, pc10])) (by rw [pc11, pc10]; omega) hd11Fit
  refine ⟨s12, (st0_9.append st10).append (.cons st11 (.cons st12 (.zero _))), by rw [pc12, pc11, pc10],
    by rw [k12, k11 _ (by decide), k10 _ (by decide) (by decide), hz9],
    by rw [k12, k11 _ (by decide), k10 _ (by decide) (by decide), ho9],
    by rw [k12, k11 _ (by decide), k10 _ (by decide) (by decide), hstk9],
    by rw [k12, hclk11],
    by rw [storeData_getElem?_ne _ d12 (by rw [htmp11]; omega), d11, d10, hJ0_9],
    by rw [storeData_getElem?_ne _ d12 (by rw [htmp11]; omega), d11, d10, hJ1_9],
    by rw [storeData_getElem?_ne _ d12 (by rw [htmp11]; omega), d11, d10, hJ2_9],
    by rw [d12, show dictSlotsB + slotIdx = (reg s11 rTmp).val from htmp11.symm,
      Array.getElem?_set_self, Option.map_some, hclk11],
    fun w => ?_⟩
  by_cases hSlotEq : w = dictSlotsB + slotIdx
  · exact Or.inr (Or.inr (Or.inr (Or.inl hSlotEq)))
  · rw [storeData_getElem?_ne _ d12 (by rw [htmp11]; exact Ne.symm hSlotEq), d11, d10]
    rcases hPres9 w with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem sweepSkewInsert_writeBF_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (_hLarge : 3 ≤ n)
    {pc next ancNode qFst : Nat}
    (hNextLe : next ≤ n) (hQF : qFst < n)
    (hBnd : pc + ((loadScratch h8 rVal slKeyFst).length + 1 + (loadScratch h8 rTmp slBackFst).length + 2) < code.size)
    (hpl : Placed code pc
      (((loadScratch h8 rVal slKeyFst ++ [Instr.add rVal rVal rOne]) ++
        loadScratch h8 rTmp slBackFst) ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal]))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pc) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hStk : (reg s rStack).val = ancNode) (hClk : (reg s rClk).val = next)
    (hSlKF : (s.data[slKeyFst]?).map Fin.val = some qFst)
    (hSlBF : (s.data[slBackFst]?).map Fin.val = some (backFstBase n m)) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input ((loadScratch h8 rVal slKeyFst).length + 1 + (loadScratch h8 rTmp slBackFst).length + 2) s t ∧
      t.pc = pc + ((loadScratch h8 rVal slKeyFst).length + 1 + (loadScratch h8 rTmp slBackFst).length + 2) ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rStack).val = ancNode ∧ (reg t rClk).val = next ∧
      (t.data[backFstBase n m + next]?).map Fin.val = some (qFst + 1) ∧
      ∀ w, w = backFstBase n m + next ∨ t.data[w]? = s.data[w]? := by
  have h2 := placed_append_left hpl
  have h1 := placed_append_left h2
  have hpl0 : Placed code pc (loadScratch h8 rVal slKeyFst) := placed_append_left h1
  have hpl1 : Placed code (pc + (loadScratch h8 rVal slKeyFst).length) [Instr.add rVal rVal rOne] := placed_right_eq h1 rfl
  have hpl2 : Placed code (pc + (loadScratch h8 rVal slKeyFst).length + 1) (loadScratch h8 rTmp slBackFst) :=
    placed_right_eq h2 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl3 : Placed code (pc + (loadScratch h8 rVal slKeyFst).length + 1 + (loadScratch h8 rTmp slBackFst).length)
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] :=
    placed_right_eq hpl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hSlKFW : slKeyFst < workCap := by unfold slKeyFst; omega
  have hSlBFW : slBackFst < workCap := by unfold slBackFst; omega
  have hBFFitW : backFstBase n m + next < workCap := by
    simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at hWork32 ⊢; omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rVal slKeyFst hSlKFW (by decide)
    hpc hpl0 (by omega) ho hSlKF
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have hstk1 : (reg s1 rStack).val = ancNode := by rw [k1 _ (by decide) (by decide), hStk]
  have hclk1 : (reg s1 rClk).val = next := by rw [k1 _ (by decide) (by decide), hClk]
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ := step_add15_at (input := input) (placed_fetch hpl1 (i := 0) rfl pc1) (by rw [pc1]; omega)
  have hval2 : (reg s2 rVal).val = qFst + 1 := by
    rw [r2, WordOps.add_val, r1, ho1]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide), hz1]
  have hstk2 : (reg s2 rStack).val = ancNode := by rw [k2 _ (by decide), hstk1]
  have hclk2 : (reg s2 rClk).val = next := by rw [k2 _ (by decide), hclk1]
  have hd2 : s2.data = s.data := d2.trans d1
  obtain ⟨s3, st3, pc3, r3, d3, k3⟩ := loadScratch_val_steps h8 (input := input) rTmp slBackFst hSlBFW (by decide)
    (by rw [pc2, pc1]) hpl2 (by omega) ho2 (by rw [hd2]; exact hSlBF)
  have hclk3 : (reg s3 rClk).val = next := by rw [k3 _ (by decide) (by decide), hclk2]
  have hval3 : (reg s3 rVal).val = qFst + 1 := by rw [k3 _ (by decide) (by decide), hval2]
  have hstk3 : (reg s3 rStack).val = ancNode := by rw [k3 _ (by decide) (by decide), hstk2]
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide) (by decide), ho2]
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide) (by decide), hz2]
  obtain ⟨s4a, st4a, pc4a, r4a, k4a, d4a⟩ := step_add15_at (input := input)
    (placed_fetch hpl3 (i := 0) rfl pc3) (by rw [pc3]; omega)
  have htmp4a : (reg s4a rTmp).val = backFstBase n m + next := by
    rw [r4a, WordOps.add_val, r3, hclk3]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hBFFitW hw)
  have hd4aFit : (reg s4a rTmp).val < workCap := by rw [htmp4a]; exact hBFFitW
  obtain ⟨s4, st4b, pc4, d4b, k4⟩ := step_storeData_at (input := input)
    (placed_fetch hpl3 (i := 1) rfl (by rw [pc4a, pc3])) (by rw [pc4a, pc3]; omega) hd4aFit
  refine ⟨s4, (((st1.append (.cons st2 (.zero _))).append st3).append (.cons st4a (.cons st4b (.zero _)))),
    by rw [pc4, pc4a, pc3]; omega,
    by rw [k4, k4a _ (by decide), hz3], by rw [k4, k4a _ (by decide), ho3],
    by rw [k4, k4a _ (by decide), hstk3], by rw [k4, k4a _ (by decide), hclk3], ?_, fun w => ?_⟩
  · rw [d4b, show backFstBase n m + next = (reg s4a rTmp).val from htmp4a.symm,
      Array.getElem?_set_self, Option.map_some, k4a _ (by decide), hval3]
  · by_cases hF : w = backFstBase n m + next
    · exact Or.inl hF
    · exact Or.inr (by rw [storeData_getElem?_ne _ d4b (by rw [htmp4a]; exact Ne.symm hF), d4a, d3, hd2])

theorem sweepSkewInsert_writeBS_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (_hLarge : 3 ≤ n)
    {pc next ancNode qSnd : Nat}
    (hNextLe : next ≤ n)
    (hBnd : pc + ((loadScratch h8 rVal slKeySnd).length + (loadScratch h8 rTmp slBackSnd).length + 2) < code.size)
    (hpl : Placed code pc
      ((loadScratch h8 rVal slKeySnd ++ loadScratch h8 rTmp slBackSnd) ++
        [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal]))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pc) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hStk : (reg s rStack).val = ancNode) (hClk : (reg s rClk).val = next)
    (hSlKS : (s.data[slKeySnd]?).map Fin.val = some qSnd)
    (hSlBS : (s.data[slBackSnd]?).map Fin.val = some (backSndBase n m)) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input ((loadScratch h8 rVal slKeySnd).length + (loadScratch h8 rTmp slBackSnd).length + 2) s t ∧
      t.pc = pc + ((loadScratch h8 rVal slKeySnd).length + (loadScratch h8 rTmp slBackSnd).length + 2) ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rStack).val = ancNode ∧ (reg t rClk).val = next ∧
      (t.data[backSndBase n m + next]?).map Fin.val = some qSnd ∧
      ∀ w, w = backSndBase n m + next ∨ t.data[w]? = s.data[w]? := by
  have h1 := placed_append_left hpl
  have hpl0 : Placed code pc (loadScratch h8 rVal slKeySnd) := placed_append_left h1
  have hpl1 : Placed code (pc + (loadScratch h8 rVal slKeySnd).length) (loadScratch h8 rTmp slBackSnd) :=
    placed_right_eq h1 rfl
  have hpl2 : Placed code (pc + (loadScratch h8 rVal slKeySnd).length + (loadScratch h8 rTmp slBackSnd).length)
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] :=
    placed_right_eq hpl (by simp only [List.length_append]; omega)
  have hSlKSW : slKeySnd < workCap := by unfold slKeySnd; omega
  have hSlBSW : slBackSnd < workCap := by unfold slBackSnd; omega
  have hBSFitW : backSndBase n m + next < workCap := by
    simp only [backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at hWork32 ⊢; omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rVal slKeySnd hSlKSW (by decide)
    hpc hpl0 (by omega) ho hSlKS
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have hclk1 : (reg s1 rClk).val = next := by rw [k1 _ (by decide) (by decide), hClk]
  have hstk1 : (reg s1 rStack).val = ancNode := by rw [k1 _ (by decide) (by decide), hStk]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ := loadScratch_val_steps h8 (input := input) rTmp slBackSnd hSlBSW (by decide)
    pc1 hpl1 (by omega) ho1 (by rw [d1]; exact hSlBS)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hz1]
  have hclk2 : (reg s2 rClk).val = next := by rw [k2 _ (by decide) (by decide), hclk1]
  have hstk2 : (reg s2 rStack).val = ancNode := by rw [k2 _ (by decide) (by decide), hstk1]
  have hval2 : (reg s2 rVal).val = qSnd := by rw [k2 _ (by decide) (by decide), r1]
  obtain ⟨s3a, st3a, pc3a, r3a, k3a, d3a⟩ := step_add15_at (input := input)
    (placed_fetch hpl2 (i := 0) rfl pc2) (by rw [pc2]; omega)
  have htmp3a : (reg s3a rTmp).val = backSndBase n m + next := by
    rw [r3a, WordOps.add_val, r2, hclk2]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hBSFitW hw)
  have hd3aFit : (reg s3a rTmp).val < workCap := by rw [htmp3a]; exact hBSFitW
  obtain ⟨s3, st3b, pc3, d3b, k3⟩ := step_storeData_at (input := input)
    (placed_fetch hpl2 (i := 1) rfl (by rw [pc3a, pc2])) (by rw [pc3a, pc2]; omega) hd3aFit
  refine ⟨s3, ((st1.append st2).append (.cons st3a (.cons st3b (.zero _)))), by rw [pc3, pc3a, pc2]; omega,
    by rw [k3, k3a _ (by decide), hz2], by rw [k3, k3a _ (by decide), ho2],
    by rw [k3, k3a _ (by decide), hstk2], by rw [k3, k3a _ (by decide), hclk2], ?_, fun w => ?_⟩
  · rw [d3b, show backSndBase n m + next = (reg s3a rTmp).val from htmp3a.symm,
      Array.getElem?_set_self, Option.map_some, k3a _ (by decide), hval2]
  · by_cases hS : w = backSndBase n m + next
    · exact Or.inl hS
    · exact Or.inr (by rw [storeData_getElem?_ne _ d3b (by rw [htmp3a]; exact Ne.symm hS), d3a, d2, d1])

theorem sweepSkewInsert_writeParNext_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (hLarge : 3 ≤ n)
    {pc pcWriteLabel next ancNode : Nat}
    (hNextLe : next ≤ n) (hWL : pcWriteLabel < code.size)
    (hBnd : pc + ((loadScratch h8 rTmp slParents).length + 2 + 1 + (sweepInitStoreScratch h8 slNext rVal).length + 2) < code.size)
    (hpl : Placed code pc
      ((((loadScratch h8 rTmp slParents ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rStack]) ++
        [Instr.add rVal rClk rOne]) ++ sweepInitStoreScratch h8 slNext rVal) ++
        [Instr.mov rVal rClk, Instr.goto pcWriteLabel]))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pc) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hStk : (reg s rStack).val = ancNode) (hClk : (reg s rClk).val = next)
    (hSlPar : (s.data[slParents]?).map Fin.val = some (parentsBase n m)) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input ((loadScratch h8 rTmp slParents).length + 2 + 1 + (sweepInitStoreScratch h8 slNext rVal).length + 2) s t ∧
      t.pc = pcWriteLabel ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rVal).val = next ∧
      (t.data[parentsBase n m + next]?).map Fin.val = some ancNode ∧
      (t.data[slNext]?).map Fin.val = some (next + 1) ∧
      ∀ w, w = slNext ∨ w = parentsBase n m + next ∨ t.data[w]? = s.data[w]? := by
  have h3 := placed_append_left hpl
  have h2 := placed_append_left h3
  have h1 := placed_append_left h2
  have hpl0 : Placed code pc (loadScratch h8 rTmp slParents) := placed_append_left h1
  have hpl1 : Placed code (pc + (loadScratch h8 rTmp slParents).length)
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rStack] := placed_right_eq h1 rfl
  have hpl2 : Placed code (pc + (loadScratch h8 rTmp slParents).length + 2) [Instr.add rVal rClk rOne] :=
    placed_right_eq h2 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl3 : Placed code (pc + (loadScratch h8 rTmp slParents).length + 2 + 1)
      (sweepInitStoreScratch h8 slNext rVal) :=
    placed_right_eq h3 (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl4 : Placed code (pc + (loadScratch h8 rTmp slParents).length + 2 + 1 +
      (sweepInitStoreScratch h8 slNext rVal).length) [Instr.mov rVal rClk, Instr.goto pcWriteLabel] :=
    placed_right_eq hpl (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hSlParW : slParents < workCap := by unfold slParents; omega
  have hSlNW : slNext < workCap := by unfold slNext; omega
  have hParFit : parentsBase n m + next < workCap := by
    simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase,
      candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase,
      rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at hWork32 ⊢; omega
  have hNext1W : next + 1 < workCap := by omega
  have hSLtPar : slNext < parentsBase n m + next := by
    have := scratch_lt_orderBase (n := n) (m := m) (sl := 29) hLarge (by decide)
    simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase,
      candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase,
      rowStartBase, ranksBase, orderBase] at *; unfold slNext; omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rTmp slParents hSlParW (by decide)
    hpc hpl0 (by omega) ho hSlPar
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have hclk1 : (reg s1 rClk).val = next := by rw [k1 _ (by decide) (by decide), hClk]
  have hstk1 : (reg s1 rStack).val = ancNode := by rw [k1 _ (by decide) (by decide), hStk]
  obtain ⟨s2a, st2a, pc2a, r2a, k2a, d2a⟩ := step_add15_at (input := input)
    (placed_fetch hpl1 (i := 0) rfl pc1) (by rw [pc1]; omega)
  have htmp2a : (reg s2a rTmp).val = parentsBase n m + next := by
    rw [r2a, WordOps.add_val, r1, hclk1]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hParFit hw)
  have hd2aFit : (reg s2a rTmp).val < workCap := by rw [htmp2a]; exact hParFit
  obtain ⟨s2, st2b, pc2, d2b, k2⟩ := step_storeData_at (input := input)
    (placed_fetch hpl1 (i := 1) rfl (by rw [pc2a, pc1])) (by rw [pc2a, pc1]; omega) hd2aFit
  have hMemPar2 : (s2.data[parentsBase n m + next]?).map Fin.val = some ancNode := by
    rw [d2b, show parentsBase n m + next = (reg s2a rTmp).val from htmp2a.symm,
      Array.getElem?_set_self, Option.map_some, k2a _ (by decide), hstk1]
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2, k2a _ (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2, k2a _ (by decide), hz1]
  have hclk2 : (reg s2 rClk).val = next := by rw [k2, k2a _ (by decide), hclk1]
  obtain ⟨s3, st3, pc3, r3, k3, d3⟩ := step_add15_at (input := input)
    (placed_fetch hpl2 (i := 0) rfl (by rw [pc2, pc2a, pc1])) (by rw [pc2, pc2a, pc1]; omega)
  have hval3 : (reg s3 rVal).val = next + 1 := by
    rw [r3, WordOps.add_val, hclk2, ho2]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hNext1W hw)
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide), ho2]
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide), hz2]
  have hclk3 : (reg s3 rClk).val = next := by rw [k3 _ (by decide), hclk2]
  obtain ⟨s4, st4, pc4, hNext4, hFr4, k4⟩ := storeScratch_val_steps h8 (input := input) slNext rVal
    (by decide) (by decide) hSlNW (by rw [pc3, pc2, pc2a, pc1]) hpl3 (by omega) ho3
  have ho4 : (reg s4 rOne).val = 1 := by rw [k4 _ (by decide), ho3]
  have hz4 : (reg s4 rZero).val = 0 := by rw [k4 _ (by decide), hz3]
  have hclk4 : (reg s4 rClk).val = next := by rw [k4 _ (by decide), hclk3]
  obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_mov_at (input := input)
    (placed_fetch hpl4 (i := 0) rfl pc4) (by rw [pc4]; omega)
  have hf5 : code[s5.pc]? = some (.goto pcWriteLabel) :=
    placed_fetch hpl4 (i := 1) rfl (by rw [pc5, pc4])
  have st6 : step code input s5 = some (.next { s5 with pc := pcWriteLabel }) := step_goto_at hf5 hWL
  refine ⟨{ s5 with pc := pcWriteLabel },
    (((st1.append (.cons st2a (.cons st2b (.zero _)))).append (.cons st3 (.zero _))).append st4).append
      (.cons st5 (.cons st6 (.zero _))),
    rfl,
    by change (reg s5 rZero).val = 0; rw [k5 _ (by decide), hz4],
    by change (reg s5 rOne).val = 1; rw [k5 _ (by decide), ho4],
    by change (reg s5 rVal).val = next; rw [r5, hclk4],
    by change (s5.data[parentsBase n m + next]?).map Fin.val = some ancNode; rw [d5, hFr4 (parentsBase n m + next) (by omega), d3, hMemPar2],
    by change (s5.data[slNext]?).map Fin.val = some (next + 1); rw [d5, hNext4, hval3],
    fun w => ?_⟩
  change w = slNext ∨ w = parentsBase n m + next ∨ s5.data[w]? = s.data[w]?
  by_cases hN : w = slNext
  · exact Or.inl hN
  by_cases hP : w = parentsBase n m + next
  · exact Or.inr (Or.inl hP)
  exact Or.inr (Or.inr (by rw [d5, hFr4 w hN, d3, storeData_getElem?_ne _ d2b (by rw [htmp2a]; exact Ne.symm hP), d2a, d1]))

theorem sweepSkewInsert_writeBackPar_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (hLarge : 3 ≤ n)
    {pcBP pcWriteLabel next ancNode qFst qSnd : Nat}
    (hNextLe : next ≤ n) (hQF : qFst < n) (_hQS : qSnd < n) (hWL : pcWriteLabel < code.size)
    (hBnd : pcBP + (loadScratch h8 rVal slKeyFst ++ [Instr.add rVal rVal rOne] ++
        loadScratch h8 rTmp slBackFst ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rVal slKeySnd ++
        loadScratch h8 rTmp slBackSnd ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rTmp slParents ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rStack] ++
        [Instr.add rVal rClk rOne] ++ sweepInitStoreScratch h8 slNext rVal ++
        [Instr.mov rVal rClk, Instr.goto pcWriteLabel]).length < code.size)
    (hpl : Placed code pcBP
      (loadScratch h8 rVal slKeyFst ++ [Instr.add rVal rVal rOne] ++
        loadScratch h8 rTmp slBackFst ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rVal slKeySnd ++
        loadScratch h8 rTmp slBackSnd ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rTmp slParents ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rStack] ++
        [Instr.add rVal rClk rOne] ++ sweepInitStoreScratch h8 slNext rVal ++
        [Instr.mov rVal rClk, Instr.goto pcWriteLabel]))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcBP) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hStk : (reg s rStack).val = ancNode) (hClk : (reg s rClk).val = next)
    (hSlKF : (s.data[slKeyFst]?).map Fin.val = some qFst)
    (hSlKS : (s.data[slKeySnd]?).map Fin.val = some qSnd)
    (hSlBF : (s.data[slBackFst]?).map Fin.val = some (backFstBase n m))
    (hSlBS : (s.data[slBackSnd]?).map Fin.val = some (backSndBase n m))
    (hSlPar : (s.data[slParents]?).map Fin.val = some (parentsBase n m)) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 92 ∧ Steps code input k s t ∧ t.pc = pcWriteLabel ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rVal).val = next ∧
      (t.data[backFstBase n m + next]?).map Fin.val = some (qFst + 1) ∧
      (t.data[backSndBase n m + next]?).map Fin.val = some qSnd ∧
      (t.data[parentsBase n m + next]?).map Fin.val = some ancNode ∧
      (t.data[slNext]?).map Fin.val = some (next + 1) ∧
      ∀ w, w = slNext ∨ w = backFstBase n m + next ∨ w = backSndBase n m + next ∨
        w = parentsBase n m + next ∨ t.data[w]? = s.data[w]? := by
  let b1 := ((loadScratch h8 rVal slKeyFst ++ [Instr.add rVal rVal rOne]) ++
    loadScratch h8 rTmp slBackFst) ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal]
  let b2 := (loadScratch h8 rVal slKeySnd ++ loadScratch h8 rTmp slBackSnd) ++
    [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal]
  let b3 := (((loadScratch h8 rTmp slParents ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rStack]) ++
    [Instr.add rVal rClk rOne]) ++ sweepInitStoreScratch h8 slNext rVal) ++
    [Instr.mov rVal rClk, Instr.goto pcWriteLabel]
  have hpl' : Placed code pcBP ((b1 ++ b2) ++ b3) := by
    have h0 := hpl
    repeat rw [List.append_assoc b1] at h0
    repeat rw [List.append_assoc b2] at h0
    have hEq : (loadScratch h8 rVal slKeyFst ++ [Instr.add rVal rVal rOne] ++
        loadScratch h8 rTmp slBackFst ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rVal slKeySnd ++
        loadScratch h8 rTmp slBackSnd ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rTmp slParents ++ [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rStack] ++
        [Instr.add rVal rClk rOne] ++ sweepInitStoreScratch h8 slNext rVal ++
        [Instr.mov rVal rClk, Instr.goto pcWriteLabel]) = ((b1 ++ b2) ++ b3) := by
      dsimp only [b1, b2, b3]; simp only [List.append_assoc]
    rw [hEq] at hpl; exact hpl
  have hb1 : b1.length = (loadScratch h8 rVal slKeyFst).length + 1 + (loadScratch h8 rTmp slBackFst).length + 2 := by
    dsimp only [b1]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hb2 : b2.length = (loadScratch h8 rVal slKeySnd).length + (loadScratch h8 rTmp slBackSnd).length + 2 := by
    dsimp only [b2]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hb3 : b3.length = (loadScratch h8 rTmp slParents).length + 2 + 1 + (sweepInitStoreScratch h8 slNext rVal).length + 2 := by
    dsimp only [b3]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hBndT : pcBP + (b1.length + b2.length + b3.length) < code.size := by
    have hsz : ((b1 ++ b2) ++ b3).length = b1.length + b2.length + b3.length := by
      simp only [List.length_append]
    rw [← hsz]; dsimp only [b1, b2, b3] at *; simp only [List.append_assoc] at *; exact hBnd
  have h12 := placed_append_left hpl'
  have hpl1 : Placed code pcBP b1 := placed_append_left h12
  have hpl2 : Placed code (pcBP + b1.length) b2 := placed_right_eq h12 rfl
  have hpl3 : Placed code (pcBP + b1.length + b2.length) b3 :=
    placed_right_eq hpl' (by simp only [List.length_append]; omega)
  have h29 := scratch_lt_orderBase (n := n) (m := m) (sl := 29) hLarge (by decide)
  have hOrdLeBF : orderBase n m ≤ backFstBase n m := by
    simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase]; omega
  have hBFLtBS : backFstBase n m + next < backSndBase n m + next := by simp only [backSndBase, backFstBase]; omega
  have hBSLtPar : backSndBase n m + next < parentsBase n m + next := by simp only [parentsBase, labelsBase]; omega
  obtain ⟨s1, st1, pc1, hz1, ho1, hstk1, hclk1, hMemBF1, hPres1⟩ :=
    sweepSkewInsert_writeBF_steps h8 input hWork32 hLarge hNextLe hQF (by rw [← hb1]; omega) hpl1
      s hpc hz ho hStk hClk hSlKF hSlBF
  have hSlKS1 : (s1.data[slKeySnd]?).map Fin.val = some qSnd := by
    have hlt : slKeySnd < backFstBase n m + next := by unfold slKeySnd; omega
    rcases hPres1 slKeySnd with h | h
    · omega
    · rw [h]; exact hSlKS
  have hSlBS1 : (s1.data[slBackSnd]?).map Fin.val = some (backSndBase n m) := by
    have hlt : slBackSnd < backFstBase n m + next := by unfold slBackSnd; omega
    rcases hPres1 slBackSnd with h | h
    · omega
    · rw [h]; exact hSlBS
  have hSlPar1 : (s1.data[slParents]?).map Fin.val = some (parentsBase n m) := by
    have hlt : slParents < backFstBase n m + next := by unfold slParents; omega
    rcases hPres1 slParents with h | h
    · omega
    · rw [h]; exact hSlPar
  have hBnd2 : pcBP + b1.length + ((loadScratch h8 rVal slKeySnd).length +
      (loadScratch h8 rTmp slBackSnd).length + 2) < code.size := by
    rw [← hb2]; omega
  obtain ⟨s2, st2, pc2, hz2, ho2, hstk2, hclk2, hMemBS2, hPres2⟩ :=
    sweepSkewInsert_writeBS_steps (pc := pcBP + b1.length) h8 input hWork32 hLarge hNextLe
      hBnd2 (by rw [hb1] at hpl2; exact hpl2)
      s1 (by rw [pc1, hb1]) hz1 ho1 hstk1 hclk1 hSlKS1 hSlBS1
  have hSlPar2 : (s2.data[slParents]?).map Fin.val = some (parentsBase n m) := by
    have hlt : slParents < backSndBase n m + next := by unfold slParents; omega
    rcases hPres2 slParents with h | h
    · omega
    · rw [h]; exact hSlPar1
  have hBnd3 : pcBP + b1.length + b2.length + ((loadScratch h8 rTmp slParents).length + 2 + 1 +
      (sweepInitStoreScratch h8 slNext rVal).length + 2) < code.size := by
    rw [← hb3]; omega
  obtain ⟨s3, st3, pc3, hz3, ho3, hval3, hMemPar3, hNext3, hPres3⟩ :=
    sweepSkewInsert_writeParNext_steps (pc := pcBP + b1.length + b2.length) h8 input hWork32 hLarge hNextLe hWL
      hBnd3 (by rw [hb1, hb2] at hpl3; exact hpl3)
      s2 (by rw [pc2, hb1, hb2]) hz2 ho2 hstk2 hclk2 hSlPar2
  have hkLe : ((loadScratch h8 rVal slKeyFst).length + 1 + (loadScratch h8 rTmp slBackFst).length + 2) +
      ((loadScratch h8 rVal slKeySnd).length + (loadScratch h8 rTmp slBackSnd).length + 2) +
      ((loadScratch h8 rTmp slParents).length + 2 + 1 + (sweepInitStoreScratch h8 slNext rVal).length + 2) ≤ 92 := by
    have := loadScratch_length_le h8 rVal slKeyFst
    have := loadScratch_length_le h8 rTmp slBackFst
    have := loadScratch_length_le h8 rVal slKeySnd
    have := loadScratch_length_le h8 rTmp slBackSnd
    have := loadScratch_length_le h8 rTmp slParents
    have := sweepInitStoreScratch_length_le h8 slNext rVal
    omega
  refine ⟨s3, _, hkLe, (st1.append st2).append st3, pc3, hz3, ho3, hval3, ?_, ?_, hMemPar3, hNext3, fun w => ?_⟩
  · have hsl : slNext < backFstBase n m + next := by unfold slNext; omega
    have hBFNePar : backFstBase n m + next < parentsBase n m + next := by
      simp only [parentsBase, labelsBase, backSndBase, backFstBase]; omega
    rcases hPres3 (backFstBase n m + next) with h | h | h
    · omega
    · omega
    · rw [h]
      rcases hPres2 (backFstBase n m + next) with h2 | h2
      · omega
      · rw [h2]; exact hMemBF1
  · have hsl : slNext < backSndBase n m + next := by unfold slNext; omega
    have hBSNePar : backSndBase n m + next < parentsBase n m + next := by
      simp only [parentsBase, labelsBase, backSndBase]; omega
    rcases hPres3 (backSndBase n m + next) with h | h | h
    · omega
    · omega
    · rw [h]; exact hMemBS2
  · rcases hPres3 w with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rw [h]
      rcases hPres2 w with h2 | h2
      · exact Or.inr (Or.inr (Or.inl h2))
      · rw [h2]
        rcases hPres1 w with h1 | h1
        · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr (Or.inr (Or.inr h1)))

theorem sweepSkewInsert_step {bits inputCap workCap : Nat}
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
    (hIdxLt : idx < H.vertexCount) (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcStart pcWriteLabel slotIdx ancNode : Nat} {q : CutPair H}
    (hWL : pcWriteLabel < code.size)
    (hSz : pcStart + (sweepSkewInsert h8 pcStart pcWriteLabel).length < code.size)
    (hpl : Placed code pcStart (sweepSkewInsert h8 pcStart pcWriteLabel))
    (hSlotLt : slotIdx < (orderedConfig dictRows large).dict.size)
    (hAncLt : ancNode < F.size)
    (hpc : s.pc = pcStart) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hPtr : (reg s rPtr).val = slotIdx)
    (hSlAnc : (s.data[slAncNode]?).map Fin.val = some ancNode)
    (hSlKF : (s.data[slKeyFst]?).map Fin.val = some q.fst.val)
    (hSlKS : (s.data[slKeySnd]?).map Fin.val = some q.snd.val) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 185 ∧ Steps code input k s t ∧ t.pc = pcWriteLabel ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rVal).val = sRef.tables.next ∧
      (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 0]?).map Fin.val = some ancNode ∧
      (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 1]?).map Fin.val = some (F.depthOf ancNode + 1) ∧
      (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 2]?).map Fin.val = some (F.mkAppendedRecord ancNode).jump ∧
      (t.data[dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx]?).map Fin.val = some sRef.tables.next ∧
      (t.data[backFstBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val = some (q.fst.val + 1) ∧
      (t.data[backSndBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val = some q.snd.val ∧
      (t.data[parentsBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val = some ancNode ∧
      (t.data[slNext]?).map Fin.val = some (sRef.tables.next + 1) ∧
      ∀ w, w = slNext ∨
        w = jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 0 ∨
        w = jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 1 ∨
        w = jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 2 ∨
        w = dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx ∨
        w = backFstBase H.vertexCount H.arcCount + sRef.tables.next ∨
        w = backSndBase H.vertexCount H.arcCount + sRef.tables.next ∨
        w = parentsBase H.vertexCount H.arcCount + sRef.tables.next ∨
        t.data[w]? = s.data[w]? := by
  let n := H.vertexCount
  let m := H.arcCount
  let next := sRef.tables.next
  have hFSize : F.size = next := inv.grounded.size_eq
  have hNextLe : next ≤ n := Nat.le_trans inv.sRefNextLe hIdxLt
  have hAncF : ancNode < F.size := hAncLt
  have hAncLeN : ancNode ≤ n := by rw [hFSize] at hAncF; omega
  have hDepLe : F.depthOf ancNode ≤ n :=
    Nat.le_trans (validJumpForest_depthOf_le_pred inv.records.valid ancNode hAncLt) hAncLeN
  unfold sweepSkewInsert at hpl hSz
  dsimp only at hpl hSz
  let i10Read : List (Instr bits 15) :=
    loadScratch h8 rStack slAncNode ++ loadScratch h8 rClk slNext ++ loadScratch h8 rTin slJumpBase ++
    [ Instr.add rRem rTin rStack, Instr.add rRem rRem rStack, Instr.add rRem rRem rStack,
      Instr.add rTmp rRem rOne, Instr.loadData rVal rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rChild rTmp,
      Instr.add rRem rTin rChild, Instr.add rRem rRem rChild, Instr.add rRem rRem rChild,
      Instr.add rTmp rRem rOne, Instr.loadData rCnt rTmp, Instr.add rTmp rTmp rOne, Instr.loadData rCmd rTmp,
      Instr.add rRem rTin rCmd, Instr.add rRem rRem rCmd, Instr.add rRem rRem rCmd,
      Instr.add rTmp rRem rOne, Instr.loadData rTout rTmp,
      Instr.sub rRem rVal rCnt, Instr.sub rOff rCnt rTout ]
  let pcCmp := pcStart + i10Read.length
  let pcUseP := pcCmp + 3
  let pcHaveJump := pcUseP + 1
  let i10Cmp : List (Instr bits 15) :=
    [ .branchLt rZero rRem (pcCmp + 1) pcUseP,
      .branchLt rRem rOff pcUseP (pcCmp + 2),
      .branchLt rOff rRem pcUseP pcHaveJump,
      .mov rCmd rStack ]
  let i10J : List (Instr bits 15) :=
    [ Instr.add rRem rTin rClk, Instr.add rRem rRem rClk, Instr.add rRem rRem rClk,
      Instr.storeData rRem rStack,
      Instr.add rRem rRem rOne, Instr.add rVal rVal rOne, Instr.storeData rRem rVal,
      Instr.add rRem rRem rOne, Instr.storeData rRem rCmd ]
  let i10Sl := loadScratch h8 rTmp slDictSlots
  let i10SlSt : List (Instr bits 15) := [.add rTmp rTmp rPtr, .storeData rTmp rClk]
  let i10BP :=
    loadScratch h8 rVal slKeyFst ++ [.add rVal rVal rOne] ++
    loadScratch h8 rTmp slBackFst ++ [.add rTmp rTmp rClk, .storeData rTmp rVal] ++
    loadScratch h8 rVal slKeySnd ++
    loadScratch h8 rTmp slBackSnd ++ [.add rTmp rTmp rClk, .storeData rTmp rVal] ++
    loadScratch h8 rTmp slParents ++ [.add rTmp rTmp rClk, .storeData rTmp rStack] ++
    [.add rVal rClk rOne] ++ sweepInitStoreScratch h8 slNext rVal ++
    [.mov rVal rClk, .goto pcWriteLabel]
  have hiReadC : pcStart + i10Read.length + 4 + (9 + i10Sl.length + 2) + i10BP.length < code.size := by
    dsimp only [i10Read, i10Cmp, i10J, i10Sl, i10SlSt, i10BP] at hSz ⊢
    simp only [List.length_append, List.length_cons, List.length_nil] at hSz ⊢; omega
  have hRC := placed_append_left hpl
  have hplR : Placed code pcStart i10Read := placed_append_left hRC
  have hplC : Placed code (pcStart + i10Read.length) i10Cmp := placed_right_eq hRC rfl
  have hplW : Placed code (pcStart + i10Read.length + 4)
      ((i10J ++ i10Sl ++ i10SlSt) ++ i10BP) := by
    have hr := placed_right_eq hpl rfl
    have hCi : (i10Read ++ i10Cmp).length = i10Read.length + 4 := by simp [i10Cmp]
    rw [hCi] at hr
    change Placed code (pcStart + i10Read.length + 4) _ at hr
    repeat rw [List.append_assoc (i10J ++ i10Sl ++ i10SlSt)] at hr
    exact hr
  have hW_01 := placed_append_left hplW
  have hW_0 := placed_append_left hW_01
  have hplW_J : Placed code pcHaveJump i10J := placed_append_left hW_0
  have hplW_Sl : Placed code (pcHaveJump + 9) i10Sl :=
    placed_right_eq hW_0 (by dsimp only [i10J]; rfl)
  have hplW_SlSt : Placed code (pcHaveJump + 9 + i10Sl.length) i10SlSt :=
    placed_right_eq hW_01 (by dsimp only [i10J]; simp only [List.length_append]; rfl)
  have hplW_BP : Placed code (pcHaveJump + 9 + i10Sl.length + 2) i10BP :=
    placed_right_eq hplW (by
      dsimp only [i10J, i10SlSt]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hBndRC : pcStart + i10Read.length + 4 < code.size := by omega
  obtain ⟨sC, kRC, hkRC, stRC, pcC, hzC, hoC, hptrC, hstkC, hclkC, htinC, hvalC, hcmdC, hdC⟩ :=
    sweepSkewInsert_readCmp_steps h8 input hWork large inv.records (by rw [hFSize]; exact hNextLe)
      hBndRC hplR hplC hAncF hpc hz ho hPtr hSlAnc
      (by rw [hFSize]; exact inv.slNextVal) inv.slJumpVal
  let dictSlotsB := dictBase n m + 1 + 2 * (orderedConfig dictRows large).dict.size
  have hDictLe := dict_size_le H dictRows large
  have hDSBJump : dictSlotsB + slotIdx < jumpBase n m := by
    dsimp only [dictSlotsB]; simp only [jumpBase]; omega
  have hBndJ : pcHaveJump + 9 + i10Sl.length + 2 < code.size := by
    dsimp only [pcHaveJump, pcUseP, pcCmp]; omega
  obtain ⟨sJ, stJ, pcJ, hzJ, hoJ, hstkJ, hclkJ, hJ0, hJ1, hJ2, hSlotJ, hPresJ⟩ :=
    sweepSkewInsert_writeJumps_steps h8 input hWork large hNextLe hDepLe hDSBJump
      hBndJ hplW_J hplW_Sl hplW_SlSt sC (by rw [pcC])
      hzC hoC hptrC hstkC (by rw [hclkC, hFSize]) htinC hvalC hcmdC
      (by rw [hdC]; exact inv.slDictSlotsVal)
  have hPresJScr : ∀ sl, sl < 30 → sJ.data[sl]? = s.data[sl]? := fun sl hsl => by
    have hsC := hdC
    have := scratch_lt_orderBase (n := n) (m := m) (sl := 29) large (by decide)
    rcases hPresJ sl with h | h | h | h | h
    · simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at h; omega
    · simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at h; omega
    · simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at h; omega
    · dsimp only [dictSlotsB] at h
      simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at h; omega
    · rw [h, hsC]
  have hBndBP : pcHaveJump + 9 + i10Sl.length + 2 + i10BP.length < code.size := by
    dsimp only [pcHaveJump, pcUseP, pcCmp]; exact hiReadC
  obtain ⟨t, kBP, hkBP, stBP, pcT, hzT, hoT, hvalT, hBF, hBS, hPar, hNextT, hPresBP⟩ :=
    sweepSkewInsert_writeBackPar_steps h8 input hWork large hNextLe q.fst.isLt q.snd.isLt hWL
      hBndBP hplW_BP sJ pcJ hzJ hoJ hstkJ hclkJ
      (by rw [hPresJScr _ (by unfold slKeyFst; omega)]; exact hSlKF)
      (by rw [hPresJScr _ (by unfold slKeySnd; omega)]; exact hSlKS)
      (by rw [hPresJScr _ (by unfold slBackFst; omega)]; exact inv.slBackFstVal)
      (by rw [hPresJScr _ (by unfold slBackSnd; omega)]; exact inv.slBackSndVal)
      (by rw [hPresJScr _ (by unfold slParents; omega)]; exact inv.slParentsVal)
  have hiSlLe : (9 + i10Sl.length + 2) ≤ 23 := by
    dsimp only [i10Sl]; have := loadScratch_length_le h8 rTmp slDictSlots; omega
  have hScrLtJ : slNext < jumpBase H.vertexCount H.arcCount := by
    have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; unfold slNext; omega
  have hScrLtDS : slNext < dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx := by
    have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *; unfold slNext; omega
  have hJ2LtBF : jumpBase n m + 3 * next + 2 < backFstBase n m + next := by
    simp only [backFstBase]; omega
  have hSlotsLtBF : dictSlotsB + slotIdx < backFstBase n m + next := Nat.lt_trans hDSBJump (by omega)
  dsimp only [n, m, next, dictSlotsB] at hDSBJump hJ0 hJ1 hJ2 hSlotJ hBF hBS hPar hNextT hPresBP hPresJ hJ2LtBF hSlotsLtBF ⊢
  refine ⟨t, kRC + (9 + i10Sl.length + 2) + kBP, by omega, (stRC.append stJ).append stBP, pcT,
    hzT, hoT, hvalT, ?_, ?_, ?_, ?_, hBF, hBS, hPar, hNextT, fun w => ?_⟩
  · rcases hPresBP (jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 0) with h | h | h | h | h
    · omega
    · omega
    · simp only [backSndBase, backFstBase] at h; omega
    · simp only [parentsBase, labelsBase, backSndBase, backFstBase] at h; omega
    · rw [h]; exact hJ0
  · rcases hPresBP (jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 1) with h | h | h | h | h
    · omega
    · omega
    · simp only [backSndBase, backFstBase] at h; omega
    · simp only [parentsBase, labelsBase, backSndBase, backFstBase] at h; omega
    · rw [h]; exact hJ1
  · rcases hPresBP (jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 2) with h | h | h | h | h
    · omega
    · omega
    · simp only [backSndBase, backFstBase] at h; omega
    · simp only [parentsBase, labelsBase, backSndBase, backFstBase] at h; omega
    · rw [h]; exact hJ2
  · rcases hPresBP (dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx) with h | h | h | h | h
    · omega
    · omega
    · simp only [backSndBase, backFstBase] at h; omega
    · simp only [parentsBase, labelsBase, backSndBase, backFstBase] at h; omega
    · rw [h]; exact hSlotJ
  · rcases hPresBP w with h | h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · rw [h]
      rcases hPresJ w with h0 | h1 | h2 | h3 | h4
      · exact Or.inr (Or.inl h0)
      · exact Or.inr (Or.inr (Or.inl h1))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h2)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h3))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h4.trans (congrArg (·[w]?) hdC)))))))))

theorem sweepInstallTail_writeLabel_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (hLarge : 3 ≤ n)
    {pcWriteLabel pcLoopTop yVal idx : Nat}
    (hYLt : yVal < n) (hIdxLt : idx < n) (hLoopBnd : pcLoopTop < code.size)
    (hBnd : pcWriteLabel + (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
        [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
        sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]).length < code.size)
    (hpl : Placed code pcWriteLabel
      (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
        [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
        sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcWriteLabel) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    {newLabel : Nat} (hVal : (reg s rVal).val = newLabel)
    (hSlY : (s.data[slY]?).map Fin.val = some yVal)
    (hSlLab : (s.data[slLabels]?).map Fin.val = some (labelsBase n m))
    (hSlIdx : (s.data[slIdx]?).map Fin.val = some idx) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 55 ∧ Steps code input k s t ∧ t.pc = pcLoopTop ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[labelsBase n m + yVal]?).map Fin.val = some newLabel ∧
      (t.data[slIdx]?).map Fin.val = some (idx + 1) ∧
      ∀ w, w = slIdx ∨ w = labelsBase n m + yVal ∨ t.data[w]? = s.data[w]? := by
  let w2 : List (Instr bits 15) := [.add rTmp rTmp rClk, .storeData rTmp rVal]
  let w4 : List (Instr bits 15) := [.add rClk rClk rOne]
  let w6 : List (Instr bits 15) := [.goto pcLoopTop]
  have hwLen : (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++ w2 ++
      loadScratch h8 rClk slIdx ++ w4 ++ sweepInitStoreScratch h8 slIdx rClk ++ w6).length =
      (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2 +
      (loadScratch h8 rClk slIdx).length + 1 + (sweepInitStoreScratch h8 slIdx rClk).length + 1 := by
    dsimp only [w2, w4, w6]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hwLe : (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2 +
      (loadScratch h8 rClk slIdx).length + 1 + (sweepInitStoreScratch h8 slIdx rClk).length + 1 ≤ 55 := by
    have := loadScratch_length_le h8 rClk slY
    have := loadScratch_length_le h8 rTmp slLabels
    have := loadScratch_length_le h8 rClk slIdx
    have := sweepInitStoreScratch_length_le h8 slIdx rClk
    omega
  have hBnd' : pcWriteLabel + ((loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2 +
      (loadScratch h8 rClk slIdx).length + 1 + (sweepInitStoreScratch h8 slIdx rClk).length + 1) < code.size := by
    rw [← hwLen]; exact hBnd
  have h5 := placed_append_left hpl
  have h4 := placed_append_left h5
  have h3 := placed_append_left h4
  have h2 := placed_append_left h3
  have h1 := placed_append_left h2
  have hpl0 : Placed code pcWriteLabel (loadScratch h8 rClk slY) := placed_append_left h1
  have hpl1 : Placed code (pcWriteLabel + (loadScratch h8 rClk slY).length) (loadScratch h8 rTmp slLabels) :=
    placed_right_eq h1 rfl
  have hpl2 : Placed code (pcWriteLabel + (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length) w2 :=
    placed_right_eq h2 (by simp only [List.length_append]; omega)
  have hpl3 : Placed code (pcWriteLabel + (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2)
      (loadScratch h8 rClk slIdx) :=
    placed_right_eq h3 (by dsimp only [w2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl4 : Placed code (pcWriteLabel + (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2 +
      (loadScratch h8 rClk slIdx).length) w4 :=
    placed_right_eq h4 (by dsimp only [w2]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl5 : Placed code (pcWriteLabel + (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2 +
      (loadScratch h8 rClk slIdx).length + 1) (sweepInitStoreScratch h8 slIdx rClk) :=
    placed_right_eq h5 (by dsimp only [w2, w4]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hpl6 : Placed code (pcWriteLabel + (loadScratch h8 rClk slY).length + (loadScratch h8 rTmp slLabels).length + 2 +
      (loadScratch h8 rClk slIdx).length + 1 + (sweepInitStoreScratch h8 slIdx rClk).length) w6 :=
    placed_right_eq hpl (by dsimp only [w2, w4]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hSlYW : slY < workCap := by unfold slY; omega
  have hSlLW : slLabels < workCap := by unfold slLabels; omega
  have hSlIW : slIdx < workCap := by unfold slIdx; omega
  have hLabFit : labelsBase n m + yVal < workCap := by
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
      stampsBase, indegBase, csrArenaWords] at hWork32 ⊢; omega
  have hSlIdxLtLab : slIdx < labelsBase n m + yVal := by
    have := scratch_lt_orderBase (n := n) (m := m) (sl := 29) hLarge (by decide)
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase] at *
    unfold slIdx; omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rClk slY hSlYW (by decide)
    hpc hpl0 (by omega) ho hSlY
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have hval1 : (reg s1 rVal).val = newLabel := by rw [k1 _ (by decide) (by decide), hVal]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ := loadScratch_val_steps h8 (input := input) rTmp slLabels hSlLW (by decide)
    pc1 hpl1 (by omega) ho1 (by rw [d1]; exact hSlLab)
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), ho1]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hz1]
  have hclk2 : (reg s2 rClk).val = yVal := by rw [k2 _ (by decide) (by decide), r1]
  have hval2 : (reg s2 rVal).val = newLabel := by rw [k2 _ (by decide) (by decide), hval1]
  obtain ⟨s3a, st3a, pc3a, r3a, k3a, d3a⟩ := step_add15_at (input := input)
    (placed_fetch hpl2 (i := 0) rfl pc2) (by rw [pc2]; omega)
  have htmp3a : (reg s3a rTmp).val = labelsBase n m + yVal := by
    rw [r3a, WordOps.add_val, r2, hclk2]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hLabFit hw)
  have hd3aFit : (reg s3a rTmp).val < workCap := by rw [htmp3a]; exact hLabFit
  obtain ⟨s3, st3b, pc3, d3b, k3⟩ := step_storeData_at (input := input)
    (placed_fetch hpl2 (i := 1) rfl (by rw [pc3a, pc2])) (by rw [pc3a, pc2]; omega) hd3aFit
  have hMemLab3 : (s3.data[labelsBase n m + yVal]?).map Fin.val = some newLabel := by
    rw [d3b, show labelsBase n m + yVal = (reg s3a rTmp).val from htmp3a.symm,
      Array.getElem?_set_self, Option.map_some, k3a _ (by decide), hval2]
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3, k3a _ (by decide), ho2]
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3, k3a _ (by decide), hz2]
  have hSlIdx3 : (s3.data[slIdx]?).map Fin.val = some idx := by
    rw [storeData_getElem?_ne _ d3b (by rw [htmp3a]; omega), d3a, d2, d1]; exact hSlIdx
  obtain ⟨s4, st4, pc4, r4, d4, k4⟩ := loadScratch_val_steps h8 (input := input) rClk slIdx hSlIW (by decide)
    (by rw [pc3, pc3a, pc2]) hpl3 (by omega) ho3 hSlIdx3
  have ho4 : (reg s4 rOne).val = 1 := by rw [k4 _ (by decide) (by decide), ho3]
  have hz4 : (reg s4 rZero).val = 0 := by rw [k4 _ (by decide) (by decide), hz3]
  obtain ⟨s5, st5, pc5, r5, k5, d5⟩ := step_add15_at (input := input)
    (placed_fetch hpl4 (i := 0) rfl pc4) (by rw [pc4]; omega)
  have hclk5 : (reg s5 rClk).val = idx + 1 := by
    rw [r5, WordOps.add_val, r4, ho4]; exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega : idx + 1 < workCap) hw)
  have ho5 : (reg s5 rOne).val = 1 := by rw [k5 _ (by decide), ho4]
  have hz5 : (reg s5 rZero).val = 0 := by rw [k5 _ (by decide), hz4]
  obtain ⟨s6, st6, pc6, hIdx6, hFr6, k6⟩ := storeScratch_val_steps h8 (input := input) slIdx rClk
    (by decide) (by decide) hSlIW (by rw [pc5, pc4]) hpl5 (by omega) ho5
  have hf6 : code[s6.pc]? = some (.goto pcLoopTop) :=
    placed_fetch hpl6 (i := 0) rfl pc6
  have st7 : step code input s6 = some (.next { s6 with pc := pcLoopTop }) := step_goto_at hf6 hLoopBnd
  have st3 : Steps code input 2 s2 s3 := .cons st3a (.cons st3b (.zero _))
  refine ⟨{ s6 with pc := pcLoopTop }, _, hwLe,
    (((((st1.append st2).append st3).append st4).append (.cons st5 (.zero _))).append st6).append (.cons st7 (.zero _)),
    rfl,
    by change (reg s6 rZero).val = 0; rw [k6 _ (by decide), hz5],
    by change (reg s6 rOne).val = 1; rw [k6 _ (by decide), ho5],
    ?_, ?_, ?_⟩
  · change (s6.data[labelsBase n m + yVal]?).map Fin.val = some newLabel
    rw [hFr6 _ (by omega), d5, d4, hMemLab3]
  · change (s6.data[slIdx]?).map Fin.val = some (idx + 1)
    rw [hIdx6, hclk5]
  · intro w
    change w = slIdx ∨ w = labelsBase n m + yVal ∨ s6.data[w]? = s.data[w]?
    by_cases hI : w = slIdx
    · exact Or.inl hI
    by_cases hL : w = labelsBase n m + yVal
    · exact Or.inr (Or.inl hL)
    rw [hFr6 w hI, d5, d4, storeData_getElem?_ne _ d3b (by rw [htmp3a]; exact Ne.symm hL), d3a, d2, d1]
    exact Or.inr (Or.inr rfl)

theorem sweepInstallTail_keep_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (hLarge : 3 ≤ n)
    {pcKeep pcWriteLabel pcLoopTop yVal idx ancNode : Nat}
    (hYLt : yVal < n) (hIdxLt : idx < n) (hLoopBnd : pcLoopTop < code.size)
    (hWL : pcWriteLabel = pcKeep + (loadScratch h8 rVal slAncNode).length + 2)
    (hBnd : pcKeep + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length < code.size)
    (hpl : Placed code pcKeep (sweepInstallTail h8 pcWriteLabel pcLoopTop))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcKeep) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlAnc : (s.data[slAncNode]?).map Fin.val = some ancNode)
    (hSlY : (s.data[slY]?).map Fin.val = some yVal)
    (hSlLab : (s.data[slLabels]?).map Fin.val = some (labelsBase n m))
    (hSlIdx : (s.data[slIdx]?).map Fin.val = some idx) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 70 ∧ Steps code input k s t ∧ t.pc = pcLoopTop ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[labelsBase n m + yVal]?).map Fin.val = some ancNode ∧
      (t.data[slIdx]?).map Fin.val = some (idx + 1) ∧
      ∀ w, w = slIdx ∨ w = labelsBase n m + yVal ∨ t.data[w]? = s.data[w]? := by
  unfold sweepInstallTail at hpl hBnd
  dsimp only at hpl hBnd
  let keepB := loadScratch h8 rVal slAncNode ++ [Instr.goto pcWriteLabel]
  let zeroB : List (Instr bits 15) := [Instr.mov rVal rZero]
  let writeLabB :=
    loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
      loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
      sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]
  have hLenK : keepB.length = (loadScratch h8 rVal slAncNode).length + 1 := by
    dsimp only [keepB]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hLenTot : (keepB ++ zeroB ++ writeLabB).length = keepB.length + 1 + writeLabB.length := by
    dsimp only [zeroB]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hBndWL : pcWriteLabel + writeLabB.length < code.size := by
    rw [hLenTot, hLenK] at hBnd; omega
  have hKeepZero := placed_append_left hpl
  have hplKeep := placed_append_left hKeepZero
  have hplAnc : Placed code pcKeep (loadScratch h8 rVal slAncNode) := placed_append_left hplKeep
  have hplGo : Placed code (pcKeep + (loadScratch h8 rVal slAncNode).length) [Instr.goto pcWriteLabel] :=
    placed_right_eq hplKeep rfl
  have hplWL : Placed code pcWriteLabel writeLabB :=
    placed_right_eq hpl (by dsimp only [keepB, zeroB, writeLabB]; rw [hWL]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hSlAW : slAncNode < workCap := by unfold slAncNode; omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ := loadScratch_val_steps h8 (input := input) rVal slAncNode hSlAW (by decide)
    hpc hplAnc (by rw [hLenTot, hLenK] at hBnd; omega) ho hSlAnc
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have hf1 : code[s1.pc]? = some (.goto pcWriteLabel) := placed_fetch hplGo (i := 0) rfl pc1
  have hWLBnd : pcWriteLabel < code.size := by omega
  have st2 : step code input s1 = some (.next { s1 with pc := pcWriteLabel }) := step_goto_at hf1 hWLBnd
  obtain ⟨t, kW, hkW, stW, pcT, hzT, hoT, hLabT, hIdxT, hPresT⟩ :=
    sweepInstallTail_writeLabel_steps h8 input hWork32 hLarge hYLt hIdxLt hLoopBnd hBndWL hplWL
      { s1 with pc := pcWriteLabel } rfl hz1 ho1 r1
      (by change (s1.data[slY]?).map Fin.val = some yVal; rw [d1]; exact hSlY)
      (by change (s1.data[slLabels]?).map Fin.val = some (labelsBase n m); rw [d1]; exact hSlLab)
      (by change (s1.data[slIdx]?).map Fin.val = some idx; rw [d1]; exact hSlIdx)
  have hKLe : (loadScratch h8 rVal slAncNode).length ≤ 12 := loadScratch_length_le h8 rVal slAncNode
  refine ⟨t, (loadScratch h8 rVal slAncNode).length + 1 + kW, by omega,
    (st1.append (.cons st2 (.zero _))).append stW, pcT, hzT, hoT, hLabT, hIdxT, fun w => ?_⟩
  rcases hPresT w with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans (congrArg (·[w]?) d1)))

theorem sweepInstallTail_zero_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {n m : Nat} (hWork32 : 32 * n + 7 * m + 17 ≤ workCap) (hLarge : 3 ≤ n)
    {pcKeep pcWriteLabel pcLoopTop yVal idx : Nat}
    (hYLt : yVal < n) (hIdxLt : idx < n) (hLoopBnd : pcLoopTop < code.size)
    (hWL : pcWriteLabel = pcKeep + (loadScratch h8 rVal slAncNode).length + 2)
    (hBnd : pcKeep + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length < code.size)
    (hpl : Placed code pcKeep (sweepInstallTail h8 pcWriteLabel pcLoopTop))
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = pcKeep + (loadScratch h8 rVal slAncNode).length + 1)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlY : (s.data[slY]?).map Fin.val = some yVal)
    (hSlLab : (s.data[slLabels]?).map Fin.val = some (labelsBase n m))
    (hSlIdx : (s.data[slIdx]?).map Fin.val = some idx) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 56 ∧ Steps code input k s t ∧ t.pc = pcLoopTop ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[labelsBase n m + yVal]?).map Fin.val = some 0 ∧
      (t.data[slIdx]?).map Fin.val = some (idx + 1) ∧
      ∀ w, w = slIdx ∨ w = labelsBase n m + yVal ∨ t.data[w]? = s.data[w]? := by
  unfold sweepInstallTail at hpl hBnd
  dsimp only at hpl hBnd
  let keepB := loadScratch h8 rVal slAncNode ++ [Instr.goto pcWriteLabel]
  let zeroB : List (Instr bits 15) := [Instr.mov rVal rZero]
  let writeLabB :=
    loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
      loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
      sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]
  have hLenK : keepB.length = (loadScratch h8 rVal slAncNode).length + 1 := by
    dsimp only [keepB]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hLenTot : (keepB ++ zeroB ++ writeLabB).length = keepB.length + 1 + writeLabB.length := by
    dsimp only [zeroB]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hBndWL : pcWriteLabel + writeLabB.length < code.size := by
    rw [hLenTot, hLenK] at hBnd; omega
  have hKeepZero := placed_append_left hpl
  have hplZero : Placed code (pcKeep + (loadScratch h8 rVal slAncNode).length + 1) zeroB :=
    placed_right_eq hKeepZero (by dsimp only [keepB, zeroB]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hplWL : Placed code pcWriteLabel writeLabB :=
    placed_right_eq hpl (by dsimp only [keepB, zeroB, writeLabB]; rw [hWL]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  have hfZ : code[s.pc]? = some (.mov rVal rZero) := placed_fetch hplZero (i := 0) rfl hpc
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ := step_mov_at (input := input) hfZ (by rw [hpc]; omega)
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide), hz]
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide), ho]
  have hval1 : (reg s1 rVal).val = 0 := by rw [r1, hz]
  obtain ⟨t, kW, hkW, stW, pcT, hzT, hoT, hLabT, hIdxT, hPresT⟩ :=
    sweepInstallTail_writeLabel_steps h8 input hWork32 hLarge hYLt hIdxLt hLoopBnd hBndWL hplWL
      s1 (by rw [pc1, hpc, hWL]) hz1 ho1 hval1
      (by rw [d1]; exact hSlY) (by rw [d1]; exact hSlLab) (by rw [d1]; exact hSlIdx)
  refine ⟨t, 1 + kW, by omega, by rw [Nat.add_comm 1 kW]; exact .cons st1 stW, pcT, hzT, hoT, hLabT, hIdxT, fun w => ?_⟩
  rcases hPresT w with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (h.trans (congrArg (·[w]?) d1)))

theorem measuredSearch_cut_lt_hi (p : Nat → PaperB.ForestHead.Probe)
    (fuel lo hi : Nat) (hlt : lo < hi) :
    (PaperB.ForestHead.measuredSearch p fuel lo hi).cut < hi := by
  induction fuel generalizing lo hi with
  | zero => exact hlt
  | succ fuel ih =>
    by_cases hs : hi ≤ lo + 1
    · simp [PaperB.ForestHead.measuredSearch, hs, hlt]
    · have hMidLo : lo < lo + (hi - lo) / 2 := by omega
      have hMidHi : lo + (hi - lo) / 2 < hi := by omega
      by_cases hp : (p (lo + (hi - lo) / 2)).ok = true
      · simp only [PaperB.ForestHead.measuredSearch, ite_eq_right hs, ite_eq_left hp,
          PaperB.ForestHead.addProbe]
        exact ih (lo + (hi - lo) / 2) hi hMidHi
      · simp only [PaperB.ForestHead.measuredSearch, ite_eq_right hs, ite_eq_right hp,
          PaperB.ForestHead.addProbe]
        exact Nat.lt_trans (ih lo (lo + (hi - lo) / 2) hMidLo) hMidHi

theorem sweep_active_step_spec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hidx : idx < H.vertexCount)
    {y m_y : Vertex H} (hyNe : y ≠ H.root)
    (hNoRoot : H.hasQuotientArcBool H.root y = false)
    (hMax : maxByRank rank (preds H y) = some m_y) :
    let c := orderedConfig dictRows large
    let cut := (PaperB.ForestHead.measuredLog
      (fun d => PaperB.ForestHead.probe (selectors c sRef) (rows.row y) m_y d)
      (F.depthOf (sRef.labelAt m_y.val) + 1)).cut
    let ancNode := F.ancestorAtDepth (sRef.labelAt m_y.val) cut
    cut ≤ F.depthOf (sRef.labelAt m_y.val) ∧
    ancNode < F.size ∧
    ∃ rStep : _root_.EX24.HeadResult H,
      _root_.EX24.stepPrepared c sRef rank y (dictRows.row y) = some rStep ∧
      rStep.measured.step.parent = ancNode ∧
      rStep.measured.step.newPair = PaperB.ForestHead.preparedKey H (dictRows.row y) ∧
      (∀ (q : CutPair H) (slotIdx : Nat),
        PaperB.ForestHead.preparedKey H (dictRows.row y) = some q →
        (PaperB.PairLookup.lookup c.dict (c.code q)).1 = some slotIdx →
        if sRef.tables.slotAt slotIdx = 0 then
          rStep.installed.allocated = true ∧ rStep.installed.node = sRef.tables.next
        else
          rStep.installed.allocated = false ∧ rStep.installed.node = sRef.tables.slotAt slotIdx) ∧
      (PaperB.ForestHead.preparedKey H (dictRows.row y) = none →
        rStep.installed.allocated = false ∧ rStep.installed.node = ancNode) := by
  let c := orderedConfig dictRows large
  let S := selectors c sRef
  have hcUse : c.usePackedWords = c := rfl
  have hmF : sRef.labelAt m_y.val < F.size := inv.grounded.size_eq ▸ inv.labelsLt m_y
  have hLabM : S.label m_y = sRef.labelAt m_y.val := rfl
  have hmDep : S.depth (S.label m_y) = F.depthOf (sRef.labelAt m_y.val) := by
    rw [hLabM]
    simpa only [S, hcUse] using packedSelector_depth c sRef inv.grounded.layout ⟨sRef.labelAt m_y.val, hmF⟩
  let pRows : Nat → PaperB.ForestHead.Probe :=
    fun d => PaperB.ForestHead.probe S (rows.row y) m_y d
  let pDict : Nat → PaperB.ForestHead.Probe :=
    fun d => PaperB.ForestHead.probe S (dictRows.row y) m_y d
  let cut := (PaperB.ForestHead.measuredLog pRows (F.depthOf (sRef.labelAt m_y.val) + 1)).cut
  let ancNode := F.ancestorAtDepth (sRef.labelAt m_y.val) cut
  have hCutLt : cut < F.depthOf (sRef.labelAt m_y.val) + 1 :=
    measuredSearch_cut_lt_hi pRows _ 0 (F.depthOf (sRef.labelAt m_y.val) + 1) (Nat.zero_lt_succ _)
  have hCutLe : cut ≤ F.depthOf (sRef.labelAt m_y.val) := Nat.lt_succ_iff.mp hCutLt
  have hAncSpec := inv.records.valid.ancestorAtDepth_spec hmF hCutLe
  have hAncF : ancNode < F.size := hAncSpec.1
  have hCutEq : (PaperB.ForestHead.measuredLog pDict (S.depth (S.label m_y) + 1)).cut = cut := by
    rw [hmDep]
    have p1 := congrArg Prod.fst (PaperB.ForestHead.measuredLog_project pRows (F.depthOf (sRef.labelAt m_y.val) + 1))
    have p2 := congrArg Prod.fst (PaperB.ForestHead.measuredLog_project pDict (F.depthOf (sRef.labelAt m_y.val) + 1))
    dsimp only at p1 p2
    dsimp only [cut]
    rw [p1, p2]
    have hOkEq : (fun d => (pDict d).ok) = (fun d => (pRows d).ok) := by
      funext d
      by_cases hz : d = 0
      · simp [pRows, pDict, PaperB.ForestHead.probe, hz]
      by_cases hd : d ≤ S.depth (S.label m_y)
      · simp only [pRows, pDict, PaperB.ForestHead.probe, ite_eq_right hz, ite_eq_left hd]
        have hiff : (PaperB.ForestHead.scan (PaperB.ForestHead.raw S (S.atDepth (S.label m_y) d)
              (S.key (S.atDepth (S.label m_y) d))) (dictRows.row y)).ok = true ↔
            (PaperB.ForestHead.scan (PaperB.ForestHead.raw S (S.atDepth (S.label m_y) d)
              (S.key (S.atDepth (S.label m_y) d))) (rows.row y)).ok = true := by
          rw [PaperB.ForestHead.scan_ok, PaperB.ForestHead.scan_ok]
          constructor <;> intro h u hu
          · exact h u (((dictRows.spec y).cover u).mpr (((rows.spec y).cover u).mp hu))
          · exact h u (((rows.spec y).cover u).mpr (((dictRows.spec y).cover u).mp hu))
        exact Bool.eq_iff_iff.mpr hiff
      · simp [pRows, pDict, PaperB.ForestHead.probe, hz, hd]
    rw [hOkEq]
  have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b := fun h => distinctRanks_of_stage1 inv.stage1 h
  have hRunPrep : PaperB.ForestHead.runPrepared S rank y (dictRows.row y) =
      PaperB.ForestHead.active S (dictRows.row y) m_y (PaperB.ForestHead.preparedKey H (dictRows.row y)) := by
    rw [PaperB.ForestHead.runPrepared_eq_runHead S rank y (dictRows.row y) (dictRows.spec y) inj]
    simp [PaperB.ForestHead.runHead, hyNe, hNoRoot, hMax,
      ← PaperB.ForestHead.preparedKey_eq_candidate y (dictRows.row y) (dictRows.spec y)]
  have hParentEq : (PaperB.ForestHead.runPrepared S rank y (dictRows.row y)).step.parent = ancNode := by
    rw [hRunPrep]
    dsimp only [PaperB.ForestHead.active, PaperB.ForestHead.finish]
    change PaperB.ForestHead.nodeAt S (S.label m_y)
      (PaperB.ForestHead.measuredLog pDict (S.depth (S.label m_y) + 1)).cut = ancNode
    rw [hCutEq, hLabM]
    by_cases hcz : cut = 0
    · simp only [PaperB.ForestHead.nodeAt, hcz, ↓reduceIte, ancNode]
      exact (inv.records.valid.ancestorAtDepth_zero hmF).symm
    · simp only [PaperB.ForestHead.nodeAt, hcz, ↓reduceIte]
      simpa only [S, hcUse] using packedSelector_atDepth c sRef inv.grounded.layout ⟨sRef.labelAt m_y.val, hmF⟩ cut
  have hPairEq : (PaperB.ForestHead.runPrepared S rank y (dictRows.row y)).step.newPair =
      PaperB.ForestHead.preparedKey H (dictRows.row y) := by
    rw [hRunPrep]; rfl
  have hStepExists : ∃ rStep, _root_.EX24.stepPrepared c sRef rank y (dictRows.row y) = some rStep := by
    refine PaperB.ForestDictionary.stepPrepared_dictionary_exists dictRows (hd := rfl) inj inv.grounded
      (by change y.val < sRef.labels.size; rw [inv.sRefLabelsSize]; exact y.isLt)
      (by rw [hParentEq, ← inv.grounded.size_eq]; exact hAncF)
      (fun k hk => by
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hk
        exact (PaperB.PairLookup.lookup_member_iff c.dict k c.sorted).mpr
          ⟨i, by simpa only [Array.length_toList] using hi, by simpa only [Array.getElem_toList] using heq⟩)
      (fun k i hk hi _ => by
        rw [inv.grounded.back_size]
        change sRef.tables.next < (PaperB.Jumps.ConcreteInit.region H.vertexCount).maxNodes + 1
        simp only [PaperB.Jumps.ConcreteInit.region]
        have := inv.sRefNextLe; omega)
  obtain ⟨rStep, hStep⟩ := hStepExists
  obtain ⟨hm, hInst, _, _, _⟩ := PaperB.ForestDictionary.stepPrepared_dictionary_parts dictRows rfl inj hStep
  have hrPar : rStep.measured.step.parent = ancNode := by rw [hm]; exact hParentEq
  have hrPair : rStep.measured.step.newPair = PaperB.ForestHead.preparedKey H (dictRows.row y) := by
    rw [hm]; exact hPairEq
  have hpNext : rStep.measured.step.parent < sRef.tables.next := by
    rw [hrPar, ← inv.grounded.size_eq]; exact hAncF
  refine ⟨hCutLe, hAncF, rStep, hStep, hrPar, hrPair, ?_, ?_⟩
  · intro q slotIdx hKey hLook
    have hq : rStep.measured.step.newPair = some q := hrPair.trans hKey
    have hi : slotIdx < sRef.tables.slots.size := by
      rw [inv.grounded.slot_size]
      exact ((PaperB.PairLookup.lookup_eq_some_iff c.dict (c.code q) c.sorted slotIdx).mp hLook).1
    have hInst' := hInst
    dsimp only [c] at hInst'
    simp only [_root_.EX24.install, ite_eq_left hpNext, hq, hLook, dite_eq_left hi] at hInst'
    by_cases hZero : sRef.tables.slotAt slotIdx = 0
    · have hn : sRef.tables.next < sRef.tables.back.size := by
        rw [inv.grounded.back_size]
        change sRef.tables.next < (PaperB.Jumps.ConcreteInit.region H.vertexCount).maxNodes + 1
        simp only [PaperB.Jumps.ConcreteInit.region]
        have := inv.sRefNextLe; omega
      simp only [ite_eq_left hZero, dite_eq_left hn, Option.some.injEq] at hInst'
      rw [ite_eq_left hZero, ← hInst']
      exact ⟨rfl, rfl⟩
    · simp only [ite_eq_right hZero, Option.some.injEq] at hInst'
      rw [ite_eq_right hZero, ← hInst']
      exact ⟨rfl, rfl⟩
  · intro hKeyNone
    have hqNone : rStep.measured.step.newPair = none := hrPair.trans hKeyNone
    have hInst' := hInst
    simp only [_root_.EX24.install, ite_eq_left hpNext, hqNone, Option.some.injEq] at hInst'
    rw [← hInst']
    exact ⟨rfl, hrPar⟩

theorem sweepInstallBlock_eq {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcLoopTop : Nat) :
    sweepInstallBlock h8 pcStart pcLoopTop =
      (sweepPairAndDictBS h8 pcStart
          (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length)
          (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8)
          (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8 + 1) ++
        sweepSkewInsert h8 (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length)
          (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8 + 1)) ++
        sweepInstallTail h8
          (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8 + 1)
          pcLoopTop := by
  unfold sweepInstallBlock; rfl

theorem sweepInstallTail_eq_parts {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcWriteLabel pcLoopTop : Nat) :
    sweepInstallTail h8 pcWriteLabel pcLoopTop =
      (loadScratch h8 rVal slAncNode ++ [Instr.goto pcWriteLabel] ++ [Instr.mov rVal rZero]) ++
        (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
          [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
          loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
          sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]) := by
  unfold sweepInstallTail
  repeat rw [List.append_assoc (loadScratch h8 rVal slAncNode ++ [Instr.goto pcWriteLabel] ++ [Instr.mov rVal rZero])]
  rfl

theorem sweepInstallTail_writeLabel_placed {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {pcKeepP pcWriteLabel pcLoopTop : Nat}
    (hWL : pcWriteLabel = pcKeepP + (loadScratch h8 rVal slAncNode).length + 2)
    (hpl : Placed code pcKeepP (sweepInstallTail h8 pcWriteLabel pcLoopTop)) :
    Placed code pcWriteLabel
      (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
        [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
        sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]) := by
  rw [sweepInstallTail_eq_parts] at hpl
  exact placed_right_eq hpl (by
    rw [hWL]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)

theorem sweepInstallBlock_len_parts {bits : Nat} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcLoopTop : Nat) :
    let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
    let d2 := (sweepSkewInsert h8 0 0).length
    let pcWriteLabel := pcStart + d1 + d2 + sweepInstallKeepLen h8 + 1
    (sweepInstallBlock h8 pcStart pcLoopTop).length =
      d1 + d2 + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length := by
  dsimp only
  rw [sweepInstallBlock_eq]
  simp only [List.length_append, sweepPairAndDictBS_length, sweepSkewInsert_length]

theorem sweepInstallBlock_slices {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {pcStart pcLoopTop : Nat}
    (hpl : Placed code pcStart (sweepInstallBlock h8 pcStart pcLoopTop)) :
    let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
    let d2 := (sweepSkewInsert h8 0 0).length
    let pcKeepP := pcStart + d1 + d2
    let pcWriteZero := pcKeepP + sweepInstallKeepLen h8
    let pcWriteLabel := pcWriteZero + 1
    Placed code pcStart (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel) ∧
    Placed code (pcStart + d1) (sweepSkewInsert h8 (pcStart + d1) pcWriteLabel) ∧
    Placed code pcKeepP (sweepInstallTail h8 pcWriteLabel pcLoopTop) := by
  dsimp only
  rw [sweepInstallBlock_eq] at hpl
  have hpl12 := placed_append_left hpl
  have hd1 := sweepPairAndDictBS_length h8 pcStart
    (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length)
    (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8)
    (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8 + 1)
  have hd2 := sweepSkewInsert_length h8 (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length)
    (pcStart + (sweepPairAndDictBS h8 0 0 0 0).length + (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8 + 1)
  refine ⟨placed_append_left hpl12, placed_right_eq hpl12 (congrArg (pcStart + ·) hd1.symm),
    placed_right_eq hpl (by rw [List.length_append, hd1, hd2]; omega)⟩

theorem sweepInstallBlock_grow_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s s1 : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hidx : idx < H.vertexCount) (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcStart pcLoopTop : Nat} (hLoopBnd : pcLoopTop < code.size)
    (hSz : pcStart + (sweepInstallBlock h8 pcStart pcLoopTop).length < code.size)
    (hpl : Placed code pcStart (sweepInstallBlock h8 pcStart pcLoopTop))
    {y : Vertex H} (ancNode : Nat) (hAncF : ancNode < F.size)
    {rStep : _root_.EX24.HeadResult H}
    (hStep : _root_.EX24.stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep)
    (hrPar : rStep.measured.step.parent = ancNode)
    {q : CutPair H} {slotIdx : Nat}
    (hKeyD : PaperB.ForestHead.preparedKey H (dictRows.row y) = some q)
    (hq : rStep.measured.step.newPair = some q)
    (hLook : (PaperB.PairLookup.lookup (orderedConfig dictRows large).dict ((orderedConfig dictRows large).code q)).1 = some slotIdx)
    (hHit : slotIdx < (orderedConfig dictRows large).dict.size)
    (hAlloc : rStep.installed.allocated = true) (hNode : rStep.installed.node = sRef.tables.next)
    (hSlAnc : (s.data[slAncNode]?).map Fin.val = some ancNode)
    (hSlY : (s.data[slY]?).map Fin.val = some y.val)
    (k1 : Nat) (hk1 : k1 ≤ 150 + 17 * (OracleContract.L H.vertexCount + 1))
    (st1 : Steps code input k1 s s1)
    (pc1 : s1.pc = pcStart + (sweepPairAndDictBS h8 0 0 0 0).length)
    (hz1 : (reg s1 rZero).val = 0) (ho1 : (reg s1 rOne).val = 1) (hptr1 : (reg s1 rPtr).val = slotIdx)
    (hSlKF1 : (s1.data[slKeyFst]?).map Fin.val = some q.fst.val)
    (hSlKS1 : (s1.data[slKeySnd]?).map Fin.val = some q.snd.val)
    (hPres1 : ∀ w, w = slKeyFst ∨ w = slKeySnd ∨ s1.data[w]? = s.data[w]?) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 390 + 17 * (OracleContract.L H.vertexCount + 1) ∧
      Steps code input k s t ∧ t.pc = pcLoopTop ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large)
        (F.appendLeaf rStep.measured.step.parent) rStep.state (idx + 1) t := by
  let n := H.vertexCount
  let m := H.arcCount
  let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
  let d2 := (sweepSkewInsert h8 0 0).length
  let pcKeepP := pcStart + d1 + d2
  let pcWriteZero := pcKeepP + sweepInstallKeepLen h8
  let pcWriteLabel := pcWriteZero + 1
  have _ := hKeyD
  have hd1 : (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length = d1 :=
    sweepPairAndDictBS_length h8 pcStart pcKeepP pcWriteZero pcWriteLabel
  have hd2 : (sweepSkewInsert h8 (pcStart + d1) pcWriteLabel).length = d2 :=
    sweepSkewInsert_length h8 (pcStart + d1) pcWriteLabel
  have hLenTot : (sweepInstallBlock h8 pcStart pcLoopTop).length =
      d1 + d2 + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length :=
    sweepInstallBlock_len_parts h8 pcStart pcLoopTop
  have hKeepLen : sweepInstallKeepLen h8 = (loadScratch h8 rVal slAncNode).length + 1 := rfl
  have hTailLen : (sweepInstallTail h8 pcWriteLabel pcLoopTop).length ≥
      (loadScratch h8 rVal slAncNode).length + 2 := by
    rw [sweepInstallTail_eq_parts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hWL : pcWriteLabel < code.size := by
    dsimp only [pcWriteLabel, pcWriteZero, pcKeepP]; rw [hKeepLen]; rw [hLenTot] at hSz; omega
  have hBnd2 : (pcStart + d1) + (sweepSkewInsert h8 (pcStart + d1) pcWriteLabel).length < code.size := by
    rw [hd2]; rw [hLenTot] at hSz; omega
  obtain ⟨_, hpl2, hpl3⟩ := sweepInstallBlock_slices h8 hpl
  have inv1 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s1 :=
    inv.of_scratch19 (fun j hj => by
      rcases hPres1 j with rfl | rfl | heq
      · unfold slKeyFst at hj; omega
      · unfold slKeySnd at hj; omega
      · exact heq)
  have hPresS1 : ∀ sl, sl < 28 → s1.data[sl]? = s.data[sl]? := fun sl hsl => by
    rcases hPres1 sl with rfl | rfl | heq
    · unfold slKeyFst at hsl; omega
    · unfold slKeySnd at hsl; omega
    · exact heq
  have hSlAnc1 : (s1.data[slAncNode]?).map Fin.val = some ancNode := by
    rw [hPresS1 _ (by unfold slAncNode; omega)]; exact hSlAnc
  have hSlY1 : (s1.data[slY]?).map Fin.val = some y.val := by
    rw [hPresS1 _ (by unfold slY; omega)]; exact hSlY
  have hSlLab1 : (s1.data[slLabels]?).map Fin.val = some (labelsBase n m) := by
    rw [hPresS1 _ (by unfold slLabels; omega)]; exact inv.slLabelsVal
  have hSlIdx1 : (s1.data[slIdx]?).map Fin.val = some idx := by
    rw [hPresS1 _ (by unfold slIdx; omega)]; exact inv.slIdxVal
  obtain ⟨s2, k2, hk2, st2, pc2, hz2, ho2, hval2, hJ0, hJ1, hJ2, hSlot2, hBF2, hBS2, hPar2, hNext2, hPres2⟩ :=
    sweepSkewInsert_step h8 input inv1 hidx hWork hWL hBnd2 hpl2 hHit hAncF pc1
      hz1 ho1 hptr1 hSlAnc1 hSlKF1 hSlKS1
  have hWLSub : pcWriteLabel + (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
      loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
      sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]).length < code.size := by
    have hLenW : (sweepInstallTail h8 pcWriteLabel pcLoopTop).length =
        sweepInstallKeepLen h8 + 1 + (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
          [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
          loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
          sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]).length := by
      rw [sweepInstallTail_eq_parts]; simp only [List.length_append, List.length_cons, List.length_nil, hKeepLen]
    rw [hLenTot] at hSz; dsimp only [pcWriteLabel, pcWriteZero, pcKeepP] at *; omega
  have hplWL : Placed code pcWriteLabel
      (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
        [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
        sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]) :=
    sweepInstallTail_writeLabel_placed h8 (by dsimp only [pcWriteLabel, pcWriteZero]; rw [hKeepLen]; omega) hpl3
  have hScrLtJump : ∀ w, w = slY ∨ w = slLabels ∨ w = slIdx →
      w < jumpBase n m ∧ w < dictBase n m + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx ∧
      w < backFstBase n m + sRef.tables.next ∧ w < backSndBase n m + sRef.tables.next ∧
      w < parentsBase n m + sRef.tables.next := fun w hw' => by
    have := scratch_lt_orderBase (n := n) (m := m) (sl := 29) large (by decide)
    have hOrdLtAll : orderBase n m < dictBase n m ∧ orderBase n m < jumpBase n m ∧
        orderBase n m < backFstBase n m ∧ orderBase n m < backSndBase n m ∧
        orderBase n m < parentsBase n m := by
      simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase,
        candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
        rowEndBase, rowStartBase, ranksBase, orderBase]; omega
    rcases hw' with rfl | rfl | rfl
    · unfold slY; omega
    · unfold slLabels; omega
    · unfold slIdx; omega
  have hPresS2 : ∀ w, w = slY ∨ w = slLabels ∨ w = slIdx → s2.data[w]? = s1.data[w]? := fun w hw' => by
    have hLt := hScrLtJump w hw'
    dsimp only [n, m] at hLt
    rcases hPres2 w with h | h | h | h | h | h | h | h | h
    · rcases hw' with rfl | rfl | rfl
      · unfold slY slNext at h; omega
      · unfold slLabels slNext at h; omega
      · unfold slIdx slNext at h; omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact h
  obtain ⟨t, k3, hk3, st3, pc3, hz3, ho3, hLab3, hIdx3, hPres3⟩ :=
    sweepInstallTail_writeLabel_steps h8 input hWork large y.isLt hidx hLoopBnd hWLSub hplWL
      s2 pc2 hz2 ho2 hval2
      (by rw [hPresS2 _ (Or.inl rfl)]; exact hSlY1)
      (by rw [hPresS2 _ (Or.inr (Or.inl rfl))]; exact hSlLab1)
      (by rw [hPresS2 _ (Or.inr (Or.inr rfl))]; exact hSlIdx1)
  have hIdxLtAll : slIdx < jumpBase H.vertexCount H.arcCount ∧
      slIdx < dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx ∧
      slIdx < backFstBase H.vertexCount H.arcCount + sRef.tables.next ∧
      slIdx < backSndBase H.vertexCount H.arcCount + sRef.tables.next ∧
      slIdx < parentsBase H.vertexCount H.arcCount + sRef.tables.next := by
    have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
    simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase,
      candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
      rowEndBase, rowStartBase, ranksBase] at *
    unfold slIdx; omega
  have hLabNeNext : labelsBase H.vertexCount H.arcCount + y.val ≠ slNext := by
    have := scratch_lt_orderBase (n := H.vertexCount) (m := H.arcCount) (sl := 29) large (by decide)
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase,
      candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
      rowEndBase, rowStartBase, ranksBase] at *
    unfold slNext; omega
  have hPresNo3 : ∀ w, w ≠ slIdx → w ≠ labelsBase H.vertexCount H.arcCount + y.val →
      t.data[w]? = s2.data[w]? := fun w hw1 hw2 => by
    rcases hPres3 w with h | h | h
    · exact absurd h hw1
    · exact absurd h hw2
    · exact h
  have hNextSRefLe : sRef.tables.next ≤ H.vertexCount := by have := inv.sRefNextLe; omega
  have hJ0T : (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 0]?).map Fin.val = some ancNode := by
    rw [hPresNo3 _ (by omega) (by simp only [labelsBase, backSndBase, backFstBase]; omega)]; exact hJ0
  have hJ1T : (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 1]?).map Fin.val = some (F.depthOf ancNode + 1) := by
    rw [hPresNo3 _ (by omega) (by simp only [labelsBase, backSndBase, backFstBase]; omega)]; exact hJ1
  have hJ2T : (t.data[jumpBase H.vertexCount H.arcCount + 3 * sRef.tables.next + 2]?).map Fin.val = some (F.mkAppendedRecord ancNode).jump := by
    rw [hPresNo3 _ (by omega) (by simp only [labelsBase, backSndBase, backFstBase]; omega)]; exact hJ2
  have hSlotT : (t.data[dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx]?).map Fin.val =
      some sRef.tables.next := by
    have hDSLtLab : dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size + slotIdx <
        labelsBase H.vertexCount H.arcCount + y.val := by
      have := dict_size_le H dictRows large
      simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase] at *; omega
    rw [hPresNo3 _ (by omega) (by omega)]; exact hSlot2
  have hBFT : (t.data[backFstBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val = some (q.fst.val + 1) := by
    rw [hPresNo3 _ (by omega) (by simp only [labelsBase, backSndBase]; omega)]; exact hBF2
  have hBST : (t.data[backSndBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val = some q.snd.val := by
    rw [hPresNo3 _ (by omega) (by simp only [labelsBase]; omega)]; exact hBS2
  have hParT : (t.data[parentsBase H.vertexCount H.arcCount + sRef.tables.next]?).map Fin.val = some ancNode := by
    rw [hPresNo3 _ (by omega) (by simp only [parentsBase, labelsBase]; omega)]; exact hPar2
  have hNextT' : (t.data[slNext]?).map Fin.val = some (sRef.tables.next + 1) := by
    rw [hPresNo3 _ (by unfold slIdx slNext; omega) hLabNeNext.symm]
    exact hNext2
  have _ := hNode
  have hInvT : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      (F.appendLeaf rStep.measured.step.parent) rStep.state (idx + 1) t := by
    refine inv.advance_grow hidx y hStep hAlloc hq hLook hHit hWork hNextT' hIdx3
      (by rw [hrPar]; exact hJ0T) (by rw [hrPar]; exact hJ1T) (by rw [hrPar]; exact hJ2T)
      hSlotT hBFT hBST hLab3 (by rw [hrPar]; exact hParT) fun j => ?_
    by_cases hI : j = slIdx
    · exact Or.inr (Or.inr (Or.inl hI))
    by_cases hL : j = labelsBase H.vertexCount H.arcCount + y.val
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))))))
    by_cases hN : j = slNext
    · exact Or.inr (Or.inl hN)
    rw [hPresNo3 j hI hL]
    rcases hPres2 j with h | h | h | h | h | h | h | h | h
    · exact absurd h hN
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
    · rcases hPres1 j with rfl | rfl | heq1
      · exact Or.inl (by unfold slKeyFst; omega)
      · exact Or.inl (by unfold slKeySnd; omega)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (h.trans heq1)))))))))))
  exact ⟨t, k1 + k2 + k3, by omega, (st1.append st2).append st3, pc3, hz3, ho3, hInvT⟩

theorem sweepInstallBlock_reuse_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (input : Input (layout bits inputCap workCap hi hw))
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s s1 : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hidx : idx < H.vertexCount) (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcStart pcLoopTop : Nat} (hLoopBnd : pcLoopTop < code.size)
    (hSz : pcStart + (sweepInstallBlock h8 pcStart pcLoopTop).length < code.size)
    (hpl : Placed code pcStart (sweepInstallBlock h8 pcStart pcLoopTop))
    {y : Vertex H}
    {rStep : _root_.EX24.HeadResult H}
    (hStep : _root_.EX24.stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep)
    {slotIdx : Nat} (hAlloc : rStep.installed.allocated = false)
    (hNode : rStep.installed.node = sRef.tables.slotAt slotIdx)
    (hSlY : (s.data[slY]?).map Fin.val = some y.val)
    (k1 : Nat) (hk1 : k1 ≤ 150 + 17 * (OracleContract.L H.vertexCount + 1))
    (st1 : Steps code input k1 s s1)
    (pc1 : s1.pc = pcStart + (sweepPairAndDictBS h8 0 0 0 0).length +
      (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8 + 1)
    (hz1 : (reg s1 rZero).val = 0) (ho1 : (reg s1 rOne).val = 1)
    (hval1 : (reg s1 rVal).val = sRef.tables.slotAt slotIdx)
    (hPres1 : ∀ w, w = slKeyFst ∨ w = slKeySnd ∨ s1.data[w]? = s.data[w]?) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
      k ≤ 390 + 17 * (OracleContract.L H.vertexCount + 1) ∧
      Steps code input k s t ∧ t.pc = pcLoopTop ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large)
        F rStep.state (idx + 1) t := by
  let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
  let d2 := (sweepSkewInsert h8 0 0).length
  let pcKeepP := pcStart + d1 + d2
  let pcWriteLabel := pcKeepP + sweepInstallKeepLen h8 + 1
  have hLenTot : (sweepInstallBlock h8 pcStart pcLoopTop).length =
      d1 + d2 + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length :=
    sweepInstallBlock_len_parts h8 pcStart pcLoopTop
  have hKeepLen : sweepInstallKeepLen h8 = (loadScratch h8 rVal slAncNode).length + 1 := rfl
  obtain ⟨_, _, hpl3⟩ := sweepInstallBlock_slices h8 hpl
  have hPresS1 : ∀ sl, sl < 28 → s1.data[sl]? = s.data[sl]? := fun sl hsl => by
    rcases hPres1 sl with rfl | rfl | heq
    · unfold slKeyFst at hsl; omega
    · unfold slKeySnd at hsl; omega
    · exact heq
  have hWLSub : pcWriteLabel + (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
      [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
      loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
      sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]).length < code.size := by
    have hLenW : (sweepInstallTail h8 pcWriteLabel pcLoopTop).length =
        sweepInstallKeepLen h8 + 1 + (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
          [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
          loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
          sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]).length := by
      rw [sweepInstallTail_eq_parts]; simp only [List.length_append, List.length_cons, List.length_nil, hKeepLen]
    rw [hLenTot] at hSz; dsimp only [pcWriteLabel, pcKeepP] at *; omega
  have hplWL : Placed code pcWriteLabel
      (loadScratch h8 rClk slY ++ loadScratch h8 rTmp slLabels ++
        [Instr.add rTmp rTmp rClk, Instr.storeData rTmp rVal] ++
        loadScratch h8 rClk slIdx ++ [Instr.add rClk rClk rOne] ++
        sweepInitStoreScratch h8 slIdx rClk ++ [Instr.goto pcLoopTop]) :=
    sweepInstallTail_writeLabel_placed h8 (by dsimp only [pcWriteLabel]; rw [hKeepLen]; omega) hpl3
  obtain ⟨t, k2, hk2, st2, pc2, hz2, ho2, hLab2, hIdx2, hPres2⟩ :=
    sweepInstallTail_writeLabel_steps h8 input hWork large y.isLt hidx hLoopBnd hWLSub hplWL
      s1 pc1 hz1 ho1 hval1
      (by rw [hPresS1 _ (by unfold slY; omega)]; exact hSlY)
      (by rw [hPresS1 _ (by unfold slLabels; omega)]; exact inv.slLabelsVal)
      (by rw [hPresS1 _ (by unfold slIdx; omega)]; exact inv.slIdxVal)
  have hInvT := inv.advance_keep hidx y hStep hAlloc (by rw [hNode]; exact hLab2) hIdx2 fun j => by
    rcases hPres2 j with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · rcases hPres1 j with rfl | rfl | heq1
      · exact Or.inl (by unfold slKeyFst; omega)
      · exact Or.inl (by unfold slKeySnd; omega)
      · exact Or.inr (Or.inr (Or.inr (h.trans heq1)))
  exact ⟨t, k1 + k2, by omega, st1.append st2, pc2, hz2, ho2, hInvT⟩

theorem sweepInstallBlock_step {bits inputCap workCap : Nat}
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
    (hidx : idx < H.vertexCount) (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcStart pcLoopTop : Nat}
    (hLoopBnd : pcLoopTop < code.size)
    (hSz : pcStart + (sweepInstallBlock h8 pcStart pcLoopTop).length < code.size)
    (hpl : Placed code pcStart (sweepInstallBlock h8 pcStart pcLoopTop))
    {y m_y : Vertex H} (hyNe : y ≠ H.root)
    (hNoRoot : H.hasQuotientArcBool H.root y = false)
    (hMax : maxByRank rank (preds H y) = some m_y)
    {rowLo rowHi : Nat} (hLoHi : rowLo < rowHi) (hRHm : rowHi ≤ H.arcCount)
    (hDiff : rowHi - rowLo = (rows.row y).length)
    (hPB : ∀ t' : Fin (rows.row y).length,
      (s.data[predBufBase H.vertexCount H.arcCount + rowLo + t'.val]?).map Fin.val =
        some ((rows.row y)[t'.val]'t'.isLt).val)
    (hpc : s.pc = pcStart) (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hSlAnc : (s.data[slAncNode]?).map Fin.val = some
      (F.ancestorAtDepth (sRef.labelAt m_y.val)
        (PaperB.ForestHead.measuredLog
          (fun d => PaperB.ForestHead.probe (selectors (orderedConfig dictRows large) sRef) (rows.row y) m_y d)
          (F.depthOf (sRef.labelAt m_y.val) + 1)).cut))
    (hSlY : (s.data[slY]?).map Fin.val = some y.val)
    (hSlRL : (s.data[slRowLo]?).map Fin.val = some rowLo)
    (hSlRH : (s.data[slRowHi]?).map Fin.val = some rowHi) :
    ∃ rStep : _root_.EX24.HeadResult H,
      _root_.EX24.stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep ∧
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 390 + 17 * (OracleContract.L H.vertexCount + 1) ∧
        Steps code input k s t ∧ t.pc = pcLoopTop ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
          (order := order) (size_order := size_order) (rank := rank) (large := large)
          (if rStep.installed.allocated then F.appendLeaf rStep.measured.step.parent else F)
          rStep.state (idx + 1) t := by
  let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
  let d2 := (sweepSkewInsert h8 0 0).length
  let pcKeepP := pcStart + d1 + d2
  let pcWriteZero := pcKeepP + sweepInstallKeepLen h8
  let pcWriteLabel := pcWriteZero + 1
  have hd1 : (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length = d1 :=
    sweepPairAndDictBS_length h8 pcStart pcKeepP pcWriteZero pcWriteLabel
  have hd2 : (sweepSkewInsert h8 (pcStart + d1) pcWriteLabel).length = d2 :=
    sweepSkewInsert_length h8 (pcStart + d1) pcWriteLabel
  have hLenTot : (sweepInstallBlock h8 pcStart pcLoopTop).length =
      d1 + d2 + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length :=
    sweepInstallBlock_len_parts h8 pcStart pcLoopTop
  have hKeepLen : sweepInstallKeepLen h8 = (loadScratch h8 rVal slAncNode).length + 1 := rfl
  have hTailLen : (sweepInstallTail h8 pcWriteLabel pcLoopTop).length ≥
      (loadScratch h8 rVal slAncNode).length + 2 := by
    rw [sweepInstallTail_eq_parts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hKP : pcKeepP < code.size := by dsimp only [pcKeepP]; rw [hLenTot] at hSz; omega
  have hWZ : pcWriteZero < code.size := by dsimp only [pcWriteZero, pcKeepP]; rw [hKeepLen]; rw [hLenTot] at hSz; omega
  have hWL : pcWriteLabel < code.size := by dsimp only [pcWriteLabel, pcWriteZero, pcKeepP]; rw [hKeepLen]; rw [hLenTot] at hSz; omega
  have hBnd1 : pcStart + (sweepPairAndDictBS h8 pcStart pcKeepP pcWriteZero pcWriteLabel).length < code.size := by
    rw [hd1]; rw [hLenTot] at hSz; omega
  have hBnd3 : pcKeepP + (sweepInstallTail h8 pcWriteLabel pcLoopTop).length < code.size := by
    dsimp only [pcKeepP]; rw [hLenTot] at hSz; omega
  obtain ⟨hpl1, _, hpl3⟩ := sweepInstallBlock_slices h8 hpl
  obtain ⟨_, hAncF, rStep, hStep, hrPar, hrPair, hKeySome, hKeyNone⟩ :=
    sweep_active_step_spec inv hidx hyNe hNoRoot hMax
  let ancNode := F.ancestorAtDepth (sRef.labelAt m_y.val)
    (PaperB.ForestHead.measuredLog
      (fun d => PaperB.ForestHead.probe (selectors (orderedConfig dictRows large) sRef) (rows.row y) m_y d)
      (F.depthOf (sRef.labelAt m_y.val) + 1)).cut
  have hPair := sweepPairAndDictBS_step h8 input inv hWork hKP hWZ hWL hBnd1 hpl1
    hNoRoot hLoHi hRHm hDiff hPB hpc hz ho hSlRL hSlRH
  by_cases hDeg2 : (rows.row y).length = 2
  · rw [ite_eq_left hDeg2] at hPair
    obtain ⟨q, slotIdx, hHit, _, hKeyD, hLook, _, hPairBranch⟩ := hPair
    have hKS := hKeySome q slotIdx hKeyD hLook
    by_cases hSlotZ : sRef.tables.slotAt slotIdx = 0
    · rw [ite_eq_left hSlotZ] at hPairBranch
      rw [ite_eq_left hSlotZ] at hKS
      obtain ⟨s1, k1, hk1, st1, pc1, hz1, ho1, hptr1, hSlKF1, hSlKS1, hPres1⟩ := hPairBranch
      have hAlloc : rStep.installed.allocated = true := hKS.1
      have hNode : rStep.installed.node = sRef.tables.next := hKS.2
      have hq : rStep.measured.step.newPair = some q := hrPair.trans hKeyD
      obtain ⟨t, k, hk, st, pcT, hzT, hoT, hInvT⟩ :=
        sweepInstallBlock_grow_step h8 input inv hidx hWork hLoopBnd hSz hpl ancNode hAncF
          hStep hrPar hKeyD hq hLook hHit hAlloc hNode hSlAnc hSlY k1 hk1 st1 (by rw [pc1, hd1])
          hz1 ho1 hptr1 hSlKF1 hSlKS1 hPres1
      refine ⟨rStep, hStep, t, k, hk, st, pcT, hzT, hoT, ?_⟩
      simpa only [hAlloc, ↓reduceIte] using hInvT
    · rw [ite_eq_right hSlotZ] at hPairBranch
      rw [ite_eq_right hSlotZ] at hKS
      obtain ⟨s1, k1, hk1, st1, pc1, hz1, ho1, hval1, hPres1⟩ := hPairBranch
      have hAlloc : rStep.installed.allocated = false := hKS.1
      have hNode : rStep.installed.node = sRef.tables.slotAt slotIdx := hKS.2
      obtain ⟨t, k, hk, st, pcT, hzT, hoT, hInvT⟩ :=
        sweepInstallBlock_reuse_step h8 input inv hidx hWork hLoopBnd hSz hpl
          hStep hAlloc hNode hSlY k1 hk1 st1 pc1 hz1 ho1 hval1 hPres1
      refine ⟨rStep, hStep, t, k, hk, st, pcT, hzT, hoT, ?_⟩
      simpa only [hAlloc, Bool.false_eq_true, ↓reduceIte] using hInvT
  · rw [ite_eq_right hDeg2] at hPair
    obtain ⟨hKeyRNone, s1, k1, hk1, st1, pc1, hz1, ho1, hd1⟩ := hPair
    have hKeyDNone : PaperB.ForestHead.preparedKey H (dictRows.row y) = none := by
      rw [PaperB.ForestHead.preparedKey_eq_candidate y _ (dictRows.spec y),
        ← PaperB.ForestHead.preparedKey_eq_candidate y _ (rows.spec y)]
      exact hKeyRNone
    have hAlloc : rStep.installed.allocated = false := (hKeyNone hKeyDNone).1
    have hNode : rStep.installed.node = ancNode := (hKeyNone hKeyDNone).2
    have hWLKeep : pcWriteLabel = pcKeepP + (loadScratch h8 rVal slAncNode).length + 2 := by
      dsimp only [pcWriteLabel, pcWriteZero]; rw [hKeepLen]; omega
    obtain ⟨t, k2, hk2, st2, pc2, hz2, ho2, hLab2, hIdx2, hPres2⟩ :=
      sweepInstallTail_keep_steps h8 input hWork large y.isLt hidx hLoopBnd hWLKeep hBnd3 hpl3
        s1 pc1 hz1 ho1
        (by rw [hd1]; exact hSlAnc) (by rw [hd1]; exact hSlY)
        (by rw [hd1]; exact inv.slLabelsVal) (by rw [hd1]; exact inv.slIdxVal)
    have hInvT := inv.advance_keep hidx y hStep hAlloc (by rw [hNode]; exact hLab2) hIdx2 fun j => by
      rcases hPres2 j with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (h.trans (congrArg (·[j]?) hd1))))
    refine ⟨rStep, hStep, t, k1 + k2, by omega, st1.append st2, pc2, hz2, ho2, ?_⟩
    simpa only [hAlloc, Bool.false_eq_true, ↓reduceIte] using hInvT

theorem sweep_stopped_step_spec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s)
    (hidx : idx < H.vertexCount)
    {y : Vertex H}
    (hStop : y = H.root ∨ rows.row y = [] ∨ H.hasQuotientArcBool H.root y = true) :
    ∃ rStep : _root_.EX24.HeadResult H,
      _root_.EX24.stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep ∧
      rStep.installed.allocated = false ∧ rStep.installed.node = 0 := by
  let c := orderedConfig dictRows large
  let S := selectors c sRef
  have hrInj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
    fun h => distinctRanks_of_stage1 inv.stage1 h
  have hRunPrep : PaperB.ForestHead.runPrepared S rank y (dictRows.row y) =
      PaperB.ForestHead.runHead S rank y (dictRows.row y) :=
    PaperB.ForestHead.runPrepared_eq_runHead S rank y (dictRows.row y) (dictRows.spec y) hrInj
  have hStopped : PaperB.ForestHead.runHead S rank y (dictRows.row y) =
      PaperB.ForestHead.stopped (H := H) := by
    rcases hStop with rfl | hEmpty | hRootArc
    · simp [PaperB.ForestHead.runHead]
    · have hPredsEmpty : preds H y = [] := by
        cases hp : preds H y with
        | nil => rfl
        | cons u us =>
          have huMem : u ∈ preds H y := by rw [hp]; simp
          have huRow : u ∈ rows.row y :=
            ((rows.spec y).cover u).mpr ((mem_preds_iff H y u).mp huMem)
          rw [hEmpty] at huRow
          cases huRow
      by_cases hyR : y = H.root
      · simp [PaperB.ForestHead.runHead, hyR]
      · by_cases hArc : H.hasQuotientArcBool H.root y = true
        · simp [PaperB.ForestHead.runHead, hyR, hArc]
        · simp [PaperB.ForestHead.runHead, hyR, hArc, hPredsEmpty, maxByRank]
    · by_cases hyR : y = H.root
      · simp [PaperB.ForestHead.runHead, hyR]
      · simp [PaperB.ForestHead.runHead, hyR, hRootArc]
  have hParentZero : (PaperB.ForestHead.runPrepared S rank y (dictRows.row y)).step.parent = 0 := by
    rw [hRunPrep, hStopped]; rfl
  have hPairNone : (PaperB.ForestHead.runPrepared S rank y (dictRows.row y)).step.newPair = none := by
    rw [hRunPrep, hStopped]; rfl
  have hZeroNext : 0 < sRef.tables.next := by
    rw [← inv.grounded.size_eq]
    exact Nat.lt_of_le_of_lt (Nat.zero_le _) (inv.grounded.size_eq ▸ inv.labelsLt y)
  have hStepExists : ∃ rStep, _root_.EX24.stepPrepared c sRef rank y (dictRows.row y) = some rStep := by
    refine PaperB.ForestDictionary.stepPrepared_dictionary_exists dictRows (hd := rfl) hrInj inv.grounded
      (by change y.val < sRef.labels.size; rw [inv.sRefLabelsSize]; exact y.isLt)
      (by rw [hParentZero]; exact hZeroNext)
      (fun k hk => by
        obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hk
        exact (PaperB.PairLookup.lookup_member_iff c.dict k c.sorted).mpr
          ⟨i, by simpa only [Array.length_toList] using hi, by simpa only [Array.getElem_toList] using heq⟩)
      (fun k i hk hi _ => by
        rw [inv.grounded.back_size]
        change sRef.tables.next < (PaperB.Jumps.ConcreteInit.region H.vertexCount).maxNodes + 1
        simp only [PaperB.Jumps.ConcreteInit.region]
        have := inv.sRefNextLe; omega)
  obtain ⟨rStep, hStep⟩ := hStepExists
  obtain ⟨hm, hInst, _, _, _⟩ := PaperB.ForestDictionary.stepPrepared_dictionary_parts dictRows rfl hrInj hStep
  have hrPar : rStep.measured.step.parent = 0 := by rw [hm]; exact hParentZero
  have hrPair : rStep.measured.step.newPair = none := by rw [hm]; exact hPairNone
  have hParLt : rStep.measured.step.parent < sRef.tables.next := by rw [hrPar]; exact hZeroNext
  simp only [_root_.EX24.install, ite_eq_left hParLt, hrPair, Option.some.injEq] at hInst
  exact ⟨rStep, hStep, by rw [← hInst]; rfl, by rw [← hInst, hrPar]; rfl⟩


end SweepLoopExec

end PaperB.RamForestProgram.Sweep
