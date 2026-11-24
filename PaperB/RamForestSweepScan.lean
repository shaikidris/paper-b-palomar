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

private def sweepHeadCheck {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (pcHalt : Nat) :
    List (Instr bits 15) :=
  [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩] ++
  loadScratch h8 rClk slIdx ++
  loadScratch h8 rVal slN ++
  [.branchLt rClk rVal (2 + (loadScratch h8 rClk slIdx).length + (loadScratch h8 rVal slN).length + 1) pcHalt]

private def sweepHeadY {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (pcCheck pcWriteZero : Nat) :
    List (Instr bits 15) :=
  let p5 := loadScratch h8 rTmp slOrder ++ [.add rTmp rTmp rClk, .loadData rVal rTmp]
  let p6 := sweepInitStoreScratch h8 slY rVal
  let p7 := loadScratch h8 rTmp slRoot
  let pcNotRoot := pcCheck + p5.length + p6.length + p7.length + 2
  p5 ++ p6 ++ p7 ++
  [.branchLt rVal rTmp pcNotRoot (pcNotRoot - 1), .branchLt rTmp rVal pcNotRoot pcWriteZero]

private def sweepHeadRows {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (pcNotRoot pcWriteZero : Nat) :
    List (Instr bits 15) :=
  let p9 := loadScratch h8 rTmp slRowStart ++ [.add rTmp rTmp rVal, .loadData rStack rTmp]
  let p10 := sweepInitStoreScratch h8 slRowLo rStack
  let p11 := loadScratch h8 rTmp slRowEnd ++ [.add rTmp rTmp rVal, .loadData rRem rTmp]
  let p12 := sweepInitStoreScratch h8 slRowHi rRem
  let pcEnd := pcNotRoot + p9.length + p10.length + p11.length + p12.length + 1
  p9 ++ p10 ++ p11 ++ p12 ++ [.branchLt rStack rRem pcEnd pcWriteZero]

def sweepHeadBlock {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (pcHalt pcWriteZero : Nat) :
    List (Instr bits 15) :=
  let hc := sweepHeadCheck h8 pcHalt
  let hy := sweepHeadY h8 hc.length pcWriteZero
  hc ++ hy ++ sweepHeadRows h8 (hc.length + hy.length) pcWriteZero

theorem sweepHeadBlock_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcHalt pcWriteZero : Nat) :
    (sweepHeadBlock h8 pcHalt pcWriteZero).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepHeadBlock sweepHeadCheck sweepHeadY sweepHeadRows
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, nonHalt, Bool.and_self]

def sweepPredScanBlock {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (pcStart pcWriteZero : Nat) :
    List (Instr bits 15) :=
  let q0 : List (Instr bits 15) := [.mov rClk rStack, .mov rChild rZero, .mov rStack rZero]
  let q1 := loadScratch h8 rVal slRoot ++ loadScratch h8 rCnt slPredBuf ++ loadScratch h8 rTin slRanks
  let pcLoop := pcStart + 3 + q1.length
  let pcAfter := pcLoop + 12
  let q2 : List (Instr bits 15) :=
    [ .branchLt rClk rRem (pcLoop + 1) pcAfter,
      .add rTmp rCnt rClk,
      .loadData rPtr rTmp,
      .branchLt rPtr rVal (pcLoop + 5) (pcLoop + 4),
      .branchLt rVal rPtr (pcLoop + 5) pcWriteZero,
      .add rTmp rTin rPtr,
      .loadData rTmp rTmp,
      .branchLt rTmp rChild (pcLoop + 10) (pcLoop + 8),
      .mov rStack rPtr,
      .mov rChild rTmp,
      .add rClk rClk rOne,
      .goto pcLoop ]
  let q3 :=
    loadScratch h8 rTmp slLabels ++
    [.add rTmp rTmp rStack, .loadData rPtr rTmp] ++
    sweepInitStoreScratch h8 slMNode rPtr ++
    loadScratch h8 rTmp slJumpBase ++
    [.add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
     .loadData rVal rTmp, .add rVal rVal rOne] ++
    sweepInitStoreScratch h8 slLoBS rZero ++
    sweepInitStoreScratch h8 slHiBS rVal
  q0 ++ q1 ++ q2 ++ q3

theorem sweepPredScanBlock_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (pcStart pcWriteZero : Nat) :
    (sweepPredScanBlock h8 pcStart pcWriteZero).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepPredScanBlock
  simp only [List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, sweepInitStoreScratch_nonHalt, nonHalt, Bool.and_self]


theorem sweepHeadBlock_length {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (a b : Nat) :
    (sweepHeadBlock h8 a b).length = (sweepHeadBlock h8 0 0).length := by
  unfold sweepHeadBlock sweepHeadCheck sweepHeadY sweepHeadRows
  simp only [List.length_append, List.length_cons, List.length_nil]

theorem sweepPredScanBlock_length {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (s a : Nat) :
    (sweepPredScanBlock h8 s a).length = (sweepPredScanBlock h8 0 0).length := by
  unfold sweepPredScanBlock; simp only [List.length_append, List.length_cons, List.length_nil]


end SweepLoopProgram

section SweepLoopExec

private theorem sweepHeadCheck_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {n m pcHalt idx : Nat}
    (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = 0)
    (hpl : Placed code 0 (sweepHeadCheck h8 pcHalt))
    (hHaltBnd : pcHalt < code.size)
    (hSz : (sweepHeadCheck h8 pcHalt).length < code.size)
    (hSlIdx : (s.data[slIdx]?).map Fin.val = some idx)
    (hSlN : (s.data[slN]?).map Fin.val = some n) :
    if idx < n then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 35 ∧
        Steps code input k s t ∧
        t.pc = (sweepHeadCheck h8 pcHalt).length ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rClk).val = idx ∧
        t.data = s.data
    else
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 35 ∧
        Steps code input k s t ∧ t.pc = pcHalt ∧ t.data = s.data := by
  let p1 : List (Instr bits 15) := [.imm rZero ⟨0, by omega⟩, .imm rOne ⟨1, by omega⟩]
  let p2 := loadScratch h8 rClk slIdx
  let p3 := loadScratch h8 rVal slN
  let pcCheck := 2 + p2.length + p3.length + 1
  let p4 : List (Instr bits 15) := [.branchLt rClk rVal pcCheck pcHalt]
  have h123 : Placed code 0 ((p1 ++ p2) ++ p3) := placed_append_left hpl
  have h12 : Placed code 0 (p1 ++ p2) := placed_append_left h123
  have hpl1 : Placed code 0 p1 := placed_append_left h12
  have hpl2 : Placed code 2 p2 := placed_right_eq h12 rfl
  have hpl3 : Placed code (2 + p2.length) p3 :=
    placed_right_eq h123 (by simp only [List.length_append]; rfl)
  have hpl4 : Placed code (2 + p2.length + p3.length) p4 :=
    placed_right_eq hpl (by simp only [List.length_append]; rfl)
  have hLenEq : (sweepHeadCheck h8 pcHalt).length = 2 + p2.length + p3.length + 1 := by
    unfold sweepHeadCheck; simp only [List.length_append, List.length_cons, List.length_nil]; rfl
  have hp2Le : p2.length ≤ 12 := loadScratch_length_le h8 rClk slIdx
  have hp3Le : p3.length ≤ 12 := loadScratch_length_le h8 rVal slN
  have hSz' : 2 + p2.length + p3.length + 1 < code.size := hLenEq ▸ hSz
  have hSlIdxW : slIdx < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlNW : slN < workCap := scratch_lt_workCap30 hWork hn (by decide)
  obtain ⟨s0, st0, pc0, r0, k0, d0⟩ :=
    step_imm_at (input := input) (s := s) (placed_fetch hpl1 (i := 0) rfl hpc) (by omega)
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
    step_imm_at (input := input) (s := s0) (placed_fetch hpl1 (i := 1) rfl (by rw [pc0, hpc]))
      (by rw [pc0, hpc]; omega)
  have hone1 : (reg s1 rOne).val = 1 := by rw [r1]
  have hzero1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide), r0]
  obtain ⟨s2, st2, pc2, r2, d2, k2⟩ :=
    loadScratch_val_steps h8 rClk slIdx hSlIdxW (by decide)
      (by rw [pc1, pc0, hpc]) hpl2 (by change 2 + p2.length < code.size; omega)
      hone1 (by rw [d1, d0]; exact hSlIdx)
  have hone2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide) (by decide), hone1]
  have hzero2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide) (by decide), hzero1]
  obtain ⟨s3, st3, pc3, r3, d3, k3⟩ :=
    loadScratch_val_steps h8 rVal slN hSlNW (by decide)
      pc2 hpl3 (by change 2 + p2.length + p3.length < code.size; omega)
      hone2 (by rw [d2, d1, d0]; exact hSlN)
  have hclk3 : (reg s3 rClk).val = idx := by rw [k3 _ (by decide) (by decide), r2]
  have hone3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide) (by decide), hone2]
  have hzero3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide) (by decide), hzero2]
  have hpc3 : s3.pc = 2 + p2.length + p3.length := by rw [pc3, Nat.add_assoc]
  have hf4 : code[s3.pc]? = some (.branchLt rClk rVal pcCheck pcHalt) :=
    placed_fetch hpl4 (i := 0) rfl hpc3
  have hPre : Steps code input (2 + p2.length + p3.length) s s3 :=
    (Steps.cons st0 (Steps.cons st1 (Steps.zero _))).append (st2.append st3)
  by_cases hlt : idx < n
  · refine ite_true_branch hlt ?_
    obtain ⟨s4, st4, pc4, k4, d4⟩ :=
      step_branchLt_true hf4 (by rw [hclk3, r3]; exact hlt) hSz'
    exact ⟨s4, 2 + p2.length + p3.length + 1, by omega, hPre.append (Steps.cons st4 (Steps.zero _)),
      by rw [pc4, hLenEq], by rw [k4, hzero3], by rw [k4, hone3], by rw [k4, hclk3],
      d4.trans (d3.trans (d2.trans (d1.trans d0)))⟩
  · refine ite_false_branch hlt ?_
    have hle : (reg s3 rVal).val ≤ (reg s3 rClk).val := by rw [r3, hclk3]; omega
    obtain ⟨s4, st4, pc4, k4, d4⟩ := step_branchLt_false hf4 hle hHaltBnd
    exact ⟨s4, 2 + p2.length + p3.length + 1, by omega, hPre.append (Steps.cons st4 (Steps.zero _)),
      pc4, d4.trans (d3.trans (d2.trans (d1.trans d0)))⟩

theorem sweepHeadBlock_halt_or_branch {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {n m pcHalt pcWriteZero idx : Nat}
    (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = 0)
    (hpl : Placed code 0 (sweepHeadBlock h8 pcHalt pcWriteZero))
    (hHaltBnd : pcHalt < code.size)
    (hSz : (sweepHeadBlock h8 pcHalt pcWriteZero).length < code.size)
    (hSlIdx : (s.data[slIdx]?).map Fin.val = some idx)
    (hSlN : (s.data[slN]?).map Fin.val = some n) :
    if idx < n then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 35 ∧
        Steps code input k s t ∧
        t.pc = (sweepHeadCheck h8 pcHalt).length ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rClk).val = idx ∧
        t.data = s.data
    else
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 35 ∧
        Steps code input k s t ∧ t.pc = pcHalt ∧ t.data = s.data := by
  have hplHC : Placed code 0 (sweepHeadCheck h8 pcHalt) :=
    placed_append_left (placed_append_left hpl)
  have hLenLe : (sweepHeadCheck h8 pcHalt).length ≤ (sweepHeadBlock h8 pcHalt pcWriteZero).length := by
    unfold sweepHeadBlock; simp only [List.length_append]; omega
  exact sweepHeadCheck_steps h8 hn hWork hpc hplHC hHaltBnd (by omega) hSlIdx hSlN

private theorem sweepHeadY_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {n m pcCheck pcWriteZero orderB idx yV rootV : Nat}
    (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    (hAddr : orderB + idx < workCap)
    (hWZ : pcWriteZero < code.size)
    (hSz : pcCheck + (sweepHeadY h8 pcCheck pcWriteZero).length < code.size)
    (hpl : Placed code pcCheck (sweepHeadY h8 pcCheck pcWriteZero))
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = pcCheck)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1) (hc : (reg s rClk).val = idx)
    (hSlOrder : (s.data[slOrder]?).map Fin.val = some orderB)
    (hSlRoot : (s.data[slRoot]?).map Fin.val = some rootV)
    (hOrd : (s.data[orderB + idx]?).map Fin.val = some yV) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 50 ∧
      Steps code input k s t ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ (reg t rVal).val = yV ∧
      (t.data[slY]?).map Fin.val = some yV ∧
      (∀ j, j ≠ slY → t.data[j]? = s.data[j]?) ∧
      if yV = rootV then t.pc = pcWriteZero
      else t.pc = pcCheck + (sweepHeadY h8 pcCheck pcWriteZero).length := by
  let p5a := loadScratch h8 rTmp slOrder
  let p5 := p5a ++ [.add rTmp rTmp rClk, .loadData rVal rTmp]
  let p6 := sweepInitStoreScratch h8 slY rVal
  let p7 := loadScratch h8 rTmp slRoot
  let pcNotRoot := pcCheck + p5.length + p6.length + p7.length + 2
  let p8 : List (Instr bits 15) :=
    [.branchLt rVal rTmp pcNotRoot (pcNotRoot - 1), .branchLt rTmp rVal pcNotRoot pcWriteZero]
  have h567 : Placed code pcCheck ((p5 ++ p6) ++ p7) := placed_append_left hpl
  have h56 : Placed code pcCheck (p5 ++ p6) := placed_append_left h567
  have hpl5 : Placed code pcCheck p5 := placed_append_left h56
  have hpl5a : Placed code pcCheck p5a := placed_append_left hpl5
  have hpl5b : Placed code (pcCheck + p5a.length) [.add rTmp rTmp rClk, .loadData rVal rTmp] :=
    placed_append_right hpl5
  have hpl6 : Placed code (pcCheck + p5.length) p6 := placed_append_right h56
  have hpl7 : Placed code (pcCheck + p5.length + p6.length) p7 :=
    placed_right_eq h567 (by simp only [List.length_append, Nat.add_assoc])
  have hpl8 : Placed code (pcCheck + p5.length + p6.length + p7.length) p8 :=
    placed_right_eq hpl (by
      dsimp only [p5, p5a, p6, p7]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc])
  have hLenEq : (sweepHeadY h8 pcCheck pcWriteZero).length = p5.length + p6.length + p7.length + 2 := by
    unfold sweepHeadY; simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]; rfl
  have hp5aLe : p5a.length ≤ 12 := loadScratch_length_le h8 rTmp slOrder
  have hp5aEq : (loadScratch h8 rTmp slOrder).length = p5a.length := rfl
  have hp5Len : p5.length = p5a.length + 2 := by simp [p5]
  have hp6Le : p6.length ≤ 12 := storeScratch_length_le h8 slY rVal
  have hp6Eq : (sweepInitStoreScratch h8 slY rVal).length = p6.length := rfl
  have hp7Le : p7.length ≤ 12 := loadScratch_length_le h8 rTmp slRoot
  have hp7Eq : (loadScratch h8 rTmp slRoot).length = p7.length := rfl
  have hSz' : pcCheck + p5.length + p6.length + p7.length + 2 < code.size := by
    rw [hLenEq] at hSz; omega
  have hBndAll : pcNotRoot < code.size := hSz'
  have hSlOrdW : slOrder < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlYW : slY < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlRootW : slRoot < workCap := scratch_lt_workCap30 hWork hn (by decide)
  obtain ⟨s5a, st5a, pc5a, r5a, d5a, k5a⟩ :=
    loadScratch_val_steps h8 rTmp slOrder hSlOrdW (by decide)
      hpc hpl5a (by change pcCheck + p5a.length < code.size; omega) ho hSlOrder
  rw [hp5aEq] at pc5a
  have hone5a : (reg s5a rOne).val = 1 := by rw [k5a _ (by decide) (by decide), ho]
  have hzero5a : (reg s5a rZero).val = 0 := by rw [k5a _ (by decide) (by decide), hz]
  have hclk5a : (reg s5a rClk).val = idx := by rw [k5a _ (by decide) (by decide), hc]
  obtain ⟨s5b, st5b, pc5b, r5b, k5b, d5b⟩ :=
    step_add15_at (input := input) (s := s5a) (placed_fetch hpl5b (i := 0) rfl pc5a)
      (by rw [pc5a]; omega)
  have hrTmp5b : (reg s5b rTmp).val = orderB + idx := by
    rw [r5b, PaperB.WordOps.add_no_wrap _ _ (by rw [r5a, hclk5a]; exact Nat.lt_of_lt_of_le hAddr hw),
      r5a, hclk5a]
  obtain ⟨s5c, st5c, pc5c, r5c, k5c, d5c⟩ :=
    step_loadData_reg (placed_fetch hpl5b (i := 1) rfl (by rw [pc5b, pc5a]))
      (by rw [pc5b, pc5a]; omega) (by rw [hrTmp5b]; exact hAddr)
      (by rw [d5b, d5a, hrTmp5b]; exact hOrd)
  have hone5c : (reg s5c rOne).val = 1 := by rw [k5c _ (by decide), k5b _ (by decide), hone5a]
  have hzero5c : (reg s5c rZero).val = 0 := by rw [k5c _ (by decide), k5b _ (by decide), hzero5a]
  have st5 : Steps code input p5.length s s5c := by
    rw [hp5Len]; exact st5a.append (Steps.cons st5b (Steps.cons st5c (Steps.zero _)))
  have hpc5c : s5c.pc = pcCheck + p5.length := by rw [pc5c, pc5b, pc5a, hp5Len]; omega
  obtain ⟨s6, st6, pc6, ySl6, fr6, k6⟩ :=
    storeScratch_val_steps h8 slY rVal (by decide) (by decide) hSlYW
      hpc5c hpl6 (by change pcCheck + p5.length + p6.length < code.size; omega) hone5c
  rw [hp6Eq] at pc6
  have hySl6 : (s6.data[slY]?).map Fin.val = some yV := by rw [ySl6, r5c]
  have hfr6 : ∀ j, j ≠ slY → s6.data[j]? = s.data[j]? := fun j hj => by
    rw [fr6 j hj, d5c, d5b, d5a]
  have hval6 : (reg s6 rVal).val = yV := by rw [k6 _ (by decide), r5c]
  have hone6 : (reg s6 rOne).val = 1 := by rw [k6 _ (by decide), hone5c]
  have hzero6 : (reg s6 rZero).val = 0 := by rw [k6 _ (by decide), hzero5c]
  obtain ⟨s7, st7, pc7, r7, d7, k7⟩ :=
    loadScratch_val_steps h8 rTmp slRoot hSlRootW (by decide)
      (by rw [pc6, Nat.add_assoc]) hpl7
      (by change pcCheck + p5.length + p6.length + p7.length < code.size; omega) hone6
      (by rw [hfr6 slRoot (by decide)]; exact hSlRoot)
  rw [hp7Eq] at pc7
  have hval7 : (reg s7 rVal).val = yV := by rw [k7 _ (by decide) (by decide), hval6]
  have hone7 : (reg s7 rOne).val = 1 := by rw [k7 _ (by decide) (by decide), hone6]
  have hzero7 : (reg s7 rZero).val = 0 := by rw [k7 _ (by decide) (by decide), hzero6]
  have hySl7 : (s7.data[slY]?).map Fin.val = some yV := by rw [d7]; exact hySl6
  have hfr7 : ∀ j, j ≠ slY → s7.data[j]? = s.data[j]? := fun j hj => by rw [d7]; exact hfr6 j hj
  have hPre : Steps code input (p5.length + p6.length + p7.length) s s7 :=
    (st5.append st6).append st7
  have hpc7 : s7.pc = pcCheck + p5.length + p6.length + p7.length := by
    rw [pc7, Nat.add_assoc]
  have hf8a : code[s7.pc]? = some (.branchLt rVal rTmp pcNotRoot (pcNotRoot - 1)) :=
    placed_fetch hpl8 (i := 0) rfl hpc7
  by_cases hlt1 : yV < rootV
  · obtain ⟨s8, st8, pc8, k8, d8⟩ :=
      step_branchLt_true hf8a (by rw [hval7, r7]; exact hlt1) hBndAll
    have hne : yV ≠ rootV := by omega
    refine ⟨s8, p5.length + p6.length + p7.length + 1, by omega, hPre.append (Steps.cons st8 (.zero _)),
      by rw [k8, hzero7], by rw [k8, hone7], by rw [k8, hval7],
      by rw [d8]; exact hySl7, fun j hj => by rw [d8]; exact hfr7 j hj, ite_false_branch hne ?_⟩
    rw [pc8, hLenEq]; dsimp [pcNotRoot]; omega
  · have hle1 : (reg s7 rTmp).val ≤ (reg s7 rVal).val := by rw [r7, hval7]; omega
    obtain ⟨s8a, st8a, pc8a, k8a, d8a⟩ :=
      step_branchLt_false hf8a hle1 (by dsimp [pcNotRoot]; omega)
    have hpc8a : s8a.pc = pcCheck + p5.length + p6.length + p7.length + 1 := by
      rw [pc8a]; dsimp [pcNotRoot]
    have hf8b : code[s8a.pc]? = some (.branchLt rTmp rVal pcNotRoot pcWriteZero) :=
      placed_fetch hpl8 (i := 1) rfl hpc8a
    have htmp8a : (reg s8a rTmp).val = rootV := by rw [k8a, r7]
    have hval8a : (reg s8a rVal).val = yV := by rw [k8a, hval7]
    by_cases hlt2 : rootV < yV
    · obtain ⟨s8b, st8b, pc8b, k8b, d8b⟩ :=
        step_branchLt_true hf8b (by rw [htmp8a, hval8a]; exact hlt2) hBndAll
      have hne : yV ≠ rootV := by omega
      refine ⟨s8b, p5.length + p6.length + p7.length + 2, by omega,
        hPre.append (Steps.cons st8a (Steps.cons st8b (.zero _))),
        by rw [k8b, k8a, hzero7], by rw [k8b, k8a, hone7], by rw [k8b, hval8a],
        by rw [d8b, d8a]; exact hySl7, fun j hj => by rw [d8b, d8a]; exact hfr7 j hj,
        ite_false_branch hne ?_⟩
      rw [pc8b, hLenEq]; dsimp [pcNotRoot]; omega
    · have hyEq : yV = rootV := by omega
      have hle2 : (reg s8a rVal).val ≤ (reg s8a rTmp).val := by rw [hval8a, htmp8a]; omega
      obtain ⟨s8b, st8b, pc8b, k8b, d8b⟩ := step_branchLt_false hf8b hle2 hWZ
      refine ⟨s8b, p5.length + p6.length + p7.length + 2, by omega,
        hPre.append (Steps.cons st8a (Steps.cons st8b (.zero _))),
        by rw [k8b, k8a, hzero7], by rw [k8b, k8a, hone7], by rw [k8b, hval8a],
        by rw [d8b, d8a]; exact hySl7, fun j hj => by rw [d8b, d8a]; exact hfr7 j hj,
        ite_true_branch hyEq pc8b⟩

private theorem sweepHeadRows_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {n m pcNotRoot pcWriteZero rsB reB yV lo hi' : Nat}
    (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    (hAddrLo : rsB + yV < workCap) (hAddrHi : reB + yV < workCap)
    (hWZ : pcWriteZero < code.size)
    (hSz : pcNotRoot + (sweepHeadRows h8 pcNotRoot pcWriteZero).length < code.size)
    (hpl : Placed code pcNotRoot (sweepHeadRows h8 pcNotRoot pcWriteZero))
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = pcNotRoot)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1) (hv : (reg s rVal).val = yV)
    (hSlRS : (s.data[slRowStart]?).map Fin.val = some rsB)
    (hSlRE : (s.data[slRowEnd]?).map Fin.val = some reB)
    (hRS : (s.data[rsB + yV]?).map Fin.val = some lo)
    (hRE : (s.data[reB + yV]?).map Fin.val = some hi')
    (hneHi1 : reB + yV ≠ slRowLo) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 60 ∧
      Steps code input k s t ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[slRowLo]?).map Fin.val = some lo ∧
      (t.data[slRowHi]?).map Fin.val = some hi' ∧
      (∀ j, j ≠ slRowLo → j ≠ slRowHi → t.data[j]? = s.data[j]?) ∧
      if lo < hi' then
        t.pc = pcNotRoot + (sweepHeadRows h8 pcNotRoot pcWriteZero).length ∧
        (reg t rStack).val = lo ∧ (reg t rRem).val = hi'
      else t.pc = pcWriteZero := by
  let p9a := loadScratch h8 rTmp slRowStart
  let p9 := p9a ++ [.add rTmp rTmp rVal, .loadData rStack rTmp]
  let p10 := sweepInitStoreScratch h8 slRowLo rStack
  let p11a := loadScratch h8 rTmp slRowEnd
  let p11 := p11a ++ [.add rTmp rTmp rVal, .loadData rRem rTmp]
  let p12 := sweepInitStoreScratch h8 slRowHi rRem
  let pcEnd := pcNotRoot + p9.length + p10.length + p11.length + p12.length + 1
  let p13 : List (Instr bits 15) := [.branchLt rStack rRem pcEnd pcWriteZero]
  have h9101112 : Placed code pcNotRoot (((p9 ++ p10) ++ p11) ++ p12) := placed_append_left hpl
  have h91011 : Placed code pcNotRoot ((p9 ++ p10) ++ p11) := placed_append_left h9101112
  have h910 : Placed code pcNotRoot (p9 ++ p10) := placed_append_left h91011
  have hpl9 : Placed code pcNotRoot p9 := placed_append_left h910
  have hpl9a : Placed code pcNotRoot p9a := placed_append_left hpl9
  have hpl9b : Placed code (pcNotRoot + p9a.length) [.add rTmp rTmp rVal, .loadData rStack rTmp] :=
    placed_append_right hpl9
  have hpl10 : Placed code (pcNotRoot + p9.length) p10 := placed_append_right h910
  have hpl11 : Placed code (pcNotRoot + p9.length + p10.length) p11 :=
    placed_right_eq h91011 (by simp only [List.length_append, Nat.add_assoc])
  have hpl11a : Placed code (pcNotRoot + p9.length + p10.length) p11a := placed_append_left hpl11
  have hpl11b : Placed code (pcNotRoot + p9.length + p10.length + p11a.length)
      [.add rTmp rTmp rVal, .loadData rRem rTmp] :=
    placed_right_eq hpl11 (by rw [Nat.add_assoc])
  have hpl12 : Placed code (pcNotRoot + p9.length + p10.length + p11.length) p12 :=
    placed_right_eq h9101112 (by simp only [List.length_append, Nat.add_assoc])
  have hpl13 : Placed code (pcNotRoot + p9.length + p10.length + p11.length + p12.length) p13 :=
    placed_right_eq hpl (by
      dsimp only [p9, p9a, p10, p11, p11a, p12]
      simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc])
  have hLenEq : (sweepHeadRows h8 pcNotRoot pcWriteZero).length =
      p9.length + p10.length + p11.length + p12.length + 1 := by
    unfold sweepHeadRows
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]; rfl
  have hp9aLe : p9a.length ≤ 12 := loadScratch_length_le h8 rTmp slRowStart
  have hp9aEq : (loadScratch h8 rTmp slRowStart).length = p9a.length := rfl
  have hp9Len : p9.length = p9a.length + 2 := by simp [p9]
  have hp10Le : p10.length ≤ 12 := storeScratch_length_le h8 slRowLo rStack
  have hp10Eq : (sweepInitStoreScratch h8 slRowLo rStack).length = p10.length := rfl
  have hp11aLe : p11a.length ≤ 12 := loadScratch_length_le h8 rTmp slRowEnd
  have hp11aEq : (loadScratch h8 rTmp slRowEnd).length = p11a.length := rfl
  have hp11Len : p11.length = p11a.length + 2 := by simp [p11]
  have hp12Le : p12.length ≤ 12 := storeScratch_length_le h8 slRowHi rRem
  have hp12Eq : (sweepInitStoreScratch h8 slRowHi rRem).length = p12.length := rfl
  have hSz' : pcNotRoot + p9.length + p10.length + p11.length + p12.length + 1 < code.size := by
    rw [hLenEq] at hSz; omega
  have hBndAll : pcEnd < code.size := hSz'
  have hSlRSW : slRowStart < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlLoW : slRowLo < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlREW : slRowEnd < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlHiW : slRowHi < workCap := scratch_lt_workCap30 hWork hn (by decide)
  obtain ⟨s9a, st9a, pc9a, r9a, d9a, k9a⟩ :=
    loadScratch_val_steps h8 rTmp slRowStart hSlRSW (by decide)
      hpc hpl9a (by change pcNotRoot + p9a.length < code.size; omega) ho hSlRS
  rw [hp9aEq] at pc9a
  have hone9a : (reg s9a rOne).val = 1 := by rw [k9a _ (by decide) (by decide), ho]
  have hzero9a : (reg s9a rZero).val = 0 := by rw [k9a _ (by decide) (by decide), hz]
  have hval9a : (reg s9a rVal).val = yV := by rw [k9a _ (by decide) (by decide), hv]
  obtain ⟨s9b, st9b, pc9b, r9b, k9b, d9b⟩ :=
    step_add15_at (input := input) (s := s9a) (placed_fetch hpl9b (i := 0) rfl pc9a)
      (by rw [pc9a]; omega)
  have hrTmp9b : (reg s9b rTmp).val = rsB + yV := by
    rw [r9b, PaperB.WordOps.add_no_wrap _ _ (by rw [r9a, hval9a]; exact Nat.lt_of_lt_of_le hAddrLo hw),
      r9a, hval9a]
  obtain ⟨s9c, st9c, pc9c, r9c, k9c, d9c⟩ :=
    step_loadData_reg (placed_fetch hpl9b (i := 1) rfl (by rw [pc9b, pc9a]))
      (by rw [pc9b, pc9a]; omega) (by rw [hrTmp9b]; exact hAddrLo)
      (by rw [d9b, d9a, hrTmp9b]; exact hRS)
  have hone9c : (reg s9c rOne).val = 1 := by rw [k9c _ (by decide), k9b _ (by decide), hone9a]
  have hzero9c : (reg s9c rZero).val = 0 := by rw [k9c _ (by decide), k9b _ (by decide), hzero9a]
  have hval9c : (reg s9c rVal).val = yV := by rw [k9c _ (by decide), k9b _ (by decide), hval9a]
  have st9 : Steps code input p9.length s s9c := by
    rw [hp9Len]; exact st9a.append (Steps.cons st9b (Steps.cons st9c (Steps.zero _)))
  have hpc9c : s9c.pc = pcNotRoot + p9.length := by rw [pc9c, pc9b, pc9a, hp9Len]; omega
  obtain ⟨s10, st10, pc10, loSl10, fr10, k10⟩ :=
    storeScratch_val_steps h8 slRowLo rStack (by decide) (by decide) hSlLoW
      hpc9c hpl10 (by change pcNotRoot + p9.length + p10.length < code.size; omega) hone9c
  rw [hp10Eq] at pc10
  have hLo10 : (s10.data[slRowLo]?).map Fin.val = some lo := by rw [loSl10, r9c]
  have hfr10 : ∀ j, j ≠ slRowLo → s10.data[j]? = s.data[j]? := fun j hj => by
    rw [fr10 j hj, d9c, d9b, d9a]
  have hstk10 : (reg s10 rStack).val = lo := by rw [k10 _ (by decide), r9c]
  have hone10 : (reg s10 rOne).val = 1 := by rw [k10 _ (by decide), hone9c]
  have hzero10 : (reg s10 rZero).val = 0 := by rw [k10 _ (by decide), hzero9c]
  have hval10 : (reg s10 rVal).val = yV := by rw [k10 _ (by decide), hval9c]
  obtain ⟨s11a, st11a, pc11a, r11a, d11a, k11a⟩ :=
    loadScratch_val_steps h8 rTmp slRowEnd hSlREW (by decide)
      (by rw [pc10, Nat.add_assoc]) hpl11a
      (by change pcNotRoot + p9.length + p10.length + p11a.length < code.size; omega) hone10
      (by rw [hfr10 slRowEnd (by decide)]; exact hSlRE)
  rw [hp11aEq] at pc11a
  have hone11a : (reg s11a rOne).val = 1 := by rw [k11a _ (by decide) (by decide), hone10]
  have hzero11a : (reg s11a rZero).val = 0 := by rw [k11a _ (by decide) (by decide), hzero10]
  have hstk11a : (reg s11a rStack).val = lo := by rw [k11a _ (by decide) (by decide), hstk10]
  have hval11a : (reg s11a rVal).val = yV := by rw [k11a _ (by decide) (by decide), hval10]
  obtain ⟨s11b, st11b, pc11b, r11b, k11b, d11b⟩ :=
    step_add15_at (input := input) (s := s11a) (placed_fetch hpl11b (i := 0) rfl pc11a)
      (by rw [pc11a]; omega)
  have hrTmp11b : (reg s11b rTmp).val = reB + yV := by
    rw [r11b, PaperB.WordOps.add_no_wrap _ _ (by rw [r11a, hval11a]; exact Nat.lt_of_lt_of_le hAddrHi hw),
      r11a, hval11a]
  obtain ⟨s11c, st11c, pc11c, r11c, k11c, d11c⟩ :=
    step_loadData_reg (placed_fetch hpl11b (i := 1) rfl (by rw [pc11b, pc11a]))
      (by rw [pc11b, pc11a]; omega) (by rw [hrTmp11b]; exact hAddrHi)
      (by rw [d11b, d11a, hrTmp11b, hfr10 (reB + yV) hneHi1]; exact hRE)
  have hone11c : (reg s11c rOne).val = 1 := by rw [k11c _ (by decide), k11b _ (by decide), hone11a]
  have hzero11c : (reg s11c rZero).val = 0 := by rw [k11c _ (by decide), k11b _ (by decide), hzero11a]
  have hstk11c : (reg s11c rStack).val = lo := by rw [k11c _ (by decide), k11b _ (by decide), hstk11a]
  have st11 : Steps code input p11.length s10 s11c := by
    rw [hp11Len]; exact st11a.append (Steps.cons st11b (Steps.cons st11c (.zero _)))
  have hpc11c : s11c.pc = pcNotRoot + p9.length + p10.length + p11.length := by
    rw [pc11c, pc11b, pc11a, hp11Len]; omega
  obtain ⟨s12, st12, pc12, hiSl12, fr12, k12⟩ :=
    storeScratch_val_steps h8 slRowHi rRem (by decide) (by decide) hSlHiW
      hpc11c hpl12 (by change pcNotRoot + p9.length + p10.length + p11.length + p12.length < code.size; omega)
      hone11c
  rw [hp12Eq] at pc12
  have hHi12 : (s12.data[slRowHi]?).map Fin.val = some hi' := by rw [hiSl12, r11c]
  have hLo12 : (s12.data[slRowLo]?).map Fin.val = some lo := by
    rw [fr12 slRowLo (by decide), d11c, d11b, d11a]; exact hLo10
  have hfr12 : ∀ j, j ≠ slRowLo → j ≠ slRowHi → s12.data[j]? = s.data[j]? := fun j h1 h2 => by
    rw [fr12 j h2, d11c, d11b, d11a]; exact hfr10 j h1
  have hstk12 : (reg s12 rStack).val = lo := by rw [k12 _ (by decide), hstk11c]
  have hrem12 : (reg s12 rRem).val = hi' := by rw [k12 _ (by decide), r11c]
  have hone12 : (reg s12 rOne).val = 1 := by rw [k12 _ (by decide), hone11c]
  have hzero12 : (reg s12 rZero).val = 0 := by rw [k12 _ (by decide), hzero11c]
  have hPre : Steps code input (p9.length + p10.length + p11.length + p12.length) s s12 :=
    ((st9.append st10).append st11).append st12
  have hpc12 : s12.pc = pcNotRoot + p9.length + p10.length + p11.length + p12.length := by
    rw [pc12, Nat.add_assoc]
  have hf13 : code[s12.pc]? = some (.branchLt rStack rRem pcEnd pcWriteZero) :=
    placed_fetch hpl13 (i := 0) rfl hpc12
  by_cases hlt : lo < hi'
  · obtain ⟨s13, st13, pc13, k13, d13⟩ :=
      step_branchLt_true hf13 (by rw [hstk12, hrem12]; exact hlt) hBndAll
    refine ⟨s13, p9.length + p10.length + p11.length + p12.length + 1, by omega,
      hPre.append (Steps.cons st13 (.zero _)),
      by rw [k13, hzero12], by rw [k13, hone12],
      by rw [d13]; exact hLo12, by rw [d13]; exact hHi12,
      fun j h1 h2 => by rw [d13]; exact hfr12 j h1 h2,
      ite_true_branch hlt ⟨by rw [pc13, hLenEq]; dsimp [pcEnd]; omega, by rw [k13, hstk12], by rw [k13, hrem12]⟩⟩
  · have hle : (reg s12 rRem).val ≤ (reg s12 rStack).val := by rw [hrem12, hstk12]; omega
    obtain ⟨s13, st13, pc13, k13, d13⟩ := step_branchLt_false hf13 hle hWZ
    refine ⟨s13, p9.length + p10.length + p11.length + p12.length + 1, by omega,
      hPre.append (Steps.cons st13 (.zero _)),
      by rw [k13, hzero12], by rw [k13, hone12],
      by rw [d13]; exact hLo12, by rw [d13]; exact hHi12,
      fun j h1 h2 => by rw [d13]; exact hfr12 j h1 h2,
      ite_false_branch hlt pc13⟩

theorem sweepHeadBlock_body_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcHalt pcWriteZero : Nat}
    (hWZ : pcWriteZero < code.size)
    (hSz : (sweepHeadBlock h8 pcHalt pcWriteZero).length < code.size)
    (hpl : Placed code 0 (sweepHeadBlock h8 pcHalt pcWriteZero))
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F sRef idx s)
    (hidx : idx < H.vertexCount)
    (hpc : s.pc = (sweepHeadCheck h8 pcHalt).length)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1) (hc : (reg s rClk).val = idx) :
    let y := orderedVertexAt order size_order ⟨idx, hidx⟩
    ∃ lo hi' : Nat,
      (s.data[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
      (s.data[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi' ∧
      lo ≤ hi' ∧ hi' ≤ H.arcCount ∧ hi' - lo = (rows.row y).length ∧
      (∀ j : Fin (rows.row y).length,
        (s.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
          some ((rows.row y)[j.val]'j.isLt).val) ∧
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 115 ∧
        Steps code input k s t ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (t.data[slY]?).map Fin.val = some y.val ∧
        (∀ j, j < 19 ∨ 22 ≤ j → t.data[j]? = s.data[j]?) ∧
        if y = H.root then t.pc = pcWriteZero
        else
          (t.data[slRowLo]?).map Fin.val = some lo ∧
          (t.data[slRowHi]?).map Fin.val = some hi' ∧
          if lo < hi' then
            t.pc = (sweepHeadBlock h8 pcHalt pcWriteZero).length ∧
            (reg t rStack).val = lo ∧ (reg t rRem).val = hi'
          else t.pc = pcWriteZero := by
  let y := orderedVertexAt order size_order ⟨idx, hidx⟩
  obtain ⟨lo, hi', hRS, hRE, hLoHi, hHiM, hDiff, hPB⟩ := inv.stage1.rows_mem y
  refine ⟨lo, hi', hRS, hRE, hLoHi, hHiM, hDiff, hPB, ?_⟩
  let n := H.vertexCount
  let m := H.arcCount
  let hcProg := sweepHeadCheck h8 pcHalt
  let hyProg := sweepHeadY h8 hcProg.length pcWriteZero
  let hrProg := sweepHeadRows h8 (hcProg.length + hyProg.length) pcWriteZero
  have hplHY : Placed code hcProg.length hyProg :=
    placed_append_right (placed_append_left hpl)
  have hplHR : Placed code (hcProg.length + hyProg.length) hrProg :=
    placed_right_eq hpl (by simp only [List.length_append]; rfl)
  have hLenBlock : (sweepHeadBlock h8 pcHalt pcWriteZero).length =
      hcProg.length + hyProg.length + hrProg.length := by
    unfold sweepHeadBlock; simp only [List.length_append]; rfl
  have hWork' : 32 * n + 7 * m + 17 ≤ workCap := by
    change rawWorkCap n m ≤ workCap at hWork
    unfold rawWorkCap at hWork; exact hWork
  have hOrdAddr : orderBase n m + idx < workCap := by
    simp only [orderBase, stampsBase, indegBase, csrArenaWords] at *; omega
  have hOrdVal : (s.data[orderBase n m + idx]?).map Fin.val = some y.val :=
    inv.stage1.order_mem ⟨idx, hidx⟩
  obtain ⟨t1, k1, hk1, st1, hz1, ho1, hv1, hySl1, hfr1, hpc1⟩ :=
    sweepHeadY_steps h8 large hWork hOrdAddr hWZ
      (by change hcProg.length + hyProg.length < code.size; omega)
      hplHY hpc hz ho hc inv.slOrderVal inv.slRootVal hOrdVal
  by_cases hyRoot : y = H.root
  · have hyV : y.val = H.root.val := by rw [hyRoot]
    have hpc1' := ite_elim_true hyV hpc1
    exact ⟨t1, k1, by omega, st1, hz1, ho1, hySl1,
      fun j hj => hfr1 j (by unfold slY at *; rcases hj with h | h <;> omega),
      ite_true_branch hyRoot hpc1'⟩
  · have hyV : y.val ≠ H.root.val := fun h => hyRoot (Fin.ext h)
    have hpc1' := ite_elim_false hyV hpc1
    have hRSAddr : rowStartBase n m + y.val < workCap := by
      have := y.isLt
      simp only [rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *; omega
    have hREAddr : rowEndBase n m + y.val < workCap := by
      have := y.isLt
      simp only [rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *; omega
    have hRElt1 : slRowLo < rowEndBase n m + y.val := by
      have := scratch_lt_orderBase (n := n) (m := m) (sl := slRowLo) large (by decide)
      simp only [rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *
      omega
    have hSlRS1 : (t1.data[slRowStart]?).map Fin.val = some (rowStartBase n m) := by
      rw [hfr1 slRowStart (by decide)]; exact inv.slRowStartVal
    have hSlRE1 : (t1.data[slRowEnd]?).map Fin.val = some (rowEndBase n m) := by
      rw [hfr1 slRowEnd (by decide)]; exact inv.slRowEndVal
    have hRS1 : (t1.data[rowStartBase n m + y.val]?).map Fin.val = some lo := by
      rw [hfr1 _ (by
        have := scratch_lt_orderBase (n := n) (m := m) (sl := slY) large (by decide)
        simp only [rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *; omega)]
      exact hRS
    have hRE1 : (t1.data[rowEndBase n m + y.val]?).map Fin.val = some hi' := by
      rw [hfr1 _ (by
        have := scratch_lt_orderBase (n := n) (m := m) (sl := slY) large (by decide)
        simp only [rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *; omega)]
      exact hRE
    obtain ⟨t2, k2, hk2, st2, hz2, ho2, hLo2, hHi2, hfr2, hpc2⟩ :=
      sweepHeadRows_steps h8 large hWork hRSAddr hREAddr hWZ
        (by change hcProg.length + hyProg.length + hrProg.length < code.size; omega)
        hplHR hpc1' hz1 ho1 hv1 hSlRS1 hSlRE1 hRS1 hRE1 (by omega)
    refine ⟨t2, k1 + k2, by omega, st1.append st2, hz2, ho2,
      by rw [hfr2 slY (by decide) (by decide)]; exact hySl1,
      fun j hj => by
        unfold slY slRowLo slRowHi at *
        rw [hfr2 j (by omega) (by omega), hfr1 j (by omega)],
      ite_false_branch hyRoot ⟨hLo2, hHi2, ?_⟩⟩
    by_cases hlt : lo < hi'
    · obtain ⟨hpc2', hstk2, hrem2⟩ := ite_elim_true hlt hpc2
      exact ite_true_branch hlt ⟨by rw [hpc2', hLenBlock], hstk2, hrem2⟩
    · exact ite_false_branch hlt (ite_elim_false hlt hpc2)

private theorem maxByRankAux_mem' {n : Nat} (rank : Fin n → Nat)
    (best : Fin n) (xs : List (Fin n)) :
    maxByRankAux rank best xs = best ∨ maxByRankAux rank best xs ∈ xs := by
  revert best
  induction xs with
  | nil => intro best; exact Or.inl rfl
  | cons x xs ih =>
    intro best
    dsimp [maxByRankAux]
    by_cases hle : rank best ≤ rank x
    · simp only [hle, ↓reduceIte]
      rcases ih x with hEq | hMem
      · exact Or.inr (List.mem_cons.mpr (Or.inl hEq))
      · exact Or.inr (List.mem_cons.mpr (Or.inr hMem))
    · simp only [hle, ↓reduceIte]
      rcases ih best with hEq | hMem
      · exact Or.inl hEq
      · exact Or.inr (List.mem_cons.mpr (Or.inr hMem))

private theorem maxByRankAux_ge' {n : Nat} (rank : Fin n → Nat)
    (best : Fin n) (xs : List (Fin n)) :
    rank best ≤ rank (maxByRankAux rank best xs) ∧
      ∀ u : Fin n, u ∈ xs → rank u ≤ rank (maxByRankAux rank best xs) := by
  revert best
  induction xs with
  | nil => intro best; exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x xs ih =>
    intro best
    dsimp [maxByRankAux]
    by_cases hle : rank best ≤ rank x
    · simp only [hle, ↓reduceIte]
      obtain ⟨hBX, hRest⟩ := ih x
      refine ⟨Nat.le_trans hle hBX, fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hTail
      · exact hBX
      · exact hRest u hTail
    · simp only [hle, ↓reduceIte]
      obtain ⟨hB, hRest⟩ := ih best
      refine ⟨hB, fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hTail
      · exact Nat.le_trans (by omega) hB
      · exact hRest u hTail

private theorem maxByRankAux_append_singleton {n : Nat} (rank : Fin n → Nat)
    (best : Fin n) (xs : List (Fin n)) (x : Fin n) :
    maxByRankAux rank best (xs ++ [x]) =
      if rank (maxByRankAux rank best xs) ≤ rank x then x else maxByRankAux rank best xs := by
  revert best
  induction xs with
  | nil => intro best; rfl
  | cons a xs ih =>
    intro best
    dsimp [maxByRankAux]
    exact ih _

private theorem maxByRank_preds_eq_row {H : LabelledQuotient}
    (rows : Rows H) (rank : Vertex H → Nat) (hInj : Function.Injective rank)
    {y : Vertex H} (u0 : Vertex H) (tl : List (Vertex H))
    (hRow : rows.row y = u0 :: tl) (hNoRoot : H.root ∉ rows.row y) :
    H.hasQuotientArcBool H.root y = false ∧
      maxByRank rank (preds H y) = some (maxByRankAux rank u0 tl) ∧
      maxByRankAux rank u0 tl ∈ rows.row y ∧
      H.HasQuotientArc (maxByRankAux rank u0 tl) y := by
  let best := maxByRankAux rank u0 tl
  have hBestMem : best ∈ rows.row y := by
    rw [hRow]
    rcases maxByRankAux_mem' rank u0 tl with h | h
    · exact List.mem_cons.mpr (Or.inl h)
    · exact List.mem_cons.mpr (Or.inr h)
  have hBestArc : H.HasQuotientArc best y := ((rows.spec y).cover best).mp hBestMem
  have hBool : H.hasQuotientArcBool H.root y = false := by
    cases hb : H.hasQuotientArcBool H.root y with
    | false => rfl
    | true =>
      have hArc := (hasQuotientArcBool_eq_true_iff H H.root y).mp hb
      exact False.elim (hNoRoot (((rows.spec y).cover H.root).mpr hArc))
  have hBestPred : best ∈ preds H y := (mem_preds_iff H y best).mpr hBestArc
  cases hps : preds H y with
  | nil =>
    rw [hps] at hBestPred; nomatch hBestPred
  | cons p0 pt =>
    let mP := maxByRankAux rank p0 pt
    have hmPMemP : mP ∈ preds H y := by
      rw [hps]
      rcases maxByRankAux_mem' rank p0 pt with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons.mpr (Or.inr h)
    have hmPRow : mP ∈ rows.row y := ((rows.spec y).cover mP).mpr ((mem_preds_iff H y mP).mp hmPMemP)
    have hGeRow : rank mP ≤ rank best := by
      rw [hRow] at hmPRow
      obtain ⟨h0, htl⟩ := maxByRankAux_ge' rank u0 tl
      rcases List.mem_cons.mp hmPRow with rfl | hTail
      · exact h0
      · exact htl mP hTail
    have hGePred : rank best ≤ rank mP := by
      rw [hps] at hBestPred
      obtain ⟨h0, hpt⟩ := maxByRankAux_ge' rank p0 pt
      rcases List.mem_cons.mp hBestPred with rfl | hTail
      · exact h0
      · exact hpt best hTail
    have hEq : mP = best := hInj (Nat.le_antisymm hGeRow hGePred)
    refine ⟨hBool, ?_, hBestMem, hBestArc⟩
    simp only [maxByRank]
    change some (maxByRankAux rank p0 pt) = some best
    rw [← hEq]

private theorem sweepPredScan_q01_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {n m pcStart lo hi' rootV pbB rkB : Nat}
    (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    (hSz : pcStart + 3 + (loadScratch h8 rVal slRoot ++ loadScratch h8 rCnt slPredBuf ++
      loadScratch h8 rTin slRanks).length < code.size)
    (hpl : Placed code pcStart ([.mov rClk rStack, .mov rChild rZero, .mov rStack rZero] ++
      (loadScratch h8 rVal slRoot ++ loadScratch h8 rCnt slPredBuf ++ loadScratch h8 rTin slRanks)))
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = pcStart)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hstk : (reg s rStack).val = lo) (hrem : (reg s rRem).val = hi')
    (hSlRoot : (s.data[slRoot]?).map Fin.val = some rootV)
    (hSlPB : (s.data[slPredBuf]?).map Fin.val = some pbB)
    (hSlRk : (s.data[slRanks]?).map Fin.val = some rkB) :
    let q1 := loadScratch h8 rVal slRoot ++ loadScratch h8 rCnt slPredBuf ++ loadScratch h8 rTin slRanks
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 40 ∧
      Steps code input k s t ∧
      t.pc = pcStart + 3 + q1.length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rClk).val = lo ∧ (reg t rRem).val = hi' ∧
      (reg t rChild).val = 0 ∧ (reg t rStack).val = 0 ∧
      (reg t rVal).val = rootV ∧ (reg t rCnt).val = pbB ∧ (reg t rTin).val = rkB ∧
      t.data = s.data := by
  let qa := loadScratch h8 rVal slRoot
  let qb := loadScratch h8 rCnt slPredBuf
  let qc := loadScratch h8 rTin slRanks
  let q0 : List (Instr bits 15) := [.mov rClk rStack, .mov rChild rZero, .mov rStack rZero]
  have hpl0 : Placed code pcStart q0 := placed_append_left hpl
  have hpl1 : Placed code (pcStart + 3) ((qa ++ qb) ++ qc) :=
    placed_right_eq hpl rfl
  have hplAB : Placed code (pcStart + 3) (qa ++ qb) := placed_append_left hpl1
  have hplA : Placed code (pcStart + 3) qa := placed_append_left hplAB
  have hplB : Placed code (pcStart + 3 + qa.length) qb := placed_append_right hplAB
  have hplC : Placed code (pcStart + 3 + qa.length + qb.length) qc :=
    placed_right_eq hpl1 (by simp only [List.length_append, Nat.add_assoc])
  have hqaLe : qa.length ≤ 12 := loadScratch_length_le h8 rVal slRoot
  have hqbLe : qb.length ≤ 12 := loadScratch_length_le h8 rCnt slPredBuf
  have hqcLe : qc.length ≤ 12 := loadScratch_length_le h8 rTin slRanks
  have hqaEq : (loadScratch h8 rVal slRoot).length = qa.length := rfl
  have hqbEq : (loadScratch h8 rCnt slPredBuf).length = qb.length := rfl
  have hqcEq : (loadScratch h8 rTin slRanks).length = qc.length := rfl
  have hq1Len : (qa ++ qb ++ qc).length = qa.length + qb.length + qc.length := by
    simp only [List.length_append]
  have hSz' : pcStart + 3 + qa.length + qb.length + qc.length < code.size := by
    rw [hq1Len] at hSz; omega
  have hSlRW : slRoot < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlPW : slPredBuf < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlRkW : slRanks < workCap := scratch_lt_workCap30 hWork hn (by decide)
  obtain ⟨s0, st0, pc0, r0, k0, d0⟩ :=
    step_mov_at (placed_fetch hpl0 (i := 0) rfl hpc) (by omega)
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
    step_mov_at (placed_fetch hpl0 (i := 1) rfl (by rw [pc0, hpc])) (by rw [pc0, hpc]; omega)
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ :=
    step_mov_at (placed_fetch hpl0 (i := 2) rfl (by rw [pc1, pc0, hpc])) (by rw [pc1, pc0, hpc]; omega)
  have hpc2 : s2.pc = pcStart + 3 := by rw [pc2, pc1, pc0, hpc]
  have hz2 : (reg s2 rZero).val = 0 := by rw [k2 _ (by decide), k1 _ (by decide), k0 _ (by decide), hz]
  have ho2 : (reg s2 rOne).val = 1 := by rw [k2 _ (by decide), k1 _ (by decide), k0 _ (by decide), ho]
  have hclk2 : (reg s2 rClk).val = lo := by rw [k2 _ (by decide), k1 _ (by decide), r0, hstk]
  have hrem2 : (reg s2 rRem).val = hi' := by rw [k2 _ (by decide), k1 _ (by decide), k0 _ (by decide), hrem]
  have hch2 : (reg s2 rChild).val = 0 := by rw [k2 _ (by decide), r1, k0 _ (by decide), hz]
  have hstk2 : (reg s2 rStack).val = 0 := by rw [r2, k1 _ (by decide), k0 _ (by decide), hz]
  have hd2 : s2.data = s.data := d2.trans (d1.trans d0)
  obtain ⟨sa, sta, pca, ra, da, ka⟩ :=
    loadScratch_val_steps h8 rVal slRoot hSlRW (by decide) hpc2 hplA
      (by change pcStart + 3 + qa.length < code.size; omega) ho2 (by rw [hd2]; exact hSlRoot)
  rw [hqaEq] at pca
  have hza : (reg sa rZero).val = 0 := by rw [ka _ (by decide) (by decide), hz2]
  have hoa : (reg sa rOne).val = 1 := by rw [ka _ (by decide) (by decide), ho2]
  have hclka : (reg sa rClk).val = lo := by rw [ka _ (by decide) (by decide), hclk2]
  have hrema : (reg sa rRem).val = hi' := by rw [ka _ (by decide) (by decide), hrem2]
  have hcha : (reg sa rChild).val = 0 := by rw [ka _ (by decide) (by decide), hch2]
  have hstka : (reg sa rStack).val = 0 := by rw [ka _ (by decide) (by decide), hstk2]
  obtain ⟨sb, stb, pcb, rb, db, kb⟩ :=
    loadScratch_val_steps h8 rCnt slPredBuf hSlPW (by decide) pca hplB
      (by change pcStart + 3 + qa.length + qb.length < code.size; omega) hoa
      (by rw [da, hd2]; exact hSlPB)
  rw [hqbEq] at pcb
  have hzb : (reg sb rZero).val = 0 := by rw [kb _ (by decide) (by decide), hza]
  have hob : (reg sb rOne).val = 1 := by rw [kb _ (by decide) (by decide), hoa]
  have hclkb : (reg sb rClk).val = lo := by rw [kb _ (by decide) (by decide), hclka]
  have hremb : (reg sb rRem).val = hi' := by rw [kb _ (by decide) (by decide), hrema]
  have hchb : (reg sb rChild).val = 0 := by rw [kb _ (by decide) (by decide), hcha]
  have hstkb : (reg sb rStack).val = 0 := by rw [kb _ (by decide) (by decide), hstka]
  have hvalb : (reg sb rVal).val = rootV := by rw [kb _ (by decide) (by decide), ra]
  obtain ⟨sc, stc, pcc, rc, dc, kc⟩ :=
    loadScratch_val_steps h8 rTin slRanks hSlRkW (by decide) pcb hplC
      (by change pcStart + 3 + qa.length + qb.length + qc.length < code.size; omega) hob
      (by rw [db, da, hd2]; exact hSlRk)
  rw [hqcEq] at pcc
  have hSt : Steps code input (3 + qa.length + qb.length + qc.length) s sc :=
    ((Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.zero _)))).append sta).append (stb.append stc)
  refine ⟨sc, _, by omega, hSt, ?_,
    by rw [kc _ (by decide) (by decide), hzb],
    by rw [kc _ (by decide) (by decide), hob],
    by rw [kc _ (by decide) (by decide), hclkb],
    by rw [kc _ (by decide) (by decide), hremb],
    by rw [kc _ (by decide) (by decide), hchb],
    by rw [kc _ (by decide) (by decide), hstkb],
    by rw [kc _ (by decide) (by decide), hvalb],
    by rw [kc _ (by decide) (by decide), rb],
    rc, dc.trans (db.trans (da.trans hd2))⟩
  rw [pcc, hq1Len]; omega

private theorem sweepPredScan_iter0_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (_h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} {rank : Vertex H → Nat}
    {pcLoop pcWriteZero pbB rkB lo hi' : Nat} {u0 : Vertex H}
    (hLoHi : lo < hi') (hHiW : hi' < workCap)
    (hAddrPB : pbB + lo < workCap)
    (hAddrRk : rkB + u0.val < workCap)
    (hWZ : pcWriteZero < code.size)
    (hSz : pcLoop + 12 < code.size)
    (hpl : Placed code pcLoop
      [ .branchLt rClk rRem (pcLoop + 1) (pcLoop + 12),
        .add rTmp rCnt rClk,
        .loadData rPtr rTmp,
        .branchLt rPtr rVal (pcLoop + 5) (pcLoop + 4),
        .branchLt rVal rPtr (pcLoop + 5) pcWriteZero,
        .add rTmp rTin rPtr,
        .loadData rTmp rTmp,
        .branchLt rTmp rChild (pcLoop + 10) (pcLoop + 8),
        .mov rStack rPtr,
        .mov rChild rTmp,
        .add rClk rClk rOne,
        .goto pcLoop ])
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = pcLoop)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hclk : (reg s rClk).val = lo) (hrem : (reg s rRem).val = hi')
    (hch : (reg s rChild).val = 0)
    (hval : (reg s rVal).val = H.root.val) (hcnt : (reg s rCnt).val = pbB)
    (htin : (reg s rTin).val = rkB)
    (hPB0 : (s.data[pbB + lo]?).map Fin.val = some u0.val)
    (hRk0 : (s.data[rkB + u0.val]?).map Fin.val = some (rank u0)) :
    if u0 = H.root then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 12 ∧
        Steps code input k s t ∧ t.pc = pcWriteZero ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data
    else
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 12 ∧
        Steps code input k s t ∧ t.pc = pcLoop ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (reg t rClk).val = lo + 1 ∧ (reg t rRem).val = hi' ∧
        (reg t rStack).val = u0.val ∧ (reg t rChild).val = rank u0 ∧
        (reg t rVal).val = H.root.val ∧ (reg t rCnt).val = pbB ∧ (reg t rTin).val = rkB ∧
        t.data = s.data := by
  obtain ⟨s0, st0, pc0, k0, d0⟩ :=
    step_branchLt_true (placed_fetch hpl (i := 0) rfl hpc) (by rw [hclk, hrem]; exact hLoHi) (by omega)
  obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
    step_add15_at (input := input) (s := s0) (placed_fetch hpl (i := 1) rfl pc0) (by rw [pc0]; omega)
  have htmp1 : (reg s1 rTmp).val = pbB + lo := by
    rw [r1, PaperB.WordOps.add_no_wrap _ _ (by rw [k0, k0, hcnt, hclk]; exact Nat.lt_of_lt_of_le hAddrPB hw),
      k0, k0, hcnt, hclk]
  obtain ⟨s2, st2, pc2, r2, k2, d2⟩ :=
    step_loadData_reg (placed_fetch hpl (i := 2) rfl (by rw [pc1, pc0]))
      (by rw [pc1, pc0]; omega) (by rw [htmp1]; exact hAddrPB)
      (by rw [d1, d0, htmp1]; exact hPB0)
  have hval2 : (reg s2 rVal).val = H.root.val := by rw [k2 _ (by decide), k1 _ (by decide), k0, hval]
  have hd2 : s2.data = s.data := d2.trans (d1.trans d0)
  by_cases hu0 : u0 = H.root
  · refine ite_true_branch hu0 ?_
    have hle1 : (reg s2 rVal).val ≤ (reg s2 rPtr).val := by rw [hval2, r2, hu0]; exact Nat.le_refl _
    obtain ⟨s3, st3, pc3, k3, d3⟩ :=
      step_branchLt_false (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0])) hle1 (by omega)
    have hle2 : (reg s3 rPtr).val ≤ (reg s3 rVal).val := by rw [k3, r2, k3, hval2, hu0]; exact Nat.le_refl _
    obtain ⟨s4, st4, pc4, k4, d4⟩ :=
      step_branchLt_false (placed_fetch hpl (i := 4) rfl (by rw [pc3])) hle2 hWZ
    exact ⟨s4, 5, by omega,
      Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4 (Steps.zero _))))),
      pc4,
      by rw [k4, k3, k2 _ (by decide), k1 _ (by decide), k0, hz],
      by rw [k4, k3, k2 _ (by decide), k1 _ (by decide), k0, ho],
      d4.trans (d3.trans hd2)⟩
  · refine ite_false_branch hu0 ?_
    have hu0V : u0.val ≠ H.root.val := fun h => hu0 (Fin.ext h)
    obtain ⟨s4, st4Pre, k4Zero, k4One, k4Clk, k4Rem, k4Ch, k4Val, k4Cnt, k4Tin, k4Ptr, d4, pc4, hk4B⟩ :
        ∃ s4 : State (layout bits inputCap workCap hi hw), ∃ k4 : Nat,
          (reg s4 rZero).val = 0 ∧ (reg s4 rOne).val = 1 ∧
          (reg s4 rClk).val = lo ∧ (reg s4 rRem).val = hi' ∧
          (reg s4 rChild).val = 0 ∧ (reg s4 rVal).val = H.root.val ∧
          (reg s4 rCnt).val = pbB ∧ (reg s4 rTin).val = rkB ∧
          (reg s4 rPtr).val = u0.val ∧
          s4.data = s.data ∧ s4.pc = pcLoop + 5 ∧
          Steps code input k4 s2 s4 ∧ k4 ≤ 2 := by
      by_cases hlt1 : u0.val < H.root.val
      · obtain ⟨s3, st3, pc3, k3, d3⟩ :=
          step_branchLt_true (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0]))
            (by rw [r2, hval2]; exact hlt1) (by omega)
        exact ⟨s3, 1,
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hz],
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, ho],
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hclk],
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hrem],
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hch],
          by rw [k3, hval2],
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hcnt],
          by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, htin],
          by rw [k3, r2], d3.trans hd2, pc3, Steps.cons st3 (Steps.zero _), by omega⟩
      · have hgt1 : H.root.val < u0.val := by omega
        obtain ⟨s3a, st3a, pc3a, k3a, d3a⟩ :=
          step_branchLt_false (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0]))
            (by rw [r2, hval2]; omega) (by omega)
        obtain ⟨s3b, st3b, pc3b, k3b, d3b⟩ :=
          step_branchLt_true (placed_fetch hpl (i := 4) rfl pc3a)
            (by rw [k3a, k3a, hval2, r2]; exact hgt1) (by omega)
        exact ⟨s3b, 2,
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hz],
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, ho],
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hclk],
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hrem],
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hch],
          by rw [k3b, k3a, hval2],
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hcnt],
          by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, htin],
          by rw [k3b, k3a, r2], d3b.trans (d3a.trans hd2), pc3b,
          Steps.cons st3a (Steps.cons st3b (Steps.zero _)), by omega⟩
    rcases hk4B with ⟨hSt4, hk4Le⟩
    obtain ⟨s5, st5, pc5, r5, k5, d5⟩ :=
      step_add15_at (input := input) (s := s4) (placed_fetch hpl (i := 5) rfl pc4) (by rw [pc4]; omega)
    have htmp5 : (reg s5 rTmp).val = rkB + u0.val := by
      rw [r5, PaperB.WordOps.add_no_wrap _ _ (by rw [k4Tin, k4Ptr]; exact Nat.lt_of_lt_of_le hAddrRk hw),
        k4Tin, k4Ptr]
    obtain ⟨s6, st6, pc6, r6, k6, d6⟩ :=
      step_loadData_reg (placed_fetch hpl (i := 6) rfl (by rw [pc5, pc4]))
        (by rw [pc5, pc4]; omega) (by rw [htmp5]; exact hAddrRk)
        (by rw [d5, d4, htmp5]; exact hRk0)
    have hch6 : (reg s6 rChild).val = 0 := by rw [k6 _ (by decide), k5 _ (by decide), k4Ch]
    have hle6 : (reg s6 rChild).val ≤ (reg s6 rTmp).val := by rw [hch6]; omega
    obtain ⟨s7, st7, pc7, k7, d7⟩ :=
      step_branchLt_false (placed_fetch hpl (i := 7) rfl (by rw [pc6, pc5, pc4])) hle6 (by omega)
    obtain ⟨s8, st8, pc8, r8, k8, d8⟩ :=
      step_mov_at (placed_fetch hpl (i := 8) rfl pc7) (by rw [pc7]; omega)
    obtain ⟨s9, st9, pc9, r9, k9, d9⟩ :=
      step_mov_at (placed_fetch hpl (i := 9) rfl (by rw [pc8, pc7])) (by rw [pc8, pc7]; omega)
    have hclk9 : (reg s9 rClk).val = lo := by
      rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Clk]
    have hone9 : (reg s9 rOne).val = 1 := by
      rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4One]
    obtain ⟨s10, st10, pc10, r10, k10, d10⟩ :=
      step_add15_at (input := input) (s := s9) (placed_fetch hpl (i := 10) rfl (by rw [pc9, pc8, pc7]))
        (by rw [pc9, pc8, pc7]; omega)
    have hclk10 : (reg s10 rClk).val = lo + 1 := by
      rw [r10, PaperB.WordOps.add_no_wrap _ _ (by rw [hclk9, hone9]; exact Nat.lt_of_lt_of_le (by omega) hw),
        hclk9, hone9]
    have st11 := step_goto_at (input := input) (placed_fetch hpl (i := 11) rfl (by rw [pc10, pc9, pc8, pc7])) (by omega)
    let s11 : State (layout bits inputCap workCap hi hw) := { s10 with pc := pcLoop }
    have hStAll : Steps code input (3 + st4Pre + 7) s s11 :=
      ((Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.zero _)))).append hSt4).append
        (Steps.cons st5 (Steps.cons st6 (Steps.cons st7 (Steps.cons st8
          (Steps.cons st9 (Steps.cons st10 (Steps.cons st11 (Steps.zero _))))))))
    refine ⟨s11, 3 + st4Pre + 7, by omega, hStAll, rfl,
      by change (reg s10 rZero).val = 0; rw [k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Zero],
      by change (reg s10 rOne).val = 1; rw [k10 _ (by decide), hone9],
      by change (reg s10 rClk).val = lo + 1; exact hclk10,
      by change (reg s10 rRem).val = hi'; rw [k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Rem],
      by change (reg s10 rStack).val = u0.val; rw [k10 _ (by decide), k9 _ (by decide), r8, k7, k6 _ (by decide), k5 _ (by decide), k4Ptr],
      by change (reg s10 rChild).val = rank u0; rw [k10 _ (by decide), r9, k8 _ (by decide), k7, r6],
      by change (reg s10 rVal).val = H.root.val; rw [k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Val],
      by change (reg s10 rCnt).val = pbB; rw [k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Cnt],
      by change (reg s10 rTin).val = rkB; rw [k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Tin],
      d10.trans (d9.trans (d8.trans (d7.trans (d6.trans (d5.trans d4)))))⟩

private theorem list_take_succ_eq {α : Type} :
    ∀ (l : List α) (i : Nat) (h : i < l.length),
      l.take (i + 1) = l.take i ++ [l[i]'h]
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, 0, _ => rfl
  | x :: xs, i + 1, h => by
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.cons_append]
    exact congrArg (x :: ·) (list_take_succ_eq xs i (by simp at h; omega))

private theorem sweepPredScan_loop_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (_h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} {rank : Vertex H → Nat}
    {pcLoop pcWriteZero pbB rkB lo hi' : Nat}
    {u0 : Vertex H} {tl : List (Vertex H)} {xs : List (Vertex H)}
    (hXsEq : xs = u0 :: tl)
    (hLen : hi' - lo = xs.length)
    (hLoLe : lo ≤ hi') (hHiW : hi' < workCap)
    (hAddrPB : ∀ j : Fin xs.length, pbB + lo + j.val < workCap)
    (hAddrRk : ∀ u : Vertex H, rkB + u.val < workCap)
    (hWZ : pcWriteZero < code.size)
    (hSz : pcLoop + 12 < code.size)
    (hpl : Placed code pcLoop
      [ .branchLt rClk rRem (pcLoop + 1) (pcLoop + 12),
        .add rTmp rCnt rClk,
        .loadData rPtr rTmp,
        .branchLt rPtr rVal (pcLoop + 5) (pcLoop + 4),
        .branchLt rVal rPtr (pcLoop + 5) pcWriteZero,
        .add rTmp rTin rPtr,
        .loadData rTmp rTmp,
        .branchLt rTmp rChild (pcLoop + 10) (pcLoop + 8),
        .mov rStack rPtr,
        .mov rChild rTmp,
        .add rClk rClk rOne,
        .goto pcLoop ])
    {s : State (layout bits inputCap workCap hi hw)}
    (hPB : ∀ j : Fin xs.length, (s.data[pbB + lo + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).val)
    (hRk : ∀ u : Vertex H, (s.data[rkB + u.val]?).map Fin.val = some (rank u)) :
    ∀ rem k : Nat, k + rem = xs.length → 1 ≤ k →
      (reg s rZero).val = 0 → (reg s rOne).val = 1 →
      (reg s rClk).val = lo + k → (reg s rRem).val = hi' →
      let best := maxByRankAux rank u0 (tl.take (k - 1))
      (reg s rStack).val = best.val → (reg s rChild).val = rank best →
      (reg s rVal).val = H.root.val → (reg s rCnt).val = pbB →
      (reg s rTin).val = rkB → s.pc = pcLoop →
      if H.root ∈ xs.drop k then
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ steps : Nat, steps ≤ 12 * rem ∧
          Steps code input steps s t ∧ t.pc = pcWriteZero ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data
      else
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ steps : Nat, steps ≤ 12 * rem + 1 ∧
          Steps code input steps s t ∧ t.pc = pcLoop + 12 ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
          (reg t rStack).val = (maxByRankAux rank u0 tl).val ∧
          t.data = s.data := by
  intro rem
  induction rem generalizing s with
  | zero =>
    intro k hkSum hk1 hz ho hclk hrem best hstk hch hval hcnt htin hpc
    have hkEq : k = xs.length := by omega
    have hDrop : xs.drop k = [] := by rw [hkEq, List.drop_length]
    have hNotMem : H.root ∉ xs.drop k := by rw [hDrop]; simp
    refine ite_false_branch hNotMem ?_
    have hle : (reg s rRem).val ≤ (reg s rClk).val := by rw [hrem, hclk]; omega
    obtain ⟨t, st, pct, kt, dt⟩ :=
      step_branchLt_false (placed_fetch hpl (i := 0) rfl hpc) hle (by omega)
    have hTakeEq : tl.take (k - 1) = tl := by
      have : tl.length = xs.length - 1 := by rw [hXsEq]; simp
      exact List.take_of_length_le (by omega)
    refine ⟨t, 1, by omega, Steps.cons st (Steps.zero _), pct,
      by rw [kt, hz], by rw [kt, ho], ?_, dt⟩
    rw [kt, hstk]; dsimp [best]; rw [hTakeEq]
  | succ rem ih =>
    intro k hkSum hk1 hz ho hclk hrem best hstk hch hval hcnt htin hpc
    have hkLt : k < xs.length := by omega
    have hCurLt : lo + k < hi' := by omega
    have hDropEq : xs.drop k = (xs[k]'hkLt) :: xs.drop (k + 1) := List.drop_eq_getElem_cons hkLt
    let u := xs[k]'hkLt
    have hAddrPBk : pbB + (lo + k) < workCap := by
      have h' := hAddrPB ⟨k, hkLt⟩; dsimp at h'; omega
    have hPBk : (s.data[pbB + (lo + k)]?).map Fin.val = some u.val := by
      have := hPB ⟨k, hkLt⟩; rwa [← Nat.add_assoc]
    obtain ⟨s0, st0, pc0, k0, d0⟩ :=
      step_branchLt_true (placed_fetch hpl (i := 0) rfl hpc) (by rw [hclk, hrem]; exact hCurLt) (by omega)
    obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
      step_add15_at (input := input) (s := s0) (placed_fetch hpl (i := 1) rfl pc0) (by rw [pc0]; omega)
    have htmp1 : (reg s1 rTmp).val = pbB + (lo + k) := by
      rw [r1, PaperB.WordOps.add_no_wrap _ _ (by rw [k0, k0, hcnt, hclk]; exact Nat.lt_of_lt_of_le hAddrPBk hw),
        k0, k0, hcnt, hclk]
    obtain ⟨s2, st2, pc2, r2, k2, d2⟩ :=
      step_loadData_reg (placed_fetch hpl (i := 2) rfl (by rw [pc1, pc0]))
        (by rw [pc1, pc0]; omega) (by rw [htmp1]; exact hAddrPBk)
        (by rw [d1, d0, htmp1]; exact hPBk)
    have hval2 : (reg s2 rVal).val = H.root.val := by rw [k2 _ (by decide), k1 _ (by decide), k0, hval]
    have hd2 : s2.data = s.data := d2.trans (d1.trans d0)
    by_cases huRoot : u = H.root
    · have hMem : H.root ∈ xs.drop k := by rw [hDropEq]; exact List.mem_cons.mpr (Or.inl huRoot.symm)
      refine ite_true_branch hMem ?_
      have hle1 : (reg s2 rVal).val ≤ (reg s2 rPtr).val := by rw [hval2, r2, huRoot]; exact Nat.le_refl _
      obtain ⟨s3, st3, pc3, k3, d3⟩ :=
        step_branchLt_false (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0])) hle1 (by omega)
      have hle2 : (reg s3 rPtr).val ≤ (reg s3 rVal).val := by rw [k3, r2, k3, hval2, huRoot]; exact Nat.le_refl _
      obtain ⟨s4, st4, pc4, k4, d4⟩ :=
        step_branchLt_false (placed_fetch hpl (i := 4) rfl (by rw [pc3])) hle2 hWZ
      exact ⟨s4, 5, by omega,
        Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3 (Steps.cons st4 (Steps.zero _))))),
        pc4,
        by rw [k4, k3, k2 _ (by decide), k1 _ (by decide), k0, hz],
        by rw [k4, k3, k2 _ (by decide), k1 _ (by decide), k0, ho],
        d4.trans (d3.trans hd2)⟩
    · have huNe : u.val ≠ H.root.val := fun h => huRoot (Fin.ext h)
      obtain ⟨s4, st4Pre, k4Zero, k4One, k4Clk, k4Rem, k4Ch, k4Stk, k4Val, k4Cnt, k4Tin, k4Ptr, d4, pc4, hk4B⟩ :
          ∃ s4 : State (layout bits inputCap workCap hi hw), ∃ k4 : Nat,
            (reg s4 rZero).val = 0 ∧ (reg s4 rOne).val = 1 ∧
            (reg s4 rClk).val = lo + k ∧ (reg s4 rRem).val = hi' ∧
            (reg s4 rChild).val = rank best ∧ (reg s4 rStack).val = best.val ∧
            (reg s4 rVal).val = H.root.val ∧ (reg s4 rCnt).val = pbB ∧
            (reg s4 rTin).val = rkB ∧ (reg s4 rPtr).val = u.val ∧
            s4.data = s.data ∧ s4.pc = pcLoop + 5 ∧
            Steps code input k4 s2 s4 ∧ k4 ≤ 2 := by
        by_cases hlt1 : u.val < H.root.val
        · obtain ⟨s3, st3, pc3, k3, d3⟩ :=
            step_branchLt_true (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0]))
              (by rw [r2, hval2]; exact hlt1) (by omega)
          exact ⟨s3, 1,
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hz],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, ho],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hclk],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hrem],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hch],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hstk],
            by rw [k3, hval2],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, hcnt],
            by rw [k3, k2 _ (by decide), k1 _ (by decide), k0, htin],
            by rw [k3, r2], d3.trans hd2, pc3, Steps.cons st3 (Steps.zero _), by omega⟩
        · have hgt1 : H.root.val < u.val := by omega
          obtain ⟨s3a, st3a, pc3a, k3a, d3a⟩ :=
            step_branchLt_false (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0]))
              (by rw [r2, hval2]; omega) (by omega)
          obtain ⟨s3b, st3b, pc3b, k3b, d3b⟩ :=
            step_branchLt_true (placed_fetch hpl (i := 4) rfl pc3a)
              (by rw [k3a, k3a, hval2, r2]; exact hgt1) (by omega)
          exact ⟨s3b, 2,
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hz],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, ho],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hclk],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hrem],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hch],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hstk],
            by rw [k3b, k3a, hval2],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, hcnt],
            by rw [k3b, k3a, k2 _ (by decide), k1 _ (by decide), k0, htin],
            by rw [k3b, k3a, r2], d3b.trans (d3a.trans hd2), pc3b,
            Steps.cons st3a (Steps.cons st3b (Steps.zero _)), by omega⟩
      rcases hk4B with ⟨hSt4, hk4Le⟩
      obtain ⟨s5, st5, pc5, r5, k5, d5⟩ :=
        step_add15_at (input := input) (s := s4) (placed_fetch hpl (i := 5) rfl pc4) (by rw [pc4]; omega)
      have htmp5 : (reg s5 rTmp).val = rkB + u.val := by
        rw [r5, PaperB.WordOps.add_no_wrap _ _ (by rw [k4Tin, k4Ptr]; exact Nat.lt_of_lt_of_le (hAddrRk u) hw),
          k4Tin, k4Ptr]
      obtain ⟨s6, st6, pc6, r6, k6, d6⟩ :=
        step_loadData_reg (placed_fetch hpl (i := 6) rfl (by rw [pc5, pc4]))
          (by rw [pc5, pc4]; omega) (by rw [htmp5]; exact hAddrRk u)
          (by rw [d5, d4, htmp5]; exact hRk u)
      have hch6 : (reg s6 rChild).val = rank best := by rw [k6 _ (by decide), k5 _ (by decide), k4Ch]
      have hstk6 : (reg s6 rStack).val = best.val := by rw [k6 _ (by decide), k5 _ (by decide), k4Stk]
      have hptr6 : (reg s6 rPtr).val = u.val := by rw [k6 _ (by decide), k5 _ (by decide), k4Ptr]
      have htlLt : k - 1 < tl.length := by rw [hXsEq] at hkLt; simp at hkLt; omega
      have huEqTl : u = tl[k - 1]'htlLt := by
        dsimp [u]
        have h1 : (xs[k]'hkLt) = (u0 :: tl)[(k - 1) + 1]'(by rw [← hXsEq]; omega) := by
          congr 1; omega
        rw [h1]; rfl
      have hTakeSucc : tl.take k = tl.take (k - 1) ++ [u] := by
        have hk' : k = (k - 1) + 1 := by omega
        calc tl.take k = tl.take ((k - 1) + 1) := by rw [← hk']
          _ = tl.take (k - 1) ++ [tl[k - 1]'htlLt] := list_take_succ_eq tl (k - 1) htlLt
          _ = tl.take (k - 1) ++ [u] := by rw [huEqTl]
      have hBestNext : maxByRankAux rank u0 (tl.take k) =
          if rank best ≤ rank u then u else best := by
        rw [hTakeSucc]; exact maxByRankAux_append_singleton rank u0 (tl.take (k - 1)) u
      obtain ⟨s9, k69, st69, hz9, ho9, hclk9, hrem9, hstk9, hch9, hval9, hcnt9, htin9, hd9, hpc9, hk69⟩ :
          ∃ s9 : State (layout bits inputCap workCap hi hw), ∃ k69 : Nat,
            Steps code input k69 s6 s9 ∧
            (reg s9 rZero).val = 0 ∧ (reg s9 rOne).val = 1 ∧
            (reg s9 rClk).val = lo + k ∧ (reg s9 rRem).val = hi' ∧
            (reg s9 rStack).val = (if rank best ≤ rank u then u else best).val ∧
            (reg s9 rChild).val = rank (if rank best ≤ rank u then u else best) ∧
            (reg s9 rVal).val = H.root.val ∧ (reg s9 rCnt).val = pbB ∧
            (reg s9 rTin).val = rkB ∧ s9.data = s6.data ∧ s9.pc = pcLoop + 10 ∧ k69 ≤ 3 := by
        by_cases hltRk : rank u < rank best
        · have hNotLe : ¬ (rank best ≤ rank u) := by omega
          simp only [hNotLe, ↓reduceIte]
          obtain ⟨s7, st7, pc7, k7, d7⟩ :=
            step_branchLt_true (placed_fetch hpl (i := 7) rfl (by rw [pc6, pc5, pc4]))
              (by rw [r6, hch6]; exact hltRk) (by omega)
          exact ⟨s7, 1, Steps.cons st7 (Steps.zero _),
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4Zero],
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4One],
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4Clk],
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4Rem],
            by rw [k7, hstk6], by rw [k7, hch6],
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4Val],
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4Cnt],
            by rw [k7, k6 _ (by decide), k5 _ (by decide), k4Tin],
            d7, pc7, by omega⟩
        · have hLeRk : rank best ≤ rank u := by omega
          simp only [hLeRk, ↓reduceIte]
          obtain ⟨s7, st7, pc7, k7, d7⟩ :=
            step_branchLt_false (placed_fetch hpl (i := 7) rfl (by rw [pc6, pc5, pc4]))
              (by rw [hch6, r6]; exact hLeRk) (by omega)
          obtain ⟨s8, st8, pc8, r8, k8, d8⟩ :=
            step_mov_at (placed_fetch hpl (i := 8) rfl pc7) (by rw [pc7]; omega)
          obtain ⟨s9, st9, pc9, r9, k9, d9⟩ :=
            step_mov_at (placed_fetch hpl (i := 9) rfl (by rw [pc8, pc7])) (by rw [pc8, pc7]; omega)
          exact ⟨s9, 3, Steps.cons st7 (Steps.cons st8 (Steps.cons st9 (Steps.zero _))),
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Zero],
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4One],
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Clk],
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Rem],
            by rw [k9 _ (by decide), r8, k7, hptr6],
            by rw [r9, k8 _ (by decide), k7, r6],
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Val],
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Cnt],
            by rw [k9 _ (by decide), k8 _ (by decide), k7, k6 _ (by decide), k5 _ (by decide), k4Tin],
            d9.trans (d8.trans d7), by rw [pc9, pc8, pc7], by omega⟩
      obtain ⟨s10, st10, pc10, r10, k10, d10⟩ :=
        step_add15_at (input := input) (s := s9) (placed_fetch hpl (i := 10) rfl hpc9) (by rw [hpc9]; omega)
      have hclk10 : (reg s10 rClk).val = lo + (k + 1) := by
        rw [r10, PaperB.WordOps.add_no_wrap _ _ (by rw [hclk9, ho9]; exact Nat.lt_of_lt_of_le (by omega) hw),
          hclk9, ho9]; omega
      have st11 := step_goto_at (input := input) (placed_fetch hpl (i := 11) rfl (by rw [pc10, hpc9])) (by omega)
      let s11 : State (layout bits inputCap workCap hi hw) := { s10 with pc := pcLoop }
      have hd11 : s11.data = s.data := d10.trans (hd9.trans (d6.trans (d5.trans d4)))
      have hStepIter : Steps code input (3 + st4Pre + (2 + k69 + 2)) s s11 :=
        ((Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.zero _)))).append hSt4).append
          ((Steps.cons st5 (Steps.cons st6 (Steps.zero _))).append
            (st69.append (Steps.cons st10 (Steps.cons st11 (Steps.zero _)))))
      have hPB11 : ∀ j : Fin xs.length,
          (s11.data[pbB + lo + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).val := by
        intro j; rw [hd11]; exact hPB j
      have hRk11 : ∀ w : Vertex H, (s11.data[rkB + w.val]?).map Fin.val = some (rank w) := by
        intro w; rw [hd11]; exact hRk w
      have ihRes := ih hPB11 hRk11 (k + 1) (by omega) (by omega)
        (by change (reg s10 rZero).val = 0; rw [k10 _ (by decide), hz9])
        (by change (reg s10 rOne).val = 1; rw [k10 _ (by decide), ho9])
        (by change (reg s10 rClk).val = lo + (k + 1); exact hclk10)
        (by change (reg s10 rRem).val = hi'; rw [k10 _ (by decide), hrem9])
        (by change (reg s10 rStack).val = (maxByRankAux rank u0 (tl.take (k + 1 - 1))).val
            rw [k10 _ (by decide), Nat.add_sub_cancel, hBestNext]; exact hstk9)
        (by change (reg s10 rChild).val = rank (maxByRankAux rank u0 (tl.take (k + 1 - 1)))
            rw [k10 _ (by decide), Nat.add_sub_cancel, hBestNext]; exact hch9)
        (by change (reg s10 rVal).val = H.root.val; rw [k10 _ (by decide), hval9])
        (by change (reg s10 rCnt).val = pbB; rw [k10 _ (by decide), hcnt9])
        (by change (reg s10 rTin).val = rkB; rw [k10 _ (by decide), htin9])
        rfl
      have hMemIff : H.root ∈ xs.drop k ↔ H.root ∈ xs.drop (k + 1) := by
        rw [hDropEq, List.mem_cons]
        exact ⟨fun h => Or.elim h (fun eq => False.elim (huRoot eq.symm)) id, Or.inr⟩
      by_cases hMemNext : H.root ∈ xs.drop (k + 1)
      · have hMemCur : H.root ∈ xs.drop k := hMemIff.mpr hMemNext
        obtain ⟨t, stTail, hkTail, hStTail, hpcT, hzt, hot, hdT⟩ := ite_elim_true hMemNext ihRes
        refine ite_true_branch hMemCur ⟨t, (3 + st4Pre + (2 + k69 + 2)) + stTail, by omega,
          hStepIter.append hStTail, hpcT, hzt, hot, hdT.trans hd11⟩
      · have hNotMemCur : H.root ∉ xs.drop k := fun h => hMemNext (hMemIff.mp h)
        obtain ⟨t, stTail, hkTail, hStTail, hpcT, hzt, hot, hstkt, hdT⟩ := ite_elim_false hMemNext ihRes
        exact ite_false_branch hNotMemCur ⟨t, (3 + st4Pre + (2 + k69 + 2)) + stTail, by omega,
          hStepIter.append hStTail, hpcT, hzt, hot, hstkt, hdT.trans hd11⟩

private theorem sweepPredScan_q3_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {n m pcAfter mY mNode dM : Nat}
    (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    (hmY : mY < n) (hmNode : mNode ≤ n) (hdMLt : dM + 1 < 2 ^ bits)
    (hpl : Placed code pcAfter
      (loadScratch h8 rTmp slLabels ++ ([.add rTmp rTmp rStack, .loadData rPtr rTmp] : List (Instr bits 15)) ++
       sweepInitStoreScratch h8 slMNode rPtr ++
       loadScratch h8 rTmp slJumpBase ++
       ([.add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
         .loadData rVal rTmp, .add rVal rVal rOne] : List (Instr bits 15)) ++
       sweepInitStoreScratch h8 slLoBS rZero ++
       sweepInitStoreScratch h8 slHiBS rVal))
    (hSz : pcAfter +
      (loadScratch h8 rTmp slLabels ++ ([.add rTmp rTmp rStack, .loadData rPtr rTmp] : List (Instr bits 15)) ++
       sweepInitStoreScratch h8 slMNode rPtr ++
       loadScratch h8 rTmp slJumpBase ++
       ([.add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
         .loadData rVal rTmp, .add rVal rVal rOne] : List (Instr bits 15)) ++
       sweepInitStoreScratch h8 slLoBS rZero ++
       sweepInitStoreScratch h8 slHiBS rVal).length < code.size)
    {s : State (layout bits inputCap workCap hi hw)}
    (hpc : s.pc = pcAfter)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1) (hstk : (reg s rStack).val = mY)
    (hSlLab : (s.data[slLabels]?).map Fin.val = some (labelsBase n m))
    (hSlJB : (s.data[slJumpBase]?).map Fin.val = some (jumpBase n m))
    (hLab : (s.data[labelsBase n m + mY]?).map Fin.val = some mNode)
    (hDep : (s.data[jumpBase n m + 1 + 3 * mNode]?).map Fin.val = some dM) :
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat, k ≤ 70 ∧
      Steps code input k s t ∧
      t.pc = pcAfter +
        (loadScratch h8 rTmp slLabels ++ ([.add rTmp rTmp rStack, .loadData rPtr rTmp] : List (Instr bits 15)) ++
         sweepInitStoreScratch h8 slMNode rPtr ++
         loadScratch h8 rTmp slJumpBase ++
         ([.add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
           .loadData rVal rTmp, .add rVal rVal rOne] : List (Instr bits 15)) ++
         sweepInitStoreScratch h8 slLoBS rZero ++
         sweepInitStoreScratch h8 slHiBS rVal).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (t.data[slMNode]?).map Fin.val = some mNode ∧
      (t.data[slLoBS]?).map Fin.val = some 0 ∧
      (t.data[slHiBS]?).map Fin.val = some (dM + 1) ∧
      ∀ j, j < 22 ∨ 25 ≤ j → t.data[j]? = s.data[j]? := by
  let a1 := loadScratch h8 rTmp slLabels
  let a2 : List (Instr bits 15) := [.add rTmp rTmp rStack, .loadData rPtr rTmp]
  let a3 := sweepInitStoreScratch h8 slMNode rPtr
  let a4 := loadScratch h8 rTmp slJumpBase
  let a5 : List (Instr bits 15) :=
    [.add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
     .loadData rVal rTmp, .add rVal rVal rOne]
  let a6 := sweepInitStoreScratch h8 slLoBS rZero
  let a7 := sweepInitStoreScratch h8 slHiBS rVal
  have h16 : Placed code pcAfter ((((((a1 ++ a2) ++ a3) ++ a4) ++ a5) ++ a6)) := placed_append_left hpl
  have h15 : Placed code pcAfter (((((a1 ++ a2) ++ a3) ++ a4) ++ a5)) := placed_append_left h16
  have h14 : Placed code pcAfter ((((a1 ++ a2) ++ a3) ++ a4)) := placed_append_left h15
  have h13 : Placed code pcAfter (((a1 ++ a2) ++ a3)) := placed_append_left h14
  have h12 : Placed code pcAfter (a1 ++ a2) := placed_append_left h13
  have hpl1 : Placed code pcAfter a1 := placed_append_left h12
  have hpl2 : Placed code (pcAfter + a1.length) a2 := placed_append_right h12
  have hpl3 : Placed code (pcAfter + a1.length + 2) a3 :=
    placed_right_eq h13 (by simp only [List.length_append]; rfl)
  have hpl4 : Placed code (pcAfter + a1.length + 2 + a3.length) a4 :=
    placed_right_eq h14 (by simp only [List.length_append, Nat.add_assoc]; rfl)
  have hpl5 : Placed code (pcAfter + a1.length + 2 + a3.length + a4.length) a5 :=
    placed_right_eq h15 (by simp only [List.length_append, Nat.add_assoc]; rfl)
  have hpl6 : Placed code (pcAfter + a1.length + 2 + a3.length + a4.length + 6) a6 :=
    placed_right_eq h16 (by simp only [List.length_append, Nat.add_assoc]; rfl)
  have hpl7 : Placed code (pcAfter + a1.length + 2 + a3.length + a4.length + 6 + a6.length) a7 :=
    placed_right_eq hpl (by simp only [List.length_append, Nat.add_assoc]; rfl)
  have hTotLen : (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7).length =
      a1.length + 2 + a3.length + a4.length + 6 + a6.length + a7.length := by
    simp only [List.length_append]; rfl
  have ha1Le : a1.length ≤ 12 := loadScratch_length_le h8 rTmp slLabels
  have ha3Le : a3.length ≤ 12 := storeScratch_length_le h8 slMNode rPtr
  have ha4Le : a4.length ≤ 12 := loadScratch_length_le h8 rTmp slJumpBase
  have ha6Le : a6.length ≤ 12 := storeScratch_length_le h8 slLoBS rZero
  have ha7Le : a7.length ≤ 12 := storeScratch_length_le h8 slHiBS rVal
  have ha1Eq : (loadScratch h8 rTmp slLabels).length = a1.length := rfl
  have ha3Eq : (sweepInitStoreScratch h8 slMNode rPtr).length = a3.length := rfl
  have ha4Eq : (loadScratch h8 rTmp slJumpBase).length = a4.length := rfl
  have ha6Eq : (sweepInitStoreScratch h8 slLoBS rZero).length = a6.length := rfl
  have ha7Eq : (sweepInitStoreScratch h8 slHiBS rVal).length = a7.length := rfl
  have hSz' : pcAfter + a1.length + 2 + a3.length + a4.length + 6 + a6.length + a7.length < code.size := by
    change pcAfter + (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7).length < code.size at hSz
    rw [hTotLen] at hSz; exact hSz
  have hWork' : 32 * n + 7 * m + 17 ≤ workCap := by
    change rawWorkCap n m ≤ workCap at hWork; unfold rawWorkCap at hWork; exact hWork
  have hLabAddr : labelsBase n m + mY < workCap := by
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
      stampsBase, indegBase, csrArenaWords] at *; omega
  have hJB3Addr : jumpBase n m + 1 + 3 * mNode < workCap := by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at *; omega
  have hSlLabW : slLabels < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlMNW : slMNode < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlJBW : slJumpBase < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlLoW : slLoBS < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hSlHiW : slHiBS < workCap := scratch_lt_workCap30 hWork hn (by decide)
  have hLabNe : labelsBase n m + mY ≠ slMNode := by
    have := scratch_lt_orderBase (n := n) (m := m) (sl := slMNode) hn (by decide)
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
      stampsBase, indegBase, csrArenaWords] at *; omega
  have hDepGt : slMNode < jumpBase n m + 1 + 3 * mNode := by
    have := scratch_lt_orderBase (n := n) (m := m) (sl := slMNode) hn (by decide)
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at *; omega
  obtain ⟨s1, st1, pc1, r1, d1, k1⟩ :=
    loadScratch_val_steps h8 rTmp slLabels hSlLabW (by decide) hpc hpl1
      (by change pcAfter + a1.length < code.size; omega) ho hSlLab
  rw [ha1Eq] at pc1
  have hz1 : (reg s1 rZero).val = 0 := by rw [k1 _ (by decide) (by decide), hz]
  have ho1 : (reg s1 rOne).val = 1 := by rw [k1 _ (by decide) (by decide), ho]
  have hstk1 : (reg s1 rStack).val = mY := by rw [k1 _ (by decide) (by decide), hstk]
  obtain ⟨s2a, st2a, pc2a, r2a, k2a, d2a⟩ :=
    step_add15_at (input := input) (s := s1) (placed_fetch hpl2 (i := 0) rfl pc1) (by rw [pc1]; omega)
  have htmp2a : (reg s2a rTmp).val = labelsBase n m + mY := by
    rw [r2a, PaperB.WordOps.add_no_wrap _ _ (by rw [r1, hstk1]; exact Nat.lt_of_lt_of_le hLabAddr hw), r1, hstk1]
  obtain ⟨s2b, st2b, pc2b, r2b, k2b, d2b⟩ :=
    step_loadData_reg (placed_fetch hpl2 (i := 1) rfl (by rw [pc2a, pc1]))
      (by rw [pc2a, pc1]; omega) (by rw [htmp2a]; exact hLabAddr)
      (by rw [d2a, d1, htmp2a]; exact hLab)
  have hz2b : (reg s2b rZero).val = 0 := by rw [k2b _ (by decide), k2a _ (by decide), hz1]
  have ho2b : (reg s2b rOne).val = 1 := by rw [k2b _ (by decide), k2a _ (by decide), ho1]
  have hpc2b : s2b.pc = pcAfter + a1.length + 2 := by rw [pc2b, pc2a, pc1]
  obtain ⟨s3, st3, pc3, d3MN, fr3, k3⟩ :=
    storeScratch_val_steps h8 slMNode rPtr (by decide) (by decide) hSlMNW hpc2b hpl3
      (by change pcAfter + a1.length + 2 + a3.length < code.size; omega) ho2b
  rw [ha3Eq] at pc3
  have hz3 : (reg s3 rZero).val = 0 := by rw [k3 _ (by decide), hz2b]
  have ho3 : (reg s3 rOne).val = 1 := by rw [k3 _ (by decide), ho2b]
  have hptr3 : (reg s3 rPtr).val = mNode := by rw [k3 _ (by decide), r2b]
  have hMN3 : (s3.data[slMNode]?).map Fin.val = some mNode := by rw [d3MN, r2b]
  have hfr3 : ∀ j, j ≠ slMNode → s3.data[j]? = s.data[j]? := fun j hj => by rw [fr3 j hj, d2b, d2a, d1]
  obtain ⟨s4, st4, pc4, r4, d4, k4⟩ :=
    loadScratch_val_steps h8 rTmp slJumpBase hSlJBW (by decide) pc3 hpl4
      (by change pcAfter + a1.length + 2 + a3.length + a4.length < code.size; omega) ho3
      (by rw [hfr3 slJumpBase (by decide)]; exact hSlJB)
  rw [ha4Eq] at pc4
  have hz4 : (reg s4 rZero).val = 0 := by rw [k4 _ (by decide) (by decide), hz3]
  have ho4 : (reg s4 rOne).val = 1 := by rw [k4 _ (by decide) (by decide), ho3]
  have hptr4 : (reg s4 rPtr).val = mNode := by rw [k4 _ (by decide) (by decide), hptr3]
  obtain ⟨s5a, st5a, pc5a, r5a, k5a, d5a⟩ :=
    step_add15_at (input := input) (s := s4) (placed_fetch hpl5 (i := 0) rfl pc4) (by rw [pc4]; omega)
  have htmp5a : (reg s5a rTmp).val = jumpBase n m + mNode := by
    rw [r5a, PaperB.WordOps.add_no_wrap _ _ (by rw [r4, hptr4]; exact Nat.lt_of_lt_of_le (by omega) hw), r4, hptr4]
  have hptr5a : (reg s5a rPtr).val = mNode := by rw [k5a _ (by decide), hptr4]
  obtain ⟨s5b, st5b, pc5b, r5b, k5b, d5b⟩ :=
    step_add15_at (input := input) (s := s5a) (placed_fetch hpl5 (i := 1) rfl (by rw [pc5a, pc4]))
      (by rw [pc5a, pc4]; omega)
  have htmp5b : (reg s5b rTmp).val = jumpBase n m + 2 * mNode := by
    rw [r5b, PaperB.WordOps.add_no_wrap _ _ (by rw [htmp5a, hptr5a]; exact Nat.lt_of_lt_of_le (by omega) hw),
      htmp5a, hptr5a]; omega
  have hptr5b : (reg s5b rPtr).val = mNode := by rw [k5b _ (by decide), hptr5a]
  obtain ⟨s5c, st5c, pc5c, r5c, k5c, d5c⟩ :=
    step_add15_at (input := input) (s := s5b) (placed_fetch hpl5 (i := 2) rfl (by rw [pc5b, pc5a, pc4]))
      (by rw [pc5b, pc5a, pc4]; omega)
  have htmp5c : (reg s5c rTmp).val = jumpBase n m + 3 * mNode := by
    rw [r5c, PaperB.WordOps.add_no_wrap _ _ (by rw [htmp5b, hptr5b]; exact Nat.lt_of_lt_of_le (by omega) hw),
      htmp5b, hptr5b]; omega
  have ho5c : (reg s5c rOne).val = 1 := by
    rw [k5c _ (by decide), k5b _ (by decide), k5a _ (by decide), ho4]
  obtain ⟨s5d, st5d, pc5d, r5d, k5d, d5d⟩ :=
    step_add15_at (input := input) (s := s5c) (placed_fetch hpl5 (i := 3) rfl (by rw [pc5c, pc5b, pc5a, pc4]))
      (by rw [pc5c, pc5b, pc5a, pc4]; omega)
  have htmp5d : (reg s5d rTmp).val = jumpBase n m + 1 + 3 * mNode := by
    rw [r5d, PaperB.WordOps.add_no_wrap _ _ (by rw [htmp5c, ho5c]; exact Nat.lt_of_lt_of_le (by omega) hw),
      htmp5c, ho5c]; omega
  have ho5d : (reg s5d rOne).val = 1 := by rw [k5d _ (by decide), ho5c]
  obtain ⟨s5e, st5e, pc5e, r5e, k5e, d5e⟩ :=
    step_loadData_reg (placed_fetch hpl5 (i := 4) rfl (by rw [pc5d, pc5c, pc5b, pc5a, pc4]))
      (by rw [pc5d, pc5c, pc5b, pc5a, pc4]; omega) (by rw [htmp5d]; exact hJB3Addr)
      (by rw [d5d, d5c, d5b, d5a, d4, htmp5d, hfr3 _ (by omega)]; exact hDep)
  have ho5e : (reg s5e rOne).val = 1 := by rw [k5e _ (by decide), ho5d]
  obtain ⟨s5f, st5f, pc5f, r5f, k5f, d5f⟩ :=
    step_add15_at (input := input) (s := s5e)
      (placed_fetch hpl5 (i := 5) rfl (by rw [pc5e, pc5d, pc5c, pc5b, pc5a, pc4]))
      (by rw [pc5e, pc5d, pc5c, pc5b, pc5a, pc4]; omega)
  have hval5f : (reg s5f rVal).val = dM + 1 := by
    rw [r5f, PaperB.WordOps.add_no_wrap _ _ (by rw [r5e, ho5e]; exact hdMLt), r5e, ho5e]
  have hz5f : (reg s5f rZero).val = 0 := by
    rw [k5f _ (by decide), k5e _ (by decide), k5d _ (by decide), k5c _ (by decide),
      k5b _ (by decide), k5a _ (by decide), hz4]
  have ho5f : (reg s5f rOne).val = 1 := by rw [k5f _ (by decide), ho5e]
  have hd5f : s5f.data = s3.data := d5f.trans (d5e.trans (d5d.trans (d5c.trans (d5b.trans (d5a.trans d4)))))
  have hpc5f : s5f.pc = pcAfter + a1.length + 2 + a3.length + a4.length + 6 := by
    rw [pc5f, pc5e, pc5d, pc5c, pc5b, pc5a, pc4]
  obtain ⟨s6, st6, pc6, d6Lo, fr6, k6⟩ :=
    storeScratch_val_steps h8 slLoBS rZero (by decide) (by decide) hSlLoW hpc5f hpl6
      (by change pcAfter + a1.length + 2 + a3.length + a4.length + 6 + a6.length < code.size; omega) ho5f
  rw [ha6Eq] at pc6
  have hz6 : (reg s6 rZero).val = 0 := by rw [k6 _ (by decide), hz5f]
  have ho6 : (reg s6 rOne).val = 1 := by rw [k6 _ (by decide), ho5f]
  have hval6 : (reg s6 rVal).val = dM + 1 := by rw [k6 _ (by decide), hval5f]
  have hLo6 : (s6.data[slLoBS]?).map Fin.val = some 0 := by rw [d6Lo, hz5f]
  have hMN6 : (s6.data[slMNode]?).map Fin.val = some mNode := by
    rw [fr6 slMNode (by decide), hd5f]; exact hMN3
  have hfr6 : ∀ j, j ≠ slMNode → j ≠ slLoBS → s6.data[j]? = s.data[j]? := fun j h1 h2 => by
    rw [fr6 j h2, hd5f]; exact hfr3 j h1
  obtain ⟨s7, st7, pc7, d7Hi, fr7, k7⟩ :=
    storeScratch_val_steps h8 slHiBS rVal (by decide) (by decide) hSlHiW pc6 hpl7
      (by change pcAfter + a1.length + 2 + a3.length + a4.length + 6 + a6.length + a7.length < code.size; omega)
      ho6
  rw [ha7Eq] at pc7
  have hStepsAll : Steps code input
      (a1.length + 2 + a3.length + a4.length + 6 + a6.length + a7.length) s s7 := by
    have st2 : Steps code input 2 s1 s2b := Steps.cons st2a (Steps.cons st2b (Steps.zero _))
    have st5 : Steps code input 6 s4 s5f :=
      Steps.cons st5a (Steps.cons st5b (Steps.cons st5c (Steps.cons st5d (Steps.cons st5e (Steps.cons st5f (Steps.zero _))))))
    exact (((((st1.append st2).append st3).append st4).append st5).append st6).append st7
  refine ⟨s7, a1.length + 2 + a3.length + a4.length + 6 + a6.length + a7.length, by omega, hStepsAll, ?_,
    by rw [k7 _ (by decide), hz6], by rw [k7 _ (by decide), ho6],
    by rw [fr7 slMNode (by decide), hMN6],
    by rw [fr7 slLoBS (by decide), hLo6],
    by rw [d7Hi, hval6],
    fun j hj => ?_⟩
  · rw [pc7]
    change pcAfter + a1.length + 2 + a3.length + a4.length + 6 + a6.length + a7.length =
      pcAfter + (a1 ++ a2 ++ a3 ++ a4 ++ a5 ++ a6 ++ a7).length
    rw [hTotLen]; omega
  unfold slMNode slLoBS slHiBS at *
  rw [fr7 j (by rcases hj with h | h <;> omega)]
  exact hfr6 j (by rcases hj with h | h <;> omega) (by rcases hj with h | h <;> omega)

theorem sweepPredScanBlock_step {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {rows dictRows : Rows H}
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {F : JumpForest} {sRef : _root_.EX24.State H} {idx : Nat}
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {pcStart pcWriteZero : Nat}
    (hWZ : pcWriteZero < code.size)
    (hSz : pcStart + (sweepPredScanBlock h8 pcStart pcWriteZero).length < code.size)
    (hpl : Placed code pcStart (sweepPredScanBlock h8 pcStart pcWriteZero))
    {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F sRef idx s)
    (hidx : idx < H.vertexCount)
    {y : Vertex H} {lo hi' : Nat}
    (hLoHi : lo < hi')
    (hDiff : hi' - lo = (rows.row y).length)
    (hPB : ∀ j : Fin (rows.row y).length,
      (s.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
        some ((rows.row y)[j.val]'j.isLt).val)
    (hHiM : hi' ≤ H.arcCount)
    (hpc : s.pc = pcStart)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hstk : (reg s rStack).val = lo) (hrem : (reg s rRem).val = hi') :
    if H.hasQuotientArcBool H.root y then
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 125 + 12 * (rows.row y).length ∧
        Steps code input k s t ∧ t.pc = pcWriteZero ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧ t.data = s.data
    else
      ∃ m_y : Vertex H,
        maxByRank rank (preds H y) = some m_y ∧ m_y ∈ rows.row y ∧ H.HasQuotientArc m_y y ∧
        ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
          k ≤ 125 + 12 * (rows.row y).length ∧
          Steps code input k s t ∧
          t.pc = pcStart + (sweepPredScanBlock h8 pcStart pcWriteZero).length ∧
          (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
          (t.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val) ∧
          (t.data[slLoBS]?).map Fin.val = some 0 ∧
          (t.data[slHiBS]?).map Fin.val = some (F.depthOf (sRef.labelAt m_y.val) + 1) ∧
          ∀ j, j < 22 ∨ 25 ≤ j → t.data[j]? = s.data[j]? := by
  let n := H.vertexCount
  let m := H.arcCount
  let q0 : List (Instr bits 15) := [.mov rClk rStack, .mov rChild rZero, .mov rStack rZero]
  let q1 := loadScratch h8 rVal slRoot ++ loadScratch h8 rCnt slPredBuf ++ loadScratch h8 rTin slRanks
  let pcLoop := pcStart + 3 + q1.length
  let pcAfter := pcLoop + 12
  let q2 : List (Instr bits 15) :=
    [ .branchLt rClk rRem (pcLoop + 1) pcAfter,
      .add rTmp rCnt rClk,
      .loadData rPtr rTmp,
      .branchLt rPtr rVal (pcLoop + 5) (pcLoop + 4),
      .branchLt rVal rPtr (pcLoop + 5) pcWriteZero,
      .add rTmp rTin rPtr,
      .loadData rTmp rTmp,
      .branchLt rTmp rChild (pcLoop + 10) (pcLoop + 8),
      .mov rStack rPtr,
      .mov rChild rTmp,
      .add rClk rClk rOne,
      .goto pcLoop ]
  let q3 :=
    loadScratch h8 rTmp slLabels ++ [.add rTmp rTmp rStack, .loadData rPtr rTmp] ++
    sweepInitStoreScratch h8 slMNode rPtr ++
    loadScratch h8 rTmp slJumpBase ++
    [.add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rPtr, .add rTmp rTmp rOne,
     .loadData rVal rTmp, .add rVal rVal rOne] ++
    sweepInitStoreScratch h8 slLoBS rZero ++
    sweepInitStoreScratch h8 slHiBS rVal
  have hLenBlock : (sweepPredScanBlock h8 pcStart pcWriteZero).length = 3 + q1.length + 12 + q3.length := by
    unfold sweepPredScanBlock
    dsimp only [q1, q3]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hSz' : pcStart + 3 + q1.length + 12 + q3.length < code.size := by
    rw [hLenBlock] at hSz; exact hSz
  have h012 : Placed code pcStart (((q0 ++ q1) ++ q2)) := placed_append_left hpl
  have hpl01 : Placed code pcStart (q0 ++ q1) := placed_append_left h012
  have hpl2 : Placed code pcLoop q2 :=
    placed_right_eq h012 (by dsimp only [pcLoop, q0]; simp only [List.length_append]; rfl)
  have hpl3 : Placed code pcAfter q3 :=
    placed_right_eq hpl (by
      dsimp only [pcAfter, pcLoop, q0, q1, q2]
      simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  obtain ⟨s1, k1, hk1, st1, pc1, hz1, ho1, hclk1, hrem1, hch1, hstk1, hval1, hcnt1, htin1, hd1⟩ :=
    sweepPredScan_q01_steps h8 large hWork (by change pcStart + 3 + q1.length < code.size; omega)
      hpl01 hpc hz ho hstk hrem inv.slRootVal inv.slPredBufVal inv.slRanksVal
  have hWork' : 32 * n + 7 * m + 17 ≤ workCap := by
    change rawWorkCap n m ≤ workCap at hWork; unfold rawWorkCap at hWork; exact hWork
  have hPB1 : ∀ j : Fin (rows.row y).length,
      (s1.data[predBufBase n m + lo + j.val]?).map Fin.val = some ((rows.row y)[j.val]'j.isLt).val := by
    intro j; rw [hd1]; exact hPB j
  have hRk1 : ∀ u : Vertex H, (s1.data[ranksBase n m + u.val]?).map Fin.val = some (rank u) := by
    intro u; rw [hd1]; exact inv.stage1.ranks_mem u
  have hAddrPB : ∀ j : Fin (rows.row y).length, predBufBase n m + lo + j.val < workCap := by
    intro j
    simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords] at *; omega
  have hAddrRk : ∀ u : Vertex H, ranksBase n m + u.val < workCap := by
    intro u; have := u.isLt
    simp only [ranksBase, orderBase, stampsBase, indegBase, csrArenaWords] at *; omega
  cases hRow : rows.row y with
  | nil => rw [hRow] at hDiff; simp at hDiff; omega
  | cons u0 tl =>
    have hPB0 : (s1.data[predBufBase n m + lo]?).map Fin.val = some u0.val := by
      have := hPB1 ⟨0, by rw [hRow]; simp⟩
      simpa [hRow] using this
    have hHiW : hi' < workCap := by omega
    have hIt0 := sweepPredScan_iter0_step h8 (code := code) (input := input) (rank := rank)
      (pcLoop := pcLoop) (pcWriteZero := pcWriteZero) (pbB := predBufBase n m)
      (rkB := ranksBase n m) hLoHi hHiW (by have := hAddrPB ⟨0, by rw [hRow]; simp⟩; omega)
      (hAddrRk u0) hWZ (by change pcLoop + 12 < code.size; omega) hpl2 pc1 hz1 ho1 hclk1 hrem1
      hch1 hval1 hcnt1 htin1 hPB0 (hRk1 u0)
    by_cases hu0 : u0 = H.root
    · have hMemRoot : H.root ∈ rows.row y := by rw [hRow]; exact List.mem_cons.mpr (Or.inl hu0.symm)
      have hBool : H.hasQuotientArcBool H.root y = true :=
        (hasQuotientArcBool_eq_true_iff H H.root y).mpr (((rows.spec y).cover H.root).mp hMemRoot)
      obtain ⟨s2, k2, hk2, st2, pc2, hz2, ho2, hd2⟩ := ite_elim_true hu0 hIt0
      exact ite_true_branch (by rw [hBool])
        ⟨s2, k1 + k2, by simp; omega, st1.append st2, pc2, hz2, ho2, hd2.trans hd1⟩
    · obtain ⟨s2, k2, hk2, st2, pc2, hz2, ho2, hclk2, hrem2, hstk2, hch2, hval2, hcnt2, htin2, hd2⟩ :=
        ite_elim_false hu0 hIt0
      have hPB2 : ∀ j : Fin (rows.row y).length,
          (s2.data[predBufBase n m + lo + j.val]?).map Fin.val = some ((rows.row y)[j.val]'j.isLt).val := by
        intro j; rw [hd2]; exact hPB1 j
      have hRk2 : ∀ u : Vertex H, (s2.data[ranksBase n m + u.val]?).map Fin.val = some (rank u) := by
        intro u; rw [hd2]; exact hRk1 u
      have hLoopRes := sweepPredScan_loop_steps h8 (code := code) (input := input) (rank := rank)
        hRow hDiff (by omega) hHiW hAddrPB hAddrRk hWZ (by change pcLoop + 12 < code.size; omega)
        hpl2 hPB2 hRk2 tl.length 1 (by rw [hRow]; simp; omega) (by omega) hz2 ho2 hclk2 hrem2
        (by simpa [maxByRankAux] using hstk2) (by simpa [maxByRankAux] using hch2)
        hval2 hcnt2 htin2 pc2
      have hDrop1 : (rows.row y).drop 1 = tl := by rw [hRow]; rfl
      by_cases hInTl : H.root ∈ (rows.row y).drop 1
      · have hMemRoot : H.root ∈ rows.row y := by
          rw [hRow]; exact List.mem_cons.mpr (Or.inr (by rwa [← hDrop1]))
        have hBool : H.hasQuotientArcBool H.root y = true :=
          (hasQuotientArcBool_eq_true_iff H H.root y).mpr (((rows.spec y).cover H.root).mp hMemRoot)
        obtain ⟨s3, k3, hk3, st3, pc3, hz3, ho3, hd3⟩ := ite_elim_true hInTl hLoopRes
        exact ite_true_branch (by rw [hBool])
          ⟨s3, k1 + k2 + k3, by simp; omega, (st1.append st2).append st3, pc3, hz3, ho3,
            hd3.trans (hd2.trans hd1)⟩
      · have hNoRoot : H.root ∉ rows.row y := by
          rw [hRow, List.mem_cons]; rintro (hEq | hTail)
          · exact hu0 hEq.symm
          · exact hInTl (by rwa [hDrop1])
        have hInj : Function.Injective rank := fun _ _ h => distinctRanks_of_stage1 inv.stage1 h
        obtain ⟨hBoolFalse, hMaxPred, hmMem, hmArc⟩ :=
          maxByRank_preds_eq_row rows rank hInj u0 tl hRow hNoRoot
        let best := maxByRankAux rank u0 tl
        obtain ⟨s3, k3, hk3, st3, pc3, hz3, ho3, hstk3, hd3⟩ := ite_elim_false hInTl hLoopRes
        have hd30 : s3.data = s.data := hd3.trans (hd2.trans hd1)
        let mNode := sRef.labelAt best.val
        have hmNodeNext : mNode < sRef.tables.next := inv.labelsLt best
        have hmNodeF : mNode < F.size := inv.grounded.size_eq ▸ hmNodeNext
        have hmNodeLeN : mNode ≤ n := Nat.le_trans (Nat.le_of_lt hmNodeNext) (Nat.le_trans inv.sRefNextLe (by omega))
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
          exact hStep inv.records.valid mNode hmNodeF
        have hdMLt : F.depthOf mNode + 1 < 2 ^ bits := Nat.lt_of_lt_of_le (by omega) hw
        have hLab : (s3.data[labelsBase n m + best.val]?).map Fin.val = some mNode := by
          rw [hd30]; exact inv.labelsMem best
        have hDep : (s3.data[jumpBase n m + 1 + 3 * mNode]?).map Fin.val = some (F.depthOf mNode) := by
          rw [hd30]; exact inv.records.depth mNode hmNodeF
        obtain ⟨s4, k4, hk4, st4, pc4, hz4, ho4, hMN4, hLo4, hHi4, hfr4⟩ :=
          sweepPredScan_q3_steps h8 large hWork best.isLt hmNodeLeN hdMLt hpl3
            (by change pcAfter + q3.length < code.size; omega)
            pc3 hz3 ho3 hstk3 (by rw [hd30]; exact inv.slLabelsVal)
            (by rw [hd30]; exact inv.slJumpVal) hLab hDep
        have hmMem' : best ∈ u0 :: tl := by rw [← hRow]; exact hmMem
        refine ite_false_branch (by rw [hBoolFalse]; decide)
          ⟨best, hMaxPred, hmMem', hmArc, s4, k1 + k2 + k3 + k4,
            by simp; omega, ((st1.append st2).append st3).append st4,
            ?_, hz4, ho4, hMN4, hLo4, hHi4,
            fun j hj => by rw [hfr4 j hj, hd30]⟩
        · rw [pc4]
          change pcAfter + q3.length = pcStart + (sweepPredScanBlock h8 pcStart pcWriteZero).length
          rw [hLenBlock]; dsimp only [pcAfter, pcLoop]; omega


end SweepLoopExec

end PaperB.RamForestProgram.Sweep
