module

public import PaperB.RamForestSweepScan
public import PaperB.RamForestSweepInsert

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

private def sweepLoopBody {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  let pcHead := 0
  let pcPredScan := (sweepHeadBlock h8 0 0).length
  let pcBS := pcPredScan + (sweepPredScanBlock h8 pcPredScan 0).length
  let pcFinalParent := pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS 0).length
  let pcInstall := pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent 0).length
  let pcWriteZero := pcInstall + (sweepPairAndDictBS h8 0 0 0 0).length +
    (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8
  let pcHalt := pcInstall + (sweepInstallBlock h8 pcInstall 0).length
  sweepHeadBlock h8 pcHalt pcWriteZero ++
  sweepPredScanBlock h8 pcPredScan pcWriteZero ++
  sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent ++
  sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall ++
  sweepInstallBlock h8 pcInstall pcHead

private theorem sweepLoopBody_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (sweepLoopBody (hi := hi) (hw := hw) h8).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold sweepLoopBody
  simp only [List.all_append, sweepHeadBlock_nonHalt, sweepPredScanBlock_nonHalt,
    sweepBSBlock_nonHalt, sweepFinalParentBlock_nonHalt, sweepInstallBlock_nonHalt, Bool.and_self]

def sweepLoopPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  mkPhase (sweepLoopBody (hi := hi) (hw := hw) h8) (sweepLoopBody_nonHalt h8)

end SweepLoopProgram

section SweepLoopExec

open PaperB.ForestHead _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

private theorem sweepLoopBody_len_parts {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    let pcPredScan := (sweepHeadBlock h8 0 0).length
    let pcBS := pcPredScan + (sweepPredScanBlock h8 pcPredScan 0).length
    let pcFinalParent := pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS 0).length
    let pcInstall := pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent 0).length
    let pcHalt := pcInstall + (sweepInstallBlock h8 pcInstall 0).length
    (sweepLoopBody (hi := hi) (hw := hw) h8).length = pcHalt := by
  unfold sweepLoopBody
  simp only [List.length_append,
    sweepHeadBlock_length, sweepPredScanBlock_length,
    sweepBSBlock_length, sweepFinalParentBlock_length, sweepInstallBlock_length]

private theorem sweepLoopBody_slices {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (hpl : Placed code 0 (sweepLoopBody (hi := hi) (hw := hw) h8)) :
    let pcPredScan := (sweepHeadBlock h8 0 0).length
    let pcBS := pcPredScan + (sweepPredScanBlock h8 pcPredScan 0).length
    let pcFinalParent := pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS 0).length
    let pcInstall := pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent 0).length
    let pcWriteZero := pcInstall + (sweepPairAndDictBS h8 0 0 0 0).length +
      (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8
    let pcHalt := pcInstall + (sweepInstallBlock h8 pcInstall 0).length
    Placed code 0 (sweepHeadBlock h8 pcHalt pcWriteZero) ∧
    Placed code pcPredScan (sweepPredScanBlock h8 pcPredScan pcWriteZero) ∧
    Placed code pcBS (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent) ∧
    Placed code pcFinalParent (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall) ∧
    Placed code pcInstall (sweepInstallBlock h8 pcInstall 0) := by
  let pcPredScan := (sweepHeadBlock h8 0 0).length
  let pcBS := pcPredScan + (sweepPredScanBlock h8 pcPredScan 0).length
  let pcFinalParent := pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS 0).length
  let pcInstall := pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent 0).length
  let pcWriteZero := pcInstall + (sweepPairAndDictBS h8 0 0 0 0).length +
    (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8
  let pcHalt := pcInstall + (sweepInstallBlock h8 pcInstall 0).length
  have hEq : sweepLoopBody (hi := hi) (hw := hw) h8 =
      sweepHeadBlock h8 pcHalt pcWriteZero ++
      sweepPredScanBlock h8 pcPredScan pcWriteZero ++
      sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent ++
      sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall ++
      sweepInstallBlock h8 pcInstall 0 := rfl
  have h1234 := placed_append_left (hEq ▸ hpl)
  have h123 := placed_append_left h1234
  have h12 := placed_append_left h123
  have h1 := placed_append_left h12
  have h2Raw := placed_append_right h12
  have h2 : Placed code pcPredScan (sweepPredScanBlock h8 pcPredScan pcWriteZero) := by
    have hl : 0 + (sweepHeadBlock h8 pcHalt pcWriteZero).length = pcPredScan := by
      dsimp only [pcPredScan]; rw [Nat.zero_add, sweepHeadBlock_length]
    rwa [hl] at h2Raw
  have h3Raw := placed_append_right h123
  have h3 : Placed code pcBS (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent) := by
    have hl : 0 + (sweepHeadBlock h8 pcHalt pcWriteZero ++
        sweepPredScanBlock h8 pcPredScan pcWriteZero).length = pcBS := by
      dsimp only [pcBS, pcPredScan]
      simp only [List.length_append, sweepHeadBlock_length, sweepPredScanBlock_length]
      omega
    rwa [hl] at h3Raw
  have h4Raw := placed_append_right h1234
  have h4 : Placed code pcFinalParent
      (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall) := by
    have hl : 0 + (sweepHeadBlock h8 pcHalt pcWriteZero ++
        sweepPredScanBlock h8 pcPredScan pcWriteZero ++
        sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent).length = pcFinalParent := by
      dsimp only [pcFinalParent, pcBS, pcPredScan]
      simp only [List.length_append, sweepHeadBlock_length, sweepPredScanBlock_length, sweepBSBlock_length]
      omega
    rwa [hl] at h4Raw
  have h5Raw := placed_append_right (hEq ▸ hpl)
  have h5 : Placed code pcInstall (sweepInstallBlock h8 pcInstall 0) := by
    have hl : 0 + (sweepHeadBlock h8 pcHalt pcWriteZero ++
        sweepPredScanBlock h8 pcPredScan pcWriteZero ++
        sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent ++
        sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall).length = pcInstall := by
      dsimp only [pcInstall, pcFinalParent, pcBS, pcPredScan]
      simp only [List.length_append, sweepHeadBlock_length, sweepPredScanBlock_length,
        sweepBSBlock_length, sweepFinalParentBlock_length]
      omega
    rwa [hl] at h5Raw
  exact ⟨h1, h2, h3, h4, h5⟩

private theorem sweepLoopBody_iter_step {bits inputCap workCap : Nat}
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
    (hBodyBnd : (sweepLoopBody (hi := hi) (hw := hw) h8).length < code.size)
    (hplBody : Placed code 0 (sweepLoopBody (hi := hi) (hw := hw) h8))
    (hpc : s.pc = 0) :
    let y := orderedVertexAt order size_order ⟨idx, hidx⟩
    ∃ rStep : _root_.EX24.HeadResult H,
      _root_.EX24.stepPrepared (orderedConfig dictRows large) sRef rank y (dictRows.row y) = some rStep ∧
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 ∧
        Steps code input k s t ∧
        t.pc = 0 ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
          (order := order) (size_order := size_order) (rank := rank) (large := large)
          (if rStep.installed.allocated then F.appendLeaf rStep.measured.step.parent else F)
          rStep.state (idx + 1) t := by
  let y := orderedVertexAt order size_order ⟨idx, hidx⟩
  let n := H.vertexCount
  let m := H.arcCount
  have hWork32 : 32 * n + 7 * m + 17 ≤ workCap := hWork
  let pcPredScan := (sweepHeadBlock h8 0 0).length
  let pcBS := pcPredScan + (sweepPredScanBlock h8 pcPredScan 0).length
  let pcFinalParent := pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS 0).length
  let pcInstall := pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent 0).length
  let d1 := (sweepPairAndDictBS h8 0 0 0 0).length
  let d2 := (sweepSkewInsert h8 0 0).length
  let pcKeepP := pcInstall + d1 + d2
  let pcWriteZero := pcKeepP + sweepInstallKeepLen h8
  let pcWriteLabel := pcWriteZero + 1
  let pcHalt := pcInstall + (sweepInstallBlock h8 pcInstall 0).length
  have hBodyLen : (sweepLoopBody (hi := hi) (hw := hw) h8).length = pcHalt :=
    sweepLoopBody_len_parts (hi := hi) (hw := hw) h8
  obtain ⟨hplHead, hplPred, hplBS, hplFP, hplInst⟩ := sweepLoopBody_slices (hi := hi) (hw := hw) h8 hplBody
  have ⟨_, _, hplTail⟩ := sweepInstallBlock_slices h8 hplInst
  have hTailLen : (sweepInstallTail h8 pcWriteLabel 0).length ≥
      (loadScratch h8 rVal slAncNode).length + 2 := by
    rw [sweepInstallTail_eq_parts]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
  have hKeepLen : sweepInstallKeepLen h8 = (loadScratch h8 rVal slAncNode).length + 1 := rfl
  have hInstLen : (sweepInstallBlock h8 pcInstall 0).length =
      d1 + d2 + (sweepInstallTail h8 pcWriteLabel 0).length :=
    sweepInstallBlock_len_parts h8 pcInstall 0
  have hHaltBnd : pcHalt < code.size := hBodyLen ▸ hBodyBnd
  have hHaltCan :
      (sweepHeadBlock h8 0 0).length +
      (sweepPredScanBlock h8 0 0).length +
      (sweepBSBlock (hi := hi) (hw := hw) h8 0 0).length +
      (sweepFinalParentBlock (hi := hi) (hw := hw) h8 0 0).length +
      (sweepInstallBlock h8 0 0).length < code.size := by
    have h1 := hHaltBnd
    dsimp only [pcHalt, pcInstall, pcFinalParent, pcBS, pcPredScan] at h1
    rw [sweepInstallBlock_length h8 _ 0, sweepFinalParentBlock_length h8 _ 0,
      sweepBSBlock_length (hi := hi) (hw := hw) h8 _ 0, sweepPredScanBlock_length h8 _ 0] at h1
    exact h1
  have hZeroBnd : 0 < code.size := by omega
  have hWZBnd : pcWriteZero < code.size := by
    have h := hHaltBnd
    dsimp only [pcWriteZero, pcKeepP, pcHalt] at h ⊢
    rw [hInstLen] at h; rw [hKeepLen]; omega
  have hHeadSz : (sweepHeadBlock h8 pcHalt pcWriteZero).length < code.size := by
    rw [sweepHeadBlock_length]; omega
  have hPredSz : pcPredScan + (sweepPredScanBlock h8 pcPredScan pcWriteZero).length < code.size := by
    rw [sweepPredScanBlock_length]; dsimp only [pcPredScan]; omega
  have hBSSz : pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS pcFinalParent).length < code.size := by
    rw [sweepBSBlock_length]; dsimp only [pcBS, pcPredScan]
    rw [sweepPredScanBlock_length h8 _ 0]; omega
  have hFPSz : pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall).length < code.size := by
    rw [sweepFinalParentBlock_length]; dsimp only [pcFinalParent, pcBS, pcPredScan]
    rw [sweepBSBlock_length (hi := hi) (hw := hw) h8 _ 0, sweepPredScanBlock_length h8 _ 0]; omega
  have hInstSz : pcInstall + (sweepInstallBlock h8 pcInstall 0).length < code.size := hHaltBnd
  have hTailBnd : pcKeepP + (sweepInstallTail h8 pcWriteLabel 0).length < code.size := by
    have h := hHaltBnd
    dsimp only [pcKeepP, pcHalt] at h ⊢; rw [hInstLen] at h; omega
  have hWLKeep : pcWriteLabel = pcKeepP + (loadScratch h8 rVal slAncNode).length + 2 := by
    dsimp only [pcWriteLabel, pcWriteZero]; rw [hKeepLen]; omega
  have hWZEq : pcWriteZero = pcKeepP + (loadScratch h8 rVal slAncNode).length + 1 := by
    dsimp only [pcWriteZero]; rw [hKeepLen]; omega
  -- 1. Head check
  have hHC := sweepHeadBlock_halt_or_branch h8 (input := input) large hWork hpc hplHead hHaltBnd hHeadSz
    inv.slIdxVal inv.slNVal
  rw [ite_eq_left hidx] at hHC
  obtain ⟨s1, k1, hk1, st1, pc1, hz1, ho1, hc1, hd1⟩ := hHC
  have inv1 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s1 :=
    inv.of_scratch19 (fun _ _ => by rw [hd1])
  -- 2. Head body
  obtain ⟨lo, hi', _, _, hLoHi, hHiM, hDiff, hPB, s2, k2, hk2, st2, hz2, ho2, hY2, hPres2, hBr2⟩ :=
    sweepHeadBlock_body_step h8 hWork hWZBnd hHeadSz hplHead inv1 hidx pc1 hz1 ho1 hc1
  have inv2 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s2 :=
    inv1.of_scratch19 (fun j hj => hPres2 j (hj.imp id (fun h => by omega)))
  have hL1Pos : 1 ≤ OracleContract.L H.vertexCount + 1 := by omega
  have hDegPos : 1 ≤ (rows.row y).length + 1 := by omega
  have hScrPred : 30 ≤ predBufBase n m := by
    have h0 : 29 < orderBase n m := scratch_lt_orderBase (n := n) (m := m) (sl := 29) large (by omega)
    have h1 : orderBase n m ≤ predBufBase n m := by
      simp only [predBufBase, rowEndBase, rowStartBase, ranksBase]; omega
    omega
  by_cases hyR : y = H.root
  · rw [ite_eq_left hyR] at hBr2
    obtain ⟨rStep, hStep, hAlloc, hNode⟩ := sweep_stopped_step_spec inv hidx (Or.inl hyR)
    obtain ⟨t, k3, hk3, st3, pc3, hz3, ho3, hLab3, hIdx3, hPres3⟩ :=
      sweepInstallTail_zero_steps h8 input hWork32 large y.isLt hidx hZeroBnd hWLKeep hTailBnd hplTail
        s2 (hBr2.trans hWZEq) hz2 ho2 hY2 inv2.slLabelsVal inv2.slIdxVal
    have hInvT := inv2.advance_keep hidx y hStep hAlloc (by rw [hNode]; exact hLab3) hIdx3 fun j => by
      rcases hPres3 j with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    have hBndK : k1 + k2 + k3 ≤ 1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
      have hMul : 1 ≤ ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 :=
        Nat.mul_pos hDegPos (Nat.pow_pos hL1Pos)
      calc k1 + k2 + k3 ≤ 206 := by omega
        _ ≤ 1200 := by decide
        _ ≤ 1200 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) :=
          Nat.le_mul_of_pos_right _ hMul
        _ = 1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
          rw [Nat.mul_assoc]
    refine ⟨rStep, hStep, t, k1 + k2 + k3, hBndK, (st1.append st2).append st3, pc3, hz3, ho3, ?_⟩
    simpa only [hAlloc, Bool.false_eq_true, ↓reduceIte] using hInvT
  · rw [ite_eq_right hyR] at hBr2
    obtain ⟨hSlRL2, hSlRH2, hRowBr⟩ := hBr2
    by_cases hNonEmpty : lo < hi'
    · rw [ite_eq_left hNonEmpty] at hRowBr
      obtain ⟨pc2, hrSt2, hrRm2⟩ := hRowBr
      have hPredLenEq : (sweepHeadBlock h8 pcHalt pcWriteZero).length = pcPredScan :=
        sweepHeadBlock_length h8 pcHalt pcWriteZero
      have hPB2 : ∀ j : Fin (rows.row y).length,
          (s2.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
            some ((rows.row y)[j.val]'j.isLt).val := fun j => by
        have hlt := hPB j
        have hPresPB := hPres2 (predBufBase H.vertexCount H.arcCount + lo + j.val)
          (Or.inr (by change 22 ≤ predBufBase n m + lo + j.val; omega))
        rw [hPresPB]; exact hlt
      -- 3. Pred scan
      have hPS := sweepPredScanBlock_step h8 (input := input) hWork hWZBnd hPredSz hplPred inv2 hidx
        hNonEmpty hDiff hPB2 hHiM (pc2.trans hPredLenEq) hz2 ho2 hrSt2 hrRm2
      by_cases hRootArc : H.hasQuotientArcBool H.root y = true
      · rw [ite_eq_left hRootArc] at hPS
        obtain ⟨s3, k3, hk3, st3, pc3, hz3, ho3, hd3⟩ := hPS
        have inv3 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
            (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s3 :=
          inv2.of_scratch19 (fun _ _ => by rw [hd3])
        obtain ⟨rStep, hStep, hAlloc, hNode⟩ := sweep_stopped_step_spec inv hidx (Or.inr (Or.inr hRootArc))
        obtain ⟨t, k4, hk4, st4, pc4, hz4, ho4, hLab4, hIdx4, hPres4⟩ :=
          sweepInstallTail_zero_steps h8 input hWork32 large y.isLt hidx hZeroBnd hWLKeep hTailBnd hplTail
            s3 (pc3.trans hWZEq) hz3 ho3 (by rw [hd3]; exact hY2) inv3.slLabelsVal inv3.slIdxVal
        have hInvT := inv3.advance_keep hidx y hStep hAlloc (by rw [hNode]; exact hLab4) hIdx4 fun j => by
          rcases hPres4 j with h | h | h
          · exact Or.inr (Or.inl h)
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
        have hBndK : k1 + k2 + k3 + k4 ≤
            1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
          have hL1Sq : 1 ≤ (OracleContract.L H.vertexCount + 1) ^ 2 := Nat.pow_pos hL1Pos
          have hD1 : 331 ≤ 331 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) :=
            Nat.le_mul_of_pos_right _ (Nat.mul_pos hDegPos hL1Sq)
          have hD2 : 12 * (rows.row y).length ≤
              12 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) := by
            have h1 : (rows.row y).length ≤ ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 :=
              Nat.le_trans (Nat.le_succ _) (Nat.le_mul_of_pos_right _ hL1Sq)
            exact Nat.mul_le_mul_left 12 h1
          have h343 : 343 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) ≤
              1200 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) :=
            Nat.mul_le_mul_right _ (by decide)
          calc k1 + k2 + k3 + k4 ≤ 331 + 12 * (rows.row y).length := by
                change k1 + k2 + k3 + k4 ≤ 331 + 12 * (rows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)).length
                omega
            _ ≤ 331 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) +
                12 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) :=
              Nat.add_le_add hD1 hD2
            _ = 343 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) := by
              rw [← Nat.add_mul]
            _ ≤ 1200 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) := h343
            _ = 1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
              rw [Nat.mul_assoc]
        refine ⟨rStep, hStep, t, k1 + k2 + k3 + k4, hBndK, ((st1.append st2).append st3).append st4,
          pc4, hz4, ho4, ?_⟩
        simpa only [hAlloc, Bool.false_eq_true, ↓reduceIte] using hInvT
      · have hNoRoot : H.hasQuotientArcBool H.root y = false := Bool.eq_false_iff.mpr hRootArc
        rw [ite_eq_right hRootArc] at hPS
        obtain ⟨m_y, hMax, _, _, s3, k3, hk3, st3, pc3, hz3, ho3, hSlM3, hSlLo3, hSlHi3, hPres3⟩ := hPS
        have inv3 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
            (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s3 :=
          inv2.of_scratch19 (fun j hj => hPres3 j (hj.imp (fun h => by omega) (fun h => by omega)))
        have hBSLenEq : pcPredScan + (sweepPredScanBlock h8 pcPredScan pcWriteZero).length = pcBS := by
          dsimp only [pcBS]; simp only [sweepPredScanBlock_length]
        have hPB3 : ∀ j : Fin (rows.row y).length,
            (s3.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
              some ((rows.row y)[j.val]'j.isLt).val := fun j => by
          have hPresPB := hPres3 (predBufBase H.vertexCount H.arcCount + lo + j.val)
            (Or.inr (by change 25 ≤ predBufBase n m + lo + j.val; omega))
          rw [hPresPB]; exact hPB2 j
        have hSlRL3 : (s3.data[slRowLo]?).map Fin.val = some lo := by
          rw [hPres3 slRowLo (Or.inl (by decide))]; exact hSlRL2
        have hSlRH3 : (s3.data[slRowHi]?).map Fin.val = some hi' := by
          rw [hPres3 slRowHi (Or.inl (by decide))]; exact hSlRH2
        have hSlY3 : (s3.data[slY]?).map Fin.val = some y.val := by
          rw [hPres3 slY (Or.inl (by decide))]; exact hY2
        -- 4. Binary search
        have hFPBnd : pcFinalParent < code.size := by
          dsimp only [pcFinalParent]
          rw [sweepBSBlock_length (hi := hi) (hw := hw) h8 pcBS 0,
            ← sweepBSBlock_length (hi := hi) (hw := hw) h8 pcBS pcFinalParent]
          omega
        obtain ⟨s4, k4, hk4, st4, pc4, hz4, ho4, hSlLo4, hPres4⟩ :=
          sweepBSBlock_step h8 (input := input) inv3 hWork hidx hFPBnd hBSSz hplBS (Nat.le_of_lt hNonEmpty) hHiM hDiff hPB3
            (pc3.trans hBSLenEq) hz3 ho3 hSlLo3 hSlHi3 hSlM3 hSlRL3 hSlRH3
        have inv4 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
            (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s4 :=
          inv3.of_scratch19 (fun j hj => by
            rcases hPres4 j with rfl | rfl | rfl | rfl | rfl | heq
            · exfalso; unfold slLoBS at hj; omega
            · exfalso; unfold slHiBS at hj; omega
            · exfalso; unfold slMidBS at hj; omega
            · exfalso; unfold slAncNode at hj; omega
            · exfalso; unfold slPredJ at hj; omega
            · exact heq)
        have hPres4Lt23 : ∀ w, w < 23 → s4.data[w]? = s3.data[w]? := fun w hw23 => by
          rcases hPres4 w with rfl | rfl | rfl | rfl | rfl | heq
          · unfold slLoBS at hw23; omega
          · unfold slHiBS at hw23; omega
          · unfold slMidBS at hw23; omega
          · unfold slAncNode at hw23; omega
          · unfold slPredJ at hw23; omega
          · exact heq
        have hSlM4 : (s4.data[slMNode]?).map Fin.val = some (sRef.labelAt m_y.val) := by
          rw [hPres4Lt23 slMNode (by decide)]; exact hSlM3
        have hCutLe : (PaperB.ForestHead.measuredLog
            (fun d => PaperB.ForestHead.probe (selectors (orderedConfig dictRows large) sRef) (rows.row y) m_y d)
            (F.depthOf (sRef.labelAt m_y.val) + 1)).cut ≤ F.depthOf (sRef.labelAt m_y.val) :=
          Nat.lt_succ_iff.mp (measuredSearch_cut_lt_hi _ _ 0 _ (Nat.zero_lt_succ _))
        -- 5. Final parent
        have hInstEq : pcInstall = pcFinalParent +
            (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent pcInstall).length := by
          dsimp only [pcInstall]
          congr 1
        obtain ⟨s5, k5, hk5, st5, pc5, hz5, ho5, hSlAnc5, hPres5⟩ :=
          sweepFinalParentBlock_step h8 input inv4 hWork hidx hInstEq hFPSz hplFP hCutLe pc4 hz4 ho4 hSlLo4 hSlM4
        have inv5 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
            (order := order) (size_order := size_order) (rank := rank) (large := large) F sRef idx s5 :=
          inv4.of_scratch19 (fun j hj => by
            rcases hPres5 j with rfl | heq
            · exfalso; unfold slAncNode at hj; omega
            · exact heq)
        have hPres5Lt26 : ∀ w, w < 26 → s5.data[w]? = s4.data[w]? := fun w hw26 => by
          rcases hPres5 w with rfl | heq
          · unfold slAncNode at hw26; omega
          · exact heq
        have hPB5 : ∀ t' : Fin (rows.row y).length,
            (s5.data[predBufBase H.vertexCount H.arcCount + lo + t'.val]?).map Fin.val =
              some ((rows.row y)[t'.val]'t'.isLt).val := fun t' => by
          have hGe30 : 30 ≤ predBufBase H.vertexCount H.arcCount + lo + t'.val := by
            change 30 ≤ predBufBase n m + lo + t'.val; omega
          have hp5 : s5.data[predBufBase H.vertexCount H.arcCount + lo + t'.val]? =
              s4.data[predBufBase H.vertexCount H.arcCount + lo + t'.val]? := by
            rcases hPres5 (predBufBase H.vertexCount H.arcCount + lo + t'.val) with h | h
            · unfold slAncNode at h; omega
            · exact h
          have hp4 : s4.data[predBufBase H.vertexCount H.arcCount + lo + t'.val]? =
              s3.data[predBufBase H.vertexCount H.arcCount + lo + t'.val]? := by
            rcases hPres4 (predBufBase H.vertexCount H.arcCount + lo + t'.val) with h | h | h | h | h | h
            · unfold slLoBS at h; omega
            · unfold slHiBS at h; omega
            · unfold slMidBS at h; omega
            · unfold slAncNode at h; omega
            · unfold slPredJ at h; omega
            · exact h
          rw [hp5, hp4]; exact hPB3 t'
        have hSlY5 : (s5.data[slY]?).map Fin.val = some y.val := by
          rw [hPres5Lt26 slY (by decide), hPres4Lt23 slY (by decide)]; exact hSlY3
        have hSlRL5 : (s5.data[slRowLo]?).map Fin.val = some lo := by
          rw [hPres5Lt26 slRowLo (by decide), hPres4Lt23 slRowLo (by decide)]; exact hSlRL3
        have hSlRH5 : (s5.data[slRowHi]?).map Fin.val = some hi' := by
          rw [hPres5Lt26 slRowHi (by decide), hPres4Lt23 slRowHi (by decide)]; exact hSlRH3
        -- 6. Install
        obtain ⟨rStep, hStep, t, k6, hk6, st6, pct, hzt, hot, invT⟩ :=
          sweepInstallBlock_step h8 input inv5 hidx hWork hZeroBnd hInstSz hplInst hyR hNoRoot hMax
            hNonEmpty hHiM hDiff hPB5 pc5 hz5 ho5 hSlAnc5 hSlY5 hSlRL5 hSlRH5
        have hBndK : k1 + k2 + k3 + k4 + k5 + k6 ≤
            1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
          let L := OracleContract.L H.vertexCount
          let d := (rows.row y).length
          have hSum : k1 + k2 + k3 + k4 + k5 + k6 ≤
              780 + 12 * d + 77 * (L + 1) + L * (d + 1) * (175 + 60 * (L + 1)) := by
            dsimp only [L, d]
            change k1 + k2 + k3 + k4 + k5 + k6 ≤
              780 + 12 * (rows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)).length +
                77 * (OracleContract.L H.vertexCount + 1) +
                OracleContract.L H.vertexCount *
                  ((rows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)).length + 1) *
                  (175 + 60 * (OracleContract.L H.vertexCount + 1))
            omega
          have hL1Sq : 1 ≤ (L + 1) ^ 2 := Nat.pow_pos hL1Pos
          have hMul1 : 1 ≤ (d + 1) * (L + 1) ^ 2 := Nat.mul_pos hDegPos hL1Sq
          have hDLe : d ≤ (d + 1) * (L + 1) ^ 2 :=
            Nat.le_trans (Nat.le_succ d) (Nat.le_mul_of_pos_right _ hL1Sq)
          have hL1Le : L + 1 ≤ (d + 1) * (L + 1) ^ 2 := by
            calc L + 1 ≤ (L + 1) * (L + 1) := Nat.le_mul_of_pos_left _ hL1Pos
              _ = (L + 1) ^ 2 := by rw [Nat.pow_two]
              _ ≤ (d + 1) * (L + 1) ^ 2 := Nat.le_mul_of_pos_left _ hDegPos
          have hk4Bound : L * (d + 1) * (175 + 60 * (L + 1)) ≤ 235 * ((d + 1) * (L + 1) ^ 2) := by
            have hA : 175 + 60 * (L + 1) ≤ 235 * (L + 1) := by omega
            have hB : L * (d + 1) * (175 + 60 * (L + 1)) ≤ (L + 1) * (d + 1) * (235 * (L + 1)) :=
              Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.le_succ L)) hA
            have hEq : (L + 1) * (d + 1) * (235 * (L + 1)) = 235 * ((d + 1) * (L + 1) ^ 2) := by
              simp only [Nat.pow_two, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
            omega
          have h780 : 780 ≤ 780 * ((d + 1) * (L + 1) ^ 2) := Nat.le_mul_of_pos_right _ hMul1
          have h12 : 12 * d ≤ 12 * ((d + 1) * (L + 1) ^ 2) := Nat.mul_le_mul_left _ hDLe
          have h77 : 77 * (L + 1) ≤ 77 * ((d + 1) * (L + 1) ^ 2) := Nat.mul_le_mul_left _ hL1Le
          have hTot : 1104 * ((d + 1) * (L + 1) ^ 2) ≤ 1200 * ((d + 1) * (L + 1) ^ 2) :=
            Nat.mul_le_mul_right _ (by decide)
          calc k1 + k2 + k3 + k4 + k5 + k6 ≤
                780 + 12 * d + 77 * (L + 1) + L * (d + 1) * (175 + 60 * (L + 1)) := hSum
            _ ≤ 780 * ((d + 1) * (L + 1) ^ 2) + 12 * ((d + 1) * (L + 1) ^ 2) +
                77 * ((d + 1) * (L + 1) ^ 2) + 235 * ((d + 1) * (L + 1) ^ 2) := by
              omega
            _ = 1104 * ((d + 1) * (L + 1) ^ 2) := by
              simp only [← Nat.add_mul]
            _ ≤ 1200 * ((d + 1) * (L + 1) ^ 2) := hTot
            _ = 1200 * (d + 1) * (L + 1) ^ 2 := by rw [Nat.mul_assoc]
        exact ⟨rStep, hStep, t, k1 + k2 + k3 + k4 + k5 + k6, hBndK,
          ((((st1.append st2).append st3).append st4).append st5).append st6,
          pct, hzt, hot, invT⟩
    · rw [ite_eq_right hNonEmpty] at hRowBr
      have hEmptyRow : rows.row y = [] := by
        apply List.eq_nil_of_length_eq_zero
        change (rows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)).length = 0
        rw [← hDiff]; omega
      obtain ⟨rStep, hStep, hAlloc, hNode⟩ := sweep_stopped_step_spec inv hidx (Or.inr (Or.inl hEmptyRow))
      obtain ⟨t, k3, hk3, st3, pc3, hz3, ho3, hLab3, hIdx3, hPres3⟩ :=
        sweepInstallTail_zero_steps h8 input hWork32 large y.isLt hidx hZeroBnd hWLKeep hTailBnd hplTail
          s2 (hRowBr.trans hWZEq) hz2 ho2 hY2 inv2.slLabelsVal inv2.slIdxVal
      have hInvT := inv2.advance_keep hidx y hStep hAlloc (by rw [hNode]; exact hLab3) hIdx3 fun j => by
        rcases hPres3 j with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      have hBndK : k1 + k2 + k3 ≤ 1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
        have hMul : 1 ≤ ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 :=
          Nat.mul_pos hDegPos (Nat.pow_pos hL1Pos)
        calc k1 + k2 + k3 ≤ 206 := by omega
          _ ≤ 1200 := by decide
          _ ≤ 1200 * (((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2) :=
            Nat.le_mul_of_pos_right _ hMul
          _ = 1200 * ((rows.row y).length + 1) * (OracleContract.L H.vertexCount + 1) ^ 2 := by
            rw [Nat.mul_assoc]
      refine ⟨rStep, hStep, t, k1 + k2 + k3, hBndK, (st1.append st2).append st3, pc3, hz3, ho3, ?_⟩
      simpa only [hAlloc, Bool.false_eq_true, ↓reduceIte] using hInvT

private def sweepRemWeight {H : LabelledQuotient} (rows : Rows H)
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (idx rem : Nat) (hLe : idx + rem ≤ H.vertexCount) : Nat :=
  ((List.finRange rem).map (fun j : Fin rem =>
    (rows.row (orderedVertexAt order size_order ⟨idx + j.val, by omega⟩)).length + 1)).sum

private theorem sweepRemWeight_succ {H : LabelledQuotient} (rows : Rows H)
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (idx rem : Nat) (hLe : idx + (rem + 1) ≤ H.vertexCount) :
    sweepRemWeight rows order size_order idx (rem + 1) hLe =
      ((rows.row (orderedVertexAt order size_order ⟨idx, by omega⟩)).length + 1) +
        sweepRemWeight rows order size_order (idx + 1) rem (by omega) := by
  unfold sweepRemWeight
  rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  congr 1
  apply List.map_congr_left
  intro j _
  dsimp only [Function.comp_def]
  have heq : (⟨idx + j.succ.val, by omega⟩ : Fin H.vertexCount) =
      ⟨(idx + 1) + j.val, by omega⟩ := by
    apply Fin.ext; simp only [Fin.val_succ]; omega
  rw [heq]

private theorem sweepRemWeight_full_le {H : LabelledQuotient} (rows : Rows H)
    (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
    (nodup : order.toList.Nodup) :
    sweepRemWeight rows order size_order 0 H.vertexCount (by omega) ≤
      H.vertexCount + H.arcCount := by
  unfold sweepRemWeight
  have hAdd : ∀ l : List (Fin H.vertexCount),
      (l.map (fun j => (rows.row (orderedVertexAt order size_order ⟨0 + j.val, by omega⟩)).length + 1)).sum =
      (l.map (fun j => (rows.row (orderedVertexAt order size_order j)).length)).sum + l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a as ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      have ha : (⟨0 + a.val, by omega⟩ : Fin H.vertexCount) = a := Fin.ext (Nat.zero_add a.val)
      rw [ha]; omega
  rw [hAdd, List.length_finRange]
  have hSum := row_length_sum_order H rows order size_order nodup
  omega

private theorem run_sweepLoop_aux {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (input : Input (layout bits inputCap workCap hi hw))
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (dictRows : Rows H) (large : 3 ≤ H.vertexCount)
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    (r : PaperB.OrderedReaderResult dictRows order size_order rank large)
    {code : Program (layout bits inputCap workCap hi hw)}
    (hBodyBnd : (sweepLoopBody (hi := hi) (hw := hw) h8).length < code.size)
    (hplBody : Placed code 0 (sweepLoopBody (hi := hi) (hw := hw) h8)) :
    ∀ (rem idx : Nat) (hSum : idx + rem = H.vertexCount)
      (F : JumpForest) (sRef : _root_.EX24.State H) (logTail : Log H)
      (s : State (layout bits inputCap workCap hi hw)),
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large)
        F sRef idx s →
      s.pc = 0 →
      Trace (orderedConfig dictRows large) rank sRef
        ((orderedRows dictRows order size_order).drop idx) r.out logTail →
      ∃ F' : JumpForest, ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 35 + 1200 * sweepRemWeight rows order size_order idx rem (by omega) *
          (OracleContract.L H.vertexCount + 1) ^ 2 ∧
        Steps code input k s t ∧
        t.pc = (sweepLoopBody (hi := hi) (hw := hw) h8).length ∧
        SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
          (order := order) (size_order := size_order) (rank := rank) (large := large)
          F' r.out H.vertexCount t := by
  intro rem
  induction rem with
  | zero =>
    intro idx hSum F sRef logTail s inv hpc hTrace
    have hidxEq : idx = H.vertexCount := by omega
    subst hidxEq
    have hDropNil : (orderedRows dictRows order size_order).drop H.vertexCount = [] := by
      apply List.drop_of_length_le
      simp [orderedRows]
    rw [hDropNil] at hTrace
    have hOutEq : sRef = r.out := by cases hTrace; rfl
    subst hOutEq
    let pcPredScan := (sweepHeadBlock h8 0 0).length
    let pcBS := pcPredScan + (sweepPredScanBlock h8 pcPredScan 0).length
    let pcFinalParent := pcBS + (sweepBSBlock (hi := hi) (hw := hw) h8 pcBS 0).length
    let pcInstall := pcFinalParent + (sweepFinalParentBlock (hi := hi) (hw := hw) h8 pcFinalParent 0).length
    let pcWriteZero := pcInstall + (sweepPairAndDictBS h8 0 0 0 0).length +
      (sweepSkewInsert h8 0 0).length + sweepInstallKeepLen h8
    let pcHalt := pcInstall + (sweepInstallBlock h8 pcInstall 0).length
    have hBodyLen : (sweepLoopBody (hi := hi) (hw := hw) h8).length = pcHalt :=
      sweepLoopBody_len_parts (hi := hi) (hw := hw) h8
    have hHaltBnd : pcHalt < code.size := hBodyLen ▸ hBodyBnd
    obtain ⟨hplHead, _, _, _, _⟩ := sweepLoopBody_slices (hi := hi) (hw := hw) h8 hplBody
    have hHeadSz : (sweepHeadBlock h8 pcHalt pcWriteZero).length < code.size := by
      rw [sweepHeadBlock_length]
      have h1 := hHaltBnd
      dsimp only [pcHalt, pcInstall, pcFinalParent, pcBS, pcPredScan] at h1
      rw [sweepInstallBlock_length h8 _ 0, sweepFinalParentBlock_length h8 _ 0,
        sweepBSBlock_length (hi := hi) (hw := hw) h8 _ 0, sweepPredScanBlock_length h8 _ 0] at h1
      omega
    have hHC := sweepHeadBlock_halt_or_branch h8 (input := input) large hCap hpc hplHead
      hHaltBnd hHeadSz inv.slIdxVal inv.slNVal
    rw [ite_eq_right (Nat.lt_irrefl H.vertexCount)] at hHC
    obtain ⟨t, k, hk, hst, htpc, hd⟩ := hHC
    have invT := inv.of_scratch19 (fun _ _ => by rw [hd])
    exact ⟨F, t, k, by omega, hst, htpc.trans hBodyLen.symm, invT⟩
  | succ rem' ih =>
    intro idx hSum F sRef logTail s inv hpc hTrace
    have hidx : idx < H.vertexCount := by omega
    obtain ⟨rTrace, tail, hStepTrace, hTraceTail⟩ :=
      orderedRows_drop_uncons dictRows rank large hidx hTrace
    obtain ⟨rStep, hStepCode, s1, k1, hk1, st1, pc1, _, _, inv1⟩ :=
      sweepLoopBody_iter_step h8 input inv hidx hCap hBodyBnd hplBody hpc
    have hRS : rTrace = rStep := Option.some.inj (hStepTrace.symm.trans hStepCode)
    rw [hRS] at hTraceTail
    obtain ⟨F', t, k2, hk2, st2, htpc, invT⟩ :=
      ih (idx + 1) (by omega)
        (if rStep.installed.allocated then F.appendLeaf rStep.measured.step.parent else F)
        rStep.state tail s1 inv1 pc1 hTraceTail
    have hW := sweepRemWeight_succ rows order size_order idx rem' (by omega)
    have hKBound : k1 + k2 ≤ 35 + 1200 * sweepRemWeight rows order size_order idx (rem' + 1) (by omega) *
        (OracleContract.L H.vertexCount + 1) ^ 2 := by
      let L1Sq := (OracleContract.L H.vertexCount + 1) ^ 2
      have hMulEq : 1200 * sweepRemWeight rows order size_order idx (rem' + 1) (by omega) * L1Sq =
          1200 * ((rows.row (orderedVertexAt order size_order ⟨idx, hidx⟩)).length + 1) * L1Sq +
            1200 * sweepRemWeight rows order size_order (idx + 1) rem' (by omega) * L1Sq := by
        rw [hW, Nat.mul_add, Nat.add_mul]
      dsimp only [L1Sq] at hMulEq
      omega
    exact ⟨F', t, k1 + k2, hKBound, st1.append st2, htpc, invT⟩

theorem run_sweepLoop {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (input : Input (layout bits inputCap workCap hi hw))
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (dictRows : Rows H) (large : 3 ≤ H.vertexCount)
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    (r : PaperB.OrderedReaderResult dictRows order size_order rank large)
    {s : State (layout bits inputCap workCap hi hw)}
    (inv0 : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      JumpForest.init
      (initial (orderedConfig dictRows large) (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1
        H.vertexCount) 0 s) :
    ∃ F' : JumpForest,
    ∃ t : State (layout bits inputCap workCap hi hw),
    ∃ states : List (State (layout bits inputCap workCap hi hw)),
    ∃ work : Nat,
      work ≤ 36 + 1200 * (H.vertexCount + H.arcCount) * (OracleContract.L H.vertexCount + 1) ^ 2 ∧
      run (sweepLoopPhase hi hw h8).code input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace (sweepLoopPhase hi hw h8).code input (Phase.initial s) states ⟨t, work⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 ∧
      t.pc = (sweepLoopPhase hi hw h8).haltPC ∧
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large)
        F' r.out H.vertexCount t := by
  let ph := sweepLoopPhase hi hw h8
  have hplBody : Placed ph.code 0 (sweepLoopBody (hi := hi) (hw := hw) h8) :=
    placed_of_phase_body (sweepLoopBody (hi := hi) (hw := hw) h8) (sweepLoopBody_nonHalt h8)
  have hCodeSz : ph.code.size = (sweepLoopBody (hi := hi) (hw := hw) h8).length + 1 := by
    simp [ph, sweepLoopPhase, mkPhase, Phase.ofLast]
  have hBodyBnd : (sweepLoopBody (hi := hi) (hw := hw) h8).length < ph.code.size := by omega
  have inv0' : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      JumpForest.init
      (initial (orderedConfig dictRows large) (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1
        H.vertexCount) 0 (Phase.initial s) :=
    inv0.of_scratch19 (fun _ _ => rfl)
  obtain ⟨F', t, k, hk, hSteps, htpc, invT⟩ :=
    run_sweepLoop_aux h8 H input hCap dictRows large r hBodyBnd hplBody H.vertexCount 0
      (Nat.zero_add _) JumpForest.init
      (initial (orderedConfig dictRows large) (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1
        H.vertexCount)
      r.log (Phase.initial s) inv0' rfl (by simpa only [List.drop_zero] using r.trace)
  have htHalt : t.pc = ph.haltPC := htpc
  have hh : ph.code[t.pc]? = some .halt := htHalt ▸ ph.haltAt
  have hRun : run ph.code input (k + 1) (Phase.initial s) = some ⟨t, k + 1⟩ :=
    hSteps.halts (step_halt_at hh)
  obtain ⟨states, ok⟩ := run_has_successfulTrace hRun
  have hFullW : sweepRemWeight rows order size_order 0 H.vertexCount (by omega) ≤
      H.vertexCount + H.arcCount :=
    sweepRemWeight_full_le rows order size_order inv0.stage1.nodup
  have hWorkLe : k + 1 ≤ 36 + 1200 * (H.vertexCount + H.arcCount) *
      (OracleContract.L H.vertexCount + 1) ^ 2 := by
    have hMul : 1200 * sweepRemWeight rows order size_order 0 H.vertexCount (by omega) *
        (OracleContract.L H.vertexCount + 1) ^ 2 ≤
        1200 * (H.vertexCount + H.arcCount) * (OracleContract.L H.vertexCount + 1) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hFullW)
    omega
  exact ⟨F', t, states, k + 1, hWorkLe, hRun, ok,
    ok.peak_eq, htHalt, invT⟩

end SweepLoopExec


end PaperB.RamForestProgram.Sweep
