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

/-! ### Stage 2c Finish-Staging Phase (`sweepStage2cPhase`, `run_sweepStage2c`) -/

section Stage2cProgram

private def stage2cCopyLoop {bits : Nat} (pcLoop pcExit : Nat) : List (Instr bits 15) :=
  [ .branchLt rRem rVal (pcLoop + 1) pcExit,
    .loadData rTmp rPtr,
    .storeData rClk rTmp,
    .add rPtr rPtr rOne,
    .add rClk rClk rOne,
    .add rRem rRem rOne,
    .goto pcLoop ]

private theorem stage2cCopyLoop_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (pcLoop pcExit : Nat) :
    (stage2cCopyLoop (bits := bits) pcLoop pcExit).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private theorem stage2cCopyLoop_length {bits : Nat} (pcLoop pcExit : Nat) :
    (stage2cCopyLoop (bits := bits) pcLoop pcExit).length = 7 := rfl

private def s2cSetup {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm rZero ⟨0, by omega⟩,
    .imm rOne ⟨1, by omega⟩ ] ++
  loadScratch h8 rClk slSource ++
  loadScratch h8 rPtr slDictBase ++
  loadScratch h8 rVal slDictCnt ++
  [ .mov rTmp rVal,
    .add rVal rVal rTmp,
    .add rVal rVal rTmp,
    .add rVal rVal rOne,
    .mov rOff rVal,
    .mov rRem rZero,
    .mov rChild rClk ]

private def s2cPrep2 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rPtr slBackFst ++
  loadScratch h8 rVal slN ++
  [ .add rVal rVal rOne,
    .add rOff rOff rVal,
    .mov rRem rZero ]

private def s2cPrep3 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rPtr slBackSnd ++
  loadScratch h8 rVal slN ++
  [ .add rVal rVal rOne,
    .add rOff rOff rVal,
    .mov rRem rZero ]

private def s2cPrep4 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rPtr slLabels ++
  loadScratch h8 rVal slN ++
  [ .add rOff rOff rVal,
    .mov rRem rZero ]

private def s2cPrep5 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  loadScratch h8 rCnt slNext ++
  [ .add rTmp rCnt rCnt,
    .add rStack rOff rTmp,
    .mov rClk rStack ] ++
  loadScratch h8 rPtr slParents ++
  [ .mov rVal rCnt,
    .mov rRem rZero ]

private def s2cFinish {bits : Nat} (_h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .mov rRem rOff,
    .add rTmp rCnt rCnt,
    .add rTin rStack rTmp,
    .add rTout rTin rCnt,
    .add rOff rTout rCnt,
    .add rChB rOff rCnt,
    .add rChB rChB rOne,
    .mov rCmd rZero,
    .mov rPtr rZero,
    .mov rClk rOne ]

private def stage2cBody {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  let pc1 := (s2cSetup h8).length
  let pc2 := pc1 + 7
  let pc3 := pc2 + (s2cPrep2 h8).length
  let pc4 := pc3 + 7
  let pc5 := pc4 + (s2cPrep3 h8).length
  let pc6 := pc5 + 7
  let pc7 := pc6 + (s2cPrep4 h8).length
  let pc8 := pc7 + 7
  let pc9 := pc8 + (s2cPrep5 h8).length
  let pc10 := pc9 + 7
  s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++
  s2cPrep2 h8 ++ stage2cCopyLoop pc3 pc4 ++
  s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6 ++
  s2cPrep4 h8 ++ stage2cCopyLoop pc7 pc8 ++
  s2cPrep5 h8 ++ stage2cCopyLoop pc9 pc10 ++
  s2cFinish h8

private theorem s2cSetup_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (s2cSetup (bits := bits) h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [s2cSetup, List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, nonHalt, Bool.and_self]

private theorem s2cPrep2_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (s2cPrep2 (bits := bits) h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [s2cPrep2, List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, nonHalt, Bool.and_self]

private theorem s2cPrep3_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (s2cPrep3 (bits := bits) h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [s2cPrep3, List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, nonHalt, Bool.and_self]

private theorem s2cPrep4_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (s2cPrep4 (bits := bits) h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [s2cPrep4, List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, nonHalt, Bool.and_self]

private theorem s2cPrep5_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (s2cPrep5 (bits := bits) h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [s2cPrep5, List.all_append, List.all_cons, List.all_nil,
    loadScratch_nonHalt, nonHalt, Bool.and_self]

private theorem s2cFinish_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (s2cFinish (bits := bits) h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [s2cFinish, List.all_cons, List.all_nil, nonHalt, Bool.and_self]

private theorem stage2cBody_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (stage2cBody (bits := bits) h8).all
      (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  unfold stage2cBody
  simp only [List.all_append, s2cSetup_nonHalt, s2cPrep2_nonHalt, s2cPrep3_nonHalt,
    s2cPrep4_nonHalt, s2cPrep5_nonHalt, s2cFinish_nonHalt, stage2cCopyLoop_nonHalt, Bool.and_self]

def sweepStage2cPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  mkPhase (stage2cBody h8) (stage2cBody_nonHalt h8)

end Stage2cProgram

section Stage2cExec

private theorem wordOption_ext {bits : Nat} {a b : Option (Word bits)}
    (h : a.map Fin.val = b.map Fin.val) : a = b := by
  cases a <;> cases b
  · rfl
  · cases h
  · cases h
  · exact congrArg some (Fin.ext (Option.some.inj h))

private theorem data_word_of_map {bits : Nat} {xs : Array (Word bits)} {j x : Nat}
    (h : (xs[j]?).map Fin.val = some x) :
    ∃ v : Word bits, xs[j]? = some v ∧ v.val = x := by
  cases hx : xs[j]? with
  | none => simp [hx] at h
  | some v => exact ⟨v, rfl, by simpa [hx] using h⟩

private theorem immNatAux_len_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst one : Fin 15) :
    ∀ f k : Nat, (immNatAux h8 dst one f k).length ≤ 1 + 2 * f
  | 0, k => by unfold immNatAux; split <;> simp
  | f + 1, k => by
    rw [immNatAux_succ]
    split
    · simp only [List.length_cons, List.length_nil]; omega
    · split <;>
      · simp only [List.length_append, List.length_cons, List.length_nil]
        have ih := immNatAux_len_le h8 dst one f (k / 2)
        omega

private theorem loadScratch_len_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) (dst : Fin 15) (sl : Nat) :
    (loadScratch h8 dst sl).length ≤ 12 := by
  unfold loadScratch immNat
  have h := immNatAux_len_le h8 rTmp rOne 5 sl
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

private theorem stage2cCopyLoop_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {pcLoop pcExit src0 dst0 len : Nat}
    (hBnd : pcLoop + 7 < code.size) (hExit : pcExit < code.size)
    (hpl : Placed code pcLoop (stage2cCopyLoop pcLoop pcExit))
    (hSrcCap : src0 + len ≤ workCap) (hDstCap : dst0 + len ≤ workCap)
    (hSrcFit : src0 + len < 2 ^ bits)
    (hDisj : src0 + len ≤ dst0 ∨ dst0 + len ≤ src0)
    (s0Data : Array (Word bits)) :
    ∀ (rem idx : Nat) (_hSum : idx + rem = len) (s : State (layout bits inputCap workCap hi hw)),
      s.pc = pcLoop →
      (reg s rZero).val = 0 → (reg s rOne).val = 1 →
      (reg s rPtr).val = src0 + idx →
      (reg s rClk).val = (dst0 + idx) % (2 ^ bits) →
      (reg s rRem).val = idx →
      (reg s rVal).val = len →
      (∀ j < idx, s.data[dst0 + j]? = s0Data[src0 + j]?) →
      (∀ j < len, s.data[src0 + j]? = s0Data[src0 + j]?) →
      (∀ w, (w < dst0 ∨ dst0 + idx ≤ w) → s.data[w]? = s0Data[w]?) →
      ∃ t : State (layout bits inputCap workCap hi hw), ∃ k : Nat,
        k ≤ 7 * rem + 1 ∧
        Steps code input k s t ∧
        t.pc = pcExit ∧
        (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
        (reg t rVal).val = len ∧
        (reg t rClk).val = (dst0 + len) % (2 ^ bits) ∧
        (∀ r : Fin 15, r ≠ rTmp → r ≠ rPtr → r ≠ rClk → r ≠ rRem → reg t r = reg s r) ∧
        (∀ j < len, t.data[dst0 + j]? = s0Data[src0 + j]?) ∧
        (∀ w, (w < dst0 ∨ dst0 + len ≤ w) → t.data[w]? = s0Data[w]?) := by
  intro rem
  induction rem with
  | zero =>
    intro idx hSum s hpc hz ho hptr hclk hrem hval hPref hSrcKeep hOutFrame
    have hidxEq : idx = len := by omega
    subst hidxEq
    obtain ⟨t, st, pct, kt, dt⟩ :=
      step_branchLt_false (input := input) (placed_fetch hpl (i := 0) rfl hpc)
        (by rw [hval, hrem]; exact Nat.le_refl _) hExit
    refine ⟨t, 1, by omega, Steps.cons st (Steps.zero _), pct,
      by rw [kt, hz], by rw [kt, ho], by rw [kt, hval], by rw [kt, hclk],
      fun r _ _ _ _ => kt r,
      fun j hj => by rw [dt]; exact hPref j hj,
      fun w hw0 => by rw [dt]; exact hOutFrame w hw0⟩
  | succ rem' ih =>
    intro idx hSum s hpc hz ho hptr hclk hrem hval hPref hSrcKeep hOutFrame
    have hLt : idx < len := by omega
    obtain ⟨s0, st0, pc0, k0, d0⟩ :=
      step_branchLt_true (input := input) (placed_fetch hpl (i := 0) rfl hpc)
        (by rw [hrem, hval]; exact hLt) (by omega)
    have hAddrSrc : src0 + idx < workCap := by omega
    have hWIdx : src0 + idx < s0.data.size := by rw [s0.data_size]; exact hAddrSrc
    let wv : Word bits := s0.data[src0 + idx]'hWIdx
    have hMemSrc : (s0.data[(reg s0 rPtr).val]?).map Fin.val = some wv.val := by
      rw [k0 rPtr, hptr, getElem?_pos s0.data (src0 + idx) hWIdx]; rfl
    have hWvEq : some wv = s0Data[src0 + idx]? := by
      have h0 : s0.data[src0 + idx]? = s.data[src0 + idx]? := by rw [d0]
      rw [← hSrcKeep idx hLt, ← h0, getElem?_pos s0.data (src0 + idx) hWIdx]
    obtain ⟨s1, st1, pc1, r1, k1, d1⟩ :=
      step_loadData_reg (input := input) (placed_fetch hpl (i := 1) rfl pc0)
        (by rw [pc0]; omega) (by rw [k0 rPtr, hptr]; exact hAddrSrc) hMemSrc
    have hDstMod : (dst0 + idx) % (2 ^ bits) = dst0 + idx :=
      Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by omega) hw)
    have hDstAddr : (reg s1 rClk).val = dst0 + idx := by
      rw [k1 _ (by decide), k0 rClk, hclk, hDstMod]
    obtain ⟨s2, st2, pc2, d2, k2⟩ :=
      step_storeData_at (input := input) (placed_fetch hpl (i := 2) rfl (by rw [pc1, pc0]))
        (by rw [pc1, pc0]; omega) (by rw [hDstAddr]; omega)
    have hrTmp1 : reg s1 rTmp = wv := by
      apply Fin.ext; exact r1
    have hd2At : s2.data[dst0 + idx]? = s0Data[src0 + idx]? := by
      rw [d2, Array.getElem?_set]
      simp only [hDstAddr, ↓reduceIte, hrTmp1]
      exact hWvEq
    have hd2Ne : ∀ w, w ≠ dst0 + idx → s2.data[w]? = s.data[w]? := by
      intro w hwNe
      rw [storeData_getElem?_ne _ d2 (by rw [hDstAddr]; exact Ne.symm hwNe), d1, d0]
    obtain ⟨s3, st3, pc3, r3, k3, d3⟩ :=
      step_add15_at (input := input) (placed_fetch hpl (i := 3) rfl (by rw [pc2, pc1, pc0]))
        (by rw [pc2, pc1, pc0]; omega)
    have hPtr3 : (reg s3 rPtr).val = src0 + (idx + 1) := by
      rw [r3, PaperB.WordOps.add_no_wrap _ _ (by
          rw [k2, k1 _ (by decide), k0 rPtr, hptr, k2, k1 _ (by decide), k0 rOne, ho]; omega),
        k2, k1 _ (by decide), k0 rPtr, hptr, k2, k1 _ (by decide), k0 rOne, ho]
      omega
    obtain ⟨s4, st4, pc4, r4, k4, d4⟩ :=
      step_add15_at (input := input) (placed_fetch hpl (i := 4) rfl (by rw [pc3, pc2, pc1, pc0]))
        (by rw [pc3, pc2, pc1, pc0]; omega)
    have hClk4 : (reg s4 rClk).val = (dst0 + (idx + 1)) % (2 ^ bits) := by
      rw [r4]
      change (((reg s3 rClk).val + (reg s3 rOne).val) % (2 ^ bits)) = (dst0 + (idx + 1)) % (2 ^ bits)
      rw [k3 _ (by decide), k2, k1 _ (by decide), k0 rClk, hclk,
        k3 _ (by decide), k2, k1 _ (by decide), k0 rOne, ho, Nat.mod_add_mod, Nat.add_assoc]
    obtain ⟨s5, st5, pc5, r5, k5, d5⟩ :=
      step_add15_at (input := input) (placed_fetch hpl (i := 5) rfl (by rw [pc4, pc3, pc2, pc1, pc0]))
        (by rw [pc4, pc3, pc2, pc1, pc0]; omega)
    have hRem5 : (reg s5 rRem).val = idx + 1 := by
      rw [r5, PaperB.WordOps.add_no_wrap _ _ (by
          rw [k4 _ (by decide), k3 _ (by decide), k2, k1 _ (by decide), k0 rRem, hrem,
            k4 _ (by decide), k3 _ (by decide), k2, k1 _ (by decide), k0 rOne, ho]
          omega),
        k4 _ (by decide), k3 _ (by decide), k2, k1 _ (by decide), k0 rRem, hrem,
        k4 _ (by decide), k3 _ (by decide), k2, k1 _ (by decide), k0 rOne, ho]
    have st6 := step_goto_at (input := input)
      (placed_fetch hpl (i := 6) rfl (by rw [pc5, pc4, pc3, pc2, pc1, pc0])) (by omega)
    let s6 : State (layout bits inputCap workCap hi hw) := { s5 with pc := pcLoop }
    have hd6 : s6.data = s2.data := by
      show s5.data = s2.data; rw [d5, d4, d3]
    have hPresRegs : ∀ r : Fin 15, r ≠ rTmp → r ≠ rPtr → r ≠ rClk → r ≠ rRem → reg s6 r = reg s r := by
      intro r hrT hrP hrC hrR
      show reg s5 r = reg s r
      rw [k5 _ hrR, k4 _ hrC, k3 _ hrP, k2, k1 _ hrT, k0]
    have hPref6 : ∀ j < idx + 1, s6.data[dst0 + j]? = s0Data[src0 + j]? := by
      intro j hj
      rw [hd6]
      by_cases hjEq : j = idx
      · subst hjEq; exact hd2At
      · rw [hd2Ne (dst0 + j) (by omega)]
        exact hPref j (by omega)
    have hSrcKeep6 : ∀ j < len, s6.data[src0 + j]? = s0Data[src0 + j]? := by
      intro j hj
      rw [hd6, hd2Ne (src0 + j) (by rcases hDisj with h | h <;> omega)]
      exact hSrcKeep j hj
    have hOut6 : ∀ w, (w < dst0 ∨ dst0 + (idx + 1) ≤ w) → s6.data[w]? = s0Data[w]? := by
      intro w hw0
      rw [hd6, hd2Ne w (by omega)]
      exact hOutFrame w (by rcases hw0 with h | h; exact Or.inl h; exact Or.inr (by omega))
    obtain ⟨t, kTail, hkTail, stTail, htpc, htz, hto, htv, htcl, hRegsTail, hPrefTail, hOutTail⟩ :=
      ih (idx + 1) (by omega) s6 rfl
        (by rw [hPresRegs rZero (by decide) (by decide) (by decide) (by decide), hz])
        (by rw [hPresRegs rOne (by decide) (by decide) (by decide) (by decide), ho])
        (by change (reg s5 rPtr).val = src0 + (idx + 1); rw [k5 _ (by decide), k4 _ (by decide), hPtr3])
        (by change (reg s5 rClk).val = (dst0 + (idx + 1)) % (2 ^ bits); rw [k5 _ (by decide), hClk4])
        hRem5
        (by change (reg s5 rVal).val = len; rw [k5 _ (by decide), k4 _ (by decide), k3 _ (by decide), k2, k1 _ (by decide), k0, hval])
        hPref6 hSrcKeep6 hOut6
    have stIter : Steps code input 7 s s6 :=
      Steps.cons st0 (Steps.cons st1 (Steps.cons st2 (Steps.cons st3
        (Steps.cons st4 (Steps.cons st5 (Steps.cons st6 (Steps.zero _)))))))
    refine ⟨t, 7 + kTail, by omega, stIter.append stTail, htpc, htz, hto, htv, htcl, ?_, hPrefTail, hOutTail⟩
    intro r hrT hrP hrC hrR
    exact (hRegsTail r hrT hrP hrC hrR).trans (hPresRegs r hrT hrP hrC hrR)

private theorem sweepSerialize_val_eq {bits : Nat} {H : LabelledQuotient}
    (s : PaperB.RetainedProperLoss.Columns H) (f : FlatPairDictionary.Fits bits s)
    (j : Nat) (hjSer : j < (FlatPairDictionary.serialize s f).size)
    (hjBound : j < 1 + s.dict.size + s.dict.size + s.slots.size) :
    ((FlatPairDictionary.serialize s f)[j]'hjSer).val =
      if h0 : j = 0 then s.dict.size
      else if h1 : j < 1 + s.dict.size then
        (s.dict[j - 1]'(by omega)).1
      else if h2 : j < 1 + 2 * s.dict.size then
        (s.dict[j - (1 + s.dict.size)]'(by omega)).2
      else (s.slots[j - (1 + 2 * s.dict.size)]?).getD 0 := by
  let ser := FlatPairDictionary.serialize s f
  have hRep := FlatPairDictionary.serialize_represents s f
  have getSame (k1 k2 : Nat) (h1 : k1 < ser.size) (h2 : k2 < ser.size) (e : k1 = k2) :
      (ser[k1]'h1) = (ser[k2]'h2) := by subst k2; rfl
  by_cases hj0 : j = 0
  · subst hj0
    simp only [↓reduceDIte]
    have hget0 : FlatPairDictionary.rowCount ser = (ser[0]'hjSer).val := by
      unfold FlatPairDictionary.rowCount
      rw [getElem?_pos _ 0 hjSer]
      rfl
    exact hget0.symm.trans hRep.rows
  · simp only [hj0, ↓reduceDIte]
    by_cases hj1 : j < 1 + s.dict.size
    · simp only [hj1, ↓reduceDIte]
      have hiD : j - 1 < s.dict.size := by omega
      have hfirst := hRep.first_eq (j - 1) (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hiD) hiD
      have hgetS : ((FlatPairDictionary.firstSlice ser hRep.valid).get (j - 1)
          (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hiD)).val = (ser[j]'hjSer).val := by
        unfold PaperB.PairLookup.ColumnReduction.Slice.get
        exact congrArg Fin.val (getSame _ _ _ _ (by show 1 + (j - 1) = j; omega))
      exact hgetS.symm.trans hfirst
    · simp only [hj1, ↓reduceDIte]
      by_cases hj2 : j < 1 + 2 * s.dict.size
      · simp only [hj2, ↓reduceDIte]
        have hiD : j - (1 + s.dict.size) < s.dict.size := by omega
        have hsec := hRep.second_eq (j - (1 + s.dict.size))
          (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hiD) hiD
        have hgetS : ((FlatPairDictionary.secondSlice ser hRep.valid).get (j - (1 + s.dict.size))
            (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hiD)).val = (ser[j]'hjSer).val := by
          unfold PaperB.PairLookup.ColumnReduction.Slice.get
          have hbase : (FlatPairDictionary.secondSlice ser hRep.valid).base.val = 1 + s.dict.size := by
            change FlatPairDictionary.secondBase (FlatPairDictionary.rowCount ser) = 1 + s.dict.size
            rw [hRep.rows]; rfl
          exact congrArg Fin.val (getSame _ _ _ _ (by rw [hbase]; omega))
        exact hgetS.symm.trans hsec
      · simp only [hj2, ↓reduceDIte]
        have hiS : j - (1 + 2 * s.dict.size) < s.slots.size := by omega
        have hsl := hRep.slot_eq (j - (1 + 2 * s.dict.size))
          (by rw [hRep.slot_len]; exact hiS) hiS
        have hgetS : ((FlatPairDictionary.slotSlice ser hRep.valid).get (j - (1 + 2 * s.dict.size))
            (by rw [hRep.slot_len]; exact hiS)).val = (ser[j]'hjSer).val := by
          unfold PaperB.PairLookup.ColumnReduction.Slice.get
          have hbase : (FlatPairDictionary.slotSlice ser hRep.valid).base.val = 1 + 2 * s.dict.size := by
            change FlatPairDictionary.slotBase (FlatPairDictionary.rowCount ser) = 1 + 2 * s.dict.size
            rw [hRep.rows]; unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase; omega
          exact congrArg Fin.val (getSame _ _ _ _ (by rw [hbase]; omega))
        exact hgetS.symm.trans hsl

private theorem array_getElem?_append_2 {α : Type} (a b : Array α) (j : Nat) :
    (a ++ b)[j]? = if j < a.size then a[j]? else b[j - a.size]? := by
  by_cases ha : j < a.size
  · have hab : j < (a ++ b).size := by simp only [Array.size_append]; omega
    rw [ite_eq_left ha, getElem?_pos (a ++ b) j hab, Array.getElem_append_left ha, getElem?_pos a j ha]
  · rw [ite_eq_right ha]
    by_cases hab : j < (a ++ b).size
    · have hb : j - a.size < b.size := by simp only [Array.size_append] at hab; omega
      rw [getElem?_pos (a ++ b) j hab, Array.getElem_append_right (by omega), getElem?_pos b _ hb]
    · have hb : ¬ (j - a.size < b.size) := by simp only [Array.size_append] at hab; omega
      rw [getElem?_neg (a ++ b) j hab, getElem?_neg b _ hb]

private theorem array_getElem?_append_4 {α : Type} (a b c d : Array α) (j : Nat)
    (_ : j < (a ++ b ++ c ++ d).size) :
    (a ++ b ++ c ++ d)[j]? =
      if j < a.size then a[j]?
      else if j < a.size + b.size then b[j - a.size]?
      else if j < a.size + b.size + c.size then c[j - (a.size + b.size)]?
      else d[j - (a.size + b.size + c.size)]? := by
  rw [array_getElem?_append_2 (a ++ b ++ c) d, array_getElem?_append_2 (a ++ b) c,
    array_getElem?_append_2 a b]
  simp only [Array.size_append]
  by_cases h1 : j < a.size
  · simp [h1, show j < a.size + b.size by omega, show j < a.size + b.size + c.size by omega]
  · by_cases h2 : j < a.size + b.size
    · simp [h1, h2, show j < a.size + b.size + c.size by omega]
    · by_cases h3 : j < a.size + b.size + c.size
      · simp [h1, h2, h3]
      · simp [h1, h2, h3]

private theorem stage2cBody_len_parts {bits : Nat} (h8 : 8 ≤ 2 ^ bits) :
    let pc1 := (s2cSetup h8).length
    let pc2 := pc1 + 7
    let pc3 := pc2 + (s2cPrep2 h8).length
    let pc4 := pc3 + 7
    let pc5 := pc4 + (s2cPrep3 h8).length
    let pc6 := pc5 + 7
    let pc7 := pc6 + (s2cPrep4 h8).length
    let pc8 := pc7 + 7
    let pc9 := pc8 + (s2cPrep5 h8).length
    let pc10 := pc9 + 7
    (stage2cBody (bits := bits) h8).length = pc10 + (s2cFinish h8).length := by
  unfold stage2cBody
  simp only [List.length_append, stage2cCopyLoop_length]

private theorem stage2cBody_len_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) :
    (stage2cBody (bits := bits) h8).length ≤ 220 := by
  have hL := stage2cBody_len_parts (bits := bits) h8
  have h1 : (s2cSetup (bits := bits) h8).length ≤ 45 := by
    unfold s2cSetup
    have a := loadScratch_len_le h8 rClk slSource
    have b := loadScratch_len_le h8 rPtr slDictBase
    have c := loadScratch_len_le h8 rVal slDictCnt
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h2 : (s2cPrep2 (bits := bits) h8).length ≤ 27 := by
    unfold s2cPrep2
    have a := loadScratch_len_le h8 rPtr slBackFst
    have b := loadScratch_len_le h8 rVal slN
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h3 : (s2cPrep3 (bits := bits) h8).length ≤ 27 := by
    unfold s2cPrep3
    have a := loadScratch_len_le h8 rPtr slBackSnd
    have b := loadScratch_len_le h8 rVal slN
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h4 : (s2cPrep4 (bits := bits) h8).length ≤ 26 := by
    unfold s2cPrep4
    have a := loadScratch_len_le h8 rPtr slLabels
    have b := loadScratch_len_le h8 rVal slN
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h5 : (s2cPrep5 (bits := bits) h8).length ≤ 29 := by
    unfold s2cPrep5
    have a := loadScratch_len_le h8 rCnt slNext
    have b := loadScratch_len_le h8 rPtr slParents
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  have h6 : (s2cFinish (bits := bits) h8).length ≤ 10 := by
    unfold s2cFinish
    simp only [List.length_cons, List.length_nil]
    omega
  dsimp only at hL
  omega

private theorem s2cSetup_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {src0 db0 dictCnt : Nat}
    (hBnd : (s2cSetup (bits := bits) h8).length < code.size)
    (hpl : Placed code 0 (s2cSetup (bits := bits) h8))
    (hScr17 : slSource < workCap) (hScr3 : slDictBase < workCap) (hScr4 : slDictCnt < workCap)
    (hFit : 1 + 3 * dictCnt < 2 ^ bits)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = 0)
    (hSrc : (s.data[slSource]?).map Fin.val = some src0)
    (hDB : (s.data[slDictBase]?).map Fin.val = some db0)
    (hDC : (s.data[slDictCnt]?).map Fin.val = some dictCnt) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (s2cSetup (bits := bits) h8).length s t ∧
      t.pc = (s2cSetup (bits := bits) h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rClk).val = src0 ∧ (reg t rPtr).val = db0 ∧
      (reg t rVal).val = 1 + 3 * dictCnt ∧ (reg t rOff).val = 1 + 3 * dictCnt ∧
      (reg t rRem).val = 0 ∧ (reg t rChild).val = src0 ∧ t.data = s.data := by
  let pc1 := (s2cSetup (bits := bits) h8).length
  let pA := 2 + (loadScratch h8 rClk slSource).length
  let pB := pA + (loadScratch h8 rPtr slDictBase).length
  let pC := pB + (loadScratch h8 rVal slDictCnt).length
  have hPc1Eq : pc1 = pC + 7 := by
    dsimp only [pc1, pC, pB, pA, s2cSetup]
    simp only [List.length_append, List.length_cons, List.length_nil]
  have hPc1Ge2 : 2 ≤ pc1 := by omega
  have hpl12 := placed_append_left hpl
  have hpl123 := placed_append_left hpl12
  have hpl1234 := placed_append_left hpl123
  have hplLS1 := placed_append_right hpl1234
  have hplLS2 := placed_append_right hpl123
  have hplLS3 := placed_append_right hpl12
  have hplEnd := placed_append_right hpl
  obtain ⟨sa, sta, pca, ra, ka, da⟩ := step_imm_at (input := input)
    (placed_fetch hpl (i := 0) rfl hpc) (by omega)
  obtain ⟨sb, stb, pcb, rb, kb, db⟩ := step_imm_at (input := input)
    (placed_fetch hpl (i := 1) rfl (by rw [pca, hpc])) (by rw [pca, hpc]; omega)
  have hzb : (reg sb rZero).val = 0 := by rw [kb _ (by decide), ra]
  have hob : (reg sb rOne).val = 1 := by rw [rb]
  obtain ⟨vSrc, hvSrc, hvSrcVal⟩ := data_word_of_map hSrc
  have hplLS1' : Placed code 2 (loadScratch h8 rClk slSource) := by
    simpa only [Nat.zero_add, List.length_cons, List.length_nil] using hplLS1
  obtain ⟨sc, stc, pcc, rc, dc, kc⟩ := loadScratch_steps h8 rClk slSource hScr17
    (by decide) (by decide) (by decide) (by rw [pcb, pca, hpc]) hplLS1'
    (by change pA < code.size; omega) hob (by rw [db, da]; exact hvSrc)
  have hzc : (reg sc rZero).val = 0 := by rw [kc _ (by decide) (by decide), hzb]
  have hoc : (reg sc rOne).val = 1 := by rw [kc _ (by decide) (by decide), hob]
  have hClkc : (reg sc rClk).val = src0 := by rw [rc, hvSrcVal]
  obtain ⟨vDB, hvDB, hvDBVal⟩ := data_word_of_map hDB
  have hplLS2' : Placed code pA (loadScratch h8 rPtr slDictBase) := by
    have hl : 0 + ([Instr.imm rZero ⟨0, by omega⟩, Instr.imm rOne ⟨1, by omega⟩] ++
        loadScratch h8 rClk slSource).length = pA := by
      simp only [pA, List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    rwa [hl] at hplLS2
  obtain ⟨sd, std, pcd, rd, dd, kd⟩ := loadScratch_steps h8 rPtr slDictBase hScr3
    (by decide) (by decide) (by decide) (by rw [pcc]) hplLS2'
    (by dsimp only [pC, pB] at hPc1Eq; omega) hoc (by rw [dc, db, da]; exact hvDB)
  have hzd : (reg sd rZero).val = 0 := by rw [kd _ (by decide) (by decide), hzc]
  have hod : (reg sd rOne).val = 1 := by rw [kd _ (by decide) (by decide), hoc]
  have hClkd : (reg sd rClk).val = src0 := by rw [kd _ (by decide) (by decide), hClkc]
  have hPtrd : (reg sd rPtr).val = db0 := by rw [rd, hvDBVal]
  obtain ⟨vDC, hvDC, hvDCVal⟩ := data_word_of_map hDC
  have hplLS3' : Placed code pB (loadScratch h8 rVal slDictCnt) := by
    have hl : 0 + ([Instr.imm rZero ⟨0, by omega⟩, Instr.imm rOne ⟨1, by omega⟩] ++
        loadScratch h8 rClk slSource ++ loadScratch h8 rPtr slDictBase).length = pB := by
      simp only [pB, pA, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc]
      omega
    rwa [hl] at hplLS3
  obtain ⟨se, ste, pce, re, de, ke⟩ := loadScratch_steps h8 rVal slDictCnt hScr4
    (by decide) (by decide) (by decide) (by rw [pcd]) hplLS3'
    (by omega) hod (by rw [dd, dc, db, da]; exact hvDC)
  have hze : (reg se rZero).val = 0 := by rw [ke _ (by decide) (by decide), hzd]
  have hoe : (reg se rOne).val = 1 := by rw [ke _ (by decide) (by decide), hod]
  have hClke : (reg se rClk).val = src0 := by rw [ke _ (by decide) (by decide), hClkd]
  have hPtre : (reg se rPtr).val = db0 := by rw [ke _ (by decide) (by decide), hPtrd]
  have hVale : (reg se rVal).val = dictCnt := by rw [re, hvDCVal]
  have hplEnd' : Placed code pC [.mov rTmp rVal, .add rVal rVal rTmp, .add rVal rVal rTmp,
      .add rVal rVal rOne, .mov rOff rVal, .mov rRem rZero, .mov rChild rClk] := by
    have hl : 0 + ([Instr.imm rZero ⟨0, by omega⟩, Instr.imm rOne ⟨1, by omega⟩] ++
        loadScratch h8 rClk slSource ++ loadScratch h8 rPtr slDictBase ++
        loadScratch h8 rVal slDictCnt).length = pC := by
      simp only [pC, pB, pA, List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_assoc]
      omega
    rwa [hl] at hplEnd
  have hPCEq : se.pc = pC := by rw [pce]
  obtain ⟨sf, stf, pcf, rf, kf, df⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 0) rfl hPCEq) (by rw [hPCEq]; omega)
  obtain ⟨sg, stg, pcg, rg, kg, dg⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 1) rfl (by rw [pcf, hPCEq])) (by rw [pcf, hPCEq]; omega)
  have hValG : (reg sg rVal).val = 2 * dictCnt := by
    rw [rg, PaperB.WordOps.add_no_wrap _ _ (by rw [kf _ (by decide), hVale, rf, hVale]; omega),
      kf _ (by decide), hVale, rf, hVale]; omega
  obtain ⟨sh, sth, pch, rh, kh, dh⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 2) rfl (by rw [pcg, pcf, hPCEq])) (by rw [pcg, pcf, hPCEq]; omega)
  have hValH : (reg sh rVal).val = 3 * dictCnt := by
    rw [rh, PaperB.WordOps.add_no_wrap _ _ (by rw [hValG, kg _ (by decide), rf, hVale]; omega),
      hValG, kg _ (by decide), rf, hVale]; omega
  obtain ⟨si, sti, pci, ri, ki, di⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 3) rfl (by rw [pch, pcg, pcf, hPCEq])) (by rw [pch, pcg, pcf, hPCEq]; omega)
  have hValI : (reg si rVal).val = 1 + 3 * dictCnt := by
    rw [ri, PaperB.WordOps.add_no_wrap _ _ (by rw [hValH, kh _ (by decide), kg _ (by decide), kf _ (by decide), hoe]; omega),
      hValH, kh _ (by decide), kg _ (by decide), kf _ (by decide), hoe]; omega
  obtain ⟨sj, stj, pcj, rj, kj, dj⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 4) rfl (by rw [pci, pch, pcg, pcf, hPCEq])) (by rw [pci, pch, pcg, pcf, hPCEq]; omega)
  obtain ⟨sk, stk, pck, rk, kk, dk⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 5) rfl (by rw [pcj, pci, pch, pcg, pcf, hPCEq])) (by rw [pcj, pci, pch, pcg, pcf, hPCEq]; omega)
  obtain ⟨sl, stl, pcl, rl, kl, dl⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 6) rfl (by rw [pck, pcj, pci, pch, pcg, pcf, hPCEq])) (by rw [pck, pcj, pci, pch, pcg, pcf, hPCEq]; omega)
  refine ⟨sl, ?_, ?_,
    by rw [kl _ (by decide), kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hze],
    by rw [kl _ (by decide), kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hoe],
    by rw [kl _ (by decide), kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hClke],
    by rw [kl _ (by decide), kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hPtre],
    by rw [kl _ (by decide), kk _ (by decide), kj _ (by decide), hValI],
    by rw [kl _ (by decide), kk _ (by decide), rj, hValI],
    by rw [kl _ (by decide), rk, kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hze],
    by rw [rl, kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hClke],
    by rw [dl, dk, dj, di, dh, dg, df, de, dd, dc, db, da]⟩
  · change Steps code input pc1 s sl
    rw [hPc1Eq]
    exact ((((Steps.cons sta (Steps.cons stb (.zero _))).append stc).append std).append ste).append
      (Steps.cons stf (Steps.cons stg (Steps.cons sth (Steps.cons sti (Steps.cons stj (Steps.cons stk (Steps.cons stl (.zero _))))))))
  · rw [pcl, pck, pcj, pci, pch, pcg, pcf, hPCEq]; omega

private theorem s2cPrepBack_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry slPtr ptrVal n offPrev clkVal childVal : Nat}
    (hSlPtr : slPtr < workCap) (hSlPtr30 : slPtr < 32) (hSlN : slN < workCap)
    (hBnd : entry + (loadScratch h8 rPtr slPtr ++ loadScratch h8 rVal slN ++
      [Instr.add rVal rVal rOne, Instr.add rOff rOff rVal, Instr.mov rRem rZero]).length < code.size)
    (hpl : Placed code entry (loadScratch h8 rPtr slPtr ++ loadScratch h8 rVal slN ++
      [Instr.add rVal rVal rOne, Instr.add rOff rOff rVal, Instr.mov rRem rZero]))
    (hFit : offPrev + (n + 1) < 2 ^ bits)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hClk : (reg s rClk).val = clkVal) (hOff : (reg s rOff).val = offPrev)
    (hChild : (reg s rChild).val = childVal)
    (hPtr : (s.data[slPtr]?).map Fin.val = some ptrVal)
    (hN : (s.data[slN]?).map Fin.val = some n) :
    let prog := loadScratch h8 rPtr slPtr ++ loadScratch h8 rVal slN ++
      [.add rVal rVal rOne, .add rOff rOff rVal, .mov rRem rZero]
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input prog.length s t ∧ t.pc = entry + prog.length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rClk).val = clkVal ∧ (reg t rPtr).val = ptrVal ∧
      (reg t rVal).val = n + 1 ∧ (reg t rOff).val = offPrev + (n + 1) ∧
      (reg t rRem).val = 0 ∧ (reg t rChild).val = childVal ∧ t.data = s.data := by
  let prog := loadScratch h8 rPtr slPtr ++ loadScratch h8 rVal slN ++
    [.add rVal rVal rOne, .add rOff rOff rVal, .mov rRem rZero]
  let pA := entry + (loadScratch h8 rPtr slPtr).length
  let pB := pA + (loadScratch h8 rVal slN).length
  have hProgLen : prog.length = (loadScratch h8 rPtr slPtr).length + (loadScratch h8 rVal slN).length + 3 := by
    dsimp only [prog]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hBnd' : pB + 3 < code.size := by
    have h1 := hBnd; change entry + prog.length < code.size at h1; rw [hProgLen] at h1
    dsimp only [pB, pA]; omega
  have hpl12 := placed_append_left hpl
  have hplLS1 := placed_append_left hpl12
  have hplLS2 := placed_append_right hpl12
  have hplEnd := placed_append_right hpl
  obtain ⟨vP, hvP, hvPVal⟩ := data_word_of_map hPtr
  obtain ⟨sa, sta, pca, ra, da, ka⟩ := loadScratch_steps h8 rPtr slPtr hSlPtr hSlPtr30
    (by decide) (by decide) hpc hplLS1 (by dsimp only [pB] at hBnd'; omega) ho hvP
  have hza : (reg sa rZero).val = 0 := by rw [ka _ (by decide) (by decide), hz]
  have hoa : (reg sa rOne).val = 1 := by rw [ka _ (by decide) (by decide), ho]
  have hClka : (reg sa rClk).val = clkVal := by rw [ka _ (by decide) (by decide), hClk]
  have hOffa : (reg sa rOff).val = offPrev := by rw [ka _ (by decide) (by decide), hOff]
  have hPtra : (reg sa rPtr).val = ptrVal := by rw [ra, hvPVal]
  have hChilda : (reg sa rChild).val = childVal := by rw [ka _ (by decide) (by decide), hChild]
  obtain ⟨vN, hvN, hvNVal⟩ := data_word_of_map hN
  have hplLS2' : Placed code pA (loadScratch h8 rVal slN) := hplLS2
  obtain ⟨sb, stb, pcb, rb, db, kb⟩ := loadScratch_steps h8 rVal slN hSlN (by decide)
    (by decide) (by decide) (by rw [pca]) hplLS2' (by omega) hoa (by rw [da]; exact hvN)
  have hzb : (reg sb rZero).val = 0 := by rw [kb _ (by decide) (by decide), hza]
  have hob : (reg sb rOne).val = 1 := by rw [kb _ (by decide) (by decide), hoa]
  have hClkb : (reg sb rClk).val = clkVal := by rw [kb _ (by decide) (by decide), hClka]
  have hPtrb : (reg sb rPtr).val = ptrVal := by rw [kb _ (by decide) (by decide), hPtra]
  have hOffb : (reg sb rOff).val = offPrev := by rw [kb _ (by decide) (by decide), hOffa]
  have hChildb : (reg sb rChild).val = childVal := by rw [kb _ (by decide) (by decide), hChilda]
  have hValb : (reg sb rVal).val = n := by rw [rb, hvNVal]
  have hplEnd' : Placed code pB [.add rVal rVal rOne, .add rOff rOff rVal, .mov rRem rZero] := by
    have hl : entry + (loadScratch h8 rPtr slPtr ++ loadScratch h8 rVal slN).length = pB := by
      simp only [pB, pA, List.length_append, Nat.add_assoc]
    rwa [hl] at hplEnd
  have hPCEq : sb.pc = pB := by rw [pcb]
  obtain ⟨sc, stc, pcc, rc, kc, dc⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 0) rfl hPCEq) (by rw [hPCEq]; omega)
  have hValc : (reg sc rVal).val = n + 1 := by
    rw [rc, PaperB.WordOps.add_no_wrap _ _ (by rw [hValb, hob]; omega), hValb, hob]
  obtain ⟨sd, std, pcd, rd, kd, dd⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 1) rfl (by rw [pcc, hPCEq])) (by rw [pcc, hPCEq]; omega)
  have hOffd : (reg sd rOff).val = offPrev + (n + 1) := by
    rw [rd, PaperB.WordOps.add_no_wrap _ _ (by rw [kc _ (by decide), hOffb, hValc]; omega),
      kc _ (by decide), hOffb, hValc]
  obtain ⟨se, ste, pce, re, ke, de⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 2) rfl (by rw [pcd, pcc, hPCEq])) (by rw [pcd, pcc, hPCEq]; omega)
  refine ⟨se, ?_, ?_,
    by rw [ke _ (by decide), kd _ (by decide), kc _ (by decide), hzb],
    by rw [ke _ (by decide), kd _ (by decide), kc _ (by decide), hob],
    by rw [ke _ (by decide), kd _ (by decide), kc _ (by decide), hClkb],
    by rw [ke _ (by decide), kd _ (by decide), kc _ (by decide), hPtrb],
    by rw [ke _ (by decide), kd _ (by decide), hValc],
    by rw [ke _ (by decide), hOffd],
    by rw [re, kd _ (by decide), kc _ (by decide), hzb],
    by rw [ke _ (by decide), kd _ (by decide), kc _ (by decide), hChildb],
    by rw [de, dd, dc, db, da]⟩
  · rw [hProgLen]; exact (sta.append stb).append (Steps.cons stc (Steps.cons std (Steps.cons ste (.zero _))))
  · rw [pce, pcd, pcc, hPCEq]; change pB + 3 = entry + prog.length; simp only [pB, pA, hProgLen, Nat.add_assoc]

private theorem s2cPrep4_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry labVal n offPrev clkVal childVal : Nat}
    (hSlLab : slLabels < workCap) (hSlN : slN < workCap)
    (hBnd : entry + (s2cPrep4 (bits := bits) h8).length < code.size)
    (hpl : Placed code entry (s2cPrep4 (bits := bits) h8))
    (hFit : offPrev + n < 2 ^ bits)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hClk : (reg s rClk).val = clkVal) (hOff : (reg s rOff).val = offPrev)
    (hChild : (reg s rChild).val = childVal)
    (hLab : (s.data[slLabels]?).map Fin.val = some labVal)
    (hN : (s.data[slN]?).map Fin.val = some n) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (s2cPrep4 (bits := bits) h8).length s t ∧
      t.pc = entry + (s2cPrep4 (bits := bits) h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rClk).val = clkVal ∧ (reg t rPtr).val = labVal ∧
      (reg t rVal).val = n ∧ (reg t rOff).val = offPrev + n ∧
      (reg t rRem).val = 0 ∧ (reg t rChild).val = childVal ∧ t.data = s.data := by
  let prog := s2cPrep4 (bits := bits) h8
  let pA := entry + (loadScratch h8 rPtr slLabels).length
  let pB := pA + (loadScratch h8 rVal slN).length
  have hProgLen : prog.length = (loadScratch h8 rPtr slLabels).length + (loadScratch h8 rVal slN).length + 2 := by
    dsimp only [prog, s2cPrep4]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hBnd' : pB + 2 < code.size := by
    have h1 := hBnd; change entry + prog.length < code.size at h1; rw [hProgLen] at h1
    dsimp only [pB, pA]; omega
  have hpl12 := placed_append_left hpl
  have hplLS1 := placed_append_left hpl12
  have hplLS2 := placed_append_right hpl12
  have hplEnd := placed_append_right hpl
  obtain ⟨vL, hvL, hvLVal⟩ := data_word_of_map hLab
  obtain ⟨sa, sta, pca, ra, da, ka⟩ := loadScratch_steps h8 rPtr slLabels hSlLab (by decide)
    (by decide) (by decide) hpc hplLS1 (by dsimp only [pB] at hBnd'; omega) ho hvL
  have hza : (reg sa rZero).val = 0 := by rw [ka _ (by decide) (by decide), hz]
  have hoa : (reg sa rOne).val = 1 := by rw [ka _ (by decide) (by decide), ho]
  have hClka : (reg sa rClk).val = clkVal := by rw [ka _ (by decide) (by decide), hClk]
  have hOffa : (reg sa rOff).val = offPrev := by rw [ka _ (by decide) (by decide), hOff]
  have hPtra : (reg sa rPtr).val = labVal := by rw [ra, hvLVal]
  have hChilda : (reg sa rChild).val = childVal := by rw [ka _ (by decide) (by decide), hChild]
  obtain ⟨vN, hvN, hvNVal⟩ := data_word_of_map hN
  have hplLS2' : Placed code pA (loadScratch h8 rVal slN) := hplLS2
  obtain ⟨sb, stb, pcb, rb, db, kb⟩ := loadScratch_steps h8 rVal slN hSlN (by decide)
    (by decide) (by decide) (by rw [pca]) hplLS2' (by omega) hoa (by rw [da]; exact hvN)
  have hzb : (reg sb rZero).val = 0 := by rw [kb _ (by decide) (by decide), hza]
  have hob : (reg sb rOne).val = 1 := by rw [kb _ (by decide) (by decide), hoa]
  have hClkb : (reg sb rClk).val = clkVal := by rw [kb _ (by decide) (by decide), hClka]
  have hPtrb : (reg sb rPtr).val = labVal := by rw [kb _ (by decide) (by decide), hPtra]
  have hOffb : (reg sb rOff).val = offPrev := by rw [kb _ (by decide) (by decide), hOffa]
  have hChildb : (reg sb rChild).val = childVal := by rw [kb _ (by decide) (by decide), hChilda]
  have hValb : (reg sb rVal).val = n := by rw [rb, hvNVal]
  have hplEnd' : Placed code pB [.add rOff rOff rVal, .mov rRem rZero] := by
    have hl : entry + (loadScratch h8 rPtr slLabels ++ loadScratch h8 rVal slN).length = pB := by
      simp only [pB, pA, List.length_append, Nat.add_assoc]
    rwa [hl] at hplEnd
  have hPCEq : sb.pc = pB := by rw [pcb]
  obtain ⟨sc, stc, pcc, rc, kc, dc⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 0) rfl hPCEq) (by rw [hPCEq]; omega)
  have hOffc : (reg sc rOff).val = offPrev + n := by
    rw [rc, PaperB.WordOps.add_no_wrap _ _ (by rw [hOffb, hValb]; exact hFit), hOffb, hValb]
  obtain ⟨sd, std, pcd, rd, kd, dd⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 1) rfl (by rw [pcc, hPCEq])) (by rw [pcc, hPCEq]; omega)
  refine ⟨sd, ?_, ?_,
    by rw [kd _ (by decide), kc _ (by decide), hzb],
    by rw [kd _ (by decide), kc _ (by decide), hob],
    by rw [kd _ (by decide), kc _ (by decide), hClkb],
    by rw [kd _ (by decide), kc _ (by decide), hPtrb],
    by rw [kd _ (by decide), kc _ (by decide), hValb],
    by rw [kd _ (by decide), hOffc],
    by rw [rd, kc _ (by decide), hzb],
    by rw [kd _ (by decide), kc _ (by decide), hChildb],
    by rw [dd, dc, db, da]⟩
  · change Steps code input prog.length s sd
    rw [hProgLen]; exact (sta.append stb).append (Steps.cons stc (Steps.cons std (.zero _)))
  · rw [pcd, pcc, hPCEq]; change pB + 2 = entry + prog.length; simp only [pB, pA, hProgLen, Nat.add_assoc]

private theorem s2cPrep5_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry nNext parVal prefixLen childVal : Nat}
    (hSlNx : slNext < workCap) (hSlPar : slParents < workCap)
    (hBnd : entry + (s2cPrep5 (bits := bits) h8).length < code.size)
    (hpl : Placed code entry (s2cPrep5 (bits := bits) h8))
    (hArenaFit : prefixLen + 2 * nNext < 2 ^ bits)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hOff : (reg s rOff).val = prefixLen)
    (hChild : (reg s rChild).val = childVal)
    (hNx : (s.data[slNext]?).map Fin.val = some nNext)
    (hPar : (s.data[slParents]?).map Fin.val = some parVal) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (s2cPrep5 (bits := bits) h8).length s t ∧
      t.pc = entry + (s2cPrep5 (bits := bits) h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rCnt).val = nNext ∧ (reg t rStack).val = prefixLen + 2 * nNext ∧
      (reg t rClk).val = prefixLen + 2 * nNext ∧ (reg t rPtr).val = parVal ∧
      (reg t rVal).val = nNext ∧ (reg t rOff).val = prefixLen ∧
      (reg t rRem).val = 0 ∧ (reg t rChild).val = childVal ∧ t.data = s.data := by
  let prog := s2cPrep5 (bits := bits) h8
  let pA := entry + (loadScratch h8 rCnt slNext).length
  let pB := pA + 3
  let pC := pB + (loadScratch h8 rPtr slParents).length
  have hProgLen : prog.length = (loadScratch h8 rCnt slNext).length + 3 + (loadScratch h8 rPtr slParents).length + 2 := by
    dsimp only [prog, s2cPrep5]; simp only [List.length_append, List.length_cons, List.length_nil]
  have hBnd' : pC + 2 < code.size := by
    have h1 := hBnd; change entry + prog.length < code.size at h1; rw [hProgLen] at h1
    dsimp only [pC, pB, pA]; omega
  have hpl12 := placed_append_left hpl
  have hpl123 := placed_append_left hpl12
  have hplLS1 := placed_append_left hpl123
  have hplMid := placed_append_right hpl123
  have hplLS2 := placed_append_right hpl12
  have hplEnd := placed_append_right hpl
  obtain ⟨vNx, hvNx, hvNxVal⟩ := data_word_of_map hNx
  obtain ⟨sa, sta, pca, ra, da, ka⟩ := loadScratch_steps h8 rCnt slNext hSlNx (by decide)
    (by decide) (by decide) hpc hplLS1 (by dsimp only [pC, pB] at hBnd'; omega) ho hvNx
  have hza : (reg sa rZero).val = 0 := by rw [ka _ (by decide) (by decide), hz]
  have hoa : (reg sa rOne).val = 1 := by rw [ka _ (by decide) (by decide), ho]
  have hOffa : (reg sa rOff).val = prefixLen := by rw [ka _ (by decide) (by decide), hOff]
  have hChilda : (reg sa rChild).val = childVal := by rw [ka _ (by decide) (by decide), hChild]
  have hCnta : (reg sa rCnt).val = nNext := by rw [ra, hvNxVal]
  have hplMid' : Placed code pA [.add rTmp rCnt rCnt, .add rStack rOff rTmp, .mov rClk rStack] := hplMid
  obtain ⟨sb, stb, pcb, rb, kb, db⟩ := step_add15_at (input := input)
    (placed_fetch hplMid' (i := 0) rfl pca) (by rw [pca]; dsimp only [pC, pB] at hBnd'; omega)
  have hTmpb : (reg sb rTmp).val = 2 * nNext := by
    rw [rb, PaperB.WordOps.add_no_wrap _ _ (by rw [hCnta]; omega), hCnta]; omega
  obtain ⟨sc, stc, pcc, rc, kc, dc⟩ := step_add15_at (input := input)
    (placed_fetch hplMid' (i := 1) rfl (by rw [pcb, pca])) (by rw [pcb, pca]; dsimp only [pC, pB] at hBnd'; omega)
  have hStackc : (reg sc rStack).val = prefixLen + 2 * nNext := by
    rw [rc, PaperB.WordOps.add_no_wrap _ _ (by rw [kb _ (by decide), hOffa, hTmpb]; exact hArenaFit),
      kb _ (by decide), hOffa, hTmpb]
  obtain ⟨sd, std, pcd, rd, kd, dd⟩ := step_mov_at (input := input)
    (placed_fetch hplMid' (i := 2) rfl (by rw [pcc, pcb, pca])) (by rw [pcc, pcb, pca]; dsimp only [pC, pB] at hBnd'; omega)
  have hzd : (reg sd rZero).val = 0 := by rw [kd _ (by decide), kc _ (by decide), kb _ (by decide), hza]
  have hod : (reg sd rOne).val = 1 := by rw [kd _ (by decide), kc _ (by decide), kb _ (by decide), hoa]
  have hCntd : (reg sd rCnt).val = nNext := by rw [kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnta]
  have hOffd : (reg sd rOff).val = prefixLen := by rw [kd _ (by decide), kc _ (by decide), kb _ (by decide), hOffa]
  have hStackd : (reg sd rStack).val = prefixLen + 2 * nNext := by rw [kd _ (by decide), hStackc]
  have hClkd : (reg sd rClk).val = prefixLen + 2 * nNext := by rw [rd, hStackc]
  have hChildd : (reg sd rChild).val = childVal := by rw [kd _ (by decide), kc _ (by decide), kb _ (by decide), hChilda]
  have hplLS2' : Placed code pB (loadScratch h8 rPtr slParents) := by
    have hl : entry + (loadScratch h8 rCnt slNext ++
        [Instr.add rTmp rCnt rCnt, Instr.add rStack rOff rTmp, Instr.mov rClk rStack]).length = pB := by
      simp only [pB, pA, List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]
    rwa [hl] at hplLS2
  obtain ⟨vPar, hvPar, hvParVal⟩ := data_word_of_map hPar
  obtain ⟨se, ste, pce, re, de, ke⟩ := loadScratch_steps h8 rPtr slParents hSlPar (by decide)
    (by decide) (by decide) (by rw [pcd, pcc, pcb, pca]) hplLS2'
    (by omega) hod (by rw [dd, dc, db, da]; exact hvPar)
  have hplEnd' : Placed code pC [.mov rVal rCnt, .mov rRem rZero] := by
    have hl : entry + (loadScratch h8 rCnt slNext ++
        [Instr.add rTmp rCnt rCnt, Instr.add rStack rOff rTmp, Instr.mov rClk rStack] ++
        loadScratch h8 rPtr slParents).length = pC := by
      simp only [pC, pB, pA, List.length_append, List.length_cons, List.length_nil, Nat.add_assoc]
      omega
    rwa [hl] at hplEnd
  have hPCEqC : se.pc = pC := by rw [pce]
  obtain ⟨sf, stf, pcf, rf, kf, df⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 0) rfl hPCEqC) (by rw [hPCEqC]; omega)
  obtain ⟨sg, stg, pcg, rg, kg, dg⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 1) rfl (by rw [pcf, hPCEqC])) (by rw [pcf, hPCEqC]; omega)
  refine ⟨sg, ?_, ?_,
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hzd],
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hod],
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hCntd],
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hStackd],
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hClkd],
    by rw [kg _ (by decide), kf _ (by decide), re, hvParVal],
    by rw [kg _ (by decide), rf, ke _ (by decide) (by decide), hCntd],
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hOffd],
    by rw [rg, kf _ (by decide), ke _ (by decide) (by decide), hzd],
    by rw [kg _ (by decide), kf _ (by decide), ke _ (by decide) (by decide), hChildd],
    by rw [dg, df, de, dd, dc, db, da]⟩
  · change Steps code input prog.length s sg
    rw [hProgLen]
    exact ((sta.append (Steps.cons stb (Steps.cons stc (Steps.cons std (.zero _))))).append ste).append
      (Steps.cons stf (Steps.cons stg (.zero _)))
  · rw [pcg, pcf, hPCEqC]; change pC + 2 = entry + prog.length; simp only [pC, pB, pA, hProgLen, Nat.add_assoc]

private theorem s2cFinish_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {entry srcVal prefixLen nNext arenaBase : Nat}
    (hBnd : entry + (s2cFinish (bits := bits) h8).length < code.size)
    (hpl : Placed code entry (s2cFinish (bits := bits) h8))
    (hEndFit : arenaBase + 5 * nNext + 1 < 2 ^ bits)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry)
    (hz : (reg s rZero).val = 0) (ho : (reg s rOne).val = 1)
    (hCnt : (reg s rCnt).val = nNext) (hStack : (reg s rStack).val = arenaBase)
    (hOff : (reg s rOff).val = prefixLen)
    (hChild : (reg s rChild).val = srcVal) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (s2cFinish (bits := bits) h8).length s t ∧
      t.pc = entry + (s2cFinish (bits := bits) h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t cmd).val = 0 ∧ (reg t count).val = nNext ∧
      (reg t registers.stackBase).val = arenaBase ∧
      (reg t tinBase).val = arenaBase + 2 * nNext ∧
      (reg t toutBase).val = arenaBase + 3 * nNext ∧
      (reg t offsetBase).val = arenaBase + 4 * nNext ∧
      (reg t childrenBase).val = arenaBase + 5 * nNext + 1 ∧
      (reg t registers.ptr).val = 0 ∧ (reg t clk).val = 1 ∧
      (reg t registers.childBase).val = srcVal ∧
      (reg t registers.remain).val = prefixLen ∧
      t.data = s.data := by
  let prog := s2cFinish (bits := bits) h8
  have hProgLen : prog.length = 10 := by
    dsimp only [prog, s2cFinish]; simp only [List.length_cons, List.length_nil]
  have hBnd' : entry + 10 < code.size := by
    have h1 := hBnd; change entry + prog.length < code.size at h1; rw [hProgLen] at h1; exact h1
  have hplEnd' : Placed code entry
      [.mov rRem rOff, .add rTmp rCnt rCnt, .add rTin rStack rTmp, .add rTout rTin rCnt,
       .add rOff rTout rCnt, .add rChB rOff rCnt, .add rChB rChB rOne,
       .mov rCmd rZero, .mov rPtr rZero, .mov rClk rOne] := hpl
  obtain ⟨sb, stb, pcb, rb, kb, db⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 0) rfl hpc) (by rw [hpc]; omega)
  have hRemB : (reg sb rRem).val = prefixLen := by rw [rb, hOff]
  obtain ⟨sc, stc, pcc, rc, kc, dc⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 1) rfl (by rw [pcb, hpc])) (by rw [pcb, hpc]; omega)
  have hTmpC : (reg sc rTmp).val = 2 * nNext := by
    rw [rc, PaperB.WordOps.add_no_wrap _ _ (by rw [kb _ (by decide), hCnt]; omega),
      kb _ (by decide), hCnt]; omega
  obtain ⟨sd, std, pcd, rd, kd, dd⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 2) rfl (by rw [pcc, pcb, hpc])) (by rw [pcc, pcb, hpc]; omega)
  have hTinD : (reg sd rTin).val = arenaBase + 2 * nNext := by
    rw [rd, PaperB.WordOps.add_no_wrap _ _ (by rw [kc _ (by decide), kb _ (by decide), hStack, hTmpC]; omega),
      kc _ (by decide), kb _ (by decide), hStack, hTmpC]
  obtain ⟨se, ste, pce, re, ke, de⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 3) rfl (by rw [pcd, pcc, pcb, hpc])) (by rw [pcd, pcc, pcb, hpc]; omega)
  have hToutE : (reg se rTout).val = arenaBase + 3 * nNext := by
    rw [re, PaperB.WordOps.add_no_wrap _ _ (by
        rw [hTinD, kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt]; omega),
      hTinD, kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt]; omega
  obtain ⟨sf, stf, pcf, rf, kf, df⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 4) rfl (by rw [pce, pcd, pcc, pcb, hpc])) (by rw [pce, pcd, pcc, pcb, hpc]; omega)
  have hOffF : (reg sf rOff).val = arenaBase + 4 * nNext := by
    rw [rf, PaperB.WordOps.add_no_wrap _ _ (by
        rw [hToutE, ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt]; omega),
      hToutE, ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt]; omega
  obtain ⟨sg, stg, pcg, rg, kg, dg⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 5) rfl (by rw [pcf, pce, pcd, pcc, pcb, hpc])) (by rw [pcf, pce, pcd, pcc, pcb, hpc]; omega)
  have hChBG : (reg sg rChB).val = arenaBase + 5 * nNext := by
    rw [rg, PaperB.WordOps.add_no_wrap _ _ (by
        rw [hOffF, kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt]; omega),
      hOffF, kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt]; omega
  obtain ⟨sh, sth, pch, rh, kh, dh⟩ := step_add15_at (input := input)
    (placed_fetch hplEnd' (i := 6) rfl (by rw [pcg, pcf, pce, pcd, pcc, pcb, hpc])) (by rw [pcg, pcf, pce, pcd, pcc, pcb, hpc]; omega)
  have hChBH : (reg sh rChB).val = arenaBase + 5 * nNext + 1 := by
    rw [rh, PaperB.WordOps.add_no_wrap _ _ (by
        rw [hChBG, kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), ho]; omega),
      hChBG, kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), ho]
  obtain ⟨si, sti, pci, ri, ki, di⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 7) rfl (by rw [pch, pcg, pcf, pce, pcd, pcc, pcb, hpc])) (by rw [pch, pcg, pcf, pce, pcd, pcc, pcb, hpc]; omega)
  obtain ⟨sj, stj, pcj, rj, kj, dj⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 8) rfl (by rw [pci, pch, pcg, pcf, pce, pcd, pcc, pcb, hpc])) (by rw [pci, pch, pcg, pcf, pce, pcd, pcc, pcb, hpc]; omega)
  obtain ⟨sk, stk, pck, rk, kk, dk⟩ := step_mov_at (input := input)
    (placed_fetch hplEnd' (i := 9) rfl (by rw [pcj, pci, pch, pcg, pcf, pce, pcd, pcc, pcb, hpc])) (by rw [pcj, pci, pch, pcg, pcf, pce, pcd, pcc, pcb, hpc]; omega)
  refine ⟨sk, ?_, ?_,
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hz],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), ho],
    by rw [kk _ (by decide), kj _ (by decide), ri, kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hz],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hCnt],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hStack],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), hTinD],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), hToutE],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), hOffF],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), hChBH],
    by rw [kk _ (by decide), rj, ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hz],
    by rw [rk, kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), ho],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), kb _ (by decide), hChild],
    by rw [kk _ (by decide), kj _ (by decide), ki _ (by decide), kh _ (by decide), kg _ (by decide), kf _ (by decide), ke _ (by decide), kd _ (by decide), kc _ (by decide), hRemB],
    by rw [dk, dj, di, dh, dg, df, de, dd, dc, db]⟩
  · change Steps code input prog.length s sk
    rw [hProgLen]
    exact Steps.cons stb (Steps.cons stc (Steps.cons std (Steps.cons ste
      (Steps.cons stf (Steps.cons stg (Steps.cons sth (Steps.cons sti (Steps.cons stj (Steps.cons stk (.zero _))))))))))
  · rw [pck, pcj, pci, pch, pcg, pcf, pce, pcd, pcc, pcb, hpc]; change entry + 10 = entry + prog.length; rw [hProgLen]

private theorem stage2cBody_slices {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    (hpl : Placed code 0 (stage2cBody h8)) :
    let pc1 := (s2cSetup h8).length
    let pc2 := pc1 + 7
    let pc3 := pc2 + (s2cPrep2 h8).length
    let pc4 := pc3 + 7
    let pc5 := pc4 + (s2cPrep3 h8).length
    let pc6 := pc5 + 7
    let pc7 := pc6 + (s2cPrep4 h8).length
    let pc8 := pc7 + 7
    let pc9 := pc8 + (s2cPrep5 h8).length
    let pc10 := pc9 + 7
    Placed code 0 (s2cSetup h8) ∧
    Placed code pc1 (stage2cCopyLoop pc1 pc2) ∧
    Placed code pc2 (s2cPrep2 h8) ∧
    Placed code pc3 (stage2cCopyLoop pc3 pc4) ∧
    Placed code pc4 (s2cPrep3 h8) ∧
    Placed code pc5 (stage2cCopyLoop pc5 pc6) ∧
    Placed code pc6 (s2cPrep4 h8) ∧
    Placed code pc7 (stage2cCopyLoop pc7 pc8) ∧
    Placed code pc8 (s2cPrep5 h8) ∧
    Placed code pc9 (stage2cCopyLoop pc9 pc10) ∧
    Placed code pc10 (s2cFinish h8) := by
  let pc1 := (s2cSetup h8).length
  let pc2 := pc1 + 7
  let pc3 := pc2 + (s2cPrep2 h8).length
  let pc4 := pc3 + 7
  let pc5 := pc4 + (s2cPrep3 h8).length
  let pc6 := pc5 + 7
  let pc7 := pc6 + (s2cPrep4 h8).length
  let pc8 := pc7 + 7
  let pc9 := pc8 + (s2cPrep5 h8).length
  let pc10 := pc9 + 7
  have hEq : stage2cBody h8 =
      s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++
      s2cPrep2 h8 ++ stage2cCopyLoop pc3 pc4 ++
      s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6 ++
      s2cPrep4 h8 ++ stage2cCopyLoop pc7 pc8 ++
      s2cPrep5 h8 ++ stage2cCopyLoop pc9 pc10 ++
      s2cFinish h8 := rfl
  have p10 := placed_append_left (hEq ▸ hpl)
  have p9 := placed_append_left p10
  have p8 := placed_append_left p9
  have p7 := placed_append_left p8
  have p6 := placed_append_left p7
  have p5 := placed_append_left p6
  have p4 := placed_append_left p5
  have p3 := placed_append_left p4
  have p2 := placed_append_left p3
  have p1 := placed_append_left p2
  have q2 := placed_append_right p2
  have q3 := placed_append_right p3
  have q4 := placed_append_right p4
  have q5 := placed_append_right p5
  have q6 := placed_append_right p6
  have q7 := placed_append_right p7
  have q8 := placed_append_right p8
  have q9 := placed_append_right p9
  have q10 := placed_append_right p10
  have q11 := placed_append_right (hEq ▸ hpl)
  refine ⟨p1, q2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2).length = pc2 := by
      dsimp only [pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q3
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8).length = pc3 := by
      dsimp only [pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q4
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4).length = pc4 := by
      dsimp only [pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q5
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4 ++ s2cPrep3 h8).length = pc5 := by
      dsimp only [pc5, pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q6
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4 ++ s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6).length = pc6 := by
      dsimp only [pc6, pc5, pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q7
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4 ++ s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6 ++ s2cPrep4 h8).length = pc7 := by
      dsimp only [pc7, pc6, pc5, pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q8
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4 ++ s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6 ++
        s2cPrep4 h8 ++ stage2cCopyLoop pc7 pc8).length = pc8 := by
      dsimp only [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q9
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4 ++ s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6 ++
        s2cPrep4 h8 ++ stage2cCopyLoop pc7 pc8 ++ s2cPrep5 h8).length = pc9 := by
      dsimp only [pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q10
  · have hl : 0 + (s2cSetup h8 ++ stage2cCopyLoop pc1 pc2 ++ s2cPrep2 h8 ++
        stage2cCopyLoop pc3 pc4 ++ s2cPrep3 h8 ++ stage2cCopyLoop pc5 pc6 ++
        s2cPrep4 h8 ++ stage2cCopyLoop pc7 pc8 ++ s2cPrep5 h8 ++ stage2cCopyLoop pc9 pc10).length = pc10 := by
      dsimp only [pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1]; simp only [List.length_append, stage2cCopyLoop_length]; omega
    rwa [hl] at q11

private theorem s2c_arena_disj (n m N dictCnt : Nat) (hd : dictCnt ≤ n) (hN : N ≤ n + 1) :
    parentsBase n m + N ≤ (1 + 3 * dictCnt + (n + 1) + (n + 1) + n) + 2 * N ∨
      (1 + 3 * dictCnt + (n + 1) + (n + 1) + n) + 2 * N + N ≤ parentsBase n m := by
  refine Or.inr ?_
  unfold parentsBase labelsBase backSndBase backFstBase jumpBase dictBase candSndBBase
    candFstBBase candSndABase candFstABase predBufBase rowEndBase rowStartBase
    ranksBase orderBase stampsBase indegBase csrArenaWords
  omega

private theorem s2c_prefix_size {bits : Nat}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows order size_order rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    {F : JumpForest}
    (hGrounded : Grounded (orderedConfig dictRows large) F r.out.tables)
    (hLabSz : r.out.labels.size = H.vertexCount) :
    let w := PaperB.RetainedProperLoss.packWordColumns r width
    let dictCnt := (orderedConfig dictRows large).dict.size
    w.dictionary.size = 1 + 3 * dictCnt ∧
    w.back.tagAndFirst.size = H.vertexCount + 1 ∧
    w.back.second.size = H.vertexCount + 1 ∧
    w.labels.size = H.vertexCount ∧
    (packedPrefix w).size =
      (1 + 3 * dictCnt) + (H.vertexCount + 1) + (H.vertexCount + 1) + H.vertexCount := by
  dsimp only
  have hSlt : (RetainedProperLoss.ofOrderedReader r).slots.size =
      (orderedConfig dictRows large).dict.size := hGrounded.slot_size
  have hDct : (RetainedProperLoss.ofOrderedReader r).dict.size =
      (orderedConfig dictRows large).dict.size := rfl
  have hP0 : (PaperB.RetainedProperLoss.packWordColumns r width).dictionary.size =
      1 + 3 * (orderedConfig dictRows large).dict.size := by
    dsimp only [PaperB.RetainedProperLoss.packWordColumns]
    rw [FlatPairDictionary.retained_words, hSlt, hDct]; omega
  have hP1 : (PaperB.RetainedProperLoss.packWordColumns r width).back.tagAndFirst.size =
      H.vertexCount + 1 := by
    dsimp only [PaperB.RetainedProperLoss.packWordColumns]
    rw [(RetainedProperLoss.packBackWords_size _ _).1]
    change r.out.tables.back.size = H.vertexCount + 1
    rw [hGrounded.back_size]
    simp only [_root_.EX24.Config.usePackedWords, orderedConfig, PaperB.Jumps.ConcreteInit.region]
  have hP2 : (PaperB.RetainedProperLoss.packWordColumns r width).back.second.size =
      H.vertexCount + 1 := by
    dsimp only [PaperB.RetainedProperLoss.packWordColumns]
    rw [(RetainedProperLoss.packBackWords_size _ _).2]
    change r.out.tables.back.size = H.vertexCount + 1
    rw [hGrounded.back_size]
    simp only [_root_.EX24.Config.usePackedWords, orderedConfig, PaperB.Jumps.ConcreteInit.region]
  have hP3 : (PaperB.RetainedProperLoss.packWordColumns r width).labels.size = H.vertexCount := by
    dsimp only [PaperB.RetainedProperLoss.packWordColumns]
    rw [BoundedScalarArray.size_pack]
    exact hLabSz
  have hPre : (packedPrefix (PaperB.RetainedProperLoss.packWordColumns r width)).size =
      (1 + 3 * (orderedConfig dictRows large).dict.size) + (H.vertexCount + 1) +
        (H.vertexCount + 1) + H.vertexCount := by
    simp only [packedPrefix, Array.size_append, hP0, hP1, hP2, hP3]
  exact ⟨hP0, hP1, hP2, hP3, hPre⟩

private theorem s2c_sourceEq_of_segs {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    {dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows order size_order rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    {F : JumpForest} {s t : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F r.out H.vertexCount s)
    {src0 : Nat}
    (hSeg1 : ∀ j < 1 + 3 * (orderedConfig dictRows large).dict.size,
      t.data[src0 + j]? = s.data[dictBase H.vertexCount H.arcCount + j]?)
    (hSeg2 : ∀ j < H.vertexCount + 1,
      t.data[src0 + (1 + 3 * (orderedConfig dictRows large).dict.size) + j]? =
        s.data[backFstBase H.vertexCount H.arcCount + j]?)
    (hSeg3 : ∀ j < H.vertexCount + 1,
      t.data[src0 + (1 + 3 * (orderedConfig dictRows large).dict.size) + (H.vertexCount + 1) + j]? =
        s.data[backSndBase H.vertexCount H.arcCount + j]?)
    (hSeg4 : ∀ j < H.vertexCount,
      t.data[src0 + (1 + 3 * (orderedConfig dictRows large).dict.size) + (H.vertexCount + 1) + (H.vertexCount + 1) + j]? =
        s.data[labelsBase H.vertexCount H.arcCount + j]?) :
    ∀ j < (packedPrefix (PaperB.RetainedProperLoss.packWordColumns r width)).size,
      t.data[src0 + j]? = (packedPrefix (PaperB.RetainedProperLoss.packWordColumns r width))[j]? := by
  intro j hj
  let n := H.vertexCount
  let m := H.arcCount
  let dictCnt := (orderedConfig dictRows large).dict.size
  let len1 := 1 + 3 * dictCnt
  let len2 := n + 1
  let len3 := n + 1
  let len4 := n
  let prefixLen := len1 + len2 + len3 + len4
  let w := PaperB.RetainedProperLoss.packWordColumns r width
  let p0 := w.dictionary
  let p1 := w.back.tagAndFirst
  let p2 := w.back.second
  let p3 := w.labels
  obtain ⟨hP0Sz, hP1Sz, hP2Sz, hP3Sz, hPreEq⟩ :=
    s2c_prefix_size r width inv.grounded inv.sRefLabelsSize
  have hBackSz : r.out.tables.back.size = n + 1 := by
    change r.out.tables.back.size = H.vertexCount + 1
    rw [inv.grounded.back_size]
    simp only [_root_.EX24.Config.usePackedWords, orderedConfig, PaperB.Jumps.ConcreteInit.region]
  have hjPre : j < prefixLen := by rw [hPreEq] at hj; exact hj
  change _ = (p0 ++ p1 ++ p2 ++ p3)[j]?
  rw [array_getElem?_append_4 p0 p1 p2 p3 j hj, hP0Sz, hP1Sz, hP2Sz]
  by_cases h1 : j < len1
  · rw [ite_eq_left h1, hSeg1 j h1]
    apply wordOption_ext
    have hSerSz : j < p0.size := hP0Sz.symm ▸ h1
    rw [Array.getElem?_eq_getElem hSerSz, Option.map_some]
    have hP0At : p0[j]'hSerSz = (FlatPairDictionary.serialize (RetainedProperLoss.ofOrderedReader r)
        (PaperB.RetainedProperLoss.dictionary_fits r width))[j]'hSerSz := rfl
    rw [hP0At]
    have hVal := sweepSerialize_val_eq (RetainedProperLoss.ofOrderedReader r)
      (PaperB.RetainedProperLoss.dictionary_fits r width) j hSerSz (by
        have hSlt : (RetainedProperLoss.ofOrderedReader r).slots.size = dictCnt := inv.grounded.slot_size
        have hDct : (RetainedProperLoss.ofOrderedReader r).dict.size = dictCnt := rfl
        rw [hSlt, hDct]; dsimp only [len1] at h1; omega)
    have hDct : (RetainedProperLoss.ofOrderedReader r).dict.size = dictCnt := rfl
    by_cases hj0 : j = 0
    · subst hj0; simpa only [↓reduceDIte, Nat.add_zero, hDct] using inv.dictHeader.trans (congrArg some hVal.symm)
    · by_cases hjA : j < 1 + dictCnt
      · have hjA' : j < 1 + (RetainedProperLoss.ofOrderedReader r).dict.size := hDct.symm ▸ hjA
        simp only [hj0, hjA', ↓reduceDIte] at hVal
        have hiA : j - 1 < dictCnt := by omega
        have hdk := (inv.dictKeys (j - 1) hiA).1
        have hidxA : dictBase n m + 1 + (j - 1) = dictBase n m + j := by omega
        rw [hidxA] at hdk; exact hdk.trans (congrArg some hVal.symm)
      · by_cases hjB : j < 1 + 2 * dictCnt
        · have hjA' : ¬ j < 1 + (RetainedProperLoss.ofOrderedReader r).dict.size := hDct.symm ▸ hjA
          have hjB' : j < 1 + 2 * (RetainedProperLoss.ofOrderedReader r).dict.size := hDct.symm ▸ hjB
          simp only [hj0, hjA', hjB', ↓reduceDIte] at hVal
          have hiB : j - (1 + dictCnt) < dictCnt := by omega
          have hdk := (inv.dictKeys (j - (1 + dictCnt)) hiB).2
          have hidxB : dictBase n m + 1 + dictCnt + (j - (1 + dictCnt)) = dictBase n m + j := by omega
          rw [hidxB] at hdk; exact hdk.trans (congrArg some hVal.symm)
        · have hjA' : ¬ j < 1 + (RetainedProperLoss.ofOrderedReader r).dict.size := hDct.symm ▸ hjA
          have hjB' : ¬ j < 1 + 2 * (RetainedProperLoss.ofOrderedReader r).dict.size := hDct.symm ▸ hjB
          simp only [hj0, hjA', hjB', ↓reduceDIte] at hVal
          have hiS : j - (1 + 2 * dictCnt) < dictCnt := by dsimp only [len1] at h1; omega
          have hds := inv.dictSlots (j - (1 + 2 * dictCnt)) hiS
          have hidxS : dictBase n m + 1 + 2 * dictCnt + (j - (1 + 2 * dictCnt)) = dictBase n m + j := by omega
          rw [hidxS] at hds
          have hSlEq : ((RetainedProperLoss.ofOrderedReader r).slots[j - (1 + 2 * (RetainedProperLoss.ofOrderedReader r).dict.size)]?).getD 0 =
              r.out.tables.slotAt (j - (1 + 2 * dictCnt)) := by rw [hDct]; rfl
          rw [hSlEq] at hVal
          exact hds.trans (congrArg some hVal.symm)
  · rw [ite_eq_right h1]
    by_cases h2 : j < len1 + len2
    · rw [ite_eq_left h2]
      have hIdx : src0 + j = src0 + len1 + (j - len1) := by omega
      rw [hIdx, hSeg2 (j - len1) (by omega)]
      apply wordOption_ext
      have hjBk : j - len1 < r.out.tables.back.size := by
        rw [hBackSz]; dsimp only [len2] at h2; omega
      have hjP1 : j - len1 < p1.size := hP1Sz.symm ▸ (by omega)
      rw [Array.getElem?_eq_getElem hjP1, Option.map_some]
      have hBm := (inv.backMem (j - len1) (by dsimp only [len2] at h2; omega)).1
      have hJoin : (r.out.tables.back[j - len1]?).join = r.out.tables.back[j - len1]'hjBk := by
        rw [Array.getElem?_eq_getElem hjBk]; rfl
      have hRead := congrArg Prod.fst (RetainedProperLoss.packBackWords_read (RetainedProperLoss.ofOrderedReader r)
        (by omega : H.vertexCount < 2 ^ bits) ⟨j - len1, hjBk⟩)
      dsimp only at hRead
      rw [hJoin] at hBm
      exact hBm.trans (congrArg some hRead.symm)
    · rw [ite_eq_right h2]
      by_cases h3 : j < len1 + len2 + len3
      · rw [ite_eq_left h3]
        have hIdx : src0 + j = src0 + len1 + len2 + (j - (len1 + len2)) := by omega
        rw [hIdx, hSeg3 (j - (len1 + len2)) (by omega)]
        apply wordOption_ext
        have hjBk : j - (len1 + len2) < r.out.tables.back.size := by
          rw [hBackSz]; dsimp only [len3] at h3; omega
        have hjP2 : j - (len1 + len2) < p2.size := hP2Sz.symm ▸ (by omega)
        rw [Array.getElem?_eq_getElem hjP2, Option.map_some]
        have hBm := (inv.backMem (j - (len1 + len2)) (by dsimp only [len3] at h3; omega)).2
        have hJoin : (r.out.tables.back[j - (len1 + len2)]?).join = r.out.tables.back[j - (len1 + len2)]'hjBk := by
          rw [Array.getElem?_eq_getElem hjBk]; rfl
        have hRead := congrArg Prod.snd (RetainedProperLoss.packBackWords_read (RetainedProperLoss.ofOrderedReader r)
          (by omega : H.vertexCount < 2 ^ bits) ⟨j - (len1 + len2), hjBk⟩)
        dsimp only at hRead
        rw [hJoin] at hBm
        exact hBm.trans (congrArg some hRead.symm)
      · rw [ite_eq_right h3]
        have hIdx : src0 + j = src0 + len1 + len2 + len3 + (j - (len1 + len2 + len3)) := by omega
        rw [hIdx, hSeg4 (j - (len1 + len2 + len3)) (by omega)]
        apply wordOption_ext
        have hkLt : j - (len1 + len2 + len3) < n := by dsimp only [prefixLen, len4] at hjPre; omega
        have hkSz : j - (len1 + len2 + len3) < r.out.labels.size := inv.sRefLabelsSize.symm ▸ hkLt
        have hLab := inv.labelsMem ⟨j - (len1 + len2 + len3), hkLt⟩
        have hPack : (p3[j - (len1 + len2 + len3)]?).map Fin.val = r.out.labels[j - (len1 + len2 + len3)]? :=
          BoundedScalarArray.getElem?_pack_map_val r.out.labels _ _ _
        have hLabVal : r.out.labelAt (j - (len1 + len2 + len3)) =
            r.out.labels[j - (len1 + len2 + len3)]'hkSz := by
          unfold _root_.EX24.State.labelAt
          rw [Array.getElem?_eq_getElem hkSz]; rfl
        have hLabGet : r.out.labels[j - (len1 + len2 + len3)]? = some (r.out.labels[j - (len1 + len2 + len3)]'hkSz) :=
          Array.getElem?_eq_getElem hkSz
        rw [hPack, hLabGet]
        simpa only [hLabVal] using hLab

private theorem s2c_loop12_exec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m dictCnt : Nat) (hn3 : 3 ≤ n) (hdLe : dictCnt ≤ n)
    (hCap : rawWorkCap n m ≤ workCap)
    (_hBits : 1 + 18 * n < 2 ^ bits)
    {pc1 pc2 pc3 pc4 : Nat}
    (hEq1 : pc1 = (s2cSetup (bits := bits) h8).length)
    (hEq2 : pc2 = pc1 + 7)
    (hEq3 : pc3 = pc2 + (s2cPrep2 (bits := bits) h8).length)
    (hEq4 : pc4 = pc3 + 7)
    (hPc4Lt : pc4 < code.size)
    (hplSetup : Placed code 0 (s2cSetup (bits := bits) h8))
    (hplL1 : Placed code pc1 (stage2cCopyLoop pc1 pc2))
    (hplP2 : Placed code pc2 (s2cPrep2 (bits := bits) h8))
    (hplL2 : Placed code pc3 (stage2cCopyLoop pc3 pc4))
    (sData : Array (Word bits))
    (hSlSrc : (sData[slSource]?).map Fin.val = some (sourceBase n m))
    (hSlDB : (sData[slDictBase]?).map Fin.val = some (dictBase n m))
    (hSlDC : (sData[slDictCnt]?).map Fin.val = some dictCnt)
    (hSlBF : (sData[slBackFst]?).map Fin.val = some (backFstBase n m))
    (hSlN : (sData[slN]?).map Fin.val = some n)
    (s0 : State (layout bits inputCap workCap hi hw))
    (hs0pc : s0.pc = 0) (hs0data : s0.data = sData) :
    let len1 := 1 + 3 * dictCnt
    let len2 := n + 1
    let src0 := sourceBase n m
    ∃ sL2 : State (layout bits inputCap workCap hi hw), ∃ k12 : Nat,
      k12 ≤ pc1 + (1 + 7 * len1) + (s2cPrep2 h8).length + (1 + 7 * len2) ∧
      Steps code input k12 s0 sL2 ∧
      sL2.pc = pc4 ∧
      (reg sL2 rZero).val = 0 ∧ (reg sL2 rOne).val = 1 ∧ (reg sL2 rOff).val = len1 + len2 ∧
      (reg sL2 rClk).val = src0 + (len1 + len2) ∧
      (reg sL2 rChild).val = src0 ∧
      (∀ w < src0, sL2.data[w]? = sData[w]?) ∧
      (∀ w, src0 + (len1 + len2) ≤ w → sL2.data[w]? = sData[w]?) ∧
      (∀ j < len1, sL2.data[src0 + j]? = sData[dictBase n m + j]?) ∧
      (∀ j < len2, sL2.data[src0 + len1 + j]? = sData[backFstBase n m + j]?) := by
  let len1 := 1 + 3 * dictCnt
  let len2 := n + 1
  let prefixMax := 6 * n + 3
  let src0 := sourceBase n m
  have hSrcEnd : src0 + prefixMax ≤ rawWorkCap n m :=
    sourceBase_plus_prefix_le n m prefixMax (Nat.le_refl _)
  have hSrc30 : 30 ≤ src0 := by dsimp only [src0]; rw [sourceBase_eq]; omega
  have hSrc012 : src0 + (len1 + len2) < 2 ^ bits := by
    dsimp only [len1, len2, prefixMax] at hSrcEnd ⊢; omega
  have hSrc01 : src0 + len1 < 2 ^ bits := by omega
  have hSrc0Lt : src0 < 2 ^ bits := by omega
  have hScrFit : ∀ sl, sl < 30 → sl < workCap := fun sl hsl =>
    scratch_lt_workCap30 hCap hn3 hsl
  have hPc3Lt : pc3 + 7 < code.size := by rw [← hEq4]; exact hPc4Lt
  have hPc2Lt : pc2 < code.size := by rw [hEq3] at hPc3Lt; omega
  have hPc1Lt : pc1 + 7 < code.size := by rw [hEq2] at hPc2Lt; omega
  have hBankOrder : dictBase n m + len1 ≤ backFstBase n m ∧ backFstBase n m + len2 ≤ src0 := by
    dsimp only [len1, len2, src0]
    unfold sourceBase parentsBase labelsBase backSndBase backFstBase jumpBase
    omega
  obtain ⟨sSetup, stSetup, pcSetup, hzSetup, hoSetup, hClkSetup, hPtrSetup, hValSetup, hOffSetup, hRemSetup, hChildSetup, hdSetup⟩ :=
    s2cSetup_steps h8 (input := input) (by rw [← hEq1]; omega) hplSetup
      (hScrFit _ (by decide)) (hScrFit _ (by decide)) (hScrFit _ (by decide))
      (by exact show 1 + 3 * dictCnt < 2 ^ bits by dsimp only [len1] at *; omega)
      s0 hs0pc (by rw [hs0data]; exact hSlSrc) (by rw [hs0data]; exact hSlDB) (by rw [hs0data]; exact hSlDC)
  have hSetupPc1 : sSetup.pc = pc1 := pcSetup.trans hEq1.symm
  have hL1SrcCap : dictBase n m + len1 ≤ workCap := by
    have := hBankOrder.1; have := hBankOrder.2
    dsimp only [len1, len2, prefixMax] at hSrcEnd ⊢; omega
  have hL1DstCap : src0 + len1 ≤ workCap := by
    dsimp only [len1, prefixMax] at hSrcEnd ⊢; omega
  have hL1SrcFit : dictBase n m + len1 < 2 ^ bits := by
    have := hBankOrder.1; have := hBankOrder.2
    dsimp only [len1, len2] at hSrc012 ⊢; omega
  obtain ⟨sL1, kL1, hkL1, stL1, pcL1, hzL1, hoL1, _, hClkL1, hRegL1, hPrefL1, hOutL1⟩ :=
    stage2cCopyLoop_steps hPc1Lt hPc2Lt hplL1 hL1SrcCap hL1DstCap hL1SrcFit
      (Or.inl (Nat.le_trans hBankOrder.1 (Nat.le_trans (Nat.le_add_right _ _) hBankOrder.2)))
      sData len1 0 (Nat.zero_add _) sSetup hSetupPc1 hzSetup hoSetup hPtrSetup
      (by simp only [Nat.add_zero]; rw [hClkSetup, Nat.mod_eq_of_lt hSrc0Lt]) hRemSetup hValSetup
      (fun j hj => by omega) (fun j _ => by rw [hdSetup, hs0data]) (fun w _ => by rw [hdSetup, hs0data])
  have hOffL1 : (reg sL1 rOff).val = len1 := by
    rw [hRegL1 rOff (by decide) (by decide) (by decide) (by decide), hOffSetup]
  have hChildL1 : (reg sL1 rChild).val = src0 := by
    rw [hRegL1 rChild (by decide) (by decide) (by decide) (by decide), hChildSetup]
  have hClkL1Mod : (reg sL1 rClk).val = src0 + len1 := by
    rw [hClkL1, Nat.mod_eq_of_lt hSrc01]
  let lP2 := (s2cPrep2 h8).length
  have hPcPrep2 : pc2 + (loadScratch h8 rPtr slBackFst ++ loadScratch h8 rVal slN ++
      [Instr.add rVal rVal rOne, Instr.add rOff rOff rVal, Instr.mov rRem rZero]).length < code.size := by
    change pc2 + (s2cPrep2 h8).length < code.size
    rw [← hEq3]; omega
  obtain ⟨sP2, stP2, pcP2, hzP2, hoP2, hClkP2, hPtrP2, hValP2, hOffP2, hRemP2, hChildP2, hdP2⟩ :=
    s2cPrepBack_steps h8 (input := input) (hScrFit _ (by decide)) (by decide) (hScrFit _ (by decide))
      hPcPrep2 hplP2 (by exact show len1 + (n + 1) < 2 ^ bits by dsimp only [len1, len2] at hSrc012 ⊢; omega)
      sL1 pcL1 hzL1 hoL1 hClkL1Mod hOffL1 hChildL1
      (by rw [hOutL1 slBackFst (Or.inl (by unfold slBackFst; omega))]; exact hSlBF)
      (by rw [hOutL1 slN (Or.inl (by unfold slN; omega))]; exact hSlN)
  have hP2Pc3 : sP2.pc = pc3 := pcP2.trans hEq3.symm
  have hL2SrcCap : backFstBase n m + len2 ≤ workCap := by
    have := hBankOrder.2; dsimp only [len2, prefixMax] at hSrcEnd ⊢; omega
  have hL2DstCap : src0 + len1 + len2 ≤ workCap := by
    dsimp only [len1, len2, prefixMax] at hSrcEnd ⊢; omega
  have hL2SrcFit : backFstBase n m + len2 < 2 ^ bits := by
    have := hBankOrder.2; omega
  obtain ⟨sL2, kL2, hkL2, stL2, pcL2, hzL2, hoL2, _, hClkL2, hRegL2, hPrefL2, hOutL2⟩ :=
    stage2cCopyLoop_steps hPc3Lt hPc4Lt hplL2 hL2SrcCap hL2DstCap hL2SrcFit
      (Or.inl (Nat.le_trans hBankOrder.2 (Nat.le_add_right _ _)))
      sL1.data len2 0 (Nat.zero_add _) sP2 hP2Pc3 hzP2 hoP2 hPtrP2
      (by simp only [Nat.add_zero]; rw [hClkP2, Nat.mod_eq_of_lt hSrc01])
      hRemP2 hValP2 (fun j hj => by omega) (fun j _ => by rw [hdP2]) (fun w _ => by rw [hdP2])
  have hOffL2 : (reg sL2 rOff).val = len1 + len2 := by
    rw [hRegL2 rOff (by decide) (by decide) (by decide) (by decide), hOffP2]
  have hChildL2 : (reg sL2 rChild).val = src0 := by
    rw [hRegL2 rChild (by decide) (by decide) (by decide) (by decide), hChildP2]
  have hClkL2Mod : (reg sL2 rClk).val = src0 + (len1 + len2) := by
    rw [hClkL2, Nat.add_assoc, Nat.mod_eq_of_lt hSrc012]
  have hSteps12 : Steps code input (pc1 + kL1 + lP2 + kL2) s0 sL2 := by
    rw [hEq1]
    exact ((stSetup.append stL1).append stP2).append stL2
  refine ⟨sL2, pc1 + kL1 + lP2 + kL2, by dsimp only [lP2]; omega,
    hSteps12, pcL2, hzL2, hoL2, hOffL2, hClkL2Mod, hChildL2,
    fun w hw => ?_, fun w hw => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hOutL2 w (Or.inl (by omega)), hOutL1 w (Or.inl hw)]
  · rw [hOutL2 w (Or.inr (by omega)), hOutL1 w (Or.inr (by omega))]
  · rw [hOutL2 (src0 + j) (Or.inl (by omega))]; exact hPrefL1 j hj
  · rw [hPrefL2 j hj]; exact hOutL1 (backFstBase n m + j) (Or.inl (by omega))

private theorem s2c_loop34_exec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m dictCnt : Nat) (hn3 : 3 ≤ n) (hdLe : dictCnt ≤ n)
    (hCap : rawWorkCap n m ≤ workCap)
    (_hBits : 1 + 18 * n < 2 ^ bits)
    {pc4 pc5 pc6 pc7 pc8 : Nat}
    (hEq5 : pc5 = pc4 + (s2cPrep3 (bits := bits) h8).length)
    (hEq6 : pc6 = pc5 + 7)
    (hEq7 : pc7 = pc6 + (s2cPrep4 (bits := bits) h8).length)
    (hEq8 : pc8 = pc7 + 7)
    (hPc8Lt : pc8 < code.size)
    (hplP3 : Placed code pc4 (s2cPrep3 (bits := bits) h8))
    (hplL3 : Placed code pc5 (stage2cCopyLoop pc5 pc6))
    (hplP4 : Placed code pc6 (s2cPrep4 (bits := bits) h8))
    (hplL4 : Placed code pc7 (stage2cCopyLoop pc7 pc8))
    (sData : Array (Word bits))
    (hSlBS : (sData[slBackSnd]?).map Fin.val = some (backSndBase n m))
    (hSlLab : (sData[slLabels]?).map Fin.val = some (labelsBase n m))
    (hSlN : (sData[slN]?).map Fin.val = some n)
    (sL2 : State (layout bits inputCap workCap hi hw))
    (hpcL2 : sL2.pc = pc4)
    (hzL2 : (reg sL2 rZero).val = 0) (hoL2 : (reg sL2 rOne).val = 1)
    (hOffL2 : (reg sL2 rOff).val = (1 + 3 * dictCnt) + (n + 1))
    (hClkL2 : (reg sL2 rClk).val = sourceBase n m + ((1 + 3 * dictCnt) + (n + 1)))
    (hChildL2 : (reg sL2 rChild).val = sourceBase n m)
    (hLowL2 : ∀ w < sourceBase n m, sL2.data[w]? = sData[w]?)
    (hHighL2 : ∀ w, sourceBase n m + ((1 + 3 * dictCnt) + (n + 1)) ≤ w → sL2.data[w]? = sData[w]?) :
    let len1 := 1 + 3 * dictCnt
    let len2 := n + 1
    let len3 := n + 1
    let len4 := n
    let prefixLen := len1 + len2 + len3 + len4
    let src0 := sourceBase n m
    ∃ sL4 : State (layout bits inputCap workCap hi hw), ∃ k34 : Nat,
      k34 ≤ (s2cPrep3 h8).length + (1 + 7 * len3) + (s2cPrep4 h8).length + (1 + 7 * len4) ∧
      Steps code input k34 sL2 sL4 ∧
      sL4.pc = pc8 ∧
      (reg sL4 rZero).val = 0 ∧ (reg sL4 rOne).val = 1 ∧ (reg sL4 rOff).val = prefixLen ∧
      (reg sL4 rChild).val = src0 ∧
      (∀ w < src0, sL4.data[w]? = sData[w]?) ∧
      (∀ w, src0 + prefixLen ≤ w → sL4.data[w]? = sData[w]?) ∧
      (∀ j < len1 + len2, sL4.data[src0 + j]? = sL2.data[src0 + j]?) ∧
      (∀ j < len3, sL4.data[src0 + len1 + len2 + j]? = sData[backSndBase n m + j]?) ∧
      (∀ j < len4, sL4.data[src0 + len1 + len2 + len3 + j]? = sData[labelsBase n m + j]?) := by
  let len1 := 1 + 3 * dictCnt
  let len2 := n + 1
  let len3 := n + 1
  let len4 := n
  let prefixLen := len1 + len2 + len3 + len4
  let prefixMax := 6 * n + 3
  let src0 := sourceBase n m
  have hPreLe : prefixLen ≤ prefixMax := by dsimp only [prefixLen, prefixMax, len1, len2, len3, len4]; omega
  have hSrcEnd : src0 + prefixMax ≤ rawWorkCap n m :=
    sourceBase_plus_prefix_le n m prefixMax (Nat.le_refl _)
  have hSrc30 : 30 ≤ src0 := by dsimp only [src0]; rw [sourceBase_eq]; omega
  have hSrc0123 : src0 + (len1 + len2 + len3) < 2 ^ bits := by
    dsimp only [prefixLen, len4] at hPreLe; omega
  have hSrc012 : src0 + (len1 + len2) < 2 ^ bits := by omega
  have hScrFit : ∀ sl, sl < 30 → sl < workCap := fun sl hsl =>
    scratch_lt_workCap30 hCap hn3 hsl
  have hPc7Lt : pc7 + 7 < code.size := by rw [← hEq8]; exact hPc8Lt
  have hPc6Lt : pc6 < code.size := by rw [hEq7] at hPc7Lt; omega
  have hPc5Lt : pc5 + 7 < code.size := by rw [← hEq6]; exact hPc6Lt
  have hBankOrder : backSndBase n m + len3 ≤ labelsBase n m ∧ labelsBase n m + len4 ≤ src0 := by
    dsimp only [len3, len4, src0]
    unfold sourceBase parentsBase labelsBase backSndBase backFstBase jumpBase
    omega
  let lP3 := (s2cPrep3 h8).length
  have hPcPrep3 : pc4 + (loadScratch h8 rPtr slBackSnd ++ loadScratch h8 rVal slN ++
      [Instr.add rVal rVal rOne, Instr.add rOff rOff rVal, Instr.mov rRem rZero]).length < code.size := by
    change pc4 + (s2cPrep3 h8).length < code.size
    rw [← hEq5]; omega
  obtain ⟨sP3, stP3, pcP3, hzP3, hoP3, hClkP3, hPtrP3, hValP3, hOffP3, hRemP3, hChildP3, hdP3⟩ :=
    s2cPrepBack_steps h8 (input := input) (hScrFit _ (by decide)) (by decide) (hScrFit _ (by decide))
      hPcPrep3 hplP3 (by exact show (len1 + len2) + (n + 1) < 2 ^ bits by dsimp only [len1, len2, len3] at hSrc0123 ⊢; omega)
      sL2 hpcL2 hzL2 hoL2 hClkL2 hOffL2 hChildL2
      (by rw [hLowL2 slBackSnd (by unfold slBackSnd; omega)]; exact hSlBS)
      (by rw [hLowL2 slN (by unfold slN; omega)]; exact hSlN)
  have hP3Pc5 : sP3.pc = pc5 := pcP3.trans hEq5.symm
  have hL3SrcCap : backSndBase n m + len3 ≤ workCap := by
    have := hBankOrder.1; have := hBankOrder.2
    dsimp only [len3, len4, prefixMax] at hSrcEnd ⊢; omega
  have hL3DstCap : src0 + (len1 + len2) + len3 ≤ workCap := by
    dsimp only [len1, len2, len3, prefixMax] at hSrcEnd ⊢; omega
  have hL3SrcFit : backSndBase n m + len3 < 2 ^ bits := by
    have := hBankOrder.1; have := hBankOrder.2
    dsimp only [len3, len4] at hSrc0123 ⊢; omega
  obtain ⟨sL3, kL3, hkL3, stL3, pcL3, hzL3, hoL3, _, hClkL3, hRegL3, hPrefL3, hOutL3⟩ :=
    stage2cCopyLoop_steps hPc5Lt hPc6Lt hplL3 hL3SrcCap hL3DstCap hL3SrcFit
      (Or.inl (by have := hBankOrder.1; have := hBankOrder.2; omega))
      sL2.data len3 0 (Nat.zero_add _) sP3 hP3Pc5 hzP3 hoP3 hPtrP3
      (by simp only [Nat.add_zero]; rw [hClkP3, Nat.mod_eq_of_lt hSrc012])
      hRemP3 hValP3 (fun j hj => by omega) (fun j _ => by rw [hdP3]) (fun w _ => by rw [hdP3])
  have hOffL3 : (reg sL3 rOff).val = len1 + len2 + len3 := by
    rw [hRegL3 rOff (by decide) (by decide) (by decide) (by decide), hOffP3]
  have hChildL3 : (reg sL3 rChild).val = src0 := by
    rw [hRegL3 rChild (by decide) (by decide) (by decide) (by decide), hChildP3]
  have hClkL3Mod : (reg sL3 rClk).val = src0 + (len1 + len2 + len3) := by
    have hMod : src0 + (len1 + len2) + len3 < 2 ^ bits := by omega
    rw [hClkL3, Nat.mod_eq_of_lt hMod, Nat.add_assoc]
  let lP4 := (s2cPrep4 h8).length
  have hPcPrep4 : pc6 + (s2cPrep4 (bits := bits) h8).length < code.size := by
    rw [← hEq7]; omega
  obtain ⟨sP4, stP4, pcP4, hzP4, hoP4, hClkP4, hPtrP4, hValP4, hOffP4, hRemP4, hChildP4, hdP4⟩ :=
    s2cPrep4_steps h8 (input := input) (hScrFit _ (by decide)) (hScrFit _ (by decide))
      hPcPrep4 hplP4 (by exact show (len1 + len2 + len3) + n < 2 ^ bits by dsimp only [prefixLen, len1, len2, len3, len4] at hPreLe hSrcEnd ⊢; omega)
      sL3 pcL3 hzL3 hoL3 hClkL3Mod hOffL3 hChildL3
      (by rw [hOutL3 slLabels (Or.inl (by unfold slLabels; omega)), hLowL2 slLabels (by unfold slLabels; omega)]; exact hSlLab)
      (by rw [hOutL3 slN (Or.inl (by unfold slN; omega)), hLowL2 slN (by unfold slN; omega)]; exact hSlN)
  have hP4Pc7 : sP4.pc = pc7 := pcP4.trans hEq7.symm
  have hL4SrcCap : labelsBase n m + len4 ≤ workCap := by
    have := hBankOrder.2; dsimp only [len4, prefixMax] at hSrcEnd ⊢; omega
  have hL4DstCap : src0 + (len1 + len2 + len3) + len4 ≤ workCap := by
    dsimp only [len1, len2, len3, len4, prefixMax] at hSrcEnd ⊢; omega
  have hL4SrcFit : labelsBase n m + len4 < 2 ^ bits := by
    have := hBankOrder.2; omega
  obtain ⟨sL4, kL4, hkL4, stL4, pcL4, hzL4, hoL4, _, _, hRegL4, hPrefL4, hOutL4⟩ :=
    stage2cCopyLoop_steps hPc7Lt hPc8Lt hplL4 hL4SrcCap hL4DstCap hL4SrcFit
      (Or.inl (Nat.le_trans hBankOrder.2 (Nat.le_add_right _ _)))
      sL3.data len4 0 (Nat.zero_add _) sP4 hP4Pc7 hzP4 hoP4 hPtrP4
      (by simp only [Nat.add_zero]; rw [hClkP4, Nat.mod_eq_of_lt hSrc0123])
      hRemP4 hValP4 (fun j hj => by omega) (fun j _ => by rw [hdP4]) (fun w _ => by rw [hdP4])
  have hOffL4 : (reg sL4 rOff).val = prefixLen := by
    rw [hRegL4 rOff (by decide) (by decide) (by decide) (by decide), hOffP4]
  have hChildL4 : (reg sL4 rChild).val = src0 := by
    rw [hRegL4 rChild (by decide) (by decide) (by decide) (by decide), hChildP4]
  refine ⟨sL4, lP3 + kL3 + lP4 + kL4, by dsimp only [lP3, lP4]; omega,
    ((stP3.append stL3).append stP4).append stL4, pcL4, hzL4, hoL4, hOffL4, hChildL4,
    fun w hw => ?_, fun w hw => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hOutL4 w (Or.inl (Nat.lt_of_lt_of_le hw (by simp only [Nat.add_assoc]; exact Nat.le_add_right _ _))),
        hOutL3 w (Or.inl (Nat.lt_of_lt_of_le hw (Nat.le_add_right _ _)))]
    exact hLowL2 w hw
  · have hw1 : src0 + (len1 + len2 + len3) + len4 ≤ w := by
      rw [Nat.add_assoc src0 (len1 + len2 + len3) len4]; exact hw
    have hw2 : src0 + (len1 + len2) + len3 ≤ w := by
      rw [Nat.add_assoc src0 (len1 + len2) len3]
      exact Nat.le_trans (Nat.le_add_right _ len4) hw1
    have hw3 : sourceBase n m + ((1 + 3 * dictCnt) + (n + 1)) ≤ w :=
      Nat.le_trans (Nat.le_add_right _ len3) hw2
    rw [hOutL4 w (Or.inr hw1), hOutL3 w (Or.inr hw2)]
    exact hHighL2 w hw3
  · rw [hOutL4 (src0 + j) (Or.inl (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)) src0)),
        hOutL3 (src0 + j) (Or.inl (Nat.add_lt_add_left hj src0))]
  · have hj' : src0 + len1 + len2 + j < src0 + (len1 + len2 + len3) := by
      rw [Nat.add_assoc src0 len1 len2, ← Nat.add_assoc src0 (len1 + len2) len3]
      exact Nat.add_lt_add_left hj (src0 + (len1 + len2))
    rw [hOutL4 (src0 + len1 + len2 + j) (Or.inl hj')]
    have hEq := hPrefL3 j hj
    rw [← Nat.add_assoc src0 len1 len2] at hEq
    rw [hEq]
    exact hLowL2 (backSndBase n m + j)
      (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _)
        (Nat.le_trans hBankOrder.1 (Nat.le_trans (Nat.le_add_right _ len4) hBankOrder.2)))
  · have hLabLt : labelsBase n m + j < src0 :=
      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) hBankOrder.2
    have hEq := hPrefL4 j hj
    rw [← Nat.add_assoc src0 (len1 + len2) len3, ← Nat.add_assoc src0 len1 len2] at hEq
    rw [hEq, hOutL3 (labelsBase n m + j) (Or.inl (Nat.lt_of_lt_of_le hLabLt (Nat.le_add_right _ _)))]
    exact hLowL2 (labelsBase n m + j) hLabLt

private theorem s2c_stage5f_exec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m dictCnt N : Nat) (hn3 : 3 ≤ n) (hdLe : dictCnt ≤ n) (hNLe : N ≤ n + 1)
    (hCap : rawWorkCap n m ≤ workCap)
    (_hBits : 1 + 18 * n < 2 ^ bits)
    {pc8 pc9 pc10 pcEnd : Nat}
    (hEq9 : pc9 = pc8 + (s2cPrep5 (bits := bits) h8).length)
    (hEq10 : pc10 = pc9 + 7)
    (hEqEnd : pcEnd = pc10 + (s2cFinish (bits := bits) h8).length)
    (hPcEndLt : pcEnd < code.size)
    (hplP5 : Placed code pc8 (s2cPrep5 (bits := bits) h8))
    (hplL5 : Placed code pc9 (stage2cCopyLoop pc9 pc10))
    (hplFin : Placed code pc10 (s2cFinish (bits := bits) h8))
    (sData : Array (Word bits))
    (hSlNext : (sData[slNext]?).map Fin.val = some N)
    (hSlParents : (sData[slParents]?).map Fin.val = some (parentsBase n m))
    (sL4 : State (layout bits inputCap workCap hi hw))
    (hpcL4 : sL4.pc = pc8)
    (hzL4 : (reg sL4 rZero).val = 0) (hoL4 : (reg sL4 rOne).val = 1)
    (hOffL4 : (reg sL4 rOff).val = (1 + 3 * dictCnt) + (n + 1) + (n + 1) + n)
    (hChildL4 : (reg sL4 rChild).val = sourceBase n m)
    (hLowL4 : ∀ w < sourceBase n m, sL4.data[w]? = sData[w]?) :
    let prefixLen := (1 + 3 * dictCnt) + (n + 1) + (n + 1) + n
    let arenaBase := prefixLen + 2 * N
    let src0 := sourceBase n m
    ∃ t : State (layout bits inputCap workCap hi hw), ∃ k5f : Nat,
      k5f ≤ (s2cPrep5 h8).length + (1 + 7 * N) + (s2cFinish h8).length ∧
      Steps code input k5f sL4 t ∧
      t.pc = pcEnd ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t cmd).val = 0 ∧ (reg t count).val = N ∧
      (reg t registers.stackBase).val = arenaBase ∧
      (reg t tinBase).val = arenaBase + 2 * N ∧
      (reg t toutBase).val = arenaBase + 3 * N ∧
      (reg t offsetBase).val = arenaBase + 4 * N ∧
      (reg t childrenBase).val = arenaBase + 5 * N + 1 ∧
      (reg t registers.ptr).val = 0 ∧ (reg t clk).val = 1 ∧
      (reg t registers.childBase).val = src0 ∧
      (reg t registers.remain).val = prefixLen ∧
      (∀ j < N, t.data[arenaBase + j]? = sData[parentsBase n m + j]?) ∧
      (∀ j < prefixLen, t.data[src0 + j]? = sL4.data[src0 + j]?) := by
  let prefixLen := (1 + 3 * dictCnt) + (n + 1) + (n + 1) + n
  let arenaBase := prefixLen + 2 * N
  let src0 := sourceBase n m
  have hPreLe : prefixLen ≤ 6 * n + 3 := by dsimp only [prefixLen]; omega
  have hArenaFits := finish_arena_before_source n m N prefixLen hNLe hPreLe
  have hSrcEnd : src0 + prefixLen ≤ rawWorkCap n m :=
    sourceBase_plus_prefix_le n m prefixLen hPreLe
  have hSrc30 : 30 ≤ src0 := by dsimp only [src0]; rw [sourceBase_eq]; omega
  have hArenaEndLt : arenaBase + 5 * N + 1 + N < 2 ^ bits := by dsimp only [arenaBase]; omega
  have hScrFit : ∀ sl, sl < 30 → sl < workCap := fun sl hsl =>
    scratch_lt_workCap30 hCap hn3 hsl
  have hPc10Lt : pc10 + (s2cFinish h8).length < code.size := hEqEnd ▸ hPcEndLt
  have hPc9Lt : pc9 + 7 < code.size := by rw [← hEq10]; omega
  have hPc8Lt : pc8 < code.size := by rw [hEq9] at hPc9Lt; omega
  let lP5 := (s2cPrep5 h8).length
  obtain ⟨sP5, stP5, pcP5, hzP5, hoP5, hCntP5, hStackP5, hClkP5, hPtrP5, hValP5, hOffP5, hRemP5, hChildP5, hdP5⟩ :=
    s2cPrep5_steps h8 (input := input) (hScrFit _ (by decide)) (hScrFit _ (by decide))
      (by rw [← hEq9]; omega) hplP5
      (by exact show prefixLen + 2 * N < 2 ^ bits by dsimp only [arenaBase] at hArenaEndLt; omega)
      sL4 hpcL4 hzL4 hoL4 hOffL4 hChildL4
      (by rw [hLowL4 slNext (by unfold slNext; omega)]; exact hSlNext)
      (by rw [hLowL4 slParents (by unfold slParents; omega)]; exact hSlParents)
  have hP5Pc9 : sP5.pc = pc9 := pcP5.trans hEq9.symm
  have hParDisj : parentsBase n m + N ≤ arenaBase ∨ arenaBase + N ≤ parentsBase n m :=
    s2c_arena_disj n m N dictCnt hdLe hNLe
  have hParBeforeSrc : parentsBase n m + N ≤ src0 := by
    dsimp only [src0]
    unfold sourceBase parentsBase labelsBase backSndBase backFstBase jumpBase dictBase
      candSndBBase candFstBBase candSndABase candFstABase predBufBase rowEndBase rowStartBase
      ranksBase orderBase stampsBase indegBase csrArenaWords
    omega
  have hL5SrcCap : parentsBase n m + N ≤ workCap := by
    dsimp only [prefixLen] at hSrcEnd; omega
  have hL5DstCap : arenaBase + N ≤ workCap := by
    have := hArenaFits.1; dsimp only [arenaBase] at hArenaEndLt ⊢; omega
  have hL5SrcFit : parentsBase n m + N < 2 ^ bits := by omega
  obtain ⟨sL5, kL5, hkL5, stL5, pcL5, hzL5, hoL5, _, _, hRegL5, hPrefL5, hOutL5⟩ :=
    stage2cCopyLoop_steps hPc9Lt (by omega : pc10 < code.size) hplL5
      hL5SrcCap hL5DstCap hL5SrcFit
      hParDisj sL4.data N 0 (Nat.zero_add _) sP5 hP5Pc9 hzP5 hoP5 hPtrP5
      (by simp only [Nat.add_zero]; rw [hClkP5, Nat.mod_eq_of_lt (by omega)])
      hRemP5 hValP5 (fun j hj => by omega) (fun j _ => by rw [hdP5]) (fun w _ => by rw [hdP5])
  have hCntL5 : (reg sL5 rCnt).val = N := by rw [hRegL5 rCnt (by decide) (by decide) (by decide) (by decide), hCntP5]
  have hStackL5 : (reg sL5 rStack).val = arenaBase := by rw [hRegL5 rStack (by decide) (by decide) (by decide) (by decide), hStackP5]
  have hOffL5 : (reg sL5 rOff).val = prefixLen := by rw [hRegL5 rOff (by decide) (by decide) (by decide) (by decide), hOffP5]
  have hChildL5 : (reg sL5 rChild).val = src0 := by rw [hRegL5 rChild (by decide) (by decide) (by decide) (by decide), hChildP5]
  let lFin := (s2cFinish h8).length
  obtain ⟨t, stFin, htpc, htz, hto, hCmdT, hCntT, hStackT, hTinT, hToutT, hOffT, hChBT, hPtrT, hClkT, hChildT, hRemT, hdT⟩ :=
    s2cFinish_steps h8 (input := input) hPc10Lt hplFin
      (by dsimp only [arenaBase] at hArenaEndLt; omega) sL5 pcL5 hzL5 hoL5 hCntL5 hStackL5 hOffL5 hChildL5
  refine ⟨t, lP5 + kL5 + lFin, by dsimp only [lP5, lFin]; omega,
    (stP5.append stL5).append stFin, htpc.trans hEqEnd.symm,
    htz, hto, hCmdT, hCntT, hStackT, hTinT, hToutT, hOffT, hChBT, hPtrT, hClkT, hChildT, hRemT,
    fun j hj => by rw [hdT, hPrefL5 j hj, hLowL4 (parentsBase n m + j) (by omega)],
    fun j hj => by
      have hA : arenaBase + N ≤ src0 + j := by
        have := hArenaFits.1; dsimp only [arenaBase] at hArenaEndLt ⊢; omega
      rw [hdT, hOutL5 (src0 + j) (Or.inr hA)]⟩

theorem run_sweepStage2c {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (input : Input (layout bits inputCap workCap hi hw))
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows order size_order rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    {F : JumpForest} {s : State (layout bits inputCap workCap hi hw)}
    (inv : SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      F r.out H.vertexCount s) :
    ∃ t : State (layout bits inputCap workCap hi hw),
    ∃ states : List (State (layout bits inputCap workCap hi hw)),
    ∃ work : Nat,
      work ≤ 120 * (H.vertexCount + 1) ∧
      run (sweepStage2cPhase hi hw h8).code input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace (sweepStage2cPhase hi hw h8).code input (Phase.initial s) states ⟨t, work⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 ∧
      t.pc = (sweepStage2cPhase hi hw h8).haltPC ∧
      Nonempty (Stage2Output H r width t) := by
  let ph := sweepStage2cPhase hi hw h8
  let n := H.vertexCount
  let m := H.arcCount
  let dictCnt := (orderedConfig dictRows large).dict.size
  let N := nodeCount (orderedConfig dictRows large) r.out
  let len1 := 1 + 3 * dictCnt
  let len2 := n + 1
  let len3 := n + 1
  let len4 := n
  let prefixLen := len1 + len2 + len3 + len4
  let arenaBase := prefixLen + 2 * N
  let src0 := sourceBase n m
  have hDictLe : dictCnt ≤ n := dict_size_le H dictRows large
  have hNEqNext : N = r.out.tables.next := nodeCount_eq_next r.index.ok
  have hNEqF : N = F.size := hNEqNext.trans inv.grounded.size_eq.symm
  have hNLe : N ≤ n + 1 := PaperB.EX24.FinalDFS.nodeCount_le r.index.ok
  have hNPos : 0 < N := by
    rw [hNEqF]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) (inv.grounded.size_eq ▸ inv.labelsLt H.root)
  have hPreLe : prefixLen ≤ 6 * n + 3 := by dsimp only [prefixLen, len1, len2, len3, len4]; omega
  have hArenaFits := finish_arena_before_source n m N prefixLen hNLe hPreLe
  have hSrcEnd : src0 + prefixLen ≤ rawWorkCap n m :=
    sourceBase_plus_prefix_le n m prefixLen hPreLe
  have hArenaEndLt : arenaBase + 5 * N + 1 + N < 2 ^ bits := by dsimp only [arenaBase]; omega
  have hplBody : Placed ph.code 0 (stage2cBody h8) :=
    placed_of_phase_body (stage2cBody h8) (stage2cBody_nonHalt h8)
  have hCodeSz : ph.code.size = (stage2cBody h8).length + 1 := by
    dsimp only [ph, sweepStage2cPhase, mkPhase, Phase.ofLast]
    rw [List.size_toArray, List.length_append, List.length_cons, List.length_nil]
  have hHaltLt : (stage2cBody h8).length < ph.code.size := by omega
  have hBodyLen := stage2cBody_len_parts (bits := bits) h8
  obtain ⟨hplSetup, hplL1, hplP2, hplL2, hplP3, hplL3, hplP4, hplL4, hplP5, hplL5, hplFin⟩ :=
    stage2cBody_slices (hi := hi) (hw := hw) h8 hplBody
  let pc1 := (s2cSetup h8).length
  let pc2 := pc1 + 7
  let pc3 := pc2 + (s2cPrep2 h8).length
  let pc4 := pc3 + 7
  let pc5 := pc4 + (s2cPrep3 h8).length
  let pc6 := pc5 + 7
  let pc7 := pc6 + (s2cPrep4 h8).length
  let pc8 := pc7 + 7
  let pc9 := pc8 + (s2cPrep5 h8).length
  let pc10 := pc9 + 7
  let pcEnd := (stage2cBody h8).length
  have hPcEndLt : pcEnd < ph.code.size := hHaltLt
  have hPc8Lt : pc8 < ph.code.size := by dsimp only [pcEnd] at hPcEndLt; rw [hBodyLen] at hPcEndLt; omega
  have hPc4Lt : pc4 < ph.code.size := by dsimp only [pc8, pc7, pc6, pc5] at hPc8Lt; omega
  let s0 : State (layout bits inputCap workCap hi hw) := Phase.initial s
  obtain ⟨sL2, k12, hk12, st12, pcL2, hzL2, hoL2, hOffL2, hClkL2, hChildL2, hLowL2, hHighL2, hSeg1, hSeg2⟩ :=
    s2c_loop12_exec h8 (code := ph.code) (input := input) n m dictCnt large hDictLe hCap width
      rfl rfl rfl rfl hPc4Lt hplSetup hplL1 hplP2 hplL2
      s.data inv.slSourceVal inv.slDictBaseVal inv.slDictCntVal inv.slBackFstVal inv.slNVal s0 rfl rfl
  obtain ⟨sL4, k34, hk34, st34, pcL4, hzL4, hoL4, hOffL4, hChildL4, hLowL4, _, hPres12, hSeg3, hSeg4⟩ :=
    s2c_loop34_exec h8 (code := ph.code) (input := input) n m dictCnt large hDictLe hCap width
      rfl rfl rfl rfl hPc8Lt hplP3 hplL3 hplP4 hplL4
      s.data inv.slBackSndVal inv.slLabelsVal inv.slNVal sL2 pcL2 hzL2 hoL2 hOffL2 hClkL2 hChildL2 hLowL2 hHighL2
  obtain ⟨t, k5f, hk5f, st5f, htpc, htz, hto, hCmdT, hCntT, hStackT, hTinT, hToutT, hOffT, hChBT, hPtrT, hClkT, hChildT, hRemT, hParT, hPresPre⟩ :=
    s2c_stage5f_exec h8 (code := ph.code) (input := input) n m dictCnt N large hDictLe hNLe hCap width
      rfl rfl hBodyLen hPcEndLt hplP5 hplL5 hplFin
      s.data (by rw [hNEqNext]; exact inv.slNextVal) inv.slParentsVal sL4 pcL4 hzL4 hoL4 hOffL4 hChildL4 hLowL4
  let workSteps := k12 + k34 + k5f
  have htHalt : t.pc = ph.haltPC := htpc
  have hh : ph.code[t.pc]? = some .halt := htHalt ▸ ph.haltAt
  have hRun : run ph.code input (workSteps + 1) (Phase.initial s) = some ⟨t, workSteps + 1⟩ :=
    ((st12.append st34).append st5f).halts (step_halt_at hh)
  obtain ⟨states, ok⟩ := run_has_successfulTrace hRun
  have hStatic : (s2cSetup h8).length + (s2cPrep2 h8).length + (s2cPrep3 h8).length +
      (s2cPrep4 h8).length + (s2cPrep5 h8).length + (s2cFinish h8).length ≤ 220 := by
    have hLenB := stage2cBody_len_le (bits := bits) h8
    omega
  have hWorkLe : workSteps + 1 ≤ 120 * (H.vertexCount + 1) := by
    dsimp only [workSteps]
    omega
  obtain ⟨_, _, _, _, hPreEq⟩ := s2c_prefix_size r width inv.grounded inv.sRefLabelsSize
  have hSourceEq : ∀ j < (packedPrefix (PaperB.RetainedProperLoss.packWordColumns r width)).size,
      t.data[src0 + j]? = (packedPrefix (PaperB.RetainedProperLoss.packWordColumns r width))[j]? :=
    s2c_sourceEq_of_segs H r width inv
      (fun j hj => (hPresPre j (by omega)).trans ((hPres12 j (by omega)).trans (hSeg1 j hj)))
      (fun j hj => by
        have h2 := hSeg2 j hj
        have h1 := hPres12 (len1 + j) (by dsimp only [len1, len2]; omega)
        have h0 := hPresPre (len1 + j) (by omega)
        dsimp only [src0, n, m, len1, len2, dictCnt] at h0 h1 h2 ⊢
        rw [← Nat.add_assoc] at h0 h1
        exact h0.trans (h1.trans h2))
      (fun j hj => by
        have h2 := hSeg3 j hj
        have h0 := hPresPre (len1 + len2 + j) (by omega)
        dsimp only [src0, n, m, len1, len2] at h0 h2 ⊢
        simp only [Nat.add_assoc] at h0 h2 ⊢
        exact h0.trans h2)
      (fun j hj => by
        have h2 := hSeg4 j hj
        have h0 := hPresPre (len1 + len2 + len3 + j) (by omega)
        dsimp only [src0, n, m, len1, len2, len3] at h0 h2 ⊢
        simp only [Nat.add_assoc] at h0 h2 ⊢
        exact h0.trans h2)
  have hWCap : rawWorkCap n m ≤ workCap := hCap
  let arena : Arena bits workCap N :=
    { base := arenaBase
      children := N
      room := Nat.le_trans hArenaFits.1 (by dsimp only [src0] at hSrcEnd; omega)
      wordFits := hArenaEndLt }
  have hCtrl : Control arena t :=
    { count_eq := hCntT
      one := hto
      zero := htz
      stackBase_eq := hStackT
      tin_eq := hTinT
      tout_eq := hToutT
      offset_eq := hOffT
      child_eq := hChBT }
  have hParents : ParentAt arena (packedInput r.index.ok).parent.read t.data := by
    intro v
    have hvF : v.val < F.size := hNEqF ▸ v.isLt
    rw [hParT v.val v.isLt, inv.parentsMem v.val hvF, packedInput_parent r.index.ok inv.grounded v]
  have hParams : PrefixCopyInput t src0 (packedPrefix (PaperB.RetainedProperLoss.packWordColumns r width)).size :=
    { cursor := hPtrT
      src := hChildT
      unit := hClkT
      count := by rw [hRemT, hPreEq] }
  exact ⟨t, states, workSteps + 1, hWorkLe, hRun, ok, ok.peak_eq, htHalt,
    ⟨{ arena := arena
       ctrl := hCtrl
       rootVal := by rw [hCmdT, packedInput_root r.index.ok]
       parents := hParents
       mass := Nat.sub_le N 1
       children := Nat.le_refl N
       place := by dsimp only [arena, arenaBase]; rw [hPreEq]
       src := src0
       fits := by rw [hPreEq]; exact Nat.le_trans hSrcEnd hCap
       apart := by rw [hPreEq]; exact hArenaFits.2
       params := hParams
       sourceAt := hSourceEq }⟩⟩

end Stage2cExec

end PaperB.RamForestProgram.Sweep
