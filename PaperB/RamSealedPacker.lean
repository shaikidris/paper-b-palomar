module

public import PaperB.RamSealedIndexShift

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false

/-! The sealed index builder composes the verified copy phases and shifts the retained index to address zero. -/

namespace PaperB.RamSealedPacker

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub add_no_wrap)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.ForestHead
open PaperB.EX16Assembly
open PaperB.DenseQuotientRows
open PaperB.DenseOriginalQuotient
open PaperB.EX44.ActualOnlineOracle
open PaperB.RamQuotientEmitter
open PaperB.OracleSealedIndexLayout
open PaperB.RamOracleQuery
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.ForestSlimIndex
open PaperB.RetainedProperLoss
open PaperB.RamDagReach
open PaperB.RamStaticReaderBridge

section ExecutionProofs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

set_option maxHeartbeats 6000000 in
private theorem run_sealedOwnersPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {mem : Array (Word bits)} {treeBaseG : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBaseG g r dense)
    {n m root Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase : Nat}
    (hn : 1 ≤ n) (hQ : Q = dense.length) (hQn : Q ≤ n)
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hDisj : SealedDisjointLayout n Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hFPFit : forestPtrsBase + 6 * Q ≤ workCap)
    (hFAFit : forestArenaBase + forestUsed ≤ workCap)
    (hEPFit : exitPtrsBase + 3 * Q ≤ workCap)
    (hEAFit : exitArenaBase + exitUsed ≤ workCap)
    (hHdrDesc : (s₀.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q))
    (hHdrTot : (s₀.data[sealedBase + hdrTotalWords]?).map Fin.val = some (sealedInitArenaOff n Q))
    (hChildStart : ∀ d ≤ Q, (s₀.data[treeBase + 7 * Q + d]?).map Fin.val = some (S.childStart d))
    (hArena : ∀ d : Fin dense.length,
      OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
        exitPtrsBase exitArenaBase exitUsed s₀.data) :
    let ph := sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32
    ∃ (t : State L16) (steps totalWords : Nat),
      totalWords ≤ retainedLinearFactor * n ∧
      steps ≤ 700 * (n + m + 1) ∧
      run ph.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some totalWords ∧
      sealedInitArenaOff n Q ≤ totalWords ∧
      (∀ addr, (addr < sealedBase + hdrTotalWords ∨
          (sealedBase + hdrTotalWords < addr ∧ addr < sealedBase + sealedOwnerDescOff n Q) ∨
          sealedBase + totalWords ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) ∧
      (∀ d : Fin dense.length,
        let descBase := sealedBase + sealedOwnerDescOff n Q + ownerDescStride * d.val
        let nD := 1 + (S.childSlice d).length
        (t.data[descBase + descN]?).map Fin.val = some nD ∧
        (if nD < 3 then
          ∀ k, 1 ≤ k → k < 10 → (t.data[descBase + k]?).map Fin.val = some 0
        else
          ∃ (dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
              exitDepthPtr exitStoredPtr exitPriorPtr : Nat),
            (t.data[descBase + descDict]?).map Fin.val = some dictPtr ∧
            (t.data[descBase + descBackFst]?).map Fin.val = some backFstPtr ∧
            (t.data[descBase + descBackSnd]?).map Fin.val = some backSndPtr ∧
            (t.data[descBase + descLabels]?).map Fin.val = some labelsPtr ∧
            (t.data[descBase + descFEntry]?).map Fin.val = some fEntryPtr ∧
            (t.data[descBase + descFStop]?).map Fin.val = some fStopPtr ∧
            (t.data[descBase + descExitDepth]?).map Fin.val = some exitDepthPtr ∧
            (t.data[descBase + descExitStored]?).map Fin.val = some exitStoredPtr ∧
            (t.data[descBase + descExitPrior]?).map Fin.val = some exitPriorPtr ∧
            (∀ (fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D : Nat),
              (s₀.data[forestPtrsBase + 6 * d.val]?).map Fin.val = some fp0 →
              (s₀.data[forestPtrsBase + 6 * d.val + 1]?).map Fin.val = some fp1 →
              (s₀.data[forestPtrsBase + 6 * d.val + 2]?).map Fin.val = some fp2 →
              (s₀.data[forestPtrsBase + 6 * d.val + 3]?).map Fin.val = some fp3 →
              (s₀.data[forestPtrsBase + 6 * d.val + 4]?).map Fin.val = some fp4 →
              (s₀.data[forestPtrsBase + 6 * d.val + 5]?).map Fin.val = some fp5 →
              ((s₀.data[fp0]?).map Fin.val).getD 0 = D →
              fp1 = fp0 + (1 + 3 * D) →
              fp2 = fp1 + (nD + 1) →
              fp3 = fp2 + (nD + 1) →
              fp4 = fp3 + nD →
              fp5 = fp4 + N_d →
              (s₀.data[exitPtrsBase + 3 * d.val]?).map Fin.val = some ep0 →
              (s₀.data[exitPtrsBase + 3 * d.val + 1]?).map Fin.val = some ep1 →
              (s₀.data[exitPtrsBase + 3 * d.val + 2]?).map Fin.val = some ep2 →
              backFstPtr = dictPtr + (fp1 - fp0) ∧
              backSndPtr = dictPtr + (fp2 - fp0) ∧
              labelsPtr = dictPtr + (fp3 - fp0) ∧
              fEntryPtr = dictPtr + (fp4 - fp0) ∧
              fStopPtr = dictPtr + (fp5 - fp0) ∧
              dictPtr + ((fp5 - fp0) + N_d) ≤ totalWords ∧
              exitDepthPtr + N_d ≤ totalWords ∧
              exitStoredPtr + 18 * N_d ≤ totalWords ∧
              exitPriorPtr + 6 * nD ≤ totalWords ∧
              (∀ k < (fp5 - fp0) + N_d, t.data[sealedBase + dictPtr + k]? = s₀.data[fp0 + k]?) ∧
              (∀ k < N_d, t.data[sealedBase + exitDepthPtr + k]? = s₀.data[ep0 + k]?) ∧
              (∀ k < 18 * N_d, t.data[sealedBase + exitStoredPtr + k]? = s₀.data[ep1 + k]?) ∧
              (∀ k < 6 * nD, t.data[sealedBase + exitPriorPtr + k]? = s₀.data[ep2 + k]?)))) := by
  intro ph
  let code := ph.code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  have hChildBound : ∀ j : Fin dense.length,
      1 + (S.childSlice j).length = 1 + (S.childStart (j.val + 1) - S.childStart j.val) := fun j => by
    simp [StaticTreeSlice.childSlice]
  have hChildSum : (List.range dense.length).foldl
      (fun acc d => acc + (S.childStart (d + 1) - S.childStart d)) 0 = dense.length - 1 := by
    rw [foldl_childSlice_aux S dense.length (Nat.le_refl _), S.childStart_zero, S.childStart_end, Nat.sub_zero]
  have hChildPrefix : ∀ k ≤ dense.length,
      (List.range k).foldl (fun acc d => acc + (S.childStart (d + 1) - S.childStart d)) 0 ≤ Q - 1 := by
    intro k hk
    rw [foldl_childSlice_aux S k hk, S.childStart_zero, Nat.sub_zero, hQ]
    have hm := S.childStart_mono k dense.length hk (Nat.le_refl _)
    rw [S.childStart_end] at hm
    exact hm
  let inv : (Nat × Nat) → State L16 → Prop := fun dc s =>
    let d := dc.1
    let curOff := dc.2
    let prefChildren := (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0
    d ≤ Q ∧
    s.pc = 1 ∧
    s.data.size = workCap ∧
    SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s ∧
    (reg s r10).val = d ∧
    (s.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q) ∧
    (s.data[sealedBase + hdrTotalWords]?).map Fin.val = some curOff ∧
    sealedInitArenaOff n Q ≤ curOff ∧
    curOff ≤ sealedInitArenaOff n Q + 19 * d + 66 * prefChildren ∧
    (∀ addr, (addr < sealedBase + hdrTotalWords ∨
        (sealedBase + hdrTotalWords < addr ∧ addr < sealedBase + sealedOwnerDescOff n Q) ∨
        sealedBase + curOff ≤ addr) →
      s.data[addr]? = s₀.data[addr]?) ∧
    (∀ j : Fin dense.length, j.val < d →
      let descBase := sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val
      let nD := 1 + (S.childSlice j).length
      (s.data[descBase + descN]?).map Fin.val = some nD ∧
      (if nD < 3 then
        ∀ k, 1 ≤ k → k < 10 → (s.data[descBase + k]?).map Fin.val = some 0
      else
        ∃ (dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
            exitDepthPtr exitStoredPtr exitPriorPtr : Nat),
          (s.data[descBase + descDict]?).map Fin.val = some dictPtr ∧
          (s.data[descBase + descBackFst]?).map Fin.val = some backFstPtr ∧
          (s.data[descBase + descBackSnd]?).map Fin.val = some backSndPtr ∧
          (s.data[descBase + descLabels]?).map Fin.val = some labelsPtr ∧
          (s.data[descBase + descFEntry]?).map Fin.val = some fEntryPtr ∧
          (s.data[descBase + descFStop]?).map Fin.val = some fStopPtr ∧
          (s.data[descBase + descExitDepth]?).map Fin.val = some exitDepthPtr ∧
          (s.data[descBase + descExitStored]?).map Fin.val = some exitStoredPtr ∧
          (s.data[descBase + descExitPrior]?).map Fin.val = some exitPriorPtr ∧
          sealedInitArenaOff n Q ≤ dictPtr ∧
          sealedInitArenaOff n Q ≤ exitDepthPtr ∧
          sealedInitArenaOff n Q ≤ exitStoredPtr ∧
          sealedInitArenaOff n Q ≤ exitPriorPtr ∧
          (∀ (fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D : Nat),
            (s₀.data[forestPtrsBase + 6 * j.val]?).map Fin.val = some fp0 →
            (s₀.data[forestPtrsBase + 6 * j.val + 1]?).map Fin.val = some fp1 →
            (s₀.data[forestPtrsBase + 6 * j.val + 2]?).map Fin.val = some fp2 →
            (s₀.data[forestPtrsBase + 6 * j.val + 3]?).map Fin.val = some fp3 →
            (s₀.data[forestPtrsBase + 6 * j.val + 4]?).map Fin.val = some fp4 →
            (s₀.data[forestPtrsBase + 6 * j.val + 5]?).map Fin.val = some fp5 →
            ((s₀.data[fp0]?).map Fin.val).getD 0 = D →
            fp1 = fp0 + (1 + 3 * D) →
            fp2 = fp1 + (nD + 1) →
            fp3 = fp2 + (nD + 1) →
            fp4 = fp3 + nD →
            fp5 = fp4 + N_d →
            (s₀.data[exitPtrsBase + 3 * j.val]?).map Fin.val = some ep0 →
            (s₀.data[exitPtrsBase + 3 * j.val + 1]?).map Fin.val = some ep1 →
            (s₀.data[exitPtrsBase + 3 * j.val + 2]?).map Fin.val = some ep2 →
            backFstPtr = dictPtr + (fp1 - fp0) ∧
            backSndPtr = dictPtr + (fp2 - fp0) ∧
            labelsPtr = dictPtr + (fp3 - fp0) ∧
            fEntryPtr = dictPtr + (fp4 - fp0) ∧
            fStopPtr = dictPtr + (fp5 - fp0) ∧
            dictPtr + ((fp5 - fp0) + N_d) ≤ curOff ∧
            exitDepthPtr + N_d ≤ curOff ∧
            exitStoredPtr + 18 * N_d ≤ curOff ∧
            exitPriorPtr + 6 * nD ≤ curOff ∧
            (∀ k < (fp5 - fp0) + N_d, s.data[sealedBase + dictPtr + k]? = s₀.data[fp0 + k]?) ∧
            (∀ k < N_d, s.data[sealedBase + exitDepthPtr + k]? = s₀.data[ep0 + k]?) ∧
            (∀ k < 18 * N_d, s.data[sealedBase + exitStoredPtr + k]? = s₀.data[ep1 + k]?) ∧
            (∀ k < 6 * nD, s.data[sealedBase + exitPriorPtr + k]? = s₀.data[ep2 + k]?))))
  let meas : (Nat × Nat) → Nat := fun dc => Q - dc.1
  let budget : (Nat × Nat) → Nat := fun dc =>
    let d := dc.1
    let rem := Q - d
    let remChildren := (dense.length - 1) -
      (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0
    100 * rem + 480 * remChildren + 2
  have curBound : ∀ d curOff, d ≤ Q →
      curOff ≤ sealedInitArenaOff n Q + 19 * d +
        66 * ((List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0) →
      curOff ≤ retainedLinearFactor * n := by
    intro d curOff hd hc
    have hp := hChildPrefix d (hQ ▸ hd)
    unfold sealedInitArenaOff at hc
    rw [retainedLinearFactor_eq]
    omega
  have hStep : ∀ dc s, inv dc s →
      (∃ t, (dc.1 = Q ∧ t.data.size = workCap ∧
          SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
          (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some dc.2 ∧
          sealedInitArenaOff n Q ≤ dc.2 ∧ dc.2 ≤ retainedLinearFactor * n ∧
          (∀ addr, (addr < sealedBase + hdrTotalWords ∨
              (sealedBase + hdrTotalWords < addr ∧ addr < sealedBase + sealedOwnerDescOff n Q) ∨
              sealedBase + dc.2 ≤ addr) →
            t.data[addr]? = s₀.data[addr]?) ∧
          (∀ j : Fin dense.length,
            let descBase := sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val
            let nD := 1 + (S.childSlice j).length
            (t.data[descBase + descN]?).map Fin.val = some nD ∧
            (if nD < 3 then
              ∀ k, 1 ≤ k → k < 10 → (t.data[descBase + k]?).map Fin.val = some 0
            else
              ∃ (dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
                  exitDepthPtr exitStoredPtr exitPriorPtr : Nat),
                (t.data[descBase + descDict]?).map Fin.val = some dictPtr ∧
                (t.data[descBase + descBackFst]?).map Fin.val = some backFstPtr ∧
                (t.data[descBase + descBackSnd]?).map Fin.val = some backSndPtr ∧
                (t.data[descBase + descLabels]?).map Fin.val = some labelsPtr ∧
                (t.data[descBase + descFEntry]?).map Fin.val = some fEntryPtr ∧
                (t.data[descBase + descFStop]?).map Fin.val = some fStopPtr ∧
                (t.data[descBase + descExitDepth]?).map Fin.val = some exitDepthPtr ∧
                (t.data[descBase + descExitStored]?).map Fin.val = some exitStoredPtr ∧
                (t.data[descBase + descExitPrior]?).map Fin.val = some exitPriorPtr ∧
                (∀ (fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D : Nat),
                  (s₀.data[forestPtrsBase + 6 * j.val]?).map Fin.val = some fp0 →
                  (s₀.data[forestPtrsBase + 6 * j.val + 1]?).map Fin.val = some fp1 →
                  (s₀.data[forestPtrsBase + 6 * j.val + 2]?).map Fin.val = some fp2 →
                  (s₀.data[forestPtrsBase + 6 * j.val + 3]?).map Fin.val = some fp3 →
                  (s₀.data[forestPtrsBase + 6 * j.val + 4]?).map Fin.val = some fp4 →
                  (s₀.data[forestPtrsBase + 6 * j.val + 5]?).map Fin.val = some fp5 →
                  ((s₀.data[fp0]?).map Fin.val).getD 0 = D →
                  fp1 = fp0 + (1 + 3 * D) →
                  fp2 = fp1 + (nD + 1) →
                  fp3 = fp2 + (nD + 1) →
                  fp4 = fp3 + nD →
                  fp5 = fp4 + N_d →
                  (s₀.data[exitPtrsBase + 3 * j.val]?).map Fin.val = some ep0 →
                  (s₀.data[exitPtrsBase + 3 * j.val + 1]?).map Fin.val = some ep1 →
                  (s₀.data[exitPtrsBase + 3 * j.val + 2]?).map Fin.val = some ep2 →
                  backFstPtr = dictPtr + (fp1 - fp0) ∧
                  backSndPtr = dictPtr + (fp2 - fp0) ∧
                  labelsPtr = dictPtr + (fp3 - fp0) ∧
                  fEntryPtr = dictPtr + (fp4 - fp0) ∧
                  fStopPtr = dictPtr + (fp5 - fp0) ∧
                  dictPtr + ((fp5 - fp0) + N_d) ≤ dc.2 ∧
                  exitDepthPtr + N_d ≤ dc.2 ∧
                  exitStoredPtr + 18 * N_d ≤ dc.2 ∧
                  exitPriorPtr + 6 * nD ≤ dc.2 ∧
                  (∀ k < (fp5 - fp0) + N_d, t.data[sealedBase + dictPtr + k]? = s₀.data[fp0 + k]?) ∧
                  (∀ k < N_d, t.data[sealedBase + exitDepthPtr + k]? = s₀.data[ep0 + k]?) ∧
                  (∀ k < 18 * N_d, t.data[sealedBase + exitStoredPtr + k]? = s₀.data[ep1 + k]?) ∧
                  (∀ k < 6 * nD, t.data[sealedBase + exitPriorPtr + k]? = s₀.data[ep2 + k]?))))) ∧
        ∃ k, k ≤ budget dc ∧ run code input k s = some ⟨t, k⟩) ∨
      (∃ dc' s' k, meas dc' < meas dc ∧ k + budget dc' ≤ budget dc ∧
        Steps code input k s s' ∧ inv dc' s') := by
    intro dc s ⟨hd, hpc, hsz, hRs, hr10, hDescPtr, hTotPtr, hCurLo, hCurHi, hFr, hDone⟩
    let d := dc.1
    let curOff := dc.2
    have hCur128 : curOff ≤ retainedLinearFactor * n := curBound d curOff hd hCurHi
    have hSBnd : sealedBase + curOff ≤ workCap := Nat.le_trans (Nat.add_le_add_left hCur128 sealedBase) hDisj.sealed_fit
    by_cases hdQ : d = Q
    · left
      have hFalse : WordOps.ltb (reg s r10) (reg s r5) = false :=
        branchLt_false (by rw [hr10, hRs.qVal]; exact Nat.le_of_eq hdQ.symm)
      have hBr := step_branchLt_at (code := code) (input := input)
        (by rw [hpc, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hFalse, ite_eq_right (by decide), hCodeSz]; omega)
      rw [hFalse, ite_eq_right (by decide)] at hBr
      let t : State L16 := { s with pc := 177 }
      have hHalt : step code input t = some (.halted t) :=
        step_halt_at (by change code[177]? = some .halt; rw [hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl)
      have hRun2 : run code input 2 s = some ⟨t, 2⟩ := (step1 hBr).halts hHalt
      have hBud : 2 ≤ budget dc := by
        dsimp [budget]
        have hSub : d ≤ dense.length := hQ ▸ hd
        have hPref := hChildPrefix d hSub
        have : (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 ≤
            dense.length - 1 := by rw [hQ] at hPref; exact hPref
        omega
      have htDone : ∀ j : Fin dense.length,
          let descBase := sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val
          let nD := 1 + (S.childSlice j).length
          (t.data[descBase + descN]?).map Fin.val = some nD ∧
          (if nD < 3 then
            ∀ k, 1 ≤ k → k < 10 → (t.data[descBase + k]?).map Fin.val = some 0
          else
            ∃ (dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
                exitDepthPtr exitStoredPtr exitPriorPtr : Nat),
              (t.data[descBase + descDict]?).map Fin.val = some dictPtr ∧
              (t.data[descBase + descBackFst]?).map Fin.val = some backFstPtr ∧
              (t.data[descBase + descBackSnd]?).map Fin.val = some backSndPtr ∧
              (t.data[descBase + descLabels]?).map Fin.val = some labelsPtr ∧
              (t.data[descBase + descFEntry]?).map Fin.val = some fEntryPtr ∧
              (t.data[descBase + descFStop]?).map Fin.val = some fStopPtr ∧
              (t.data[descBase + descExitDepth]?).map Fin.val = some exitDepthPtr ∧
              (t.data[descBase + descExitStored]?).map Fin.val = some exitStoredPtr ∧
              (t.data[descBase + descExitPrior]?).map Fin.val = some exitPriorPtr ∧
              (∀ (fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D : Nat),
                (s₀.data[forestPtrsBase + 6 * j.val]?).map Fin.val = some fp0 →
                (s₀.data[forestPtrsBase + 6 * j.val + 1]?).map Fin.val = some fp1 →
                (s₀.data[forestPtrsBase + 6 * j.val + 2]?).map Fin.val = some fp2 →
                (s₀.data[forestPtrsBase + 6 * j.val + 3]?).map Fin.val = some fp3 →
                (s₀.data[forestPtrsBase + 6 * j.val + 4]?).map Fin.val = some fp4 →
                (s₀.data[forestPtrsBase + 6 * j.val + 5]?).map Fin.val = some fp5 →
                ((s₀.data[fp0]?).map Fin.val).getD 0 = D →
                fp1 = fp0 + (1 + 3 * D) →
                fp2 = fp1 + (nD + 1) →
                fp3 = fp2 + (nD + 1) →
                fp4 = fp3 + nD →
                fp5 = fp4 + N_d →
                (s₀.data[exitPtrsBase + 3 * j.val]?).map Fin.val = some ep0 →
                (s₀.data[exitPtrsBase + 3 * j.val + 1]?).map Fin.val = some ep1 →
                (s₀.data[exitPtrsBase + 3 * j.val + 2]?).map Fin.val = some ep2 →
                backFstPtr = dictPtr + (fp1 - fp0) ∧
                backSndPtr = dictPtr + (fp2 - fp0) ∧
                labelsPtr = dictPtr + (fp3 - fp0) ∧
                fEntryPtr = dictPtr + (fp4 - fp0) ∧
                fStopPtr = dictPtr + (fp5 - fp0) ∧
                dictPtr + ((fp5 - fp0) + N_d) ≤ dc.2 ∧
                exitDepthPtr + N_d ≤ dc.2 ∧
                exitStoredPtr + 18 * N_d ≤ dc.2 ∧
                exitPriorPtr + 6 * nD ≤ dc.2 ∧
                (∀ k < (fp5 - fp0) + N_d, t.data[sealedBase + dictPtr + k]? = s₀.data[fp0 + k]?) ∧
                (∀ k < N_d, t.data[sealedBase + exitDepthPtr + k]? = s₀.data[ep0 + k]?) ∧
                (∀ k < 18 * N_d, t.data[sealedBase + exitStoredPtr + k]? = s₀.data[ep1 + k]?) ∧
                (∀ k < 6 * nD, t.data[sealedBase + exitPriorPtr + k]? = s₀.data[ep2 + k]?))) := fun j => by
        have hj := hDone j (by omega)
        dsimp only at hj ⊢
        refine ⟨hj.1, ?_⟩
        have hj2 := hj.2
        by_cases hSmJ : 1 + (S.childSlice j).length < 3
        · rw [ite_eq_left hSmJ] at hj2 ⊢
          exact hj2
        · rw [ite_eq_right hSmJ] at hj2 ⊢
          rcases hj2 with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, _, _, _, _, hCp⟩
          exact ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hCp⟩
      have hRt : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t :=
        { consts :=
            { zero := hRs.consts.zero
              one := hRs.consts.one
              nVal := hRs.consts.nVal
              mVal := hRs.consts.mVal
              rootVal := hRs.consts.rootVal }
          qVal := hRs.qVal
          treeBaseVal := hRs.treeBaseVal
          forestPtrsVal := hRs.forestPtrsVal
          exitPtrsVal := hRs.exitPtrsVal
          sealedBaseVal := hRs.sealedBaseVal }
      refine ⟨t, ⟨hdQ, hsz, hRt, hTotPtr, hCurLo, hCur128, hFr, htDone⟩, 2, ?_, hRun2⟩
      exact Nat.le_trans (by decide) hBud
    · right
      have hdLt : d < Q := Nat.lt_of_le_of_ne hd hdQ
      have hdFin : d < dense.length := hQ ▸ hdLt
      let dFin : Fin dense.length := ⟨d, hdFin⟩
      let descBase := sealedBase + sealedOwnerDescOff n Q + ownerDescStride * d
      let nD := 1 + (S.childSlice dFin).length
      have hnDEq : nD = 1 + (S.childStart (d + 1) - S.childStart d) := hChildBound dFin
      have hDescLe : descBase + ownerDescStride ≤ sealedBase + sealedInitArenaOff n Q := by
        unfold descBase sealedOwnerDescOff sealedInitArenaOff ownerDescStride; omega
      have hDesc10Le : descBase + 10 ≤ sealedBase + sealedInitArenaOff n Q := hDescLe
      have hDescFit : descBase + ownerDescStride ≤ workCap := by omega
      have hNotDesc : ∀ addr, (addr < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ addr) →
          addr ≠ descBase := fun addr h => by
        rcases h with h | h
        · unfold descBase sealedOwnerDescOff hdrTotalWords at *; omega
        · rw [retainedLinearFactor_eq] at h
          have h128le : sealedBase + sealedInitArenaOff n Q ≤ sealedBase + 128 * n := by
            unfold sealedInitArenaOff; omega
          have : descBase + 10 ≤ addr := Nat.le_trans hDesc10Le (Nat.le_trans h128le h)
          omega
      have hOutDesc10 : ∀ addr, (addr < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ addr) →
          addr < descBase + 1 ∨ descBase + 10 ≤ addr := fun addr h => by
        rcases h with h | h
        · exact Or.inl (by unfold descBase sealedOwnerDescOff hdrTotalWords at *; omega)
        · rw [retainedLinearFactor_eq] at h
          have h128le : sealedBase + sealedInitArenaOff n Q ≤ sealedBase + 128 * n := by
            unfold sealedInitArenaOff; omega
          exact Or.inr (Nat.le_trans hDesc10Le (Nat.le_trans h128le h))
      have hSBHdr : sealedBase + hdrOwnerDesc < workCap := by
        rw [hdrOwnerDesc_eq]; unfold descBase sealedOwnerDescOff ownerDescStride at hDescFit; omega
      have hFrTree : ∀ addr, treeBase ≤ addr → addr < treeBase + staticTreeWords Q → s.data[addr]? = s₀.data[addr]? := by
        intro addr ha1 ha2
        apply hFr addr
        rcases hDisj.disj_tree with h | h
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inl (by rw [hdrTotalWords_eq]; omega)
      have hCS0 : (s.data[treeBase + 7 * Q + d]?).map Fin.val = some (S.childStart d) := by
        rw [hFrTree _ (by omega) (by unfold staticTreeWords; omega)]
        exact hChildStart d (Nat.le_of_lt hdLt)
      have hCS1 : (s.data[treeBase + 7 * Q + d + 1]?).map Fin.val = some (S.childStart (d + 1)) := by
        rw [hFrTree _ (by omega) (by unfold staticTreeWords; omega)]
        simpa [Nat.add_assoc] using hChildStart (d + 1) hdLt
      have hMonoCS : S.childStart d ≤ S.childStart (d + 1) :=
        S.childStart_mono d (d + 1) (Nat.le_succ d) (hQ ▸ hdLt)
      have hCS_le : S.childStart (d + 1) - S.childStart d ≤ Q - 1 := by
        have hm0 := S.childStart_mono 0 d (Nat.zero_le d) (Nat.le_of_lt (hQ ▸ hdLt))
        have hm1 := S.childStart_mono (d + 1) dense.length (hQ ▸ hdLt) (Nat.le_refl _)
        rw [S.childStart_zero] at hm0
        rw [S.childStart_end] at hm1
        omega
      obtain ⟨s24, hs24, pc24, sz24, r24_11, r24_12, r24_15, hPres24, hDescN24, hFr24⟩ :=
        sealedOwners_preamble (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
          h32 hBits (d := d) (descBase := descBase) rfl hnDEq hRs.consts.one hRs.qVal hRs.treeBaseVal hRs.sealedBaseVal hr10 hdLt hpc hsz
          hDescPtr hDescFit hTreeFit hSBHdr hCS0 hCS1 hMonoCS hCS_le
      have hPrefSucc : (List.range (d + 1)).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 =
          (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 +
            (S.childStart (d + 1) - S.childStart d) := by
        rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hPrefLe : (List.range (d + 1)).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 ≤
          dense.length - 1 := by
        have hSub : d + 1 ≤ dense.length := hQ ▸ hdLt
        have hp := hChildPrefix (d + 1) hSub
        rw [hQ] at hp
        exact hp
      by_cases hSmall : nD < 3
      · obtain ⟨sNext, hsNext, pcNext, szNext, rNext_10, hPresSmall, hZeros, hFrSmall⟩ :=
          sealedOwners_small_step (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
            h32 hBits (d := d) (descBase := descBase) pc24 sz24
            (by rw [hPres24 rZero (by decide) (by decide) (by decide)]; exact hRs.consts.zero)
            (by rw [hPres24 rOne (by decide) (by decide) (by decide)]; exact hRs.consts.one)
            (by rw [hPres24 r10 (by decide) (by decide) (by decide)]; exact hr10)
            r24_11 r24_12 r24_15 hSmall hDescFit
            (by unfold descBase sealedOwnerDescOff ownerDescStride at hDescFit; omega)
        have hPresN : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → r ≠ r12 → r ≠ r15 → reg sNext r = reg s r :=
          fun r h0 h1 h2 h5 => by rw [hPresSmall r h0 h1 h2 h5, hPres24 r h1 h2 h5]
        have hDataN : ∀ addr, (addr < descBase ∨ descBase + 10 ≤ addr) → sNext.data[addr]? = s.data[addr]? :=
          fun addr hOut => by
            rcases hOut with h | h
            · rw [hFrSmall addr (Or.inl (by unfold descBase at h ⊢; omega)),
                hFr24 addr (by unfold descBase at h ⊢; omega)]
            · rw [hFrSmall addr (Or.inr h), hFr24 addr (by unfold descBase at h ⊢; omega)]
        refine ⟨⟨d + 1, curOff⟩, sNext, 23 + 43, by dsimp [meas]; omega, ?_, hs24.append hsNext, ?_⟩
        · have hPrefLe' : (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 +
              (S.childStart (d + 1) - S.childStart d) ≤ dense.length - 1 := by
            rw [← hPrefSucc]; exact hPrefLe
          dsimp only [budget, d, curOff]
          rw [hPrefSucc]
          exact so_small_budget_arith Q dc.1 dense.length _ _ hdLt hPrefLe'
        · refine ⟨hdLt, pcNext, szNext, ?_, rNext_10, ?_, ?_, hCurLo, ?_, ?_, ?_⟩
          · exact
              { consts :=
                  { zero := by rw [hPresN rZero (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.zero
                    one := by rw [hPresN rOne (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.one
                    nVal := by rw [hPresN rN (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.nVal
                    mVal := by rw [hPresN rM (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.mVal
                    rootVal := by rw [hPresN rRoot (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.rootVal }
                qVal := by rw [hPresN r5 (by decide) (by decide) (by decide) (by decide)]; exact hRs.qVal
                treeBaseVal := by rw [hPresN r6 (by decide) (by decide) (by decide) (by decide)]; exact hRs.treeBaseVal
                forestPtrsVal := by rw [hPresN r7 (by decide) (by decide) (by decide) (by decide)]; exact hRs.forestPtrsVal
                exitPtrsVal := by rw [hPresN r8 (by decide) (by decide) (by decide) (by decide)]; exact hRs.exitPtrsVal
                sealedBaseVal := by rw [hPresN r9 (by decide) (by decide) (by decide) (by decide)]; exact hRs.sealedBaseVal }
          · rw [hDataN _ (Or.inl (by unfold descBase sealedOwnerDescOff hdrOwnerDesc; omega))]; exact hDescPtr
          · rw [hDataN _ (Or.inl (by unfold descBase sealedOwnerDescOff hdrTotalWords; omega))]; exact hTotPtr
          · dsimp only [d, curOff]
            rw [hPrefSucc]
            exact so_small_cur_arith (sealedInitArenaOff n Q) dc.2 dc.1 _ _ hCurHi
          · intro addr hOut
            rw [hDataN addr (by
              rcases hOut with h | h | h
              · exact Or.inl (by unfold descBase sealedOwnerDescOff hdrTotalWords at *; omega)
              · exact Or.inl (by unfold descBase sealedOwnerDescOff at *; omega)
              · exact Or.inr (Nat.le_trans hDesc10Le (Nat.le_trans (Nat.add_le_add_left hCurLo sealedBase) h)))]
            exact hFr addr hOut
          · intro j hj
            by_cases hjd : j.val = d
            · have hjEq : j = dFin := Fin.ext hjd
              rw [hjEq]
              dsimp only
              refine ⟨?_, ?_⟩
              · rw [hFrSmall _ (Or.inl (by rw [descN_eq, Nat.add_zero]; exact Nat.lt_succ_self _))]
                exact hDescN24
              · rw [ite_eq_left hSmall]
                exact hZeros
            · have hjLt : j.val < d := by omega
              have hjPrev := hDone j hjLt
              have hKeep : ∀ addr,
                  sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val ≤ addr →
                  addr < sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val + 10 →
                  sNext.data[addr]? = s.data[addr]? := fun addr ha1 ha2 =>
                hDataN addr (Or.inl (by unfold descBase ownerDescStride at *; omega))
              dsimp only at hjPrev ⊢
              rw [hKeep _ (by omega) (by rw [descN_eq]; omega)]
              refine ⟨hjPrev.1, ?_⟩
              have hj2 := hjPrev.2
              by_cases hSmJ : 1 + (S.childSlice j).length < 3
              · rw [ite_eq_left hSmJ] at hj2 ⊢
                exact fun k hk1 hk2 => by rw [hKeep _ (by omega) (by omega)]; exact hj2 k hk1 hk2
              · rw [ite_eq_right hSmJ] at hj2 ⊢
                rcases hj2 with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hDGe, hEDGe, hESGe, hEPGe, hCp⟩
                refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9,
                  by rw [hKeep _ (by rw [descDict_eq]; omega) (by rw [descDict_eq]; omega)]; exact hp1,
                  by rw [hKeep _ (by rw [descBackFst_eq]; omega) (by rw [descBackFst_eq]; omega)]; exact hp2,
                  by rw [hKeep _ (by rw [descBackSnd_eq]; omega) (by rw [descBackSnd_eq]; omega)]; exact hp3,
                  by rw [hKeep _ (by rw [descLabels_eq]; omega) (by rw [descLabels_eq]; omega)]; exact hp4,
                  by rw [hKeep _ (by rw [descFEntry_eq]; omega) (by rw [descFEntry_eq]; omega)]; exact hp5,
                  by rw [hKeep _ (by rw [descFStop_eq]; omega) (by rw [descFStop_eq]; omega)]; exact hp6,
                  by rw [hKeep _ (by rw [descExitDepth_eq]; omega) (by rw [descExitDepth_eq]; omega)]; exact hp7,
                  by rw [hKeep _ (by rw [descExitStored_eq]; omega) (by rw [descExitStored_eq]; omega)]; exact hp8,
                  by rw [hKeep _ (by rw [descExitPrior_eq]; omega) (by rw [descExitPrior_eq]; omega)]; exact hp9,
                  hDGe, hEDGe, hESGe, hEPGe, ?_⟩
                intro fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, c1, c2, c3, c4⟩ :=
                  hCp fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                refine ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9,
                  fun k hk => by rw [hDataN _ (Or.inr (Nat.le_trans hDesc10Le (Nat.le_trans (Nat.add_le_add_left hDGe sealedBase) (Nat.le_add_right _ k))))]; exact c1 k hk,
                  fun k hk => by rw [hDataN _ (Or.inr (Nat.le_trans hDesc10Le (Nat.le_trans (Nat.add_le_add_left hEDGe sealedBase) (Nat.le_add_right _ k))))]; exact c2 k hk,
                  fun k hk => by rw [hDataN _ (Or.inr (Nat.le_trans hDesc10Le (Nat.le_trans (Nat.add_le_add_left hESGe sealedBase) (Nat.le_add_right _ k))))]; exact c3 k hk,
                  fun k hk => by rw [hDataN _ (Or.inr (Nat.le_trans hDesc10Le (Nat.le_trans (Nat.add_le_add_left hEPGe sealedBase) (Nat.le_add_right _ k))))]; exact c4 k hk⟩
      · as_aux_lemma =>
        have hLarge : 3 ≤ nD := Nat.le_of_not_lt hSmall
        have hArD := hArena dFin
        dsimp only [OwnerExitArenaAt] at hArD
        rw [dite_eq_left hLarge] at hArD
        rcases hArD with ⟨_, _, _, _, _, wCols, _, _, _, _, _, _, _, _, _, _,
          fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2,
          _, _, _, hfp0, hfp1, hfp2, hfp3, hfp4, hfp5, hD1, hD2, hD3, hD4, hD5,
          hwDict, hwBF, hwBS, hwLab, hwStop, hwLe, hwWc, hFA1, hFA2,
          _, _, _, _, _, _, _, _, _, _, _, _, hep0, hep1, hep2,
          hEA0a, hEA0b, hEA1a, hEA1b, hEA2a, hEA2b, _, _, _, _, _⟩
        let N_d := wCols.entry.size
        let wc := (fp5 - fp0) + N_d
        have hWcSum : wCols.wordCount = wc := by
          dsimp only [WordColumns.wordCount, wc, N_d]
          rw [hwDict, hwBF, hwBS, hwLab, hwStop, hD5, hD4, hD3, hD2, hD1]
          exact so_wc_arith fp0 (((s₀.data[fp0]?).map Fin.val).getD 0) nD wCols.entry.size
        have hND_le : N_d ≤ nD + 1 := hwLe
        have hCurInc : wc + (N_d + 18 * N_d + 6 * nD) ≤ 19 + 66 * (S.childStart (d + 1) - S.childStart d) := by
          rw [← hWcSum]
          have hWcBd : wCols.wordCount ≤ 19 * nD := hwWc
          have hStep : wCols.wordCount + (N_d + 18 * N_d + 6 * nD) ≤
              19 * nD + (nD + 1 + 18 * (nD + 1) + 6 * nD) :=
            Nat.add_le_add hWcBd
              (Nat.add_le_add (Nat.add_le_add hND_le (Nat.mul_le_mul_left 18 hND_le)) (Nat.le_refl _))
          refine Nat.le_trans hStep ?_
          have h3cs : 3 ≤ 1 + (S.childStart (d + 1) - S.childStart d) := hnDEq ▸ hLarge
          have hCsGe : 2 ≤ S.childStart (d + 1) - S.childStart d := Nat.le_of_add_le_add_left (a := 1) h3cs
          rw [hnDEq]
          exact so_cur_arith _ hCsGe
        let cur1 := curOff + wc
        let cur2 := cur1 + N_d
        let cur3 := cur2 + 18 * N_d
        let cur4 := cur3 + 6 * nD
        have hNextCur128 : cur4 ≤ retainedLinearFactor * n := by
          have hp : (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 +
              (S.childStart (d + 1) - S.childStart d) ≤ Q - 1 := by
            have hSub := hChildPrefix (d + 1) (hQ ▸ hdLt)
            rwa [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil] at hSub
          have hCurHi' : curOff ≤ 16 + n + 21 * Q +
              19 * d + 66 * ((List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0) :=
            hCurHi
          have hAssoc : cur4 = curOff + (wc + (N_d + 18 * N_d + 6 * nD)) := by
            dsimp only [cur4, cur3, cur2, cur1]
            simp only [Nat.add_assoc]
          have hSumStep : cur4 ≤ (16 + n + 21 * Q + 19 * d +
              66 * ((List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0)) +
              (19 + 66 * (S.childStart (d + 1) - S.childStart d)) := by
            rw [hAssoc]
            exact Nat.add_le_add hCurHi' hCurInc
          rw [retainedLinearFactor_eq]
          exact Nat.le_trans hSumStep (so_cur128_arith n Q d _ _ hn hQn hdLt hp)
        have hNextCurWork : sealedBase + cur4 ≤ workCap :=
          Nat.le_trans (Nat.add_le_add_left hNextCur128 sealedBase) hDisj.sealed_fit
        have hS0Same : ∀ addr,
            (forestPtrsBase ≤ addr ∧ addr < forestPtrsBase + 6 * Q) ∨
            (forestArenaBase ≤ addr ∧ addr < forestArenaBase + forestUsed) ∨
            (exitPtrsBase ≤ addr ∧ addr < exitPtrsBase + 3 * Q) ∨
            (exitArenaBase ≤ addr ∧ addr < exitArenaBase + exitUsed) →
            s24.data[addr]? = s₀.data[addr]? := fun addr hReg => by
          rw [hFr24 addr (hNotDesc addr (by
            rcases hReg with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
            · rcases hDisj.disj_fPtrs with h | h
              · exact Or.inr (Nat.le_trans h ha)
              · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
            · rcases hDisj.disj_fArena with h | h
              · exact Or.inr (Nat.le_trans h ha)
              · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
            · rcases hDisj.disj_ePtrs with h | h
              · exact Or.inr (Nat.le_trans h ha)
              · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
            · rcases hDisj.disj_eArena with h | h
              · exact Or.inr (Nat.le_trans h ha)
              · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))))]
          apply hFr addr
          rcases hReg with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · rcases hDisj.disj_fPtrs with h | h
            · exact Or.inr (Or.inr (Nat.le_trans (Nat.add_le_add_left hCur128 sealedBase) (Nat.le_trans h ha)))
            · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
          · rcases hDisj.disj_fArena with h | h
            · exact Or.inr (Or.inr (Nat.le_trans (Nat.add_le_add_left hCur128 sealedBase) (Nat.le_trans h ha)))
            · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
          · rcases hDisj.disj_ePtrs with h | h
            · exact Or.inr (Or.inr (Nat.le_trans (Nat.add_le_add_left hCur128 sealedBase) (Nat.le_trans h ha)))
            · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
          · rcases hDisj.disj_eArena with h | h
            · exact Or.inr (Or.inr (Nat.le_trans (Nat.add_le_add_left hCur128 sealedBase) (Nat.le_trans h ha)))
            · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
        have hTot24 : (s24.data[sealedBase + hdrTotalWords]?).map Fin.val = some curOff := by
          rw [hFr24 _ (by unfold descBase sealedOwnerDescOff hdrTotalWords; omega)]
          exact hTotPtr
        have hFP24_eq : ∀ j < 6, s24.data[forestPtrsBase + 6 * d + j]? = s₀.data[forestPtrsBase + 6 * d + j]? :=
          fun j hj => hS0Same _ (Or.inl ⟨by omega, by omega⟩)
        have hEP24_eq : ∀ j < 3, s24.data[exitPtrsBase + 3 * d + j]? = s₀.data[exitPtrsBase + 3 * d + j]? :=
          fun j hj => hS0Same _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
        have hOutReg : ∀ addr, (addr < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ addr) →
            (addr < descBase + 1 ∨ descBase + 10 ≤ addr) ∧
            (addr < descBase + 7 ∨ descBase + 8 ≤ addr) ∧
            (addr < descBase + 8 ∨ descBase + 9 ≤ addr) ∧
            (addr < descBase + 9 ∨ descBase + 10 ≤ addr) ∧
            (addr < sealedBase + curOff ∨ sealedBase + cur4 ≤ addr) := fun addr h =>
          ⟨hOutDesc10 addr h,
           by rcases hOutDesc10 addr h with h1 | h1
              · exact Or.inl (Nat.lt_of_lt_of_le h1 (Nat.add_le_add_left (by decide) _))
              · exact Or.inr (Nat.le_trans (Nat.add_le_add_left (by decide) _) h1),
           by rcases hOutDesc10 addr h with h1 | h1
              · exact Or.inl (Nat.lt_of_lt_of_le h1 (Nat.add_le_add_left (by decide) _))
              · exact Or.inr (Nat.le_trans (Nat.add_le_add_left (by decide) _) h1),
           by rcases hOutDesc10 addr h with h1 | h1
              · exact Or.inl (Nat.lt_of_lt_of_le h1 (Nat.add_le_add_left (by decide) _))
              · exact Or.inr h1,
           by rcases h with h1 | h1
              · exact Or.inl (Nat.lt_of_lt_of_le h1 (Nat.add_le_add_left (by rw [hdrTotalWords_eq]; unfold sealedInitArenaOff at hCurLo; omega) _))
              · exact Or.inr (Nat.le_trans (Nat.add_le_add_left hNextCur128 sealedBase) h1)⟩
        have hDisjSub : ∀ a b, (sealedBase + retainedLinearFactor * n ≤ a ∨ b ≤ sealedBase) →
            ∀ x, a ≤ x → x < b →
            x < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ x :=
          fun a b h x ha hb => by
            rcases h with h | h
            · exact Or.inr (Nat.le_trans h ha)
            · exact Or.inl (by rw [hdrTotalWords_eq]; exact Nat.lt_of_lt_of_le hb (Nat.le_trans h (Nat.le_add_right _ _)))
        have hFP_out : ∀ k ≤ 5,
            forestPtrsBase + 6 * d + k < sealedBase + hdrTotalWords ∨
            sealedBase + retainedLinearFactor * n ≤ forestPtrsBase + 6 * d + k := fun k hk =>
          hDisjSub _ _ hDisj.disj_fPtrs _ (by omega)
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hk) _) (by omega))
        have hFAEnd : fp0 + wc ≤ forestArenaBase + forestUsed := by
          have hLe : fp0 ≤ fp5 := by simp only [hD5, hD4, hD3, hD2, hD1]; omega
          have hSpan : fp0 + wc = fp5 + wCols.stop.size := by
            dsimp only [wc, N_d]
            rw [hwStop, ← Nat.add_assoc, Nat.add_sub_cancel' hLe]
          rw [hSpan]
          exact hFA2
        have hFA_out : ∀ k < wc,
            fp0 + k < sealedBase + hdrTotalWords ∨
            sealedBase + retainedLinearFactor * n ≤ fp0 + k := fun k hk =>
          hDisjSub _ _ hDisj.disj_fArena _ (Nat.le_trans hFA1 (Nat.le_add_right _ _))
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk fp0) hFAEnd)
        have hEP_out : ∀ k ≤ 2,
            exitPtrsBase + 3 * d + k < sealedBase + hdrTotalWords ∨
            sealedBase + retainedLinearFactor * n ≤ exitPtrsBase + 3 * d + k := fun k hk =>
          hDisjSub _ _ hDisj.disj_ePtrs _ (by omega)
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hk) _) (by omega))
        have hEA0_out : ∀ k < N_d,
            ep0 + k < sealedBase + hdrTotalWords ∨
            sealedBase + retainedLinearFactor * n ≤ ep0 + k := fun k hk =>
          hDisjSub _ _ hDisj.disj_eArena _ (Nat.le_trans hEA0a (Nat.le_add_right _ _))
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk ep0) hEA0b)
        have hEA1_out : ∀ k < 18 * N_d,
            ep1 + k < sealedBase + hdrTotalWords ∨
            sealedBase + retainedLinearFactor * n ≤ ep1 + k := fun k hk =>
          hDisjSub _ _ hDisj.disj_eArena _ (Nat.le_trans hEA1a (Nat.le_add_right _ _))
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk ep1) hEA1b)
        have hEA2_out : ∀ k < 6 * nD,
            ep2 + k < sealedBase + hdrTotalWords ∨
            sealedBase + retainedLinearFactor * n ≤ ep2 + k := fun k hk =>
          hDisjSub _ _ hDisj.disj_eArena _ (Nat.le_trans hEA2a (Nat.le_add_right _ _))
            (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk ep2) hEA2b)
        have hFPFitLocal : fp0 + wc ≤ workCap := Nat.le_trans hFAEnd hFAFit
        have hSafeF : sealedBase + curOff + wc ≤ fp0 ∨ fp0 + wc ≤ sealedBase + curOff ∨ sealedBase + curOff < fp0 := by
          rcases hDisj.disj_fArena with h | h
          · have hCur : curOff + wc ≤ cur4 := by unfold cur4 cur3 cur2 cur1; omega
            have hCurBd := Nat.le_trans hCur hNextCur128
            exact Or.inl (by
              rw [Nat.add_assoc]
              exact Nat.le_trans (Nat.add_le_add_left hCurBd _) (Nat.le_trans h hFA1))
          · exact Or.inr (Or.inl (Nat.le_trans hFAEnd (Nat.le_trans h (Nat.le_add_right _ _))))
        have hDescCur : descBase + 10 ≤ sealedBase + curOff :=
          Nat.le_trans hDesc10Le (Nat.add_le_add_left hCurLo _)
        have hFPtrFit : forestPtrsBase + 6 * d + 6 ≤ workCap := Nat.le_trans (by omega) hFPFit
        have hEPtrFit : exitPtrsBase + 3 * d + 3 ≤ workCap := Nat.le_trans (by omega) hEPFit
        have hTotLtDesc : sealedBase + hdrTotalWords < descBase := by
          simp only [hdrTotalWords_eq, descBase, sealedOwnerDescOff]; omega
        have hTotFit : sealedBase + hdrTotalWords < workCap :=
          Nat.lt_of_lt_of_le hTotLtDesc (Nat.le_trans (Nat.le_add_right _ _) hDescFit)
        have hNdiff : N_d = fp5 - fp4 := by rw [hD5, Nat.add_sub_cancel_left]
        have hCur01 : curOff ≤ cur1 := Nat.le_add_right _ _
        have hCur12 : cur1 ≤ cur2 := Nat.le_add_right _ _
        have hCur23 : cur2 ≤ cur3 := Nat.le_add_right _ _
        have hCur34 : cur3 ≤ cur4 := Nat.le_add_right _ _
        have hCur3Le4 := hCur34
        have hCur2Le4 := Nat.le_trans hCur23 hCur3Le4
        have hCur1Le4 := Nat.le_trans hCur12 hCur2Le4
        have hDescBefore : descBase + 7 ≤ sealedBase + curOff := Nat.le_trans (by omega) hDescCur
        have descApart : ∀ {x k : Nat}, (x < descBase + k ∨ descBase + (k + 1) ≤ x) →
            x ≠ descBase + k := by
          intro x k h
          rcases h with h | h <;> omega
        have hBeforePayload : ∀ {lo hi : Nat}, curOff ≤ lo → hi ≤ cur4 → ∀ {addr},
            (addr < sealedBase + curOff ∨ sealedBase + cur4 ≤ addr) →
            addr < sealedBase + lo ∨ sealedBase + hi ≤ addr := by
          intro lo hi hlo hhi addr h
          exact h.imp (fun h => Nat.lt_of_lt_of_le h (Nat.add_le_add_left hlo _))
            (fun h => Nat.le_trans (Nat.add_le_add_left hhi _) h)
        obtain ⟨s91, hs91, pc91, sz91, r91_12, r91_15, hPres91, wDict, wBF, wBS, wLab, wFE, wFS, hFr91, cpF⟩ :=
          sealedOwners_large_forest (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
            (d := d) (forestPtrsBase := forestPtrsBase) (sealedBase := sealedBase)
            (descBase := descBase) (curOff := curOff) (N_d := N_d) (wc := wc)
            h32 hBits pc24 sz24
            (by rw [hPres24 rOne (by decide) (by decide) (by decide)]; exact hRs.consts.one)
            (by rw [hPres24 r7 (by decide) (by decide) (by decide)]; exact hRs.forestPtrsVal)
            (by rw [hPres24 r9 (by decide) (by decide) (by decide)]; exact hRs.sealedBaseVal)
            (by rw [hPres24 r10 (by decide) (by decide) (by decide)]; exact hr10)
            r24_11 r24_12 r24_15 hLarge hDescFit hDescBefore hFPtrFit hTotFit hTot24
            (by
              have h0 := hFP24_eq 0 (by decide)
              rw [Nat.add_zero] at h0
              rw [h0]; exact hfp0)
            (by rw [hFP24_eq 1 (by decide)]; exact hfp1)
            (by rw [hFP24_eq 2 (by decide)]; exact hfp2)
            (by rw [hFP24_eq 3 (by decide)]; exact hfp3)
            (by rw [hFP24_eq 4 (by decide)]; exact hfp4)
            (by rw [hFP24_eq 5 (by decide)]; exact hfp5)
            hD1 hD2 hD3 hD4 hD5 rfl hFPFitLocal
            (Nat.le_trans (by rw [Nat.add_assoc]; exact Nat.add_le_add_left hCur1Le4 _) hNextCurWork)
            (fun k hk => (hOutReg _ (hFP_out k hk)).1.imp id (Nat.le_trans (Nat.add_le_add_left (by decide : 7 ≤ 10) _)))
            (fun k hk => (hOutReg _ (hFA_out k hk)).1.imp id (Nat.le_trans (Nat.add_le_add_left (by decide : 7 ≤ 10) _)))
            hSafeF
        have hPres91' : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s91 r = reg s r :=
          fun r h1 h2 h3 h4 h5 => by rw [hPres91 r h1 h2 h3 h4 h5, hPres24 r h1 h2 h5]
        have h91Outside : ∀ addr, (addr < descBase + 1 ∨ descBase + 7 ≤ addr) →
            (addr < sealedBase + curOff ∨ sealedBase + cur1 ≤ addr) →
            s91.data[addr]? = s24.data[addr]? := fun addr hd ha =>
          hFr91 addr hd (ha.imp id (by rw [Nat.add_assoc]; exact id))
        have h91Source : ∀ addr,
            (addr < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ addr) →
            s91.data[addr]? = s24.data[addr]? := fun addr ha =>
          h91Outside addr
            ((hOutReg addr ha).1.imp id (Nat.le_trans (Nat.add_le_add_left (by decide : 7 ≤ 10) _)))
            (hBeforePayload (Nat.le_refl _) hCur1Le4 (hOutReg addr ha).2.2.2.2)
        have hSafeE0 : sealedBase + cur1 + N_d ≤ ep0 ∨ ep0 + N_d ≤ sealedBase + cur1 ∨ sealedBase + cur1 < ep0 := by
          rcases hDisj.disj_eArena with h | h
          · apply Or.inl
            rw [Nat.add_assoc]
            exact Nat.le_trans (Nat.add_le_add_left (Nat.le_trans hCur2Le4 hNextCur128) _)
              (Nat.le_trans h hEA0a)
          · exact Or.inr (Or.inl (Nat.le_trans hEA0b (Nat.le_trans h (Nat.le_add_right _ _))))
        obtain ⟨s117, hs117, pc117, sz117, r117_12, r117_15, hPres117, wED, hFr117Raw, cpE0⟩ :=
          sealedOwners_large_exit0 (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
            (d := d) (forestPtrsBase := forestPtrsBase) (exitPtrsBase := exitPtrsBase)
            (sealedBase := sealedBase) (descBase := descBase) (cur1 := cur1) (N_d := N_d)
            h32 hBits pc91 sz91
            (by rw [hPres91' rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.one)
            (by rw [hPres91' r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.forestPtrsVal)
            (by rw [hPres91' r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.exitPtrsVal)
            (by rw [hPres91' r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.sealedBaseVal)
            (by rw [hPres91' r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr10)
            r91_12 r91_15 hDescFit hFPtrFit hEPtrFit (by omega) hNdiff
            (Nat.le_trans hEA0b hEAFit)
            (by rw [Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hCur2Le4 _) hNextCurWork)
            (Nat.lt_of_lt_of_le (by rw [descExitDepth_eq]; omega) (Nat.le_trans hDescCur (Nat.add_le_add_left hCur01 _)))
            (by rw [h91Source _ (hFP_out 4 (by decide)), hFP24_eq 4 (by decide)]; exact hfp4)
            (by rw [h91Source _ (hFP_out 5 (by decide)), hFP24_eq 5 (by decide)]; exact hfp5)
            (by
              have hs0 := h91Source _ (hEP_out 0 (by decide))
              have hp0 := hEP24_eq 0 (by decide)
              simp only [Nat.add_zero] at hs0 hp0
              rw [hs0, hp0]; exact hep0)
            (fun k _ hk => by rw [descExitDepth_eq]; exact descApart (hOutReg _ (hFP_out k hk)).2.1)
            (by rw [descExitDepth_eq]; exact descApart (hOutReg _ (hEP_out 0 (by decide))).2.1)
            (fun k hk => by rw [descExitDepth_eq]; exact descApart (hOutReg _ (hEA0_out k hk)).2.1)
            hSafeE0
        have hFr117 : ∀ addr, addr ≠ descBase + descExitDepth →
            (addr < sealedBase + cur1 ∨ sealedBase + cur2 ≤ addr) →
            s117.data[addr]? = s91.data[addr]? := fun addr hd ha =>
          hFr117Raw addr hd (ha.imp id (by rw [Nat.add_assoc]; exact id))
        have h117Source : ∀ addr,
            (addr < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ addr) →
            s117.data[addr]? = s24.data[addr]? := fun addr ha =>
          (hFr117 addr (by rw [descExitDepth_eq]; exact descApart (hOutReg addr ha).2.1)
            (hBeforePayload hCur01 hCur2Le4 (hOutReg addr ha).2.2.2.2)).trans (h91Source addr ha)
        have hPres117' : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s117 r = reg s r :=
          fun r h1 h2 h3 h4 h5 => by rw [hPres117 r h1 h2 h3 h4 h5, hPres91' r h1 h2 h3 h4 h5]
        have hSafeE1 : sealedBase + cur2 + 18 * N_d ≤ ep1 ∨ ep1 + 18 * N_d ≤ sealedBase + cur2 ∨ sealedBase + cur2 < ep1 := by
          rcases hDisj.disj_eArena with h | h
          · apply Or.inl
            rw [Nat.add_assoc]
            exact Nat.le_trans (Nat.add_le_add_left (Nat.le_trans hCur3Le4 hNextCur128) _)
              (Nat.le_trans h hEA1a)
          · exact Or.inr (Or.inl (Nat.le_trans hEA1b (Nat.le_trans h (Nat.le_add_right _ _))))
        obtain ⟨s149, hs149, pc149, sz149, r149_12, r149_15, hPres149, wES, hFr149Raw, cpE1⟩ :=
          sealedOwners_large_exit1 (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
            (d := d) (forestPtrsBase := forestPtrsBase) (exitPtrsBase := exitPtrsBase)
            (sealedBase := sealedBase) (descBase := descBase) (cur2 := cur2) (N_d := N_d)
            h32 hBits pc117 sz117
            (by rw [hPres117' rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.one)
            (by rw [hPres117' r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.forestPtrsVal)
            (by rw [hPres117' r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.exitPtrsVal)
            (by rw [hPres117' r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.sealedBaseVal)
            (by rw [hPres117' r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr10)
            r117_12 r117_15 hDescFit hFPtrFit hEPtrFit (by omega) hNdiff
            (Nat.le_trans hEA1b hEAFit)
            (by rw [Nat.add_assoc]; exact Nat.le_trans (Nat.add_le_add_left hCur3Le4 _) hNextCurWork)
            (Nat.lt_of_lt_of_le (by rw [descExitStored_eq]; omega)
              (Nat.le_trans hDescCur (Nat.add_le_add_left (Nat.le_trans hCur01 hCur12) _)))
            (by rw [h117Source _ (hFP_out 4 (by decide)), hFP24_eq 4 (by decide)]; exact hfp4)
            (by rw [h117Source _ (hFP_out 5 (by decide)), hFP24_eq 5 (by decide)]; exact hfp5)
            (by rw [h117Source _ (hEP_out 1 (by decide)), hEP24_eq 1 (by decide)]; exact hep1)
            (fun k _ hk => by rw [descExitStored_eq]; exact descApart (hOutReg _ (hFP_out k hk)).2.2.1)
            (by rw [descExitStored_eq]; exact descApart (hOutReg _ (hEP_out 1 (by decide))).2.2.1)
            (fun k hk => by rw [descExitStored_eq]; exact descApart (hOutReg _ (hEA1_out k hk)).2.2.1)
            hSafeE1
        have hFr149 : ∀ addr, addr ≠ descBase + descExitStored →
            (addr < sealedBase + cur2 ∨ sealedBase + cur3 ≤ addr) →
            s149.data[addr]? = s117.data[addr]? := fun addr hd ha =>
          hFr149Raw addr hd (ha.imp id (by rw [Nat.add_assoc]; exact id))
        have h149Source : ∀ addr,
            (addr < sealedBase + hdrTotalWords ∨ sealedBase + retainedLinearFactor * n ≤ addr) →
            s149.data[addr]? = s24.data[addr]? := fun addr ha =>
          (hFr149 addr (by rw [descExitStored_eq]; exact descApart (hOutReg addr ha).2.2.1)
            (hBeforePayload (Nat.le_trans hCur01 hCur12) hCur3Le4 (hOutReg addr ha).2.2.2.2)).trans
            (h117Source addr ha)
        have hPres149' : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s149 r = reg s r :=
          fun r h1 h2 h3 h4 h5 => by rw [hPres149 r h1 h2 h3 h4 h5, hPres117' r h1 h2 h3 h4 h5]
        have hSafeE2 : sealedBase + cur3 + 6 * nD ≤ ep2 ∨ ep2 + 6 * nD ≤ sealedBase + cur3 ∨ sealedBase + cur3 < ep2 := by
          rcases hDisj.disj_eArena with h | h
          · apply Or.inl
            rw [Nat.add_assoc]
            exact Nat.le_trans (Nat.add_le_add_left hNextCur128 _)
              (Nat.le_trans h hEA2a)
          · exact Or.inr (Or.inl (Nat.le_trans hEA2b (Nat.le_trans h (Nat.le_add_right _ _))))
        have hDesc0_149 : (s149.data[descBase + descN]?).map Fin.val = some nD := by
          have hBefore : descBase + descN < sealedBase + curOff := by rw [descN_eq]; omega
          rw [hFr149 _ (by rw [descN_eq, descExitStored_eq]; omega)
                (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left (Nat.le_trans hCur01 hCur12) _))),
            hFr117 _ (by rw [descN_eq, descExitDepth_eq]; omega)
                (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur01 _))),
            h91Outside _ (Or.inl (by rw [descN_eq]; omega)) (Or.inl hBefore)]
          exact hDescN24
        obtain ⟨sNext, hsNext, pcNext, szNext, rNext_10, hPresExit2, wEP, hTotOut, hFrNext, cpE2⟩ :=
          sealedOwners_large_exit2 (bits := bits) (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw)
            (d := d) (exitPtrsBase := exitPtrsBase) (sealedBase := sealedBase) (descBase := descBase)
            (cur3 := cur3) (nD := nD)
            h32 hBits pc149 sz149
            (by rw [hPres149' rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.one)
            (by rw [hPres149' r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.exitPtrsVal)
            (by rw [hPres149' r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.sealedBaseVal)
            (by rw [hPres149' r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr10)
            r149_12 r149_15 hDescFit hEPtrFit (Nat.le_trans hEA2b hEAFit) hNextCurWork hTotFit
            (Nat.lt_of_lt_of_le (by rw [descExitPrior_eq]; omega)
              (Nat.le_trans hDescCur (Nat.add_le_add_left (Nat.le_trans hCur01 (Nat.le_trans hCur12 hCur23)) _)))
            hTotLtDesc (Nat.lt_of_lt_of_le hTotLtDesc (by omega)) hDesc0_149
            (by rw [h149Source _ (hEP_out 2 (by decide)), hEP24_eq 2 (by decide)]; exact hep2)
            (by rw [descExitPrior_eq]; exact descApart (hOutReg _ (hEP_out 2 (by decide))).2.2.2.1)
            (fun k hk => by rw [descExitPrior_eq]; exact descApart (hOutReg _ (hEA2_out k hk)).2.2.2.1)
            hSafeE2
        have hPresN : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg sNext r = reg s r :=
          fun r h0 h1 h2 h3 h4 h5 => by rw [hPresExit2 r h0 h1 h2 h3 h4 h5, hPres149' r h1 h2 h3 h4 h5]
        have hDataOutside : ∀ addr, addr ≠ sealedBase + hdrTotalWords →
            (addr < descBase ∨ descBase + 10 ≤ addr) →
            (addr < sealedBase + curOff ∨ sealedBase + cur4 ≤ addr) →
            sNext.data[addr]? = s.data[addr]? := fun addr hHdr hD hA => by
          rw [hFrNext addr hHdr (by rw [descExitPrior_eq]; rcases hD with h | h <;> omega)
              (by rcases hA with h | h; exact Or.inl (by unfold cur3 cur2 cur1; omega); exact Or.inr h),
            hFr149 addr (by rw [descExitStored_eq]; rcases hD with h | h <;> omega)
              (by rcases hA with h | h; exact Or.inl (by unfold cur2 cur1; omega); exact Or.inr (by unfold cur4 at h; omega)),
            hFr117 addr (by rw [descExitDepth_eq]; rcases hD with h | h <;> omega)
              (by rcases hA with h | h; exact Or.inl (by unfold cur1; omega); exact Or.inr (by unfold cur4 cur3 at h; omega)),
            h91Outside addr (by rcases hD with h | h; exact Or.inl (by omega); exact Or.inr (by omega))
              (by rcases hA with h | h; exact Or.inl h; exact Or.inr (by unfold cur4 cur3 cur2 at h; omega)),
            hFr24 addr (by rcases hD with h | h <;> omega)]
        let kTot := 23 + (52 + (6 * wc + 1)) + (20 + (6 * N_d + 1)) + (26 + (6 * (18 * N_d) + 1)) + (22 + (6 * (6 * nD) + 1))
        have hStepsLarge : Steps code input kTot s sNext := by
          simpa only [kTot, Nat.add_assoc] using
            hs24.append (hs91.append (hs117.append (hs149.append hsNext)))
        have hCur02 : curOff ≤ cur2 := Nat.le_trans hCur01 hCur12
        have hCur03 : curOff ≤ cur3 := Nat.le_trans hCur02 hCur23
        have hCur04 : curOff ≤ cur4 := Nat.le_trans hCur03 hCur34
        have hDescFloor : sealedBase + sealedOwnerDescOff n Q ≤ descBase :=
          Nat.le_add_right _ _
        have hSlotBefore : ∀ k < 10, descBase + k < sealedBase + curOff :=
          fun k hk => Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hDescCur
        have hSlotAfterHeader : ∀ k, sealedBase + hdrTotalWords < descBase + k :=
          fun k => Nat.lt_of_lt_of_le hTotLtDesc (Nat.le_add_right _ _)
        have hPayloadAfterDesc : ∀ {off k j : Nat}, curOff ≤ off → j < 10 →
            descBase + j < sealedBase + off + k := by
          intro off k j ho hj
          exact Nat.lt_of_lt_of_le (hSlotBefore j hj)
            (Nat.le_trans (Nat.add_le_add_left ho _) (Nat.le_add_right _ _))
        have hPayloadAfterHeader : ∀ {off k : Nat}, curOff ≤ off →
            sealedBase + hdrTotalWords < sealedBase + off + k :=
          fun ho => Nat.lt_trans (hSlotAfterHeader 0) (hPayloadAfterDesc ho (by decide))
        refine ⟨⟨d + 1, cur4⟩, sNext, kTot, by dsimp [meas]; omega, ?_, hStepsLarge, ?_⟩
        · have hPrefLe' : (List.range d).foldl (fun acc i => acc + (S.childStart (i + 1) - S.childStart i)) 0 +
              (S.childStart (d + 1) - S.childStart d) ≤ dense.length - 1 := by
            rw [← hPrefSucc]; exact hPrefLe
          have hWcBd : wc ≤ 19 * nD := hWcSum ▸ hwWc
          have h3cs : 3 ≤ 1 + (S.childStart (d + 1) - S.childStart d) := hnDEq ▸ hLarge
          have hCsGe : 2 ≤ S.childStart (d + 1) - S.childStart d := Nat.le_of_add_le_add_left (a := 1) h3cs
          have hKLe : kTot ≤ 100 + 480 * (S.childStart (d + 1) - S.childStart d) := by
            have hKStep : kTot ≤
                23 + (52 + (6 * (19 * nD) + 1)) + (20 + (6 * (nD + 1) + 1)) +
                  (26 + (6 * (18 * (nD + 1)) + 1)) + (22 + (6 * (6 * nD) + 1)) := by
              dsimp only [kTot]
              exact Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add
                    (Nat.add_le_add (Nat.le_refl _)
                      (Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add (Nat.mul_le_mul_left 6 hWcBd) (Nat.le_refl _))))
                    (Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add (Nat.mul_le_mul_left 6 hND_le) (Nat.le_refl _))))
                  (Nat.add_le_add (Nat.le_refl _) (Nat.add_le_add (Nat.mul_le_mul_left 6 (Nat.mul_le_mul_left 18 hND_le)) (Nat.le_refl _))))
                (Nat.le_refl _)
            refine Nat.le_trans hKStep ?_
            rw [hnDEq]
            exact so_budget_arith _ hCsGe
          dsimp only [budget, d]
          rw [hPrefSucc]
          exact so_large_budget_arith kTot Q dc.1 dense.length _ _ hKLe hdLt hPrefLe'
        · refine ⟨hdLt, pcNext, szNext, ?_, rNext_10, ?_, hTotOut, ?_, ?_, ?_, ?_⟩
          · exact
              { consts :=
                  { zero := by rw [hPresN rZero (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.zero
                    one := by rw [hPresN rOne (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.one
                    nVal := by rw [hPresN rN (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.nVal
                    mVal := by rw [hPresN rM (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.mVal
                    rootVal := by rw [hPresN rRoot (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.consts.rootVal }
                qVal := by rw [hPresN r5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.qVal
                treeBaseVal := by rw [hPresN r6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.treeBaseVal
                forestPtrsVal := by rw [hPresN r7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.forestPtrsVal
                exitPtrsVal := by rw [hPresN r8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.exitPtrsVal
                sealedBaseVal := by rw [hPresN r9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hRs.sealedBaseVal }
          · have hHead : sealedBase + hdrOwnerDesc < sealedBase + hdrTotalWords := by
              exact Nat.add_lt_add_left (by decide : hdrOwnerDesc < hdrTotalWords) _
            have hDesc := Nat.lt_trans hHead hTotLtDesc
            rw [hDataOutside _ (Nat.ne_of_lt hHead) (Or.inl hDesc)
              (Or.inl (Nat.lt_trans hDesc (hSlotBefore 0 (by decide))))]
            exact hDescPtr
          · dsimp only [cur4, cur3, cur2, cur1]
            exact Nat.le_trans hCurLo (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
          · have hAssoc : cur4 = curOff + (wc + (N_d + 18 * N_d + 6 * nD)) := by
              dsimp only [cur4, cur3, cur2, cur1]
              simp only [Nat.add_assoc]
            dsimp only [d]
            rw [hPrefSucc, hAssoc]
            exact so_large_cur_arith (sealedInitArenaOff n Q) curOff _ dc.1 _ _ hCurHi hCurInc
          · intro addr hOut
            rcases hOut with h | ⟨h1, h2⟩ | h
            · have hBd := Nat.lt_trans h hTotLtDesc
              rw [hDataOutside addr (Nat.ne_of_lt h) (Or.inl hBd)
                (Or.inl (Nat.lt_trans hBd (hSlotBefore 0 (by decide))))]
              exact hFr addr (Or.inl h)
            · have hBd := Nat.lt_of_lt_of_le h2 hDescFloor
              rw [hDataOutside addr (Nat.ne_of_gt h1) (Or.inl hBd)
                (Or.inl (Nat.lt_trans hBd (hSlotBefore 0 (by decide))))]
              exact hFr addr (Or.inr (Or.inl ⟨h1, h2⟩))
            · have hOld := Nat.le_trans (Nat.add_le_add_left hCur04 _) h
              rw [hDataOutside addr
                (Nat.ne_of_gt (Nat.lt_of_lt_of_le (hPayloadAfterHeader (off := curOff) (k := 0)
                  (Nat.le_refl _)) (by simpa only [Nat.add_zero] using hOld)))
                (Or.inr (Nat.le_trans hDescCur hOld)) (Or.inr h)]
              exact hFr addr (Or.inr (Or.inr hOld))
          · intro j hj
            by_cases hjd : j.val = d
            · have hjEq : j = dFin := Fin.ext hjd
              rw [hjEq]
              dsimp only
              have hKeepDesc : ∀ k < 10, k ≠ descExitDepth → k ≠ descExitStored → k ≠ descExitPrior →
                  sNext.data[descBase + k]? = s91.data[descBase + k]? := fun k hk h7 h8 h9 => by
                have hBefore := hSlotBefore k hk
                rw [hFrNext _ (Nat.ne_of_gt (hSlotAfterHeader k)) (fun h => h9 (Nat.add_left_cancel h))
                    (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur03 _))),
                  hFr149 _ (fun h => h8 (Nat.add_left_cancel h))
                    (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur02 _))),
                  hFr117 _ (fun h => h7 (Nat.add_left_cancel h))
                    (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur01 _)))]
              have hN_slot : (sNext.data[descBase + descN]?).map Fin.val = some nD := by
                have hd7 : descN ≠ descExitDepth := by decide
                have hd8 : descN ≠ descExitStored := by decide
                have hd9 : descN ≠ descExitPrior := by decide
                have hs := hKeepDesc descN (by decide) hd7 hd8 hd9
                have hb := h91Outside (descBase + descN)
                  (Or.inl (Nat.add_lt_add_left (by decide : descN < 1) _))
                  (Or.inl (hSlotBefore descN (by decide)))
                exact (congrArg (Option.map Fin.val) (hs.trans hb)).trans hDescN24
              refine ⟨hN_slot, ?_⟩
              rw [ite_eq_right hSmall]
              refine ⟨curOff, curOff + (fp1 - fp0), curOff + (fp2 - fp0), curOff + (fp3 - fp0),
                curOff + (fp4 - fp0), curOff + (fp5 - fp0), cur1, cur2, cur3,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hCurLo, by unfold cur1; omega, by unfold cur2 cur1; omega, by unfold cur3 cur2 cur1; omega, ?_⟩
              · rw [hKeepDesc descDict (by rw [descDict_eq]; omega) (by unfold descDict descExitDepth; omega) (by unfold descDict descExitStored; omega) (by unfold descDict descExitPrior; omega)]; exact wDict
              · rw [hKeepDesc descBackFst (by rw [descBackFst_eq]; omega) (by unfold descBackFst descExitDepth; omega) (by unfold descBackFst descExitStored; omega) (by unfold descBackFst descExitPrior; omega)]; exact wBF
              · rw [hKeepDesc descBackSnd (by rw [descBackSnd_eq]; omega) (by unfold descBackSnd descExitDepth; omega) (by unfold descBackSnd descExitStored; omega) (by unfold descBackSnd descExitPrior; omega)]; exact wBS
              · rw [hKeepDesc descLabels (by rw [descLabels_eq]; omega) (by unfold descLabels descExitDepth; omega) (by unfold descLabels descExitStored; omega) (by unfold descLabels descExitPrior; omega)]; exact wLab
              · rw [hKeepDesc descFEntry (by rw [descFEntry_eq]; omega) (by unfold descFEntry descExitDepth; omega) (by unfold descFEntry descExitStored; omega) (by unfold descFEntry descExitPrior; omega)]; exact wFE
              · rw [hKeepDesc descFStop (by rw [descFStop_eq]; omega) (by unfold descFStop descExitDepth; omega) (by unfold descFStop descExitStored; omega) (by unfold descFStop descExitPrior; omega)]; exact wFS
              · have hBefore := hSlotBefore descExitDepth (by decide)
                rw [hFrNext (descBase + descExitDepth) (Nat.ne_of_gt (hSlotAfterHeader _))
                    (fun h => (by decide : descExitDepth ≠ descExitPrior) (Nat.add_left_cancel h))
                    (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur03 _))),
                  hFr149 (descBase + descExitDepth)
                    (fun h => (by decide : descExitDepth ≠ descExitStored) (Nat.add_left_cancel h))
                    (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur02 _)))]
                exact wED
              · have hBefore := hSlotBefore descExitStored (by decide)
                rw [hFrNext (descBase + descExitStored) (Nat.ne_of_gt (hSlotAfterHeader _))
                    (fun h => (by decide : descExitStored ≠ descExitPrior) (Nat.add_left_cancel h))
                    (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur03 _)))]
                exact wES
              · exact wEP
              · intro gp0 gp1 gp2 gp3 gp4 gp5 ge0 ge1 ge2 gNd gD ag0 ag1 ag2 ag3 ag4 ag5 aD ad1 ad2 ad3 ad4 ad5 ae0 ae1 ae2
                have e0 : gp0 = fp0 := Option.some.inj (ag0.symm.trans hfp0)
                have e1 : gp1 = fp1 := Option.some.inj (ag1.symm.trans hfp1)
                have e2 : gp2 = fp2 := Option.some.inj (ag2.symm.trans hfp2)
                have e3 : gp3 = fp3 := Option.some.inj (ag3.symm.trans hfp3)
                have e4 : gp4 = fp4 := Option.some.inj (ag4.symm.trans hfp4)
                have e5 : gp5 = fp5 := Option.some.inj (ag5.symm.trans hfp5)
                have ee0 : ge0 = ep0 := Option.some.inj (ae0.symm.trans hep0)
                have ee1 : ge1 = ep1 := Option.some.inj (ae1.symm.trans hep1)
                have ee2 : ge2 = ep2 := Option.some.inj (ae2.symm.trans hep2)
                have egNd : gNd = N_d := by
                  rw [e4, e5] at ad5
                  exact Nat.add_left_cancel (ad5.symm.trans hD5)
                rw [e0, e1, e2, e3, e4, e5, ee0, ee1, ee2, egNd]
                refine ⟨rfl, rfl, rfl, rfl, rfl, hCur1Le4, hCur2Le4, hCur3Le4, Nat.le_refl _,
                  fun k hk => ?_, fun k hk => ?_, fun k hk => ?_, fun k hk => ?_⟩
                · have hBefore : sealedBase + curOff + k < sealedBase + cur1 := by
                    rw [Nat.add_assoc]
                    exact Nat.add_lt_add_left (Nat.add_lt_add_left hk _) _
                  rw [hFrNext _ (Nat.ne_of_gt (hPayloadAfterHeader (Nat.le_refl _)))
                      (Nat.ne_of_gt (hPayloadAfterDesc (Nat.le_refl _) (by decide))) (Or.inl (Nat.lt_of_lt_of_le hBefore
                        (Nat.add_le_add_left (Nat.le_trans hCur12 hCur23) _))),
                    hFr149 _ (Nat.ne_of_gt (hPayloadAfterDesc (Nat.le_refl _) (by decide)))
                      (Or.inl (Nat.lt_of_lt_of_le hBefore (Nat.add_le_add_left hCur12 _))),
                    hFr117 _ (Nat.ne_of_gt (hPayloadAfterDesc (Nat.le_refl _) (by decide))) (Or.inl hBefore),
                    cpF k hk, hS0Same _ (Or.inr (Or.inl ⟨
                      Nat.le_trans hFA1 (Nat.le_add_right _ _),
                      Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hFAEnd⟩))]
                · have hBefore : sealedBase + cur1 + k < sealedBase + cur2 := by
                    rw [Nat.add_assoc]
                    exact Nat.add_lt_add_left (Nat.add_lt_add_left hk _) _
                  rw [hFrNext _ (Nat.ne_of_gt (hPayloadAfterHeader hCur01))
                      (Nat.ne_of_gt (hPayloadAfterDesc hCur01 (by decide))) (Or.inl (Nat.lt_of_lt_of_le hBefore
                        (Nat.add_le_add_left hCur23 _))),
                    hFr149 _ (Nat.ne_of_gt (hPayloadAfterDesc hCur01 (by decide))) (Or.inl hBefore),
                    cpE0 k hk, h91Source _ (hEA0_out k hk),
                    hS0Same _ (Or.inr (Or.inr (Or.inr
                      ⟨Nat.le_trans hEA0a (Nat.le_add_right _ _),
                        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hEA0b⟩)))]
                · have hBefore : sealedBase + cur2 + k < sealedBase + cur3 := by
                    rw [Nat.add_assoc]
                    exact Nat.add_lt_add_left (Nat.add_lt_add_left hk _) _
                  rw [hFrNext _ (Nat.ne_of_gt (hPayloadAfterHeader hCur02))
                      (Nat.ne_of_gt (hPayloadAfterDesc hCur02 (by decide))) (Or.inl hBefore),
                    cpE1 k hk, h117Source _ (hEA1_out k hk),
                    hS0Same _ (Or.inr (Or.inr (Or.inr
                      ⟨Nat.le_trans hEA1a (Nat.le_add_right _ _),
                        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hEA1b⟩)))]
                · rw [cpE2 k hk, h149Source _ (hEA2_out k hk),
                    hS0Same _ (Or.inr (Or.inr (Or.inr
                      ⟨Nat.le_trans hEA2a (Nat.le_add_right _ _),
                        Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hEA2b⟩)))]
            · have hjLt : j.val < d := by omega
              have hjPrev := hDone j hjLt
              have hKeep : ∀ addr,
                  sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val ≤ addr →
                  addr < sealedBase + sealedOwnerDescOff n Q + ownerDescStride * j.val + 10 →
                  sNext.data[addr]? = s.data[addr]? := fun addr ha1 ha2 => by
                have hHeader : sealedBase + hdrTotalWords < sealedBase + sealedOwnerDescOff n Q := by
                  exact Nat.add_lt_add_left (by rw [hdrTotalWords_eq]; unfold sealedOwnerDescOff; omega) _
                have hDesc : addr < descBase := by
                  apply Nat.lt_of_lt_of_le ha2
                  dsimp only [descBase]
                  rw [ownerDescStride_eq]
                  omega
                exact hDataOutside addr
                  (Nat.ne_of_gt (Nat.lt_of_lt_of_le hHeader (Nat.le_trans (Nat.le_add_right _ _) ha1)))
                  (Or.inl hDesc) (Or.inl (Nat.lt_trans hDesc (hSlotBefore 0 (by decide))))
              dsimp only at hjPrev ⊢
              rw [hKeep _ (by omega) (by rw [descN_eq]; omega)]
              refine ⟨hjPrev.1, ?_⟩
              have hj2 := hjPrev.2
              by_cases hSmJ : 1 + (S.childSlice j).length < 3
              · rw [ite_eq_left hSmJ] at hj2 ⊢
                exact fun k hk1 hk2 => by rw [hKeep _ (by omega) (by omega)]; exact hj2 k hk1 hk2
              · rw [ite_eq_right hSmJ] at hj2 ⊢
                rcases hj2 with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hDGe, hEDGe, hESGe, hEPGe, hCp⟩
                refine ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9,
                  by rw [hKeep _ (by rw [descDict_eq]; omega) (by rw [descDict_eq]; omega)]; exact hp1,
                  by rw [hKeep _ (by rw [descBackFst_eq]; omega) (by rw [descBackFst_eq]; omega)]; exact hp2,
                  by rw [hKeep _ (by rw [descBackSnd_eq]; omega) (by rw [descBackSnd_eq]; omega)]; exact hp3,
                  by rw [hKeep _ (by rw [descLabels_eq]; omega) (by rw [descLabels_eq]; omega)]; exact hp4,
                  by rw [hKeep _ (by rw [descFEntry_eq]; omega) (by rw [descFEntry_eq]; omega)]; exact hp5,
                  by rw [hKeep _ (by rw [descFStop_eq]; omega) (by rw [descFStop_eq]; omega)]; exact hp6,
                  by rw [hKeep _ (by rw [descExitDepth_eq]; omega) (by rw [descExitDepth_eq]; omega)]; exact hp7,
                  by rw [hKeep _ (by rw [descExitStored_eq]; omega) (by rw [descExitStored_eq]; omega)]; exact hp8,
                  by rw [hKeep _ (by rw [descExitPrior_eq]; omega) (by rw [descExitPrior_eq]; omega)]; exact hp9,
                  hDGe, hEDGe, hESGe, hEPGe, ?_⟩
                intro gp0 gp1 gp2 gp3 gp4 gp5 ge0 ge1 ge2 gNd gD a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, c1, c2, c3, c4⟩ :=
                  hCp gp0 gp1 gp2 gp3 gp4 gp5 ge0 ge1 ge2 gNd gD a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
                have hKeepPayload : ∀ {off len k : Nat}, sealedInitArenaOff n Q ≤ off →
                    off + len ≤ curOff → k < len →
                    sNext.data[sealedBase + off + k]? = s.data[sealedBase + off + k]? := by
                  intro off len k ho hl hk
                  have hDesc : descBase + 10 ≤ sealedBase + off + k :=
                    Nat.le_trans hDesc10Le
                      (Nat.le_trans (Nat.add_le_add_left ho _) (Nat.le_add_right _ _))
                  have hBefore : sealedBase + off + k < sealedBase + curOff := by
                    rw [Nat.add_assoc]
                    exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hl) _
                  exact hDataOutside _ (Nat.ne_of_gt (Nat.lt_of_lt_of_le hTotLtDesc
                    (Nat.le_trans (Nat.le_add_right _ _) hDesc))) (Or.inr hDesc) (Or.inl hBefore)
                exact ⟨b1, b2, b3, b4, b5, Nat.le_trans b6 hCur04, Nat.le_trans b7 hCur04,
                  Nat.le_trans b8 hCur04, Nat.le_trans b9 hCur04,
                  fun k hk => (hKeepPayload hDGe b6 hk).trans (c1 k hk),
                  fun k hk => (hKeepPayload hEDGe b7 hk).trans (c2 k hk),
                  fun k hk => (hKeepPayload hESGe b8 hk).trans (c3 k hk),
                  fun k hk => (hKeepPayload hEPGe b9 hk).trans (c4 k hk)⟩
  -- Execute PC 0 (`imm r10 0`) and apply `while_steps_budget` from `⟨0, sealedInitArenaOff n Q⟩`
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  obtain ⟨s1, hs1, pc1, r1_10, p1, d1⟩ := step_imm16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hCodeSz]; omega)
  have hInitInv : inv ⟨0, sealedInitArenaOff n Q⟩ s1 := by
    refine ⟨Nat.zero_le _, pc1, by rw [d1]; exact hSz, ?_, congrArg Fin.val r1_10,
      by rw [d1]; exact hHdrDesc, by rw [d1]; exact hHdrTot, Nat.le_refl _,
      by simp only [List.range_zero, List.foldl_nil]; omega,
      fun _ _ => by rw [d1]; rfl, fun j hj => False.elim (Nat.not_lt_zero _ hj)⟩
    exact
      { consts :=
          { zero := by rw [p1 rZero (by decide)]; exact hRegs.consts.zero
            one := by rw [p1 rOne (by decide)]; exact hRegs.consts.one
            nVal := by rw [p1 rN (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [p1 rM (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [p1 rRoot (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [p1 r5 (by decide)]; exact hRegs.qVal
        treeBaseVal := by rw [p1 r6 (by decide)]; exact hRegs.treeBaseVal
        forestPtrsVal := by rw [p1 r7 (by decide)]; exact hRegs.forestPtrsVal
        exitPtrsVal := by rw [p1 r8 (by decide)]; exact hRegs.exitPtrsVal
        sealedBaseVal := by rw [p1 r9 (by decide)]; exact hRegs.sealedBaseVal }
  obtain ⟨dcEnd, t, kLoop, hkLoop, hRunLoop, _, htSz, htRegs, htTot, htLo, ht128, htFr, htDone⟩ :=
    while_steps_budget (code := code) (input := input) inv meas budget _ hStep Q
      ⟨0, sealedInitArenaOff n Q⟩ s1 (by dsimp [meas]; omega) hInitInv
  have hStepsTot : run code input (1 + kLoop) (Phase.initial s₀) = some ⟨t, 1 + kLoop⟩ := by
    obtain ⟨m, last, route, halt, cost⟩ := run_has_steps_then_halt hRunLoop
    obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
    have term : step code input last = some (.halted t) := by
      change t = last at sameHalt; rw [sameHalt]; exact step_halt_at atHalt
    have exec := ((step1 hs1).append route).halts term
    change kLoop = m + 1 at cost
    simpa [Nat.add_assoc, ← cost] using exec
  have hBudget0 : 1 + budget ⟨0, sealedInitArenaOff n Q⟩ ≤ 700 * (n + m + 1) := by
    dsimp [budget]; omega
  refine ⟨t, 1 + kLoop, dcEnd.2, ht128, by omega, hStepsTot, htSz, htRegs, htTot, htLo,
    htFr, htDone⟩

set_option maxHeartbeats 2000000 in
private theorem run_sealed_pack_aux (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {g : Digraph} {r : Fin g.vertexCount}
    {order : List (Fin g.vertexCount)}
    (hLen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order)
    {dense : List (Fin g.vertexCount)} {treeBaseG : Nat}
    (S : StaticTreeSlice s₀.data treeBaseG g r dense)
    (hPack : MatchesPackedLayout S)
    {m root Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase : Nat}
    (hm : m = g.arcCount) (hRoot : root = r.val) (hQ : Q = dense.length)
    (htb : treeBase = treeBaseG)
    (hRegs : SealedPackEntryRegs g.vertexCount m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hDisj : SealedDisjointLayout g.vertexCount Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hFPFit : forestPtrsBase + 6 * Q ≤ workCap)
    (hFAFit : forestArenaBase + forestUsed ≤ workCap)
    (hEPFit : exitPtrsBase + 3 * Q ≤ workCap)
    (hEAFit : exitArenaBase + exitUsed ≤ workCap)
    (hOrigToDense : ∀ v : Fin g.vertexCount,
      (s₀.data[3 * g.vertexCount + v.val]?).map Fin.val =
        some (if _ : v ∈ dense then dense.idxOf v + 1 else 0))
    (hDenseToOrig : ∀ d : Fin dense.length,
      (s₀.data[4 * g.vertexCount + d.val]?).map Fin.val = some (dense[d.val]'d.isLt).val)
    (hArena : ∀ d : Fin dense.length,
      OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
        exitPtrsBase exitArenaBase exitUsed s₀.data)
    (hTag : TagsFit bits) (hQWork : queryWorkCap ≤ 2 ^ bits) :
    let code := sealedPackProgram (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32
    ∃ (t : State L16) (states : List (State L16)) (steps totalWords : Nat),
      totalWords ≤ retainedLinearFactor * g.vertexCount ∧
      steps ≤ 900 * (g.vertexCount + g.arcCount + 1) ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint L16 ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs g.vertexCount m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      sealedBase + totalWords ≤ workCap ∧
      (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some totalWords ∧
      (let I := t.data.extract sealedBase (sealedBase + totalWords)
       ValidSealedOracleIndex g r I ∧
       I.size = totalWords ∧
       (I[hdrTotalWords]?).map Fin.val = some totalWords ∧
       ∀ addr, (addr < sealedBase ∨ sealedBase + totalWords ≤ addr) →
         t.data[addr]? = s₀.data[addr]?) := by
  intro code
  subst hm hRoot htb
  have hn : 1 ≤ g.vertexCount := Fin.pos r
  have hQPos : 1 ≤ Q := hQ ▸ S.qPos
  have hQn : Q ≤ g.vertexCount := hQ ▸ S.length_le
  obtain ⟨t1, st1, k1, hk1, hRun1, hTr1, hPk1, t1sz, hR1, hH0, hH1, hH2, hH3, hH4, hH5,
      hH6, hH7, hH8, hH9, hH10, hH11, hH12, hH13, hH14, hH15,
      hCpO, hCpD, hCpTLo, hCpTHi, hFr1⟩ :=
    run_sealedHeaderPhase h32 hBits hn hQPos hQn hRegs hSz hDisj hTreeFit
  have hChildStart1 : ∀ d ≤ Q, (t1.data[treeBase + 7 * Q + d]?).map Fin.val = some (S.childStart d) := by
    intro d hd
    have hTreeKeep : t1.data[treeBase + 7 * Q + d]? = s₀.data[treeBase + 7 * Q + d]? := by
      apply hFr1
      rcases hDisj.disj_tree with h | h
      · unfold sealedOwnerDescOff; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega)
      · change treeBase + staticTreeWords Q ≤ sealedBase at h; unfold staticTreeWords at h; exact Or.inl (by omega)
    rw [hTreeKeep, hQ]
    exact S.childStart_mem d (hQ ▸ hd)
  have hArena1 : ∀ d : Fin dense.length,
      OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
        exitPtrsBase exitArenaBase exitUsed t1.data := by
    intro d
    let nD := 1 + (S.childSlice d).length
    have hSameF : ∀ addr, forestPtrsBase ≤ addr → addr < forestPtrsBase + 6 * Q → t1.data[addr]? = s₀.data[addr]? := fun addr ha hb => by
      apply hFr1
      rcases hDisj.disj_fPtrs with h | h
      · unfold sealedOwnerDescOff; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hSameFA : ∀ addr, forestArenaBase ≤ addr → addr < forestArenaBase + forestUsed → t1.data[addr]? = s₀.data[addr]? := fun addr ha hb => by
      apply hFr1
      rcases hDisj.disj_fArena with h | h
      · unfold sealedOwnerDescOff; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hSameE : ∀ addr, exitPtrsBase ≤ addr → addr < exitPtrsBase + 3 * Q → t1.data[addr]? = s₀.data[addr]? := fun addr ha hb => by
      apply hFr1
      rcases hDisj.disj_ePtrs with h | h
      · unfold sealedOwnerDescOff; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hSameEA : ∀ addr, exitArenaBase ≤ addr → addr < exitArenaBase + exitUsed → t1.data[addr]? = s₀.data[addr]? := fun addr ha hb => by
      apply hFr1
      rcases hDisj.disj_eArena with h | h
      · unfold sealedOwnerDescOff; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega)
      · exact Or.inl (by omega)
    have hAr0 := hArena d
    dsimp only [OwnerExitArenaAt] at hAr0 ⊢
    by_cases hLarge : 3 ≤ nD
    · rw [dite_eq_left hLarge] at hAr0 ⊢
      rcases hAr0 with ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R0, F, ref, wFit, ok0,
        prior, hb, B0, hPl0, fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2,
        incH, covH, rArcH, hfp0, hfp1, hfp2, hfp3, hfp4, hfp5, hD1, hD2, hD3, hD4, hD5,
        hwDict, hwBF, hwBS, hwLab, hwStop, hwLe, hwWc, hFA1, hFA2,
        hSlD, hSlBF, hSlBS, hSlLb, hSlFE, hSlFS, hRep, hKnown, hBackR, hVIdx, hLabB, hHitB,
        hep0, hep1, hep2, hEA0a, hEA0b, hEA1a, hEA1b, hEA2a, hEA2b, hRSlots, hPriorSz, hRBase0, hBStart0, hDepAddr0, hExitSpec0⟩
      have hSzEq : t1.data.size = s₀.data.size := by rw [t1sz, hSz]
      let R1 : Region bits t1.data.size :=
        { slots := R0.slots
          depthAddr := R0.depthAddr
          depthMem := fun v => by rw [hSzEq]; exact R0.depthMem v
          base := R0.base
          recordAddr := R0.recordAddr
          recordMem := fun v => by rw [hSzEq]; exact R0.recordMem v }
      have ok1 : Occupied t1.data R1 F ref wFit :=
        { size_eq := ok0.size_eq
          valid := ok0.valid
          depth := fun v => by
            have hd0 : (R0.depthAddr v).val = ep0 + v.val := hDepAddr0 v
            have hmem : t1.data[(R1.depthAddr v).val]? = s₀.data[(R0.depthAddr v).val]? :=
              hSameEA _ (by rw [show (R1.depthAddr v).val = ep0 + v.val from hd0]; omega)
                (by rw [show (R1.depthAddr v).val = ep0 + v.val from hd0]; have hv := Nat.lt_of_lt_of_eq v.isLt hRSlots; omega)
            have htG : (t1.data[(R1.depthAddr v).val]?).map Fin.val = some (t1.data[(R1.depthAddr v).val]'(R1.depthMem v)).val := by
              rw [Array.getElem?_eq_getElem (R1.depthMem v), Option.map_some]
            have hsG : (s₀.data[(R0.depthAddr v).val]?).map Fin.val = some (s₀.data[(R0.depthAddr v).val]'(R0.depthMem v)).val := by
              rw [Array.getElem?_eq_getElem (R0.depthMem v), Option.map_some]
            have heq := Option.some.inj (htG.symm.trans ((congrArg (Option.map Fin.val) hmem).trans hsG))
            exact heq.trans (ok0.depth v)
          parent_eq := ok0.parent_eq
          jump_eq := ok0.jump_eq
          maps := ok0.maps
          packed := fun v hr i => by
            have hk := i.isLt
            have hmem : t1.data[R1.base.val + 18 * v.val + i.val]? = s₀.data[R0.base.val + 18 * v.val + i.val]? :=
              hSameEA _ (by change exitArenaBase ≤ R0.base.val + 18 * v.val + i.val; rw [hRBase0]; omega)
                (by change R0.base.val + 18 * v.val + i.val < exitArenaBase + exitUsed; rw [hRBase0]; have hv := Nat.lt_of_lt_of_eq v.isLt hRSlots; omega)
            rw [Array.getElem?_eq_getElem (by have hm := R1.recordMem v; omega),
                Array.getElem?_eq_getElem (by have hm := R0.recordMem v; omega), Option.some.injEq] at hmem
            exact hmem.trans (ok0.packed v hr i) }
      let B1 : BaseView prior.size t1.data.size := ⟨B0.start, by rw [hSzEq]; exact B0.fits⟩
      have hPl1 : Placed wFit prior hb t1.data B1 := by
        intro j
        have hj : j.val < 6 * nD := Nat.lt_of_lt_of_eq j.isLt (congrArg (6 * ·) hPriorSz)
        have hmem : t1.data[B1.start + j.val]? = s₀.data[B0.start + j.val]? :=
          hSameEA _ (by dsimp [B1]; rw [hBStart0]; omega) (by dsimp [B1]; rw [hBStart0]; omega)
        rw [Array.getElem?_eq_getElem (by have := B1.fits; omega),
            Array.getElem?_eq_getElem (by have := B0.fits; omega), Option.some.injEq] at hmem
        exact hmem.trans (hPl0 j)
      have hD0Same : t1.data[fp0]? = s₀.data[fp0]? :=
        hSameFA fp0 hFA1 (by rw [hD5, hD4, hD3, hD2, hD1] at hFA2; omega)
      have hSubFA : ∀ (base : Nat) (arr : Array (Word bits)),
          forestArenaBase ≤ base → base + arr.size ≤ forestArenaBase + forestUsed →
          SliceAt s₀.data base arr → SliceAt t1.data base arr := fun base arr hb1 hb2 hSl => by
        refine ⟨by rw [t1sz]; exact Nat.le_trans hb2 hFAFit, fun j hj => ?_⟩
        rw [hSameFA (base + j) (by omega) (by omega)]
        exact hSl.2 j hj
      refine ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R1, F, ref, wFit, ok1,
        prior, hb, B1, hPl1, fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2,
        incH, covH, rArcH,
        by rw [hSameF _ (by omega) (by omega)]; exact hfp0,
        by rw [hSameF _ (by omega) (by omega)]; exact hfp1,
        by rw [hSameF _ (by omega) (by omega)]; exact hfp2,
        by rw [hSameF _ (by omega) (by omega)]; exact hfp3,
        by rw [hSameF _ (by omega) (by omega)]; exact hfp4,
        by rw [hSameF _ (by omega) (by omega)]; exact hfp5,
        by rw [hD0Same]; exact hD1, hD2, hD3, hD4, hD5,
        by rw [hD0Same]; exact hwDict, hwBF, hwBS, hwLab, hwStop, hwLe, hwWc, hFA1, hFA2,
        hSubFA fp0 _ hFA1 (by rw [hwDict, ← hD1]; omega) hSlD,
        hSubFA fp1 _ (by omega) (by rw [hwBF, ← hD2]; omega) hSlBF,
        hSubFA fp2 _ (by omega) (by rw [hwBS, ← hD3]; omega) hSlBS,
        hSubFA fp3 _ (by omega) (by rw [hwLab, ← hD4]; omega) hSlLb,
        hSubFA fp4 _ (by omega) (by rw [← hD5]; omega) hSlFE,
        hSubFA fp5 _ (by omega) hFA2 hSlFS,
        hRep, hKnown, hBackR, hVIdx, hLabB, hHitB,
        by rw [hSameE _ (by omega) (by omega)]; exact hep0,
        by rw [hSameE _ (by omega) (by omega)]; exact hep1,
        by rw [hSameE _ (by omega) (by omega)]; exact hep2,
        hEA0a, hEA0b, hEA1a, hEA1b, hEA2a, hEA2b, hRSlots, hPriorSz, hRBase0, hBStart0, hDepAddr0, ?_⟩
      intro P hLt aNode hCh y hProper
      obtain ⟨hSt0, hRn0⟩ := hExitSpec0 P hLt aNode hCh y hProper
      obtain ⟨_, _, haF, _, _⟩ := hHitB P hLt aNode hCh
      have huF : wCols.labelAt y.val < F.size := (hLabB y).1
      have hDepEq : depthAt t1.data R1 aNode = depthAt s₀.data R0 aNode := by
        rw [depthAt_exact ok1 haF, depthAt_exact ok0 haF]
      have hFoldEq : foldStored t1.data R1 wFit.tags (wCols.labelAt y.val) (depthAt t1.data R1 aNode) =
          foldStored s₀.data R0 wFit.tags (wCols.labelAt y.val) (depthAt s₀.data R0 aNode) := by
        rw [hDepEq, foldStored_exact ok1 huF, foldStored_exact ok0 huF]
      refine ⟨by rw [hFoldEq]; exact hSt0, fun hPrior => ?_⟩
      obtain ⟨hx0, hx1⟩ := hRn0 hPrior
      have hRunEq : PriorBase.run t1.data R1 wFit.tags prior ⟨y.val, hPrior⟩ (wCols.labelAt y.val) (depthAt t1.data R1 aNode) =
          PriorBase.run s₀.data R0 wFit.tags prior ⟨y.val, hPrior⟩ (wCols.labelAt y.val) (depthAt s₀.data R0 aNode) := by
        simp only [PriorBase.run, hFoldEq]
      rw [hRunEq]; exact ⟨hx0, hx1⟩
    · rw [dite_eq_right hLarge]; exact trivial
  obtain ⟨t2, k2, totalWords, hTot128, hk2, hRun2, t2sz, ht2Regs, ht2Tot, ht2Lo, hFr2, hOwners2⟩ :=
    run_sealedOwnersPhase h32 hBits S hn hQ hQn hR1 t1sz hDisj hTreeFit hFPFit hFAFit hEPFit hEAFit
      hH14 hH15 hChildStart1 hArena1
  obtain ⟨t, states, huRegs, huData, hRun, hTr, hPk⟩ :=
    run_linked_pair (sealedHeaderPhase h32) (sealedOwnersPhase h32).code
      (by have hSzO := sealedOwnersCode_size (bits := bits) (inputCap := inputCap) (workCap := workCap)
            (hi := hi) (hw := hw) h32
          change 0 < (sealedOwnersCode h32).size
          omega)
      hRun1 hRun2
  have hStepsLe : k1 + k2 ≤ 900 * (g.vertexCount + g.arcCount + 1) := by omega
  have hTSz : t.data.size = workCap := by rw [huData]; exact t2sz
  have hSB_fit : sealedBase + totalWords ≤ workCap :=
    Nat.le_trans (Nat.add_le_add_left hTot128 sealedBase) hDisj.sealed_fit
  let I := t.data.extract sealedBase (sealedBase + totalWords)
  have hISz : I.size = totalWords := by
    dsimp [I]; rw [Array.size_extract, Nat.min_eq_left (by rw [hTSz]; exact hSB_fit)]; omega
  have hIGet : ∀ j < totalWords, I[j]? = t2.data[sealedBase + j]? := fun j hj => by
    have hjI : j < I.size := by rw [hISz]; exact hj
    have hjT : sealedBase + j < t.data.size := by rw [hTSz]; omega
    rw [Array.getElem?_eq_getElem hjI, Array.getElem_extract, ← Array.getElem?_eq_getElem hjT, huData]
  have hHdrKeep : ∀ slot < 15, t2.data[sealedBase + slot]? = t1.data[sealedBase + slot]? := fun slot hs => by
    apply hFr2; left; rw [hdrTotalWords_eq]; omega
  have hHdrSz : oracleHeaderSize ≤ I.size := by
    rw [hISz, oracleHeaderSize_eq]; unfold sealedInitArenaOff at ht2Lo; omega
  have hStaKeep : ∀ j, 16 ≤ j → j < sealedOwnerDescOff g.vertexCount Q →
      t2.data[sealedBase + j]? = t1.data[sealedBase + j]? := fun j hj1 hj2 => by
    apply hFr2; right; left; rw [hdrTotalWords_eq]; omega
  have hTotWord : (I[hdrTotalWords]?).map Fin.val = some totalWords := by
    rw [hIGet _ (by rw [hdrTotalWords_eq]; unfold sealedInitArenaOff at ht2Lo; omega)]; exact ht2Tot
  let Hdr : StaticHeaderSpec I g.vertexCount Q :=
    { n_pos := hn
      q_pos := hQPos
      q_le := hQn
      hdr_fit := hHdrSz
      hN := by rw [hIGet _ (by rw [hdrN_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrN_eq]; omega)]; exact hH4
      hQ := by rw [hIGet _ (by rw [hdrQCount_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrQCount_eq]; omega)]; exact hH5
      hTotal := by rw [hTotWord, hISz]
      headBase := sealedHeadOff g.vertexCount Q
      domParentBase := sealedDomParentOff g.vertexCount Q
      domDepthBase := sealedDomDepthOff g.vertexCount Q
      origToDenseBase := sealedOrigToDenseOff
      denseToOrigBase := sealedDenseToOrigOff g.vertexCount
      entryBase := sealedEntryOff g.vertexCount Q
      stopBase := sealedStopOff g.vertexCount Q
      origOfEntryBase := sealedOrigOfEntryOff g.vertexCount Q
      childStartBase := sealedChildStartOff g.vertexCount Q
      childEntriesBase := sealedChildEntriesOff g.vertexCount Q
      childStopsBase := sealedChildStopsOff g.vertexCount Q
      childIdsBase := sealedChildIdsOff g.vertexCount Q
      ownerDescBase := sealedOwnerDescOff g.vertexCount Q
      hHeadBase := by rw [hIGet _ (by rw [hdrHead_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrHead_eq]; omega)]; exact hH0
      hDomParentBase := by rw [hIGet _ (by rw [hdrDomParent_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrDomParent_eq]; omega)]; exact hH1
      hDomDepthBase := by rw [hIGet _ (by rw [hdrDomDepth_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrDomDepth_eq]; omega)]; exact hH2
      hOrigToDenseBase := by rw [hIGet _ (by rw [hdrOrigToDense_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrOrigToDense_eq]; omega)]; exact hH3
      hDenseToOrigBase := by rw [hIGet _ (by rw [hdrDenseToOrig_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrDenseToOrig_eq]; omega)]; exact hH6
      hEntryBase := by rw [hIGet _ (by rw [hdrEntry_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrEntry_eq]; omega)]; exact hH7
      hStopBase := by rw [hIGet _ (by rw [hdrStop_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrStop_eq]; omega)]; exact hH8
      hOrigOfEntryBase := by rw [hIGet _ (by rw [hdrOrigOfEntry_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrOrigOfEntry_eq]; omega)]; exact hH9
      hChildStartBase := by rw [hIGet _ (by rw [hdrChildStart_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrChildStart_eq]; omega)]; exact hH10
      hChildEntriesBase := by rw [hIGet _ (by rw [hdrChildEntries_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrChildEntries_eq]; omega)]; exact hH11
      hChildStopsBase := by rw [hIGet _ (by rw [hdrChildStops_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrChildStops_eq]; omega)]; exact hH12
      hChildIdsBase := by rw [hIGet _ (by rw [hdrChildIds_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrChildIds_eq]; omega)]; exact hH13
      hOwnerDescBase := by rw [hIGet _ (by rw [hdrOwnerDesc_eq]; unfold sealedInitArenaOff at ht2Lo; omega), hHdrKeep _ (by rw [hdrOwnerDesc_eq]; omega)]; exact hH14
      origToDense_fit := by rw [hISz]; unfold sealedOrigToDenseOff; unfold sealedInitArenaOff at ht2Lo; omega
      denseToOrig_fit := by rw [hISz]; unfold sealedDenseToOrigOff; unfold sealedInitArenaOff at ht2Lo; omega
      head_fit := by rw [hISz]; unfold sealedHeadOff; unfold sealedInitArenaOff at ht2Lo; omega
      domParent_fit := by rw [hISz]; unfold sealedDomParentOff; unfold sealedInitArenaOff at ht2Lo; omega
      domDepth_fit := by rw [hISz]; unfold sealedDomDepthOff; unfold sealedInitArenaOff at ht2Lo; omega
      entry_fit := by rw [hISz]; unfold sealedEntryOff; unfold sealedInitArenaOff at ht2Lo; omega
      stop_fit := by rw [hISz]; unfold sealedStopOff; unfold sealedInitArenaOff at ht2Lo; omega
      origOfEntry_fit := by rw [hISz]; unfold sealedOrigOfEntryOff; unfold sealedInitArenaOff at ht2Lo; omega
      childStart_fit := by rw [hISz]; unfold sealedChildStartOff; unfold sealedInitArenaOff at ht2Lo; omega
      childEntries_fit := by rw [hISz]; unfold sealedChildEntriesOff; unfold sealedInitArenaOff at ht2Lo; omega
      childStops_fit := by rw [hISz]; unfold sealedChildStopsOff; unfold sealedInitArenaOff at ht2Lo; omega
      childIds_fit := by rw [hISz]; unfold sealedChildIdsOff; unfold sealedInitArenaOff at ht2Lo; omega
      ownerDesc_fit := by rw [hISz, ownerDescStride_eq]; unfold sealedOwnerDescOff; unfold sealedInitArenaOff at ht2Lo; omega }
  let HdrQ : StaticHeaderSpec I g.vertexCount dense.length := hQ ▸ Hdr
  let B := StaticReaderBridge.ofSlice g r order hLen hTopo S hPack
  have hSData : StaticTreeSliceHeaderData S I HdrQ := by
    subst hQ
    refine StaticTreeSliceHeaderData.ofSliceCopy S I HdrQ
      (fun d => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedHeadOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedHeadOff; omega) (by unfold sealedHeadOff sealedOwnerDescOff; omega),
          ← Nat.add_assoc, hCpTHi d.val (by have := d.isLt; omega)])
      (fun d => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedDomParentOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedDomParentOff; omega) (by unfold sealedDomParentOff sealedOwnerDescOff; omega),
          ← Nat.add_assoc, hCpTLo d.val (by have := d.isLt; omega)])
      (fun d => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedDomDepthOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedDomDepthOff; omega) (by unfold sealedDomDepthOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedDomDepthOff g.vertexCount dense.length + d.val) =
            sealedBase + sealedDomParentOff g.vertexCount dense.length + (dense.length + d.val) by
            unfold sealedDomDepthOff sealedDomParentOff; omega,
          hCpTLo (dense.length + d.val) (by have := d.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun d => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedEntryOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedEntryOff; omega) (by unfold sealedEntryOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedEntryOff g.vertexCount dense.length + d.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (dense.length + d.val) by
            unfold sealedEntryOff sealedHeadOff; omega,
          hCpTHi (dense.length + d.val) (by have := d.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun d => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedStopOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedStopOff; omega) (by unfold sealedStopOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedStopOff g.vertexCount dense.length + d.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (2 * dense.length + d.val) by
            unfold sealedStopOff sealedHeadOff; omega,
          hCpTHi (2 * dense.length + d.val) (by have := d.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun k => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedOrigOfEntryOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedOrigOfEntryOff; omega) (by unfold sealedOrigOfEntryOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedOrigOfEntryOff g.vertexCount dense.length + k.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (3 * dense.length + k.val) by
            unfold sealedOrigOfEntryOff sealedHeadOff; omega,
          hCpTHi (3 * dense.length + k.val) (by have := k.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun idx => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedChildStartOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedChildStartOff; omega) (by unfold sealedChildStartOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedChildStartOff g.vertexCount dense.length + idx.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (4 * dense.length + idx.val) by
            unfold sealedChildStartOff sealedHeadOff; omega,
          hCpTHi (4 * dense.length + idx.val) (by have := idx.isLt; omega)]
        exact congrArg (fun idx2 => s₀.data[idx2]?) (by omega))
      (fun pos => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedChildEntriesOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedChildEntriesOff; omega) (by unfold sealedChildEntriesOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedChildEntriesOff g.vertexCount dense.length + pos.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (5 * dense.length + 1 + pos.val) by
            unfold sealedChildEntriesOff sealedHeadOff; omega,
          hCpTHi (5 * dense.length + 1 + pos.val) (by have := pos.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun pos => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedChildStopsOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedChildStopsOff; omega) (by unfold sealedChildStopsOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedChildStopsOff g.vertexCount dense.length + pos.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (6 * dense.length + 1 + pos.val) by
            unfold sealedChildStopsOff sealedHeadOff; omega,
          hCpTHi (6 * dense.length + 1 + pos.val) (by have := pos.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun pos => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedChildIdsOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedChildIdsOff; omega) (by unfold sealedChildIdsOff sealedOwnerDescOff; omega),
          show sealedBase + (sealedChildIdsOff g.vertexCount dense.length + pos.val) =
            sealedBase + sealedHeadOff g.vertexCount dense.length + (7 * dense.length + 1 + pos.val) by
            unfold sealedChildIdsOff sealedHeadOff; omega,
          hCpTHi (7 * dense.length + 1 + pos.val) (by have := pos.isLt; omega)]
        exact congrArg (fun idx => s₀.data[idx]?) (by omega))
      (fun v => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedOrigToDenseOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedOrigToDenseOff; omega) (by unfold sealedOrigToDenseOff sealedOwnerDescOff; omega),
          ← Nat.add_assoc, hCpO v.val v.isLt]
        exact hOrigToDense v)
      (fun d => by
        dsimp only [HdrQ, Hdr]
        rw [hIGet _ (by unfold sealedDenseToOrigOff; unfold sealedInitArenaOff at ht2Lo; omega),
          hStaKeep _ (by unfold sealedDenseToOrigOff; omega) (by unfold sealedDenseToOrigOff sealedOwnerDescOff; omega),
          ← Nat.add_assoc, hCpD d.val d.isLt]
        exact hDenseToOrig d)
  have hSRecs : ∀ d : Fin dense.length, Nonempty (RamQuotientOwnerRecord S I HdrQ d) := by
    intro d
    subst hQ
    obtain ⟨hND, hRest⟩ := hOwners2 d
    let nD := 1 + (S.childSlice d).length
    have hDescFitI : sealedOwnerDescOff g.vertexCount dense.length + ownerDescStride * d.val + ownerDescStride ≤ I.size := by
      rw [hISz, ownerDescStride_eq]; unfold sealedOwnerDescOff; unfold sealedInitArenaOff at ht2Lo; omega
    have hIlt : I.size ≤ 2 ^ bits := by
      rw [hISz]
      exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_left totalWords sealedBase) hSB_fit) hBits)
    have hIGetD : ∀ k < 10, I[sealedOwnerDescOff g.vertexCount dense.length + ownerDescStride * d.val + k]? =
        t2.data[sealedBase + sealedOwnerDescOff g.vertexCount dense.length + ownerDescStride * d.val + k]? := fun k hk => by
      rw [hIGet (sealedOwnerDescOff g.vertexCount dense.length + ownerDescStride * d.val + k)
        (by rw [ownerDescStride_eq, hISz] at hDescFitI; rw [ownerDescStride_eq]; omega), ← Nat.add_assoc, ← Nat.add_assoc]
    have hD0 : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descN]?).map Fin.val = some nD := by
      rw [hIGetD descN (by rw [descN_eq]; omega)]; exact hND
    by_cases hSm : nD < 3
    · rw [ite_eq_left hSm] at hRest
      refine ⟨{
        nD := nD
        nD_eq := rfl
        dictPtr := 0
        backFstPtr := 0
        backSndPtr := 0
        labelsPtr := 0
        fEntryPtr := 0
        fStopPtr := 0
        exitDepthPtr := 0
        exitStoredPtr := 0
        exitPriorPtr := 0
        descBase := Hdr.ownerDescBase + ownerDescStride * d.val
        descBase_val := rfl
        descFits := hDescFitI
        hDescN := hD0
        hDescDict := by rw [hIGetD descDict (by rw [descDict_eq]; omega), descDict_eq]; exact hRest 1 (by decide) (by decide)
        hDescBackFst := by rw [hIGetD descBackFst (by rw [descBackFst_eq]; omega), descBackFst_eq]; exact hRest 2 (by decide) (by decide)
        hDescBackSnd := by rw [hIGetD descBackSnd (by rw [descBackSnd_eq]; omega), descBackSnd_eq]; exact hRest 3 (by decide) (by decide)
        hDescLabels := by rw [hIGetD descLabels (by rw [descLabels_eq]; omega), descLabels_eq]; exact hRest 4 (by decide) (by decide)
        hDescFEntry := by rw [hIGetD descFEntry (by rw [descFEntry_eq]; omega), descFEntry_eq]; exact hRest 5 (by decide) (by decide)
        hDescFStop := by rw [hIGetD descFStop (by rw [descFStop_eq]; omega), descFStop_eq]; exact hRest 6 (by decide) (by decide)
        hDescExitDepth := by rw [hIGetD descExitDepth (by rw [descExitDepth_eq]; omega), descExitDepth_eq]; exact hRest 7 (by decide) (by decide)
        hDescExitStored := by rw [hIGetD descExitStored (by rw [descExitStored_eq]; omega), descExitStored_eq]; exact hRest 8 (by decide) (by decide)
        hDescExitPrior := by rw [hIGetD descExitPrior (by rw [descExitPrior_eq]; omega), descExitPrior_eq]; exact hRest 9 (by decide) (by decide)
        large_spec := fun hL => (Nat.not_lt.mpr hL hSm).elim }⟩
    · rw [ite_eq_right hSm] at hRest
      rcases hRest with ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hLC⟩
      refine ⟨ownerExitArenaAt_to_record S HdrQ d (hArena1 d) nD rfl p1 p2 p3 p4 p5 p6 p7 p8 p9
        hDescFitI hIlt hD0
        (by rw [hIGetD descDict (by rw [descDict_eq]; omega)]; exact hp1)
        (by rw [hIGetD descBackFst (by rw [descBackFst_eq]; omega)]; exact hp2)
        (by rw [hIGetD descBackSnd (by rw [descBackSnd_eq]; omega)]; exact hp3)
        (by rw [hIGetD descLabels (by rw [descLabels_eq]; omega)]; exact hp4)
        (by rw [hIGetD descFEntry (by rw [descFEntry_eq]; omega)]; exact hp5)
        (by rw [hIGetD descFStop (by rw [descFStop_eq]; omega)]; exact hp6)
        (by rw [hIGetD descExitDepth (by rw [descExitDepth_eq]; omega)]; exact hp7)
        (by rw [hIGetD descExitStored (by rw [descExitStored_eq]; omega)]; exact hp8)
        (by rw [hIGetD descExitPrior (by rw [descExitPrior_eq]; omega)]; exact hp9)
        (fun fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 => by
          obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, c1, c2, c3, c4⟩ :=
            hLC fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15
          refine ⟨b1, b2, b3, b4, b5, by rw [hISz]; exact b6, by rw [hISz]; exact b7,
            by rw [hISz]; exact b8, by rw [hISz]; exact b9,
            fun k hk => by rw [hIGet _ (by omega), ← Nat.add_assoc]; exact c1 k hk,
            fun k hk => by rw [hIGet _ (by omega), ← Nat.add_assoc]; exact c2 k hk,
            fun k hk => by rw [hIGet _ (by omega), ← Nat.add_assoc]; exact c3 k hk,
            fun k hk => by rw [hIGet _ (by omega), ← Nat.add_assoc]; exact c4 k hk⟩)⟩
  have hValid : ValidSealedOracleIndex g r I := by
    have hGen : ∀ (qc : Nat) (hB : B.q.count = qc)
        (Hdr' : StaticHeaderSpec I g.vertexCount qc),
        StaticTreeSliceHeaderData S I Hdr' →
        (∀ d : Fin dense.length, Nonempty (RamQuotientOwnerRecord S I Hdr' d)) →
        ValidSealedOracleIndex g r I := by
      intro qc hB Hdr' hD' hR'
      subst hB
      exact StaticReaderBridge.validSealedOracleIndex B hTag hQWork Hdr' hD' hR'
    exact hGen dense.length B.count_eq HdrQ hSData hSRecs
  have htRegs : SealedPackEntryRegs g.vertexCount g.arcCount r.val Q treeBase
      forestPtrsBase exitPtrsBase sealedBase t :=
    { consts :=
        { zero := by rw [reg_eq_of_regs_eq huRegs rZero]; exact ht2Regs.consts.zero
          one := by rw [reg_eq_of_regs_eq huRegs rOne]; exact ht2Regs.consts.one
          nVal := by rw [reg_eq_of_regs_eq huRegs rN]; exact ht2Regs.consts.nVal
          mVal := by rw [reg_eq_of_regs_eq huRegs rM]; exact ht2Regs.consts.mVal
          rootVal := by rw [reg_eq_of_regs_eq huRegs rRoot]; exact ht2Regs.consts.rootVal }
      qVal := by rw [reg_eq_of_regs_eq huRegs r5]; exact ht2Regs.qVal
      treeBaseVal := by rw [reg_eq_of_regs_eq huRegs r6]; exact ht2Regs.treeBaseVal
      forestPtrsVal := by rw [reg_eq_of_regs_eq huRegs r7]; exact ht2Regs.forestPtrsVal
      exitPtrsVal := by rw [reg_eq_of_regs_eq huRegs r8]; exact ht2Regs.exitPtrsVal
      sealedBaseVal := by rw [reg_eq_of_regs_eq huRegs r9]; exact ht2Regs.sealedBaseVal }
  refine ⟨t, states, k1 + k2, totalWords, hTot128, hStepsLe, hRun, hTr, hPk, hTSz, htRegs,
    hSB_fit, by rw [huData]; exact ht2Tot, hValid, hISz, hTotWord, fun addr hOut => ?_⟩
  rw [huData, hFr2 addr (by rcases hOut with h | h; exact Or.inl (by rw [hdrTotalWords_eq]; omega); exact Or.inr (Or.inr h)),
    hFr1 addr (by rcases hOut with h | h; exact Or.inl h; exact Or.inr (by unfold sealedOwnerDescOff; unfold sealedInitArenaOff at ht2Lo; omega))]

/-- **Master EX5.2 Packer Theorem (Into `[sealedBase .. sealedBase + totalWords)`)**:
Executes `sealedPackProgram` in `O(n + m + 1)` steps with `tracePeakWords =
inputCap + workCap + 16`, packs `I := t.data.extract sealedBase (sealedBase + totalWords)`
with `totalWords ≤ 128 * n` (`< 2 ^ bits`), and establishes `ValidSealedOracleIndex g r I`. -/
theorem run_sealed_pack (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {g : Digraph} {r : Fin g.vertexCount}
    {order : List (Fin g.vertexCount)}
    (hLen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order)
    {dense : List (Fin g.vertexCount)} {treeBaseG : Nat}
    (S : StaticTreeSlice s₀.data treeBaseG g r dense)
    (hPack : MatchesPackedLayout S)
    {m root Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase : Nat}
    (hm : m = g.arcCount) (hRoot : root = r.val) (hQ : Q = dense.length)
    (htb : treeBase = treeBaseG)
    (hRegs : SealedPackEntryRegs g.vertexCount m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hDisj : SealedDisjointLayout g.vertexCount Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hFPFit : forestPtrsBase + 6 * Q ≤ workCap)
    (hFAFit : forestArenaBase + forestUsed ≤ workCap)
    (hEPFit : exitPtrsBase + 3 * Q ≤ workCap)
    (hEAFit : exitArenaBase + exitUsed ≤ workCap)
    (hOrigToDense : ∀ v : Fin g.vertexCount,
      (s₀.data[3 * g.vertexCount + v.val]?).map Fin.val =
        some (if _ : v ∈ dense then dense.idxOf v + 1 else 0))
    (hDenseToOrig : ∀ d : Fin dense.length,
      (s₀.data[4 * g.vertexCount + d.val]?).map Fin.val = some (dense[d.val]'d.isLt).val)
    (hArena : ∀ d : Fin dense.length,
      OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
        exitPtrsBase exitArenaBase exitUsed s₀.data)
    (hTag : TagsFit bits) (hQWork : queryWorkCap ≤ 2 ^ bits) :
    let code := sealedPackProgram (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32
    ∃ (t : State L16) (states : List (State L16)) (steps totalWords : Nat),
      totalWords ≤ retainedLinearFactor * g.vertexCount ∧
      steps ≤ 900 * (g.vertexCount + g.arcCount + 1) ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint L16 ∧
      t.data.size = workCap ∧
      sealedBase + totalWords ≤ workCap ∧
      (let I := t.data.extract sealedBase (sealedBase + totalWords)
       ValidSealedOracleIndex g r I ∧
       I.size = totalWords ∧
       (I[hdrTotalWords]?).map Fin.val = some totalWords ∧
       ∀ addr, (addr < sealedBase ∨ sealedBase + totalWords ≤ addr) →
         t.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨t, states, steps, totalWords, hTot128, hStepsLe, hRun, hTr, hPk, hTSz, _, hSB_fit, _,
      hValid, hISz, hTotWord, hKeep⟩ :=
    run_sealed_pack_aux h32 hBits hLen hTopo S hPack hm hRoot hQ htb hRegs hSz hDisj hTreeFit hFPFit hFAFit
      hEPFit hEAFit hOrigToDense hDenseToOrig hArena hTag hQWork
  exact ⟨t, states, steps, totalWords, hTot128, hStepsLe, hRun, hTr, hPk, hTSz, hSB_fit,
    hValid, hISz, hTotWord, hKeep⟩

/-- **Master EX5.2 Packer + Prefix Shift (`sealedPackAndShiftProgram`)**:
Packs into `[sealedBase .. sealedBase + totalWords)` and forward-shifts `I` into
`[0 .. totalWords)`, matching `SealedBuild.copyPrefix` verbatim for chaining with
`SealedBuild.build` in `RamSealedOracleBuild.lean`. -/
theorem run_sealed_pack_and_shift (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {g : Digraph} {r : Fin g.vertexCount}
    {order : List (Fin g.vertexCount)}
    (hLen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order)
    {dense : List (Fin g.vertexCount)} {treeBaseG : Nat}
    (S : StaticTreeSlice s₀.data treeBaseG g r dense)
    (hPack : MatchesPackedLayout S)
    {m root Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase : Nat}
    (hm : m = g.arcCount) (hRoot : root = r.val) (hQ : Q = dense.length)
    (htb : treeBase = treeBaseG)
    (hRegs : SealedPackEntryRegs g.vertexCount m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hDisj : SealedDisjointLayout g.vertexCount Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hFPFit : forestPtrsBase + 6 * Q ≤ workCap)
    (hFAFit : forestArenaBase + forestUsed ≤ workCap)
    (hEPFit : exitPtrsBase + 3 * Q ≤ workCap)
    (hEAFit : exitArenaBase + exitUsed ≤ workCap)
    (hOrigToDense : ∀ v : Fin g.vertexCount,
      (s₀.data[3 * g.vertexCount + v.val]?).map Fin.val =
        some (if _ : v ∈ dense then dense.idxOf v + 1 else 0))
    (hDenseToOrig : ∀ d : Fin dense.length,
      (s₀.data[4 * g.vertexCount + d.val]?).map Fin.val = some (dense[d.val]'d.isLt).val)
    (hArena : ∀ d : Fin dense.length,
      OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
        exitPtrsBase exitArenaBase exitUsed s₀.data)
    (hTag : TagsFit bits) (hQWork : queryWorkCap ≤ 2 ^ bits) :
    let code := sealedPackAndShiftProgram (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32
    ∃ (t : State L16) (states : List (State L16)) (steps totalWords : Nat)
      (cfg : SealedBuild.SealLayout L16),
      cfg.k = totalWords ∧
      totalWords ≤ retainedLinearFactor * g.vertexCount ∧
      steps ≤ 1700 * (g.vertexCount + g.arcCount + 1) ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint L16 ∧
      t.data.size = workCap ∧
      ValidSealedOracleIndex g r (SealedBuild.copyPrefix cfg t) ∧
      (SealedBuild.copyPrefix cfg t).size = totalWords ∧
      ((SealedBuild.copyPrefix cfg t)[hdrTotalWords]?).map Fin.val = some totalWords := by
  intro code
  have hPosBase : 0 < sealedBase := by
    have hn : 1 ≤ g.vertexCount := Fin.pos r
    rcases hDisj.disj_orig with h | h
    · rw [retainedLinearFactor_eq] at h; omega
    · omega
  obtain ⟨t1, _, k1, totalWords, hTot128, hk1, hRun1, _, _, ht1Sz, ht1Regs, hSB_fit,
      ht1Tot, hValid1, hI1Sz, hTotWord1, _⟩ :=
    run_sealed_pack_aux h32 hBits hLen hTopo S hPack hm hRoot hQ htb hRegs hSz hDisj hTreeFit hFPFit hFAFit
      hEPFit hEAFit hOrigToDense hDenseToOrig hArena hTag hQWork
  obtain ⟨t2, k2, hk2, hRun2, ht2Sz, ht2Get⟩ :=
    run_shiftToZeroPhase h32 hBits ht1Regs ht1Sz ht1Tot hPosBase hSB_fit
  obtain ⟨t, states, _, huData, hRun, hTr, hPk⟩ :=
    run_linked_pair (sealedPackPhase h32) (shiftToZeroPhase h32).code
      (by have hSzS := shiftToZeroCode_size (bits := bits) (inputCap := inputCap) (workCap := workCap)
            (hi := hi) (hw := hw) h32
          change 0 < (shiftToZeroCode h32).size
          omega)
      hRun1 hRun2
  have hStepsLe : k1 + k2 ≤ 1700 * (g.vertexCount + g.arcCount + 1) := by
    rw [retainedLinearFactor_eq] at hTot128
    omega
  have hTSz : t.data.size = workCap := by rw [huData]; exact ht2Sz
  let cfg : SealedBuild.SealLayout L16 :=
    { registerFits := by change 16 ≤ 2 ^ bits; omega
      k := totalWords
      k_le_workCap := by change totalWords ≤ workCap; omega }
  have hCpEq : SealedBuild.copyPrefix cfg t = t1.data.extract sealedBase (sealedBase + totalWords) := by
    apply Array.ext
    · rw [SealedBuild.copyPrefix_size, hI1Sz]
    · intro i hi1 hi2
      have hiTot : i < totalWords := by rw [SealedBuild.copyPrefix_size] at hi1; exact hi1
      have hLHS : (SealedBuild.copyPrefix cfg t)[i] =
          t.data[i]'(by rw [hTSz]; omega) :=
        SealedBuild.copyPrefix_getElem cfg t ⟨i, hiTot⟩
      have hRHS : (t1.data.extract sealedBase (sealedBase + totalWords))[i]'hi2 =
          t1.data[sealedBase + i]'(by rw [ht1Sz]; omega) := by
        rw [Array.getElem_extract]
      rw [hLHS, hRHS]
      apply Option.some.inj
      rw [← Array.getElem?_eq_getElem (by rw [hTSz]; omega), huData, ht2Get i hiTot,
        Array.getElem?_eq_getElem (by rw [ht1Sz]; omega)]
  refine ⟨t, states, k1 + k2, totalWords, cfg, rfl, hTot128, hStepsLe, hRun, hTr, hPk, hTSz,
    ?_, ?_, ?_⟩
  · rw [hCpEq]; exact hValid1
  · rw [hCpEq]; exact hI1Sz
  · rw [hCpEq]; exact hTotWord1

end ExecutionProofs

end PaperB.RamSealedPacker
