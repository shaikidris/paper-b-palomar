module

public import PaperB.RamExitFamilyKernels
public import PaperB.RamExitFamilyCopies
public import PaperB.RamExitFamilyRegisters
public import PaperB.RamExitFamilyProgram
public import PaperB.RamExitFamilyLoop

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 650000
set_option maxErrors 160

/-!
The exit-family loop invariant and outer induction. The induction takes the
large-quotient step as a premise, with its exact step, space, and frame contract.
It computes the cumulative execution bound from disjoint child and arc counts.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter prefixTreeBase)
open PaperB.ForestHead (Vertex)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex)
open PaperB.ForestSlimIndex
open PaperB.OracleSealedIndexLayout (SliceAt)
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
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open PaperB.RamForestProgram.Finish (packedPayload)
open PaperB.ExitMap.Retention (TagsFit)
open PaperB.OracleContract (L)


/-! ### 5. Loop Invariant, Sub-Program Chaining, and `run_exit_family_loop` -/

section LoopInductionAndMain

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

private theorem qStartFn_prefix_mono {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) {a b : Nat}
    (hab : a ≤ b) (hb : b ≤ dense.length) :
    qStartFn S a ≤ qStartFn S b := by
  have hMono (t : Nat) : a + t ≤ dense.length → qStartFn S a ≤ qStartFn S (a + t) := by
    induction t with
    | zero => intro _; exact Nat.le_refl _
    | succ t ih =>
      intro h
      have ht : a + t < dense.length := by omega
      have hStep : qStartFn S (a + (t + 1)) = qStartFn S (a + t) +
          (S.emittedArcs ⟨a + t, ht⟩).length := by
        simpa only [Nat.add_assoc] using qStartFn_succ S ht
      rw [hStep]
      exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hab
  exact hMono t hb

structure ExitLoopInv
    {origData : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData (prefixTreeBase workCap) g r dense)
    (n m Q forestUsed d exitUsed : Nat)
    (s : State L16) : Prop where
  dLe : d ≤ Q
  szEq : s.data.size = workCap
  regs : ExitLoopRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
    (loopBaseOf workCap) d exitUsed s
  usedLe : exitUsed ≤ exitUsedPrefix S d
  inPtr : (s.data[inPtrAddr]?).map Fin.val = some (exitSubInBase (loopBaseOf workCap) n m)
  dataPtr : (s.data[dataPtrAddr]?).map Fin.val = some (exitSubWorkBase (loopBaseOf workCap) n m workCap)
  statePtr : (s.data[statePtrAddr]?).map Fin.val = some (exitSubStateBase (loopBaseOf workCap) n m)
  st11 : (s.data[exitSubStateBase (loopBaseOf workCap) n m + 11]?).map Fin.val =
    some (exitPtrsBase (loopBaseOf workCap) n m)
  st12 : (s.data[exitSubStateBase (loopBaseOf workCap) n m + 12]?).map Fin.val =
    some (exitArenaBase (loopBaseOf workCap) n m)
  st13 : (s.data[exitSubStateBase (loopBaseOf workCap) n m + 13]?).map Fin.val =
    some (exitSubInBase (loopBaseOf workCap) n m)
  st14 : (s.data[exitSubStateBase (loopBaseOf workCap) n m + 14]?).map Fin.val =
    some (exitSubWorkBase (loopBaseOf workCap) n m workCap)
  outerFrame : ∀ addr, 3 ≤ addr → addr < exitPtrsBase (loopBaseOf workCap) n m →
    s.data[addr]? = origData[addr]?
  builtLt : ∀ j : Fin dense.length, j.val < d →
    OwnerExitArenaAt S j (ownerForestPtrsBase (loopBaseOf workCap) n m)
      (forestArenaBase (loopBaseOf workCap) n m) forestUsed
      (exitPtrsBase (loopBaseOf workCap) n m) (exitArenaBase (loopBaseOf workCap) n m)
      exitUsed s.data

variable (exitLarge_sub_steps : ∀
    (h100 : 100 ≤ 2 ^ bits) (input : Input (layout16 bits inputCap workCap hi hw))
    {origData : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ j : Fin dense.length, (S.ramQuotient j).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (origData[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (j : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs j).length),
      let ea := (countingSortedArcs (1 + (S.childSlice j).length) (S.emittedArcs j))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds j hx).2.1)).symm)
      (origData[emitBaseOf workCap + 3 * n + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (origData[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.headLocal ∧
      (origData[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ j : Fin dense.length,
      OwnerForestPackedRecordAt S j (loopBaseOf workCap) n m forestUsed origData)
    {d : Fin dense.length} {exitUsed : Nat} {s₀ : State (layout16 bits inputCap workCap hi hw)}
    (hInv : ExitLoopInv S n m Q forestUsed d.val exitUsed s₀)
    (hPC : s₀.pc = offLargeA)
    (hr11 : (reg s₀ r11).val = 1 + (S.childSlice d).length)
    (hLarge : 3 ≤ 1 + (S.childSlice d).length),
    let code := exitFamilyLoopProgram hi hw h100
    ∃ (sEnd : State (layout16 bits inputCap workCap hi hw)) (kIter newExitUsed : Nat),
      kIter ≤ 12300 * (2 * (S.childSlice d).length + (S.emittedArcs d).length) * OracleContract.L n ∧
      Steps code input kIter s₀ sEnd ∧
      sEnd.pc = offHdr ∧
      ExitLoopInv S n m Q forestUsed (d.val + 1) newExitUsed sEnd)

include exitLarge_sub_steps

private theorem exitLoop_spec
    (h100 : 100 ≤ 2 ^ bits) (input : Input L16)
    {origData : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ j : Fin dense.length, (S.ramQuotient j).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (origData[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (j : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs j).length),
      let ea := (countingSortedArcs (1 + (S.childSlice j).length) (S.emittedArcs j))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds j hx).2.1)).symm)
      (origData[emitBaseOf workCap + 3 * n + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (origData[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.headLocal ∧
      (origData[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S j.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ j : Fin dense.length,
      OwnerForestPackedRecordAt S j (loopBaseOf workCap) n m forestUsed origData) :
    ∀ (rem d exitUsed : Nat) (s : State L16),
      d + rem = Q →
      s.pc = offHdr →
      ExitLoopInv S n m Q forestUsed d exitUsed s →
      ∃ (sEnd : State L16) (kRem endUsed : Nat),
        kRem ≤ 30 * rem +
          12300 * (2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d)) *
            OracleContract.L n ∧
        Steps (exitFamilyLoopProgram hi hw h100) input kRem s sEnd ∧
        sEnd.pc = offHdr ∧
        ExitLoopInv S n m Q forestUsed Q endUsed sEnd := by
  let subCode := exitSubProgram hw h100
  have hnPos : 1 ≤ n := by rw [hn]; exact Fin.pos r
  have hQn : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hTreeFit : prefixTreeBase workCap + staticTreeWords Q ≤ workCap := by
    have := Nat.mul_div_le workCap 4
    first | (simp only [prefixTreeBase, prefixQuarter, staticTreeWords]; omega) | omega
  have hWorkEnd : exitSubWorkBase (loopBaseOf workCap) n m workCap + workCap / 16 ≤ workCap :=
    exitSubWorkEnd_le_workCap hCap
  have hEndEA : exitArenaBase (loopBaseOf workCap) n m ≤ workCap := by
    unfold exitSubWorkBase exitSubInBase exitSubStateBase at hWorkEnd; omega
  intro rem
  induction rem with
  | zero =>
    intro d exitUsed s hd hPC hInv
    have hdEq : d = Q := by omega
    subst d
    have hCS0 : S.childStart Q - S.childStart Q = 0 := Nat.sub_self _
    have hQS0 : qStartFn S Q - qStartFn S Q = 0 := Nat.sub_self _
    exact ⟨s, 0, exitUsed, by rw [hCS0, hQS0]; omega, Steps.zero s, hPC, hInv⟩
  | succ rem ih =>
    intro d exitUsed s hd hPC hInv
    have hdLtQ : d < Q := by omega
    let dFin : Fin dense.length := ⟨d, by rw [← hQ]; exact hdLtQ⟩
    obtain ⟨sP, hsHdr, pcP, rP, dP⟩ :=
      exitHdr_lt_step (sp_hdr subCode h100) (by rw [exitFamilyLoopCodeOf_size]; first | (simp only [offHdr]; omega) | omega)
        hPC hInv.regs hdLtQ
    have hRegsP : ExitLoopRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
        (loopBaseOf workCap) d exitUsed sP :=
      exitLoopRegs_of_keep hInv.regs (fun i _ => reg_eq_of_regs_eq rP i)
    have hTreeMemP : ∀ k, prefixTreeBase workCap ≤ k → k < prefixTreeBase workCap + staticTreeWords Q →
        sP.data[k]? = origData[k]? := by
      intro k hk1 hk2
      rw [dP]
      refine hInv.outerFrame k (by unfold prefixTreeBase prefixQuarter at hk1; omega) ?_
      have := Nat.mul_div_le workCap 4
      unfold prefixTreeBase prefixQuarter staticTreeWords at hk2
      first | (simp only [exitPtrsBase, loopBaseOf, prefixQuarter, loopWorkWords]; omega) | omega
    obtain ⟨sBr, hsBr, pcBr, dBr, regsBr, hr11⟩ :=
      exitPrep_steps h100 (sp_prep subCode h100)
        (by rw [exitFamilyLoopCodeOf_size]; first | (simp only [offLargeA]; omega) | omega)
        S hQ hTreeFit hBits pcP hTreeMemP dFin hRegsP
    have hDataEqBr : sBr.data = s.data := dBr.trans dP
    by_cases hSmall : 1 + (S.childSlice dFin).length < 3
    · rw [ite_eq_left hSmall] at pcBr
      obtain ⟨sNext, hsSm, pcNext, szNext, regsNext, _, hFrSm⟩ :=
        exitSmall_steps h100 (sp_small subCode h100)
          (by rw [exitFamilyLoopCodeOf_size]; first | (simp only [offSmall]; omega) | omega)
          pcBr (by rw [hDataEqBr, hInv.szEq]) regsBr hdLtQ hQn
          (by rw [hDataEqBr]; exact hInv.statePtr) (by rw [hDataEqBr]; exact hInv.st11)
          hEndEA hBits
      have hUsedNextLe : exitUsed ≤ exitUsedPrefix S (d + 1) := by
        have hSucc : exitUsedPrefix S (d + 1) = exitUsedPrefix S d +
            (if 3 ≤ 1 + (S.childSlice dFin).length then
              47 * (S.childSlice dFin).length else 0) := exitUsedPrefix_succ S dFin.isLt
        rw [hSucc, ite_eq_right (by omega), Nat.add_zero]
        exact hInv.usedLe
      have hOuterNext : ∀ addr, 3 ≤ addr → addr < exitPtrsBase (loopBaseOf workCap) n m →
          sNext.data[addr]? = origData[addr]? := by
        intro addr ha1 ha2
        rw [hFrSm addr (Or.inl (by omega)), hDataEqBr]
        exact hInv.outerFrame addr ha1 ha2
      have hArenaD : OwnerExitArenaAt S dFin (ownerForestPtrsBase (loopBaseOf workCap) n m)
          (forestArenaBase (loopBaseOf workCap) n m) forestUsed (exitPtrsBase (loopBaseOf workCap) n m)
          (exitArenaBase (loopBaseOf workCap) n m) exitUsed sNext.data := by
        try simp only [OwnerExitArenaAt]
        rw [dite_eq_right (by omega)]
        trivial
      have hBuiltNext : ∀ j : Fin dense.length, j.val < d + 1 →
          OwnerExitArenaAt S j (ownerForestPtrsBase (loopBaseOf workCap) n m)
            (forestArenaBase (loopBaseOf workCap) n m) forestUsed (exitPtrsBase (loopBaseOf workCap) n m)
            (exitArenaBase (loopBaseOf workCap) n m) exitUsed sNext.data := by
        intro j hj
        by_cases hEq : j.val = d
        · have : j = dFin := Fin.ext hEq
          rw [this]; exact hArenaD
        · refine ownerExitArena_mono S j (hInv.builtLt j (by omega)) (Nat.le_refl _)
            (by rw [szNext, hInv.szEq]) ?_ ?_ ?_ ?_
          · intro k hk
            rw [hFrSm _ (Or.inl (by have := ownerForestPtrsBase_add_44n (loopBaseOf workCap) n m; omega)),
              hDataEqBr]
          · intro addr ha1 ha2
            have hFA : forestArenaBase (loopBaseOf workCap) n m + forestUsed ≤
                exitPtrsBase (loopBaseOf workCap) n m := by
              have := forestArenaEnd_eq (loopBaseOf workCap) n m; first | (simp only [exitPtrsBase]; omega) | omega
            rw [hFrSm _ (Or.inl (by omega)), hDataEqBr]
          · intro k hk
            let a := exitPtrsBase (loopBaseOf workCap) n m + 3 * j.val + k
            have hjd : j.val < d := by omega
            have hAddr : a < exitPtrsBase (loopBaseOf workCap) n m + 3 * d := by
              dsimp only [a]
              omega
            exact (hFrSm a (Or.inl hAddr)).trans (congrArg (fun m => m[a]?) hDataEqBr)
          · intro addr ha1 ha2
            rw [hFrSm _ (Or.inr (by unfold exitArenaBase at ha1; omega)), hDataEqBr]
      have hInvNext : ExitLoopInv S n m Q forestUsed (d + 1) exitUsed sNext :=
        { dLe := by omega
          szEq := szNext
          regs := regsNext
          usedLe := hUsedNextLe
          inPtr := by rw [hFrSm _ (Or.inl (by first | (simp only [inPtrAddr, exitPtrsBase, loopWorkWords]; omega) | omega)), hDataEqBr]; exact hInv.inPtr
          dataPtr := by rw [hFrSm _ (Or.inl (by first | (simp only [dataPtrAddr, exitPtrsBase, loopWorkWords]; omega) | omega)), hDataEqBr]; exact hInv.dataPtr
          statePtr := by rw [hFrSm _ (Or.inl (by first | (simp only [statePtrAddr, exitPtrsBase, loopWorkWords]; omega) | omega)), hDataEqBr]; exact hInv.statePtr
          st11 := by rw [hFrSm _ (Or.inr (by first | (simp only [exitSubStateBase, exitArenaBase]; omega) | omega)), hDataEqBr]; exact hInv.st11
          st12 := by rw [hFrSm _ (Or.inr (by first | (simp only [exitSubStateBase, exitArenaBase]; omega) | omega)), hDataEqBr]; exact hInv.st12
          st13 := by rw [hFrSm _ (Or.inr (by first | (simp only [exitSubStateBase, exitArenaBase]; omega) | omega)), hDataEqBr]; exact hInv.st13
          st14 := by rw [hFrSm _ (Or.inr (by first | (simp only [exitSubStateBase, exitArenaBase]; omega) | omega)), hDataEqBr]; exact hInv.st14
          outerFrame := hOuterNext
          builtLt := hBuiltNext }
      obtain ⟨sEnd, kTail, endUsed, hkTail, hsTail, pcEnd, hInvEnd⟩ :=
        ih (d + 1) exitUsed sNext (by omega) pcNext hInvNext
      have hCSMono : S.childStart d ≤ S.childStart (d + 1) :=
        S.childStart_mono d (d + 1) (Nat.le_succ _) (by omega)
      have hCSQ : S.childStart (d + 1) ≤ S.childStart Q :=
        S.childStart_mono (d + 1) Q (by omega) (by rw [hQ] <;> omega)
      have hQSMono : qStartFn S d ≤ qStartFn S (d + 1) := by
        rw [qStartFn_succ S dFin.isLt]; exact Nat.le_add_right _ _
      have hQSQ : qStartFn S (d + 1) ≤ qStartFn S Q :=
        qStartFn_prefix_mono S (by omega) (by rw [hQ] <;> omega)
      have hkAll : 1 + 13 + 15 + kTail ≤ 30 * (rem + 1) +
          12300 * (2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d)) *
            OracleContract.L n := by
        have hDiff : 2 * (S.childStart Q - S.childStart (d + 1)) + (qStartFn S Q - qStartFn S (d + 1)) ≤
            2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d) := by omega
        have hMul : 12300 * (2 * (S.childStart Q - S.childStart (d + 1)) +
              (qStartFn S Q - qStartFn S (d + 1))) * OracleContract.L n ≤
            12300 * (2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d)) *
              OracleContract.L n :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDiff)
        omega
      exact ⟨sEnd, 1 + 13 + 15 + kTail, endUsed, hkAll,
        by
          change Steps (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) input _ s sEnd
          simpa only [Nat.add_assoc] using hsHdr.append (hsBr.append (hsSm.append hsTail)), pcEnd, hInvEnd⟩
    · rw [ite_eq_right hSmall] at pcBr
      have hLarge : 3 ≤ 1 + (S.childSlice dFin).length := by omega
      have hInvBr : ExitLoopInv S n m Q forestUsed d exitUsed sBr :=
        { hInv with
          regs := regsBr
          szEq := by rw [hDataEqBr]; exact hInv.szEq
          inPtr := by rw [hDataEqBr]; exact hInv.inPtr
          dataPtr := by rw [hDataEqBr]; exact hInv.dataPtr
          statePtr := by rw [hDataEqBr]; exact hInv.statePtr
          st11 := by rw [hDataEqBr]; exact hInv.st11
          st12 := by rw [hDataEqBr]; exact hInv.st12
          st13 := by rw [hDataEqBr]; exact hInv.st13
          st14 := by rw [hDataEqBr]; exact hInv.st14
          outerFrame := fun a ha1 ha2 => by rw [hDataEqBr]; exact hInv.outerFrame a ha1 ha2
          builtLt := fun j hj => by rw [hDataEqBr]; exact hInv.builtLt j hj }
      obtain ⟨sNext, kIter, nextUsed, hkIter, hsIter, pcNext, hInvNext⟩ :=
        exitLarge_sub_steps h100 input S hn hm hQ hFlat hCap hBits hForestLe hQStarts hArcs hRecs
          hInvBr pcBr hr11 hLarge
      obtain ⟨sEnd, kTail, endUsed, hkTail, hsTail, pcEnd, hInvEnd⟩ :=
        ih (d + 1) nextUsed sNext (by omega) pcNext hInvNext
      have hSliceLen : (S.childSlice dFin).length = S.childStart (d + 1) - S.childStart d := by
        simp [StaticTreeSlice.childSlice, dFin]
      have hCSMono : S.childStart d ≤ S.childStart (d + 1) :=
        S.childStart_mono d (d + 1) (Nat.le_succ _) (by omega)
      have hCSQ : S.childStart (d + 1) ≤ S.childStart Q :=
        S.childStart_mono (d + 1) Q (by omega) (by rw [hQ] <;> omega)
      have hQSSucc : qStartFn S (d + 1) = qStartFn S d + (S.emittedArcs dFin).length :=
        qStartFn_succ S dFin.isLt
      have hQSQ : qStartFn S (d + 1) ≤ qStartFn S Q :=
        qStartFn_prefix_mono S (by omega) (by rw [hQ] <;> omega)
      have hkAll : 1 + 13 + kIter + kTail ≤ 30 * (rem + 1) +
          12300 * (2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d)) *
            OracleContract.L n := by
        have hFactor : 12300 * (2 * (S.childSlice dFin).length + (S.emittedArcs dFin).length) * OracleContract.L n +
            12300 * (2 * (S.childStart Q - S.childStart (d + 1)) + (qStartFn S Q - qStartFn S (d + 1))) *
              OracleContract.L n =
            12300 * (2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d)) *
              OracleContract.L n := by
          have hS : (2 * (S.childSlice dFin).length + (S.emittedArcs dFin).length) +
              (2 * (S.childStart Q - S.childStart (d + 1)) + (qStartFn S Q - qStartFn S (d + 1))) =
              2 * (S.childStart Q - S.childStart d) + (qStartFn S Q - qStartFn S d) := by
            rw [hSliceLen, hQSSucc]; omega
          rw [← Nat.add_mul, ← Nat.mul_add, hS]
        omega
      exact ⟨sEnd, 1 + 13 + kIter + kTail, endUsed, hkAll,
        by
          change Steps (exitFamilyLoopCodeOf (hi := hi) (hw := hw) subCode h100) input _ s sEnd
          simpa only [Nat.add_assoc] using hsHdr.append (hsBr.append (hsIter.append hsTail)), pcEnd, hInvEnd⟩

/-- End-to-end execution theorem for `exitFamilyLoopProgram`: starting from
`LoopIterRegs` (and `StaticTreeSlice`, counting-sorted `emitBase` arcs, and
`OwnerForestPackedRecordAt` from `prefixAndForestLoopProgram`), computes all
owner exit summaries in `O((n + m + 1) * L n)` Word-RAM steps (`≤ 30000 * ...`),
producing `SealedPackEntryRegs`, `SealedDisjointLayout`, `OwnerExitArenaAt` for
every `d < Q`, `exitUsed ≤ 48 * n`, and preserving `[3 .. exitPtrsBase)`. -/
theorem run_exit_family_loop_of_large
    (h100 : 100 ≤ 2 ^ bits) (input : Input L16)
    {s₀ : State L16}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice s₀.data (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ d : Fin dense.length, (S.ramQuotient d).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
      (loopBaseOf workCap) Q forestUsed s₀)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds d hx).2.1)).symm)
      (s₀.data[emitBaseOf workCap + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ d : Fin dense.length,
      OwnerForestPackedRecordAt S d (loopBaseOf workCap) n m forestUsed s₀.data) :
    let code := exitFamilyLoopProgram hi hw h100
    ∃ (t : State L16) (states : List (State L16)) (steps exitUsed : Nat),
      steps ≤ 30000 * ((n + m + 1) * OracleContract.L n) ∧
      steps ≤ 30000 * ((n + m + 1) * OracleContract.L n ^ 2) ∧
      Steps code input (steps - 1) (Phase.initial s₀) t ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = inputCap + workCap + 16 ∧
      t.pc = code.size - 1 ∧
      exitUsed ≤ 48 * n ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m r.val Q (prefixTreeBase workCap)
        (ownerForestPtrsBase (loopBaseOf workCap) n m)
        (exitPtrsBase (loopBaseOf workCap) n m) (5 * n) t ∧
      SealedDisjointLayout n Q (prefixTreeBase workCap)
        (ownerForestPtrsBase (loopBaseOf workCap) n m)
        (forestArenaBase (loopBaseOf workCap) n m) forestUsed
        (exitPtrsBase (loopBaseOf workCap) n m)
        (exitArenaBase (loopBaseOf workCap) n m) exitUsed (5 * n) workCap ∧
      (∀ d : Fin dense.length,
        OwnerExitArenaAt S d (ownerForestPtrsBase (loopBaseOf workCap) n m)
          (forestArenaBase (loopBaseOf workCap) n m) forestUsed
          (exitPtrsBase (loopBaseOf workCap) n m)
          (exitArenaBase (loopBaseOf workCap) n m) exitUsed t.data) ∧
      (∀ addr, 3 ≤ addr → addr < exitPtrsBase (loopBaseOf workCap) n m →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  let subCode := exitSubProgram hw h100
  have hnPos : 1 ≤ n := by rw [hn]; exact Fin.pos r
  have hQn : Q ≤ n := by rw [hQ, hn]; exact S.length_le
  have hWorkEnd : exitSubWorkBase (loopBaseOf workCap) n m workCap + workCap / 16 ≤ workCap :=
    exitSubWorkEnd_le_workCap hCap
  have hInitPC : (Phase.initial s₀).pc = offInitA := rfl
  have hInitSz : (Phase.initial s₀).data.size = workCap := hSz
  have hInitRegs : LoopEntryRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
      (loopBaseOf workCap) (Phase.initial s₀) :=
    (exitLoopRegs_of_keep
      (show ExitLoopRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
          (loopBaseOf workCap) (reg s₀ r9).val (reg s₀ r10).val s₀ from
        ⟨hRegs.entry, rfl, rfl⟩)
      (fun i _ => reg_eq_of_regs_eq (show (Phase.initial s₀).regs = s₀.regs from rfl) i)).entry
  obtain ⟨s1, hsInit, pc1, sz1, regs1, m0, m1, m2, m11, m12, m13, m14, hFrInit⟩ :=
    exitInit_steps h100 (sp_initA subCode h100) (sp_initB subCode h100)
      (by rw [exitFamilyLoopCodeOf_size]; first | (simp only [offInitB]; omega) | omega)
      hInitPC hInitSz hInitRegs (by first | (simp only [exitSubWorkBase] at hWorkEnd ⊢; omega) | omega) hBits
  have hOuterInit : ∀ addr, 3 ≤ addr → addr < exitPtrsBase (loopBaseOf workCap) n m →
      s1.data[addr]? = s₀.data[addr]? := by
    intro addr ha1 ha2
    exact hFrInit addr (by first | (simp only [inPtrAddr]; omega) | omega) (by first | (simp only [dataPtrAddr]; omega) | omega)
      (by first | (simp only [statePtrAddr]; omega) | omega) (Or.inl (by first | (simp only [exitSubStateBase, exitArenaBase]; omega) | omega))
  have hInv0 : ExitLoopInv S n m Q forestUsed 0 0 s1 :=
    { dLe := Nat.zero_le Q
      szEq := sz1
      regs := regs1
      usedLe := by rw [exitUsedPrefix_zero]; exact Nat.le_refl 0
      inPtr := m0
      dataPtr := m1
      statePtr := m2
      st11 := m11
      st12 := m12
      st13 := m13
      st14 := m14
      outerFrame := hOuterInit
      builtLt := fun j hj => by omega }
  obtain ⟨sQ, kLoop, exitUsed, hkLoop, hsLoop, pcQ, hInvQ⟩ :=
    exitLoop_spec exitLarge_sub_steps h100 input S hn hm hQ hFlat hCap hBits hForestLe hQStarts hArcs hRecs
      Q 0 0 s1 (Nat.zero_add Q) pc1 hInv0
  obtain ⟨sFinIn, hsDone, pcFinIn, rFinIn, dFinIn⟩ :=
    exitHdr_done_step (sp_hdr subCode h100)
      (by rw [exitFamilyLoopCodeOf_size]; first | (simp only [offFinish]; omega) | omega)
      pcQ hInvQ.regs
  have hRegsFinIn : ExitLoopRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
      (loopBaseOf workCap) Q exitUsed sFinIn :=
    exitLoopRegs_of_keep hInvQ.regs (fun i _ => reg_eq_of_regs_eq rFinIn i)
  obtain ⟨t, hsFinish, pcT, dT, hSealedRegs⟩ :=
    exitFinish_steps h100 (sp_finish subCode h100)
      (by rw [exitFamilyLoopCodeOf_size]; first | (simp only [offFinish]; omega) | omega)
      pcFinIn (by rw [dFinIn, hInvQ.szEq]) hRegsFinIn
      (by rw [dFinIn]; exact hInvQ.statePtr) (by rw [dFinIn]; exact hInvQ.st11)
      (by unfold exitSubWorkBase exitSubInBase exitSubStateBase exitArenaBase at hWorkEnd; omega)
      hBits
  have hPCFin : t.pc = code.size - 1 := by
    change t.pc = (exitFamilyLoopCodeOf subCode h100).size - 1
    rw [pcT, exitFamilyLoopCodeOf_size]; first | (simp only [offFinish]; omega) | omega
  have hStepsAll : Steps code input (47 + kLoop + 1 + 16) (Phase.initial s₀) t :=
    hsInit.append (hsLoop.append (hsDone.append hsFinish))
  have hHalt : step code input t = some (.halted t) :=
    PaperB.RamProgram.step_halt_at (code := code) (input := input)
      (by rw [hPCFin]; exact exitFamilyLoopProgram_last_halt hi hw h100)
  have hRun : run code input ((47 + kLoop + 1 + 16) + 1) (Phase.initial s₀) =
      some ⟨t, (47 + kLoop + 1 + 16) + 1⟩ :=
    hStepsAll.halts hHalt
  obtain ⟨states, hTrace⟩ := run_has_successfulTrace hRun
  have hPeak : tracePeakWords input states = inputCap + workCap + 16 := by
    rw [hTrace.peak_eq]; rfl
  have hDataEqT : t.data = sQ.data := dT.trans dFinIn
  have hSzT : t.data.size = workCap := by rw [hDataEqT, hInvQ.szEq]
  have hExitUsedLe : exitUsed ≤ 48 * n := by
    rw [hn]; exact Nat.le_trans hInvQ.usedLe (exitUsedPrefix_le_48n S (hQ ▸ Nat.le_refl Q))
  have hDisj : SealedDisjointLayout n Q (prefixTreeBase workCap)
      (ownerForestPtrsBase (loopBaseOf workCap) n m)
      (forestArenaBase (loopBaseOf workCap) n m) forestUsed
      (exitPtrsBase (loopBaseOf workCap) n m)
      (exitArenaBase (loopBaseOf workCap) n m) exitUsed (5 * n) workCap := by
    have h640 : 640 * (n + m + 1) ≤ workCap := by omega
    exact canonical_quarter_disjoint hQn h640
      (by first | (simp only [ownerForestPtrsBase, loopSortEntryBase, loopCursorBase, loopDegBase, loopSubStateBase, loopSubWorkBase, loopBaseOf, prefixQuarter]; omega) | omega)
      (by first | (simp only [forestArenaBase, ownerForestPtrsBase, loopSortEntryBase, loopCursorBase, loopDegBase, loopSubStateBase, loopSubWorkBase, loopBaseOf, prefixQuarter]; omega) | omega)
      (by first | (simp only [exitPtrsBase, loopBaseOf, prefixQuarter]; omega) | omega)
      (by first | (simp only [exitArenaBase, exitPtrsBase, loopBaseOf, prefixQuarter]; omega) | omega)
  have hLPos : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hLSq : OracleContract.L n ≤ OracleContract.L n ^ 2 := by
    simpa only [Nat.pow_two, Nat.one_mul] using Nat.mul_le_mul_right (OracleContract.L n) hLPos
  have hkBound : (47 + kLoop + 1 + 16) + 1 ≤ 30000 * ((n + m + 1) * OracleContract.L n) := by
    have hCSEnd : S.childStart Q - S.childStart 0 ≤ n := by
      rw [S.childStart_zero, hQ, S.childStart_end]; omega
    have hQSEnd : qStartFn S Q - qStartFn S 0 ≤ m := by
      rw [hm, qStartFn_zero, Nat.sub_zero]; exact qStartFn_le_arcCount S Q
    have hSum : 2 * (S.childStart Q - S.childStart 0) + (qStartFn S Q - qStartFn S 0) ≤
        2 * (n + m + 1) := by omega
    have hLoopMul : 12300 * (2 * (S.childStart Q - S.childStart 0) + (qStartFn S Q - qStartFn S 0)) *
          OracleContract.L n ≤ 24600 * ((n + m + 1) * OracleContract.L n) := by
      have h1 := Nat.mul_le_mul_right (OracleContract.L n) (Nat.mul_le_mul_left 12300 hSum)
      simpa only [← Nat.mul_assoc, show 12300 * 2 = 24600 by decide] using h1
    have hConst : 47 + 30 * Q + 1 + 16 + 1 ≤ 5400 * ((n + m + 1) * OracleContract.L n) := by
      have hLin : 47 + 30 * Q + 1 + 16 + 1 ≤ 5400 * (n + m + 1) := by omega
      calc
        _ ≤ 5400 * (n + m + 1) := hLin
        _ ≤ (5400 * (n + m + 1)) * OracleContract.L n :=
          Nat.le_mul_of_pos_right _ hLPos
        _ = 5400 * ((n + m + 1) * OracleContract.L n) := Nat.mul_assoc _ _ _
    omega
  have hkBoundSq : (47 + kLoop + 1 + 16) + 1 ≤ 30000 * ((n + m + 1) * OracleContract.L n ^ 2) :=
    Nat.le_trans hkBound (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hLSq))
  refine ⟨t, states, (47 + kLoop + 1 + 16) + 1, exitUsed, hkBound, hkBoundSq,
    by simpa only [Nat.add_sub_cancel] using hStepsAll, hRun, hTrace, hPeak, hPCFin,
    hExitUsedLe, hSzT, hSealedRegs, hDisj, ?_, ?_⟩
  · intro d
    rw [hDataEqT]
    exact hInvQ.builtLt d (Nat.lt_of_lt_of_eq d.isLt hQ.symm)
  · intro addr ha1 ha2
    rw [hDataEqT]
    exact hInvQ.outerFrame addr ha1 ha2

end LoopInductionAndMain

end PaperB.RamExitFamilyLoop
