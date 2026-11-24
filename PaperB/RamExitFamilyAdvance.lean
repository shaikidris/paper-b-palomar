module

public import PaperB.RamExitFamilyInduction

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option warningAsError true

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter prefixTreeBase)
open PaperB.ForestHead (Vertex)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex rawInputCap)
open PaperB.ForestSlimIndex
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
open PaperB.RamStaticReaderBridge (denseRank)
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



variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

/-- Advance the loop invariant after a checked owner record has been stored.
The memory frame guarantees that earlier records remain queryable. -/
theorem ExitLoopInv.advance
    {origData : Array (Word bits)} {g : Digraph} {r : Fin g.vertexCount}
    {dense : List (Fin g.vertexCount)}
    {S : StaticTreeSlice origData (prefixTreeBase workCap) g r dense}
    {n m Q forestUsed exitUsed totalLen : Nat} {d : Fin dense.length}
    {s₀ sEnd : State L16}
    (hInv : ExitLoopInv S n m Q forestUsed d.val exitUsed s₀)
    (hdQ : d.val < Q) (hQn : Q ≤ n)
    (hForestLe : forestUsed ≤ 38 * n)
    (hSz : sEnd.data.size = workCap)
    (hRegs : ExitLoopRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
      (loopBaseOf workCap) (d.val + 1) (exitUsed + totalLen) sEnd)
    (hUsed : exitUsed + totalLen ≤ exitUsedPrefix S (d.val + 1))
    (hBefore : ∀ a < exitPtrsBase (loopBaseOf workCap) n m, sEnd.data[a]? = s₀.data[a]?)
    (hKeep : ∀ j, 11 ≤ j → j < 15 →
      sEnd.data[exitSubStateBase (loopBaseOf workCap) n m + j]? =
        s₀.data[exitSubStateBase (loopBaseOf workCap) n m + j]?)
    (hKeepOldPtr : ∀ j : Fin dense.length, j.val < d.val → ∀ k < 3,
      sEnd.data[exitPtrsBase (loopBaseOf workCap) n m + 3 * j.val + k]? =
        s₀.data[exitPtrsBase (loopBaseOf workCap) n m + 3 * j.val + k]?)
    (hKeepOldPayload : ∀ addr, exitArenaBase (loopBaseOf workCap) n m ≤ addr →
      addr < exitArenaBase (loopBaseOf workCap) n m + exitUsed →
      sEnd.data[addr]? = s₀.data[addr]?)
    (hNew : OwnerExitArenaAt S d (ownerForestPtrsBase (loopBaseOf workCap) n m)
      (forestArenaBase (loopBaseOf workCap) n m) forestUsed (exitPtrsBase (loopBaseOf workCap) n m)
      (exitArenaBase (loopBaseOf workCap) n m) (exitUsed + totalLen) sEnd.data) :
    ExitLoopInv S n m Q forestUsed (d.val + 1) (exitUsed + totalLen) sEnd := by
  let loopBase := loopBaseOf workCap
  have hPtrLo : 3 ≤ exitPtrsBase loopBase n m := by simp only [exitPtrsBase, loopWorkWords]; omega
  have hFPBound := ownerForestPtrsBase_add_44n loopBase n m
  have hFABound : forestArenaBase loopBase n m + forestUsed ≤ exitPtrsBase loopBase n m := by
    exact Nat.le_trans (Nat.add_le_add_left hForestLe _)
      (Nat.le_of_eq (forestArenaEnd_eq loopBase n m))
  refine
    { dLe := hdQ
      szEq := hSz
      regs := hRegs
      usedLe := hUsed
      inPtr := ?_
      dataPtr := ?_
      statePtr := ?_
      st11 := ?_
      st12 := ?_
      st13 := ?_
      st14 := ?_
      outerFrame := fun a ha1 ha2 => (hBefore a ha2).trans (hInv.outerFrame a ha1 ha2)
      builtLt := ?_ }
  · rw [hBefore inPtrAddr (by change inPtrAddr < exitPtrsBase loopBase n m; simp only [inPtrAddr]; omega)]
    exact hInv.inPtr
  · rw [hBefore dataPtrAddr (by change dataPtrAddr < exitPtrsBase loopBase n m; simp only [dataPtrAddr]; omega)]
    exact hInv.dataPtr
  · rw [hBefore statePtrAddr (by change statePtrAddr < exitPtrsBase loopBase n m; simp only [statePtrAddr]; omega)]
    exact hInv.statePtr
  · rw [hKeep 11 (by decide) (by decide)]
    exact hInv.st11
  · rw [hKeep 12 (by decide) (by decide)]
    exact hInv.st12
  · rw [hKeep 13 (by decide) (by decide)]
    exact hInv.st13
  · rw [hKeep 14 (by decide) (by decide)]
    exact hInv.st14
  · intro j hj
    by_cases heq : j = d
    · exact heq.symm ▸ hNew
    · have hNe : j.val ≠ d.val := fun h => heq (Fin.ext h)
      have hjLt : j.val < d.val := by omega
      refine ownerExitArena_mono S j (hInv.builtLt j hjLt) (Nat.le_add_right _ _)
        (hSz.trans hInv.szEq.symm) ?_ ?_ (hKeepOldPtr j hjLt) hKeepOldPayload
      · intro k hk
        have hjN := Nat.lt_of_lt_of_le (Nat.lt_trans hjLt hdQ) hQn
        exact hBefore (ownerForestPtrsBase loopBase n m + 6 * j.val + k)
          (show ownerForestPtrsBase loopBase n m + 6 * j.val + k < exitPtrsBase loopBase n m from by omega)
      · intro addr _ hAddr
        exact hBefore addr (Nat.lt_of_lt_of_le hAddr hFABound)

end PaperB.RamExitFamilyLoop
