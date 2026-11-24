module

public import PaperB.RamPrefixAndForestLoop
public import PaperB.RamExitSummaryBuild
public import PaperB.RamSealedPacker

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-!
EX5.1 Exit-Summary Family Loop (`PaperB.RamExitFamilyLoop`):
Fixed 16-register Word-RAM program `exitFamilyLoopProgram` consuming the output of
`prefixAndForestLoopProgram` (`StaticTreeSlice`, `qStartFn`, `countingSortedArcs`,
and `OwnerForestPackedRecordAt`), invoking lifted 15-register `exitSummaryBuildProgram`
on reusable scratch `[exitSubInBase, exitSubWorkBase)` for every large quotient
(`3 ≤ n_d`), copying `[exitDepth (N_d), exitStored (18*N_d), exitPrior (6*n_d)]`
into `exitArenaBase`, writing `[ep0, ep1, ep2]` at `exitPtrsBase + 3*d` (or `[0,0,0]`
for small quotients `n_d < 3`), and halting in `SealedPackEntryRegs` +
`SealedDisjointLayout` + `OwnerExitArenaAt` for `RamSealedPacker`.
-/

namespace PaperB.RamExitFamilyLoop

open PaperB
open PaperB.RamBuildPrefix (prefixQuarter)
open PaperB.RamForestProgram.RawBuild (SerializedProperLossIndex)
open PaperB.RamForestProgram.Finish (packedPayload)
open PaperB.OracleSealedIndexLayout (SliceAt)
open PaperB.ExitMap.JumpMapRoute (foldFusedAux selectAtDepth)
open PaperB.ForestSlimIndex
open PaperB.Digraph (lemma22ExitTails)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamDagReach
open PaperB.RamPrefixAndForestLoop
open PaperB.RamFamilyForestLoop
open PaperB.RamQuotientEmitter
open PaperB.RamDataSliceAdapter
open PaperB.RamStaticReaderBridge
open PaperB.RetainedProperLoss
open PaperB.ForestHead (Vertex)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.RamSealedPacker
open PaperB.RamProgram.ExitSummaryBuild
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)
open PaperB.Digraph (dominates_refl dominates_reachable_predecessor_of_ne rank_lt_of_strict_dominator)
open PaperB.Exit.OrderedReaderResult (exitDenseOwnerSlots_read exitDenseOwnerCell exitTransferDrivers)
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase (RouteSlotEdges route_parentPath)

section LayoutAndInvariants

def exitPtrsBase (loopBase n m : Nat) : Nat :=
  loopBase + loopWorkWords n m

def exitArenaBase (loopBase n m : Nat) : Nat :=
  exitPtrsBase loopBase n m + 3 * n

def exitSubStateBase (loopBase n m : Nat) : Nat :=
  exitArenaBase loopBase n m + 48 * n

def exitSubInBase (loopBase n m : Nat) : Nat :=
  exitSubStateBase loopBase n m + 16

def exitSubWorkBase (loopBase n m workCap : Nat) : Nat :=
  exitSubInBase loopBase n m + workCap / 64

def exitFamilySubInCap (workCap : Nat) : Nat := workCap / 64

def exitFamilySubWorkCap (workCap : Nat) : Nat := workCap / 16

theorem exitSubWorkEnd_le_workCap {n m workCap : Nat}
    (hCap : 800 * (n + m + 1) ≤ workCap) :
    exitSubWorkBase (loopBaseOf workCap) n m workCap + workCap / 16 ≤ workCap := by
  have h4 : 4 * prefixQuarter workCap ≤ workCap := Nat.mul_div_le workCap 4
  have h16 : 16 * (workCap / 16) ≤ workCap := Nat.mul_div_le workCap 16
  have h64 : 64 * (workCap / 64) ≤ workCap := Nat.mul_div_le workCap 64
  unfold exitSubWorkBase exitSubInBase exitSubStateBase exitArenaBase exitPtrsBase
    loopBaseOf loopWorkWords
  omega

theorem exitSubInCap_fits {n m n_d m_d workCap : Nat}
    (hCap : 800 * (n + m + 1) ≤ workCap) (hn : n_d ≤ n) (hm : m_d ≤ m) :
    6 + 6 * n_d + 3 * m_d ≤ workCap / 64 := by
  have h64 : 64 * (workCap / 64) ≤ workCap := Nat.mul_div_le workCap 64
  omega

theorem exitSubWorkCap_fits {n m n_d m_d workCap : Nat}
    (hCap : 800 * (n + m + 1) ≤ workCap) (hLarge : 3 ≤ n_d) (hn : n_d ≤ n) (hm : m_d ≤ m) :
    exitWorkCap n_d m_d ≤ workCap / 16 := by
  have h16 : 16 * (workCap / 16) ≤ workCap := Nat.mul_div_le workCap 16
  unfold exitWorkCap
  omega

theorem L_mono {a b : Nat} (hab : a ≤ b) :
    OracleContract.L a ≤ OracleContract.L b := by
  unfold OracleContract.L
  exact Nat.add_le_add_right ((Nat.le_log2 (by omega)).mpr
    (Nat.le_trans (Nat.log2_self_le (by omega)) (Nat.add_le_add_right hab 1))) 1

/-- Strengthened owner forest record exposing the `OrderedReaderResult` witness from
`RamForestRawBuild` so downstream exit summary construction and `OwnerExitArenaAt` match
`packWordColumns ordResH hWidth`. Implies `OwnerForestRecordAt`. -/
def OwnerForestPackedRecordAt {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (loopBase n m forestUsed : Nat) (data : Array (Word bits)) : Prop :=
  let n_d := 1 + (S.childSlice d).length
  if n_d < 3 then
    ∀ k < 6, (data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
  else
    ∃ (pH : PaperB.ForestDictionary.Rows (S.ramQuotient d))
      (dataH : Array (Vertex (S.ramQuotient d)))
      (sizeH : dataH.size = (S.ramQuotient d).vertexCount)
      (rankH : Vertex (S.ramQuotient d) → Nat)
      (hlarge : 3 ≤ (S.ramQuotient d).vertexCount)
      (incH : ∀ i j : Fin (S.ramQuotient d).vertexCount, i.val < j.val →
        rankH (orderedVertexAt dataH sizeH i) < rankH (orderedVertexAt dataH sizeH j))
      (covH : ∀ v : Vertex (S.ramQuotient d), ∃ i : Fin (S.ramQuotient d).vertexCount,
        orderedVertexAt dataH sizeH i = v)
      (rArcH : ∀ u v : Vertex (S.ramQuotient d), (S.ramQuotient d).HasQuotientArc u v →
        rankH u < rankH v)
      (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
      (hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits)
      (ptrBase : Nat),
      let w := packWordColumns ordResH hWidth
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      SerializedProperLossIndex (S.ramQuotient d) w ∧
      w.wordCount ≤ 19 * n_d ∧
      forestArenaBase loopBase n m ≤ ptrBase ∧
      ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
      (∀ k < w.wordCount, data[ptrBase + k]? = (packedPayload w)[k]?)

theorem ownerForestPacked_to_record {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {S : StaticTreeSlice mem treeBase g r dense} {d : Fin dense.length}
    {loopBase n m forestUsed : Nat} {data : Array (Word bits)}
    (h : OwnerForestPackedRecordAt S d loopBase n m forestUsed data) :
    OwnerForestRecordAt S d loopBase n m forestUsed data := by
  dsimp only [OwnerForestPackedRecordAt, OwnerForestRecordAt] at h ⊢
  by_cases hSmall : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hSmall] at h ⊢; exact h
  · rw [ite_eq_right hSmall] at h ⊢
    obtain ⟨_, _, _, _, _, _, _, _, ordResH, hWidth, ptrBase, hRest⟩ := h
    exact ⟨packWordColumns ordResH hWidth, ptrBase, hRest⟩

theorem ownerForestPacked_mono {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    {loopBase n m forestUsed : Nat} {d1 d2 : Array (Word bits)}
    (h1 : OwnerForestPackedRecordAt S d loopBase n m forestUsed d1)
    (hPtrs : ∀ k < 6,
      d2[ownerForestPtrsBase loopBase n m + 6 * d.val + k]? =
        d1[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?)
    (hArena : ∀ addr, forestArenaBase loopBase n m ≤ addr →
      addr < forestArenaBase loopBase n m + forestUsed → d2[addr]? = d1[addr]?) :
    OwnerForestPackedRecordAt S d loopBase n m forestUsed d2 := by
  dsimp only [OwnerForestPackedRecordAt] at h1 ⊢
  by_cases hSmall : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hSmall] at h1 ⊢
    intro k hk; rw [hPtrs k hk]; exact h1 k hk
  · rw [ite_eq_right hSmall] at h1 ⊢
    obtain ⟨pH, dataH, sizeH, rankH, hlarge, incH, covH, rArcH, ordResH, hWidth, ptrBase,
      hIdx, hwCnt, hLo, hHi, hp0, hp1, hp2, hp3, hp4, hp5, hPay⟩ := h1
    refine ⟨pH, dataH, sizeH, rankH, hlarge, incH, covH, rArcH, ordResH, hWidth, ptrBase,
      hIdx, hwCnt, hLo, hHi, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [show d2[ownerForestPtrsBase loopBase n m + 6 * d.val]? = _ from hPtrs 0 (by decide)]; exact hp0
    · rw [hPtrs 1 (by decide)]; exact hp1
    · rw [hPtrs 2 (by decide)]; exact hp2
    · rw [hPtrs 3 (by decide)]; exact hp3
    · rw [hPtrs 4 (by decide)]; exact hp4
    · rw [hPtrs 5 (by decide)]; exact hp5
    · intro k hk
      rw [hArena (ptrBase + k) (by omega) (by omega)]
      exact hPay k hk

theorem ownerExitArena_mono {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    {forestPtrsBase forestArenaBase forestUsed exitPtrsBase exitArenaBase exitUsed1 exitUsed2 : Nat}
    {d1 d2 : Array (Word bits)}
    (h1 : OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed1 d1)
    (hFu : exitUsed1 ≤ exitUsed2)
    (hSz : d2.size = d1.size)
    (hFP : ∀ k < 6, d2[forestPtrsBase + 6 * d.val + k]? = d1[forestPtrsBase + 6 * d.val + k]?)
    (hFA : ∀ addr, forestArenaBase ≤ addr → addr < forestArenaBase + forestUsed → d2[addr]? = d1[addr]?)
    (hEP : ∀ k < 3, d2[exitPtrsBase + 3 * d.val + k]? = d1[exitPtrsBase + 3 * d.val + k]?)
    (hEA : ∀ addr, exitArenaBase ≤ addr → addr < exitArenaBase + exitUsed1 → d2[addr]? = d1[addr]?) :
    OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed2 d2 := by
  dsimp only [OwnerExitArenaAt] at h1 ⊢
  by_cases hLarge : 3 ≤ 1 + (S.childSlice d).length
  · rw [dite_eq_left hLarge] at h1 ⊢
    rcases h1 with ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R1, F, ref, wFit, ok1,
      prior, hb, B1, hPlaced1, fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2,
      hInc, hCov, hRArc, hfp0, hfp1, hfp2, hfp3, hfp4, hfp5,
      h10, h21, h32, h43, h54, hwDictSz, hwBFSz, hwBSSz, hwLabSz, hwStpSz, hwEntLe, hwCntLe,
      hfaLo, hfaHi,
      hSl0, hSl1, hSl2, hSl3, hSl4, hSl5, hRep, hKnown, hBack, hVIdx, hLabB, hHitB,
      hep0, hep1, hep2, hep0Lo, hep0Hi, hep1Lo, hep1Hi, hep2Lo, hep2Hi,
      hSlotsEq, hPriorSz, hRBase, hBStart, hDepthAddr, hExitSpec⟩
    let R2 : Region bits d2.size :=
      { slots := R1.slots
        depthAddr := R1.depthAddr
        depthMem := fun v => hSz.symm ▸ R1.depthMem v
        base := R1.base
        recordAddr := R1.recordAddr
        recordMem := fun v => hSz.symm ▸ R1.recordMem v }
    let B2 : SealedPriorBase.BaseView prior.size d2.size :=
      { start := B1.start
        fits := hSz.symm ▸ B1.fits }
    have hD1Eq : ∀ addr, exitArenaBase ≤ addr → addr < exitArenaBase + exitUsed1 →
        (hA2 : addr < d2.size) → (hA1 : addr < d1.size) → d2[addr]'hA2 = d1[addr]'hA1 := by
      intro addr ha1 ha2 hA2 hA1
      apply Option.some.inj
      rw [← Array.getElem?_eq_getElem hA2, ← Array.getElem?_eq_getElem hA1]
      exact hEA addr ha1 ha2
    have hR2Depth : ∀ x : Fin R2.slots,
        d2[(R2.depthAddr x).val]'(R2.depthMem x) = d1[(R1.depthAddr x).val]'(R1.depthMem x) := by
      intro x
      have hx := hDepthAddr x
      have hxLt : x.val < wCols.entry.size := by rw [← hSlotsEq]; exact x.isLt
      change (R1.depthAddr x).val = ep0 + x.val at hx
      refine hD1Eq (R1.depthAddr x).val ?_ ?_ (R2.depthMem x) (R1.depthMem x)
      · rw [hx]; omega
      · rw [hx]; omega
    have hR2Rec : ∀ (v : Fin R2.slots) (i : Fin 18),
        d2[R2.base.val + 18 * v.val + i.val]'(by exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (R2.recordMem v)) =
          d1[R1.base.val + 18 * v.val + i.val]'(by exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt _) (R1.recordMem v)) := by
      intro v i
      have hvLt : v.val < wCols.entry.size := by rw [← hSlotsEq]; exact v.isLt
      have hiLt := i.isLt
      change d2[R1.base.val + 18 * v.val + i.val]'_ = d1[R1.base.val + 18 * v.val + i.val]'_
      exact hD1Eq _ (by rw [hRBase]; omega) (by rw [hRBase]; omega) _ _
    have ok2 : Occupied d2 R2 F ref wFit :=
      { size_eq := ok1.size_eq
        valid := ok1.valid
        depth := fun v => by rw [hR2Depth v]; exact ok1.depth v
        parent_eq := ok1.parent_eq
        jump_eq := ok1.jump_eq
        maps := ok1.maps
        packed := fun v hr i => by rw [hR2Rec v i]; exact ok1.packed v hr i }
    have hPlaced2 : SealedPriorBase.Placed wFit prior hb d2 B2 := by
      intro j
      have hj := j.isLt
      have hEq : d2[B2.start + j.val]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) B2.fits) =
          d1[B1.start + j.val]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) B1.fits) :=
        hD1Eq (B1.start + j.val) (by rw [hBStart]; omega) (by rw [hBStart]; omega) _ _
      exact hEq.trans (hPlaced1 j)
    have hEqFA : ∀ (sBase : Nat) (vals : Array (Word bits)),
        forestArenaBase ≤ sBase → sBase + vals.size ≤ forestArenaBase + forestUsed →
        SliceAt d1 sBase vals → SliceAt d2 sBase vals := by
      intro sBase vals hs1 hs2 hSl
      refine ⟨hSz.symm ▸ hSl.1, fun k hk => ?_⟩
      rw [hFA (sBase + k) (by omega) (by omega)]
      exact hSl.2 k hk
    have hfp0' : (d2[forestPtrsBase + 6 * d.val]?).map Fin.val = some fp0 := by
      rw [show d2[forestPtrsBase + 6 * d.val]? = _ from hFP 0 (by decide)]; exact hfp0
    have hD2 : ((d2[fp0]?).map Fin.val).getD 0 = ((d1[fp0]?).map Fin.val).getD 0 := by
      rw [hFA fp0 hfaLo (by omega)]
    have hDepthEq2 : ∀ a, depthAt d2 R2 a = depthAt d1 R1 a := by
      intro a
      by_cases ha : a < R1.slots
      · simp only [depthAt, show R2.slots = R1.slots from rfl, dite_eq_left ha]
        exact congrArg Fin.val (hR2Depth ⟨a, ha⟩)
      · simp only [depthAt, show R2.slots = R1.slots from rfl, dite_eq_right ha]
    have hRecEq2 : ∀ a, recordAt d2 R2 wFit.tags a = recordAt d1 R1 wFit.tags a := by
      intro a
      by_cases ha : a < R1.slots
      · simp only [recordAt, show R2.slots = R1.slots from rfl, dite_eq_left ha]
        unfold PaperB.StoredPacking.readStoredAt PaperB.StoredPacking.readStoredBlockAt
        congr 1
        funext i
        simp only [PaperB.StoredPacking.stored_offset_no_wrap]
        change d2[R2.base.val + 18 * a + i.val]'_ = d1[R1.base.val + 18 * a + i.val]'_
        exact hR2Rec ⟨a, ha⟩ i
      · simp only [recordAt, show R2.slots = R1.slots from rfl, dite_eq_right ha]
    have hFoldEq2 : ∀ u dd, foldStored d2 R2 wFit.tags u dd = foldStored d1 R1 wFit.tags u dd := by
      intro u dd
      simp only [foldStored, funext hDepthEq2, funext hRecEq2]
    refine ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R2, F, ref, wFit, ok2,
      prior, hb, B2, hPlaced2, fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2,
      hInc, hCov, hRArc, hfp0', ?_, ?_, ?_, ?_, ?_,
      ?_, h21, h32, h43, h54, ?_, hwBFSz, hwBSSz, hwLabSz, hwStpSz, hwEntLe, hwCntLe,
      hfaLo, hfaHi,
      hEqFA fp0 wCols.dictionary hfaLo (by rw [hwDictSz, ← h10]; omega) hSl0,
      ?_, ?_, ?_, ?_, ?_, hRep, hKnown, hBack, hVIdx, hLabB, hHitB,
      ?_, ?_, ?_, hep0Lo, by omega, hep1Lo, by omega, hep2Lo, by omega,
      hSlotsEq, hPriorSz, hRBase, hBStart, hDepthAddr, ?_⟩
    · rw [hFP 1 (by decide)]; exact hfp1
    · rw [hFP 2 (by decide)]; exact hfp2
    · rw [hFP 3 (by decide)]; exact hfp3
    · rw [hFP 4 (by decide)]; exact hfp4
    · rw [hFP 5 (by decide)]; exact hfp5
    · rw [hD2]; exact h10
    · rw [hD2]; exact hwDictSz
    · exact hEqFA fp1 wCols.back.tagAndFirst (by omega) (by omega) hSl1
    · exact hEqFA fp2 wCols.back.second (by omega) (by omega) hSl2
    · exact hEqFA fp3 wCols.labels (by omega) (by omega) hSl3
    · exact hEqFA fp4 wCols.entry (by omega) (by omega) hSl4
    · exact hEqFA fp5 wCols.stop (by omega) (by omega) hSl5
    · rw [show d2[exitPtrsBase + 3 * d.val]? = _ from hEP 0 (by decide)]; exact hep0
    · rw [hEP 1 (by decide)]; exact hep1
    · rw [hEP 2 (by decide)]; exact hep2
    · intro P hCan aNode hHit y hProp
      have hEx := hExitSpec P hCan aNode hHit y hProp
      have hD : depthAt d2 R2 aNode = depthAt d1 R1 aNode := hDepthEq2 aNode
      change (foldStored d2 R2 wFit.tags (wCols.labelAt y.val) (depthAt d2 R2 aNode)).steps ≤ _ ∧ _
      rw [hD, hFoldEq2]
      refine ⟨hEx.1, fun hP => ?_⟩
      have hRun2 : PriorBase.run d2 R2 wFit.tags prior ⟨y.val, hP⟩ (wCols.labelAt y.val) (depthAt d1 R1 aNode) =
          PriorBase.run d1 R1 wFit.tags prior ⟨y.val, hP⟩ (wCols.labelAt y.val) (depthAt d1 R1 aNode) := by
        simp only [PriorBase.run, hFoldEq2]
      rw [hRun2]
      exact hEx.2 hP
  · rw [dite_eq_right hLarge]
    trivial

/-- Loop registers during exit-summary iteration `d` with `exitUsed` words allocated in `exitArena`. -/
structure ExitLoopRegs (n m root Q treeBase emitBase loopBase d exitUsed : Nat)
    {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  entry : LoopEntryRegs n m root Q treeBase emitBase loopBase s
  dVal : (reg s r9).val = d
  usedVal : (reg s r10).val = exitUsed

theorem exitLoopRegs_of_keep {n m root Q treeBase emitBase loopBase d exitUsed : Nat}
    {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {s t : State (layout16 bits inputCap workCap hi hw)}
    (h : ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed s)
    (hKeep : ∀ r : Fin 16, r.val ≤ 10 → reg t r = reg s r) :
    ExitLoopRegs n m root Q treeBase emitBase loopBase d exitUsed t where
  entry :=
    { consts :=
        { zero := (congrArg Fin.val (hKeep rZero (by decide))).trans h.entry.consts.zero
          one := (congrArg Fin.val (hKeep rOne (by decide))).trans h.entry.consts.one
          nVal := (congrArg Fin.val (hKeep rN (by decide))).trans h.entry.consts.nVal
          mVal := (congrArg Fin.val (hKeep rM (by decide))).trans h.entry.consts.mVal
          rootVal := (congrArg Fin.val (hKeep rRoot (by decide))).trans h.entry.consts.rootVal }
      qVal := (congrArg Fin.val (hKeep r5 (by decide))).trans h.entry.qVal
      treeBaseVal := (congrArg Fin.val (hKeep r6 (by decide))).trans h.entry.treeBaseVal
      emitBaseVal := (congrArg Fin.val (hKeep r7 (by decide))).trans h.entry.emitBaseVal
      loopBaseVal := (congrArg Fin.val (hKeep r8 (by decide))).trans h.entry.loopBaseVal }
  dVal := (congrArg Fin.val (hKeep r9 (by decide))).trans h.dVal
  usedVal := (congrArg Fin.val (hKeep r10 (by decide))).trans h.usedVal

end LayoutAndInvariants

end PaperB.RamExitFamilyLoop
