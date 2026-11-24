module

public import PaperB.Exit
public import PaperB.ForestBuild
public import PaperB.TreeIndex
public import PaperB.ForestIntervals
public import PaperB.ForestIntervalQuery
public import PaperB.ExitMap
public import PaperB.ExitSummary
public import PaperB.FiniteSiblingFlat
public import PaperB.FiniteSiblingBudget
public import PaperB.SiblingVertexBudget
public import PaperB.ExitNonempty
public import PaperB.ThirdBlockLift
public import PaperB.ThirdBlock
public import PaperB.LastExit
public import PaperB.StructuralPaper
public import PaperB.LastExitBridge
public import PaperB.SeedOrder
public import PaperB.ArcOwnerTotal
public import PaperB.SeedOrderActual
public import PaperB.ExitIncoming
public import PaperB.ExitLCABridge
public import PaperB.ExitMapRetention
public import PaperB.JumpMapFold
public import PaperB.ExitArraySweep
public import PaperB.ActualJumpMaps
public import PaperB.LastExitPaper
public import PaperB.ExitKernels
public import PaperB.FusedJumpMaps
public import PaperB.GlobalSiblingEmitter
public import PaperB.RetainedRouteProof
public import PaperB.BothReachableRoute
public import PaperB.PhysicalExitModel
public import PaperB.ExitLinearSchedule
public import PaperB.ThirdReachableRoute
public import PaperB.AllOrigOracleCases
public import PaperB.ExitSpanBridge
public import PaperB.OriginalStaticConnector
public import PaperB.DenseQuotientRows
public import PaperB.ForestEventChronology
public import PaperB.ExitActualInputsBuild
public import PaperB.ExitActualContract
public import PaperB.ActualOnlineOracle

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
`PaperB.Index` closes milestone `EX4.2` + `EX4.3` and certifies Paper B **Lemma 5.1**
(`PaperB.compressed_exit_summaries`), together with the Paper B v1.2 cubic and
original-tree LCA correspondence (`PaperB.compressed_exit_summaries_v12`) and
constructive non-vacuity (`PaperB.compressed_exit_summaries_nonvacuous`).
-/

namespace PaperB

open PaperB.LabelledQuotient
open PaperB.ForestHead
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.BuiltExit
open PaperB.BuiltExit.PackedRuntime.ExactCount
open PaperB.EX24.InputPrepCheckpoint
open PaperB.Exit.OrderedReaderResult
open PaperB.ExitActualContract
open _root_.EX24.PreparedSweep

/-- **Paper B v1.3, Lemma 5.1 (compressed exit summaries).**
Given a flat acyclic quotient `H` with `3 ≤ H.vertexCount`, a topological ordered
forest reader `r`, and original-tree preorder ranks `entryRank` fitting fixed-width
words, builds in topological order a sealed base vector (`6 * H.vertexCount` words)
and constant-size jump-map bank (`≤ 19 * (H.vertexCount + 1)` words) occupying
`≤ 25 * H.vertexCount + 19 ≤ 44 * H.vertexCount + 19` retained words (`O(n_H)`), in
`≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount` total build
steps (`O((n_H + m_H) L)`) using `O(n_H + m_H)` working words, such that every proper-loss
query `(B, y)` recovers `σ^B_s(y)` for both `s ∈ B` (matching `H.ExitTailMem B _ y`)
in `≤ 60 * OracleContract.L H.vertexCount + 3` (`O(L)`) word operations and `6`
injective sealed base reads. -/
theorem compressed_exit_summaries
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat)
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    {bits endpoints : Nat}
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (wFit : Width bits (max r.out.tables.next endpoints))
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits) :
    let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
      hRank wFit hLayout
    let S := actualCompactArraySchedule r increasing covers
      (g := C.built.bundle.g0) C.built.bundle.full C.built.bundle.ch
    let inp := actualInput C.built.bundle C.wFit.tags C.built.bank C.hLayout entryRank
    let basesStatic := toStaticSlots C.built.bases
    let sweepWork := ListWork.total (List.ofFn S.vertex) (fun y =>
      let cb := countedBase inp basesStatic y
      let instCalls :=
        match S.mapSlot.read y with
        | none => 0
        | some i =>
          install_count inp
            (actualLookup C.built.bundle i).1
            (actualLookup C.built.bundle i).2
      19 + cb.labelledOccurrenceVisits +
        (60 * OracleContract.L H.vertexCount + 3) * (cb.fusedCalls + instCalls))
    let totalBuildSteps :=
      ForestIncomingRaw.rawTotal H (ForestIncomingRaw.prepare H) +
        C.built.seedWrites + C.built.sweepWrites + sweepWork + C.sealed.size
    -- 1. Build time `O((n_H + m_H) L)` and `O(n_H + m_H)` working/retained words
    totalBuildSteps ≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount ∧
    C.retainedWords ≤ 25 * H.vertexCount + 19 ∧
    C.retainedWords ≤ 44 * H.vertexCount + 19 ∧
    C.sealed.size = 6 * H.vertexCount ∧
    -- 2. Exact base, edge-chronology, and online `O(L)` query evaluation
    (∀ y, (countedBase inp basesStatic y).values = inp.base basesStatic y) ∧
    (∀ (B : CutPair H) (y : Vertex H), H.ProperLoss B y →
      ∃ (u d c : Nat),
        u < C.built.bundle.F.size ∧
        (let raw := SealedPriorBase.run C.built.bank.mem
            (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
            C.wFit.tags C.sealed C.sealView y u d
          if B.fst < B.snd then raw else swapTwo raw) = C.built.model.ref B y ∧
        1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount + 3 ∧
        C.sealView.start + (6 * y.val + 5) < C.sealed.size ∧
        Function.Injective (fun k : Fin 6 => C.sealView.start + (6 * y.val + k.val)) ∧
        ∀ (j : Fin 2) (l h : Nat),
          BuiltExit.Test l h (Two.get (C.built.model.ref B y) j) ↔
            C.built.model.Fits l h B (C.built.model.endpoint B j) y) := by
  intro C S inp basesStatic sweepWork totalBuildSteps
  obtain ⟨hBaseEq, _, _, hTotal, _, hRet, hRetSlack⟩ :=
    actualBuildWork_bound C increasing covers
  refine ⟨hTotal, hRet, hRetSlack, C.sealed_size, hBaseEq, ?_⟩
  intro B y hProp
  obtain ⟨u, d, c, huLt, hEval, hReadLt, hReadInj, _, _, _, hL, _⟩ :=
    query_exact C B y hProp
  refine ⟨u, d, c, huLt, hEval, hL, hReadLt, hReadInj, ?_⟩
  intro j l h
  exact C.built.model.ref_test B y j l h

/-- Vacuous base case for Lemma 5.1 when `H.vertexCount < 3`: no `CutPair H` exists,
so no proper-loss exit summary query can occur. -/
theorem compressed_exit_summaries_small {H : LabelledQuotient}
    (hSmall : H.vertexCount < 3) (B : CutPair H) (y : Vertex H) :
    ¬ H.ProperLoss B y :=
  small_quotient_vacuous hSmall B y

/-- **Paper B v1.2 correspondence for Lemma 5.1.**
Preserves the v1.2 cubic bounds (`O((n_H + m_H) L^3)` build, `O(L^3)` query) from the exact
same executable contract `ActualSealedContract`, together with the original-tree LCA
equivalence (`ExitLCABridge.DFSIndex.dominatorLCA_eq_extrema`) showing that storing min/max
DFS preorder ranks recovers the exact common-dominator / LCA semantics of the exit tail set. -/
theorem compressed_exit_summaries_v12
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (flat : H.IsFlat)
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    {bits endpoints : Nat}
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (wFit : Width bits (max r.out.tables.next endpoints))
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits) :
    let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
      hRank wFit hLayout
    let S := actualCompactArraySchedule r increasing covers
      (g := C.built.bundle.g0) C.built.bundle.full C.built.bundle.ch
    let inp := actualInput C.built.bundle C.wFit.tags C.built.bank C.hLayout entryRank
    let basesStatic := toStaticSlots C.built.bases
    let sweepWork := ListWork.total (List.ofFn S.vertex) (fun y =>
      let cb := countedBase inp basesStatic y
      let instCalls :=
        match S.mapSlot.read y with
        | none => 0
        | some i =>
          install_count inp
            (actualLookup C.built.bundle i).1
            (actualLookup C.built.bundle i).2
      19 + cb.labelledOccurrenceVisits +
        (60 * OracleContract.L H.vertexCount + 3) * (cb.fusedCalls + instCalls))
    let totalBuildSteps :=
      ForestIncomingRaw.rawTotal H (ForestIncomingRaw.prepare H) +
        C.built.seedWrites + C.built.sweepWrites + sweepWork + C.sealed.size
    totalBuildSteps ≤ 209 * (H.vertexCount + H.arcCount) * OracleContract.L H.vertexCount ^ 3 ∧
    C.retainedWords ≤ 44 * H.vertexCount + 19 ∧
    (∀ (B : CutPair H) (y : Vertex H), H.ProperLoss B y →
      ∃ (u d c : Nat),
        u < C.built.bundle.F.size ∧
        (let raw := SealedPriorBase.run C.built.bank.mem
            (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
            C.wFit.tags C.sealed C.sealView y u d
          if B.fst < B.snd then raw else swapTwo raw) = C.built.model.ref B y ∧
        1 + c + 1 ≤ 60 * OracleContract.L H.vertexCount ^ 3 + 3) ∧
    (∀ {g : Digraph} {rv : Fin g.vertexCount} (hacyc : g.IsAcyclic)
      (I : PaperB.Digraph.ExitLCABridge.DFSIndex g rv)
      {vs : List (Fin g.vertexCount)} {a b : Fin g.vertexCount}
      (hne : vs ≠ [])
      (hr : PaperB.Digraph.ExitLCABridge.AllReach rv vs)
      (ha : a ∈ vs) (hb : b ∈ vs),
      (I.rank a).val ≤ (I.rank b).val →
      I.record vs = .span (I.rank a).val (I.rank b).val →
      g.dominatorLCA rv vs hacyc hne hr =
        g.dominatorLCA rv [a, b] hacyc (by simp)
          (PaperB.Digraph.ExitLCABridge.pairReach (hr a ha) (hr b hb))) := by
  intro C S inp basesStatic sweepWork totalBuildSteps
  obtain ⟨_, _, _, _, hV12, _, hRetSlack⟩ := actualBuildWork_bound C increasing covers
  refine ⟨hV12, hRetSlack, ?_, ?_⟩
  · intro B y hProp
    obtain ⟨u, d, c, huLt, hEval, _, _, _, _, _, _, hV12Q⟩ := query_exact C B y hProp
    exact ⟨u, d, c, huLt, hEval, hV12Q⟩
  · intro g rv hacyc I vs a b hne hr ha hb hord hs
    exact I.dominatorLCA_eq_extrema hacyc hne hr ha hb hord hs

/-- Non-vacuity witness for Lemma 5.1: re-exports `ExitActualContract.nonvacuous_diamond_contract`,
confirming inhabited `LiveStoreOK`, `ActualSealedContract`, `sealed.size = 24`,
`retainedWords ≤ 195`, and exact `SealedPriorBase.run` query equality in `O(L)` steps
on a 4-vertex flat acyclic diamond quotient. -/
abbrev compressed_exit_summaries_nonvacuous :=
  @ExitActualContract.nonvacuous_diamond_contract

end PaperB
