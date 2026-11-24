module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalLoop
public import PaperB.RamExitSummarySweepRows
public import PaperB.RamExitSummarySweepAArc

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 350000

/-!
EX5.1 / EX5.2 Word-RAM exit-summary builder (`PaperB/RamExitSummaryBuild.lean`).

Contains:
1. Mathematical bridges connecting the Word-RAM Stage 4 computations (`Step 4A` incoming-arc
   base fold, `Step 4B` endpoint-lift + `Stored.parentOnly`/`Stored.skew`) to
   `ActualSealedContract`, `DecodedOccupied`, `LiveStoreOK`, `BaseBound`, and
   `SealedPriorBase.Placed`.
2. `stage4Phase` (`run_stage4`), composed via `PhaseChain` & `run_linkNonEmpty` with
   `setupPhases` into the single fixed 15-register Word-RAM program `exitSummaryBuildProgram`,
   proving `run_exitSummaryBuild`.
-/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.BuiltExit (vjoin zero Test get_vjoin test_zero)
open PaperB.ExitSummary (endpointsInside_span_iff)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.ArcParents
open PaperB.ForestHead (Vertex)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open PaperB.RetainedProperLoss (encodeBackPair encodeBackPair_eq_iff ofOrderedReader)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalDepthColumn
open PaperB.Exit.OrderedReaderResult
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)

/-! Execution of one incoming-arc update in the prior-base sweep. -/

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4A_arc_spec {code : Program DomL} {input : Input DomL}
    (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code loopPc (step4ALoopInstrs (bits := bits) loopPc h100))
    (hSz : loopPc + 406 < code.size)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hFitRank : ∀ x : Fin H.origVertexCount, entryRank x < 2 ^ bits)
    {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F ref live)
    (hFSize : F.size = r.out.tables.next)
    (B := buildActualSweepBundle H flat increasing covers rankArc r)
    (hFEq : F = B.F)
    (ownerSlot : Nat) (hOwnPos : 0 < ownerSlot) (hOwnLt : ownerSlot < r.out.tables.next)
    (Bcut : CutPair H) (baseFn : Vertex H → Values)
    (arcPtr arcEnd e : Nat) (heLt : e < H.arcCount)
    (hPtrLt : arcPtr < arcEnd) (hEndLe : arcEnd ≤ H.arcCount)
    (st : State DomL) (hpc : st.pc = loopPc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hPtr : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr]?).map Fin.val = some arcPtr)
    (hEnd : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcEnd]?).map Fin.val = some arcEnd)
    (hArcId : (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + arcPtr]?).map Fin.val = some e)
    (hBFst : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48]?).map Fin.val = some Bcut.fst.val)
    (hBSnd : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 49]?).map Fin.val = some Bcut.snd.val)
    (hOwnEn : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 50]?).map Fin.val =
      some (r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)))
    (hOwnSt : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 51]?).map Fin.val =
      some (r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)))
    (hOwnDep : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 52]?).map Fin.val =
      some (F.depthOf ownerSlot))
    (acc : Values)
    (hAcc : ValuesWordsAt st.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0) acc)
    (hDepth : ∀ w : Fin r.out.tables.next, (st.data[w.val]?).map Fin.val = some (F.depthOf w.val))
    (hStored : ∀ w : Fin r.out.tables.next, live w.val →
      (st.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
      (st.data[storedBase r.out.tables.next + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 2) (ref w.val).parentMap ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 10) (ref w.val).jumpMap)
    (hBaseAtU : let u := (rawOccurrence H ⟨e, heLt⟩).1
      ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * u.val) (baseFn u))
    (hLiveAtV : let u := (rawOccurrence H ⟨e, heLt⟩).1
      let v := (selectors (orderedConfig p large) r.out).label u
      let hvLt : v < r.out.tables.next := B.G.size_eq ▸ B.E.label_lt u True.intro
      u.val ≠ Bcut.fst.val → u.val ≠ Bcut.snd.val → 0 < v →
      r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) ≤
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) →
      r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) <
        r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) →
      live v) :
    ∃ k t, k ≤ 700 * OracleContract.L H.vertexCount ∧
      Steps code input k st t ∧ t.pc = loopPc ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr]?).map Fin.val =
        some (arcPtr + 1) ∧
      ValuesWordsAt t.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0)
        (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) ∧
      (∀ j, (j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr ∨
          (metaArrBase H.vertexCount H.arcCount r.out.tables.next + (mIdxArcPtr + 1) ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEvalU) ∨
          (metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + 53) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 55 ≤ j) →
        t.data[j]? = st.data[j]?) := by
  let u := (rawOccurrence H ⟨e, heLt⟩).1
  by_cases hEndPoint : u.val = Bcut.fst.val ∨ u.val = Bcut.snd.val
  · exact step4A_arc_direct_spec (input := input) loopPc h100 hPl hSz flat increasing covers
      rankArc hIn hWork (F := F) (ref := ref) ownerSlot Bcut baseFn arcPtr arcEnd e heLt hPtrLt hEndLe
      st hpc hMeta hPtr hEnd hArcId hBFst hBSnd acc hAcc hEndPoint
  · exact step4A_arc_nonendpoint_spec loopPc h100 hPl hSz flat increasing covers rankArc
      hIn hWork hFitRank ok hFSize B hFEq ownerSlot hOwnPos hOwnLt Bcut baseFn arcPtr arcEnd e
      heLt hPtrLt hEndLe st hpc hMeta hPtr hEnd hArcId hBFst hBSnd hOwnEn hOwnSt hOwnDep acc
      hAcc hDepth hStored hBaseAtU hLiveAtV
      ⟨fun h => hEndPoint (.inl h), fun h => hEndPoint (.inr h)⟩

end PaperB.RamProgram.ExitSummaryBuild
