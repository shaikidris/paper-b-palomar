module

public import PaperB.RamOracleQueryParts
public import PaperB.OracleSealedIndexLayout
public import PaperB.SealedQueryRegisters
public import PaperB.ActualOnlineOracle
public import PaperB.ExitActualContract

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.3 Complete Sealed Word-RAM Query ROM (`oracleQueryProgram` / `oracleQueryPhase`)
and Exact Correctness & `O(L)` Work / Footprint Bridge (`oracleQueryProgram_spec`).

1. `ValidSealedOracleIndex`: sealed array invariant over `OracleSealedIndexLayout`
   (`StaticHeaderSpec` + global static tree/DFS/child tables + per-owner descriptors).
   Non-vacuous: uses `ExitMap.JumpMapRoute.StoredExit.Occupied`,
   `ExitMap.SealedPriorBase.Placed`, and the direct `foldStored` `≤ 3 * ceilLog2 (n + 2)`
   step bound (with an `ofLiveStoreOK` builder via `ExitActualInputsBuild.live_foldStored_steps_le`;
   never requires `JumpMapRoute.StoreOK`).
2. `oracleQueryCode` / `oracleQueryProgram` / `oracleQueryPhase`:
   One fixed `SealedQueryR.Phase bits 16` program (`workCap = queryWorkCap = 32`),
   independent of `(g, r, F, t)`, implementing all branches of `OracleRuntime.route`
   and `OracleRuntime.answer` using only `I.words` (read-only) and local scratch `data[0..31]`.
3. `oracleQueryProgram_spec`:
   For every `(g, r, acyc)`, valid sealed index `I`, failure set `F`, and target `t`,
   `observe` halts cleanly with `o.operations ≤ 1200 * OracleContract.L g.vertexCount`,
   `o.words = I.size + queryWorkCap + 16`, and `o.answer = true ↔ g.ReachableAvoiding F r t`.
-/

namespace PaperB.RamOracleQuery

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap zero)
open PaperB.RamProgram
open PaperB.RamOracleQueryParts
open PaperB.OracleSealedIndexLayout
open PaperB.SealedQuery
open PaperB.SealedQueryR
open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ForestHead
open PaperB.RetainedProperLoss
open PaperB.ForestSlimIndex
open PaperB.DenseQuotientRows
open PaperB.DenseOriginalQuotient
open PaperB.EX16Assembly
open PaperB.EX44
open PaperB.EX44.RetainedRouteProof
open PaperB.EX44.ActualOnlineOracle
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.SealedPriorBase
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open _root_.EX24.PreparedSweep

/-! ### 1. Sealed Index Specification (`ValidSealedOracleIndex`, Non-Vacuous) -/

section SealedSpec

/-- Non-vacuous hop-step bound obtained from `ExitActualContract.LiveStoreOK` and
`ExitActualInputsBuild.DecodedOccupied`. Never requires `JumpMapRoute.StoreOK`. -/
theorem foldStored_steps_le_of_live {bits endpoints n : Nat} {mem : Array (Word bits)}
    {R : Region bits mem.size} {F : JumpForest} {ref : ExitMap.CheckedFold.Store}
    {w : Width bits (max R.slots endpoints)}
    (live : Nat → Prop)
    (dec : DecodedOccupied mem R F ref w.tags live)
    (liveOK : ExitActualContract.LiveStoreOK F ref live)
    {u : Nat} (huLive : live u) (hn : F.numInserted ≤ n) (d : Nat) :
    (foldStored mem R w.tags u d).steps ≤ 3 * ceilLog2 (n + 2) :=
  ExitActualContract.live_foldStored_steps_le dec liveOK huLive hn d

/-- Per-owner sealed quotient & exit-map descriptor record for owner `d : Fin q.count`.
For `Dq.vertexCount < 3`, no `CutPair Dq` exists so only the 10-word descriptor header is needed.
For `3 ≤ Dq.vertexCount`, the descriptor points to valid `WordColumns`, `FlatPairDictionary`,
`Occupied` exit bank, and `SealedPriorBase` slices satisfying `≤ 3 * ceilLog2 (n + 2)` hops. -/
structure SealedOwnerRecord
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (I : Array (Word bits))
    {n qCount : Nat} (Hdr : StaticHeaderSpec I n qCount)
    (d : Fin q.count) where
  nD : Nat
  nD_eq : nD = (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
  dictPtr : Nat
  backFstPtr : Nat
  backSndPtr : Nat
  labelsPtr : Nat
  fEntryPtr : Nat
  fStopPtr : Nat
  exitDepthPtr : Nat
  exitStoredPtr : Nat
  exitPriorPtr : Nat
  descBase : Nat
  descBase_val : descBase = Hdr.ownerDescBase + ownerDescStride * d.val
  descFits : descBase + ownerDescStride ≤ I.size
  hDescN : (I[descBase + descN]?).map Fin.val = some nD
  hDescDict : (I[descBase + descDict]?).map Fin.val = some dictPtr
  hDescBackFst : (I[descBase + descBackFst]?).map Fin.val = some backFstPtr
  hDescBackSnd : (I[descBase + descBackSnd]?).map Fin.val = some backSndPtr
  hDescLabels : (I[descBase + descLabels]?).map Fin.val = some labelsPtr
  hDescFEntry : (I[descBase + descFEntry]?).map Fin.val = some fEntryPtr
  hDescFStop : (I[descBase + descFStop]?).map Fin.val = some fStopPtr
  hDescExitDepth : (I[descBase + descExitDepth]?).map Fin.val = some exitDepthPtr
  hDescExitStored : (I[descBase + descExitStored]?).map Fin.val = some exitStoredPtr
  hDescExitPrior : (I[descBase + descExitPrior]?).map Fin.val = some exitPriorPtr
  large_spec :
    let Dq := denseQuotient progress injRank q originalRows hRows rows childOK d
    ∀ large : 3 ≤ Dq.vertexCount,
      ∃ (pD : ForestDictionary.Rows Dq) (dataD : Array (Vertex Dq))
        (sizeD : dataD.size = Dq.vertexCount) (rankD : Vertex Dq → Nat)
        (ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large)
        (wCols : WordColumns bits)
        (endpoints : Nat) (R : Region bits I.size) (F : JumpForest)
        (ref : Nat → ExitMap.CheckedFold.Stored) (wFit : Width bits (max R.slots endpoints))
        (_ok : Occupied I R F ref wFit)
        (prior : Array (Option Values)) (hb : BaseBound (max R.slots endpoints) prior)
        (B : BaseView prior.size I.size) (_hPlaced : Placed wFit prior hb I B),
        SliceAt I dictPtr wCols.dictionary ∧
        FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordRes) ∧
        SliceAt I backFstPtr wCols.back.tagAndFirst ∧
        SliceAt I backSndPtr wCols.back.second ∧
        SliceAt I labelsPtr wCols.labels ∧
        SliceAt I fEntryPtr wCols.entry ∧
        SliceAt I fStopPtr wCols.stop ∧
        wCols.labels.size = Dq.vertexCount ∧
        wCols.entry.size = wCols.stop.size ∧
        wCols.back.tagAndFirst.size = wCols.back.second.size ∧
        (∀ a v, wCols.known a v = (ofOrderedReader ordRes).known a v) ∧
        (∀ j (P : CutPair Dq),
          wCols.back.read j = some (encodeBackPair (some P)) ↔
            (ofOrderedReader ordRes).back[j]? = some (some P)) ∧
        (∀ v : Vertex Dq, (orderedConfig pD large).vertexIndex v = v.val) ∧
        (∀ y : Fin Dq.vertexCount,
          wCols.labelAt y.val < F.size ∧ wCols.labelAt y.val < wCols.entry.size) ∧
        (∀ (P : CutPair Dq), P.fst < P.snd →
          ∀ aNode : Nat, checkedHit ordRes P = some aNode →
            aNode < wCols.entry.size ∧ aNode < wCols.stop.size ∧
            aNode < F.size ∧ aNode < wCols.back.tagAndFirst.size ∧
            aNode < wCols.back.second.size) ∧
        prior.size = Dq.vertexCount ∧
        R.base.val = exitStoredPtr ∧
        B.start = exitPriorPtr ∧
        (∀ x : Fin R.slots, (R.depthAddr x).val = exitDepthPtr + x.val) ∧
        (∀ (P : CutPair Dq), P.fst < P.snd →
          ∀ aNode : Nat, checkedHit ordRes P = some aNode →
            ∀ y : Vertex Dq, Dq.ProperLoss P y →
              let u := wCols.labelAt y.val
              let dDepth := depthAt I R aNode
              (foldStored I R wFit.tags u dDepth).steps ≤ 3 * ceilLog2 (g.vertexCount + 2) ∧
              ∀ hPrior : y.val < prior.size,
                (PriorBase.run I R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x0 =
                  ExitSummary.summary
                    ((lemma22ExitTails Dq P P.fst y).map
                      (fun v => (OriginalEntryInverse.originalRank q v).getD 0)) ∧
                (PriorBase.run I R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x1 =
                  ExitSummary.summary
                    ((lemma22ExitTails Dq P P.snd y).map
                      (fun v => (OriginalEntryInverse.originalRank q v).getD 0)))

/-- Complete sealed oracle index specification over `OracleSealedIndexLayout`. -/
def ValidSealedOracleIndex {bits : Nat} (g : Digraph) (r : Fin g.vertexCount)
    (I : Array (Word bits)) : Prop :=
  TagsFit bits ∧
  queryWorkCap ≤ 2 ^ bits ∧
  ∃ (rank : Fin g.vertexCount → Nat)
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    (buckets : ForestLayout.ChildLists q.count)
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (inv : OriginalEntryInverse.Index q)
    (Hdr : StaticHeaderSpec I g.vertexCount q.count),
      q.input.root.val = 0 ∧
      q.reader.tables.size q.reader.tables.root ≤ q.count ∧
      (∀ d : Fin q.count,
        (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d ∧
        StaticChildLookup.Valid (q.reader.ranges.read d)) ∧
      NatSliceAt I Hdr.headBase q.count
        (fun d => if hd : d < q.count then (q.reader.tables.head ⟨d, hd⟩).val else 0) ∧
      NatSliceAt I Hdr.domParentBase q.count
        (fun d => if hd : d < q.count then (q.reader.tables.parent ⟨d, hd⟩).val else 0) ∧
      NatSliceAt I Hdr.domDepthBase q.count
        (fun d => if hd : d < q.count then q.reader.tables.depth ⟨d, hd⟩ else 0) ∧
      NatSliceAt I Hdr.origToDenseBase g.vertexCount
        (fun v => if hv : v < g.vertexCount then
          match q.ids.find ⟨v, hv⟩ with | none => 0 | some d => d.val + 1 else 0) ∧
      NatSliceAt I Hdr.denseToOrigBase q.count
        (fun d => if hd : d < q.count then (q.ids.originals.read ⟨d, hd⟩).val else 0) ∧
      NatSliceAt I Hdr.entryBase q.count
        (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0) ∧
      NatSliceAt I Hdr.stopBase q.count
        (fun d => if hd : d < q.count then q.reader.stop ⟨d, hd⟩ else 0) ∧
      NatSliceAt I Hdr.origOfEntryBase q.count
        (fun rk => if hr : rk < q.count then (inv.slots.read ⟨rk, hr⟩).val else 0) ∧
      (∃ cStart : Fin (q.count + 1) → Nat,
        cStart ⟨0, Nat.zero_lt_succ _⟩ = 0 ∧
        (∀ d : Fin q.count,
          cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
            cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + (q.reader.ranges.read d).size) ∧
        NatSliceAt I Hdr.childStartBase (q.count + 1)
          (fun idx => if hi : idx < q.count + 1 then cStart ⟨idx, hi⟩ else 0) ∧
        (∀ (d : Fin q.count) (j : Nat) (hj : j < (q.reader.ranges.read d).size),
          let pos := cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j
          let ch := (q.reader.ranges.read d)[j]'hj
          pos < q.count ∧
          (I[Hdr.childEntriesBase + pos]?).map Fin.val = some ch.entry ∧
          (I[Hdr.childStopsBase + pos]?).map Fin.val = some ch.stop ∧
          (I[Hdr.childIdsBase + pos]?).map Fin.val = some ch.id.val)) ∧
      (∀ d : Fin q.count,
        Nonempty (SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d))

abbrev SealedIndexValid {bits : Nat} (g : Digraph) (r : Fin g.vertexCount)
    (I : Array (Word bits)) : Prop :=
  ValidSealedOracleIndex g r I

theorem ValidSealedOracleIndex.index_size_lt {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hVal : ValidSealedOracleIndex g r I) : I.size < 2 ^ bits := by
  rcases hVal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, Hdr, _⟩
  have ht := Hdr.hTotal
  cases h : I[hdrTotalWords]? with
  | none => simp [h] at ht
  | some w =>
    simp only [h, Option.map_some, Option.some.injEq] at ht
    rw [← ht]; exact w.isLt

end SealedSpec

/-! ### 2. Fixed Word-RAM Query Bytecode (`oracleQueryCode` / `oracleQueryPhase`) -/

section FixedProgram

private def zeroW (bits : Nat) : Word bits := zero bits
private def oneW {bits : Nat} (hTag : TagsFit bits) : Word bits :=
  ⟨1, Nat.lt_trans (by decide : 1 < 2) hTag⟩
private def twoW {bits : Nat} (hTag : TagsFit bits) : Word bits :=
  ⟨2, hTag⟩
private def slotW {bits : Nat} (hWork : queryWorkCap ≤ 2 ^ bits)
    (k : Nat) (hk : k < queryWorkCap) : Word bits :=
  ⟨k, Nat.lt_of_lt_of_le hk hWork⟩
private def hdrW {bits : Nat} (hWork : queryWorkCap ≤ 2 ^ bits)
    (k : Nat) (hk : k < oracleHeaderSize) : Word bits :=
  slotW hWork k (Nat.lt_trans hk (by decide : oracleHeaderSize < queryWorkCap))
private def descW {bits : Nat} (hWork : queryWorkCap ≤ 2 ^ bits)
    (k : Nat) (hk : k < ownerDescStride) : Word bits :=
  slotW hWork k (Nat.lt_trans hk (by decide : ownerDescStride < queryWorkCap))

-- Scratch slot offsets (`< 32 = queryWorkCap`)
private abbrev slTag : Nat := 0
private abbrev slFail0 : Nat := 1
private abbrev slFail1 : Nat := 2
private abbrev slTarget : Nat := 3
private abbrev slADense : Nat := 4
private abbrev slBDense : Nat := 5
private abbrev slXDense : Nat := 6
private abbrev slD : Nat := 7
private abbrev slUDense : Nat := 8
private abbrev slULocal : Nat := 9
private abbrev slVDense : Nat := 10
private abbrev slVLocal : Nat := 11
private abbrev slYDense : Nat := 12
private abbrev slYLocal : Nat := 13
private abbrev slDescBase : Nat := 14
private abbrev slSwapped : Nat := 15
private abbrev slHitNode : Nat := 16
private abbrev slX0Tag : Nat := 17
private abbrev slX0Lo : Nat := 18
private abbrev slX0Hi : Nat := 19
private abbrev slX1Tag : Nat := 20
private abbrev slX1Lo : Nat := 21
private abbrev slX1Hi : Nat := 22
private abbrev slKey0 : Nat := 23
private abbrev slKey1 : Nat := 24

private abbrev codeLayout (bits cap : Nat) (hCap : cap ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) :
    Layout bits :=
  ⟨16, cap, queryWorkCap, hCap, hWork⟩

/-- Fixed size of `ExitEval.exitEvalProgram`. -/
def exitEvalSize {bits cap : Nat} (hCap : cap ≤ 2 ^ bits) (hTag : TagsFit bits) : Nat :=
  (ExitEval.exitEvalProgram (bits := bits) (inputCap := cap) (fits := hCap) hTag).size

-- Block PC anchors (`oracleQueryCode`)
private abbrev pc0 : Nat := 0
private abbrev pc1 : Nat := 24
private abbrev pc2 : Nat := 51
private abbrev pc3 : Nat := 117
private abbrev pc4 : Nat := 219
private abbrev pc5a : Nat := 474
private abbrev pc5b : Nat := 674
private def pc6 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits) (hTag : TagsFit bits) : Nat :=
  848 + exitEvalSize hCap hTag
private def okPC {bits cap : Nat} (hCap : cap ≤ 2 ^ bits) (hTag : TagsFit bits) : Nat :=
  pc6 hCap hTag + 20
private def failPC {bits cap : Nat} (hCap : cap ≤ 2 ^ bits) (hTag : TagsFit bits) : Nat :=
  pc6 hCap hTag + 22

-- Block 0 (`size = 24`, at `pc0 = 0`): save ABI `r0..r3`, translate target `x`, dispatch on `tag`.
private def blkSaveAndTarget {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  #[.imm 15 (slotW hWork slTag (by decide)), .storeData 15 0,
    .imm 15 (slotW hWork slFail0 (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slFail1 (by decide)), .storeData 15 2,
    .imm 15 (slotW hWork slTarget (by decide)), .storeData 15 3,
    .imm 0 (hdrW hWork hdrOrigToDense (by decide)),
    .imm 6 (oneW hTag)] ++
  liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits cap hCap).registerCount = 16))
    10 14 (sealedTranslation hCap) ++
  #[.imm 6 (oneW hTag),
    .branchLt 5 6 (failPC hCap hTag) 16,
    .sub 1 5 6,
    .imm 15 (slotW hWork slXDense (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slTag (by decide)), .loadData 0 15,
    .branchLt 0 6 (okPC hCap hTag) 22,
    .imm 7 (twoW hTag),
    .branchLt 0 7 24 pc2]

@[simp] private theorem blkSaveAndTarget_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkSaveAndTarget hCap hWork hTag).size = 24 := by
  simp [blkSaveAndTarget, liftMap, sealedTranslation]

-- Block 1 (`size = 27`, at `pc1 = 24`): `tag = 1` (`FailureSet.one a`).
private def blkTag1 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  #[.imm 15 (slotW hWork slFail0 (by decide)), .loadData 3 15,
    .imm 0 (hdrW hWork hdrOrigToDense (by decide))] ++
  liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits cap hCap).registerCount = 16))
    (pc1 + 3) (pc1 + 7) (sealedTranslation hCap) ++
  #[.imm 6 (oneW hTag),
    .branchLt 5 6 (okPC hCap hTag) (pc1 + 9),
    .sub 1 5 6,
    .branchLt 1 6 (failPC hCap hTag) (pc1 + 11),
    .imm 15 (slotW hWork slADense (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc1 + 15) (pc1 + 22)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (failPC hCap hTag) (pc1 + 24),
    .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
    .goto (pc6 hCap hTag)]

@[simp] private theorem blkTag1_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkTag1 hCap hWork hTag).size = 27 := by
  simp [blkTag1, liftMap, sealedTranslation, PairGuard.rom]

-- Block 2 (`size = 66`, at `pc2 = 51`): `tag = 2` (`FailureSet.two a b`).
private def blkTag2 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  #[.imm 15 (slotW hWork slFail0 (by decide)), .loadData 3 15,
    .imm 0 (hdrW hWork hdrOrigToDense (by decide))] ++
  liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits cap hCap).registerCount = 16))
    (pc2 + 3) (pc2 + 7) (sealedTranslation hCap) ++
  #[.imm 6 (oneW hTag), .imm 7 (twoW hTag),
    .imm 15 (slotW hWork slADense (by decide)), .storeData 15 5,
    .branchLt 5 6 (pc2 + 25) (pc2 + 12),
    .branchLt 5 7 (failPC hCap hTag) (pc2 + 13),
    .sub 1 5 6,
    .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc2 + 16) (pc2 + 23)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (failPC hCap hTag) (pc2 + 25),
    .imm 15 (slotW hWork slFail1 (by decide)), .loadData 3 15,
    .imm 0 (hdrW hWork hdrOrigToDense (by decide))] ++
  liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits cap hCap).registerCount = 16))
    (pc2 + 28) (pc2 + 32) (sealedTranslation hCap) ++
  #[.imm 6 (oneW hTag), .imm 7 (twoW hTag),
    .imm 15 (slotW hWork slBDense (by decide)), .storeData 15 5,
    .branchLt 5 6 (pc2 + 50) (pc2 + 37),
    .branchLt 5 7 (failPC hCap hTag) (pc2 + 38),
    .sub 1 5 6,
    .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc2 + 41) (pc2 + 48)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (failPC hCap hTag) (pc2 + 50),
    .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 2 15,
    .imm 6 (oneW hTag),
    .branchLt 1 6 (pc2 + 56) (pc2 + 59),
    .branchLt 2 6 (okPC hCap hTag) (pc2 + 57),
    .sub 1 2 6,
    .goto (pc6 hCap hTag),
    .sub 1 1 6,
    .imm 15 (slotW hWork slADense (by decide)), .storeData 15 1,
    .branchLt 2 6 (pc6 hCap hTag) (pc2 + 63),
    .sub 2 2 6,
    .imm 15 (slotW hWork slBDense (by decide)), .storeData 15 2]

@[simp] private theorem blkTag2_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkTag2 hCap hWork hTag).size = 66 := by
  simp [blkTag2, liftMap, sealedTranslation, PairGuard.rom]

-- Block 3 (`size = 102`, at `pc3 = 117`): `routePair` (`ancestor a b`, `ancestor b a`, `EX53 LCA`).
private def blkRoutePair {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  #[.imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 2 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc3 + 4) (pc3 + 20) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (pc3 + 25) (pc3 + 22),
    .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
    .goto (pc6 hCap hTag),
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slADense (by decide)), .loadData 2 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc3 + 29) (pc3 + 45) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (pc3 + 50) (pc3 + 47),
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
    .goto (pc6 hCap hTag),
    .imm 15 (slotW hWork slADense (by decide)), .loadData 0 15,
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
    .imm 2 (hdrW hWork hdrHead (by decide)),
    .imm 3 (hdrW hWork hdrDomParent (by decide)),
    .imm 4 (hdrW hWork hdrDomDepth (by decide)),
    .imm 5 (zeroW bits), .imm 6 (zeroW bits), .imm 7 (zeroW bits),
    .imm 8 (zeroW bits), .imm 9 (zeroW bits), .imm 10 (zeroW bits),
    .imm 11 (zeroW bits), .imm 12 (zeroW bits), .imm 13 (zeroW bits),
    .imm 14 (zeroW bits), .imm 15 (zeroW bits)] ++
  liftMap (ρ16 rfl (rfl : (EX53.layout bits cap hCap).registerCount = 16))
    (pc3 + 68) (pc3 + 100) (EX53.program hCap) ++
  #[.imm 15 (slotW hWork slD (by decide)), .storeData 15 0]

@[simp] private theorem blkRoutePair_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkRoutePair hCap hWork hTag).size = 102 := by
  unfold blkRoutePair
  have hLca : (liftMap (L := codeLayout bits cap hCap hWork)
      (ρ16 rfl (rfl : (EX53.layout bits cap hCap).registerCount = 16))
      (pc3 + 68) (pc3 + 100) (EX53.program hCap)).size = 32 := by
    simp [liftMap]; rfl
  have hA1 := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc3 + 4) (pc3 + 20)
  have hA2 := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc3 + 29) (pc3 + 45)
  simp only [Array.size_append]
  rw [hA1, hA2, hLca]
  simp

-- Block 4 (`size = 255`, at `pc4 = 219`): `routeBlocks` (`child(d,a)`, `child(d,b)`, `child(d,x)` + equality guards).
private def blkRouteBlocks {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  #[.imm 15 (slotW hWork slD (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slADense (by decide)), .loadData 2 15] ++
  childSearchBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 4) (pc4 + 64) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (failPC hCap hTag) (pc4 + 66),
    .imm 15 (slotW hWork slUDense (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slULocal (by decide)), .storeData 15 2,
    .imm 15 (slotW hWork slD (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 2 15] ++
  childSearchBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 74) (pc4 + 134) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (failPC hCap hTag) (pc4 + 136),
    .imm 15 (slotW hWork slVDense (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slVLocal (by decide)), .storeData 15 2,
    .imm 15 (slotW hWork slD (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slXDense (by decide)), .loadData 2 15] ++
  childSearchBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 144) (pc4 + 204) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (pc4 + 206),
    .imm 15 (slotW hWork slYDense (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slYLocal (by decide)), .storeData 15 2,
    .imm 15 (slotW hWork slYDense (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slUDense (by decide)), .loadData 3 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc4 + 214) (pc4 + 221)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (pc4 + 223) (pc4 + 226),
    .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
    .goto (pc6 hCap hTag),
    .imm 15 (slotW hWork slYDense (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slVDense (by decide)), .loadData 3 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc4 + 230) (pc4 + 237)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (pc4 + 239) (pc4 + 242),
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
    .goto (pc6 hCap hTag),
    .imm 15 (slotW hWork slULocal (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slVLocal (by decide)), .loadData 3 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc4 + 246) (pc4 + 253)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) pc5a]

@[simp] private theorem blkRouteBlocks_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkRouteBlocks hCap hWork hTag).size = 255 := by
  unfold blkRouteBlocks
  have hC1 := childSearchBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 4) (pc4 + 64)
  have hC2 := childSearchBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 74) (pc4 + 134)
  have hC3 := childSearchBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 144) (pc4 + 204)
  simp only [Array.size_append, liftMap, Array.size_map, PairGuard.rom]
  rw [hC1, hC2, hC3]
  simp

-- Block 5A (`size = 200`, at `pc5a = 474`): owner descriptor, pair lookup, back-key check, known-node check.
private def blkPairAndKnown {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  have hOne : 1 < 2 ^ bits := Nat.lt_trans (by decide : 1 < 2) hTag
  #[.imm 15 (hdrW hWork hdrOwnerDesc (by decide)), .loadInput 2 15,
    .imm 15 (slotW hWork slD (by decide)), .loadData 3 15,
    .add 4 3 3, .add 5 4 4, .add 5 5 5, .add 4 4 5,
    .add 14 2 4,
    .imm 15 (slotW hWork slDescBase (by decide)), .storeData 15 14,
    .imm 15 (slotW hWork slULocal (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slVLocal (by decide)), .loadData 2 15,
    .branchLt 1 2 (pc5a + 16) (pc5a + 20),
    .imm 3 (zeroW bits), .mov 11 1, .mov 12 2, .goto (pc5a + 23),
    .imm 3 (oneW hTag), .mov 11 2, .mov 12 1,
    .imm 15 (slotW hWork slSwapped (by decide)), .storeData 15 3,
    .imm 15 (slotW hWork slKey0 (by decide)), .storeData 15 11,
    .imm 15 (slotW hWork slKey1 (by decide)), .storeData 15 12,
    .imm 6 (descW hWork descDict (by decide)),
    .add 15 14 6, .loadInput 1 15,
    .loadInput 8 1,
    .add 7 1 6, .add 9 7 8,
    .imm 4 (zeroW bits), .imm 5 (zeroW bits)] ++
  liftMap (ρ16 rfl (rfl : (ThreeCalls.layout bits cap hCap).registerCount = 16))
    (pc5a + 37) (pc5a + 114)
    (ThreeCalls.EqualityTail.checkedProgram hCap hOne (ThreeCalls.concreteSetup bits hOne)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (pc5a + 116),
    .imm 15 (slotW hWork slDescBase (by decide)), .loadData 14 15,
    .imm 7 (descW hWork descDict (by decide)),
    .add 15 14 7, .loadInput 1 15, .loadInput 8 1,
    .add 1 1 6, .add 1 1 8, .add 1 1 8,
    .add 15 1 3, .loadInput 2 15,
    .branchLt 2 6 (okPC hCap hTag) (pc5a + 128),
    .imm 15 (slotW hWork slHitNode (by decide)), .storeData 15 2,
    .imm 7 (descW hWork descBackFst (by decide)),
    .add 15 14 7, .loadInput 1 15,
    .add 15 1 2, .loadInput 3 15,
    .imm 15 (slotW hWork slKey0 (by decide)), .loadData 1 15,
    .add 1 1 6] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc5a + 138) (pc5a + 145)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (pc5a + 147) (okPC hCap hTag),
    .imm 15 (slotW hWork slDescBase (by decide)), .loadData 14 15,
    .imm 15 (slotW hWork slHitNode (by decide)), .loadData 2 15,
    .imm 7 (descW hWork descBackSnd (by decide)),
    .add 15 14 7, .loadInput 1 15,
    .add 15 1 2, .loadInput 3 15,
    .imm 15 (slotW hWork slKey1 (by decide)), .loadData 1 15] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc5a + 158) (pc5a + 165)
    (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits cap hCap) rfl (zeroW bits) (oneW hTag)) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (pc5a + 167) (okPC hCap hTag),
    .imm 15 (slotW hWork slDescBase (by decide)), .loadData 14 15,
    .imm 15 (slotW hWork slHitNode (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slYLocal (by decide)), .loadData 2 15,
    .imm 7 (descW hWork descLabels (by decide)), .add 15 14 7, .loadInput 3 15,
    .imm 7 (descW hWork descFEntry (by decide)), .add 15 14 7, .loadInput 4 15,
    .imm 7 (descW hWork descFStop (by decide)), .add 15 14 7, .loadInput 5 15,
    .imm 6 (zeroW bits), .imm 7 (oneW hTag)] ++
  liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits cap hCap).registerCount = 16))
    (pc5a + 184) (pc5a + 198) (KnownNodeCheck.knownNodeProgram hCap) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) pc5b]

@[simp] private theorem blkPairAndKnown_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkPairAndKnown hCap hWork hTag).size = 200 := by
  unfold blkPairAndKnown
  have hOne : 1 < 2 ^ bits := Nat.lt_trans (by decide : 1 < 2) hTag
  have hEq : (ThreeCalls.EqualityTail.checkedProgram hCap hOne (ThreeCalls.concreteSetup bits hOne)).size = 77 :=
    ThreeCalls.EqualityTail.checkedProgram_size hCap hOne (ThreeCalls.concreteSetup bits hOne)
  have hKn : (KnownNodeCheck.knownNodeProgram (bits := bits) hCap).size = 14 := rfl
  simp [liftMap, PairGuard.rom, hEq, hKn]

-- Block 5B (`size = 174 + exitEvalSize`, at `pc5b = 674`): `exitEvalProgram` + span orientation & `testSpan`.
private def blkExitTest {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  let sz := exitEvalSize hCap hTag
  #[.imm 15 (slotW hWork slDescBase (by decide)), .loadData 14 15,
    .imm 7 (descW hWork descLabels (by decide)), .add 15 14 7, .loadInput 3 15,
    .imm 15 (slotW hWork slYLocal (by decide)), .loadData 8 15,
    .add 15 3 8, .loadInput 6 15,
    .imm 7 (descW hWork descExitDepth (by decide)), .add 15 14 7, .loadInput 9 15,
    .imm 15 (slotW hWork slHitNode (by decide)), .loadData 12 15,
    .add 15 9 12, .loadInput 7 15,
    .imm 12 (descW hWork descExitStored (by decide)), .add 15 14 12, .loadInput 10 15,
    .imm 12 (descW hWork descExitPrior (by decide)), .add 15 14 12, .loadInput 11 15] ++
  liftMap (ρ16 rfl (rfl : (ExitEval.exitEvalLayout bits cap hCap).registerCount = 16))
    (pc5b + 22) (pc5b + 22 + sz) (ExitEval.exitEvalProgram (fits := hCap) hTag) ++
  #[.imm 15 (slotW hWork slX0Tag (by decide)), .storeData 15 0,
    .imm 15 (slotW hWork slX0Lo (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slX0Hi (by decide)), .storeData 15 2,
    .imm 15 (slotW hWork slX1Tag (by decide)), .storeData 15 3,
    .imm 15 (slotW hWork slX1Lo (by decide)), .storeData 15 4,
    .imm 15 (slotW hWork slX1Hi (by decide)), .storeData 15 5,
    .imm 15 (slotW hWork slSwapped (by decide)), .loadData 0 15,
    .imm 6 (oneW hTag),
    .branchLt 0 6 (pc5b + 62 + sz) (pc5b + 38 + sz),
    .imm 15 (slotW hWork slX0Tag (by decide)), .loadData 0 15,
    .imm 15 (slotW hWork slX0Lo (by decide)), .loadData 1 15,
    .imm 15 (slotW hWork slX0Hi (by decide)), .loadData 2 15,
    .imm 15 (slotW hWork slX1Tag (by decide)), .loadData 3 15,
    .imm 15 (slotW hWork slX1Lo (by decide)), .loadData 4 15,
    .imm 15 (slotW hWork slX1Hi (by decide)), .loadData 5 15,
    .imm 15 (slotW hWork slX0Tag (by decide)), .storeData 15 3,
    .imm 15 (slotW hWork slX0Lo (by decide)), .storeData 15 4,
    .imm 15 (slotW hWork slX0Hi (by decide)), .storeData 15 5,
    .imm 15 (slotW hWork slX1Tag (by decide)), .storeData 15 0,
    .imm 15 (slotW hWork slX1Lo (by decide)), .storeData 15 1,
    .imm 15 (slotW hWork slX1Hi (by decide)), .storeData 15 2,
    .imm 15 (slotW hWork slX0Tag (by decide)), .loadData 0 15,
    .imm 6 (oneW hTag),
    .branchLt 0 6 (pc5b + 118 + sz) (pc5b + 66 + sz),
    .imm 15 (hdrW hWork hdrOrigOfEntry (by decide)), .loadInput 14 15,
    .imm 15 (slotW hWork slX0Lo (by decide)), .loadData 2 15,
    .add 15 14 2, .loadInput 2 15,
    .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 74 + sz) (pc5b + 90 + sz) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (pc5b + 92 + sz),
    .imm 15 (hdrW hWork hdrOrigOfEntry (by decide)), .loadInput 14 15,
    .imm 15 (slotW hWork slX0Hi (by decide)), .loadData 2 15,
    .add 15 14 2, .loadInput 2 15,
    .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 100 + sz) (pc5b + 116 + sz) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (pc5b + 118 + sz),
    .imm 15 (slotW hWork slX1Tag (by decide)), .loadData 0 15,
    .imm 6 (oneW hTag),
    .branchLt 0 6 (failPC hCap hTag) (pc5b + 122 + sz),
    .imm 15 (hdrW hWork hdrOrigOfEntry (by decide)), .loadInput 14 15,
    .imm 15 (slotW hWork slX1Lo (by decide)), .loadData 2 15,
    .add 15 14 2, .loadInput 2 15,
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 130 + sz) (pc5b + 146 + sz) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (pc5b + 148 + sz),
    .imm 15 (hdrW hWork hdrOrigOfEntry (by decide)), .loadInput 14 15,
    .imm 15 (slotW hWork slX1Hi (by decide)), .loadData 2 15,
    .add 15 14 2, .loadInput 2 15,
    .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 156 + sz) (pc5b + 172 + sz) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (failPC hCap hTag)]

@[simp] private theorem blkExitTest_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkExitTest hCap hWork hTag).size = 174 + exitEvalSize hCap hTag := by
  unfold blkExitTest
  let sz := exitEvalSize hCap hTag
  have hA1 := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 74 + sz) (pc5b + 90 + sz)
  have hA2 := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 100 + sz) (pc5b + 116 + sz)
  have hA3 := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 130 + sz) (pc5b + 146 + sz)
  have hA4 := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 156 + sz) (pc5b + 172 + sz)
  simp only [Array.size_append, liftMap, Array.size_map]
  rw [hA1, hA2, hA3, hA4]
  simp [exitEvalSize]
  omega

-- Block 6 (`size = 24`, at `pc6 = 848 + exitEvalSize`): `singleTest` (`!ancestor r1 xDense`), `ok`, `fail`.
private def blkTail {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  #[.imm 15 (slotW hWork slXDense (by decide)), .loadData 2 15] ++
  ancestorCheckBlock (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc6 hCap hTag + 2) (pc6 hCap hTag + 18) ++
  #[.imm 6 (oneW hTag),
    .branchLt 0 6 (okPC hCap hTag) (failPC hCap hTag),
    .imm 0 (oneW hTag), .halt,
    .imm 0 (zeroW bits), .halt]

@[simp] private theorem blkTail_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (blkTail hCap hWork hTag).size = 24 := by
  unfold blkTail
  have hA := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc6 hCap hTag + 2) (pc6 hCap hTag + 18)
  simp only [Array.size_append]
  change 2 + (ancestorCheckBlock _ _ _ _ _ _ _ _ _).size + 6 = 24
  rw [hA]

/-- One fixed sealed Word-RAM query ROM (`workCap = queryWorkCap = 32`, `R = 16`),
independent of any digraph `g`, source `r`, failure set `F`, target `t`, or index contents. -/
def oracleQueryProgram {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    Program (codeLayout bits cap hCap hWork) :=
  blkSaveAndTarget hCap hWork hTag ++
  blkTag1 hCap hWork hTag ++
  blkTag2 hCap hWork hTag ++
  blkRoutePair hCap hWork hTag ++
  blkRouteBlocks hCap hWork hTag ++
  blkPairAndKnown hCap hWork hTag ++
  blkExitTest hCap hWork hTag ++
  blkTail hCap hWork hTag

@[simp] theorem oracleQueryProgram_size {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    (oracleQueryProgram hCap hWork hTag).size = 872 + exitEvalSize hCap hTag := by
  unfold oracleQueryProgram
  simp only [Array.size_append]
  rw [blkSaveAndTarget_size, blkTag1_size, blkTag2_size, blkRoutePair_size,
    blkRouteBlocks_size, blkPairAndKnown_size, blkExitTest_size, blkTail_size]
  omega

/-- Complete EX5.3 sealed query phase (`SealedQueryR.Phase bits 16`) wrapping `oracleQueryProgram`
with read-only index `I` and fixed scratch workspace `workCap = queryWorkCap = 32`. -/
def oracleQueryPhase {bits : Nat} (I : Array (Word bits))
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    SealedQueryR.Phase bits 16 where
  index := I
  workCap := queryWorkCap
  hR := by decide
  hI := hI
  hWork := hWork
  code := oracleQueryProgram hI hWork hTag

section PlacementAndBlocks

private theorem place_blk01 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag)
      (oracleQueryProgram hCap hWork hTag) 0 := by
  unfold oracleQueryProgram
  exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
      (placedSlice_self _))))))

private theorem place_blk012 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag ++
      blkTag2 hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) 0 := by
  unfold oracleQueryProgram
  exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_self _)))))

private theorem place_blk0123 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag ++
      blkTag2 hCap hWork hTag ++ blkRoutePair hCap hWork hTag)
      (oracleQueryProgram hCap hWork hTag) 0 := by
  unfold oracleQueryProgram
  exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_self _))))

private theorem place_blk01234 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag ++
      blkTag2 hCap hWork hTag ++ blkRoutePair hCap hWork hTag ++ blkRouteBlocks hCap hWork hTag)
      (oracleQueryProgram hCap hWork hTag) 0 := by
  unfold oracleQueryProgram
  exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_self _)))

private theorem place_blk012345a {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag ++
      blkTag2 hCap hWork hTag ++ blkRoutePair hCap hWork hTag ++ blkRouteBlocks hCap hWork hTag ++
      blkPairAndKnown hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) 0 := by
  unfold oracleQueryProgram
  exact placedSlice_append_left (placedSlice_append_left (placedSlice_self _))

private theorem place_blk012345a5b {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag ++
      blkTag2 hCap hWork hTag ++ blkRoutePair hCap hWork hTag ++ blkRouteBlocks hCap hWork hTag ++
      blkPairAndKnown hCap hWork hTag ++ blkExitTest hCap hWork hTag)
      (oracleQueryProgram hCap hWork hTag) 0 := by
  unfold oracleQueryProgram
  exact placedSlice_append_left (placedSlice_self _)

private theorem placedSlice_append_right_at {bits cap : Nat}
    {hCap : cap ≤ 2 ^ bits} {hWork : queryWorkCap ≤ 2 ^ bits}
    {a b linked : Program (codeLayout bits cap hCap hWork)} {base sa n : Nat}
    (h : PlacedSlice (a ++ b) linked base) (ha : a.size = sa) (hn : base + sa = n) :
    PlacedSlice b linked n := by
  have hr := placedSlice_append_right h
  have heq : base + a.size = n := by
    have : a.size = sa := ha
    omega
  exact heq ▸ hr

private theorem place_blk0 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkSaveAndTarget hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc0 :=
  placedSlice_append_left (place_blk01 hCap hWork hTag)

private theorem place_blk1 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkTag1 hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc1 :=
  placedSlice_append_right_at (place_blk01 hCap hWork hTag)
    (blkSaveAndTarget_size hCap hWork hTag) rfl

private theorem place_blk2 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkTag2 hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc2 :=
  placedSlice_append_right_at (place_blk012 hCap hWork hTag)
    (by rw [Array.size_append, blkSaveAndTarget_size, blkTag1_size]) rfl

private theorem place_blk3 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkRoutePair hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc3 :=
  placedSlice_append_right_at (place_blk0123 hCap hWork hTag)
    (by rw [Array.size_append, Array.size_append, blkSaveAndTarget_size, blkTag1_size, blkTag2_size]) rfl

private theorem place_blk4 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkRouteBlocks hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc4 :=
  placedSlice_append_right_at (place_blk01234 hCap hWork hTag)
    (by rw [Array.size_append, Array.size_append, Array.size_append, blkSaveAndTarget_size,
      blkTag1_size, blkTag2_size, blkRoutePair_size]) rfl

private theorem place_blk5a {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkPairAndKnown hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc5a :=
  placedSlice_append_right_at (place_blk012345a hCap hWork hTag)
    (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
      blkSaveAndTarget_size, blkTag1_size, blkTag2_size, blkRoutePair_size, blkRouteBlocks_size]) rfl

private theorem place_blk5b {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkExitTest hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) pc5b :=
  placedSlice_append_right_at (place_blk012345a5b hCap hWork hTag)
    (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
      Array.size_append, blkSaveAndTarget_size, blkTag1_size, blkTag2_size, blkRoutePair_size,
      blkRouteBlocks_size, blkPairAndKnown_size]) rfl

private theorem place_blk6 {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice (blkTail hCap hWork hTag) (oracleQueryProgram hCap hWork hTag) (pc6 hCap hTag) := by
  have h : PlacedSlice
      ((blkSaveAndTarget hCap hWork hTag ++ blkTag1 hCap hWork hTag ++
        blkTag2 hCap hWork hTag ++ blkRoutePair hCap hWork hTag ++
        blkRouteBlocks hCap hWork hTag ++ blkPairAndKnown hCap hWork hTag ++
        blkExitTest hCap hWork hTag) ++ blkTail hCap hWork hTag)
      (oracleQueryProgram hCap hWork hTag) 0 := by
    unfold oracleQueryProgram
    exact placedSlice_self _
  exact placedSlice_append_right_at h
    (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
      Array.size_append, Array.size_append, blkSaveAndTarget_size, blkTag1_size, blkTag2_size,
      blkRoutePair_size, blkRouteBlocks_size, blkPairAndKnown_size, blkExitTest_size])
    (by unfold pc6; omega)

private theorem prog_pc_lt {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {hTag : TagsFit bits} (p : Nat)
    (hp : p ≤ okPC hCap hTag + 3) :
    p < (oracleQueryProgram hCap hWork hTag).size := by
  rw [oracleQueryProgram_size]
  unfold okPC pc6 at hp
  omega

private theorem prog_pc_lt_const {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {hTag : TagsFit bits} {p : Nat}
    (hp : p ≤ 868) :
    p < (oracleQueryProgram hCap hWork hTag).size := by
  apply prog_pc_lt
  unfold okPC pc6
  omega

private theorem okPC_lt {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    okPC hCap hTag < (oracleQueryProgram hCap hWork hTag).size :=
  prog_pc_lt _ (by omega)

private theorem failPC_lt {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    failPC hCap hTag < (oracleQueryProgram hCap hWork hTag).size :=
  prog_pc_lt _ (by unfold failPC okPC; omega)

private theorem blkTail_post_placed {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 0 6 (okPC hCap hTag) (failPC hCap hTag),
        .imm 0 (oneW hTag), .halt,
        .imm 0 (zeroW bits), .halt] : Program (codeLayout bits cap hCap hWork))
      (oracleQueryProgram hCap hWork hTag) (pc6 hCap hTag + 18) := by
  have h6 := place_blk6 hCap hWork hTag
  unfold blkTail at h6
  have ha := ancestorCheckBlock_size (L := codeLayout bits cap hCap hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc6 hCap hTag + 2) (pc6 hCap hTag + 18)
  exact placedSlice_append_right_at h6 (by rw [Array.size_append, ha]; rfl) rfl

private theorem putReg_eq_same {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits}
    (s : State (codeLayout bits cap hCap hWork)) (d : Fin 16) (w : Word bits) :
    reg (putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s d w) d = w := by
  have h := reg_putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s d d w
  rw [ite_eq_left rfl] at h
  exact h

private theorem putReg_eq_other {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits}
    (s : State (codeLayout bits cap hCap hWork)) {d j : Fin 16} (hne : j ≠ d) (w : Word bits) :
    reg (putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s d w) j = reg s j := by
  have h := reg_putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s d j w
  rw [ite_eq_right hne] at h
  exact h

private theorem step_imm16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {d : Fin 16} {val : Word bits}
    (hf : code[s.pc]? = some (.imm d val)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg rfl s d val)) :=
  step_imm_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (d := d) (w := val) hf hn

private theorem step_mov16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {d src : Fin 16}
    (hf : code[s.pc]? = some (.mov d src)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg rfl s d (reg s src))) :=
  step_mov_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (d := d) (src := src) hf hn

private theorem step_add16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {d x y : Fin 16}
    (hf : code[s.pc]? = some (.add d x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg rfl s d (add (reg s x) (reg s y)))) :=
  step_add_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (d := d) (x := x) (y := y) hf hn

private theorem step_sub16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {d x y : Fin 16}
    (hf : code[s.pc]? = some (.sub d x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg rfl s d (sub (reg s x) (reg s y)))) :=
  step_sub_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (d := d) (x := x) (y := y) hf hn

private theorem step_loadInput16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {d addr : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d addr))
    (hread : input.words[(reg s addr).val]? = some w)
    (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (putReg rfl s d w)) :=
  step_loadInput_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (d := d) (addr := addr) hf hread hn

private theorem step_branchLt16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {x y : Fin 16} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yesPC noPC))
    (hfit : (if (reg s x).val < (reg s y).val then yesPC else noPC) < code.size) :
    step code input s = some (.next
      { s with pc := if (reg s x).val < (reg s y).val then yesPC else noPC }) :=
  step_branchLt_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (x := x) (y := y) hf hfit

private theorem step_goto16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork)) {s : State (codeLayout bits cap hCap hWork)}
    {targetPC : Nat}
    (hf : code[s.pc]? = some (.goto targetPC))
    (hfit : targetPC < code.size) :
    step code input s = some (.next { s with pc := targetPC }) :=
  step_goto_at hf hfit

private theorem halt_okPC {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {hTag : TagsFit bits}
    (input : Input (codeLayout bits cap hCap hWork))
    {s : State (codeLayout bits cap hCap hWork)} (hpc : s.pc = okPC hCap hTag) :
    ∃ u, Steps (oracleQueryProgram hCap hWork hTag) input 1 s u ∧
      step (oracleQueryProgram hCap hWork hTag) input u = some (.halted u) ∧
      reg u 0 = oneW hTag := by
  have hpl := blkTail_post_placed hCap hWork hTag
  have h1 : (oracleQueryProgram hCap hWork hTag)[s.pc]? = some (.imm 0 (oneW hTag)) := by
    rw [hpc]; exact placedSlice_fetch hpl (k := 2) rfl
  have h2 : (oracleQueryProgram hCap hWork hTag)[s.pc + 1]? = some .halt := by
    rw [hpc]; exact placedSlice_fetch hpl (k := 3) rfl
  have hs1 := step_imm16 input h1 (prog_pc_lt _ (by rw [hpc]; omega))
  let u := putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s 0 (oneW hTag)
  have hu : u.pc = s.pc + 1 := putReg_pc rfl s 0 (oneW hTag)
  refine ⟨u, Steps.cons hs1 (Steps.zero u), step_halt_at (by rw [hu]; exact h2), ?_⟩
  exact putReg_eq_same s 0 (oneW hTag)

private theorem halt_failPC {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits} {hTag : TagsFit bits}
    (input : Input (codeLayout bits cap hCap hWork))
    {s : State (codeLayout bits cap hCap hWork)} (hpc : s.pc = failPC hCap hTag) :
    ∃ u, Steps (oracleQueryProgram hCap hWork hTag) input 1 s u ∧
      step (oracleQueryProgram hCap hWork hTag) input u = some (.halted u) ∧
      reg u 0 = zeroW bits := by
  have hpl := blkTail_post_placed hCap hWork hTag
  have h1 : (oracleQueryProgram hCap hWork hTag)[s.pc]? = some (.imm 0 (zeroW bits)) := by
    rw [hpc]; exact placedSlice_fetch hpl (k := 4) rfl
  have h2 : (oracleQueryProgram hCap hWork hTag)[s.pc + 1]? = some .halt := by
    rw [hpc]; exact placedSlice_fetch hpl (k := 5) rfl
  have hs1 := step_imm16 input h1 (prog_pc_lt _ (by rw [hpc]; unfold failPC okPC; omega))
  let u := putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s 0 (zeroW bits)
  have hu : u.pc = s.pc + 1 := putReg_pc rfl s 0 (zeroW bits)
  refine ⟨u, Steps.cons hs1 (Steps.zero u), step_halt_at (by rw [hu]; exact h2), ?_⟩
  exact putReg_eq_same s 0 (zeroW bits)

private theorem step_writeSlot {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits}
    {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork))
    {s : State (codeLayout bits cap hCap hWork)}
    (k : Nat) (hk : k < queryWorkCap) (r : Fin 16) (hr : r ≠ 15)
    (hf0 : code[s.pc]? = some (.imm 15 (slotW hWork k hk)))
    (hf1 : code[s.pc + 1]? = some (.storeData 15 r))
    (hn1 : s.pc + 1 < code.size) (hn2 : s.pc + 2 < code.size) :
    ∃ t, Steps code input 2 s t ∧
      t.pc = s.pc + 2 ∧
      (∀ j : Fin 16, j ≠ 15 → reg t j = reg s j) ∧
      reg t 15 = slotW hWork k hk ∧
      t.data = s.data.set k (reg s r) (by rw [s.data_size]; exact hk) := by
  have hs1 := step_imm16 input hf0 hn1
  let s1 := putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s 15 (slotW hWork k hk)
  have h1pc : s1.pc = s.pc + 1 := putReg_pc rfl s 15 (slotW hWork k hk)
  have h1r15 : reg s1 15 = slotW hWork k hk := putReg_eq_same s 15 _
  have h1rr : reg s1 r = reg s r := putReg_eq_other s hr _
  have hfit : (reg s1 15).val < s1.data.size := by
    rw [h1r15, putReg_data, s.data_size]; exact hk
  have hs2 := step_storeData_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (input := input) (addr := 15) (src := r) (by rw [h1pc]; exact hf1) hfit (by rw [h1pc]; exact hn2)
  let t : State (codeLayout bits cap hCap hWork) :=
    { s1 with
      data := s1.data.set (reg s1 15).val (reg s1 r) hfit
      pc := s1.pc + 1
      data_size := by simp only [Array.size_set, s1.data_size] }
  refine ⟨t, Steps.cons hs1 (Steps.cons hs2 (Steps.zero t)), ?_, ?_, ?_, ?_⟩
  · change s1.pc + 1 = s.pc + 2; omega
  · intro j hj; exact putReg_eq_other s hj _
  · exact h1r15
  · change s1.data.set (reg s1 15).val (reg s1 r) hfit = _
    simp only [h1r15, h1rr, slotW]; rfl

private theorem step_readSlot {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits}
    {code : Program (codeLayout bits cap hCap hWork)}
    (input : Input (codeLayout bits cap hCap hWork))
    {s : State (codeLayout bits cap hCap hWork)}
    (k : Nat) (hk : k < queryWorkCap) (d : Fin 16) (hd : d ≠ 15) (w : Word bits)
    (hw : s.data[k]? = some w)
    (hf0 : code[s.pc]? = some (.imm 15 (slotW hWork k hk)))
    (hf1 : code[s.pc + 1]? = some (.loadData d 15))
    (hn1 : s.pc + 1 < code.size) (hn2 : s.pc + 2 < code.size) :
    ∃ t, Steps code input 2 s t ∧
      t.pc = s.pc + 2 ∧
      (∀ j : Fin 16, j ≠ d → j ≠ 15 → reg t j = reg s j) ∧
      reg t d = w ∧
      reg t 15 = slotW hWork k hk ∧
      t.data = s.data := by
  have hs1 := step_imm16 input hf0 hn1
  let s1 := putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s 15 (slotW hWork k hk)
  have h1pc : s1.pc = s.pc + 1 := putReg_pc rfl s 15 _
  have h1r15 : reg s1 15 = slotW hWork k hk := putReg_eq_same s 15 _
  have h1d : s1.data = s.data := putReg_data rfl s 15 _
  have hload : s1.data[(reg s1 15).val]? = some w := by
    rw [h1d, h1r15]; exact hw
  have hs2 := step_loadData_next (h16 := (rfl : (codeLayout bits cap hCap hWork).registerCount = 16))
    (input := input) (d := d) (addr := 15) (by rw [h1pc]; exact hf1) hload (by rw [h1pc]; exact hn2)
  let t := putReg (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) s1 d w
  refine ⟨t, Steps.cons hs1 (Steps.cons hs2 (Steps.zero t)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [putReg_pc]; omega
  · intro j hjd hj15
    exact (putReg_eq_other s1 hjd w).trans (putReg_eq_other s hj15 _)
  · exact putReg_eq_same s1 d w
  · exact (putReg_eq_other s1 (Ne.symm hd) w).trans h1r15
  · rw [putReg_data, h1d]

private theorem data_set_getElem? {α : Type} (a : Array α) (k : Nat) (v : α)
    (hk : k < a.size) (j : Nat) :
    (a.set k v hk)[j]? = if j = k then some v else a[j]? := by
  by_cases hj : j < a.size
  · have hj' : j < (a.set k v hk).size := by simpa only [Array.size_set] using hj
    rw [getElem?_pos (a.set k v hk) j hj', getElem?_pos a j hj, Array.getElem_set]
    by_cases hjk : k = j
    · subst hjk; simp
    · simp [hjk, Ne.symm hjk]
  · have hj' : ¬ j < (a.set k v hk).size := by simpa only [Array.size_set] using hj
    have hne : j ≠ k := fun h => hj (h ▸ hk)
    rw [getElem?_neg (a.set k v hk) j hj', getElem?_neg a j hj, ite_eq_right hne]

private theorem data_set_other {α : Type} (a : Array α) (k : Nat) (v : α)
    (hk : k < a.size) {j : Nat} (hne : j ≠ k) :
    (a.set k v hk)[j]? = a[j]? := by
  rw [data_set_getElem?, ite_eq_right hne]

private theorem data_set_same {α : Type} (a : Array α) (k : Nat) (v : α)
    (hk : k < a.size) :
    (a.set k v hk)[k]? = some v := by
  rw [data_set_getElem?, ite_eq_left rfl]

private theorem place_blk0_pre {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice
      (#[.imm 15 (slotW hWork slTag (by decide)), .storeData 15 0,
        .imm 15 (slotW hWork slFail0 (by decide)), .storeData 15 1,
        .imm 15 (slotW hWork slFail1 (by decide)), .storeData 15 2,
        .imm 15 (slotW hWork slTarget (by decide)), .storeData 15 3,
        .imm 0 (hdrW hWork hdrOrigToDense (by decide)),
        .imm 6 (oneW hTag)] : Program (codeLayout bits cap hCap hWork))
      (oracleQueryProgram hCap hWork hTag) 0 := by
  have h0 := place_blk0 hCap hWork hTag
  unfold blkSaveAndTarget at h0
  exact placedSlice_append_left (placedSlice_append_left h0)

private theorem place_blk0_trans {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice
      (liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits cap hCap).registerCount = 16))
        10 14 (sealedTranslation hCap))
      (oracleQueryProgram hCap hWork hTag) 10 := by
  have h0 := place_blk0 hCap hWork hTag
  unfold blkSaveAndTarget at h0
  exact placedSlice_append_right_at (placedSlice_append_left h0) rfl rfl

private theorem place_blk0_post {bits cap : Nat} (hCap : cap ≤ 2 ^ bits)
    (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits) :
    PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 5 6 (failPC hCap hTag) 16,
        .sub 1 5 6,
        .imm 15 (slotW hWork slXDense (by decide)), .storeData 15 1,
        .imm 15 (slotW hWork slTag (by decide)), .loadData 0 15,
        .branchLt 0 6 (okPC hCap hTag) 22,
        .imm 7 (twoW hTag),
        .branchLt 0 7 24 pc2] : Program (codeLayout bits cap hCap hWork))
      (oracleQueryProgram hCap hWork hTag) 14 := by
  have h0 := place_blk0 hCap hWork hTag
  unfold blkSaveAndTarget at h0
  have hst : (liftMap (L := codeLayout bits cap hCap hWork)
      (ρ16 rfl (rfl : (sealedTranslationLayout bits cap hCap).registerCount = 16))
      10 14 (sealedTranslation hCap)).size = 4 := by
    simp [liftMap, sealedTranslation]
  exact placedSlice_append_right_at h0 (by rw [Array.size_append, hst]) rfl

private theorem exec_blkSaveAndTarget {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = 0)
    (tag f0 f1 tgt origToDenseBase wTgt : Word bits)
    (hr0 : reg s 0 = tag) (hr1 : reg s 1 = f0) (hr2 : reg s 2 = f1) (hr3 : reg s 3 = tgt)
    (hOrigHdr : I[hdrOrigToDense]? = some origToDenseBase)
    (hMapTgt : origToDenseBase.val + tgt.val < I.size)
    (hwTgt : I[origToDenseBase.val + tgt.val]? = some wTgt) :
    (wTgt.val = 0 →
      ∃ t k, k ≤ 18 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = failPC hI hTag) ∧
    (wTgt.val ≠ 0 → tag.val = 0 →
      ∃ t k, k ≤ 22 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = okPC hI hTag) ∧
    (wTgt.val ≠ 0 → tag.val = 1 →
      ∃ t k, k ≤ 24 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc1 ∧
        t.data.size = queryWorkCap ∧
        t.data[slFail0]? = some f0 ∧
        (t.data[slXDense]?).map Fin.val = some (wTgt.val - 1)) ∧
    (wTgt.val ≠ 0 → tag.val = 2 →
      ∃ t k, k ≤ 24 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc2 ∧
        t.data.size = queryWorkCap ∧
        t.data[slFail0]? = some f0 ∧
        t.data[slFail1]? = some f1 ∧
        (t.data[slXDense]?).map Fin.val = some (wTgt.val - 1)) := by
  let prog := oracleQueryProgram hI hWork hTag
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have hPre := place_blk0_pre hI hWork hTag
  have hPost := place_blk0_post hI hWork hTag
  obtain ⟨s1, hs1, h1pc, h1r, _, h1d⟩ := step_writeSlot inp slTag (by decide) 0 (by decide)
    (by rw [hpc]; exact placedSlice_fetch hPre (k := 0) rfl)
    (by rw [hpc]; exact placedSlice_fetch hPre (k := 1) rfl)
    (prog_pc_lt_const (by omega)) (prog_pc_lt_const (by omega))
  rw [hpc] at h1pc
  obtain ⟨s2, hs2, h2pc, h2r, _, h2d⟩ := step_writeSlot inp slFail0 (by decide) 1 (by decide)
    (by rw [h1pc]; exact placedSlice_fetch hPre (k := 2) rfl)
    (by rw [h1pc]; exact placedSlice_fetch hPre (k := 3) rfl)
    (prog_pc_lt_const (by omega)) (prog_pc_lt_const (by omega))
  rw [h1pc] at h2pc
  obtain ⟨s3, hs3, h3pc, h3r, _, h3d⟩ := step_writeSlot inp slFail1 (by decide) 2 (by decide)
    (by rw [h2pc]; exact placedSlice_fetch hPre (k := 4) rfl)
    (by rw [h2pc]; exact placedSlice_fetch hPre (k := 5) rfl)
    (prog_pc_lt_const (by omega)) (prog_pc_lt_const (by omega))
  rw [h2pc] at h3pc
  obtain ⟨s4, hs4, h4pc, h4r, _, h4d⟩ := step_writeSlot inp slTarget (by decide) 3 (by decide)
    (by rw [h3pc]; exact placedSlice_fetch hPre (k := 6) rfl)
    (by rw [h3pc]; exact placedSlice_fetch hPre (k := 7) rfl)
    (prog_pc_lt_const (by omega)) (prog_pc_lt_const (by omega))
  rw [h3pc] at h4pc
  have hs5 := step_imm16 inp (by rw [h4pc]; exact placedSlice_fetch hPre (k := 8) rfl)
    (prog_pc_lt_const (by omega))
  let s5 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s4 0
    (hdrW hWork hdrOrigToDense (by decide))
  have h5pc : s5.pc = 9 := by rw [putReg_pc, h4pc]
  have hs6 := step_imm16 inp (by rw [h5pc]; exact placedSlice_fetch hPre (k := 9) rfl)
    (prog_pc_lt_const (by omega))
  let s6 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s5 6 (oneW hTag)
  have h6pc : s6.pc = 10 := by rw [putReg_pc, h5pc]
  have h6r0 : reg s6 0 = hdrW hWork hdrOrigToDense (by decide) :=
    (putReg_eq_other s5 (by decide : (0 : Fin 16) ≠ 6) _).trans (putReg_eq_same s4 0 _)
  have h6r3 : reg s6 3 = tgt := by
    rw [putReg_eq_other s5 (by decide : (3 : Fin 16) ≠ 6),
      putReg_eq_other s4 (by decide : (3 : Fin 16) ≠ 0),
      h4r 3 (by decide), h3r 3 (by decide), h2r 3 (by decide), h1r 3 (by decide), hr3]
  have h6d : s6.data = s4.data := by rw [putReg_data, putReg_data]
  obtain ⟨s7, hs7, h7pc, _, h7r5, h7d⟩ := lifted_sealedTranslation (h16 := rfl)
    (place_blk0_trans hI hWork hTag) (prog_pc_lt_const (by omega)) inp s6 h6pc
    (hdrW hWork hdrOrigToDense (by decide)) origToDenseBase tgt h6r0 h6r3 hOrigHdr hMapTgt
  have h7r5_eq : reg s7 5 = wTgt := by
    have hp : I[origToDenseBase.val + tgt.val]? = some (I[origToDenseBase.val + tgt.val]'hMapTgt) :=
      getElem?_pos I _ hMapTgt
    exact h7r5.trans (Option.some.inj (hp.symm.trans hwTgt))
  have hs8 := step_imm16 inp (by rw [h7pc]; exact placedSlice_fetch hPost (k := 0) rfl)
    (prog_pc_lt_const (by omega))
  let s8 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s7 6 (oneW hTag)
  have h8pc : s8.pc = 15 := by rw [putReg_pc, h7pc]
  have h8r5 : reg s8 5 = wTgt := (putReg_eq_other s7 (by decide : (5 : Fin 16) ≠ 6) _).trans h7r5_eq
  have h8r6 : reg s8 6 = oneW hTag := putReg_eq_same s7 6 _
  have hpre : Steps prog inp 15 s s8 :=
    ((((hs1.append hs2).append hs3).append hs4).append
      (Steps.cons hs5 (Steps.cons hs6 (Steps.zero s6)))).append
      (hs7.append (Steps.cons hs8 (Steps.zero s8)))
  have hs4_sz : s4.data.size = queryWorkCap := by
    rw [h4d, Array.size_set, h3d, Array.size_set, h2d, Array.size_set, h1d, Array.size_set, s.data_size]
  have hs4_tag : s4.data[slTag]? = some tag := by
    rw [h4d, data_set_other _ _ _ _ (by decide), h3d, data_set_other _ _ _ _ (by decide),
      h2d, data_set_other _ _ _ _ (by decide), h1d, data_set_same, hr0]
  have hs4_f0 : s4.data[slFail0]? = some f0 := by
    rw [h4d, data_set_other _ _ _ _ (by decide), h3d, data_set_other _ _ _ _ (by decide),
      h2d, data_set_same, h1r 1 (by decide), hr1]
  have hs4_f1 : s4.data[slFail1]? = some f1 := by
    rw [h4d, data_set_other _ _ _ _ (by decide), h3d, data_set_same,
      h2r 2 (by decide), h1r 2 (by decide), hr2]
  have h8d : s8.data = s4.data := by rw [putReg_data, h7d, h6d]
  have commonNonZero : wTgt.val ≠ 0 →
      ∃ s12, Steps prog inp 21 s s12 ∧ s12.pc = 21 ∧
        reg s12 0 = tag ∧ reg s12 6 = oneW hTag ∧
        s12.data.size = queryWorkCap ∧ s12.data[slFail0]? = some f0 ∧
        s12.data[slFail1]? = some f1 ∧ (s12.data[slXDense]?).map Fin.val = some (wTgt.val - 1) := by
    intro hwne
    have hge1 : ¬ wTgt.val < 1 := by omega
    have hs9 := step_branchLt16 inp (by rw [h8pc]; exact placedSlice_fetch hPost (k := 1) rfl) (by
        rw [h8r5, h8r6, oneW]; change (if wTgt.val < 1 then failPC hI hTag else 16) < prog.size
        rw [ite_eq_right hge1]; exact prog_pc_lt_const (by omega))
    let s9 := { s8 with pc := if (reg s8 5).val < (reg s8 6).val then failPC hI hTag else 16 }
    have h9pc : s9.pc = 16 := by
      change (if (reg s8 5).val < (reg s8 6).val then _ else _) = _
      rw [h8r5, h8r6, oneW]; exact ite_eq_right hge1
    have hs10 := step_sub16 inp (by rw [h9pc]; exact placedSlice_fetch hPost (k := 2) rfl)
      (prog_pc_lt_const (by omega))
    let s10 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s9 1 (sub (reg s9 5) (reg s9 6))
    have h10pc : s10.pc = 17 := by rw [putReg_pc, h9pc]
    have h10r1 : (reg s10 1).val = wTgt.val - 1 := by
      have hr1eq : reg s10 1 = sub (reg s9 5) (reg s9 6) := putReg_eq_same s9 1 _
      have hsub := sub_no_wrap (reg s9 5) (reg s9 6)
        (by show (reg s8 6).val ≤ (reg s8 5).val; rw [h8r5, h8r6, oneW]; change 1 ≤ wTgt.val; omega)
      rw [hr1eq, hsub]; show (reg s8 5).val - (reg s8 6).val = wTgt.val - 1
      rw [h8r5, h8r6, oneW]
    have h10d : s10.data = s4.data := by rw [putReg_data]; exact h8d
    obtain ⟨s11, hs11, h11pc, h11r, _, h11d⟩ := step_writeSlot inp slXDense (by decide) 1 (by decide)
      (by rw [h10pc]; exact placedSlice_fetch hPost (k := 3) rfl)
      (by rw [h10pc]; exact placedSlice_fetch hPost (k := 4) rfl)
      (prog_pc_lt_const (by omega)) (prog_pc_lt_const (by omega))
    rw [h10pc] at h11pc
    have h11tag : s11.data[slTag]? = some tag := by
      rw [h11d, data_set_other _ _ _ _ (by decide), h10d]; exact hs4_tag
    obtain ⟨s12, hs12, h12pc, h12r, h12r0, _, h12d⟩ :=
      step_readSlot inp slTag (by decide) 0 (by decide) tag h11tag
        (by rw [h11pc]; exact placedSlice_fetch hPost (k := 5) rfl)
        (by rw [h11pc]; exact placedSlice_fetch hPost (k := 6) rfl)
        (prog_pc_lt_const (by omega)) (prog_pc_lt_const (by omega))
    rw [h11pc] at h12pc
    have h12r6 : reg s12 6 = oneW hTag := by
      have hs9r6 : reg s9 6 = oneW hTag := h8r6
      rw [h12r 6 (by decide) (by decide), h11r 6 (by decide),
        putReg_eq_other s9 (by decide : (6 : Fin 16) ≠ 1) _, hs9r6]
    have hsteps := ((hpre.append (Steps.cons hs9 (Steps.cons hs10 (Steps.zero s10)))).append hs11).append hs12
    refine ⟨s12, hsteps, h12pc, h12r0, h12r6, ?_, ?_, ?_, ?_⟩
    · rw [h12d, h11d, Array.size_set, h10d, hs4_sz]
    · rw [h12d, h11d, data_set_other _ _ _ _ (by decide), h10d]; exact hs4_f0
    · rw [h12d, h11d, data_set_other _ _ _ _ (by decide), h10d]; exact hs4_f1
    · rw [h12d, h11d, data_set_same, Option.map_some, h10r1]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hw0
    have hs9 := step_branchLt16 inp (by rw [h8pc]; exact placedSlice_fetch hPost (k := 1) rfl) (by
        rw [h8r5, h8r6, hw0, oneW]; change (if (0 : Nat) < 1 then failPC hI hTag else 16) < prog.size
        simp only [ite_eq_left (by decide : (0 : Nat) < 1)]; exact failPC_lt hI hWork hTag)
    let s9 := { s8 with pc := if (reg s8 5).val < (reg s8 6).val then failPC hI hTag else 16 }
    have h9pc : s9.pc = failPC hI hTag := by
      change (if (reg s8 5).val < (reg s8 6).val then _ else _) = _
      rw [h8r5, h8r6, hw0, oneW]; simp
    exact ⟨s9, 16, by omega, hpre.append (Steps.cons hs9 (Steps.zero s9)), h9pc⟩
  · intro hwne htag0
    obtain ⟨s12, hsteps, h12pc, h12r0, h12r6, _, _, _, _⟩ := commonNonZero hwne
    have hs13 := step_branchLt16 inp (by rw [h12pc]; exact placedSlice_fetch hPost (k := 7) rfl) (by
        rw [h12r0, h12r6, htag0, oneW]
        change (if (0 : Nat) < 1 then okPC hI hTag else 22) < prog.size
        simp only [ite_eq_left (by decide : (0 : Nat) < 1)]; exact okPC_lt hI hWork hTag)
    let s13 := { s12 with pc := if (reg s12 0).val < (reg s12 6).val then okPC hI hTag else 22 }
    have h13pc : s13.pc = okPC hI hTag := by
      change (if (reg s12 0).val < (reg s12 6).val then _ else _) = _
      rw [h12r0, h12r6, htag0, oneW]; simp
    exact ⟨s13, 22, Nat.le_refl _, hsteps.append (Steps.cons hs13 (Steps.zero s13)), h13pc⟩
  · intro hwne htag1
    obtain ⟨s12, hsteps, h12pc, h12r0, h12r6, hsz, hf0, _, hx⟩ := commonNonZero hwne
    have hs13 := step_branchLt16 inp (by rw [h12pc]; exact placedSlice_fetch hPost (k := 7) rfl) (by
        rw [h12r0, h12r6, htag1, oneW]
        change (if (1 : Nat) < 1 then okPC hI hTag else 22) < prog.size
        simp only [ite_eq_right (by decide : ¬ (1 : Nat) < 1)]; exact prog_pc_lt_const (by omega))
    let s13 := { s12 with pc := if (reg s12 0).val < (reg s12 6).val then okPC hI hTag else 22 }
    have h13pc : s13.pc = 22 := by
      change (if (reg s12 0).val < (reg s12 6).val then _ else _) = _
      rw [h12r0, h12r6, htag1, oneW]; simp
    have hs14 := step_imm16 inp (by rw [h13pc]; exact placedSlice_fetch hPost (k := 8) rfl)
      (prog_pc_lt_const (by omega))
    let s14 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s13 7 (twoW hTag)
    have h14pc : s14.pc = 23 := by rw [putReg_pc, h13pc]
    have h14r0 : reg s14 0 = tag := (putReg_eq_other s13 (by decide : (0 : Fin 16) ≠ 7) _).trans h12r0
    have h14r7 : reg s14 7 = twoW hTag := putReg_eq_same s13 7 _
    have hs15 := step_branchLt16 inp (by rw [h14pc]; exact placedSlice_fetch hPost (k := 9) rfl) (by
        rw [h14r0, h14r7, htag1, twoW]
        change (if (1 : Nat) < 2 then 24 else pc2) < prog.size
        simp only [ite_eq_left (by decide : (1 : Nat) < 2)]; exact prog_pc_lt_const (by omega))
    let s15 := { s14 with pc := if (reg s14 0).val < (reg s14 7).val then 24 else pc2 }
    have h15pc : s15.pc = pc1 := by
      change (if (reg s14 0).val < (reg s14 7).val then _ else _) = _
      rw [h14r0, h14r7, htag1, twoW]; simp [pc1]
    have h15d : s15.data = s12.data := by rw [putReg_data]
    exact ⟨s15, 24, Nat.le_refl _,
      hsteps.append (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (Steps.zero s15)))),
      h15pc, by rw [h15d]; exact hsz, by rw [h15d]; exact hf0, by rw [h15d]; exact hx⟩
  · intro hwne htag2
    obtain ⟨s12, hsteps, h12pc, h12r0, h12r6, hsz, hf0, hf1, hx⟩ := commonNonZero hwne
    have hs13 := step_branchLt16 inp (by rw [h12pc]; exact placedSlice_fetch hPost (k := 7) rfl) (by
        rw [h12r0, h12r6, htag2, oneW]
        change (if (2 : Nat) < 1 then okPC hI hTag else 22) < prog.size
        simp only [ite_eq_right (by decide : ¬ (2 : Nat) < 1)]; exact prog_pc_lt_const (by omega))
    let s13 := { s12 with pc := if (reg s12 0).val < (reg s12 6).val then okPC hI hTag else 22 }
    have h13pc : s13.pc = 22 := by
      change (if (reg s12 0).val < (reg s12 6).val then _ else _) = _
      rw [h12r0, h12r6, htag2, oneW]; simp
    have hs14 := step_imm16 inp (by rw [h13pc]; exact placedSlice_fetch hPost (k := 8) rfl)
      (prog_pc_lt_const (by omega))
    let s14 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s13 7 (twoW hTag)
    have h14pc : s14.pc = 23 := by rw [putReg_pc, h13pc]
    have h14r0 : reg s14 0 = tag := (putReg_eq_other s13 (by decide : (0 : Fin 16) ≠ 7) _).trans h12r0
    have h14r7 : reg s14 7 = twoW hTag := putReg_eq_same s13 7 _
    have hs15 := step_branchLt16 inp (by rw [h14pc]; exact placedSlice_fetch hPost (k := 9) rfl) (by
        rw [h14r0, h14r7, htag2, twoW]
        change (if (2 : Nat) < 2 then 24 else pc2) < prog.size
        simp only [ite_eq_right (by decide : ¬ (2 : Nat) < 2)]; exact prog_pc_lt_const (by unfold pc2; omega))
    let s15 := { s14 with pc := if (reg s14 0).val < (reg s14 7).val then 24 else pc2 }
    have h15pc : s15.pc = pc2 := by
      change (if (reg s14 0).val < (reg s14 7).val then _ else _) = _
      rw [h14r0, h14r7, htag2, twoW]; simp
    have h15d : s15.data = s12.data := by rw [putReg_data]
    exact ⟨s15, 24, Nat.le_refl _,
      hsteps.append (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (Steps.zero s15)))),
      h15pc, by rw [h15d]; exact hsz, by rw [h15d]; exact hf0, by rw [h15d]; exact hf1,
      by rw [h15d]; exact hx⟩

private theorem reg_r16 {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits}
    (s : State (codeLayout bits cap hCap hWork)) (i : Fin 16) :
    reg s (r16 (rfl : (codeLayout bits cap hCap hWork).registerCount = 16) i) = reg s i :=
  rfl

private theorem exec_blkTag1 {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc1)
    (f0 xW origToDenseBase wA : Word bits)
    (hf0 : s.data[slFail0]? = some f0)
    (hx : s.data[slXDense]? = some xW)
    (hOrigHdr : I[hdrOrigToDense]? = some origToDenseBase)
    (hMapA : origToDenseBase.val + f0.val < I.size)
    (hwA : I[origToDenseBase.val + f0.val]? = some wA) :
    (wA.val = 0 →
      ∃ t k, k ≤ 9 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = okPC hI hTag) ∧
    (wA.val = 1 →
      ∃ t k, k ≤ 11 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = failPC hI hTag) ∧
    (2 ≤ wA.val → wA.val - 1 = xW.val →
      ∃ t k, k ≤ 24 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = failPC hI hTag) ∧
    (2 ≤ wA.val → wA.val - 1 ≠ xW.val →
      ∃ t k, k ≤ 27 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc6 hI hTag ∧ (reg t 1).val = wA.val - 1 ∧ t.data[slXDense]? = some xW) := by
  let prog := oracleQueryProgram hI hWork hTag
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have h1 := place_blk1 hI hWork hTag
  have hPre : PlacedSlice
      (#[.imm 15 (slotW hWork slFail0 (by decide)), .loadData 3 15,
        .imm 0 (hdrW hWork hdrOrigToDense (by decide))] : Program (codeLayout bits I.size hI hWork))
      prog pc1 := by
    unfold blkTag1 at h1
    exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left h1)))
  have hTr : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (pc1 + 3) (pc1 + 7) (sealedTranslation hI))
      prog (pc1 + 3) := by
    unfold blkTag1 at h1
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h1))) rfl rfl
  have hMid : PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 5 6 (okPC hI hTag) (pc1 + 9),
        .sub 1 5 6,
        .branchLt 1 6 (failPC hI hTag) (pc1 + 11),
        .imm 15 (slotW hWork slADense (by decide)), .storeData 15 1,
        .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] : Program (codeLayout bits I.size hI hWork))
      prog (pc1 + 7) := by
    unfold blkTag1 at h1
    have hst : (liftMap (L := codeLayout bits I.size hI hWork)
        (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (pc1 + 3) (pc1 + 7) (sealedTranslation hI)).size = 4 := by
      simp [liftMap, sealedTranslation]
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left h1))
      (by rw [Array.size_append, hst]; rfl) rfl
  have hGuard : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
        (pc1 + 15) (pc1 + 22)
        (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      prog (pc1 + 15) := by
    unfold blkTag1 at h1
    have hst : (liftMap (L := codeLayout bits I.size hI hWork)
        (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (pc1 + 3) (pc1 + 7) (sealedTranslation hI)).size = 4 := by
      simp [liftMap, sealedTranslation]
    exact placedSlice_append_right_at (placedSlice_append_left h1)
      (by rw [Array.size_append, Array.size_append, hst]; rfl) rfl
  have hPost : PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 0 6 (failPC hI hTag) (pc1 + 24),
        .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
        .goto (pc6 hI hTag)] : Program (codeLayout bits I.size hI hWork))
      prog (pc1 + 22) := by
    unfold blkTag1 at h1
    have hst : (liftMap (L := codeLayout bits I.size hI hWork)
        (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (pc1 + 3) (pc1 + 7) (sealedTranslation hI)).size = 4 := by
      simp [liftMap, sealedTranslation]
    have hpg : (liftMap (L := codeLayout bits I.size hI hWork)
        (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
        (pc1 + 15) (pc1 + 22)
        (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag))).size = 7 := by
      simp [liftMap, PairGuard.rom]
    exact placedSlice_append_right_at h1
      (by rw [Array.size_append, Array.size_append, Array.size_append, hst, hpg]; rfl) rfl
  obtain ⟨s1, hs1, h1pc, h1r, h1r3, _, h1d⟩ := step_readSlot inp slFail0 (by decide) 3 (by decide) f0 hf0
    (by rw [hpc]; exact placedSlice_fetch hPre (k := 0) rfl)
    (by rw [hpc]; exact placedSlice_fetch hPre (k := 1) rfl)
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc1]; omega))
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc1]; omega))
  rw [hpc] at h1pc
  have hs2 := step_imm16 inp (by rw [h1pc]; exact placedSlice_fetch hPre (k := 2) rfl)
    (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc1]; omega))
  let s2 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s1 0
    (hdrW hWork hdrOrigToDense (by decide))
  have h2pc : s2.pc = pc1 + 3 := by rw [putReg_pc, h1pc]
  have h2r0 : reg s2 0 = hdrW hWork hdrOrigToDense (by decide) := putReg_eq_same s1 0 _
  have h2r3 : reg s2 3 = f0 := (putReg_eq_other s1 (by decide : (3 : Fin 16) ≠ 0) _).trans h1r3
  have h2d : s2.data = s.data := by rw [putReg_data, h1d]
  obtain ⟨s3, hs3, h3pc, _, h3r5, h3d⟩ := lifted_sealedTranslation (h16 := rfl) hTr
    (prog_pc_lt_const (by dsimp only [pc1]; omega)) inp s2 h2pc
    (hdrW hWork hdrOrigToDense (by decide)) origToDenseBase f0 h2r0 h2r3 hOrigHdr hMapA
  have h3r5_eq : reg s3 5 = wA := by
    have hp : I[origToDenseBase.val + f0.val]? = some (I[origToDenseBase.val + f0.val]'hMapA) :=
      getElem?_pos I _ hMapA
    exact h3r5.trans (Option.some.inj (hp.symm.trans hwA))
  have hs4 := step_imm16 inp (by rw [h3pc]; exact placedSlice_fetch hMid (k := 0) rfl)
    (prog_pc_lt_const (by rw [h3pc]; dsimp only [pc1]; omega))
  let s4 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s3 6 (oneW hTag)
  have h4pc : s4.pc = pc1 + 8 := by rw [putReg_pc, h3pc]
  have h4r5 : reg s4 5 = wA := (putReg_eq_other s3 (by decide : (5 : Fin 16) ≠ 6) _).trans h3r5_eq
  have h4r6 : reg s4 6 = oneW hTag := putReg_eq_same s3 6 _
  have h4d : s4.data = s.data := by rw [putReg_data, h3d, h2d]
  have hpre : Steps prog inp 8 s s4 :=
    (hs1.append (Steps.cons hs2 (Steps.zero s2))).append (hs3.append (Steps.cons hs4 (Steps.zero s4)))
  have midGe1 : ¬ wA.val < 1 →
      ∃ s6, Steps prog inp 10 s s6 ∧ s6.pc = pc1 + 10 ∧
        (reg s6 1).val = wA.val - 1 ∧ reg s6 6 = oneW hTag ∧ s6.data = s.data := by
    intro hge1
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hMid (k := 1) rfl) (by
        rw [h4r5, h4r6, oneW]; change (if wA.val < 1 then okPC hI hTag else pc1 + 9) < prog.size
        rw [ite_eq_right hge1]; exact prog_pc_lt_const (by dsimp only [pc1]; omega))
    let s5 := { s4 with pc := if (reg s4 5).val < (reg s4 6).val then okPC hI hTag else pc1 + 9 }
    have h5pc : s5.pc = pc1 + 9 := by
      change (if (reg s4 5).val < (reg s4 6).val then _ else _) = _
      rw [h4r5, h4r6, oneW]; exact ite_eq_right hge1
    have hs6 := step_sub16 inp (by rw [h5pc]; exact placedSlice_fetch hMid (k := 2) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc1]; omega))
    let s6 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s5 1 (sub (reg s5 5) (reg s5 6))
    have h6pc : s6.pc = pc1 + 10 := by rw [putReg_pc, h5pc]
    have h6r1 : (reg s6 1).val = wA.val - 1 := by
      have hr1 := putReg_eq_same s5 1 (sub (reg s5 5) (reg s5 6))
      have hsub := sub_no_wrap (reg s5 5) (reg s5 6)
        (by show (reg s4 6).val ≤ (reg s4 5).val; rw [h4r5, h4r6, oneW]; change 1 ≤ wA.val; omega)
      rw [hr1, hsub]; show (reg s4 5).val - (reg s4 6).val = wA.val - 1; rw [h4r5, h4r6, oneW]
    have h6r6 : reg s6 6 = oneW hTag :=
      (putReg_eq_other s5 (by decide : (6 : Fin 16) ≠ 1) _).trans h4r6
    exact ⟨s6, hpre.append (Steps.cons hs5 (Steps.cons hs6 (Steps.zero s6))), h6pc, h6r1, h6r6,
      by rw [putReg_data]; exact h4d⟩
  have midGe2 : 2 ≤ wA.val →
      ∃ s11, Steps prog inp 20 s s11 ∧ s11.pc = pc1 + 23 ∧
        (reg s11 0).val = (if wA.val - 1 = xW.val then 0 else 1) ∧
        reg s11 6 = oneW hTag ∧
        (s11.data[slADense]?).map Fin.val = some (wA.val - 1) ∧
        s11.data[slXDense]? = some xW := by
    intro hge2
    obtain ⟨s6, h6st, h6pc, h6r1, h6r6, h6d⟩ := midGe1 (by omega)
    have hnotlt : ¬ (reg s6 1).val < (reg s6 6).val := by
      rw [h6r1, h6r6, oneW]; change ¬ (wA.val - 1 < 1); omega
    have hs7 := step_branchLt16 inp (by rw [h6pc]; exact placedSlice_fetch hMid (k := 3) rfl) (by
        change (if (reg s6 1).val < (reg s6 6).val then failPC hI hTag else pc1 + 11) < prog.size
        rw [ite_eq_right hnotlt]; exact prog_pc_lt_const (by dsimp only [pc1]; omega))
    let s7 := { s6 with pc := if (reg s6 1).val < (reg s6 6).val then failPC hI hTag else pc1 + 11 }
    have h7pc : s7.pc = pc1 + 11 := by
      change (if (reg s6 1).val < (reg s6 6).val then _ else _) = _; exact ite_eq_right hnotlt
    have hs7' := h6st.append (Steps.cons hs7 (Steps.zero s7))
    have h7d : s7.data = s.data := h6d
    obtain ⟨s8, hs8, h8pc, h8r, _, h8d⟩ := step_writeSlot inp slADense (by decide) 1 (by decide)
      (by rw [h7pc]; exact placedSlice_fetch hMid (k := 4) rfl)
      (by rw [h7pc]; exact placedSlice_fetch hMid (k := 5) rfl)
      (prog_pc_lt_const (by rw [h7pc]; dsimp only [pc1]; omega))
      (prog_pc_lt_const (by rw [h7pc]; dsimp only [pc1]; omega))
    rw [h7pc] at h8pc
    have h8x : s8.data[slXDense]? = some xW := by
      rw [h8d, data_set_other _ _ _ _ (by decide), h7d]; exact hx
    have h8a : (s8.data[slADense]?).map Fin.val = some (wA.val - 1) := by
      rw [h8d, data_set_same, Option.map_some]; exact congrArg some h6r1
    obtain ⟨s9, hs9, h9pc, h9r, h9r3, _, h9d⟩ := step_readSlot inp slXDense (by decide) 3 (by decide) xW h8x
      (by rw [h8pc]; exact placedSlice_fetch hMid (k := 6) rfl)
      (by rw [h8pc]; exact placedSlice_fetch hMid (k := 7) rfl)
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc1]; omega))
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc1]; omega))
    rw [h8pc] at h9pc
    have h9r1 : (reg s9 1).val = wA.val - 1 := by
      rw [h9r 1 (by decide) (by decide), h8r 1 (by decide)]; exact h6r1
    have h9d' : s9.data = s8.data := h9d
    obtain ⟨s10, hs10, h10pc, h10r0, h10d⟩ := lifted_pairGuard (h16 := rfl) (zeroW bits) (oneW hTag) rfl rfl
      hGuard (prog_pc_lt_const (by dsimp only [pc1]; omega)) inp s9 h9pc
    have h10r0' : (reg s10 0).val = (if wA.val - 1 = xW.val then 0 else 1) := by
      rw [reg_r16] at h10r0
      rw [h10r0]
      change (if (reg s9 1).val = (reg s9 3).val then 0 else 1) = _
      rw [h9r1, h9r3]
    have hs11 := step_imm16 inp (by rw [h10pc]; exact placedSlice_fetch hPost (k := 0) rfl)
      (prog_pc_lt_const (by rw [h10pc]; dsimp only [pc1]; omega))
    let s11 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s10 6 (oneW hTag)
    have h11pc : s11.pc = pc1 + 23 := by rw [putReg_pc, h10pc]
    have h11r0 : (reg s11 0).val = (if wA.val - 1 = xW.val then 0 else 1) := by
      rw [putReg_eq_other s10 (by decide : (0 : Fin 16) ≠ 6) _]; exact h10r0'
    have h11r6 : reg s11 6 = oneW hTag := putReg_eq_same s10 6 _
    have h11d : s11.data = s8.data := by rw [putReg_data, h10d, h9d']
    have htot := (((hs7'.append hs8).append hs9).append hs10).append (Steps.cons hs11 (Steps.zero s11))
    refine ⟨s11, htot, h11pc, h11r0, h11r6, by rw [h11d]; exact h8a, by rw [h11d]; exact h8x⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hw0
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hMid (k := 1) rfl) (by
        rw [h4r5, h4r6, hw0, oneW]; change (if (0 : Nat) < 1 then okPC hI hTag else pc1 + 9) < prog.size
        simp only [ite_eq_left (by decide : (0 : Nat) < 1)]; exact okPC_lt hI hWork hTag)
    let s5 := { s4 with pc := if (reg s4 5).val < (reg s4 6).val then okPC hI hTag else pc1 + 9 }
    have h5pc : s5.pc = okPC hI hTag := by
      change (if (reg s4 5).val < (reg s4 6).val then _ else _) = _; rw [h4r5, h4r6, hw0, oneW]; simp
    exact ⟨s5, 9, Nat.le_refl _, hpre.append (Steps.cons hs5 (Steps.zero s5)), h5pc⟩
  · intro hw1
    obtain ⟨s6, h6st, h6pc, h6r1, h6r6, _⟩ := midGe1 (by omega)
    have hlt1 : (reg s6 1).val < (reg s6 6).val := by
      rw [h6r1, h6r6, hw1, oneW]; change 1 - 1 < 1; decide
    have hs7 := step_branchLt16 inp (by rw [h6pc]; exact placedSlice_fetch hMid (k := 3) rfl) (by
        change (if (reg s6 1).val < (reg s6 6).val then failPC hI hTag else pc1 + 11) < prog.size
        rw [ite_eq_left hlt1]; exact failPC_lt hI hWork hTag)
    let s7 := { s6 with pc := if (reg s6 1).val < (reg s6 6).val then failPC hI hTag else pc1 + 11 }
    have h7pc : s7.pc = failPC hI hTag := by
      change (if (reg s6 1).val < (reg s6 6).val then _ else _) = _; exact ite_eq_left hlt1
    exact ⟨s7, 11, Nat.le_refl _, h6st.append (Steps.cons hs7 (Steps.zero s7)), h7pc⟩
  · intro hge2 heqx
    obtain ⟨s11, h11st, h11pc, h11r0, h11r6, _, _⟩ := midGe2 hge2
    have hlt : (reg s11 0).val < (reg s11 6).val := by
      rw [h11r0, h11r6, oneW, ite_eq_left heqx]; change 0 < 1; decide
    have hs12 := step_branchLt16 inp (by rw [h11pc]; exact placedSlice_fetch hPost (k := 1) rfl) (by
        change (if (reg s11 0).val < (reg s11 6).val then failPC hI hTag else pc1 + 24) < prog.size
        rw [ite_eq_left hlt]; exact failPC_lt hI hWork hTag)
    let s12 := { s11 with pc := if (reg s11 0).val < (reg s11 6).val then failPC hI hTag else pc1 + 24 }
    have h12pc : s12.pc = failPC hI hTag := by
      change (if (reg s11 0).val < (reg s11 6).val then _ else _) = _; exact ite_eq_left hlt
    exact ⟨s12, 21, by omega, h11st.append (Steps.cons hs12 (Steps.zero s12)), h12pc⟩
  · intro hge2 hneqx
    obtain ⟨s11, h11st, h11pc, h11r0, h11r6, h11a, h11x⟩ := midGe2 hge2
    have hnlt : ¬ (reg s11 0).val < (reg s11 6).val := by
      rw [h11r0, h11r6, oneW, ite_eq_right hneqx]; change ¬ (1 < 1); decide
    have hs12 := step_branchLt16 inp (by rw [h11pc]; exact placedSlice_fetch hPost (k := 1) rfl) (by
        change (if (reg s11 0).val < (reg s11 6).val then failPC hI hTag else pc1 + 24) < prog.size
        rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by dsimp only [pc1]; omega))
    let s12 := { s11 with pc := if (reg s11 0).val < (reg s11 6).val then failPC hI hTag else pc1 + 24 }
    have h12pc : s12.pc = pc1 + 24 := by
      change (if (reg s11 0).val < (reg s11 6).val then _ else _) = _; exact ite_eq_right hnlt
    obtain ⟨aW, haW, haVal⟩ : ∃ aW : Word bits, s12.data[slADense]? = some aW ∧ aW.val = wA.val - 1 := by
      cases hget : s11.data[slADense]? with
      | none => rw [hget] at h11a; cases h11a
      | some w =>
          rw [hget, Option.map_some, Option.some.injEq] at h11a
          exact ⟨w, rfl, h11a⟩
    obtain ⟨s13, hs13, h13pc, _, h13r1, _, h13d⟩ := step_readSlot inp slADense (by decide) 1 (by decide) aW haW
      (by rw [h12pc]; exact placedSlice_fetch hPost (k := 2) rfl)
      (by rw [h12pc]; exact placedSlice_fetch hPost (k := 3) rfl)
      (prog_pc_lt_const (by rw [h12pc]; dsimp only [pc1]; omega))
      (prog_pc_lt_const (by rw [h12pc]; dsimp only [pc1]; omega))
    rw [h12pc] at h13pc
    have hs14 := step_goto16 inp (by rw [h13pc]; exact placedSlice_fetch hPost (k := 4) rfl)
      (prog_pc_lt _ (by unfold okPC; omega))
    let s14 := { s13 with pc := pc6 hI hTag }
    have h14pc : s14.pc = pc6 hI hTag := rfl
    have htot := ((h11st.append (Steps.cons hs12 (Steps.zero s12))).append hs13).append
      (Steps.cons hs14 (Steps.zero s14))
    refine ⟨s14, 24, by omega, htot, h14pc, ?_, ?_⟩
    · change (reg s13 1).val = wA.val - 1; rw [h13r1]; exact haVal
    · change s13.data[slXDense]? = some xW; rw [h13d]; exact h11x

private theorem unwrap_map_val {bits : Nat} (a : Array (Word bits)) (k v : Nat)
    (h : (a[k]?).map Fin.val = some v) :
    ∃ w : Word bits, a[k]? = some w ∧ w.val = v := by
  cases hget : a[k]? with
  | none => rw [hget] at h; cases h
  | some w => rw [hget, Option.map_some, Option.some.injEq] at h; exact ⟨w, rfl, h⟩

private theorem exec_blkTag2_half {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (slFail : Nat) (hkFail : slFail < queryWorkCap) (_hneFailX : slXDense ≠ slFail)
    (slDst : Nat) (hkDst : slDst < queryWorkCap) (hneDstX : slXDense ≠ slDst)
    (base donePC : Nat) (hbase : base ≤ 80) (hdone : donePC = base + 25)
    (hf0 : (oracleQueryProgram hI hWork hTag)[base]? = some (.imm 15 (slotW hWork slFail hkFail)))
    (hf1 : (oracleQueryProgram hI hWork hTag)[base + 1]? = some (.loadData 3 15))
    (hf2 : (oracleQueryProgram hI hWork hTag)[base + 2]? = some (.imm 0 (hdrW hWork hdrOrigToDense (by decide))))
    (hTr : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (base + 3) (base + 7) (sealedTranslation hI))
      (oracleQueryProgram hI hWork hTag) (base + 3))
    (hMid : PlacedSlice
      (#[.imm 6 (oneW hTag), .imm 7 (twoW hTag),
        .imm 15 (slotW hWork slDst hkDst), .storeData 15 5,
        .branchLt 5 6 donePC (base + 12),
        .branchLt 5 7 (failPC hI hTag) (base + 13),
        .sub 1 5 6,
        .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] :
        Program (codeLayout bits I.size hI hWork))
      (oracleQueryProgram hI hWork hTag) (base + 7))
    (hGuard : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
        (base + 16) (base + 23)
        (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      (oracleQueryProgram hI hWork hTag) (base + 16))
    (hp0 : (oracleQueryProgram hI hWork hTag)[base + 23]? = some (.imm 6 (oneW hTag)))
    (hp1 : (oracleQueryProgram hI hWork hTag)[base + 24]? = some (.branchLt 0 6 (failPC hI hTag) donePC))
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = base)
    (fVal xW origToDenseBase wVal : Word bits)
    (hFail : s.data[slFail]? = some fVal) (hx : s.data[slXDense]? = some xW)
    (hOrigHdr : I[hdrOrigToDense]? = some origToDenseBase)
    (hMap : origToDenseBase.val + fVal.val < I.size)
    (hwVal : I[origToDenseBase.val + fVal.val]? = some wVal) :
    (wVal.val = 1 →
      ∃ t k, k ≤ 13 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = failPC hI hTag) ∧
    (2 ≤ wVal.val → wVal.val - 1 = xW.val →
      ∃ t k, k ≤ 22 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = failPC hI hTag) ∧
    (wVal.val = 0 ∨ (2 ≤ wVal.val ∧ wVal.val - 1 ≠ xW.val) →
      ∃ t k, k ≤ 22 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = donePC ∧
        t.data[slDst]? = some wVal ∧
        (∀ j, j ≠ slDst → t.data[j]? = s.data[j]?)) := by
  let prog := oracleQueryProgram hI hWork hTag
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  obtain ⟨s1, hs1, h1pc, _, h1r3, _, h1d⟩ := step_readSlot inp slFail hkFail 3 (by decide) fVal hFail
    (by rw [hpc]; exact hf0) (by rw [hpc]; exact hf1)
    (prog_pc_lt_const (by rw [hpc]; omega)) (prog_pc_lt_const (by rw [hpc]; omega))
  rw [hpc] at h1pc
  have hs2 := step_imm16 inp (by rw [h1pc]; exact hf2) (prog_pc_lt_const (by rw [h1pc]; omega))
  let s2 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s1 0
    (hdrW hWork hdrOrigToDense (by decide))
  have h2pc : s2.pc = base + 3 := by rw [putReg_pc, h1pc]
  have h2r0 : reg s2 0 = hdrW hWork hdrOrigToDense (by decide) := putReg_eq_same s1 0 _
  have h2r3 : reg s2 3 = fVal := (putReg_eq_other s1 (by decide : (3 : Fin 16) ≠ 0) _).trans h1r3
  have h2d : s2.data = s.data := by rw [putReg_data, h1d]
  obtain ⟨s3, hs3, h3pc, _, h3r5, h3d⟩ := lifted_sealedTranslation (h16 := rfl) hTr
    (prog_pc_lt_const (by omega)) inp s2 h2pc
    (hdrW hWork hdrOrigToDense (by decide)) origToDenseBase fVal h2r0 h2r3 hOrigHdr hMap
  have h3r5_eq : reg s3 5 = wVal := by
    have hp : I[origToDenseBase.val + fVal.val]? = some (I[origToDenseBase.val + fVal.val]'hMap) :=
      getElem?_pos I _ hMap
    exact h3r5.trans (Option.some.inj (hp.symm.trans hwVal))
  have hs4 := step_imm16 inp (by rw [h3pc]; exact placedSlice_fetch hMid (k := 0) rfl)
    (prog_pc_lt_const (by rw [h3pc]; omega))
  let s4 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s3 6 (oneW hTag)
  have h4pc : s4.pc = base + 8 := by rw [putReg_pc, h3pc]
  have hs5 := step_imm16 inp (by rw [h4pc]; exact placedSlice_fetch hMid (k := 1) rfl)
    (prog_pc_lt_const (by rw [h4pc]; omega))
  let s5 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s4 7 (twoW hTag)
  have h5pc : s5.pc = base + 9 := by rw [putReg_pc, h4pc]
  have h5r5 : reg s5 5 = wVal :=
    ((putReg_eq_other s4 (by decide : (5 : Fin 16) ≠ 7) _).trans
      (putReg_eq_other s3 (by decide : (5 : Fin 16) ≠ 6) _)).trans h3r5_eq
  have h5r6 : reg s5 6 = oneW hTag :=
    (putReg_eq_other s4 (by decide : (6 : Fin 16) ≠ 7) _).trans (putReg_eq_same s3 6 _)
  have h5r7 : reg s5 7 = twoW hTag := putReg_eq_same s4 7 _
  have h5d : s5.data = s.data := by rw [putReg_data, putReg_data, h3d, h2d]
  obtain ⟨s6, hs6, h6pc, h6r, _, h6d⟩ := step_writeSlot inp slDst hkDst 5 (by decide)
    (by rw [h5pc]; exact placedSlice_fetch hMid (k := 2) rfl)
    (by rw [h5pc]; exact placedSlice_fetch hMid (k := 3) rfl)
    (prog_pc_lt_const (by rw [h5pc]; omega)) (prog_pc_lt_const (by rw [h5pc]; omega))
  rw [h5pc] at h6pc
  have h6r5 : reg s6 5 = wVal := (h6r 5 (by decide)).trans h5r5
  have h6r6 : reg s6 6 = oneW hTag := (h6r 6 (by decide)).trans h5r6
  have h6r7 : reg s6 7 = twoW hTag := (h6r 7 (by decide)).trans h5r7
  have h6dst : s6.data[slDst]? = some wVal := by
    rw [h6d, data_set_same, h5r5]
  have h6frame : ∀ j, j ≠ slDst → s6.data[j]? = s.data[j]? := fun j hj => by
    rw [h6d, data_set_other _ _ _ _ hj, h5d]
  have hpre : Steps prog inp 11 s s6 :=
    (((hs1.append (Steps.cons hs2 (Steps.zero s2))).append hs3).append
      (Steps.cons hs4 (Steps.cons hs5 (Steps.zero s5)))).append hs6
  have hge1Mid : ¬ wVal.val < 1 →
      ∃ s7, Steps prog inp 12 s s7 ∧ s7.pc = base + 12 ∧
        reg s7 5 = wVal ∧ reg s7 6 = oneW hTag ∧ reg s7 7 = twoW hTag ∧
        s7.data = s6.data := by
    intro hge1
    have hs7 := step_branchLt16 inp (by rw [h6pc]; exact placedSlice_fetch hMid (k := 4) rfl) (by
        rw [h6r5, h6r6, oneW]; change (if wVal.val < 1 then donePC else base + 12) < prog.size
        rw [ite_eq_right hge1]; exact prog_pc_lt_const (by omega))
    let s7 := { s6 with pc := if (reg s6 5).val < (reg s6 6).val then donePC else base + 12 }
    have h7pc : s7.pc = base + 12 := by
      change (if (reg s6 5).val < (reg s6 6).val then _ else _) = _
      rw [h6r5, h6r6, oneW]; exact ite_eq_right hge1
    exact ⟨s7, hpre.append (Steps.cons hs7 (Steps.zero s7)), h7pc, h6r5, h6r6, h6r7, rfl⟩
  have hge2Mid : 2 ≤ wVal.val →
      ∃ s12, Steps prog inp 21 s s12 ∧ s12.pc = base + 24 ∧
        (reg s12 0).val = (if wVal.val - 1 = xW.val then 0 else 1) ∧
        reg s12 6 = oneW hTag ∧ s12.data = s6.data := by
    intro hge2
    obtain ⟨s7, h7st, h7pc, h7r5, h7r6, h7r7, h7d⟩ := hge1Mid (by omega)
    have hn2 : ¬ (reg s7 5).val < (reg s7 7).val := by
      rw [h7r5, h7r7, twoW]; change ¬ (wVal.val < 2); omega
    have hs8 := step_branchLt16 inp (by rw [h7pc]; exact placedSlice_fetch hMid (k := 5) rfl) (by
        change (if (reg s7 5).val < (reg s7 7).val then failPC hI hTag else base + 13) < prog.size
        rw [ite_eq_right hn2]; exact prog_pc_lt_const (by omega))
    let s8 := { s7 with pc := if (reg s7 5).val < (reg s7 7).val then failPC hI hTag else base + 13 }
    have h8pc : s8.pc = base + 13 := by
      change (if (reg s7 5).val < (reg s7 7).val then _ else _) = _; exact ite_eq_right hn2
    have hs9 := step_sub16 inp (by rw [h8pc]; exact placedSlice_fetch hMid (k := 6) rfl)
      (prog_pc_lt_const (by rw [h8pc]; omega))
    let s9 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s8 1 (sub (reg s8 5) (reg s8 6))
    have h9pc : s9.pc = base + 14 := by rw [putReg_pc, h8pc]
    have h9r1 : (reg s9 1).val = wVal.val - 1 := by
      have hr1 := putReg_eq_same s8 1 (sub (reg s8 5) (reg s8 6))
      have hsub := sub_no_wrap (reg s8 5) (reg s8 6)
        (by show (reg s7 6).val ≤ (reg s7 5).val; rw [h7r5, h7r6, oneW]; change 1 ≤ wVal.val; omega)
      rw [hr1, hsub]; show (reg s7 5).val - (reg s7 6).val = wVal.val - 1; rw [h7r5, h7r6, oneW]
    have h9x : s9.data[slXDense]? = some xW := by
      rw [putReg_data]; change s7.data[slXDense]? = _; rw [h7d, h6frame slXDense hneDstX]; exact hx
    obtain ⟨s10, hs10, h10pc, h10r, h10r3, _, h10d⟩ := step_readSlot inp slXDense (by decide) 3 (by decide) xW h9x
      (by rw [h9pc]; exact placedSlice_fetch hMid (k := 7) rfl)
      (by rw [h9pc]; exact placedSlice_fetch hMid (k := 8) rfl)
      (prog_pc_lt_const (by rw [h9pc]; omega)) (prog_pc_lt_const (by rw [h9pc]; omega))
    rw [h9pc] at h10pc
    have h10r1 : (reg s10 1).val = wVal.val - 1 :=
      (congrArg Fin.val (h10r 1 (by decide) (by decide))).trans h9r1
    obtain ⟨s11, hs11, h11pc, h11r0, h11d⟩ := lifted_pairGuard (h16 := rfl) (zeroW bits) (oneW hTag) rfl rfl
      hGuard (prog_pc_lt_const (by omega)) inp s10 h10pc
    have h11lt : s11.pc + 1 ≤ 868 := by
      rw [h11pc]; exact Nat.le_trans (Nat.add_le_add_right hbase 24) (by decide)
    have hs12 := step_imm16 inp (by rw [h11pc]; exact hp0) (prog_pc_lt_const h11lt)
    let s12 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s11 6 (oneW hTag)
    have h12pc : s12.pc = base + 24 := by rw [putReg_pc, h11pc]
    have h12r0 : (reg s12 0).val = (if wVal.val - 1 = xW.val then 0 else 1) := by
      rw [putReg_eq_other s11 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s11 0, h11r0]
      change (if (reg s10 1).val = (reg s10 3).val then 0 else 1) = _
      rw [h10r1, h10r3]
    have h12r6 : reg s12 6 = oneW hTag := putReg_eq_same s11 6 _
    have h12d : s12.data = s6.data := by
      rw [putReg_data, h11d, h10d, putReg_data]; exact h7d
    have htot := (((h7st.append (Steps.cons hs8 (Steps.cons hs9 (Steps.zero s9)))).append hs10).append hs11).append
      (Steps.cons hs12 (Steps.zero s12))
    exact ⟨s12, htot, h12pc, h12r0, h12r6, h12d⟩
  refine ⟨?_, ?_, ?_⟩
  · intro hw1
    obtain ⟨s7, h7st, h7pc, h7r5, _, h7r7, _⟩ := hge1Mid (by omega)
    have hlt2 : (reg s7 5).val < (reg s7 7).val := by rw [h7r5, h7r7, hw1, twoW]; change 1 < 2; decide
    have hs8 := step_branchLt16 inp (by rw [h7pc]; exact placedSlice_fetch hMid (k := 5) rfl) (by
        change (if (reg s7 5).val < (reg s7 7).val then failPC hI hTag else base + 13) < prog.size
        rw [ite_eq_left hlt2]; exact failPC_lt hI hWork hTag)
    let s8 := { s7 with pc := if (reg s7 5).val < (reg s7 7).val then failPC hI hTag else base + 13 }
    have h8pc : s8.pc = failPC hI hTag := by
      change (if (reg s7 5).val < (reg s7 7).val then _ else _) = _; exact ite_eq_left hlt2
    exact ⟨s8, 13, Nat.le_refl _, h7st.append (Steps.cons hs8 (Steps.zero s8)), h8pc⟩
  · intro hge2 heqx
    obtain ⟨s12, h12st, h12pc, h12r0, h12r6, _⟩ := hge2Mid hge2
    have hlt : (reg s12 0).val < (reg s12 6).val := by
      rw [h12r0, h12r6, oneW, ite_eq_left heqx]; change 0 < 1; decide
    have hs13 := step_branchLt16 inp (by rw [h12pc]; exact hp1) (by
        change (if (reg s12 0).val < (reg s12 6).val then failPC hI hTag else donePC) < prog.size
        rw [ite_eq_left hlt]; exact failPC_lt hI hWork hTag)
    let s13 := { s12 with pc := if (reg s12 0).val < (reg s12 6).val then failPC hI hTag else donePC }
    have h13pc : s13.pc = failPC hI hTag := by
      change (if (reg s12 0).val < (reg s12 6).val then _ else _) = _; exact ite_eq_left hlt
    exact ⟨s13, 22, Nat.le_refl _, h12st.append (Steps.cons hs13 (Steps.zero s13)), h13pc⟩
  · intro hcase
    rcases hcase with hw0 | ⟨hge2, hneqx⟩
    · have hlt1 : (reg s6 5).val < (reg s6 6).val := by
        rw [h6r5, h6r6, hw0, oneW]; change 0 < 1; decide
      have hs7 := step_branchLt16 inp (by rw [h6pc]; exact placedSlice_fetch hMid (k := 4) rfl) (by
          change (if (reg s6 5).val < (reg s6 6).val then donePC else base + 12) < prog.size
          rw [ite_eq_left hlt1]; exact prog_pc_lt_const (by omega))
      let s7 := { s6 with pc := if (reg s6 5).val < (reg s6 6).val then donePC else base + 12 }
      have h7pc : s7.pc = donePC := by
        change (if (reg s6 5).val < (reg s6 6).val then _ else _) = _; exact ite_eq_left hlt1
      exact ⟨s7, 12, by omega, hpre.append (Steps.cons hs7 (Steps.zero s7)), h7pc, h6dst, h6frame⟩
    · obtain ⟨s12, h12st, h12pc, h12r0, h12r6, h12d⟩ := hge2Mid hge2
      have hnlt : ¬ (reg s12 0).val < (reg s12 6).val := by
        rw [h12r0, h12r6, oneW, ite_eq_right hneqx]; change ¬ (1 < 1); decide
      have hs13 := step_branchLt16 inp (by rw [h12pc]; exact hp1) (by
          change (if (reg s12 0).val < (reg s12 6).val then failPC hI hTag else donePC) < prog.size
          rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by omega))
      let s13 := { s12 with pc := if (reg s12 0).val < (reg s12 6).val then failPC hI hTag else donePC }
      have h13pc : s13.pc = donePC := by
        change (if (reg s12 0).val < (reg s12 6).val then _ else _) = _; exact ite_eq_right hnlt
      exact ⟨s13, 22, Nat.le_refl _, h12st.append (Steps.cons hs13 (Steps.zero s13)), h13pc,
        by change s12.data[slDst]? = _; rw [h12d]; exact h6dst,
        fun j hj => by change s12.data[j]? = _; rw [h12d]; exact h6frame j hj⟩

private theorem exec_blkTag2 {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc2)
    (f0 f1 xW origToDenseBase wA wB : Word bits)
    (hf0 : s.data[slFail0]? = some f0) (hf1 : s.data[slFail1]? = some f1)
    (hx : s.data[slXDense]? = some xW)
    (hOrigHdr : I[hdrOrigToDense]? = some origToDenseBase)
    (hMapA : origToDenseBase.val + f0.val < I.size)
    (hMapB : origToDenseBase.val + f1.val < I.size)
    (hwA : I[origToDenseBase.val + f0.val]? = some wA)
    (hwB : I[origToDenseBase.val + f1.val]? = some wB) :
    (wA.val = 1 ∨ (2 ≤ wA.val ∧ wA.val - 1 = xW.val) ∨
      wB.val = 1 ∨ (2 ≤ wB.val ∧ wB.val - 1 = xW.val) →
      ∃ t k, k ≤ 44 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = failPC hI hTag) ∧
    (wA.val = 0 → wB.val = 0 →
      ∃ t k, k ≤ 54 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = okPC hI hTag) ∧
    (wA.val = 0 → 2 ≤ wB.val → wB.val - 1 ≠ xW.val →
      ∃ t k, k ≤ 54 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc6 hI hTag ∧ (reg t 1).val = wB.val - 1 ∧ t.data[slXDense]? = some xW) ∧
    (2 ≤ wA.val → wA.val - 1 ≠ xW.val → wB.val = 0 →
      ∃ t k, k ≤ 54 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc6 hI hTag ∧ (reg t 1).val = wA.val - 1 ∧ t.data[slXDense]? = some xW) ∧
    (2 ≤ wA.val → wA.val - 1 ≠ xW.val → 2 ≤ wB.val → wB.val - 1 ≠ xW.val →
      ∃ t k, k ≤ 58 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc3 ∧
        t.data.size = queryWorkCap ∧
        (t.data[slADense]?).map Fin.val = some (wA.val - 1) ∧
        (t.data[slBDense]?).map Fin.val = some (wB.val - 1) ∧
        t.data[slXDense]? = some xW) := by
  let prog := oracleQueryProgram hI hWork hTag
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have h2 := place_blk2 hI hWork hTag
  have hstSz : ∀ base ret, (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
      base ret (sealedTranslation hI)).size = 4 := fun _ _ => by simp [liftMap, sealedTranslation]
  have hpgSz : ∀ base ret, (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
      base ret (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl
        (zeroW bits) (oneW hTag))).size = 7 := fun _ _ => by simp [liftMap, PairGuard.rom]
  have hPre0 : PlacedSlice
      (#[.imm 15 (slotW hWork slFail0 (by decide)), .loadData 3 15,
        .imm 0 (hdrW hWork hdrOrigToDense (by decide))] : Program (codeLayout bits I.size hI hWork))
      prog pc2 := by
    unfold blkTag2 at h2
    exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left h2)))))))
  have hTr0 : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (pc2 + 3) (pc2 + 7) (sealedTranslation hI))
      prog (pc2 + 3) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
          (placedSlice_append_left h2))))))) rfl rfl
  have hMid0 : PlacedSlice
      (#[.imm 6 (oneW hTag), .imm 7 (twoW hTag),
        .imm 15 (slotW hWork slADense (by decide)), .storeData 15 5,
        .branchLt 5 6 (pc2 + 25) (pc2 + 12),
        .branchLt 5 7 (failPC hI hTag) (pc2 + 13),
        .sub 1 5 6,
        .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] :
        Program (codeLayout bits I.size hI hWork)) prog (pc2 + 7) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h2))))))
      (by rw [Array.size_append, hstSz]; rfl) rfl
  have hG0 : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
        (pc2 + 16) (pc2 + 23)
        (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      prog (pc2 + 16) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left h2)))))
      (by rw [Array.size_append, Array.size_append, hstSz]; rfl) rfl
  have hMidChunk : PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 0 6 (failPC hI hTag) (pc2 + 25),
        .imm 15 (slotW hWork slFail1 (by decide)), .loadData 3 15,
        .imm 0 (hdrW hWork hdrOrigToDense (by decide))] : Program (codeLayout bits I.size hI hWork))
      prog (pc2 + 23) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left h2))))
      (by rw [Array.size_append, Array.size_append, Array.size_append, hstSz, hpgSz]; rfl) rfl
  have hTr1 : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (sealedTranslationLayout bits I.size hI).registerCount = 16))
        (pc2 + 28) (pc2 + 32) (sealedTranslation hI))
      prog (pc2 + 28) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h2)))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        hstSz, hpgSz]; rfl) rfl
  have hMid1 : PlacedSlice
      (#[.imm 6 (oneW hTag), .imm 7 (twoW hTag),
        .imm 15 (slotW hWork slBDense (by decide)), .storeData 15 5,
        .branchLt 5 6 (pc2 + 50) (pc2 + 37),
        .branchLt 5 7 (failPC hI hTag) (pc2 + 38),
        .sub 1 5 6,
        .imm 15 (slotW hWork slXDense (by decide)), .loadData 3 15] :
        Program (codeLayout bits I.size hI hWork)) prog (pc2 + 32) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left h2))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, hstSz, hpgSz, hstSz]; rfl) rfl
  have hG1 : PlacedSlice
      (liftMap (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
        (pc2 + 41) (pc2 + 48)
        (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      prog (pc2 + 41) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at (placedSlice_append_left h2)
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, hstSz, hpgSz, hstSz]; rfl) rfl
  have hTail : PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 0 6 (failPC hI hTag) (pc2 + 50),
        .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 2 15,
        .imm 6 (oneW hTag),
        .branchLt 1 6 (pc2 + 56) (pc2 + 59),
        .branchLt 2 6 (okPC hI hTag) (pc2 + 57),
        .sub 1 2 6,
        .goto (pc6 hI hTag),
        .sub 1 1 6,
        .imm 15 (slotW hWork slADense (by decide)), .storeData 15 1,
        .branchLt 2 6 (pc6 hI hTag) (pc2 + 63),
        .sub 2 2 6,
        .imm 15 (slotW hWork slBDense (by decide)), .storeData 15 2] :
        Program (codeLayout bits I.size hI hWork)) prog (pc2 + 48) := by
    unfold blkTag2 at h2
    exact placedSlice_append_right_at h2
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append, hstSz, hpgSz, hstSz, hpgSz]; rfl) rfl
  have hA := exec_blkTag2_half hI hWork hTag slFail0 (by decide) (by decide) slADense (by decide)
    (by decide) pc2 (pc2 + 25) (by dsimp only [pc2]; omega) rfl
    (placedSlice_fetch hPre0 (k := 0) rfl) (placedSlice_fetch hPre0 (k := 1) rfl)
    (placedSlice_fetch hPre0 (k := 2) rfl) hTr0 hMid0 hG0
    (placedSlice_fetch hMidChunk (k := 0) rfl) (placedSlice_fetch hMidChunk (k := 1) rfl)
    s hpc f0 xW origToDenseBase wA hf0 hx hOrigHdr hMapA hwA
  have runB : (wA.val = 0 ∨ (2 ≤ wA.val ∧ wA.val - 1 ≠ xW.val)) →
      ∃ sa ka, ka ≤ 22 ∧ Steps prog inp ka s sa ∧ sa.pc = pc2 + 25 ∧
        sa.data[slADense]? = some wA ∧ sa.data[slXDense]? = some xW ∧
        sa.data[slFail1]? = some f1 ∧ sa.data.size = queryWorkCap := by
    intro hokA
    obtain ⟨sa, ka, hka, hsa, hapc, hadst, haframe⟩ := hA.2.2 hokA
    refine ⟨sa, ka, hka, hsa, hapc, hadst, ?_, ?_, ?_⟩
    · rw [haframe slXDense (by decide)]; exact hx
    · rw [haframe slFail1 (by decide)]; exact hf1
    · exact sa.data_size
  have runBothOk : (wA.val = 0 ∨ (2 ≤ wA.val ∧ wA.val - 1 ≠ xW.val)) →
      (wB.val = 0 ∨ (2 ≤ wB.val ∧ wB.val - 1 ≠ xW.val)) →
      ∃ sb kb, kb ≤ 44 ∧ Steps prog inp kb s sb ∧ sb.pc = pc2 + 50 ∧
        sb.data[slADense]? = some wA ∧ sb.data[slBDense]? = some wB ∧
        sb.data[slXDense]? = some xW ∧ sb.data.size = queryWorkCap := by
    intro hokA hokB
    obtain ⟨sa, ka, hka, hsa, hapc, haA, haX, haF1, haSz⟩ := runB hokA
    have hB := exec_blkTag2_half hI hWork hTag slFail1 (by decide) (by decide) slBDense (by decide)
      (by decide) (pc2 + 25) (pc2 + 50) (by dsimp only [pc2]; omega) rfl
      (placedSlice_fetch hMidChunk (k := 2) rfl) (placedSlice_fetch hMidChunk (k := 3) rfl)
      (placedSlice_fetch hMidChunk (k := 4) rfl) hTr1 hMid1 hG1
      (placedSlice_fetch hTail (k := 0) rfl) (placedSlice_fetch hTail (k := 1) rfl)
      sa hapc f1 xW origToDenseBase wB haF1 haX hOrigHdr hMapB hwB
    obtain ⟨sb, kb, hkb, hsb, hbpc, hbB, hbframe⟩ := hB.2.2 hokB
    refine ⟨sb, ka + kb, by omega, hsa.append hsb, hbpc, ?_, hbB, ?_, ?_⟩
    · rw [hbframe slADense (by decide)]; exact haA
    · rw [hbframe slXDense (by decide)]; exact haX
    · exact sb.data_size
  have runToTail : (wA.val = 0 ∨ (2 ≤ wA.val ∧ wA.val - 1 ≠ xW.val)) →
      (wB.val = 0 ∨ (2 ≤ wB.val ∧ wB.val - 1 ≠ xW.val)) →
      ∃ s3 k3, k3 ≤ 49 ∧ Steps prog inp k3 s s3 ∧ s3.pc = pc2 + 55 ∧
        reg s3 1 = wA ∧ reg s3 2 = wB ∧ reg s3 6 = oneW hTag ∧
        s3.data[slADense]? = some wA ∧ s3.data[slBDense]? = some wB ∧
        s3.data[slXDense]? = some xW ∧ s3.data.size = queryWorkCap := by
    intro hokA hokB
    obtain ⟨sb, kb, hkb, hsb, hbpc, hbA, hbB, hbX, hbSz⟩ := runBothOk hokA hokB
    obtain ⟨s1, hs1, h1pc, h1r, h1r1, _, h1d⟩ := step_readSlot inp slADense (by decide) 1 (by decide) wA hbA
      (by rw [hbpc]; exact placedSlice_fetch hTail (k := 2) rfl)
      (by rw [hbpc]; exact placedSlice_fetch hTail (k := 3) rfl)
      (prog_pc_lt_const (by rw [hbpc]; dsimp only [pc2]; omega))
      (prog_pc_lt_const (by rw [hbpc]; dsimp only [pc2]; omega))
    rw [hbpc] at h1pc
    obtain ⟨s2, hs2, h2pc, h2r, h2r2, _, h2d⟩ := step_readSlot inp slBDense (by decide) 2 (by decide) wB
      (by rw [h1d]; exact hbB)
      (by rw [h1pc]; exact placedSlice_fetch hTail (k := 4) rfl)
      (by rw [h1pc]; exact placedSlice_fetch hTail (k := 5) rfl)
      (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc2]; omega))
      (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc2]; omega))
    rw [h1pc] at h2pc
    have hs3 := step_imm16 inp (by rw [h2pc]; exact placedSlice_fetch hTail (k := 6) rfl)
      (prog_pc_lt_const (by rw [h2pc]; dsimp only [pc2]; omega))
    let s3 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s2 6 (oneW hTag)
    have h3pc : s3.pc = pc2 + 55 := by rw [putReg_pc, h2pc]
    have h3r1 : reg s3 1 = wA :=
      ((putReg_eq_other s2 (by decide : (1 : Fin 16) ≠ 6) _).trans
        (h2r 1 (by decide) (by decide))).trans h1r1
    have h3r2 : reg s3 2 = wB := (putReg_eq_other s2 (by decide : (2 : Fin 16) ≠ 6) _).trans h2r2
    have h3r6 : reg s3 6 = oneW hTag := putReg_eq_same s2 6 _
    have h3d : s3.data = sb.data := by rw [putReg_data, h2d, h1d]
    exact ⟨s3, kb + 5, by omega,
      hsb.append ((hs1.append hs2).append (Steps.cons hs3 (Steps.zero s3))),
      h3pc, h3r1, h3r2, h3r6, by rw [h3d]; exact hbA, by rw [h3d]; exact hbB,
      by rw [h3d]; exact hbX, by rw [h3d]; exact hbSz⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hfail
    rcases hfail with hA1 | ⟨hA2, hAx⟩ | hB1 | ⟨hB2, hBx⟩
    · obtain ⟨t, k, hk, ht, hpcT⟩ := hA.1 hA1
      exact ⟨t, k, by omega, ht, hpcT⟩
    · obtain ⟨t, k, hk, ht, hpcT⟩ := hA.2.1 hA2 hAx
      exact ⟨t, k, by omega, ht, hpcT⟩
    · by_cases hAok : wA.val = 0 ∨ (2 ≤ wA.val ∧ wA.val - 1 ≠ xW.val)
      · obtain ⟨sa, ka, hka, hsa, hapc, _, haX, haF1, _⟩ := runB hAok
        have hB := exec_blkTag2_half hI hWork hTag slFail1 (by decide) (by decide) slBDense (by decide)
          (by decide) (pc2 + 25) (pc2 + 50) (by dsimp only [pc2]; omega) rfl
          (placedSlice_fetch hMidChunk (k := 2) rfl) (placedSlice_fetch hMidChunk (k := 3) rfl)
          (placedSlice_fetch hMidChunk (k := 4) rfl) hTr1 hMid1 hG1
          (placedSlice_fetch hTail (k := 0) rfl) (placedSlice_fetch hTail (k := 1) rfl)
          sa hapc f1 xW origToDenseBase wB haF1 haX hOrigHdr hMapB hwB
        obtain ⟨sb, kb, hkb, hsb, hbpc⟩ := hB.1 hB1
        exact ⟨sb, ka + kb, by omega, hsa.append hsb, hbpc⟩
      · have hAfail : wA.val = 1 ∨ (2 ≤ wA.val ∧ wA.val - 1 = xW.val) := by
          by_cases h0 : wA.val = 0
          · exact (hAok (Or.inl h0)).elim
          · by_cases h1 : wA.val = 1
            · exact Or.inl h1
            · right; refine ⟨by omega, ?_⟩
              by_cases heq : wA.val - 1 = xW.val
              · exact heq
              · exact (hAok (Or.inr ⟨by omega, heq⟩)).elim
        rcases hAfail with h1 | ⟨h2, hx2⟩
        · obtain ⟨t, k, hk, ht, hpcT⟩ := hA.1 h1; exact ⟨t, k, by omega, ht, hpcT⟩
        · obtain ⟨t, k, hk, ht, hpcT⟩ := hA.2.1 h2 hx2; exact ⟨t, k, by omega, ht, hpcT⟩
    · by_cases hAok : wA.val = 0 ∨ (2 ≤ wA.val ∧ wA.val - 1 ≠ xW.val)
      · obtain ⟨sa, ka, hka, hsa, hapc, _, haX, haF1, _⟩ := runB hAok
        have hB := exec_blkTag2_half hI hWork hTag slFail1 (by decide) (by decide) slBDense (by decide)
          (by decide) (pc2 + 25) (pc2 + 50) (by dsimp only [pc2]; omega) rfl
          (placedSlice_fetch hMidChunk (k := 2) rfl) (placedSlice_fetch hMidChunk (k := 3) rfl)
          (placedSlice_fetch hMidChunk (k := 4) rfl) hTr1 hMid1 hG1
          (placedSlice_fetch hTail (k := 0) rfl) (placedSlice_fetch hTail (k := 1) rfl)
          sa hapc f1 xW origToDenseBase wB haF1 haX hOrigHdr hMapB hwB
        obtain ⟨sb, kb, hkb, hsb, hbpc⟩ := hB.2.1 hB2 hBx
        exact ⟨sb, ka + kb, by omega, hsa.append hsb, hbpc⟩
      · have hAfail : wA.val = 1 ∨ (2 ≤ wA.val ∧ wA.val - 1 = xW.val) := by
          by_cases h0 : wA.val = 0
          · exact (hAok (Or.inl h0)).elim
          · by_cases h1 : wA.val = 1
            · exact Or.inl h1
            · right; refine ⟨by omega, ?_⟩
              by_cases heq : wA.val - 1 = xW.val
              · exact heq
              · exact (hAok (Or.inr ⟨by omega, heq⟩)).elim
        rcases hAfail with h1 | ⟨h2, hx2⟩
        · obtain ⟨t, k, hk, ht, hpcT⟩ := hA.1 h1; exact ⟨t, k, by omega, ht, hpcT⟩
        · obtain ⟨t, k, hk, ht, hpcT⟩ := hA.2.1 h2 hx2; exact ⟨t, k, by omega, ht, hpcT⟩
  · intro hwA0 hwB0
    obtain ⟨s3, k3, hk3, hs3, h3pc, h3r1, h3r2, h3r6, _, _, _, _⟩ :=
      runToTail (Or.inl hwA0) (Or.inl hwB0)
    have hlt1 : (reg s3 1).val < (reg s3 6).val := by rw [h3r1, h3r6, hwA0, oneW]; change 0 < 1; decide
    have hs4 := step_branchLt16 inp (by rw [h3pc]; exact placedSlice_fetch hTail (k := 7) rfl) (by
        change (if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59) < prog.size
        rw [ite_eq_left hlt1]; exact prog_pc_lt_const (by dsimp only [pc2]; omega))
    let s4 := { s3 with pc := if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59 }
    have h4pc : s4.pc = pc2 + 56 := by
      change (if (reg s3 1).val < (reg s3 6).val then _ else _) = _; exact ite_eq_left hlt1
    have hlt2 : (reg s4 2).val < (reg s4 6).val := by
      show (reg s3 2).val < (reg s3 6).val; rw [h3r2, h3r6, hwB0, oneW]; change 0 < 1; decide
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hTail (k := 8) rfl) (by
        change (if (reg s4 2).val < (reg s4 6).val then okPC hI hTag else pc2 + 57) < prog.size
        rw [ite_eq_left hlt2]; exact okPC_lt hI hWork hTag)
    let s5 := { s4 with pc := if (reg s4 2).val < (reg s4 6).val then okPC hI hTag else pc2 + 57 }
    have h5pc : s5.pc = okPC hI hTag := by
      change (if (reg s4 2).val < (reg s4 6).val then _ else _) = _; exact ite_eq_left hlt2
    exact ⟨s5, k3 + 2, by omega, hs3.append (Steps.cons hs4 (Steps.cons hs5 (Steps.zero s5))), h5pc⟩
  · intro hwA0 hwB2 hBnx
    obtain ⟨s3, k3, hk3, hs3, h3pc, h3r1, h3r2, h3r6, _, _, h3X, _⟩ :=
      runToTail (Or.inl hwA0) (Or.inr ⟨hwB2, hBnx⟩)
    have hlt1 : (reg s3 1).val < (reg s3 6).val := by rw [h3r1, h3r6, hwA0, oneW]; change 0 < 1; decide
    have hs4 := step_branchLt16 inp (by rw [h3pc]; exact placedSlice_fetch hTail (k := 7) rfl) (by
        change (if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59) < prog.size
        rw [ite_eq_left hlt1]; exact prog_pc_lt_const (by dsimp only [pc2]; omega))
    let s4 := { s3 with pc := if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59 }
    have h4pc : s4.pc = pc2 + 56 := by
      change (if (reg s3 1).val < (reg s3 6).val then _ else _) = _; exact ite_eq_left hlt1
    have hn2 : ¬ (reg s4 2).val < (reg s4 6).val := by
      show ¬ (reg s3 2).val < (reg s3 6).val; rw [h3r2, h3r6, oneW]; change ¬ wB.val < 1; omega
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hTail (k := 8) rfl) (by
        change (if (reg s4 2).val < (reg s4 6).val then okPC hI hTag else pc2 + 57) < prog.size
        rw [ite_eq_right hn2]; exact prog_pc_lt_const (by dsimp only [pc2]; omega))
    let s5 := { s4 with pc := if (reg s4 2).val < (reg s4 6).val then okPC hI hTag else pc2 + 57 }
    have h5pc : s5.pc = pc2 + 57 := by
      change (if (reg s4 2).val < (reg s4 6).val then _ else _) = _; exact ite_eq_right hn2
    have hs6 := step_sub16 inp (by rw [h5pc]; exact placedSlice_fetch hTail (k := 9) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc2]; omega))
    let s6 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s5 1 (sub (reg s5 2) (reg s5 6))
    have h6pc : s6.pc = pc2 + 58 := by rw [putReg_pc, h5pc]
    have h6r1 : (reg s6 1).val = wB.val - 1 := by
      have hr1 := putReg_eq_same s5 1 (sub (reg s5 2) (reg s5 6))
      have hsub := sub_no_wrap (reg s5 2) (reg s5 6)
        (by show (reg s3 6).val ≤ (reg s3 2).val; rw [h3r2, h3r6, oneW]; change 1 ≤ wB.val; omega)
      rw [hr1, hsub]; show (reg s3 2).val - (reg s3 6).val = wB.val - 1; rw [h3r2, h3r6, oneW]
    have hs7 := step_goto16 inp (by rw [h6pc]; exact placedSlice_fetch hTail (k := 10) rfl)
      (prog_pc_lt _ (by unfold okPC; omega))
    let s7 := { s6 with pc := pc6 hI hTag }
    refine ⟨s7, k3 + 4, by omega,
      hs3.append (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero s7))))),
      rfl, h6r1, ?_⟩
    change s6.data[slXDense]? = _; rw [putReg_data]; exact h3X
  · intro hwA2 hAnx hwB0
    obtain ⟨s3, k3, hk3, hs3, h3pc, h3r1, h3r2, h3r6, h3A, _, h3X, _⟩ :=
      runToTail (Or.inr ⟨hwA2, hAnx⟩) (Or.inl hwB0)
    have hn1 : ¬ (reg s3 1).val < (reg s3 6).val := by
      rw [h3r1, h3r6, oneW]; change ¬ wA.val < 1; omega
    have hs4 := step_branchLt16 inp (by rw [h3pc]; exact placedSlice_fetch hTail (k := 7) rfl) (by
        change (if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59) < prog.size
        rw [ite_eq_right hn1]; exact prog_pc_lt_const (by dsimp only [pc2]; omega))
    let s4 := { s3 with pc := if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59 }
    have h4pc : s4.pc = pc2 + 59 := by
      change (if (reg s3 1).val < (reg s3 6).val then _ else _) = _; exact ite_eq_right hn1
    have hs5 := step_sub16 inp (by rw [h4pc]; exact placedSlice_fetch hTail (k := 11) rfl)
      (prog_pc_lt_const (by rw [h4pc]; dsimp only [pc2]; omega))
    let s5 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s4 1 (sub (reg s4 1) (reg s4 6))
    have h5pc : s5.pc = pc2 + 60 := by rw [putReg_pc, h4pc]
    have h5r1 : (reg s5 1).val = wA.val - 1 := by
      have hr1 := putReg_eq_same s4 1 (sub (reg s4 1) (reg s4 6))
      have hsub := sub_no_wrap (reg s4 1) (reg s4 6)
        (by show (reg s3 6).val ≤ (reg s3 1).val; rw [h3r1, h3r6, oneW]; change 1 ≤ wA.val; omega)
      rw [hr1, hsub]; show (reg s3 1).val - (reg s3 6).val = wA.val - 1; rw [h3r1, h3r6, oneW]
    have h5r2 : reg s5 2 = wB :=
      (putReg_eq_other s4 (by decide : (2 : Fin 16) ≠ 1) _).trans h3r2
    have h5r6 : reg s5 6 = oneW hTag :=
      (putReg_eq_other s4 (by decide : (6 : Fin 16) ≠ 1) _).trans h3r6
    have h5d : s5.data = s3.data := putReg_data rfl s4 1 _
    obtain ⟨s6, hs6, h6pc, h6r, _, h6d⟩ := step_writeSlot inp slADense (by decide) 1 (by decide)
      (by rw [h5pc]; exact placedSlice_fetch hTail (k := 12) rfl)
      (by rw [h5pc]; exact placedSlice_fetch hTail (k := 13) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc2]; omega))
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc2]; omega))
    rw [h5pc] at h6pc
    have hlt2 : (reg s6 2).val < (reg s6 6).val := by
      rw [h6r 2 (by decide), h6r 6 (by decide), h5r2, h5r6, hwB0, oneW]; change 0 < 1; decide
    have hs7 := step_branchLt16 inp (by rw [h6pc]; exact placedSlice_fetch hTail (k := 14) rfl) (by
        change (if (reg s6 2).val < (reg s6 6).val then pc6 hI hTag else pc2 + 63) < prog.size
        rw [ite_eq_left hlt2]; exact prog_pc_lt _ (by unfold okPC; omega))
    let s7 := { s6 with pc := if (reg s6 2).val < (reg s6 6).val then pc6 hI hTag else pc2 + 63 }
    have h7pc : s7.pc = pc6 hI hTag := by
      change (if (reg s6 2).val < (reg s6 6).val then _ else _) = _; exact ite_eq_left hlt2
    refine ⟨s7, k3 + 5, by omega,
      hs3.append ((Steps.cons hs4 (Steps.cons hs5 (Steps.zero s5))).append
        (hs6.append (Steps.cons hs7 (Steps.zero s7)))),
      h7pc, (congrArg Fin.val (h6r 1 (by decide))).trans h5r1, ?_⟩
    change s6.data[slXDense]? = _; rw [h6d, data_set_other _ _ _ _ (by decide), h5d]; exact h3X
  · intro hwA2 hAnx hwB2 hBnx
    obtain ⟨s3, k3, hk3, hs3, h3pc, h3r1, h3r2, h3r6, h3A, h3B, h3X, h3Sz⟩ :=
      runToTail (Or.inr ⟨hwA2, hAnx⟩) (Or.inr ⟨hwB2, hBnx⟩)
    have hn1 : ¬ (reg s3 1).val < (reg s3 6).val := by
      rw [h3r1, h3r6, oneW]; change ¬ wA.val < 1; omega
    have hs4 := step_branchLt16 inp (by rw [h3pc]; exact placedSlice_fetch hTail (k := 7) rfl) (by
        change (if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59) < prog.size
        rw [ite_eq_right hn1]; exact prog_pc_lt_const (by dsimp only [pc2]; omega))
    let s4 := { s3 with pc := if (reg s3 1).val < (reg s3 6).val then pc2 + 56 else pc2 + 59 }
    have h4pc : s4.pc = pc2 + 59 := by
      change (if (reg s3 1).val < (reg s3 6).val then _ else _) = _; exact ite_eq_right hn1
    have hs5 := step_sub16 inp (by rw [h4pc]; exact placedSlice_fetch hTail (k := 11) rfl)
      (prog_pc_lt_const (by rw [h4pc]; dsimp only [pc2]; omega))
    let s5 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s4 1 (sub (reg s4 1) (reg s4 6))
    have h5pc : s5.pc = pc2 + 60 := by rw [putReg_pc, h4pc]
    have h5r1 : (reg s5 1).val = wA.val - 1 := by
      have hr1 := putReg_eq_same s4 1 (sub (reg s4 1) (reg s4 6))
      have hsub := sub_no_wrap (reg s4 1) (reg s4 6)
        (by show (reg s3 6).val ≤ (reg s3 1).val; rw [h3r1, h3r6, oneW]; change 1 ≤ wA.val; omega)
      rw [hr1, hsub]; show (reg s3 1).val - (reg s3 6).val = wA.val - 1; rw [h3r1, h3r6, oneW]
    have h5r2 : reg s5 2 = wB :=
      (putReg_eq_other s4 (by decide : (2 : Fin 16) ≠ 1) _).trans h3r2
    have h5r6 : reg s5 6 = oneW hTag :=
      (putReg_eq_other s4 (by decide : (6 : Fin 16) ≠ 1) _).trans h3r6
    have h5d : s5.data = s3.data := putReg_data rfl s4 1 _
    obtain ⟨s6, hs6, h6pc, h6r, _, h6d⟩ := step_writeSlot inp slADense (by decide) 1 (by decide)
      (by rw [h5pc]; exact placedSlice_fetch hTail (k := 12) rfl)
      (by rw [h5pc]; exact placedSlice_fetch hTail (k := 13) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc2]; omega))
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc2]; omega))
    rw [h5pc] at h6pc
    have h6r2 : reg s6 2 = wB := (h6r 2 (by decide)).trans h5r2
    have h6r6 : reg s6 6 = oneW hTag := (h6r 6 (by decide)).trans h5r6
    have hn2 : ¬ (reg s6 2).val < (reg s6 6).val := by
      rw [h6r2, h6r6, oneW]; change ¬ wB.val < 1; omega
    have hs7 := step_branchLt16 inp (by rw [h6pc]; exact placedSlice_fetch hTail (k := 14) rfl) (by
        change (if (reg s6 2).val < (reg s6 6).val then pc6 hI hTag else pc2 + 63) < prog.size
        rw [ite_eq_right hn2]; exact prog_pc_lt_const (by dsimp only [pc2]; omega))
    let s7 := { s6 with pc := if (reg s6 2).val < (reg s6 6).val then pc6 hI hTag else pc2 + 63 }
    have h7pc : s7.pc = pc2 + 63 := by
      change (if (reg s6 2).val < (reg s6 6).val then _ else _) = _; exact ite_eq_right hn2
    have hs8 := step_sub16 inp (by rw [h7pc]; exact placedSlice_fetch hTail (k := 15) rfl)
      (prog_pc_lt_const (by rw [h7pc]; dsimp only [pc2]; omega))
    let s8 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      s7 2 (sub (reg s7 2) (reg s7 6))
    have h8pc : s8.pc = pc2 + 64 := by rw [putReg_pc, h7pc]
    have h8r2 : (reg s8 2).val = wB.val - 1 := by
      have hr2 := putReg_eq_same s7 2 (sub (reg s7 2) (reg s7 6))
      have hsub := sub_no_wrap (reg s7 2) (reg s7 6)
        (by show (reg s6 6).val ≤ (reg s6 2).val; rw [h6r2, h6r6, oneW]; change 1 ≤ wB.val; omega)
      rw [hr2, hsub]; show (reg s6 2).val - (reg s6 6).val = wB.val - 1; rw [h6r2, h6r6, oneW]
    have h8d : s8.data = s6.data := putReg_data rfl s7 2 _
    obtain ⟨s9, hs9, h9pc, _, _, h9d⟩ := step_writeSlot inp slBDense (by decide) 2 (by decide)
      (by rw [h8pc]; exact placedSlice_fetch hTail (k := 16) rfl)
      (by rw [h8pc]; exact placedSlice_fetch hTail (k := 17) rfl)
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc2]; omega))
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc2]; omega))
    rw [h8pc] at h9pc
    have h9pc' : s9.pc = pc3 := by rw [h9pc]
    have htot := hs3.append ((Steps.cons hs4 (Steps.cons hs5 (Steps.zero s5))).append
      (hs6.append ((Steps.cons hs7 (Steps.cons hs8 (Steps.zero s8))).append hs9)))
    refine ⟨s9, k3 + 8, by omega, htot, h9pc', ?_, ?_, ?_, ?_⟩
    · rw [h9d, Array.size_set, h8d, h6d, Array.size_set, h5d, h3Sz]
    · rw [h9d, data_set_other _ _ _ _ (by decide), h8d, h6d, data_set_same, Option.map_some]
      exact congrArg some h5r1
    · rw [h9d, data_set_same, Option.map_some]; exact congrArg some h8r2
    · rw [h9d, data_set_other _ _ _ _ (by decide), h8d, h6d, data_set_other _ _ _ _ (by decide), h5d]; exact h3X

private theorem natSliceAt_read {bits : Nat} {mem : Array (Word bits)} {base len : Nat}
    {f : Nat → Nat} (h : NatSliceAt mem base len f) (j : Nat) (hj : j < len) :
    ∃ w : Word bits, mem[base + j]? = some w ∧ w.val = f j :=
  unwrap_map_val mem (base + j) (f j) (h.2 j hj)

private theorem lca_jumps_bound {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (a b : Fin q.count)
    (hRoot : q.reader.tables.size q.reader.tables.root ≤ q.count)
    (hq : q.count ≤ g.vertexCount) :
    (q.reader.lca a b).jumps ≤ 2 * OracleContract.L g.vertexCount := by
  have hpow := q.reader.lca_pow_jumps_le a b
  have hqle : q.reader.tables.size q.reader.tables.root ≤ g.vertexCount :=
    Nat.le_trans hRoot hq
  have hmul : q.reader.tables.size q.reader.tables.root * q.reader.tables.size q.reader.tables.root ≤
      g.vertexCount * g.vertexCount := Nat.mul_le_mul hqle hqle
  have hltL : g.vertexCount < 2 ^ OracleContract.L g.vertexCount := by
    have hlog : g.vertexCount + 1 < 2 ^ OracleContract.L g.vertexCount :=
      (Nat.log2_lt (by omega)).mp (Nat.lt_succ_self (Nat.log2 (g.vertexCount + 1)))
    omega
  have hsq : g.vertexCount * g.vertexCount < 2 ^ (2 * OracleContract.L g.vertexCount) := by
    by_cases h0 : g.vertexCount = 0
    · rw [h0, Nat.zero_mul]; exact Nat.pow_pos (by decide : 0 < 2)
    · have hpos : 0 < g.vertexCount := Nat.pos_of_ne_zero h0
      have h1 := Nat.mul_lt_mul_of_pos_right hltL hpos
      have h2 : (2 ^ OracleContract.L g.vertexCount) * g.vertexCount <
          (2 ^ OracleContract.L g.vertexCount) * (2 ^ OracleContract.L g.vertexCount) :=
        Nat.mul_lt_mul_of_pos_left hltL (Nat.pow_pos (by decide : 0 < 2))
      have h3 := Nat.lt_trans h1 h2
      rwa [← Nat.pow_add, ← Nat.two_mul] at h3
  have h2lt : 2 ^ (q.reader.lca a b).jumps < 2 ^ (2 * OracleContract.L g.vertexCount) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hpow hmul) hsq
  have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h2lt
  exact Nat.le_of_lt hlt

private noncomputable def packedOfValid {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hI : I.size ≤ 2 ^ bits)
    (q : OriginalReader g r) (Hdr : StaticHeaderSpec I g.vertexCount q.count)
    (hHead : NatSliceAt I Hdr.headBase q.count
      (fun d => if hd : d < q.count then (q.reader.tables.head ⟨d, hd⟩).val else 0))
    (hParent : NatSliceAt I Hdr.domParentBase q.count
      (fun d => if hd : d < q.count then (q.reader.tables.parent ⟨d, hd⟩).val else 0))
    (hDepth : NatSliceAt I Hdr.domDepthBase q.count
      (fun d => if hd : d < q.count then q.reader.tables.depth ⟨d, hd⟩ else 0))
    (headBaseW parentBaseW depthBaseW : Word bits)
    (hHB : I[hdrHead]? = some headBaseW) (hHBv : headBaseW.val = Hdr.headBase)
    (hPB : I[hdrDomParent]? = some parentBaseW) (hPBv : parentBaseW.val = Hdr.domParentBase)
    (hDB : I[hdrDomDepth]? = some depthBaseW) (hDBv : depthBaseW.val = Hdr.domDepthBase) :
    EX53.Packed (bits := bits) (cap := I.size) (fit := hI) ⟨I, rfl⟩ q.reader.tables where
  idsFit := Nat.le_trans Hdr.q_le (Nat.le_trans (Nat.le_trans (Nat.le_add_left _ _) Hdr.origToDense_fit) hI)
  headersFit := Nat.le_trans (by decide : 3 ≤ oracleHeaderSize) Hdr.hdr_fit
  depthFits := fun v => by
    obtain ⟨w, _, hwv⟩ := natSliceAt_read hDepth v.val v.isLt
    rw [dite_eq_left v.isLt] at hwv
    rw [← hwv]
    exact w.isLt
  headBase := headBaseW
  parentBase := parentBaseW
  depthBase := depthBaseW
  headHeader := hHB
  parentHeader := hPB
  depthHeader := hDB
  headCell := fun v => by
    obtain ⟨w, hw, hwv⟩ := natSliceAt_read hHead v.val v.isLt
    rw [dite_eq_left v.isLt] at hwv
    rw [hHBv]
    exact hw.trans (congrArg some (Fin.ext hwv))
  parentCell := fun v => by
    obtain ⟨w, hw, hwv⟩ := natSliceAt_read hParent v.val v.isLt
    rw [dite_eq_left v.isLt] at hwv
    rw [hPBv]
    exact hw.trans (congrArg some (Fin.ext hwv))
  depthCell := fun v => by
    obtain ⟨w, hw, hwv⟩ := natSliceAt_read hDepth v.val v.isLt
    rw [dite_eq_left v.isLt] at hwv
    rw [hDBv]
    exact hw.trans (congrArg some (Fin.ext hwv))

private theorem exec_blkRoutePair {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits)
    (hTag : TagsFit bits) (q : OriginalReader g r)
    (Hdr : StaticHeaderSpec I g.vertexCount q.count)
    (hRootSz : q.reader.tables.size q.reader.tables.root ≤ q.count)
    (hHead : NatSliceAt I Hdr.headBase q.count
      (fun d => if hd : d < q.count then (q.reader.tables.head ⟨d, hd⟩).val else 0))
    (hParent : NatSliceAt I Hdr.domParentBase q.count
      (fun d => if hd : d < q.count then (q.reader.tables.parent ⟨d, hd⟩).val else 0))
    (hDepth : NatSliceAt I Hdr.domDepthBase q.count
      (fun d => if hd : d < q.count then q.reader.tables.depth ⟨d, hd⟩ else 0))
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (hStop : NatSliceAt I Hdr.stopBase q.count
      (fun d => if hd : d < q.count then q.reader.stop ⟨d, hd⟩ else 0))
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc3)
    (aDense bDense : Fin q.count) (aW bW xW : Word bits)
    (haS : s.data[slADense]? = some aW) (hbS : s.data[slBDense]? = some bW)
    (hxS : s.data[slXDense]? = some xW)
    (haV : aW.val = aDense.val) (hbV : bW.val = bDense.val) :
    (q.reader.isAncestor aDense bDense = true →
      ∃ t k, k ≤ 23 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc6 hI hTag ∧ (reg t 1).val = aDense.val ∧ t.data[slXDense]? = some xW) ∧
    (q.reader.isAncestor aDense bDense = false → q.reader.isAncestor bDense aDense = true →
      ∃ t k, k ≤ 43 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc6 hI hTag ∧ (reg t 1).val = bDense.val ∧ t.data[slXDense]? = some xW) ∧
    (q.reader.isAncestor aDense bDense = false → q.reader.isAncestor bDense aDense = false →
      ∃ t k, k ≤ 28 * OracleContract.L g.vertexCount + 80 ∧
        Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
        t.pc = pc4 ∧
        (t.data[slD]?).map Fin.val = some (q.reader.lca aDense bDense).node.val ∧
        t.data[slADense]? = some aW ∧
        t.data[slBDense]? = some bW ∧
        t.data[slXDense]? = some xW ∧
        t.data.size = queryWorkCap) := by
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have h3 := place_blk3 hI hWork hTag
  have hA1Sz : (ancestorCheckBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
      (zeroW bits) (oneW hTag) 1 2 (pc3 + 4) (pc3 + 20)).size = 16 :=
    ancestorCheckBlock_size rfl _ _ _ _ 1 2 (pc3 + 4) (pc3 + 20)
  have hA2Sz : (ancestorCheckBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
      (zeroW bits) (oneW hTag) 1 2 (pc3 + 29) (pc3 + 45)).size = 16 :=
    ancestorCheckBlock_size rfl _ _ _ _ 1 2 (pc3 + 29) (pc3 + 45)
  have hLcaSz : (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (EX53.layout bits I.size hI).registerCount = 16))
      (pc3 + 68) (pc3 + 100) (EX53.program hI)).size = 32 := by
    simp [liftMap]; rfl
  have hC0 : PlacedSlice
      (#[.imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 2 15] :
        Program (codeLayout bits I.size hI hWork))
      (oracleQueryProgram hI hWork hTag) pc3 := by
    unfold blkRoutePair at h3
    exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h3)))))
  have hC1 : PlacedSlice
      (ancestorCheckBlock (L := codeLayout bits I.size hI hWork) rfl
        (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
        (zeroW bits) (oneW hTag) 1 2 (pc3 + 4) (pc3 + 20))
      (oracleQueryProgram hI hWork hTag) (pc3 + 4) := by
    unfold blkRoutePair at h3
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left h3))))) rfl rfl
  have hC2 : PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 0 6 (pc3 + 25) (pc3 + 22),
        .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
        .goto (pc6 hI hTag),
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slADense (by decide)), .loadData 2 15] :
        Program (codeLayout bits I.size hI hWork))
      (oracleQueryProgram hI hWork hTag) (pc3 + 20) := by
    unfold blkRoutePair at h3
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left h3)))) (by rw [Array.size_append, hA1Sz]; rfl) rfl
  have hC3 : PlacedSlice
      (ancestorCheckBlock (L := codeLayout bits I.size hI hWork) rfl
        (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
        (zeroW bits) (oneW hTag) 1 2 (pc3 + 29) (pc3 + 45))
      (oracleQueryProgram hI hWork hTag) (pc3 + 29) := by
    unfold blkRoutePair at h3
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h3)))
      (by rw [Array.size_append, Array.size_append, hA1Sz]; rfl) rfl
  have hC4 : PlacedSlice
      (#[.imm 6 (oneW hTag),
        .branchLt 0 6 (pc3 + 50) (pc3 + 47),
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
        .goto (pc6 hI hTag),
        .imm 15 (slotW hWork slADense (by decide)), .loadData 0 15,
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
        .imm 2 (hdrW hWork hdrHead (by decide)),
        .imm 3 (hdrW hWork hdrDomParent (by decide)),
        .imm 4 (hdrW hWork hdrDomDepth (by decide)),
        .imm 5 (zeroW bits), .imm 6 (zeroW bits), .imm 7 (zeroW bits),
        .imm 8 (zeroW bits), .imm 9 (zeroW bits), .imm 10 (zeroW bits),
        .imm 11 (zeroW bits), .imm 12 (zeroW bits), .imm 13 (zeroW bits),
        .imm 14 (zeroW bits), .imm 15 (zeroW bits)] :
        Program (codeLayout bits I.size hI hWork))
      (oracleQueryProgram hI hWork hTag) (pc3 + 45) := by
    unfold blkRoutePair at h3
    exact placedSlice_append_right_at
      (placedSlice_append_left (placedSlice_append_left h3))
      (by rw [Array.size_append, Array.size_append, Array.size_append, hA1Sz, hA2Sz]; rfl) rfl
  have hC5 : PlacedSlice
      (liftMap (L := codeLayout bits I.size hI hWork)
        (ρ16 rfl (rfl : (EX53.layout bits I.size hI).registerCount = 16))
        (pc3 + 68) (pc3 + 100) (EX53.program hI))
      (oracleQueryProgram hI hWork hTag) (pc3 + 68) := by
    unfold blkRoutePair at h3
    exact placedSlice_append_right_at (placedSlice_append_left h3)
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        hA1Sz, hA2Sz]; rfl) rfl
  have hC6 : PlacedSlice
      (#[.imm 15 (slotW hWork slD (by decide)), .storeData 15 0] :
        Program (codeLayout bits I.size hI hWork))
      (oracleQueryProgram hI hWork hTag) (pc3 + 100) := by
    unfold blkRoutePair at h3
    exact placedSlice_append_right_at h3
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, hA1Sz, hA2Sz, hLcaSz]; rfl) rfl
  obtain ⟨entryBaseW, hEB, hEBv⟩ := unwrap_map_val I hdrEntry Hdr.entryBase Hdr.hEntryBase
  obtain ⟨stopBaseW, hSB, hSBv⟩ := unwrap_map_val I hdrStop Hdr.stopBase Hdr.hStopBase
  obtain ⟨entA, hEntA, hEntAv⟩ := natSliceAt_read hEntry aDense.val aDense.isLt
  obtain ⟨entB, hEntB, hEntBv⟩ := natSliceAt_read hEntry bDense.val bDense.isLt
  obtain ⟨stpA, hStpA, hStpAv⟩ := natSliceAt_read hStop aDense.val aDense.isLt
  obtain ⟨stpB, hStpB, hStpBv⟩ := natSliceAt_read hStop bDense.val bDense.isLt
  rw [dite_eq_left aDense.isLt] at hEntAv hStpAv
  rw [dite_eq_left bDense.isLt] at hEntBv hStpBv
  have hHdrE : (hdrW hWork hdrEntry (by decide) : Word bits).val = hdrEntry := rfl
  have hHdrS : (hdrW hWork hdrStop (by decide) : Word bits).val = hdrStop := rfl
  have hOne : (oneW hTag : Word bits).val = 1 := rfl
  have hZero : (zeroW bits : Word bits).val = 0 := rfl
  obtain ⟨s1, hs1, h1pc, _, h1r1, _, h1d⟩ := step_readSlot (s := s) inp slADense (by decide) 1 (by decide) aW haS
    (by rw [hpc]; exact placedSlice_fetch hC0 (k := 0) rfl)
    (by rw [hpc]; exact placedSlice_fetch hC0 (k := 1) rfl)
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc3]; omega))
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc3]; omega))
  rw [hpc] at h1pc
  obtain ⟨s2, hs2, h2pc, h2r, h2r2, _, h2d⟩ := step_readSlot (s := s1) inp slBDense (by decide) 2 (by decide) bW
    (by rw [h1d]; exact hbS)
    (by rw [h1pc]; exact placedSlice_fetch hC0 (k := 2) rfl)
    (by rw [h1pc]; exact placedSlice_fetch hC0 (k := 3) rfl)
    (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc3]; omega))
    (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc3]; omega))
  rw [h1pc] at h2pc
  have h2r1 : reg s2 1 = aW := (h2r 1 (by decide) (by decide)).trans h1r1
  have h2d' : s2.data = s.data := h2d.trans h1d
  obtain ⟨s3, k1, hk1, hs3, h3pc, h3r0, h3d⟩ := ancestorCheckBlock_spec (h16 := rfl)
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide)) (zeroW bits) (oneW hTag)
    hZero hOne 1 2 (by decide) (by decide) hC1 (prog_pc_lt_const (by dsimp only [pc3]; omega))
    inp s2 h2pc (by rw [hHdrE]; exact hEB) (by rw [hHdrS]; exact hSB)
    (by rw [reg_r16, h2r1, haV, hEBv]; exact hEntA)
    (by rw [reg_r16, h2r2, hbV, hEBv]; exact hEntB)
    (by rw [reg_r16, h2r1, haV, hSBv]; exact hStpA)
  have h3d' : s3.data = s.data := h3d.trans h2d'
  have hs4 := step_imm16 inp (by rw [h3pc]; exact placedSlice_fetch hC2 (k := 0) rfl)
    (prog_pc_lt_const (by rw [h3pc]; dsimp only [pc3]; omega))
  let s4 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s3 6 (oneW hTag)
  have h4pc : s4.pc = pc3 + 21 := by rw [putReg_pc, h3pc]
  have h4r0 : (reg s4 0).val =
      if q.reader.isAncestor aDense bDense = true then 1 else 0 := by
    rw [putReg_eq_other s3 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s3 0, h3r0]
    rw [hEntAv, hEntBv, hStpAv]
    have hanc := (q.reader.isAncestor_exact aDense bDense).trans (q.reader.ancestor_iff_interval aDense bDense)
    by_cases hA : q.reader.isAncestor aDense bDense = true
    · have hI := hanc.mp hA; rw [ite_eq_left hI, ite_eq_left hA]
    · have hnI : ¬ (q.reader.entry aDense ≤ q.reader.entry bDense ∧
          q.reader.entry bDense < q.reader.stop aDense) := fun h => hA (hanc.mpr h)
      rw [ite_eq_right hnI, ite_eq_right hA]
  have h4r6 : reg s4 6 = oneW hTag := putReg_eq_same s3 6 _
  have h4d : s4.data = s.data := by rw [putReg_data, h3d']
  have hpre1 : Steps (oracleQueryProgram hI hWork hTag) inp (k1 + 5) s s4 := by
    have hk_eq : 2 + 2 + k1 + Nat.succ 0 = k1 + 5 := by omega
    rw [← hk_eq]
    exact ((hs1.append hs2).append hs3).append (Steps.cons hs4 (Steps.zero s4))
  have hNotA : q.reader.isAncestor aDense bDense = false →
      ∃ s9 k2, k2 ≤ 25 ∧ Steps (oracleQueryProgram hI hWork hTag) inp (k1 + k2) s s9 ∧
        s9.pc = pc3 + 46 ∧
        (reg s9 0).val = (if q.reader.isAncestor bDense aDense = true then 1 else 0) ∧
        reg s9 6 = oneW hTag ∧ s9.data = s.data := by
    intro hAfalse
    have hlt1 : (reg s4 0).val < (reg s4 6).val := by
      rw [h4r0, h4r6, hAfalse, oneW]; change (if false = true then 1 else 0) < 1; decide
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hC2 (k := 1) rfl) (by
        change (if (reg s4 0).val < (reg s4 6).val then pc3 + 25 else pc3 + 22) < _
        rw [ite_eq_left hlt1]; exact prog_pc_lt_const (by dsimp only [pc3]; omega))
    let s5 := { s4 with pc := if (reg s4 0).val < (reg s4 6).val then pc3 + 25 else pc3 + 22 }
    have h5pc : s5.pc = pc3 + 25 := by
      change (if (reg s4 0).val < (reg s4 6).val then _ else _) = _; exact ite_eq_left hlt1
    have h5d : s5.data = s.data := h4d
    obtain ⟨s6, hs6, h6pc, _, h6r1, _, h6d⟩ := step_readSlot (s := s5) inp slBDense (by decide) 1 (by decide) bW
      (by rw [h5d]; exact hbS)
      (by rw [h5pc]; exact placedSlice_fetch hC2 (k := 5) rfl)
      (by rw [h5pc]; exact placedSlice_fetch hC2 (k := 6) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc3]; omega))
    rw [h5pc] at h6pc
    obtain ⟨s7, hs7, h7pc, h7r, h7r2, _, h7d⟩ := step_readSlot (s := s6) inp slADense (by decide) 2 (by decide) aW
      (by rw [h6d, h5d]; exact haS)
      (by rw [h6pc]; exact placedSlice_fetch hC2 (k := 7) rfl)
      (by rw [h6pc]; exact placedSlice_fetch hC2 (k := 8) rfl)
      (prog_pc_lt_const (by rw [h6pc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [h6pc]; dsimp only [pc3]; omega))
    rw [h6pc] at h7pc
    have h7r1 : reg s7 1 = bW := (h7r 1 (by decide) (by decide)).trans h6r1
    have h7d' : s7.data = s.data := by rw [h7d, h6d, h5d]
    obtain ⟨s8, k2', hk2', hs8, h8pc, h8r0, h8d⟩ := ancestorCheckBlock_spec (h16 := rfl)
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide)) (zeroW bits) (oneW hTag)
      hZero hOne 1 2 (by decide) (by decide) hC3 (prog_pc_lt_const (by dsimp only [pc3]; omega))
      inp s7 h7pc (by rw [hHdrE]; exact hEB) (by rw [hHdrS]; exact hSB)
      (by rw [reg_r16, h7r1, hbV, hEBv]; exact hEntB)
      (by rw [reg_r16, h7r2, haV, hEBv]; exact hEntA)
      (by rw [reg_r16, h7r1, hbV, hSBv]; exact hStpB)
    have h8d' : s8.data = s.data := h8d.trans h7d'
    have hs9 := step_imm16 inp (by rw [h8pc]; exact placedSlice_fetch hC4 (k := 0) rfl)
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc3]; omega))
    let s9 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s8 6 (oneW hTag)
    have h9pc : s9.pc = pc3 + 46 := by rw [putReg_pc, h8pc]
    have h9r0 : (reg s9 0).val = if q.reader.isAncestor bDense aDense = true then 1 else 0 := by
      rw [putReg_eq_other s8 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s8 0, h8r0]
      rw [hEntBv, hEntAv, hStpBv]
      have hanc := (q.reader.isAncestor_exact bDense aDense).trans (q.reader.ancestor_iff_interval bDense aDense)
      by_cases hB : q.reader.isAncestor bDense aDense = true
      · have hI := hanc.mp hB; rw [ite_eq_left hI, ite_eq_left hB]
      · have hnI : ¬ (q.reader.entry bDense ≤ q.reader.entry aDense ∧
            q.reader.entry aDense < q.reader.stop bDense) := fun h => hB (hanc.mpr h)
        rw [ite_eq_right hnI, ite_eq_right hB]
    have h9r6 : reg s9 6 = oneW hTag := putReg_eq_same s8 6 _
    have h9d : s9.data = s.data := by rw [putReg_data, h8d']
    refine ⟨s9, k2' + 11, by omega, ?_, h9pc, h9r0, h9r6, h9d⟩
    have hk_eq : k1 + 5 + Nat.succ 0 + (2 + 2) + k2' + Nat.succ 0 = k1 + (k2' + 11) := by omega
    rw [← hk_eq]
    exact (((hpre1.append (Steps.cons hs5 (Steps.zero s5))).append (hs6.append hs7)).append hs8).append
      (Steps.cons hs9 (Steps.zero s9))
  refine ⟨?_, ?_, ?_⟩
  · intro hAB
    have hnlt : ¬ (reg s4 0).val < (reg s4 6).val := by
      rw [h4r0, h4r6, hAB, oneW]; change ¬ (if true = true then 1 else 0) < 1; decide
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hC2 (k := 1) rfl) (by
        change (if (reg s4 0).val < (reg s4 6).val then pc3 + 25 else pc3 + 22) < _
        rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by dsimp only [pc3]; omega))
    let s5 := { s4 with pc := if (reg s4 0).val < (reg s4 6).val then pc3 + 25 else pc3 + 22 }
    have h5pc : s5.pc = pc3 + 22 := by
      change (if (reg s4 0).val < (reg s4 6).val then _ else _) = _; exact ite_eq_right hnlt
    obtain ⟨s6, hs6, h6pc, _, h6r1, _, h6d⟩ := step_readSlot (s := s5) inp slADense (by decide) 1 (by decide) aW
      (by rw [h4d]; exact haS)
      (by rw [h5pc]; exact placedSlice_fetch hC2 (k := 2) rfl)
      (by rw [h5pc]; exact placedSlice_fetch hC2 (k := 3) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc3]; omega))
    rw [h5pc] at h6pc
    have hs7 := step_goto16 inp (by rw [h6pc]; exact placedSlice_fetch hC2 (k := 4) rfl)
      (prog_pc_lt _ (by unfold okPC; omega))
    let s7 := { s6 with pc := pc6 hI hTag }
    refine ⟨s7, k1 + 9, by omega,
      (hpre1.append (Steps.cons hs5 (Steps.zero s5))).append
        (hs6.append (Steps.cons hs7 (Steps.zero s7))),
      rfl, ?_, ?_⟩
    · change (reg s6 1).val = aDense.val; rw [h6r1, haV]
    · change s6.data[slXDense]? = some xW; rw [h6d, h4d]; exact hxS
  · intro hAfalse hBA
    obtain ⟨s9, k2, hk2, hs9, h9pc, h9r0, h9r6, h9d⟩ := hNotA hAfalse
    have hnlt : ¬ (reg s9 0).val < (reg s9 6).val := by
      rw [h9r0, h9r6, hBA, oneW]; change ¬ (if true = true then 1 else 0) < 1; decide
    have hs10 := step_branchLt16 inp (by rw [h9pc]; exact placedSlice_fetch hC4 (k := 1) rfl) (by
        change (if (reg s9 0).val < (reg s9 6).val then pc3 + 50 else pc3 + 47) < _
        rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by dsimp only [pc3]; omega))
    let s10 := { s9 with pc := if (reg s9 0).val < (reg s9 6).val then pc3 + 50 else pc3 + 47 }
    have h10pc : s10.pc = pc3 + 47 := by
      change (if (reg s9 0).val < (reg s9 6).val then _ else _) = _; exact ite_eq_right hnlt
    obtain ⟨s11, hs11, h11pc, _, h11r1, _, h11d⟩ := step_readSlot (s := s10) inp slBDense (by decide) 1 (by decide) bW
      (by rw [h9d]; exact hbS)
      (by rw [h10pc]; exact placedSlice_fetch hC4 (k := 2) rfl)
      (by rw [h10pc]; exact placedSlice_fetch hC4 (k := 3) rfl)
      (prog_pc_lt_const (by rw [h10pc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [h10pc]; dsimp only [pc3]; omega))
    rw [h10pc] at h11pc
    have hs12 := step_goto16 inp (by rw [h11pc]; exact placedSlice_fetch hC4 (k := 4) rfl)
      (prog_pc_lt _ (by unfold okPC; omega))
    let s12 := { s11 with pc := pc6 hI hTag }
    refine ⟨s12, k1 + k2 + 4, by omega,
      (hs9.append (Steps.cons hs10 (Steps.zero s10))).append
        (hs11.append (Steps.cons hs12 (Steps.zero s12))),
      rfl, ?_, ?_⟩
    · change (reg s11 1).val = bDense.val; rw [h11r1, hbV]
    · change s11.data[slXDense]? = some xW; rw [h11d, h9d]; exact hxS
  · intro hAfalse hBfalse
    obtain ⟨s9, k2, hk2, hs9, h9pc, h9r0, h9r6, h9d⟩ := hNotA hAfalse
    have hlt2 : (reg s9 0).val < (reg s9 6).val := by
      rw [h9r0, h9r6, hBfalse, oneW]; change (if false = true then 1 else 0) < 1; decide
    have hs10 := step_branchLt16 inp (by rw [h9pc]; exact placedSlice_fetch hC4 (k := 1) rfl) (by
        change (if (reg s9 0).val < (reg s9 6).val then pc3 + 50 else pc3 + 47) < _
        rw [ite_eq_left hlt2]; exact prog_pc_lt_const (by dsimp only [pc3]; omega))
    let s10 := { s9 with pc := if (reg s9 0).val < (reg s9 6).val then pc3 + 50 else pc3 + 47 }
    have h10pc : s10.pc = pc3 + 50 := by
      change (if (reg s9 0).val < (reg s9 6).val then _ else _) = _; exact ite_eq_left hlt2
    obtain ⟨s11, hs11, h11pc, _, h11r0, _, h11d⟩ := step_readSlot (s := s10) inp slADense (by decide) 0 (by decide) aW
      (by rw [h9d]; exact haS)
      (by rw [h10pc]; exact placedSlice_fetch hC4 (k := 5) rfl)
      (by rw [h10pc]; exact placedSlice_fetch hC4 (k := 6) rfl)
      (prog_pc_lt_const (by rw [h10pc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [h10pc]; dsimp only [pc3]; omega))
    rw [h10pc] at h11pc
    obtain ⟨s12, hs12, h12pc, h12r, h12r1, _, h12d⟩ := step_readSlot (s := s11) inp slBDense (by decide) 1 (by decide) bW
      (by rw [h11d, h9d]; exact hbS)
      (by rw [h11pc]; exact placedSlice_fetch hC4 (k := 7) rfl)
      (by rw [h11pc]; exact placedSlice_fetch hC4 (k := 8) rfl)
      (prog_pc_lt_const (by rw [h11pc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [h11pc]; dsimp only [pc3]; omega))
    rw [h11pc] at h12pc
    have h12r0 : reg s12 0 = aW := (h12r 0 (by decide) (by decide)).trans h11r0
    have h12d' : s12.data = s.data := by rw [h12d, h11d, h9d]
    have immF : ∀ (k : Nat) (_hk : 9 ≤ k ∧ k ≤ 22)
        (d : Fin 16) (val : Word bits),
        (#[.imm 6 (oneW hTag),
          .branchLt 0 6 (pc3 + 50) (pc3 + 47),
          .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
          .goto (pc6 hI hTag),
          .imm 15 (slotW hWork slADense (by decide)), .loadData 0 15,
          .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
          .imm 2 (hdrW hWork hdrHead (by decide)),
          .imm 3 (hdrW hWork hdrDomParent (by decide)),
          .imm 4 (hdrW hWork hdrDomDepth (by decide)),
          .imm 5 (zeroW bits), .imm 6 (zeroW bits), .imm 7 (zeroW bits),
          .imm 8 (zeroW bits), .imm 9 (zeroW bits), .imm 10 (zeroW bits),
          .imm 11 (zeroW bits), .imm 12 (zeroW bits), .imm 13 (zeroW bits),
          .imm 14 (zeroW bits), .imm 15 (zeroW bits)] :
          Program (codeLayout bits I.size hI hWork))[k]? = some (.imm d val) →
        ∀ u : State (codeLayout bits I.size hI hWork), u.pc = pc3 + (45 + k) →
        ∃ u', step (oracleQueryProgram hI hWork hTag) inp u = some (.next u') ∧
          u'.pc = pc3 + (45 + (k + 1)) ∧
          (∀ j : Fin 16, reg u' (r16 rfl j) = if j = d then val else reg u (r16 rfl j)) ∧
          u'.data = u.data := by
      intro k _hk d val hf u hupc
      have hfetch : (oracleQueryProgram hI hWork hTag)[u.pc]? = some (.imm d val) := by
        rw [hupc, ← Nat.add_assoc]; exact placedSlice_fetch hC4 (k := k) hf
      have hst := step_imm16 inp hfetch (prog_pc_lt_const (by rw [hupc]; dsimp only [pc3]; omega))
      let u' := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) u d val
      refine ⟨u', hst, by rw [putReg_pc, hupc]; omega, fun j => ?_, putReg_data rfl u d val⟩
      rw [reg_r16]; exact reg_putReg rfl u d j val
    obtain ⟨u2, hu2, hu2pc, hu2r, hu2d⟩ :=
      immF 9 (by omega) 2 (hdrW hWork hdrHead (by decide)) rfl s12 h12pc
    obtain ⟨u3, hu3, hu3pc, hu3r, hu3d⟩ :=
      immF 10 (by omega) 3 (hdrW hWork hdrDomParent (by decide)) rfl u2 hu2pc
    obtain ⟨u4, hu4, hu4pc, hu4r, hu4d⟩ :=
      immF 11 (by omega) 4 (hdrW hWork hdrDomDepth (by decide)) rfl u3 hu3pc
    obtain ⟨u5, hu5, hu5pc, hu5r, hu5d⟩ := immF 12 (by omega) 5 (zeroW bits) rfl u4 hu4pc
    obtain ⟨u6, hu6, hu6pc, hu6r, hu6d⟩ := immF 13 (by omega) 6 (zeroW bits) rfl u5 hu5pc
    obtain ⟨u7, hu7, hu7pc, hu7r, hu7d⟩ := immF 14 (by omega) 7 (zeroW bits) rfl u6 hu6pc
    obtain ⟨u8, hu8, hu8pc, hu8r, hu8d⟩ := immF 15 (by omega) 8 (zeroW bits) rfl u7 hu7pc
    obtain ⟨u9, hu9, hu9pc, hu9r, hu9d⟩ := immF 16 (by omega) 9 (zeroW bits) rfl u8 hu8pc
    obtain ⟨u10, hu10, hu10pc, hu10r, hu10d⟩ := immF 17 (by omega) 10 (zeroW bits) rfl u9 hu9pc
    obtain ⟨u11, hu11, hu11pc, hu11r, hu11d⟩ := immF 18 (by omega) 11 (zeroW bits) rfl u10 hu10pc
    obtain ⟨u12, hu12, hu12pc, hu12r, hu12d⟩ := immF 19 (by omega) 12 (zeroW bits) rfl u11 hu11pc
    obtain ⟨u13, hu13, hu13pc, hu13r, hu13d⟩ := immF 20 (by omega) 13 (zeroW bits) rfl u12 hu12pc
    obtain ⟨u14, hu14, hu14pc, hu14r, hu14d⟩ := immF 21 (by omega) 14 (zeroW bits) rfl u13 hu13pc
    obtain ⟨u15, hu15, hu15pc, hu15r, hu15d⟩ := immF 22 (by omega) 15 (zeroW bits) rfl u14 hu14pc
    have hu15d' : u15.data = s.data := by
      rw [hu15d, hu14d, hu13d, hu12d, hu11d, hu10d, hu9d, hu8d, hu7d, hu6d, hu5d, hu4d, hu3d, hu2d, h12d']
    have hImmSteps : Steps (oracleQueryProgram hI hWork hTag) inp 14 s12 u15 :=
      Steps.cons hu2 (Steps.cons hu3 (Steps.cons hu4 (Steps.cons hu5 (Steps.cons hu6 (Steps.cons hu7
        (Steps.cons hu8 (Steps.cons hu9 (Steps.cons hu10 (Steps.cons hu11 (Steps.cons hu12
          (Steps.cons hu13 (Steps.cons hu14 (Steps.cons hu15 (Steps.zero u15))))))))))))))
    obtain ⟨headBaseW, hHB, hHBv⟩ := unwrap_map_val I hdrHead Hdr.headBase Hdr.hHeadBase
    obtain ⟨parentBaseW, hPB, hPBv⟩ := unwrap_map_val I hdrDomParent Hdr.domParentBase Hdr.hDomParentBase
    obtain ⟨depthBaseW, hDB, hDBv⟩ := unwrap_map_val I hdrDomDepth Hdr.domDepthBase Hdr.hDomDepthBase
    let P := packedOfValid hI q Hdr hHead hParent hDepth headBaseW parentBaseW depthBaseW
      hHB hHBv hPB hPBv hDB hDBv
    have hregInit : ∀ i : Fin 16,
        reg u15 (r16 (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) i) =
          reg (EX53.initial P aDense bDense) i := by
      intro i
      have hinit : reg (EX53.initial P aDense bDense) i =
          (Array.ofFn (fun j : Fin 16 =>
            let f0 : Fin 16 → Word bits := fun _ => zeroW bits
            let f1 := fun j : Fin 16 => if j = 0 then P.node aDense else f0 j
            let f2 := fun j : Fin 16 => if j = 1 then P.node bDense else f1 j
            let f3 := fun j : Fin 16 => if j = 3 then hdrW hWork hdrDomParent (by decide) else f2 j
            if j = 4 then hdrW hWork hdrDomDepth (by decide) else f3 j))[i.val]'(by simp) := rfl
      rw [Array.getElem_ofFn] at hinit
      rw [hinit, hu15r i, hu14r i, hu13r i, hu12r i, hu11r i, hu10r i, hu9r i, hu8r i,
        hu7r i, hu6r i, hu5r i, hu4r i, hu3r i, hu2r i]
      rcases i with ⟨v, hv⟩
      match v with
      | 0 => exact Fin.ext (by change (reg s12 0).val = (P.node aDense).val; rw [h12r0]; exact haV)
      | 1 => exact Fin.ext (by change (reg s12 1).val = (P.node bDense).val; rw [h12r1]; exact hbV)
      | 2 => exact Fin.ext rfl
      | 3 => exact Fin.ext rfl
      | 4 => exact Fin.ext rfl
      | 5 => exact Fin.ext rfl
      | 6 => exact Fin.ext rfl
      | 7 => exact Fin.ext rfl
      | 8 => exact Fin.ext rfl
      | 9 => exact Fin.ext rfl
      | 10 => exact Fin.ext rfl
      | 11 => exact Fin.ext rfl
      | 12 => exact Fin.ext rfl
      | 13 => exact Fin.ext rfl
      | 14 => exact Fin.ext rfl
      | 15 => exact Fin.ext rfl
      | _ + 16 => exact False.elim (by omega)
    have hu15pc' : u15.pc = pc3 + 68 := by rw [hu15pc]
    obtain ⟨sLca, hsLca, hLcaPc, hLcaR0, hLcaD⟩ := lifted_staticLCA (h16 := rfl) hC5
      (prog_pc_lt_const (by dsimp only [pc3]; omega)) inp u15 hu15pc' P
      (q.reader.lca_execution aDense bDense) hregInit
    obtain ⟨sFin, hsFin, hFinPc, _, _, hFinD⟩ := step_writeSlot inp slD (by decide) 0 (by decide)
      (by rw [hLcaPc]; exact placedSlice_fetch hC6 (k := 0) rfl)
      (by rw [hLcaPc]; exact placedSlice_fetch hC6 (k := 1) rfl)
      (prog_pc_lt_const (by rw [hLcaPc]; dsimp only [pc3]; omega))
      (prog_pc_lt_const (by rw [hLcaPc]; dsimp only [pc3]; omega))
    rw [hLcaPc] at hFinPc
    have hFinPc' : sFin.pc = pc4 := by rw [hFinPc]
    have hjumps := lca_jumps_bound q aDense bDense hRootSz Hdr.q_le
    have htot := (((((hs9.append (Steps.cons hs10 (Steps.zero s10))).append
      (hs11.append hs12)).append hImmSteps).append hsLca).append hsFin)
    refine ⟨sFin, _, by omega, htot, hFinPc', ?_, ?_, ?_, ?_, sFin.data_size⟩
    · rw [hFinD, data_set_same, Option.map_some, ← reg_r16 sLca 0, hLcaR0]; rfl
    · rw [hFinD, data_set_other _ _ _ _ (by decide), hLcaD, hu15d']; exact haS
    · rw [hFinD, data_set_other _ _ _ _ (by decide), hLcaD, hu15d']; exact hbS
    · rw [hFinD, data_set_other _ _ _ _ (by decide), hLcaD, hu15d']; exact hxS

private theorem log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  by_cases ha : a = 0
  · subst ha; exact Nat.zero_le _
  · have hb : b ≠ 0 := by omega
    have haPow : 2 ^ Nat.log2 a ≤ a := (Nat.le_log2 ha).mp (Nat.le_refl _)
    have hbPow : b < 2 ^ (Nat.log2 b + 1) := (Nat.log2_lt hb).mp (Nat.lt_succ_self _)
    have hpow : 2 ^ Nat.log2 a < 2 ^ (Nat.log2 b + 1) :=
      Nat.lt_of_le_of_lt (Nat.le_trans haPow h) hbPow
    have hlt := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hpow
    omega

private theorem cStart_le_count {N : Nat} (lenOf : Fin N → Nat)
    (cStart : Fin (N + 1) → Nat)
    (h0 : cStart ⟨0, Nat.zero_lt_succ _⟩ = 0)
    (hStep : ∀ d : Fin N,
      cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
        cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + lenOf d)
    (hBound : ∀ (d : Fin N) (j : Nat), j < lenOf d →
      cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j < N) :
    ∀ k : Nat, ∀ hk : k ≤ N, cStart ⟨k, Nat.lt_succ_of_le hk⟩ ≤ N := by
  intro k
  induction k with
  | zero => intro hk; rw [h0]; exact Nat.zero_le _
  | succ k ih =>
      intro hk
      have hk' : k < N := by omega
      have ihk := ih (Nat.le_of_lt hk')
      let d : Fin N := ⟨k, hk'⟩
      have hst := hStep d
      change cStart ⟨k + 1, Nat.lt_succ_of_le hk⟩ = cStart ⟨k, Nat.lt_succ_of_lt hk'⟩ + lenOf d at hst
      rw [hst]
      by_cases hz : lenOf d = 0
      · rw [hz, Nat.add_zero]; exact ihk
      · have hpos : lenOf d - 1 < lenOf d := by omega
        have hb := hBound d (lenOf d - 1) hpos
        change cStart ⟨k, Nat.lt_succ_of_lt hk'⟩ + (lenOf d - 1) < N at hb
        omega

private theorem childSearch_eq_reader {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits)
    (hTag : TagsFit bits) (q : OriginalReader g r)
    {buckets : ForestLayout.ChildLists q.count} (rows : DenseQuotientRows.Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hMapEq : ∀ d : Fin q.count, (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d)
    (hRangesValid : ∀ d : Fin q.count, StaticChildLookup.Valid (q.reader.ranges.read d))
    (Hdr : StaticHeaderSpec I g.vertexCount q.count) (hISz : I.size < 2 ^ bits)
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (cStart : Fin (q.count + 1) → Nat)
    (hc0 : cStart ⟨0, Nat.zero_lt_succ _⟩ = 0)
    (hcStep : ∀ d : Fin q.count,
      cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
        cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + (q.reader.ranges.read d).size)
    (hcSlice : NatSliceAt I Hdr.childStartBase (q.count + 1)
      (fun idx => if hi : idx < q.count + 1 then cStart ⟨idx, hi⟩ else 0))
    (hcItems : ∀ (d : Fin q.count) (j : Nat) (hj : j < (q.reader.ranges.read d).size),
      let pos := cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j
      let ch := (q.reader.ranges.read d)[j]'hj
      pos < q.count ∧
      (I[Hdr.childEntriesBase + pos]?).map Fin.val = some ch.entry ∧
      (I[Hdr.childStopsBase + pos]?).map Fin.val = some ch.stop ∧
      (I[Hdr.childIdsBase + pos]?).map Fin.val = some ch.id.val)
    {base retPC : Nat}
    (hpl : PlacedSlice (childSearchBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
      (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
      (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) base retPC)
      (oracleQueryProgram hI hWork hTag) base)
    (hret : retPC < (oracleQueryProgram hI hWork hTag).size)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = base)
    (dDense zDense : Fin q.count)
    (hreg1 : (reg s 1).val = dDense.val) (hreg2 : (reg s 2).val = zDense.val) :
    ∃ t k, k ≤ 11 * OracleContract.L g.vertexCount + 44 ∧
      Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
      t.pc = retPC ∧ t.data = s.data ∧
      (q.reader.child dDense zDense = none → (reg t 0).val = 0) ∧
      (∀ c : Fin q.count, q.reader.child dDense zDense = some c →
        ∃ (hp : q.input.parent.read c = dDense) (hne : c ≠ dDense),
          (reg t 0).val = 1 ∧
          (reg t 1).val = c.val ∧
          (reg t 2).val = (EX44.ActualOnlineOracle.denseChild q rows childOK dDense c hp hne).val) := by
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  obtain ⟨entryBaseW, hEB, hEBv⟩ := unwrap_map_val I hdrEntry Hdr.entryBase Hdr.hEntryBase
  obtain ⟨cStartBaseW, hCSB, hCSBv⟩ := unwrap_map_val I hdrChildStart Hdr.childStartBase Hdr.hChildStartBase
  obtain ⟨cEntBaseW, hCEB, hCEBv⟩ := unwrap_map_val I hdrChildEntries Hdr.childEntriesBase Hdr.hChildEntriesBase
  obtain ⟨cStopBaseW, hCPB, hCPBv⟩ := unwrap_map_val I hdrChildStops Hdr.childStopsBase Hdr.hChildStopsBase
  obtain ⟨cIdBaseW, hCIB, hCIBv⟩ := unwrap_map_val I hdrChildIds Hdr.childIdsBase Hdr.hChildIdsBase
  obtain ⟨entryZ, hEZ, hEZv⟩ := natSliceAt_read hEntry zDense.val zDense.isLt
  rw [dite_eq_left zDense.isLt, Fin.eta zDense zDense.isLt] at hEZv
  have hd0lt : dDense.val < q.count + 1 := Nat.lt_succ_of_lt dDense.isLt
  have hd1lt : dDense.val + 1 < q.count + 1 := Nat.succ_lt_succ dDense.isLt
  obtain ⟨cStart0, hCS0, hCS0v⟩ := natSliceAt_read hcSlice dDense.val hd0lt
  obtain ⟨cStart1, hCS1, hCS1v⟩ := natSliceAt_read hcSlice (dDense.val + 1) hd1lt
  rw [dite_eq_left hd0lt] at hCS0v
  rw [dite_eq_left hd1lt] at hCS1v
  have hcStepD := hcStep dDense
  have hcLen : cStart1.val - cStart0.val = (q.reader.ranges.read dDense).size := by omega
  have hLe := cStart_le_count (fun u => (q.reader.ranges.read u).size) cStart hc0 hcStep
    (fun u j hj => (hcItems u j hj).1) (dDense.val + 1) (Nat.succ_le_of_lt dDense.isLt)
  have hc1Le : cStart1.val ≤ q.count := by
    rw [hCS1v]; exact hLe
  have hOrder : cStart0.val ≤ cStart1.val := by omega
  have hSliceFit : cStartBaseW.val + (reg s (r16 rfl 1)).val + 1 < 2 ^ bits := by
    rw [reg_r16, hreg1, hCSBv]
    exact Nat.lt_of_le_of_lt (by have := Hdr.childStart_fit; omega) hISz
  have hEntWithin : cEntBaseW.val + cStart0.val + (cStart1.val - cStart0.val) ≤ I.size := by
    rw [hCEBv]; have := Hdr.childEntries_fit; omega
  have hEntFit : cEntBaseW.val + cStart0.val + (cStart1.val - cStart0.val) < 2 ^ bits :=
    Nat.lt_of_le_of_lt hEntWithin hISz
  have hStopWithin : cStopBaseW.val + cStart0.val + (cStart1.val - cStart0.val) ≤ I.size := by
    rw [hCPBv]; have := Hdr.childStops_fit; omega
  have hIdWithin : cIdBaseW.val + cStart0.val + (cStart1.val - cStart0.val) ≤ I.size := by
    rw [hCIBv]; have := Hdr.childIds_fit; omega
  have hValid := hRangesValid dDense
  have hSorted : ∀ (i j : Nat) (hi : i < cStart1.val - cStart0.val) (hj : j < cStart1.val - cStart0.val),
      i ≤ j →
      (inp.words[cEntBaseW.val + cStart0.val + i]'(by change _ < I.size; omega)).val ≤
      (inp.words[cEntBaseW.val + cStart0.val + j]'(by change _ < I.size; omega)).val := by
    intro i j hi hj hij
    have hi' : i < (q.reader.ranges.read dDense).size := by omega
    have hj' : j < (q.reader.ranges.read dDense).size := by omega
    obtain ⟨_, hEi, _, _⟩ := hcItems dDense i hi'
    obtain ⟨_, hEj, _, _⟩ := hcItems dDense j hj'
    obtain ⟨wi, hwi, hwiV⟩ := unwrap_map_val I (Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i)) _ hEi
    obtain ⟨wj, hwj, hwjV⟩ := unwrap_map_val I (Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + j)) _ hEj
    have hpi : I[Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i)]? =
        some (inp.words[cEntBaseW.val + cStart0.val + i]'(by change _ < I.size; omega)) := by
      have hidx : Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i) = cEntBaseW.val + cStart0.val + i := by
        rw [hCEBv, hCS0v, Nat.add_assoc]
      rw [hidx]
      exact getElem?_pos I _ (by change _ < I.size; omega)
    have hqj : I[Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + j)]? =
        some (inp.words[cEntBaseW.val + cStart0.val + j]'(by change _ < I.size; omega)) := by
      have hidx : Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + j) = cEntBaseW.val + cStart0.val + j := by
        rw [hCEBv, hCS0v, Nat.add_assoc]
      rw [hidx]
      exact getElem?_pos I _ (by change _ < I.size; omega)
    have heqi := Option.some.inj (hpi.symm.trans hwi)
    have heqj := Option.some.inj (hqj.symm.trans hwj)
    rw [heqi, heqj, hwiV, hwjV]
    by_cases hlt : i < j
    · exact Nat.le_of_lt (StaticChildLookup.entry_strict hValid ⟨i, hi'⟩ ⟨j, hj'⟩ hlt)
    · have heq : i = j := by omega
      subst heq; exact Nat.le_refl _
  obtain ⟨t, steps, hsteps, hst, htpc, htd, hSpec⟩ := childSearchBlock_spec (h16 := rfl)
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
    (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
    (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) rfl rfl
    hpl hret inp s hpc
    hEB hCSB hCEB hCPB hCIB
    (by rw [reg_r16, hreg2, hEBv]; exact hEZ)
    (by rw [reg_r16, hreg1, hCSBv]; exact hCS0)
    (by rw [reg_r16, hreg1, hCSBv, Nat.add_assoc]; exact hCS1)
    hOrder hSliceFit hEntFit hEntWithin hStopWithin hIdWithin hSorted
  let p : Predecessor.Slice (bits := bits) (cap := I.size) (hcap := hI) ⟨I, rfl⟩ :=
    ⟨add cEntBaseW cStart0, cStart1.val - cStart0.val,
      by rw [add_no_wrap cEntBaseW cStart0 (by omega)]; exact hEntFit,
      by rw [add_no_wrap cEntBaseW cStart0 (by omega)]; exact hEntWithin⟩
  have hget_at : ∀ (k : Nat) (hk : k < cStart1.val - cStart0.val),
      p.get k hk = inp.words[cEntBaseW.val + cStart0.val + k]'(by change _ < I.size; omega) := fun k hk => by
    have hA := add_no_wrap cEntBaseW cStart0 (by omega)
    have hidx : (add cEntBaseW cStart0).val + k = cEntBaseW.val + cStart0.val + k := by rw [hA]
    have h1 : I[cEntBaseW.val + cStart0.val + k]? = some (p.get k hk) := by
      rw [← hidx]
      change I[(add cEntBaseW cStart0).val + k]? = some (I[(add cEntBaseW cStart0).val + k]'(by rw [hA]; omega))
      exact getElem?_pos I _ (by rw [hA]; omega)
    have h2 : I[cEntBaseW.val + cStart0.val + k]? =
        some (inp.words[cEntBaseW.val + cStart0.val + k]'(by change _ < I.size; omega)) :=
      getElem?_pos I _ (by change _ < I.size; omega)
    exact Option.some.inj (h1.symm.trans h2)
  have hpSorted : p.Sorted := fun i j hi hj hij => by
    rw [hget_at i hi, hget_at j hj]
    exact hSorted i j hi hj hij
  obtain ⟨res, _, hans, _, _⟩ := Predecessor.worker_correct p entryZ hpSorted
  let count := (reg res.finalState ⟨0, by change 0 < 7; decide⟩).val
  obtain ⟨hZeroAns, hSuccAns⟩ := hSpec count hans
  have hLenLe : cStart1.val - cStart0.val ≤ g.vertexCount := by
    have := Hdr.q_le; omega
  have hLogLe : Nat.log2 (cStart1.val - cStart0.val + 1) + 1 ≤ OracleContract.L g.vertexCount :=
    Nat.succ_le_succ (log2_mono (Nat.succ_le_succ hLenLe))
  have hStepsLe : steps ≤ 11 * OracleContract.L g.vertexCount + 44 := by
    have : 11 * (Nat.log2 (cStart1.val - cStart0.val + 1) + 1) ≤ 11 * OracleContract.L g.vertexCount :=
      Nat.mul_le_mul_left 11 hLogLe
    omega
  refine ⟨t, steps, hStepsLe, hst, htpc, htd, ?_, ?_⟩
  · -- `q.reader.child dDense zDense = none → (reg t 0).val = 0`
    intro hNone
    cases hcnt : count with
    | zero => rw [← reg_r16 t 0]; exact hZeroAns hcnt
    | succ pos =>
        by_cases hpos : pos < cStart1.val - cStart0.val
        · have hSucc := hSuccAns pos hcnt hpos
          have hpos' : pos < (q.reader.ranges.read dDense).size := by omega
          obtain ⟨_, hEi, hSi, _⟩ := hcItems dDense pos hpos'
          obtain ⟨wLo, hwLo, hwLoV⟩ := unwrap_map_val I (Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + pos)) _ hEi
          obtain ⟨wHi, hwHi, hwHiV⟩ := unwrap_map_val I (Hdr.childStopsBase + (cStart ⟨dDense.val, hd0lt⟩ + pos)) _ hSi
          have hloEq : (inp.words[cEntBaseW.val + (cStart0.val + pos)]'(by change _ < I.size; omega)).val =
              ((q.reader.ranges.read dDense)[pos]'hpos').entry := by
            have hidx : Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + pos) =
                cEntBaseW.val + (cStart0.val + pos) := by rw [hCEBv, hCS0v]
            have hp : I[Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + pos)]? =
                some (inp.words[cEntBaseW.val + (cStart0.val + pos)]'(by change _ < I.size; omega)) := by
              rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
            rw [Option.some.inj (hp.symm.trans hwLo), hwLoV]
          have hhiEq : (inp.words[cStopBaseW.val + (cStart0.val + pos)]'(by change _ < I.size; omega)).val =
              ((q.reader.ranges.read dDense)[pos]'hpos').stop := by
            have hidx : Hdr.childStopsBase + (cStart ⟨dDense.val, hd0lt⟩ + pos) =
                cStopBaseW.val + (cStart0.val + pos) := by rw [hCPBv, hCS0v]
            have hp : I[Hdr.childStopsBase + (cStart ⟨dDense.val, hd0lt⟩ + pos)]? =
                some (inp.words[cStopBaseW.val + (cStart0.val + pos)]'(by change _ < I.size; omega)) := by
              rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
            rw [Option.some.inj (hp.symm.trans hwHi), hwHiV]
          by_cases hcond :
              (inp.words[cEntBaseW.val + (cStart0.val + pos)]'(by change _ < I.size; omega)).val ≤ entryZ.val ∧
              entryZ.val < (inp.words[cStopBaseW.val + (cStart0.val + pos)]'(by change _ < I.size; omega)).val
          · -- Contradiction: `StaticChildLookup.lookup` must return `some`
            exfalso
            have hIn : StaticChildLookup.Contains ((q.reader.ranges.read dDense)[pos]'hpos') (q.reader.entry zDense) := by
              change ((q.reader.ranges.read dDense)[pos]'hpos').entry ≤ q.reader.entry zDense ∧
                q.reader.entry zDense < ((q.reader.ranges.read dDense)[pos]'hpos').stop
              rw [← hloEq, ← hhiEq, ← hEZv]
              exact hcond
            have hSome := (StaticChildLookup.lookup_some_iff hValid (q.reader.entry zDense) _).mpr
              ⟨⟨pos, hpos'⟩, rfl, hIn⟩
            have hCh : q.reader.child dDense zDense =
                (StaticChildLookup.lookup (q.reader.ranges.read dDense) (q.reader.entry zDense)).map
                  (fun c => c.id) := rfl
            rw [hCh, hSome] at hNone
            cases hNone
          · rw [ite_eq_right hcond] at hSucc
            rw [← reg_r16 t 0]; exact hSucc
        · -- `count ≥ p.len + 1` impossible because `Answer.1` says `count ≤ p.len`
          exfalso; have := hans.1; change count ≤ cStart1.val - cStart0.val at this; rw [hcnt] at this; omega
  · -- `q.reader.child dDense zDense = some c`
    intro c hcSome
    have hCh : q.reader.child dDense zDense =
        (StaticChildLookup.lookup (q.reader.ranges.read dDense) (q.reader.entry zDense)).map
          (fun z => z.id) := rfl
    rw [hCh] at hcSome
    cases hLk : StaticChildLookup.lookup (q.reader.ranges.read dDense) (q.reader.entry zDense) with
    | none => rw [hLk] at hcSome; cases hcSome
    | some z =>
        rw [hLk, Option.map_some, Option.some.injEq] at hcSome
        obtain ⟨i, hiZ, hCont⟩ := (StaticChildLookup.lookup_some_iff hValid (q.reader.entry zDense) z).mp hLk
        have hidC : (StaticChildLookup.childAt (q.reader.ranges.read dDense) i).id = c := by
          rw [hiZ]; exact hcSome
        -- `count = i.val + 1` by `Predecessor.Answer`!
        have hAiEnt : (p.get i.val (by change i.val < cStart1.val - cStart0.val; omega)).val ≤ entryZ.val := by
          obtain ⟨_, hEi, _, _⟩ := hcItems dDense i.val i.isLt
          obtain ⟨wLo, hwLo, hwLoV⟩ := unwrap_map_val I (Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)) _ hEi
          have hidx : Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val) =
              cEntBaseW.val + cStart0.val + i.val := by rw [hCEBv, hCS0v, Nat.add_assoc]
          have hp : I[Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)]? =
              some (inp.words[cEntBaseW.val + cStart0.val + i.val]'(by change _ < I.size; omega)) := by
            rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
          rw [hget_at i.val (by change i.val < cStart1.val - cStart0.val; omega),
            Option.some.inj (hp.symm.trans hwLo), hwLoV, hEZv]
          exact hCont.1
        have hiLtCnt : i.val < count := by
          by_cases hle : count ≤ i.val
          · exfalso
            have hGt := hans.2.2 i.val (by change i.val < cStart1.val - cStart0.val; omega) hle
            omega
          · omega
        have hCntLeI1 : count ≤ i.val + 1 := by
          by_cases hgt : i.val + 1 < count
          · exfalso
            have hi1 : i.val + 1 < (q.reader.ranges.read dDense).size := by
              have := hans.1; change count ≤ cStart1.val - cStart0.val at this; omega
            have hAi1 := hans.2.1 (i.val + 1) (by change i.val + 1 < cStart1.val - cStart0.val; omega) hgt
            obtain ⟨_, hEi1, _, _⟩ := hcItems dDense (i.val + 1) hi1
            obtain ⟨wLo1, hwLo1, hwLo1V⟩ := unwrap_map_val I (Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + (i.val + 1))) _ hEi1
            have hidx : Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + (i.val + 1)) =
                cEntBaseW.val + cStart0.val + (i.val + 1) := by rw [hCEBv, hCS0v, Nat.add_assoc]
            have hp : I[Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + (i.val + 1))]? =
                some (inp.words[cEntBaseW.val + cStart0.val + (i.val + 1)]'(by change _ < I.size; omega)) := by
              rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
            rw [hget_at (i.val + 1) (by change i.val + 1 < cStart1.val - cStart0.val; omega),
              Option.some.inj (hp.symm.trans hwLo1), hwLo1V, hEZv] at hAi1
            have hDisj := hValid.2 i ⟨i.val + 1, hi1⟩ (Nat.lt_succ_self _)
            change (StaticChildLookup.childAt (q.reader.ranges.read dDense) i).stop ≤
              ((q.reader.ranges.read dDense)[i.val + 1]'hi1).entry at hDisj
            have hEnd := hCont.2
            omega
          · omega
        have hCntEq : count = i.val + 1 := by omega
        have hpos : i.val < cStart1.val - cStart0.val := by omega
        have hSucc := hSuccAns i.val hCntEq hpos
        obtain ⟨_, hEi, hSi, hIi⟩ := hcItems dDense i.val i.isLt
        obtain ⟨wLo, hwLo, hwLoV⟩ := unwrap_map_val I (Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)) _ hEi
        obtain ⟨wHi, hwHi, hwHiV⟩ := unwrap_map_val I (Hdr.childStopsBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)) _ hSi
        obtain ⟨wId, hwId, hwIdV⟩ := unwrap_map_val I (Hdr.childIdsBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)) _ hIi
        have hloEq : (inp.words[cEntBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)).val =
            ((q.reader.ranges.read dDense)[i.val]'i.isLt).entry := by
          have hidx : Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val) =
              cEntBaseW.val + (cStart0.val + i.val) := by rw [hCEBv, hCS0v]
          have hp : I[Hdr.childEntriesBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)]? =
              some (inp.words[cEntBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)) := by
            rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
          rw [Option.some.inj (hp.symm.trans hwLo), hwLoV]
        have hhiEq : (inp.words[cStopBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)).val =
            ((q.reader.ranges.read dDense)[i.val]'i.isLt).stop := by
          have hidx : Hdr.childStopsBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val) =
              cStopBaseW.val + (cStart0.val + i.val) := by rw [hCPBv, hCS0v]
          have hp : I[Hdr.childStopsBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)]? =
              some (inp.words[cStopBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)) := by
            rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
          rw [Option.some.inj (hp.symm.trans hwHi), hwHiV]
        have hidEq : (inp.words[cIdBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)).val = c.val := by
          have hidx : Hdr.childIdsBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val) =
              cIdBaseW.val + (cStart0.val + i.val) := by rw [hCIBv, hCS0v]
          have hp : I[Hdr.childIdsBase + (cStart ⟨dDense.val, hd0lt⟩ + i.val)]? =
              some (inp.words[cIdBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)) := by
            rw [hidx]; exact getElem?_pos I _ (by change _ < I.size; omega)
          rw [Option.some.inj (hp.symm.trans hwId), hwIdV]
          exact congrArg Fin.val hidC
        have hcond :
            (inp.words[cEntBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)).val ≤ entryZ.val ∧
            entryZ.val < (inp.words[cStopBaseW.val + (cStart0.val + i.val)]'(by change _ < I.size; omega)).val := by
          rw [hloEq, hhiEq, hEZv]
          change (StaticChildLookup.childAt (q.reader.ranges.read dDense) i).entry ≤ q.reader.entry zDense ∧
            q.reader.entry zDense < (StaticChildLookup.childAt (q.reader.ranges.read dDense) i).stop
          exact hCont
        rw [ite_eq_left hcond] at hSucc
        -- Extract `hp` and `hne` and relate `i.val + 1` to `denseChild`
        have hMapI : ((q.reader.ranges.read dDense).toList.map (fun z => z.id))[i.val]'(by
            simp only [List.length_map, Array.length_toList]; exact i.isLt) =
            ((q.reader.ranges.read dDense)[i.val]'i.isLt).id := by
          simp [List.getElem_map]
        have hiLen : i.val < (buckets.get dDense).length := by
          rw [← hMapEq dDense]; simp only [List.length_map, Array.length_toList]; exact i.isLt
        have hBuckAt : (buckets.get dDense)[i.val]'hiLen = c := by
          have he := congrArg (fun xs : List (Fin q.count) =>
            xs[i.val]?) (hMapEq dDense)
          rw [List.getElem?_eq_getElem (by simp only [List.length_map, Array.length_toList]; exact i.isLt),
            List.getElem?_eq_getElem hiLen, Option.some.injEq] at he
          rw [← he, hMapI]; exact hidC
        have hMem : c ∈ buckets.get dDense := hBuckAt ▸ List.getElem_mem hiLen
        obtain ⟨hNotRoot, hParent⟩ := (childOK dDense c).mp hMem
        have hNeD : c ≠ dDense := by
          intro hEq
          have hd := q.reader.input_ok.depth_step c hNotRoot
          rw [hParent, ← hEq] at hd
          omega
        let dc := EX44.ActualOnlineOracle.denseChild q rows childOK dDense c hParent hNeD
        have hdc : dc.val = i.val + 1 := by
          have hOcc : DenseQuotientRows.Occurs buckets dDense (.inr c) :=
            (childOK dDense c).mpr ⟨hNotRoot, hParent⟩
          have hKey1 : rows.key dDense dc = .inr c :=
            congrArg Subtype.val (rows.decode_encode dDense ⟨.inr c, hOcc⟩)
          have hLenSucc : i.val + 1 < rows.length dDense := by
            rw [rows.length_exact]; omega
          have hKey2 : rows.key dDense ⟨i.val + 1, hLenSucc⟩ = .inr c := by
            rw [rows.key_succ dDense i.val hiLen, hBuckAt]
          have heq := rows.key_injective dDense (hKey1.trans hKey2.symm)
          exact congrArg Fin.val heq
        refine ⟨hParent, hNeD, ?_, ?_, ?_⟩
        · rw [← reg_r16 t 0]; exact hSucc.1
        · rw [← reg_r16 t 1, hSucc.2.1]; exact hidEq
        · rw [← reg_r16 t 2, hSucc.2.2, hCntEq, hdc]

private theorem exec_blkRouteBlocks {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits)
    (hTag : TagsFit bits) (q : OriginalReader g r)
    {buckets : ForestLayout.ChildLists q.count} (rows : DenseQuotientRows.Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hMapEq : ∀ d : Fin q.count, (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d)
    (hRangesValid : ∀ d : Fin q.count, StaticChildLookup.Valid (q.reader.ranges.read d))
    (Hdr : StaticHeaderSpec I g.vertexCount q.count) (hISz : I.size < 2 ^ bits)
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (cStart : Fin (q.count + 1) → Nat)
    (hc0 : cStart ⟨0, Nat.zero_lt_succ _⟩ = 0)
    (hcStep : ∀ d : Fin q.count,
      cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
        cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + (q.reader.ranges.read d).size)
    (hcSlice : NatSliceAt I Hdr.childStartBase (q.count + 1)
      (fun idx => if hi : idx < q.count + 1 then cStart ⟨idx, hi⟩ else 0))
    (hcItems : ∀ (d : Fin q.count) (j : Nat) (hj : j < (q.reader.ranges.read d).size),
      let pos := cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j
      let ch := (q.reader.ranges.read d)[j]'hj
      pos < q.count ∧
      (I[Hdr.childEntriesBase + pos]?).map Fin.val = some ch.entry ∧
      (I[Hdr.childStopsBase + pos]?).map Fin.val = some ch.stop ∧
      (I[Hdr.childIdsBase + pos]?).map Fin.val = some ch.id.val)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc4)
    (dDense aDense bDense xDense : Fin q.count)
    (dW aW bW xW : Word bits)
    (hdS : s.data[slD]? = some dW) (haS : s.data[slADense]? = some aW)
    (hbS : s.data[slBDense]? = some bW) (hxS : s.data[slXDense]? = some xW)
    (hdV : dW.val = dDense.val) (haV : aW.val = aDense.val)
    (hbV : bW.val = bDense.val) (hxV : xW.val = xDense.val) :
    (q.reader.child dDense aDense = none →
      ∃ t k, k ≤ 11 * OracleContract.L g.vertexCount + 50 ∧
        Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧ t.pc = failPC hI hTag) ∧
    (∀ uDense, q.reader.child dDense aDense = some uDense →
      q.reader.child dDense bDense = none →
      ∃ t k, k ≤ 22 * OracleContract.L g.vertexCount + 104 ∧
        Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧ t.pc = failPC hI hTag) ∧
    (∀ uDense vDense, q.reader.child dDense aDense = some uDense →
      q.reader.child dDense bDense = some vDense →
      q.reader.child dDense xDense = none →
      ∃ t k, k ≤ 33 * OracleContract.L g.vertexCount + 158 ∧
        Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧ t.pc = okPC hI hTag) ∧
    (∀ uDense vDense yDense, q.reader.child dDense aDense = some uDense →
      q.reader.child dDense bDense = some vDense →
      q.reader.child dDense xDense = some yDense →
      ((yDense = uDense →
        ∃ t k, k ≤ 33 * OracleContract.L g.vertexCount + 175 ∧
          Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
          t.pc = pc6 hI hTag ∧ (reg t 1).val = aDense.val ∧ t.data[slXDense]? = some xW) ∧
       (yDense ≠ uDense → yDense = vDense →
        ∃ t k, k ≤ 33 * OracleContract.L g.vertexCount + 185 ∧
          Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
          t.pc = pc6 hI hTag ∧ (reg t 1).val = bDense.val ∧ t.data[slXDense]? = some xW) ∧
       (yDense ≠ uDense → yDense ≠ vDense → uDense = vDense →
        ∃ t k, k ≤ 33 * OracleContract.L g.vertexCount + 192 ∧
          Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧ t.pc = okPC hI hTag) ∧
       (yDense ≠ uDense → yDense ≠ vDense → uDense ≠ vDense →
        ∃ (hpU : q.input.parent.read uDense = dDense) (hneU : uDense ≠ dDense)
          (hpV : q.input.parent.read vDense = dDense) (hneV : vDense ≠ dDense)
          (hpY : q.input.parent.read yDense = dDense) (hneY : yDense ≠ dDense),
          ∃ t k, k ≤ 33 * OracleContract.L g.vertexCount + 192 ∧
            Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
            t.pc = pc5a ∧
            t.data.size = queryWorkCap ∧
            (t.data[slD]?).map Fin.val = some dDense.val ∧
            t.data[slADense]? = some aW ∧
            t.data[slBDense]? = some bW ∧
            (t.data[slULocal]?).map Fin.val = some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val ∧
            (t.data[slVLocal]?).map Fin.val = some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val ∧
            (t.data[slYLocal]?).map Fin.val = some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense yDense hpY hneY).val))) := by
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have h4 := place_blk4 hI hWork hTag
  have hCSz : ∀ b rPC, (childSearchBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
      (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
      (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) b rPC).size = 60 :=
    fun b rPC => childSearchBlock_size rfl _ _ _ _ _ _ _ b rPC
  have hPGSz : ∀ b rPC, (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
      b rPC (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl
        (zeroW bits) (oneW hTag))).size = 7 :=
    fun _ _ => by simp [liftMap, PairGuard.rom]
  have hA0 : PlacedSlice
      (#[.imm 15 (slotW hWork slD (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slADense (by decide)), .loadData 2 15] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) pc4 := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
          (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h4)))))))))))
  have hA1 : PlacedSlice (childSearchBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
      (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
      (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 4) (pc4 + 64))
      (oracleQueryProgram hI hWork hTag) (pc4 + 4) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
          (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h4))))))))))) rfl rfl
  have hA2 : PlacedSlice
      (#[.imm 6 (oneW hTag), .branchLt 0 6 (failPC hI hTag) (pc4 + 66),
        .imm 15 (slotW hWork slUDense (by decide)), .storeData 15 1,
        .imm 15 (slotW hWork slULocal (by decide)), .storeData 15 2,
        .imm 15 (slotW hWork slD (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 2 15] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) (pc4 + 64) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
          (placedSlice_append_left (placedSlice_append_left h4))))))))))
      (by rw [Array.size_append, hCSz]; rfl) rfl
  have hA3 : PlacedSlice (childSearchBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
      (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
      (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 74) (pc4 + 134))
      (oracleQueryProgram hI hWork hTag) (pc4 + 74) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
          (placedSlice_append_left h4)))))))))
      (by rw [Array.size_append, Array.size_append, hCSz]; rfl) rfl
  have hA4 : PlacedSlice
      (#[.imm 6 (oneW hTag), .branchLt 0 6 (failPC hI hTag) (pc4 + 136),
        .imm 15 (slotW hWork slVDense (by decide)), .storeData 15 1,
        .imm 15 (slotW hWork slVLocal (by decide)), .storeData 15 2,
        .imm 15 (slotW hWork slD (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slXDense (by decide)), .loadData 2 15] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) (pc4 + 134) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h4))))))))
      (by rw [Array.size_append, Array.size_append, Array.size_append, hCSz, hCSz]; rfl) rfl
  have hA5 : PlacedSlice (childSearchBlock (L := codeLayout bits I.size hI hWork) rfl
      (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrChildStart (by decide))
      (hdrW hWork hdrChildEntries (by decide)) (hdrW hWork hdrChildStops (by decide))
      (hdrW hWork hdrChildIds (by decide)) (zeroW bits) (oneW hTag) (pc4 + 144) (pc4 + 204))
      (oracleQueryProgram hI hWork hTag) (pc4 + 144) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left (placedSlice_append_left h4)))))))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        hCSz, hCSz]; rfl) rfl
  have hA6 : PlacedSlice
      (#[.imm 6 (oneW hTag), .branchLt 0 6 (okPC hI hTag) (pc4 + 206),
        .imm 15 (slotW hWork slYDense (by decide)), .storeData 15 1,
        .imm 15 (slotW hWork slYLocal (by decide)), .storeData 15 2,
        .imm 15 (slotW hWork slYDense (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slUDense (by decide)), .loadData 3 15] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) (pc4 + 204) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
        (placedSlice_append_left h4))))))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, hCSz, hCSz, hCSz]; rfl) rfl
  have hA7 : PlacedSlice (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
      (pc4 + 214) (pc4 + 221)
      (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      (oracleQueryProgram hI hWork hTag) (pc4 + 214) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h4)))))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, hCSz, hCSz, hCSz]; rfl) rfl
  have hA8 : PlacedSlice
      (#[.imm 6 (oneW hTag), .branchLt 0 6 (pc4 + 223) (pc4 + 226),
        .imm 15 (slotW hWork slADense (by decide)), .loadData 1 15,
        .goto (pc6 hI hTag),
        .imm 15 (slotW hWork slYDense (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slVDense (by decide)), .loadData 3 15] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) (pc4 + 221) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left (placedSlice_append_left h4))))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append, hCSz, hCSz, hCSz, hPGSz]; rfl) rfl
  have hA9 : PlacedSlice (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
      (pc4 + 230) (pc4 + 237)
      (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      (oracleQueryProgram hI hWork hTag) (pc4 + 230) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left
      (placedSlice_append_left h4)))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        hCSz, hCSz, hCSz, hPGSz]; rfl) rfl
  have hA10 : PlacedSlice
      (#[.imm 6 (oneW hTag), .branchLt 0 6 (pc4 + 239) (pc4 + 242),
        .imm 15 (slotW hWork slBDense (by decide)), .loadData 1 15,
        .goto (pc6 hI hTag),
        .imm 15 (slotW hWork slULocal (by decide)), .loadData 1 15,
        .imm 15 (slotW hWork slVLocal (by decide)), .loadData 3 15] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) (pc4 + 237) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left (placedSlice_append_left h4))
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, hCSz, hCSz, hCSz, hPGSz, hPGSz]; rfl) rfl
  have hA11 : PlacedSlice (liftMap (L := codeLayout bits I.size hI hWork)
      (ρ16 rfl (rfl : (KnownNodeCheck.knownCheckLayout bits I.size hI).registerCount = 16))
      (pc4 + 246) (pc4 + 253)
      (PairGuard.rom (L := KnownNodeCheck.knownCheckLayout bits I.size hI) rfl (zeroW bits) (oneW hTag)))
      (oracleQueryProgram hI hWork hTag) (pc4 + 246) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at (placedSlice_append_left h4)
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, hCSz, hCSz, hCSz, hPGSz, hPGSz]; rfl) rfl
  have hA12 : PlacedSlice
      (#[.imm 6 (oneW hTag), .branchLt 0 6 (okPC hI hTag) pc5a] :
        Program (codeLayout bits I.size hI hWork)) (oracleQueryProgram hI hWork hTag) (pc4 + 253) := by
    unfold blkRouteBlocks at h4
    exact placedSlice_append_right_at h4
      (by rw [Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append, Array.size_append,
        Array.size_append, Array.size_append, Array.size_append,
        hCSz, hCSz, hCSz, hPGSz, hPGSz, hPGSz]; rfl) rfl
  -- Call 1: `child(dDense, aDense)`
  obtain ⟨s1, hs1, h1pc, _, h1r1, _, h1d⟩ := step_readSlot (s := s) inp slD (by decide) 1 (by decide) dW hdS
    (by rw [hpc]; exact placedSlice_fetch hA0 (k := 0) rfl)
    (by rw [hpc]; exact placedSlice_fetch hA0 (k := 1) rfl)
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc4]; omega))
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc4]; omega))
  rw [hpc] at h1pc
  obtain ⟨s2, hs2, h2pc, h2r, h2r2, _, h2d⟩ := step_readSlot (s := s1) inp slADense (by decide) 2 (by decide) aW
    (by rw [h1d]; exact haS)
    (by rw [h1pc]; exact placedSlice_fetch hA0 (k := 2) rfl)
    (by rw [h1pc]; exact placedSlice_fetch hA0 (k := 3) rfl)
    (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc4]; omega))
    (prog_pc_lt_const (by rw [h1pc]; dsimp only [pc4]; omega))
  rw [h1pc] at h2pc
  have h2r1 : reg s2 1 = dW := (h2r 1 (by decide) (by decide)).trans h1r1
  have h2d' : s2.data = s.data := h2d.trans h1d
  obtain ⟨s3, kc1, hkc1, hs3, h3pc, h3d, hC1None, hC1Some⟩ := childSearch_eq_reader hI hWork hTag q rows
    childOK hMapEq hRangesValid Hdr hISz hEntry cStart hc0 hcStep hcSlice hcItems hA1
    (prog_pc_lt_const (by dsimp only [pc4]; omega)) s2 h2pc dDense aDense
    (by rw [h2r1]; exact hdV) (by rw [h2r2]; exact haV)
  have h3d' : s3.data = s.data := h3d.trans h2d'
  have hs4 := step_imm16 inp (by rw [h3pc]; exact placedSlice_fetch hA2 (k := 0) rfl)
    (prog_pc_lt_const (by rw [h3pc]; dsimp only [pc4]; omega))
  let s4 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s3 6 (oneW hTag)
  have h4pc : s4.pc = pc4 + 65 := by rw [putReg_pc, h3pc]
  have h4r0 : reg s4 0 = reg s3 0 := putReg_eq_other s3 (by decide : (0 : Fin 16) ≠ 6) _
  have h4r1 : reg s4 1 = reg s3 1 := putReg_eq_other s3 (by decide : (1 : Fin 16) ≠ 6) _
  have h4r2 : reg s4 2 = reg s3 2 := putReg_eq_other s3 (by decide : (2 : Fin 16) ≠ 6) _
  have h4r6 : reg s4 6 = oneW hTag := putReg_eq_same s3 6 _
  have h4d : s4.data = s.data := by rw [putReg_data, h3d']
  have hpre1 : Steps (oracleQueryProgram hI hWork hTag) inp (kc1 + 5) s s4 := by
    have hk_eq : 2 + 2 + kc1 + Nat.succ 0 = kc1 + 5 := by omega
    rw [← hk_eq]
    exact ((hs1.append hs2).append hs3).append (Steps.cons hs4 (Steps.zero s4))
  -- Helper after `child(dDense, aDense) = some uDense` advancing to end of `child(dDense, bDense)`
  have hAfterU : ∀ uDense, q.reader.child dDense aDense = some uDense →
      ∃ (hpU : q.input.parent.read uDense = dDense) (hneU : uDense ≠ dDense)
        (sB : State (codeLayout bits I.size hI hWork)) (kc2 : Nat),
        kc2 ≤ 11 * OracleContract.L g.vertexCount + 54 ∧
        Steps (oracleQueryProgram hI hWork hTag) inp (kc1 + 5 + kc2) s sB ∧
        sB.pc = pc4 + 135 ∧
        reg sB 6 = oneW hTag ∧
        sB.data[slD]? = some dW ∧ sB.data[slADense]? = some aW ∧
        sB.data[slBDense]? = some bW ∧ sB.data[slXDense]? = some xW ∧
        (sB.data[slUDense]?).map Fin.val = some uDense.val ∧
        (sB.data[slULocal]?).map Fin.val =
          some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val ∧
        (∀ j, j ≠ slUDense → j ≠ slULocal → sB.data[j]? = s.data[j]?) ∧
        (q.reader.child dDense bDense = none → (reg sB 0).val = 0) ∧
        (∀ vDense, q.reader.child dDense bDense = some vDense →
          ∃ (hpV : q.input.parent.read vDense = dDense) (hneV : vDense ≠ dDense),
            (reg sB 0).val = 1 ∧ (reg sB 1).val = vDense.val ∧
            (reg sB 2).val = (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val) := by
    intro uDense hU
    obtain ⟨hpU, hneU, h0U, h1U, h2U⟩ := hC1Some uDense hU
    have hnlt : ¬ (reg s4 0).val < (reg s4 6).val := by
      rw [h4r0, h0U, h4r6, oneW]; change ¬ (1 < 1); decide
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hA2 (k := 1) rfl) (by
        change (if (reg s4 0).val < (reg s4 6).val then failPC hI hTag else pc4 + 66) < _
        rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
    let s5 := { s4 with pc := if (reg s4 0).val < (reg s4 6).val then failPC hI hTag else pc4 + 66 }
    have h5pc : s5.pc = pc4 + 66 := by
      change (if (reg s4 0).val < (reg s4 6).val then _ else _) = _; exact ite_eq_right hnlt
    obtain ⟨s6, hs6, h6pc, h6r, _, h6d⟩ := step_writeSlot (s := s5) inp slUDense (by decide) 1 (by decide)
      (by rw [h5pc]; exact placedSlice_fetch hA2 (k := 2) rfl)
      (by rw [h5pc]; exact placedSlice_fetch hA2 (k := 3) rfl)
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h5pc]; dsimp only [pc4]; omega))
    rw [h5pc] at h6pc
    have h6r2 : reg s6 2 = reg s4 2 := h6r 2 (by decide)
    obtain ⟨s7, hs7, h7pc, _, _, h7d⟩ := step_writeSlot (s := s6) inp slULocal (by decide) 2 (by decide)
      (by rw [h6pc]; exact placedSlice_fetch hA2 (k := 4) rfl)
      (by rw [h6pc]; exact placedSlice_fetch hA2 (k := 5) rfl)
      (prog_pc_lt_const (by rw [h6pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h6pc]; dsimp only [pc4]; omega))
    rw [h6pc] at h7pc
    have h7frame : ∀ j, j ≠ slUDense → j ≠ slULocal → s7.data[j]? = s.data[j]? := fun j hju hjul => by
      rw [h7d, data_set_other _ _ _ _ hjul, h6d, data_set_other _ _ _ _ hju, h4d]
    have h7UD : (s7.data[slUDense]?).map Fin.val = some uDense.val := by
      rw [h7d, data_set_other _ _ _ _ (by decide), h6d, data_set_same, Option.map_some]
      exact congrArg some (h4r1.symm ▸ h1U)
    have h7UL : (s7.data[slULocal]?).map Fin.val =
        some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val := by
      rw [h7d, data_set_same, Option.map_some, congrArg Fin.val (h6r2.trans h4r2), h2U]
    obtain ⟨s8, hs8, h8pc, _, h8r1, _, h8d⟩ := step_readSlot (s := s7) inp slD (by decide) 1 (by decide) dW
      (by rw [h7frame slD (by decide) (by decide)]; exact hdS)
      (by rw [h7pc]; exact placedSlice_fetch hA2 (k := 6) rfl)
      (by rw [h7pc]; exact placedSlice_fetch hA2 (k := 7) rfl)
      (prog_pc_lt_const (by rw [h7pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h7pc]; dsimp only [pc4]; omega))
    rw [h7pc] at h8pc
    obtain ⟨s9, hs9, h9pc, h9r, h9r2, _, h9d⟩ := step_readSlot (s := s8) inp slBDense (by decide) 2 (by decide) bW
      (by rw [h8d, h7frame slBDense (by decide) (by decide)]; exact hbS)
      (by rw [h8pc]; exact placedSlice_fetch hA2 (k := 8) rfl)
      (by rw [h8pc]; exact placedSlice_fetch hA2 (k := 9) rfl)
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h8pc]; dsimp only [pc4]; omega))
    rw [h8pc] at h9pc
    have h9r1 : reg s9 1 = dW := (h9r 1 (by decide) (by decide)).trans h8r1
    have h9d' : s9.data = s7.data := h9d.trans h8d
    obtain ⟨s10, kc2', hkc2', hs10, h10pc, h10d, hC2None, hC2Some⟩ := childSearch_eq_reader hI hWork hTag q rows
      childOK hMapEq hRangesValid Hdr hISz hEntry cStart hc0 hcStep hcSlice hcItems hA3
      (prog_pc_lt_const (by dsimp only [pc4]; omega)) s9 h9pc dDense bDense
      (by rw [h9r1]; exact hdV) (by rw [h9r2]; exact hbV)
    have h10d' : s10.data = s7.data := h10d.trans h9d'
    have hs11 := step_imm16 inp (by rw [h10pc]; exact placedSlice_fetch hA4 (k := 0) rfl)
      (prog_pc_lt_const (by rw [h10pc]; dsimp only [pc4]; omega))
    let s11 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s10 6 (oneW hTag)
    have h11pc : s11.pc = pc4 + 135 := by rw [putReg_pc, h10pc]
    have h11d : s11.data = s7.data := by rw [putReg_data, h10d']
    have htot := hpre1.append (((((Steps.cons hs5 (Steps.zero s5)).append (hs6.append hs7)).append
      (hs8.append hs9)).append hs10).append (Steps.cons hs11 (Steps.zero s11)))
    refine ⟨hpU, hneU, s11, 1 + (2 + 2) + (2 + 2) + kc2' + 1, by omega, htot, h11pc,
      putReg_eq_same s10 6 _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h11d, h7frame slD (by decide) (by decide)]; exact hdS
    · rw [h11d, h7frame slADense (by decide) (by decide)]; exact haS
    · rw [h11d, h7frame slBDense (by decide) (by decide)]; exact hbS
    · rw [h11d, h7frame slXDense (by decide) (by decide)]; exact hxS
    · rw [h11d]; exact h7UD
    · rw [h11d]; exact h7UL
    · intro j h1 h2; rw [h11d]; exact h7frame j h1 h2
    · intro hN; rw [putReg_eq_other s10 (by decide : (0 : Fin 16) ≠ 6) _]; exact hC2None hN
    · intro vDense hV
      obtain ⟨hpV, hneV, h0V, h1V, h2V⟩ := hC2Some vDense hV
      exact ⟨hpV, hneV,
        by rw [putReg_eq_other s10 (by decide : (0 : Fin 16) ≠ 6) _]; exact h0V,
        by rw [putReg_eq_other s10 (by decide : (1 : Fin 16) ≠ 6) _]; exact h1V,
        by rw [putReg_eq_other s10 (by decide : (2 : Fin 16) ≠ 6) _]; exact h2V⟩
  -- Helper after `child(dDense, bDense) = some vDense` advancing to end of `child(dDense, xDense)`
  have hAfterUV : ∀ uDense vDense,
      q.reader.child dDense aDense = some uDense →
      q.reader.child dDense bDense = some vDense →
      ∃ (hpU : q.input.parent.read uDense = dDense) (hneU : uDense ≠ dDense)
        (hpV : q.input.parent.read vDense = dDense) (hneV : vDense ≠ dDense)
        (sC : State (codeLayout bits I.size hI hWork)) (kTot : Nat),
        kTot ≤ 33 * OracleContract.L g.vertexCount + 157 ∧
        Steps (oracleQueryProgram hI hWork hTag) inp kTot s sC ∧
        sC.pc = pc4 + 205 ∧
        reg sC 6 = oneW hTag ∧
        sC.data[slD]? = some dW ∧ sC.data[slADense]? = some aW ∧
        sC.data[slBDense]? = some bW ∧ sC.data[slXDense]? = some xW ∧
        (sC.data[slUDense]?).map Fin.val = some uDense.val ∧
        (sC.data[slVDense]?).map Fin.val = some vDense.val ∧
        (sC.data[slULocal]?).map Fin.val =
          some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val ∧
        (sC.data[slVLocal]?).map Fin.val =
          some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val ∧
        (q.reader.child dDense xDense = none → (reg sC 0).val = 0) ∧
        (∀ yDense, q.reader.child dDense xDense = some yDense →
          ∃ (hpY : q.input.parent.read yDense = dDense) (hneY : yDense ≠ dDense),
            (reg sC 0).val = 1 ∧ (reg sC 1).val = yDense.val ∧
            (reg sC 2).val = (EX44.ActualOnlineOracle.denseChild q rows childOK dDense yDense hpY hneY).val) := by
    intro uDense vDense hU hV
    obtain ⟨hpU, hneU, sB, kc2, hkc2, hsB, hBpc, hBr6, hBD, hBA, hBB, hBX, hBUD, hBUL, hBframe, _, hBsome⟩ :=
      hAfterU uDense hU
    obtain ⟨hpV, hneV, h0V, h1V, h2V⟩ := hBsome vDense hV
    have hnlt : ¬ (reg sB 0).val < (reg sB 6).val := by
      rw [h0V, hBr6, oneW]; change ¬ (1 < 1); decide
    have hs12 := step_branchLt16 inp (by rw [hBpc]; exact placedSlice_fetch hA4 (k := 1) rfl) (by
        change (if (reg sB 0).val < (reg sB 6).val then failPC hI hTag else pc4 + 136) < _
        rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
    let s12 := { sB with pc := if (reg sB 0).val < (reg sB 6).val then failPC hI hTag else pc4 + 136 }
    have h12pc : s12.pc = pc4 + 136 := by
      change (if (reg sB 0).val < (reg sB 6).val then _ else _) = _; exact ite_eq_right hnlt
    obtain ⟨s13, hs13, h13pc, h13r, _, h13d⟩ := step_writeSlot (s := s12) inp slVDense (by decide) 1 (by decide)
      (by rw [h12pc]; exact placedSlice_fetch hA4 (k := 2) rfl)
      (by rw [h12pc]; exact placedSlice_fetch hA4 (k := 3) rfl)
      (prog_pc_lt_const (by rw [h12pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h12pc]; dsimp only [pc4]; omega))
    rw [h12pc] at h13pc
    have h13r2 : reg s13 2 = reg sB 2 := h13r 2 (by decide)
    obtain ⟨s14, hs14, h14pc, _, _, h14d⟩ := step_writeSlot (s := s13) inp slVLocal (by decide) 2 (by decide)
      (by rw [h13pc]; exact placedSlice_fetch hA4 (k := 4) rfl)
      (by rw [h13pc]; exact placedSlice_fetch hA4 (k := 5) rfl)
      (prog_pc_lt_const (by rw [h13pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h13pc]; dsimp only [pc4]; omega))
    rw [h13pc] at h14pc
    have h14frame : ∀ j, j ≠ slVDense → j ≠ slVLocal → s14.data[j]? = sB.data[j]? := fun j h1 h2 => by
      rw [h14d, data_set_other _ _ _ _ h2, h13d, data_set_other _ _ _ _ h1]
    have h14VD : (s14.data[slVDense]?).map Fin.val = some vDense.val := by
      rw [h14d, data_set_other _ _ _ _ (by decide), h13d, data_set_same, Option.map_some]
      exact congrArg some h1V
    have h14VL : (s14.data[slVLocal]?).map Fin.val =
        some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val := by
      rw [h14d, data_set_same, Option.map_some]
      exact congrArg some (h13r2.symm ▸ h2V)
    obtain ⟨s15, hs15, h15pc, _, h15r1, _, h15d⟩ := step_readSlot (s := s14) inp slD (by decide) 1 (by decide) dW
      (by rw [h14frame slD (by decide) (by decide)]; exact hBD)
      (by rw [h14pc]; exact placedSlice_fetch hA4 (k := 6) rfl)
      (by rw [h14pc]; exact placedSlice_fetch hA4 (k := 7) rfl)
      (prog_pc_lt_const (by rw [h14pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h14pc]; dsimp only [pc4]; omega))
    rw [h14pc] at h15pc
    obtain ⟨s16, hs16, h16pc, h16r, h16r2, _, h16d⟩ := step_readSlot (s := s15) inp slXDense (by decide) 2 (by decide) xW
      (by rw [h15d, h14frame slXDense (by decide) (by decide)]; exact hBX)
      (by rw [h15pc]; exact placedSlice_fetch hA4 (k := 8) rfl)
      (by rw [h15pc]; exact placedSlice_fetch hA4 (k := 9) rfl)
      (prog_pc_lt_const (by rw [h15pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h15pc]; dsimp only [pc4]; omega))
    rw [h15pc] at h16pc
    have h16r1 : reg s16 1 = dW := (h16r 1 (by decide) (by decide)).trans h15r1
    have h16d' : s16.data = s14.data := h16d.trans h15d
    obtain ⟨s17, kc3', hkc3', hs17, h17pc, h17d, hC3None, hC3Some⟩ := childSearch_eq_reader hI hWork hTag q rows
      childOK hMapEq hRangesValid Hdr hISz hEntry cStart hc0 hcStep hcSlice hcItems hA5
      (prog_pc_lt_const (by dsimp only [pc4]; omega)) s16 h16pc dDense xDense
      (by rw [h16r1]; exact hdV) (by rw [h16r2]; exact hxV)
    have h17d' : s17.data = s14.data := h17d.trans h16d'
    have hs18 := step_imm16 inp (by rw [h17pc]; exact placedSlice_fetch hA6 (k := 0) rfl)
      (prog_pc_lt_const (by rw [h17pc]; dsimp only [pc4]; omega))
    let s18 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s17 6 (oneW hTag)
    have h18pc : s18.pc = pc4 + 205 := by rw [putReg_pc, h17pc]
    have h18d : s18.data = s14.data := by rw [putReg_data, h17d']
    have htot := hsB.append (((((Steps.cons hs12 (Steps.zero s12)).append (hs13.append hs14)).append
      (hs15.append hs16)).append hs17).append (Steps.cons hs18 (Steps.zero s18)))
    refine ⟨hpU, hneU, hpV, hneV, s18, kc1 + 5 + kc2 + (1 + (2 + 2) + (2 + 2) + kc3' + 1), by omega,
      htot, h18pc, putReg_eq_same s17 6 _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h18d, h14frame slD (by decide) (by decide)]; exact hBD
    · rw [h18d, h14frame slADense (by decide) (by decide)]; exact hBA
    · rw [h18d, h14frame slBDense (by decide) (by decide)]; exact hBB
    · rw [h18d, h14frame slXDense (by decide) (by decide)]; exact hBX
    · rw [h18d, h14frame slUDense (by decide) (by decide)]; exact hBUD
    · rw [h18d]; exact h14VD
    · rw [h18d, h14frame slULocal (by decide) (by decide)]; exact hBUL
    · rw [h18d]; exact h14VL
    · intro hN; rw [putReg_eq_other s17 (by decide : (0 : Fin 16) ≠ 6) _]; exact hC3None hN
    · intro yDense hY
      obtain ⟨hpY, hneY, h0Y, h1Y, h2Y⟩ := hC3Some yDense hY
      exact ⟨hpY, hneY,
        by rw [putReg_eq_other s17 (by decide : (0 : Fin 16) ≠ 6) _]; exact h0Y,
        by rw [putReg_eq_other s17 (by decide : (1 : Fin 16) ≠ 6) _]; exact h1Y,
        by rw [putReg_eq_other s17 (by decide : (2 : Fin 16) ≠ 6) _]; exact h2Y⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Branch 1: `child d a = none`
    intro hN
    have h0z := hC1None hN
    have hlt : (reg s4 0).val < (reg s4 6).val := by
      rw [h4r0, h0z, h4r6, oneW]; change 0 < 1; decide
    have hs5 := step_branchLt16 inp (by rw [h4pc]; exact placedSlice_fetch hA2 (k := 1) rfl) (by
        change (if (reg s4 0).val < (reg s4 6).val then failPC hI hTag else pc4 + 66) < _
        rw [ite_eq_left hlt]; exact failPC_lt hI hWork hTag)
    let s5 := { s4 with pc := if (reg s4 0).val < (reg s4 6).val then failPC hI hTag else pc4 + 66 }
    have h5pc : s5.pc = failPC hI hTag := by
      change (if (reg s4 0).val < (reg s4 6).val then _ else _) = _; exact ite_eq_left hlt
    exact ⟨s5, kc1 + 5 + 1, by omega, hpre1.append (Steps.cons hs5 (Steps.zero s5)), h5pc⟩
  · -- Branch 2: `child d a = some u`, `child d b = none`
    intro uDense hU hN
    obtain ⟨_, _, sB, kc2, hkc2, hsB, hBpc, hBr6, _, _, _, _, _, _, _, hBnone, _⟩ := hAfterU uDense hU
    have hlt : (reg sB 0).val < (reg sB 6).val := by
      rw [hBnone hN, hBr6, oneW]; change 0 < 1; decide
    have hs12 := step_branchLt16 inp (by rw [hBpc]; exact placedSlice_fetch hA4 (k := 1) rfl) (by
        change (if (reg sB 0).val < (reg sB 6).val then failPC hI hTag else pc4 + 136) < _
        rw [ite_eq_left hlt]; exact failPC_lt hI hWork hTag)
    let s12 := { sB with pc := if (reg sB 0).val < (reg sB 6).val then failPC hI hTag else pc4 + 136 }
    have h12pc : s12.pc = failPC hI hTag := by
      change (if (reg sB 0).val < (reg sB 6).val then _ else _) = _; exact ite_eq_left hlt
    exact ⟨s12, kc1 + 5 + kc2 + 1, by omega, hsB.append (Steps.cons hs12 (Steps.zero s12)), h12pc⟩
  · -- Branch 3: `child d a = some u`, `child d b = some v`, `child d x = none`
    intro uDense vDense hU hV hN
    obtain ⟨_, _, _, _, sC, kTot, hkTot, hsC, hCpc, hCr6, _, _, _, _, _, _, _, _, hCnone, _⟩ :=
      hAfterUV uDense vDense hU hV
    have hlt : (reg sC 0).val < (reg sC 6).val := by
      rw [hCnone hN, hCr6, oneW]; change 0 < 1; decide
    have hs19 := step_branchLt16 inp (by rw [hCpc]; exact placedSlice_fetch hA6 (k := 1) rfl) (by
        change (if (reg sC 0).val < (reg sC 6).val then okPC hI hTag else pc4 + 206) < _
        rw [ite_eq_left hlt]; exact okPC_lt hI hWork hTag)
    let s19 := { sC with pc := if (reg sC 0).val < (reg sC 6).val then okPC hI hTag else pc4 + 206 }
    have h19pc : s19.pc = okPC hI hTag := by
      change (if (reg sC 0).val < (reg sC 6).val then _ else _) = _; exact ite_eq_left hlt
    exact ⟨s19, kTot + 1, by omega, hsC.append (Steps.cons hs19 (Steps.zero s19)), h19pc⟩
  · -- Branch 4: all 3 children found (`u`, `v`, `y`)
    intro uDense vDense yDense hU hV hY
    obtain ⟨hpU, hneU, hpV, hneV, sC, kTot, hkTot, hsC, hCpc, hCr6, hCD, hCA, hCB, hCX,
      hCUD, hCVD, hCUL, hCVL, _, hCsome⟩ := hAfterUV uDense vDense hU hV
    obtain ⟨hpY, hneY, h0Y, h1Y, h2Y⟩ := hCsome yDense hY
    have hnlt : ¬ (reg sC 0).val < (reg sC 6).val := by
      rw [h0Y, hCr6, oneW]; change ¬ (1 < 1); decide
    have hs19 := step_branchLt16 inp (by rw [hCpc]; exact placedSlice_fetch hA6 (k := 1) rfl) (by
        change (if (reg sC 0).val < (reg sC 6).val then okPC hI hTag else pc4 + 206) < _
        rw [ite_eq_right hnlt]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
    let s19 := { sC with pc := if (reg sC 0).val < (reg sC 6).val then okPC hI hTag else pc4 + 206 }
    have h19pc : s19.pc = pc4 + 206 := by
      change (if (reg sC 0).val < (reg sC 6).val then _ else _) = _; exact ite_eq_right hnlt
    obtain ⟨s20, hs20, h20pc, h20r, _, h20d⟩ := step_writeSlot (s := s19) inp slYDense (by decide) 1 (by decide)
      (by rw [h19pc]; exact placedSlice_fetch hA6 (k := 2) rfl)
      (by rw [h19pc]; exact placedSlice_fetch hA6 (k := 3) rfl)
      (prog_pc_lt_const (by rw [h19pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h19pc]; dsimp only [pc4]; omega))
    rw [h19pc] at h20pc
    have h20r2 : reg s20 2 = reg sC 2 := h20r 2 (by decide)
    obtain ⟨s21, hs21, h21pc, _, _, h21d⟩ := step_writeSlot (s := s20) inp slYLocal (by decide) 2 (by decide)
      (by rw [h20pc]; exact placedSlice_fetch hA6 (k := 4) rfl)
      (by rw [h20pc]; exact placedSlice_fetch hA6 (k := 5) rfl)
      (prog_pc_lt_const (by rw [h20pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h20pc]; dsimp only [pc4]; omega))
    rw [h20pc] at h21pc
    have h21frame : ∀ j, j ≠ slYDense → j ≠ slYLocal → s21.data[j]? = sC.data[j]? := fun j h1 h2 => by
      rw [h21d, data_set_other _ _ _ _ h2, h20d, data_set_other _ _ _ _ h1]
    have h21YL : (s21.data[slYLocal]?).map Fin.val =
        some (EX44.ActualOnlineOracle.denseChild q rows childOK dDense yDense hpY hneY).val := by
      rw [h21d, data_set_same, Option.map_some]; exact congrArg some (h20r2.symm ▸ h2Y)
    obtain ⟨yW, hyW, hyWV⟩ := unwrap_map_val s21.data slYDense yDense.val (by
      rw [h21d, data_set_other _ _ _ _ (by decide), h20d, data_set_same, Option.map_some]
      exact congrArg some h1Y)
    obtain ⟨uW, huW, huWV⟩ := unwrap_map_val s21.data slUDense uDense.val (by
      rw [h21frame slUDense (by decide) (by decide)]; exact hCUD)
    obtain ⟨s22, hs22, h22pc, _, h22r1, _, h22d⟩ := step_readSlot (s := s21) inp slYDense (by decide) 1 (by decide) yW hyW
      (by rw [h21pc]; exact placedSlice_fetch hA6 (k := 6) rfl)
      (by rw [h21pc]; exact placedSlice_fetch hA6 (k := 7) rfl)
      (prog_pc_lt_const (by rw [h21pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h21pc]; dsimp only [pc4]; omega))
    rw [h21pc] at h22pc
    obtain ⟨s23, hs23, h23pc, h23r, h23r3, _, h23d⟩ := step_readSlot (s := s22) inp slUDense (by decide) 3 (by decide) uW
      (by rw [h22d]; exact huW)
      (by rw [h22pc]; exact placedSlice_fetch hA6 (k := 8) rfl)
      (by rw [h22pc]; exact placedSlice_fetch hA6 (k := 9) rfl)
      (prog_pc_lt_const (by rw [h22pc]; dsimp only [pc4]; omega))
      (prog_pc_lt_const (by rw [h22pc]; dsimp only [pc4]; omega))
    rw [h22pc] at h23pc
    have h23r1 : reg s23 1 = yW := (h23r 1 (by decide) (by decide)).trans h22r1
    have h23d' : s23.data = s21.data := h23d.trans h22d
    obtain ⟨s24, hs24, h24pc, h24r0, h24d⟩ := lifted_pairGuard (h16 := rfl) (zeroW bits) (oneW hTag) rfl rfl
      hA7 (prog_pc_lt_const (by dsimp only [pc4]; omega)) inp s23 h23pc
    have hs25 := step_imm16 inp (by rw [h24pc]; exact placedSlice_fetch hA8 (k := 0) rfl)
      (prog_pc_lt_const (by rw [h24pc]; dsimp only [pc4]; omega))
    let s25 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s24 6 (oneW hTag)
    have h25pc : s25.pc = pc4 + 222 := by rw [putReg_pc, h24pc]
    have h25r0 : (reg s25 0).val = if yDense = uDense then 0 else 1 := by
      rw [putReg_eq_other s24 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s24 0, h24r0]
      rw [reg_r16, reg_r16, h23r1, h23r3, hyWV, huWV]
      by_cases hYU : yDense = uDense
      · rw [ite_eq_left (congrArg Fin.val hYU), ite_eq_left hYU]
      · have hnv : yDense.val ≠ uDense.val := fun h => hYU (Fin.ext h)
        rw [ite_eq_right hnv, ite_eq_right hYU]
    have h25r6 : reg s25 6 = oneW hTag := putReg_eq_same s24 6 _
    have h25d : s25.data = s21.data := by rw [putReg_data, h24d, h23d']
    have hmid1 : Steps (oracleQueryProgram hI hWork hTag) inp (kTot + 14) s s25 := by
      have hk_eq : kTot + Nat.succ 0 + (2 + 2) + (2 + 2) + 4 + Nat.succ 0 = kTot + 14 := by omega
      rw [← hk_eq]
      exact ((((hsC.append (Steps.cons hs19 (Steps.zero s19))).append (hs20.append hs21)).append
        (hs22.append hs23)).append hs24).append (Steps.cons hs25 (Steps.zero s25))
    -- Helper when `yDense ≠ uDense` advancing to second PairGuard check (`yDense = vDense`)
    have hNeU : yDense ≠ uDense →
        ∃ s31 : State (codeLayout bits I.size hI hWork),
          Steps (oracleQueryProgram hI hWork hTag) inp (kTot + 24) s s31 ∧
          s31.pc = pc4 + 238 ∧
          (reg s31 0).val = (if yDense = vDense then 0 else 1) ∧
          reg s31 6 = oneW hTag ∧ s31.data = s21.data := by
      intro hyu
      have hnlt1 : ¬ (reg s25 0).val < (reg s25 6).val := by
        rw [h25r0, h25r6, ite_eq_right hyu, oneW]; change ¬ (1 < 1); decide
      have hs26 := step_branchLt16 inp (by rw [h25pc]; exact placedSlice_fetch hA8 (k := 1) rfl) (by
          change (if (reg s25 0).val < (reg s25 6).val then pc4 + 223 else pc4 + 226) < _
          rw [ite_eq_right hnlt1]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
      let s26 := { s25 with pc := if (reg s25 0).val < (reg s25 6).val then pc4 + 223 else pc4 + 226 }
      have h26pc : s26.pc = pc4 + 226 := by
        change (if (reg s25 0).val < (reg s25 6).val then _ else _) = _; exact ite_eq_right hnlt1
      obtain ⟨vW, hvW, hvWV⟩ := unwrap_map_val s21.data slVDense vDense.val (by
        rw [h21frame slVDense (by decide) (by decide)]; exact hCVD)
      obtain ⟨s27, hs27, h27pc, _, h27r1, _, h27d⟩ := step_readSlot (s := s26) inp slYDense (by decide) 1 (by decide) yW
        (by rw [h25d]; exact hyW)
        (by rw [h26pc]; exact placedSlice_fetch hA8 (k := 5) rfl)
        (by rw [h26pc]; exact placedSlice_fetch hA8 (k := 6) rfl)
        (prog_pc_lt_const (by rw [h26pc]; dsimp only [pc4]; omega))
        (prog_pc_lt_const (by rw [h26pc]; dsimp only [pc4]; omega))
      rw [h26pc] at h27pc
      obtain ⟨s28, hs28, h28pc, h28r, h28r3, _, h28d⟩ := step_readSlot (s := s27) inp slVDense (by decide) 3 (by decide) vW
        (by rw [h27d, h25d]; exact hvW)
        (by rw [h27pc]; exact placedSlice_fetch hA8 (k := 7) rfl)
        (by rw [h27pc]; exact placedSlice_fetch hA8 (k := 8) rfl)
        (prog_pc_lt_const (by rw [h27pc]; dsimp only [pc4]; omega))
        (prog_pc_lt_const (by rw [h27pc]; dsimp only [pc4]; omega))
      rw [h27pc] at h28pc
      have h28r1 : reg s28 1 = yW := (h28r 1 (by decide) (by decide)).trans h27r1
      have h28d' : s28.data = s21.data := by rw [h28d, h27d, h25d]
      obtain ⟨s29, hs29, h29pc, h29r0, h29d⟩ := lifted_pairGuard (h16 := rfl) (zeroW bits) (oneW hTag) rfl rfl
        hA9 (prog_pc_lt_const (by dsimp only [pc4]; omega)) inp s28 h28pc
      have hs30 := step_imm16 inp (by rw [h29pc]; exact placedSlice_fetch hA10 (k := 0) rfl)
        (prog_pc_lt_const (by rw [h29pc]; dsimp only [pc4]; omega))
      let s30 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s29 6 (oneW hTag)
      have h30pc : s30.pc = pc4 + 238 := by rw [putReg_pc, h29pc]
      have h30r0 : (reg s30 0).val = if yDense = vDense then 0 else 1 := by
        rw [putReg_eq_other s29 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s29 0, h29r0]
        rw [reg_r16, reg_r16, h28r1, h28r3, hyWV, hvWV]
        by_cases hYV : yDense = vDense
        · rw [ite_eq_left (congrArg Fin.val hYV), ite_eq_left hYV]
        · have hnv : yDense.val ≠ vDense.val := fun h => hYV (Fin.ext h)
          rw [ite_eq_right hnv, ite_eq_right hYV]
      have h30d : s30.data = s21.data := by rw [putReg_data, h29d, h28d']
      refine ⟨s30, ?_, h30pc, h30r0, putReg_eq_same s29 6 _, h30d⟩
      have hk_eq : kTot + 14 + Nat.succ 0 + (2 + 2) + 4 + Nat.succ 0 = kTot + 24 := by omega
      rw [← hk_eq]
      exact (((hmid1.append (Steps.cons hs26 (Steps.zero s26))).append (hs27.append hs28)).append hs29).append
        (Steps.cons hs30 (Steps.zero s30))
    -- Helper when `yDense ≠ uDense` and `yDense ≠ vDense` advancing to final `PairGuard` (`uLocal = vLocal`)
    have hNeUV : yDense ≠ uDense → yDense ≠ vDense →
        ∃ s37 : State (codeLayout bits I.size hI hWork),
          Steps (oracleQueryProgram hI hWork hTag) inp (kTot + 35) s s37 ∧
          (s37.pc = if uDense = vDense then okPC hI hTag else pc5a) ∧
          s37.data = s21.data := by
      intro hyu hyv
      obtain ⟨s30, hs30, h30pc, h30r0, h30r6, h30d⟩ := hNeU hyu
      have hnlt2 : ¬ (reg s30 0).val < (reg s30 6).val := by
        rw [h30r0, h30r6, ite_eq_right hyv, oneW]; change ¬ (1 < 1); decide
      have hs31 := step_branchLt16 inp (by rw [h30pc]; exact placedSlice_fetch hA10 (k := 1) rfl) (by
          change (if (reg s30 0).val < (reg s30 6).val then pc4 + 239 else pc4 + 242) < _
          rw [ite_eq_right hnlt2]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
      let s31 := { s30 with pc := if (reg s30 0).val < (reg s30 6).val then pc4 + 239 else pc4 + 242 }
      have h31pc : s31.pc = pc4 + 242 := by
        change (if (reg s30 0).val < (reg s30 6).val then _ else _) = _; exact ite_eq_right hnlt2
      obtain ⟨ulW, hulW, hulWV⟩ := unwrap_map_val s21.data slULocal
        (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val
        (by rw [h21frame slULocal (by decide) (by decide)]; exact hCUL)
      obtain ⟨vlW, hvlW, hvlWV⟩ := unwrap_map_val s21.data slVLocal
        (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val
        (by rw [h21frame slVLocal (by decide) (by decide)]; exact hCVL)
      obtain ⟨s32, hs32, h32pc, _, h32r1, _, h32d⟩ := step_readSlot (s := s31) inp slULocal (by decide) 1 (by decide) ulW
        (by rw [h30d]; exact hulW)
        (by rw [h31pc]; exact placedSlice_fetch hA10 (k := 5) rfl)
        (by rw [h31pc]; exact placedSlice_fetch hA10 (k := 6) rfl)
        (prog_pc_lt_const (by rw [h31pc]; dsimp only [pc4]; omega))
        (prog_pc_lt_const (by rw [h31pc]; dsimp only [pc4]; omega))
      rw [h31pc] at h32pc
      obtain ⟨s33, hs33, h33pc, h33r, h33r3, _, h33d⟩ := step_readSlot (s := s32) inp slVLocal (by decide) 3 (by decide) vlW
        (by rw [h32d, h30d]; exact hvlW)
        (by rw [h32pc]; exact placedSlice_fetch hA10 (k := 7) rfl)
        (by rw [h32pc]; exact placedSlice_fetch hA10 (k := 8) rfl)
        (prog_pc_lt_const (by rw [h32pc]; dsimp only [pc4]; omega))
        (prog_pc_lt_const (by rw [h32pc]; dsimp only [pc4]; omega))
      rw [h32pc] at h33pc
      have h33r1 : reg s33 1 = ulW := (h33r 1 (by decide) (by decide)).trans h32r1
      have h33d' : s33.data = s21.data := by rw [h33d, h32d, h30d]
      obtain ⟨s34, hs34, h34pc, h34r0, h34d⟩ := lifted_pairGuard (h16 := rfl) (zeroW bits) (oneW hTag) rfl rfl
        hA11 (prog_pc_lt_const (by dsimp only [pc4]; omega)) inp s33 h33pc
      have hs35 := step_imm16 inp (by rw [h34pc]; exact placedSlice_fetch hA12 (k := 0) rfl)
        (prog_pc_lt_const (by rw [h34pc]; dsimp only [pc4]; omega))
      let s35 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s34 6 (oneW hTag)
      have h35pc : s35.pc = pc4 + 254 := by rw [putReg_pc, h34pc]
      have h35r0 : (reg s35 0).val = if uDense = vDense then 0 else 1 := by
        rw [putReg_eq_other s34 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s34 0, h34r0]
        rw [reg_r16, reg_r16, h33r1, h33r3, hulWV, hvlWV]
        by_cases huv : uDense = vDense
        · have huv' :
              (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val =
              (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val := by
            subst huv; rfl
          rw [ite_eq_left huv', ite_eq_left huv]
        · have huv' :
              (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU).val ≠
              (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV).val := fun h => by
            have hnrU : uDense ≠ q.input.root := fun hr => hneU (by rw [← hpU, hr, q.reader.input_ok.parent_root])
            have hnrV : vDense ≠ q.input.root := fun hr => hneV (by rw [← hpV, hr, q.reader.input_ok.parent_root])
            have hk1 : rows.key dDense (EX44.ActualOnlineOracle.denseChild q rows childOK dDense uDense hpU hneU) = .inr uDense :=
              congrArg Subtype.val (rows.decode_encode dDense ⟨.inr uDense, (childOK dDense uDense).mpr ⟨hnrU, hpU⟩⟩)
            have hk2 : rows.key dDense (EX44.ActualOnlineOracle.denseChild q rows childOK dDense vDense hpV hneV) = .inr vDense :=
              congrArg Subtype.val (rows.decode_encode dDense ⟨.inr vDense, (childOK dDense vDense).mpr ⟨hnrV, hpV⟩⟩)
            have heq := hk1.symm.trans ((congrArg (rows.key dDense) (Fin.ext h)).trans hk2)
            cases heq; exact huv rfl
          rw [ite_eq_right huv', ite_eq_right huv]
      have h35r6 : reg s35 6 = oneW hTag := putReg_eq_same s34 6 _
      have hs36 := step_branchLt16 inp (by rw [h35pc]; exact placedSlice_fetch hA12 (k := 1) rfl) (by
          rw [h35r0, h35r6, oneW]
          by_cases huv : uDense = vDense
          · simp [huv, okPC_lt hI hWork hTag]
          · simp [huv]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
      let s36 := { s35 with pc := if (reg s35 0).val < (reg s35 6).val then okPC hI hTag else pc5a }
      have h36pc : s36.pc = if uDense = vDense then okPC hI hTag else pc5a := by
        change (if (reg s35 0).val < (reg s35 6).val then _ else _) = _
        rw [h35r0, h35r6, oneW]
        by_cases huv : uDense = vDense <;> simp [huv]
      have h36d : s36.data = s21.data := by rw [putReg_data, h34d, h33d']
      refine ⟨s36, ?_, h36pc, h36d⟩
      have hk_eq : kTot + 24 + Nat.succ 0 + (2 + 2) + 4 + Nat.succ 0 + Nat.succ 0 = kTot + 35 := by omega
      rw [← hk_eq]
      exact ((((hs30.append (Steps.cons hs31 (Steps.zero s31))).append (hs32.append hs33)).append hs34).append
        (Steps.cons hs35 (Steps.zero s35))).append (Steps.cons hs36 (Steps.zero s36))
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- `yDense = uDense`
      intro hyu
      have hlt : (reg s25 0).val < (reg s25 6).val := by
        rw [h25r0, h25r6, ite_eq_left hyu, oneW]; change 0 < 1; decide
      have hs26 := step_branchLt16 inp (by rw [h25pc]; exact placedSlice_fetch hA8 (k := 1) rfl) (by
          change (if (reg s25 0).val < (reg s25 6).val then pc4 + 223 else pc4 + 226) < _
          rw [ite_eq_left hlt]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
      let s26 := { s25 with pc := if (reg s25 0).val < (reg s25 6).val then pc4 + 223 else pc4 + 226 }
      have h26pc : s26.pc = pc4 + 223 := by
        change (if (reg s25 0).val < (reg s25 6).val then _ else _) = _; exact ite_eq_left hlt
      obtain ⟨s27, hs27, h27pc, _, h27r1, _, h27d⟩ := step_readSlot (s := s26) inp slADense (by decide) 1 (by decide) aW
        (by rw [h25d, h21frame slADense (by decide) (by decide)]; exact hCA)
        (by rw [h26pc]; exact placedSlice_fetch hA8 (k := 2) rfl)
        (by rw [h26pc]; exact placedSlice_fetch hA8 (k := 3) rfl)
        (prog_pc_lt_const (by rw [h26pc]; dsimp only [pc4]; omega))
        (prog_pc_lt_const (by rw [h26pc]; dsimp only [pc4]; omega))
      rw [h26pc] at h27pc
      have hs28 := step_goto16 inp (by rw [h27pc]; exact placedSlice_fetch hA8 (k := 4) rfl)
        (prog_pc_lt _ (by unfold okPC; omega))
      let s28 := { s27 with pc := pc6 hI hTag }
      refine ⟨s28, kTot + 14 + 1 + 2 + 1, by omega,
        ((hmid1.append (Steps.cons hs26 (Steps.zero s26))).append hs27).append (Steps.cons hs28 (Steps.zero s28)),
        rfl, ?_, ?_⟩
      · change (reg s27 1).val = aDense.val; rw [h27r1, haV]
      · change s27.data[slXDense]? = some xW; rw [h27d, h25d, h21frame slXDense (by decide) (by decide)]; exact hCX
    · -- `yDense ≠ uDense`, `yDense = vDense`
      intro hyu hyv
      obtain ⟨s30, hs30, h30pc, h30r0, h30r6, h30d⟩ := hNeU hyu
      have hlt : (reg s30 0).val < (reg s30 6).val := by
        rw [h30r0, h30r6, ite_eq_left hyv, oneW]; change 0 < 1; decide
      have hs31 := step_branchLt16 inp (by rw [h30pc]; exact placedSlice_fetch hA10 (k := 1) rfl) (by
          change (if (reg s30 0).val < (reg s30 6).val then pc4 + 239 else pc4 + 242) < _
          rw [ite_eq_left hlt]; exact prog_pc_lt_const (by dsimp only [pc4]; omega))
      let s31 := { s30 with pc := if (reg s30 0).val < (reg s30 6).val then pc4 + 239 else pc4 + 242 }
      have h31pc : s31.pc = pc4 + 239 := by
        change (if (reg s30 0).val < (reg s30 6).val then _ else _) = _; exact ite_eq_left hlt
      obtain ⟨s32, hs32, h32pc, _, h32r1, _, h32d⟩ := step_readSlot (s := s31) inp slBDense (by decide) 1 (by decide) bW
        (by rw [h30d, h21frame slBDense (by decide) (by decide)]; exact hCB)
        (by rw [h31pc]; exact placedSlice_fetch hA10 (k := 2) rfl)
        (by rw [h31pc]; exact placedSlice_fetch hA10 (k := 3) rfl)
        (prog_pc_lt_const (by rw [h31pc]; dsimp only [pc4]; omega))
        (prog_pc_lt_const (by rw [h31pc]; dsimp only [pc4]; omega))
      rw [h31pc] at h32pc
      have hs33 := step_goto16 inp (by rw [h32pc]; exact placedSlice_fetch hA10 (k := 4) rfl)
        (prog_pc_lt _ (by unfold okPC; omega))
      let s33 := { s32 with pc := pc6 hI hTag }
      refine ⟨s33, kTot + 24 + 1 + 2 + 1, by omega,
        ((hs30.append (Steps.cons hs31 (Steps.zero s31))).append hs32).append (Steps.cons hs33 (Steps.zero s33)),
        rfl, ?_, ?_⟩
      · change (reg s32 1).val = bDense.val; rw [h32r1, hbV]
      · change s32.data[slXDense]? = some xW; rw [h32d, h30d, h21frame slXDense (by decide) (by decide)]; exact hCX
    · -- `uDense = vDense`
      intro hyu hyv huv
      obtain ⟨s36, hs36, h36pc, _⟩ := hNeUV hyu hyv
      rw [ite_eq_left huv] at h36pc
      exact ⟨s36, kTot + 35, by omega, hs36, h36pc⟩
    · -- `uDense ≠ vDense`: arrive at `pc5a`
      intro hyu hyv huv
      obtain ⟨s36, hs36, h36pc, h36d⟩ := hNeUV hyu hyv
      rw [ite_eq_right huv] at h36pc
      refine ⟨hpU, hneU, hpV, hneV, hpY, hneY, s36, kTot + 35, by omega, hs36, h36pc, s36.data_size,
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [h36d, h21frame slD (by decide) (by decide), hCD, Option.map_some]; exact congrArg some hdV
      · rw [h36d, h21frame slADense (by decide) (by decide)]; exact hCA
      · rw [h36d, h21frame slBDense (by decide) (by decide)]; exact hCB
      · rw [h36d, h21frame slULocal (by decide) (by decide)]; exact hCUL
      · rw [h36d, h21frame slVLocal (by decide) (by decide)]; exact hCVL
      · rw [h36d]; exact h21YL

private def castState16' {bits : Nat} {L : RamProgram.Layout bits} (h16 : L.registerCount = 16)
    (L₀ : RamProgram.Layout bits) (h₀ : L₀.registerCount = 16) (s : State L) : State L₀ :=
  { regs := Array.ofFn (fun i : Fin L₀.registerCount => reg s (r16 h16 ⟨i.val, h₀ ▸ i.isLt⟩))
    data := Array.replicate L₀.workCap ⟨0, Nat.two_pow_pos bits⟩
    pc := 0
    regs_size := by simp
    data_size := by simp }

private theorem reg_castState16' {bits : Nat} {L : RamProgram.Layout bits} (h16 : L.registerCount = 16)
    (L₀ : RamProgram.Layout bits) (h₀ : L₀.registerCount = 16) (s : State L) (q : Fin L₀.registerCount) :
    reg (castState16' h16 L₀ h₀ s) q = reg s (r16 h16 ⟨q.val, h₀ ▸ q.isLt⟩) := by
  change (Array.ofFn (fun i : Fin L₀.registerCount => reg s (r16 h16 ⟨i.val, h₀ ▸ i.isLt⟩)))[q.val]'(by
    simp only [Array.size_ofFn]; exact q.isLt) = _
  rw [Array.getElem_ofFn]

private theorem castState16_agrees' {bits : Nat} {L : RamProgram.Layout bits} (h16 : L.registerCount = 16)
    (L₀ : RamProgram.Layout bits) (h₀ : L₀.registerCount = 16)
    {base : Nat} {s : State L} (hpc : s.pc = base) :
    StateAgreement (ρ16 h16 h₀) base (castState16' h16 L₀ h₀ s) s :=
  ⟨hpc, fun r => (reg_castState16' h16 L₀ h₀ s r).symm⟩

private theorem placedSlice_right_pc {bits cap : Nat}
    {hCap : cap ≤ 2 ^ bits} {hWork : queryWorkCap ≤ 2 ^ bits}
    {a b linked : Program (codeLayout bits cap hCap hWork)} {base n : Nat}
    (h : PlacedSlice (a ++ b) linked base) (hn : base + a.size = n) :
    PlacedSlice b linked n :=
  hn ▸ placedSlice_append_right h

private theorem lifted_pairSearch_exact
    {bits : Nat} {L : RamProgram.Layout bits} (h16 : L.registerCount = 16)
    {linked : Program L} {base retPC : Nat}
    (hone : 1 < 2 ^ bits)
    (hpl : PlacedSlice (liftMap (ρ16 h16 (rfl : (ThreeCalls.layout bits L.inputCap L.inputFits).registerCount = 16))
      base retPC (ThreeCalls.EqualityTail.checkedProgram L.inputFits hone (ThreeCalls.concreteSetup bits hone)))
      linked base)
    (hret : retPC < linked.size)
    (input : Input L) (s : State L) (hpc : s.pc = base)
    {a : Array PairLookup.Key}
    (c : PairLookup.ColumnReduction.Columns (bits := bits) input.words a)
    (hs : PairLookup.StrictSorted a) (x y : Word bits)
    (h7 : reg s (r16 h16 7) = c.first.base)
    (h8 : (reg s (r16 h16 8)).val = c.first.len)
    (h9 : reg s (r16 h16 9) = c.second.base)
    (h11 : reg s (r16 h16 11) = x)
    (h12 : reg s (r16 h16 12) = y)
    (h4 : reg s (r16 h16 4) = zero bits)
    (h5 : reg s (r16 h16 5) = zero bits) :
    ∃ (t : State L) (steps : Nat),
      steps ≤ 33 * (Nat.log2 (a.size + 1) + 1) + 39 ∧
      Steps linked input steps s t ∧
      t.pc = retPC ∧
      (reg t (r16 h16 0)).val =
        (if (PairLookup.lookup a (x.val, y.val)).1.isSome then 1 else 0) ∧
      (∀ row : Nat, (PairLookup.lookup a (x.val, y.val)).1 = some row →
        (reg t (r16 h16 3)).val = row) ∧
      t.data = s.data := by
  let L₀ := ThreeCalls.layout bits L.inputCap L.inputFits
  let sub := ThreeCalls.EqualityTail.checkedProgram L.inputFits hone (ThreeCalls.concreteSetup bits hone)
  have rel : RelocatedZeroWork (ρ16 h16 rfl) sub linked base retPC :=
    placedSlice_relocatedZeroWork (ρ16_inj h16 rfl) rfl hret hpl
  let i₀ : Input (Predecessor.layout bits L.inputCap L.inputFits) := ⟨input.words, input.size_eq⟩
  let j₀ : Input L₀ := ⟨input.words, input.size_eq⟩
  let c₀ : PairLookup.ColumnReduction.Columns (bits := bits) i₀.words a := c
  let s₀ : State L₀ := castState16' h16 L₀ rfl s
  have heqR : ∀ q : Fin 16, ThreeCalls.setupReg s₀ q = reg s (r16 h16 q) := fun q =>
    reg_castState16' h16 L₀ rfl s ⟨q.val, q.isLt⟩
  obtain ⟨lo, hi, k, _, _, _, n, s20, s40, s60,
    hlo, hhi₂, _, _, _, _, _, _, _, _,
    hp60, hk0, _, _, hlo60, hhi60,
    h607, h609, h6011, h6012, _, hk, hfinish, _, hprefix, hbudget⟩ :=
    ThreeCalls.pair_search_prefix_from_pc0 L.inputFits hone c₀ hs x y (j := j₀) rfl s₀ rfl
      ((heqR 7).trans h7) (by rw [heqR 8]; exact h8) ((heqR 9).trans h9)
      ((heqR 11).trans h11) ((heqR 12).trans h12)
      ((heqR 4).trans h4) ((heqR 5).trans h5)
  have hhi₁ : hi ≤ c₀.first.len := by rw [c₀.first_len, ← c₀.second_len]; exact hhi₂
  have hcol₁ : (ThreeCalls.setupReg s60 7).val + (ThreeCalls.setupReg s60 14).val ≤ L.inputCap := by
    rw [h607, hhi60]
    have h₁ := c₀.first.within
    rw [i₀.size_eq] at h₁
    exact Nat.le_trans (Nat.add_le_add_left hhi₁ _) h₁
  have hcol₂ : (ThreeCalls.setupReg s60 9).val + (ThreeCalls.setupReg s60 14).val ≤ L.inputCap := by
    rw [h609, hhi60]
    have h₂ := c₀.second.within
    rw [i₀.size_eq] at h₂
    exact Nat.le_trans (Nat.add_le_add_left hhi₂ _) h₂
  have hk60 : (ThreeCalls.setupReg s60 0).val ≤
      (ThreeCalls.setupReg s60 14).val - (ThreeCalls.setupReg s60 13).val := by
    simpa only [hk0, hlo60, hhi60] using hk
  have hmatch :=
    ThreeCalls.selectedPairMatches_iff_finish_isSome c₀ x y (j := j₀) rfl s60 hp60
      hk hhi₁ hhi₂ hk0 hlo60 h607 h609 h6011 h6012
  obtain ⟨m, v, b, hm, hTailSteps, hTailHalt, hTailOut, hTailMatch, hTailIndex⟩ :=
    ThreeCalls.EqualityTail.validation_trace_with_index L.inputFits hone (ThreeCalls.concreteSetup bits hone)
      j₀ s60 hp60 hk60 hcol₁ hcol₂
  have hchecked : Steps sub j₀ n s₀ s60 :=
    PaperB.RamEqualityTailTransfer.steps_checkedProgram hprefix
  have hFullRun := (hchecked.append hTailSteps).halts hTailHalt
  obtain ⟨t, hst, htpc, htreg, _, hdata⟩ :=
    run_relocatedZeroWork rel (rfl : j₀.words = input.words) hFullRun (castState16_agrees' h16 L₀ rfl hpc)
  have hbIff : b = true ↔ (PairLookup.lookup a (x.val, y.val)).1.isSome = true :=
    hTailMatch.trans (hmatch.trans (by rw [hfinish]))
  have h0val : (reg t (r16 h16 0)).val =
      (if (PairLookup.lookup a (x.val, y.val)).1.isSome then 1 else 0) := by
    have hr0 : reg t (r16 h16 0) = ThreeCalls.setupReg v 0 :=
      htreg ⟨0, by change 0 < 16; decide⟩
    rw [hr0]
    change (reg v 0).val = _
    rw [hTailOut]
    cases b with
    | false =>
      have hns : ¬ ((PairLookup.lookup a (x.val, y.val)).1.isSome = true) := fun h => by
        have := hbIff.mpr h; cases this
      rw [ite_eq_right hns]
      rfl
    | true =>
      have hs' : (PairLookup.lookup a (x.val, y.val)).1.isSome = true := hbIff.mp rfl
      rw [ite_eq_left hs']
      rfl
  refine ⟨t, n + m + 1, by omega, hst, htpc, h0val, ?_, hdata⟩
  intro row hrow
  have hbTrue : b = true := hbIff.mpr (by simp [hrow])
  have hix : ThreeCalls.EqualityTail.chosenIndex s60 = row := by
    have hf : PairLookup.ColumnReduction.finish c₀.first c₀.second x y lo k = some row := by
      simpa only [hfinish] using hrow
    by_cases hpos : 0 < k
    · let d := lo + (k - 1)
      have hd₁ : d < c₀.first.len := by dsimp [d]; omega
      have hd₂ : d < c₀.second.len := by dsimp [d]; omega
      have hboth : lo + (k - 1) < c₀.first.len ∧ lo + (k - 1) < c₀.second.len := ⟨hd₁, hd₂⟩
      have hfinEq : PairLookup.ColumnReduction.finish c₀.first c₀.second x y lo k =
          (if (c₀.first.get d hd₁).val = x.val ∧ (c₀.second.get d hd₂).val = y.val
            then some d else none) := by
        simp only [PairLookup.ColumnReduction.finish, ite_eq_left hpos, dite_eq_left hboth] <;> rfl
      have hdrow : d = row := by
        rw [hfinEq] at hf
        split at hf
        · exact Option.some.inj hf
        · simp at hf
      change (ThreeCalls.setupReg s60 13).val + (ThreeCalls.setupReg s60 0).val - 1 = row
      rw [hlo60, hk0]
      dsimp [d] at hdrow
      omega
    · simp [PairLookup.ColumnReduction.finish, hpos] at hf
  have hr3 : reg t (r16 h16 3) = ThreeCalls.setupReg v 3 :=
    htreg ⟨3, by change 3 < 16; decide⟩
  rw [hr3]
  exact (hTailIndex hbTrue).trans hix

private theorem exec_blkPairAndKnown_phase1
    {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {dDense : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr dDense)
    {large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK dDense)}
    {dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))}
    {sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense) → Nat}
    (ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large)
    (wCols : WordColumns bits)
    (hDictSlice : SliceAt I rec.dictPtr wCols.dictionary)
    (hRep : FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordRes))
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (y : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc5a)
    (hDataSz : s.data.size = queryWorkCap)
    (hCD : (s.data[slD]?).map Fin.val = some dDense.val)
    (hCUL : (s.data[slULocal]?).map Fin.val = some P.fst.val)
    (hCVL : (s.data[slVLocal]?).map Fin.val = some P.snd.val)
    (hCYL : (s.data[slYLocal]?).map Fin.val = some y.val) :
    let prog := oracleQueryProgram hI hWork hTag
    let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
    ∃ (s114 : State (codeLayout bits I.size hI hWork))
      (descBaseW swW k0W k1W yW : Word bits) (k1 : Nat),
      k1 ≤ 33 * (Nat.log2 ((ofOrderedReader ordRes).dict.size + 1) + 1) + 73 ∧
      Steps prog inp k1 s s114 ∧
      s114.pc = pc5a + 114 ∧
      descBaseW.val = rec.descBase ∧
      swW.val = (if P.fst < P.snd then 0 else 1) ∧
      k0W.val = P.canonical.fst.val ∧
      k1W.val = P.canonical.snd.val ∧
      yW.val = y.val ∧
      (reg s114 (r16 rfl 0)).val =
        (if (PairLookup.lookup (ofOrderedReader ordRes).dict (k0W.val, k1W.val)).1.isSome then 1 else 0) ∧
      (∀ row : Nat,
        (PairLookup.lookup (ofOrderedReader ordRes).dict (k0W.val, k1W.val)).1 = some row →
        (reg s114 (r16 rfl 3)).val = row) ∧
      s114.data.size = queryWorkCap ∧
      (∀ idx, idx < 14 → s114.data[idx]? = s.data[idx]?) ∧
      s114.data[slDescBase]? = some descBaseW ∧
      s114.data[slSwapped]? = some swW ∧
      s114.data[slKey0]? = some k0W ∧
      s114.data[slKey1]? = some k1W ∧
      s114.data[slYLocal]? = some yW := by
  intro prog inp
  have hOne : 1 < 2 ^ bits := Nat.lt_trans (by decide : 1 < 2) hTag
  have h5aPl := place_blk5a hI hWork hTag
  unfold blkPairAndKnown at h5aPl
  have hEqSz : (ThreeCalls.EqualityTail.checkedProgram hI hOne (ThreeCalls.concreteSetup bits hOne)).size = 77 :=
    ThreeCalls.EqualityTail.checkedProgram_size hI hOne (ThreeCalls.concreteSetup bits hOne)
  have hPrePl := placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left h5aPl)))))))
  have hSearchPl := placedSlice_right_pc (n := pc5a + 37) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left h5aPl))))))) (by dsimp only [pc5a]; rfl)
  -- Unpack scratch & header words
  have hOwnerHdr : hdrOwnerDesc < I.size := Nat.lt_of_lt_of_le (by decide) Hdr.hdr_fit
  have hIlt : I.size < 2 ^ bits := by
    have htf : hdrTotalWords < I.size := Nat.lt_of_lt_of_le (by decide) Hdr.hdr_fit
    have hm := Hdr.hTotal
    rw [getElem?_pos I hdrTotalWords htf, Option.map_some] at hm
    rw [← Option.some.inj hm]
    exact (I[hdrTotalWords]'htf).isLt
  let ownerDescW := I[hdrOwnerDesc]'hOwnerHdr
  have hOwnerHdr? : I[hdrOwnerDesc]? = some ownerDescW := getElem?_pos I hdrOwnerDesc hOwnerHdr
  have hOwnerVal : ownerDescW.val = Hdr.ownerDescBase := by
    have hm := Hdr.hOwnerDescBase
    rw [hOwnerHdr?, Option.map_some] at hm
    exact Option.some.inj hm
  obtain ⟨dW, hdW, hdWv⟩ : ∃ w, s.data[slD]? = some w ∧ w.val = dDense.val := by
    cases hw : s.data[slD]? with
    | none => simp [hw] at hCD
    | some w => exact ⟨w, rfl, by simpa [hw] using hCD⟩
  obtain ⟨uW, huW, huWv⟩ : ∃ w, s.data[slULocal]? = some w ∧ w.val = P.fst.val := by
    cases hw : s.data[slULocal]? with
    | none => simp [hw] at hCUL
    | some w => exact ⟨w, rfl, by simpa [hw] using hCUL⟩
  obtain ⟨vW, hvW, hvWv⟩ : ∃ w, s.data[slVLocal]? = some w ∧ w.val = P.snd.val := by
    cases hw : s.data[slVLocal]? with
    | none => simp [hw] at hCVL
    | some w => exact ⟨w, rfl, by simpa [hw] using hCVL⟩
  obtain ⟨yW, hyW, hyWv⟩ : ∃ w, s.data[slYLocal]? = some w ∧ w.val = y.val := by
    cases hw : s.data[slYLocal]? with
    | none => simp [hw] at hCYL
    | some w => exact ⟨w, rfl, by simpa [hw] using hCYL⟩
  have hDescFits : rec.descBase + 10 ≤ I.size := rec.descFits
  have hDescFit2 : rec.descBase < 2 ^ bits := by omega
  have hDescEq : Hdr.ownerDescBase + 10 * dDense.val = rec.descBase := rec.descBase_val.symm
  have hDescAddFit : ownerDescW.val + 10 * dW.val < 2 ^ bits := by
    rw [hOwnerVal, hdWv, hDescEq]; exact hDescFit2
  have h2dFit : dW.val + dW.val < 2 ^ bits := by omega
  have h4dFit : 2 * dW.val + 2 * dW.val < 2 ^ bits := by omega
  have h8dFit : 4 * dW.val + 4 * dW.val < 2 ^ bits := by omega
  have h10dFit : 2 * dW.val + 8 * dW.val < 2 ^ bits := by omega
  -- Steps 0..14
  have hs0 := step_imm16 inp (by rw [hpc]; exact placedSlice_fetch hPrePl (k := 0) rfl)
    (prog_pc_lt_const (by rw [hpc]; dsimp only [pc5a]; omega))
  let s1 := putReg rfl s 15 (hdrW hWork hdrOwnerDesc (by decide))
  have hs1 := step_loadInput16 inp (s := s1)
    (by simp [s1, putReg_pc, hpc]; exact placedSlice_fetch hPrePl (k := 1) rfl)
    (by change I[(reg s1 15).val]? = _; rw [putReg_eq_same]; exact hOwnerHdr?)
    (prog_pc_lt_const (by simp [s1, putReg_pc, hpc]; dsimp only [pc5a]; omega))
  let s2 := putReg rfl s1 2 ownerDescW
  obtain ⟨s4, hs23, h4pc, h4r, h4r3, _, h4d_eq⟩ := step_readSlot (s := s2) inp slD (by decide) 3 (Fin.ne_of_val_ne (by decide)) dW
    (by simp [s2, s1, putReg_data, hdW])
    (by simp [s2, s1, putReg_pc, hpc]; exact placedSlice_fetch hPrePl (k := 2) rfl)
    (by simp [s2, s1, putReg_pc, hpc]; exact placedSlice_fetch hPrePl (k := 3) rfl)
    (prog_pc_lt_const (by simp [s2, s1, putReg_pc, hpc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by simp [s2, s1, putReg_pc, hpc]; dsimp only [pc5a]; omega))
  have h4pc' : s4.pc = pc5a + 4 := by simp [s2, s1, putReg_pc, hpc] at h4pc; exact h4pc
  have h4r2 : reg s4 2 = ownerDescW := by
    rw [h4r 2 (by decide : (2 : Fin 16) ≠ 3) (by decide : (2 : Fin 16) ≠ 15)]; exact putReg_eq_same s1 2 _
  have h4d : s4.data = s.data := by rw [h4d_eq]; simp [s2, s1, putReg_data]
  -- Steps 4..8: compute descBaseW = ownerDescBase + 10 * d
  let w2d := add dW dW
  let w4d := add w2d w2d
  let w8d := add w4d w4d
  let w10d := add w2d w8d
  let descBaseW := add ownerDescW w10d
  have hw2d : w2d.val = 2 * dW.val := by change (add dW dW).val = _; rw [add_no_wrap dW dW h2dFit]; omega
  have hw4d : w4d.val = 4 * dW.val := by change (add w2d w2d).val = _; rw [add_no_wrap w2d w2d (by rw [hw2d]; exact h4dFit)]; omega
  have hw8d : w8d.val = 8 * dW.val := by change (add w4d w4d).val = _; rw [add_no_wrap w4d w4d (by rw [hw4d]; exact h8dFit)]; omega
  have hw10d : w10d.val = 10 * dW.val := by change (add w2d w8d).val = _; rw [add_no_wrap w2d w8d (by rw [hw2d, hw8d]; exact h10dFit)]; omega
  have hDescWVal : descBaseW.val = rec.descBase := by
    change (add ownerDescW w10d).val = rec.descBase
    rw [add_no_wrap ownerDescW w10d (by rw [hw10d]; exact hDescAddFit), hOwnerVal, hw10d, hdWv, hDescEq]
  have hs4 := step_add16 inp (s := s4) (by rw [h4pc']; exact placedSlice_fetch hPrePl (k := 4) rfl)
    (prog_pc_lt_const (by rw [h4pc']; dsimp only [pc5a]; omega))
  let s5 := putReg rfl s4 4 (add (reg s4 3) (reg s4 3))
  have hs5 := step_add16 inp (s := s5) (by simp [s5, putReg_pc, h4pc']; exact placedSlice_fetch hPrePl (k := 5) rfl)
    (prog_pc_lt_const (by simp [s5, putReg_pc, h4pc']; dsimp only [pc5a]; omega))
  let s6 := putReg rfl s5 5 (add (reg s5 4) (reg s5 4))
  have hs6 := step_add16 inp (s := s6) (by simp [s6, s5, putReg_pc, h4pc']; exact placedSlice_fetch hPrePl (k := 6) rfl)
    (prog_pc_lt_const (by simp [s6, s5, putReg_pc, h4pc']; dsimp only [pc5a]; omega))
  let s7 := putReg rfl s6 5 (add (reg s6 5) (reg s6 5))
  have hs7 := step_add16 inp (s := s7) (by simp [s7, s6, s5, putReg_pc, h4pc']; exact placedSlice_fetch hPrePl (k := 7) rfl)
    (prog_pc_lt_const (by simp [s7, s6, s5, putReg_pc, h4pc']; dsimp only [pc5a]; omega))
  let s8 := putReg rfl s7 4 (add (reg s7 4) (reg s7 5))
  have hs8 := step_add16 inp (s := s8) (by simp [s8, s7, s6, s5, putReg_pc, h4pc']; exact placedSlice_fetch hPrePl (k := 8) rfl)
    (prog_pc_lt_const (by simp [s8, s7, s6, s5, putReg_pc, h4pc']; dsimp only [pc5a]; omega))
  let s9 := putReg rfl s8 14 (add (reg s8 2) (reg s8 4))
  have h9pc : s9.pc = pc5a + 9 := by simp [s9, s8, s7, s6, s5, putReg_pc, h4pc']
  have h9r14 : reg s9 14 = descBaseW := by
    have h4a : reg s5 4 = w2d := by simp [s5, putReg_eq_same, h4r3, w2d]
    have h5a : reg s6 5 = w4d := by simp [s6, putReg_eq_same, h4a, w4d]
    have h5b : reg s7 5 = w8d := by simp [s7, putReg_eq_same, h5a, w8d]
    have h4b : reg s7 4 = w2d := by
      rw [putReg_eq_other s6 (by decide : (4 : Fin 16) ≠ 5), putReg_eq_other s5 (by decide : (4 : Fin 16) ≠ 5)]; exact h4a
    have h4c : reg s8 4 = w10d := by simp [s8, putReg_eq_same, h4b, h5b, w10d]
    have h2c : reg s8 2 = ownerDescW := by
      rw [putReg_eq_other s7 (by decide : (2 : Fin 16) ≠ 4), putReg_eq_other s6 (by decide : (2 : Fin 16) ≠ 5),
        putReg_eq_other s5 (by decide : (2 : Fin 16) ≠ 5), putReg_eq_other s4 (by decide : (2 : Fin 16) ≠ 4)]
      exact h4r2
    simp [s9, putReg_eq_same, h2c, h4c, descBaseW]
  have h9d : s9.data = s.data := by simp [s9, s8, s7, s6, s5, putReg_data, h4d]
  -- Steps 9..14: store slDescBase, load slULocal, slVLocal
  obtain ⟨s11, hs9_10, h11pc, h11r, _, h11d⟩ := step_writeSlot inp slDescBase (by decide) 14 (by decide : (14 : Fin 16) ≠ 15)
    (by rw [h9pc]; exact placedSlice_fetch hPrePl (k := 9) rfl)
    (by rw [h9pc]; exact placedSlice_fetch hPrePl (k := 10) rfl)
    (prog_pc_lt_const (by rw [h9pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h9pc]; dsimp only [pc5a]; omega))
  rw [h9pc] at h11pc
  have h11dU : s11.data[slULocal]? = some uW := by
    rw [h11d, data_set_other _ _ _ _ (by decide), h9d]; exact huW
  have h11dV : s11.data[slVLocal]? = some vW := by
    rw [h11d, data_set_other _ _ _ _ (by decide), h9d]; exact hvW
  obtain ⟨s13, hs11_12, h13pc, h13r, h13r1, _, h13d⟩ := step_readSlot (s := s11) inp slULocal (by decide) 1 (by decide : (1 : Fin 16) ≠ 15) uW h11dU
    (by rw [h11pc]; exact placedSlice_fetch hPrePl (k := 11) rfl)
    (by rw [h11pc]; exact placedSlice_fetch hPrePl (k := 12) rfl)
    (prog_pc_lt_const (by rw [h11pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h11pc]; dsimp only [pc5a]; omega))
  rw [h11pc] at h13pc
  have h13dV : s13.data[slVLocal]? = some vW := by rw [h13d]; exact h11dV
  obtain ⟨s15, hs13_14, h15pc, h15r, h15r2, _, h15d⟩ := step_readSlot (s := s13) inp slVLocal (by decide) 2 (by decide : (2 : Fin 16) ≠ 15) vW h13dV
    (by rw [h13pc]; exact placedSlice_fetch hPrePl (k := 13) rfl)
    (by rw [h13pc]; exact placedSlice_fetch hPrePl (k := 14) rfl)
    (prog_pc_lt_const (by rw [h13pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h13pc]; dsimp only [pc5a]; omega))
  rw [h13pc] at h15pc
  have h15r1 : reg s15 1 = uW := by
    rw [h15r 1 (by decide : (1 : Fin 16) ≠ 2) (by decide : (1 : Fin 16) ≠ 15)]; exact h13r1
  have h15r14 : reg s15 14 = descBaseW := by
    rw [h15r 14 (by decide : (14 : Fin 16) ≠ 2) (by decide : (14 : Fin 16) ≠ 15),
      h13r 14 (by decide : (14 : Fin 16) ≠ 1) (by decide : (14 : Fin 16) ≠ 15),
      h11r 14 (by decide : (14 : Fin 16) ≠ 15)]; exact h9r14
  have h15d : s15.data = s.data.set slDescBase descBaseW (by rw [hDataSz]; decide) := by
    rw [h15d, h13d, h11d]; simp only [h9d, h9r14]
  have hp0_15 : Steps prog inp 15 s s15 :=
    Steps.cons hs0 (Steps.cons hs1 (hs23.append (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (hs9_10.append (hs11_12.append hs13_14)))))))))
  -- Steps 15..22: orient pair into (r3 = swapped, r11 = key0, r12 = key1) at pc5a + 23
  let Pcan := P.canonical
  have hCanOrd : Pcan.fst < Pcan.snd := by
    dsimp only [Pcan]
    by_cases hlt : P.fst < P.snd
    · simp [CutPair.canonical, hlt]
    · have hne : P.fst ≠ P.snd := P.ne
      have hgt : P.snd < P.fst := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hne (Fin.ext h.symm))
      simp [CutPair.canonical, hlt, hgt]
  have hCanVal0 : Pcan.fst.val = if uW.val < vW.val then uW.val else vW.val := by
    rw [huWv, hvWv]; dsimp only [Pcan]
    by_cases hlt : P.fst < P.snd
    · have hltN : P.fst.val < P.snd.val := hlt
      simp [CutPair.canonical, hlt, hltN]
    · have hltN : ¬ P.fst.val < P.snd.val := hlt
      simp [CutPair.canonical, hlt, hltN]
  have hCanVal1 : Pcan.snd.val = if uW.val < vW.val then vW.val else uW.val := by
    rw [huWv, hvWv]; dsimp only [Pcan]
    by_cases hlt : P.fst < P.snd
    · have hltN : P.fst.val < P.snd.val := hlt
      simp [CutPair.canonical, hlt, hltN]
    · have hltN : ¬ P.fst.val < P.snd.val := hlt
      simp [CutPair.canonical, hlt, hltN]
  have h23Branch : ∃ s23 k15_23, k15_23 ≤ 5 ∧ Steps prog inp k15_23 s15 s23 ∧
      s23.pc = pc5a + 23 ∧
      reg s23 3 = (if P.fst < P.snd then zeroW bits else oneW hTag) ∧
      reg s23 11 = (if P.fst < P.snd then uW else vW) ∧
      reg s23 12 = (if P.fst < P.snd then vW else uW) ∧
      reg s23 14 = descBaseW ∧
      s23.data = s15.data := by
    by_cases hlt : P.fst < P.snd
    · have hltW : (reg s15 1).val < (reg s15 2).val := by rw [h15r1, h15r2, huWv, hvWv]; exact hlt
      have hs15 := step_branchLt16 inp (by rw [h15pc]; exact placedSlice_fetch hPrePl (k := 15) rfl) (by
        change (if (reg s15 1).val < (reg s15 2).val then pc5a + 16 else pc5a + 20) < _
        rw [ite_eq_left hltW]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
      let s16 := { s15 with pc := if (reg s15 1).val < (reg s15 2).val then pc5a + 16 else pc5a + 20 }
      have h16pc : s16.pc = pc5a + 16 := by change (if (reg s15 1).val < (reg s15 2).val then _ else _) = _; exact ite_eq_left hltW
      have hs16 := step_imm16 inp (s := s16) (by rw [h16pc]; exact placedSlice_fetch hPrePl (k := 16) rfl)
        (prog_pc_lt_const (by rw [h16pc]; dsimp only [pc5a]; omega))
      let s17 := putReg rfl s16 3 (zeroW bits)
      have hs17 := step_mov16 inp (s := s17) (by simp [s17, putReg_pc, h16pc]; exact placedSlice_fetch hPrePl (k := 17) rfl)
        (prog_pc_lt_const (by simp [s17, putReg_pc, h16pc]; dsimp only [pc5a]; omega))
      let s18 := putReg rfl s17 11 (reg s17 1)
      have hs18 := step_mov16 inp (s := s18) (by simp [s18, s17, putReg_pc, h16pc]; exact placedSlice_fetch hPrePl (k := 18) rfl)
        (prog_pc_lt_const (by simp [s18, s17, putReg_pc, h16pc]; dsimp only [pc5a]; omega))
      let s19 := putReg rfl s18 12 (reg s18 2)
      have hs19 := step_goto16 inp (s := s19) (by simp [s19, s18, s17, putReg_pc, h16pc]; exact placedSlice_fetch hPrePl (k := 19) rfl)
        (prog_pc_lt_const (by dsimp only [pc5a]; omega))
      let s23 := { s19 with pc := pc5a + 23 }
      refine ⟨s23, 5, by decide, Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19 (Steps.zero s23))))),
        rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [ite_eq_left hlt]; change reg s19 3 = zeroW bits
        rw [putReg_eq_other s18 (by decide : (3 : Fin 16) ≠ 12),
          putReg_eq_other s17 (by decide : (3 : Fin 16) ≠ 11)]; exact putReg_eq_same s16 3 _
      · rw [ite_eq_left hlt]; change reg s19 11 = uW
        rw [putReg_eq_other s18 (by decide : (11 : Fin 16) ≠ 12)]
        change reg s18 11 = uW
        rw [putReg_eq_same s17 11 _, putReg_eq_other s16 (by decide : (1 : Fin 16) ≠ 3)]; exact h15r1
      · rw [ite_eq_left hlt]; change reg s19 12 = vW
        rw [putReg_eq_same s18 12 _, putReg_eq_other s17 (by decide : (2 : Fin 16) ≠ 11),
          putReg_eq_other s16 (by decide : (2 : Fin 16) ≠ 3)]; exact h15r2
      · change reg s19 14 = descBaseW
        rw [putReg_eq_other s18 (by decide : (14 : Fin 16) ≠ 12), putReg_eq_other s17 (by decide : (14 : Fin 16) ≠ 11),
          putReg_eq_other s16 (by decide : (14 : Fin 16) ≠ 3)]; exact h15r14
      · rfl
    · have hltW : ¬ ((reg s15 1).val < (reg s15 2).val) := by rw [h15r1, h15r2, huWv, hvWv]; exact hlt
      have hs15 := step_branchLt16 inp (by rw [h15pc]; exact placedSlice_fetch hPrePl (k := 15) rfl) (by
        change (if (reg s15 1).val < (reg s15 2).val then pc5a + 16 else pc5a + 20) < _
        rw [ite_eq_right hltW]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
      let s20 := { s15 with pc := if (reg s15 1).val < (reg s15 2).val then pc5a + 16 else pc5a + 20 }
      have h20pc : s20.pc = pc5a + 20 := by change (if (reg s15 1).val < (reg s15 2).val then _ else _) = _; exact ite_eq_right hltW
      have hs20 := step_imm16 inp (s := s20) (by rw [h20pc]; exact placedSlice_fetch hPrePl (k := 20) rfl)
        (prog_pc_lt_const (by rw [h20pc]; dsimp only [pc5a]; omega))
      let s21 := putReg rfl s20 3 (oneW hTag)
      have hs21 := step_mov16 inp (s := s21) (by simp [s21, putReg_pc, h20pc]; exact placedSlice_fetch hPrePl (k := 21) rfl)
        (prog_pc_lt_const (by simp [s21, putReg_pc, h20pc]; dsimp only [pc5a]; omega))
      let s22 := putReg rfl s21 11 (reg s21 2)
      have hs22 := step_mov16 inp (s := s22) (by simp [s22, s21, putReg_pc, h20pc]; exact placedSlice_fetch hPrePl (k := 22) rfl)
        (prog_pc_lt_const (by simp [s22, s21, putReg_pc, h20pc]; dsimp only [pc5a]; omega))
      let s23 := putReg rfl s22 12 (reg s22 1)
      refine ⟨s23, 4, by decide, Steps.cons hs15 (Steps.cons hs20 (Steps.cons hs21 (Steps.cons hs22 (Steps.zero s23)))),
        by simp [s23, s22, s21, putReg_pc, h20pc], ?_, ?_, ?_, ?_, ?_⟩
      · rw [ite_eq_right hlt]; change reg s23 3 = oneW hTag
        rw [putReg_eq_other s22 (by decide : (3 : Fin 16) ≠ 12),
          putReg_eq_other s21 (by decide : (3 : Fin 16) ≠ 11)]; exact putReg_eq_same s20 3 _
      · rw [ite_eq_right hlt]; change reg s23 11 = vW
        rw [putReg_eq_other s22 (by decide : (11 : Fin 16) ≠ 12)]
        change reg s22 11 = vW
        rw [putReg_eq_same s21 11 _, putReg_eq_other s20 (by decide : (2 : Fin 16) ≠ 3)]; exact h15r2
      · rw [ite_eq_right hlt]; change reg s23 12 = uW
        rw [putReg_eq_same s22 12 _, putReg_eq_other s21 (by decide : (1 : Fin 16) ≠ 11),
          putReg_eq_other s20 (by decide : (1 : Fin 16) ≠ 3)]; exact h15r1
      · change reg s23 14 = descBaseW
        rw [putReg_eq_other s22 (by decide : (14 : Fin 16) ≠ 12), putReg_eq_other s21 (by decide : (14 : Fin 16) ≠ 11),
          putReg_eq_other s20 (by decide : (14 : Fin 16) ≠ 3)]; exact h15r14
      · rfl
  obtain ⟨s23, k15_23, hk15_23, hs15_23, h23pc, h23r3, h23r11, h23r12, h23r14, h23d⟩ := h23Branch
  let swW := if P.fst < P.snd then zeroW bits else oneW hTag
  let k0W := if P.fst < P.snd then uW else vW
  let k1W := if P.fst < P.snd then vW else uW
  have hk0Val : k0W.val = Pcan.fst.val := by
    dsimp only [k0W, Pcan]; by_cases hlt : P.fst < P.snd <;> simp [CutPair.canonical, hlt, huWv, hvWv]
  have hk1Val : k1W.val = Pcan.snd.val := by
    dsimp only [k1W, Pcan]; by_cases hlt : P.fst < P.snd <;> simp [CutPair.canonical, hlt, huWv, hvWv]
  -- Steps 23..36: store slSwapped, slKey0, slKey1, load dictPtr & nDict, prepare pair search
  have h23dsz : s23.data.size = queryWorkCap := by rw [h23d, h15d]; simp [s.data_size]
  obtain ⟨s25, hs23_24, h25pc, h25r, _, h25d⟩ := step_writeSlot inp slSwapped (by decide) 3 (by decide : (3 : Fin 16) ≠ 15)
    (by rw [h23pc]; exact placedSlice_fetch hPrePl (k := 23) rfl)
    (by rw [h23pc]; exact placedSlice_fetch hPrePl (k := 24) rfl)
    (prog_pc_lt_const (by rw [h23pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h23pc]; dsimp only [pc5a]; omega))
  rw [h23pc] at h25pc
  obtain ⟨s27, hs25_26, h27pc, h27r, _, h27d⟩ := step_writeSlot inp slKey0 (by decide) 11 (by decide : (11 : Fin 16) ≠ 15)
    (by rw [h25pc]; exact placedSlice_fetch hPrePl (k := 25) rfl)
    (by rw [h25pc]; exact placedSlice_fetch hPrePl (k := 26) rfl)
    (prog_pc_lt_const (by rw [h25pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h25pc]; dsimp only [pc5a]; omega))
  rw [h25pc] at h27pc
  obtain ⟨s29, hs27_28, h29pc, h29r, _, h29d⟩ := step_writeSlot inp slKey1 (by decide) 12 (by decide : (12 : Fin 16) ≠ 15)
    (by rw [h27pc]; exact placedSlice_fetch hPrePl (k := 27) rfl)
    (by rw [h27pc]; exact placedSlice_fetch hPrePl (k := 28) rfl)
    (prog_pc_lt_const (by rw [h27pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h27pc]; dsimp only [pc5a]; omega))
  rw [h27pc] at h29pc
  have h25r11 : reg s25 11 = k0W := by
    rw [h25r 11 (by decide : (11 : Fin 16) ≠ 15)]; exact h23r11
  have h27r12 : reg s27 12 = k1W := by
    rw [h27r 12 (by decide : (12 : Fin 16) ≠ 15), h25r 12 (by decide : (12 : Fin 16) ≠ 15)]; exact h23r12
  have h29r11 : reg s29 11 = k0W := by
    rw [h29r 11 (by decide : (11 : Fin 16) ≠ 15), h27r 11 (by decide : (11 : Fin 16) ≠ 15)]; exact h25r11
  have h29r12 : reg s29 12 = k1W := by
    rw [h29r 12 (by decide : (12 : Fin 16) ≠ 15)]; exact h27r12
  have h29r14 : reg s29 14 = descBaseW := by
    rw [h29r 14 (by decide : (14 : Fin 16) ≠ 15), h27r 14 (by decide : (14 : Fin 16) ≠ 15),
      h25r 14 (by decide : (14 : Fin 16) ≠ 15)]; exact h23r14
  -- Dict header & dictionary[0]
  have hDictSlotLt : rec.descBase + descDict < I.size := by
    have := rec.descFits; change rec.descBase + 1 < I.size; omega
  let dictPtrW := I[rec.descBase + descDict]'hDictSlotLt
  have hDictSlot? : I[rec.descBase + descDict]? = some dictPtrW := getElem?_pos I _ hDictSlotLt
  have hDictPtrVal : dictPtrW.val = rec.dictPtr := by
    have hm := rec.hDescDict; rw [hDictSlot?, Option.map_some] at hm; exact Option.some.inj hm
  have hDictAddrFit : descBaseW.val + (descW hWork descDict (by decide)).val < 2 ^ bits := by
    rw [hDescWVal]; change rec.descBase + 1 < 2 ^ bits; omega
  have hWCols0Lt : 0 < wCols.dictionary.size := by
    have := hRep.valid.keysWithin
    unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at this
    omega
  have hDict0LtI : rec.dictPtr < I.size := by have := hDictSlice.1; omega
  let nDictW := I[rec.dictPtr]'hDict0LtI
  have hDict0? : I[rec.dictPtr]? = some nDictW := getElem?_pos I rec.dictPtr hDict0LtI
  have hNDictEq : nDictW = wCols.dictionary[0]'hWCols0Lt := by
    have hs := hDictSlice.2 0 hWCols0Lt
    rw [Nat.add_zero, hDict0?] at hs
    exact Option.some.inj hs
  have hNDictVal : nDictW.val = (ofOrderedReader ordRes).dict.size := by
    have hr := hRep.rows
    have hrc : FlatPairDictionary.rowCount wCols.dictionary = (wCols.dictionary[0]'hWCols0Lt).val := by
      unfold FlatPairDictionary.rowCount
      rw [getElem?_pos wCols.dictionary 0 hWCols0Lt, Option.map_some, Option.getD_some]
    rw [← hr, hrc, hNDictEq]
  have hColFits1 : dictPtrW.val + (descW hWork descDict (by decide)).val < 2 ^ bits := by
    rw [hDictPtrVal]; change rec.dictPtr + 1 < 2 ^ bits
    have := hDictSlice.1; omega
  have hColFits2 : (dictPtrW.val + 1) + nDictW.val < 2 ^ bits := by
    rw [hDictPtrVal, hNDictVal]
    have hKW := hRep.valid.keysWithin
    rw [hRep.rows] at hKW
    unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at hKW
    have := hDictSlice.1; omega
  have hs29 := step_imm16 inp (s := s29) (by rw [h29pc]; exact placedSlice_fetch hPrePl (k := 29) rfl)
    (prog_pc_lt_const (by rw [h29pc]; dsimp only [pc5a]; omega))
  let s30 := putReg rfl s29 6 (descW hWork descDict (by decide))
  have hs30 := step_add16 inp (s := s30) (by simp [s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 30) rfl)
    (prog_pc_lt_const (by simp [s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s31 := putReg rfl s30 15 (add (reg s30 14) (reg s30 6))
  have h31r15 : (reg s31 15).val = rec.descBase + descDict := by
    have h14 : reg s30 14 = descBaseW := by
      rw [putReg_eq_other s29 (by decide : (14 : Fin 16) ≠ 6)]; exact h29r14
    have h6 : reg s30 6 = descW hWork descDict (by decide) := putReg_eq_same s29 6 _
    dsimp only [s31]; rw [putReg_eq_same]
    change (add (reg s30 14) (reg s30 6)).val = _
    rw [h14, h6, add_no_wrap _ _ hDictAddrFit, hDescWVal]; rfl
  have hs31 := step_loadInput16 inp (s := s31)
    (by simp [s31, s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 31) rfl)
    (by change I[(reg s31 15).val]? = _; rw [h31r15]; exact hDictSlot?)
    (prog_pc_lt_const (by simp [s31, s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s32 := putReg rfl s31 1 dictPtrW
  have hs32 := step_loadInput16 inp (s := s32)
    (by simp [s32, s31, s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 32) rfl)
    (by change I[(reg s32 1).val]? = _; rw [putReg_eq_same, hDictPtrVal]; exact hDict0?)
    (prog_pc_lt_const (by simp [s32, s31, s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s33 := putReg rfl s32 8 nDictW
  have hs33 := step_add16 inp (s := s33)
    (by simp [s33, s32, s31, s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 33) rfl)
    (prog_pc_lt_const (by simp [s33, s32, s31, s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s34 := putReg rfl s33 7 (add (reg s33 1) (reg s33 6))
  have hs34 := step_add16 inp (s := s34)
    (by simp [s34, s33, s32, s31, s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 34) rfl)
    (prog_pc_lt_const (by simp [s34, s33, s32, s31, s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s35 := putReg rfl s34 9 (add (reg s34 7) (reg s34 8))
  have hs35 := step_imm16 inp (s := s35)
    (by simp [s35, s34, s33, s32, s31, s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 35) rfl)
    (prog_pc_lt_const (by simp [s35, s34, s33, s32, s31, s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s36 := putReg rfl s35 4 (zeroW bits)
  have hs36 := step_imm16 inp (s := s36)
    (by simp [s36, s35, s34, s33, s32, s31, s30, putReg_pc, h29pc]; exact placedSlice_fetch hPrePl (k := 36) rfl)
    (prog_pc_lt_const (by simp [s36, s35, s34, s33, s32, s31, s30, putReg_pc, h29pc]; dsimp only [pc5a]; omega))
  let s37 := putReg rfl s36 5 (zeroW bits)
  have h37pc : s37.pc = pc5a + 37 := by simp [s37, s36, s35, s34, s33, s32, s31, s30, putReg_pc, h29pc]
  have hs29_37 : Steps prog inp 8 s29 s37 :=
    Steps.cons hs29 (Steps.cons hs30 (Steps.cons hs31 (Steps.cons hs32 (Steps.cons hs33
      (Steps.cons hs34 (Steps.cons hs35 (Steps.cons hs36 (Steps.zero s37))))))))
  have hp0_37 : Steps prog inp (15 + k15_23 + 14) s s37 := by
    have hk := (hp0_15.append hs15_23).append (hs23_24.append (hs25_26.append (hs27_28.append hs29_37)))
    simpa only [Nat.add_assoc] using hk
  -- Columns for lifted_pairSearch_exact
  let cols := columnsOfDictSlice I rec.dictPtr wCols.dictionary hDictSlice hRep hIlt
  have h37r7 : reg s37 7 = cols.first.base := by
    have h1_33 : reg s33 1 = dictPtrW := by
      rw [putReg_eq_other s32 (by decide : (1 : Fin 16) ≠ 8), putReg_eq_same s31 1 _]
    have h6_33 : reg s33 6 = descW hWork descDict (by decide) := by
      rw [putReg_eq_other s32 (by decide : (6 : Fin 16) ≠ 8), putReg_eq_other s31 (by decide : (6 : Fin 16) ≠ 1),
        putReg_eq_other s30 (by decide : (6 : Fin 16) ≠ 15), putReg_eq_same s29 6 _]
    have hr7 : reg s37 7 = add dictPtrW (descW hWork descDict (by decide)) := by
      rw [putReg_eq_other s36 (by decide : (7 : Fin 16) ≠ 5), putReg_eq_other s35 (by decide : (7 : Fin 16) ≠ 4),
        putReg_eq_other s34 (by decide : (7 : Fin 16) ≠ 9)]
      change reg (putReg rfl s33 7 (add (reg s33 1) (reg s33 6))) 7 = _
      rw [putReg_eq_same, h1_33, h6_33]
    rw [hr7]
    apply Fin.ext
    change (add dictPtrW (descW hWork descDict (by decide))).val = rec.dictPtr + 1
    rw [add_no_wrap _ _ hColFits1, hDictPtrVal]; rfl
  have h37r8 : (reg s37 8).val = cols.first.len := by
    have hr8 : reg s37 8 = nDictW := by
      rw [putReg_eq_other s36 (by decide : (8 : Fin 16) ≠ 5), putReg_eq_other s35 (by decide : (8 : Fin 16) ≠ 4),
        putReg_eq_other s34 (by decide : (8 : Fin 16) ≠ 9), putReg_eq_other s33 (by decide : (8 : Fin 16) ≠ 7),
        putReg_eq_same s32 8 _]
    rw [hr8, hNDictVal]
    exact cols.first_len.symm
  have h37r9 : reg s37 9 = cols.second.base := by
    have h1_33 : reg s33 1 = dictPtrW := by
      rw [putReg_eq_other s32 (by decide : (1 : Fin 16) ≠ 8), putReg_eq_same s31 1 _]
    have h6_33 : reg s33 6 = descW hWork descDict (by decide) := by
      rw [putReg_eq_other s32 (by decide : (6 : Fin 16) ≠ 8), putReg_eq_other s31 (by decide : (6 : Fin 16) ≠ 1),
        putReg_eq_other s30 (by decide : (6 : Fin 16) ≠ 15), putReg_eq_same s29 6 _]
    have h7_34 : reg s34 7 = add dictPtrW (descW hWork descDict (by decide)) := by
      change reg (putReg rfl s33 7 (add (reg s33 1) (reg s33 6))) 7 = _
      rw [putReg_eq_same, h1_33, h6_33]
    have h8_34 : reg s34 8 = nDictW := by
      rw [putReg_eq_other s33 (by decide : (8 : Fin 16) ≠ 7), putReg_eq_same s32 8 _]
    have hr9 : reg s37 9 = add (add dictPtrW (descW hWork descDict (by decide))) nDictW := by
      rw [putReg_eq_other s36 (by decide : (9 : Fin 16) ≠ 5), putReg_eq_other s35 (by decide : (9 : Fin 16) ≠ 4)]
      change reg (putReg rfl s34 9 (add (reg s34 7) (reg s34 8))) 9 = _
      rw [putReg_eq_same, h7_34, h8_34]
    rw [hr9]
    apply Fin.ext
    have hA : (add dictPtrW (descW hWork descDict (by decide))).val = rec.dictPtr + 1 := by
      rw [add_no_wrap _ _ hColFits1, hDictPtrVal]; rfl
    change (add (add dictPtrW (descW hWork descDict (by decide))) nDictW).val =
      rec.dictPtr + 1 + FlatPairDictionary.rowCount wCols.dictionary
    rw [add_no_wrap _ _ (by rw [hA]; rw [hDictPtrVal] at hColFits2; exact hColFits2),
      hA, hNDictVal, hRep.rows]
  have h37r11 : reg s37 11 = k0W := by
    rw [putReg_eq_other s36 (by decide : (11 : Fin 16) ≠ 5), putReg_eq_other s35 (by decide : (11 : Fin 16) ≠ 4),
      putReg_eq_other s34 (by decide : (11 : Fin 16) ≠ 9), putReg_eq_other s33 (by decide : (11 : Fin 16) ≠ 7),
      putReg_eq_other s32 (by decide : (11 : Fin 16) ≠ 8), putReg_eq_other s31 (by decide : (11 : Fin 16) ≠ 1),
      putReg_eq_other s30 (by decide : (11 : Fin 16) ≠ 15), putReg_eq_other s29 (by decide : (11 : Fin 16) ≠ 6)]
    exact h29r11
  have h37r12 : reg s37 12 = k1W := by
    rw [putReg_eq_other s36 (by decide : (12 : Fin 16) ≠ 5), putReg_eq_other s35 (by decide : (12 : Fin 16) ≠ 4),
      putReg_eq_other s34 (by decide : (12 : Fin 16) ≠ 9), putReg_eq_other s33 (by decide : (12 : Fin 16) ≠ 7),
      putReg_eq_other s32 (by decide : (12 : Fin 16) ≠ 8), putReg_eq_other s31 (by decide : (12 : Fin 16) ≠ 1),
      putReg_eq_other s30 (by decide : (12 : Fin 16) ≠ 15), putReg_eq_other s29 (by decide : (12 : Fin 16) ≠ 6)]
    exact h29r12
  have h37r4 : reg s37 4 = zero bits := by
    rw [putReg_eq_other s36 (by decide : (4 : Fin 16) ≠ 5)]; exact putReg_eq_same s35 4 _
  have h37r5 : reg s37 5 = zero bits := putReg_eq_same s36 5 _
  have h37data : s37.data = s29.data := by simp [s37, s36, s35, s34, s33, s32, s31, s30, putReg_data]
  have h29frame : ∀ idx, idx < 14 → s29.data[idx]? = s.data[idx]? := by
    intro idx hidx
    rw [h29d, data_set_other _ _ _ _ (by dsimp only [slKey1]; omega),
      h27d, data_set_other _ _ _ _ (by dsimp only [slKey0]; omega),
      h25d, data_set_other _ _ _ _ (by dsimp only [slSwapped]; omega),
      h23d, h15d, data_set_other _ _ _ _ (by dsimp only [slDescBase]; omega)]
  have h29dDesc : s29.data[slDescBase]? = some descBaseW := by
    rw [h29d, data_set_other _ _ _ _ (by decide),
      h27d, data_set_other _ _ _ _ (by decide),
      h25d, data_set_other _ _ _ _ (by decide),
      h23d, h15d, data_set_same]
  have h29dSw : s29.data[slSwapped]? = some swW := by
    rw [h29d, data_set_other _ _ _ _ (by decide),
      h27d, data_set_other _ _ _ _ (by decide),
      h25d, data_set_same, h23r3]
  have h29dK0 : s29.data[slKey0]? = some k0W := by
    rw [h29d, data_set_other _ _ _ _ (by decide),
      h27d, data_set_same, h25r11]
  have h29dK1 : s29.data[slKey1]? = some k1W := by
    rw [h29d, data_set_same, h27r12]
  have hCodeCan : orderedPairCode Pcan = (k0W.val, k1W.val) := by
    change (Pcan.fst.val, Pcan.snd.val) = (k0W.val, k1W.val)
    rw [hk0Val, hk1Val]
  -- Run lifted_pairSearch_exact
  obtain ⟨s114, kSearch, hkSearch, hsSearch, h114pc, h114r0, h114r3, h114d⟩ :=
    lifted_pairSearch_exact rfl hOne hSearchPl (prog_pc_lt_const (by dsimp only [pc5a]; omega))
      inp s37 h37pc cols (dict_sorted ordRes) k0W k1W
      h37r7 h37r8 h37r9 h37r11 h37r12 h37r4 h37r5
  have h114dsz : s114.data.size = queryWorkCap := by
    rw [h114d, h37data, h29d, Array.size_set, h27d, Array.size_set, h25d, Array.size_set, h23dsz]
  have hp0_114 : Steps prog inp (15 + k15_23 + 14 + kSearch) s s114 := hp0_37.append hsSearch
  have hSwVal : swW.val = if P.fst < P.snd then 0 else 1 := by
    dsimp only [swW]
    by_cases hlt : P.fst < P.snd
    · rw [ite_eq_left hlt, ite_eq_left hlt]; rfl
    · rw [ite_eq_right hlt, ite_eq_right hlt]; rfl
  have h114Y : s114.data[slYLocal]? = some yW := by
    rw [h114d, h37data, h29d, data_set_other _ _ _ _ (by decide),
      h27d, data_set_other _ _ _ _ (by decide),
      h25d, data_set_other _ _ _ _ (by decide),
      h23d, h15d, data_set_other _ _ _ _ (by decide)]
    exact hyW
  exact ⟨s114, descBaseW, swW, k0W, k1W, yW, 15 + k15_23 + 14 + kSearch,
    by omega, hp0_114, h114pc, hDescWVal, hSwVal, hk0Val, hk1Val, hyWv,
    h114r0, h114r3, h114dsz,
    (fun idx hidx => by rw [h114d, h37data]; exact h29frame idx hidx),
    (by rw [h114d, h37data]; exact h29dDesc),
    (by rw [h114d, h37data]; exact h29dSw),
    (by rw [h114d, h37data]; exact h29dK0),
    (by rw [h114d, h37data]; exact h29dK1),
    h114Y⟩

private theorem exec_blkPairAndKnown_phase2
    {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {dDense : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr dDense)
    {large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK dDense)}
    {dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))}
    {sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense) → Nat}
    (ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large)
    (wCols : WordColumns bits)
    (hDictSlice : SliceAt I rec.dictPtr wCols.dictionary)
    (hRep : FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordRes))
    (hBackFst : SliceAt I rec.backFstPtr wCols.back.tagAndFirst)
    (hBackSnd : SliceAt I rec.backSndPtr wCols.back.second)
    (hBackSz : wCols.back.tagAndFirst.size = wCols.back.second.size)
    (hBackRead : ∀ j (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense)),
      wCols.back.read j = some (encodeBackPair (some P)) ↔
        (ofOrderedReader ordRes).back[j]? = some (some P))
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (s114 : State (codeLayout bits I.size hI hWork))
    (descBaseW swW k0W k1W yW : Word bits)
    (h114pc : s114.pc = pc5a + 114)
    (hDescWVal : descBaseW.val = rec.descBase)
    (hk0Val : k0W.val = P.canonical.fst.val)
    (hk1Val : k1W.val = P.canonical.snd.val)
    (h114r0 : (reg s114 (r16 rfl 0)).val =
      (if (PairLookup.lookup (ofOrderedReader ordRes).dict (k0W.val, k1W.val)).1.isSome then 1 else 0))
    (h114r3 : ∀ row : Nat,
      (PairLookup.lookup (ofOrderedReader ordRes).dict (k0W.val, k1W.val)).1 = some row →
      (reg s114 (r16 rfl 3)).val = row)
    (h114dsz : s114.data.size = queryWorkCap)
    (h114Desc : s114.data[slDescBase]? = some descBaseW)
    (h114Sw : s114.data[slSwapped]? = some swW)
    (h114K0 : s114.data[slKey0]? = some k0W)
    (h114K1 : s114.data[slKey1]? = some k1W)
    (h114Y : s114.data[slYLocal]? = some yW) :
    let prog := oracleQueryProgram hI hWork hTag
    let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
    (checkedHit ordRes P.canonical = none →
      ∃ t k2, k2 ≤ 47 ∧ Steps prog inp k2 s114 t ∧ t.pc = okPC hI hTag) ∧
    (∀ aNode : Nat, checkedHit ordRes P.canonical = some aNode →
      ∃ s167 k2, k2 ≤ 47 ∧ Steps prog inp k2 s114 s167 ∧
        s167.pc = pc5a + 167 ∧
        s167.data.size = queryWorkCap ∧
        (∀ idx, idx < 14 → s167.data[idx]? = s114.data[idx]?) ∧
        s167.data[slDescBase]? = some descBaseW ∧
        s167.data[slSwapped]? = some swW ∧
        (s167.data[slHitNode]?).map Fin.val = some aNode ∧
        s167.data[slYLocal]? = some yW) := by
  intro prog inp
  have hOne : 1 < 2 ^ bits := Nat.lt_trans (by decide : 1 < 2) hTag
  have h5aPl := place_blk5a hI hWork hTag
  unfold blkPairAndKnown at h5aPl
  have hEqSz : (ThreeCalls.EqualityTail.checkedProgram hI hOne (ThreeCalls.concreteSetup bits hOne)).size = 77 :=
    ThreeCalls.EqualityTail.checkedProgram_size hI hOne (ThreeCalls.concreteSetup bits hOne)
  have hMid1Pl := placedSlice_right_pc (n := pc5a + 114) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left h5aPl)))))) (by simp [liftMap, hEqSz, pc5a])
  have hGuard1Pl := placedSlice_right_pc (n := pc5a + 138) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h5aPl)))))
    (by simp [liftMap, hEqSz, pc5a])
  have hMid2Pl := placedSlice_right_pc (n := pc5a + 145) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left h5aPl))))
    (by simp [liftMap, PairGuard.rom, hEqSz, pc5a])
  have hGuard2Pl := placedSlice_right_pc (n := pc5a + 158) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left h5aPl)))
    (by simp [liftMap, PairGuard.rom, hEqSz, pc5a])
  have hMid3Pl := placedSlice_right_pc (n := pc5a + 165) (placedSlice_append_left (placedSlice_append_left h5aPl))
    (by simp [liftMap, PairGuard.rom, hEqSz, pc5a])
  have hIlt : I.size < 2 ^ bits := by
    have htf : hdrTotalWords < I.size := Nat.lt_of_lt_of_le (by decide) Hdr.hdr_fit
    have hm := Hdr.hTotal
    rw [getElem?_pos I hdrTotalWords htf, Option.map_some] at hm
    rw [← Option.some.inj hm]
    exact (I[hdrTotalWords]'htf).isLt
  have hDescFits : rec.descBase + 10 ≤ I.size := rec.descFits
  have hDictSlotLt : rec.descBase + descDict < I.size := by change rec.descBase + 1 < I.size; omega
  let dictPtrW := I[rec.descBase + descDict]'hDictSlotLt
  have hDictSlot? : I[rec.descBase + descDict]? = some dictPtrW := getElem?_pos I _ hDictSlotLt
  have hDictPtrVal : dictPtrW.val = rec.dictPtr := by
    have hm := rec.hDescDict; rw [hDictSlot?, Option.map_some] at hm; exact Option.some.inj hm
  have hDictAddrFit : descBaseW.val + (descW hWork descDict (by decide)).val < 2 ^ bits := by
    rw [hDescWVal]; change rec.descBase + 1 < 2 ^ bits; omega
  have hWCols0Lt : 0 < wCols.dictionary.size := by
    have := hRep.valid.keysWithin
    unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at this
    omega
  have hDict0LtI : rec.dictPtr < I.size := by have := hDictSlice.1; omega
  let nDictW := I[rec.dictPtr]'hDict0LtI
  have hDict0? : I[rec.dictPtr]? = some nDictW := getElem?_pos I rec.dictPtr hDict0LtI
  have hNDictEq : nDictW = wCols.dictionary[0]'hWCols0Lt := by
    have hs := hDictSlice.2 0 hWCols0Lt
    rw [Nat.add_zero, hDict0?] at hs
    exact Option.some.inj hs
  have hNDictVal : nDictW.val = (ofOrderedReader ordRes).dict.size := by
    have hr := hRep.rows
    have hrc : FlatPairDictionary.rowCount wCols.dictionary = (wCols.dictionary[0]'hWCols0Lt).val := by
      unfold FlatPairDictionary.rowCount
      rw [getElem?_pos wCols.dictionary 0 hWCols0Lt, Option.map_some, Option.getD_some]
    rw [← hr, hrc, hNDictEq]
  have hColFits1 : dictPtrW.val + (descW hWork descDict (by decide)).val < 2 ^ bits := by
    rw [hDictPtrVal]; change rec.dictPtr + 1 < 2 ^ bits
    have := hDictSlice.1; omega
  have hColFits2 : (dictPtrW.val + 1) + nDictW.val < 2 ^ bits := by
    rw [hDictPtrVal, hNDictVal]
    have hKW := hRep.valid.keysWithin
    rw [hRep.rows] at hKW
    unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at hKW
    have := hDictSlice.1; omega
  let Pcan := P.canonical
  have hCanOrd : Pcan.fst < Pcan.snd := by
    dsimp only [Pcan]
    by_cases hlt : P.fst < P.snd
    · simp [CutPair.canonical, hlt]
    · have hne : P.fst ≠ P.snd := P.ne
      have hgt : P.snd < P.fst := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hne (Fin.ext h.symm))
      simp [CutPair.canonical, hlt, hgt]
  have hCodeCan : orderedPairCode Pcan = (k0W.val, k1W.val) := by
    change (Pcan.fst.val, Pcan.snd.val) = (k0W.val, k1W.val)
    rw [hk0Val, hk1Val]
  -- Helpers connecting Grounded + checkedHit
  obtain ⟨_, F', hG, _, _⟩ := ordRes.index.ok.2.2
  have hLookupBack : ∀ (row : Nat),
      (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = some row →
      let a := ((ofOrderedReader ordRes).slots[row]?).getD 0
      row < (ofOrderedReader ordRes).dict.size ∧
      (a = 0 → checkedHit ordRes Pcan = none) ∧
      (a ≠ 0 → ∃ q', (ofOrderedReader ordRes).back[a]? = some (some q')) := by
    intro row hrow a
    have hrowLt : row < (ofOrderedReader ordRes).dict.size :=
      ((PairLookup.lookup_eq_some_iff _ _ (dict_sorted ordRes) row).mp hrow).1
    refine ⟨hrowLt, ?_, ?_⟩
    · intro ha0
      cases hc : checkedHit ordRes Pcan with
      | none => rfl
      | some a' =>
        have hb := (checked_iff_back ordRes Pcan a').mp hc
        obtain ⟨_, ha'ne, j, hj, hslot⟩ := hG.backward a' Pcan hb
        have hj' : (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = some j := hj
        have hrj : row = j := Option.some.inj (hrow.symm.trans hj')
        have haEq : a' = a := by rw [← hslot, ← hrj]; rfl
        exact absurd (haEq.trans ha0) ha'ne
    · intro haNe
      obtain ⟨q', _, hqb⟩ := hG.forward row (by exact haNe)
      exact ⟨q', hqb⟩
  have hMissOfNone : (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = none →
      checkedHit ordRes Pcan = none := by
    intro hnone
    cases hc : checkedHit ordRes Pcan with
    | none => rfl
    | some a' =>
      have hb := (checked_iff_back ordRes Pcan a').mp hc
      obtain ⟨_, _, j, hj, _⟩ := hG.backward a' Pcan hb
      have : (none : Option Nat) = some j := hnone.symm.trans hj
      cases this
  -- Execute post-search jump on dict miss
  have hDictMissPath :
      (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = none →
      ∃ t k2, k2 ≤ 47 ∧ Steps prog inp k2 s114 t ∧ t.pc = okPC hI hTag := by
    intro hnone
    have h114r0_0 : (reg s114 0).val = 0 := by
      change (reg s114 (r16 rfl 0)).val = 0
      rw [h114r0, ← hCodeCan, hnone]; rfl
    have hs114 := step_imm16 inp (s := s114)
      (by rw [h114pc]; exact placedSlice_fetch hMid1Pl (k := 0) rfl)
      (prog_pc_lt_const (by rw [h114pc]; dsimp only [pc5a]; omega))
    let s115 := putReg rfl s114 6 (oneW hTag)
    have hlt115 : (reg s115 0).val < (reg s115 6).val := by
      have h0 : reg s115 0 = reg s114 0 := putReg_eq_other s114 (by decide : (0 : Fin 16) ≠ 6) _
      have h6 : reg s115 6 = oneW hTag := putReg_eq_same s114 6 _
      rw [h0, h6, h114r0_0]; exact (by decide : 0 < 1)
    have hs115 := step_branchLt16 inp (s := s115)
      (by simp [s115, putReg_pc, h114pc]; exact placedSlice_fetch hMid1Pl (k := 1) rfl)
      (by
        change (if (reg s115 0).val < (reg s115 6).val then okPC hI hTag else pc5a + 116) < _
        rw [ite_eq_left hlt115]; exact okPC_lt hI hWork hTag)
    let t := { s115 with pc := if (reg s115 0).val < (reg s115 6).val then okPC hI hTag else pc5a + 116 }
    refine ⟨t, 2, by decide,
      Steps.cons hs114 (Steps.cons hs115 (Steps.zero t)), ?_⟩
    change (if (reg s115 0).val < (reg s115 6).val then _ else _) = _
    exact ite_eq_left hlt115
  -- For any lookup = some row, advance to pc5a + 128 (or okPC if slot = 0)
  have hRowBranch : ∀ row,
      (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = some row →
      let a := ((ofOrderedReader ordRes).slots[row]?).getD 0
      (a = 0 → ∃ t k2, k2 ≤ 47 ∧ Steps prog inp k2 s114 t ∧ t.pc = okPC hI hTag) ∧
      (a ≠ 0 → ∃ (s128 : State (codeLayout bits I.size hI hWork)) (aW : Word bits),
        Steps prog inp 14 s114 s128 ∧
        s128.pc = pc5a + 128 ∧
        aW.val = a ∧
        reg s128 2 = aW ∧
        reg s128 6 = oneW hTag ∧
        reg s128 14 = descBaseW ∧
        s128.data = s114.data) := by
    intro row hrow a
    have hrowKey : (PairLookup.lookup (ofOrderedReader ordRes).dict (k0W.val, k1W.val)).1 = some row := by
      rw [← hCodeCan]; exact hrow
    obtain ⟨hrowLt, _, hHasBack⟩ := hLookupBack row hrow
    have h114r0_1 : (reg s114 0).val = 1 := by
      change (reg s114 (r16 rfl 0)).val = 1
      rw [h114r0, hrowKey]; rfl
    have h114r3' : (reg s114 3).val = row := h114r3 row hrowKey
    have hs114 := step_imm16 inp (s := s114)
      (by rw [h114pc]; exact placedSlice_fetch hMid1Pl (k := 0) rfl)
      (prog_pc_lt_const (by rw [h114pc]; dsimp only [pc5a]; omega))
    let s115 := putReg rfl s114 6 (oneW hTag)
    have hge115 : ¬ ((reg s115 0).val < (reg s115 6).val) := by
      have h0 : reg s115 0 = reg s114 0 := putReg_eq_other s114 (by decide : (0 : Fin 16) ≠ 6) _
      have h6 : reg s115 6 = oneW hTag := putReg_eq_same s114 6 _
      rw [h0, h6, h114r0_1]; change ¬ (1 < 1); omega
    have hs115 := step_branchLt16 inp (s := s115)
      (by simp [s115, putReg_pc, h114pc]; exact placedSlice_fetch hMid1Pl (k := 1) rfl)
      (by
        change (if (reg s115 0).val < (reg s115 6).val then okPC hI hTag else pc5a + 116) < _
        rw [ite_eq_right hge115]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
    let s116 := { s115 with pc := if (reg s115 0).val < (reg s115 6).val then okPC hI hTag else pc5a + 116 }
    have h116pc : s116.pc = pc5a + 116 := by
      change (if (reg s115 0).val < (reg s115 6).val then _ else _) = _; exact ite_eq_right hge115
    have h116dDesc : s116.data[slDescBase]? = some descBaseW := by
      change s114.data[slDescBase]? = _; exact h114Desc
    obtain ⟨s118, hs116_117, h118pc, h118r, h118r14, _, h118d⟩ := step_readSlot (s := s116) inp slDescBase (by decide) 14 (by decide : (14 : Fin 16) ≠ 15) descBaseW
      h116dDesc
      (by rw [h116pc]; exact placedSlice_fetch hMid1Pl (k := 2) rfl)
      (by rw [h116pc]; exact placedSlice_fetch hMid1Pl (k := 3) rfl)
      (prog_pc_lt_const (by rw [h116pc]; dsimp only [pc5a]; omega))
      (prog_pc_lt_const (by rw [h116pc]; dsimp only [pc5a]; omega))
    rw [h116pc] at h118pc
    have h118r3 : reg s118 3 = reg s114 3 := by
      rw [h118r 3 (by decide : (3 : Fin 16) ≠ 14) (by decide : (3 : Fin 16) ≠ 15)]
      exact putReg_eq_other s114 (by decide : (3 : Fin 16) ≠ 6) _
    have h118r6 : reg s118 6 = oneW hTag := by
      rw [h118r 6 (by decide : (6 : Fin 16) ≠ 14) (by decide : (6 : Fin 16) ≠ 15)]
      exact putReg_eq_same s114 6 _
    have hs118 := step_imm16 inp (s := s118)
      (by rw [h118pc]; exact placedSlice_fetch hMid1Pl (k := 4) rfl)
      (prog_pc_lt_const (by rw [h118pc]; dsimp only [pc5a]; omega))
    let s119 := putReg rfl s118 7 (descW hWork descDict (by decide))
    have hs119 := step_add16 inp (s := s119)
      (by simp [s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 5) rfl)
      (prog_pc_lt_const (by simp [s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s120 := putReg rfl s119 15 (add (reg s119 14) (reg s119 7))
    have h120r15 : (reg s120 15).val = rec.descBase + descDict := by
      have h14 : reg s119 14 = descBaseW := by
        rw [putReg_eq_other s118 (by decide : (14 : Fin 16) ≠ 7)]; exact h118r14
      have h7 : reg s119 7 = descW hWork descDict (by decide) := putReg_eq_same s118 7 _
      dsimp only [s120]; rw [putReg_eq_same]
      change (add (reg s119 14) (reg s119 7)).val = _
      rw [h14, h7, add_no_wrap _ _ hDictAddrFit, hDescWVal]; rfl
    have hs120 := step_loadInput16 inp (s := s120)
      (by simp [s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 6) rfl)
      (by change I[(reg s120 15).val]? = _; rw [h120r15]; exact hDictSlot?)
      (prog_pc_lt_const (by simp [s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s121 := putReg rfl s120 1 dictPtrW
    have hs121 := step_loadInput16 inp (s := s121)
      (by simp [s121, s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 7) rfl)
      (by change I[(reg s121 1).val]? = _; rw [putReg_eq_same, hDictPtrVal]; exact hDict0?)
      (prog_pc_lt_const (by simp [s121, s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s122 := putReg rfl s121 8 nDictW
    have hs122 := step_add16 inp (s := s122)
      (by simp [s122, s121, s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 8) rfl)
      (prog_pc_lt_const (by simp [s122, s121, s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s123 := putReg rfl s122 1 (add (reg s122 1) (reg s122 6))
    have hs123 := step_add16 inp (s := s123)
      (by simp [s123, s122, s121, s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 9) rfl)
      (prog_pc_lt_const (by simp [s123, s122, s121, s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s124 := putReg rfl s123 1 (add (reg s123 1) (reg s123 8))
    have hs124 := step_add16 inp (s := s124)
      (by simp [s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 10) rfl)
      (prog_pc_lt_const (by simp [s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s125 := putReg rfl s124 1 (add (reg s124 1) (reg s124 8))
    -- Compute exact address dictPtr + 1 + nDict + nDict + row in I
    have hSlotLen : row < (FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).len := by
      have := hRep.slot_len
      have hss : (ofOrderedReader ordRes).slots.size = (ofOrderedReader ordRes).dict.size := by
        obtain ⟨_, _, hG', _, _⟩ := ordRes.index.ok.2.2
        exact hG'.slot_size
      omega
    have hBase1Lt : dictPtrW.val + (oneW hTag).val < 2 ^ bits := by
      change dictPtrW.val + (descW hWork descDict (by decide)).val < 2 ^ bits; exact hColFits1
    have hBase2Lt : (dictPtrW.val + 1) + nDictW.val < 2 ^ bits := hColFits2
    have hBase3Lt : (dictPtrW.val + 1 + nDictW.val) + nDictW.val < 2 ^ bits := by
      have hKW := hRep.valid.keysWithin
      rw [hRep.rows] at hKW
      unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at hKW
      have := hDictSlice.1
      rw [hDictPtrVal, hNDictVal]
      omega
    have hSlotAddrLt : (dictPtrW.val + 1 + nDictW.val + nDictW.val) + row < I.size := by
      have hW := (FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).within
      have hBase : (FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).base.val =
          FlatPairDictionary.slotBase (FlatPairDictionary.rowCount wCols.dictionary) := rfl
      rw [hBase, hRep.rows] at hW
      unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at hW
      have := hDictSlice.1
      rw [hDictPtrVal, hNDictVal]
      omega
    have hSlotAddrFit : (dictPtrW.val + 1 + nDictW.val + nDictW.val) + row < 2 ^ bits :=
      Nat.lt_of_lt_of_le hSlotAddrLt hI
    have hSlotEq : (I[(dictPtrW.val + 1 + nDictW.val + nDictW.val) + row]'hSlotAddrLt).val = a := by
      have hIdxW : 1 + 2 * (ofOrderedReader ordRes).dict.size + row < wCols.dictionary.size := by
        have hW := (FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).within
        have hBase : (FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).base.val =
            FlatPairDictionary.slotBase (FlatPairDictionary.rowCount wCols.dictionary) := rfl
        rw [hBase, hRep.rows] at hW
        unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase at hW
        omega
      have hSl := hDictSlice.2 (1 + 2 * (ofOrderedReader ordRes).dict.size + row) hIdxW
      have hIdxEq : (dictPtrW.val + 1 + nDictW.val + nDictW.val) + row =
          rec.dictPtr + (1 + 2 * (ofOrderedReader ordRes).dict.size + row) := by
        rw [hDictPtrVal, hNDictVal]; omega
      have hElem : I[(dictPtrW.val + 1 + nDictW.val + nDictW.val) + row]? =
          some (wCols.dictionary[1 + 2 * (ofOrderedReader ordRes).dict.size + row]'hIdxW) := by
        rw [hIdxEq]; exact hSl
      rw [getElem?_pos I _ hSlotAddrLt] at hElem
      have hw : I[(dictPtrW.val + 1 + nDictW.val + nDictW.val) + row]'hSlotAddrLt =
          wCols.dictionary[1 + 2 * (ofOrderedReader ordRes).dict.size + row]'hIdxW := Option.some.inj hElem
      rw [hw]
      have hSA := hRep.slotAt_eq row
      unfold FlatPairDictionary.slotAt at hSA
      rw [dite_eq_left hSlotLen] at hSA
      change ((FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).get row hSlotLen).val = a at hSA
      unfold PairLookup.ColumnReduction.Slice.get at hSA
      have hBaseEq : (FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).base.val + row =
          1 + 2 * (ofOrderedReader ordRes).dict.size + row := by
        change FlatPairDictionary.slotBase (FlatPairDictionary.rowCount wCols.dictionary) + row = _
        rw [hRep.rows]
        unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase; omega
      have hElem2 : (wCols.dictionary[1 + 2 * (ofOrderedReader ordRes).dict.size + row]'hIdxW).val =
          ((FlatPairDictionary.slotSlice wCols.dictionary hRep.valid).get row hSlotLen).val := by
        unfold PairLookup.ColumnReduction.Slice.get
        simp only [hBaseEq]
      rw [hElem2]
      exact hSA
    let aW := I[(dictPtrW.val + 1 + nDictW.val + nDictW.val) + row]'hSlotAddrLt
    have haW? : I[(dictPtrW.val + 1 + nDictW.val + nDictW.val) + row]? = some aW :=
      getElem?_pos I _ hSlotAddrLt
    have h125r1 : (reg s125 1).val = dictPtrW.val + 1 + nDictW.val + nDictW.val := by
      have hr1_122 : reg s122 1 = dictPtrW := by
        rw [putReg_eq_other s121 (by decide : (1 : Fin 16) ≠ 8)]; exact putReg_eq_same s120 1 _
      have hr6_122 : reg s122 6 = oneW hTag := by
        rw [putReg_eq_other s121 (by decide : (6 : Fin 16) ≠ 8), putReg_eq_other s120 (by decide : (6 : Fin 16) ≠ 1),
          putReg_eq_other s119 (by decide : (6 : Fin 16) ≠ 15), putReg_eq_other s118 (by decide : (6 : Fin 16) ≠ 7)]; exact h118r6
      have hr8_122 : reg s122 8 = nDictW := putReg_eq_same s121 8 _
      have hr1_123 : (reg s123 1).val = dictPtrW.val + 1 := by
        dsimp only [s123]; rw [putReg_eq_same]
        change (add (reg s122 1) (reg s122 6)).val = _
        rw [hr1_122, hr6_122, add_no_wrap _ _ hBase1Lt]; rfl
      have hr8_123 : reg s123 8 = nDictW := by
        rw [putReg_eq_other s122 (by decide : (8 : Fin 16) ≠ 1)]; exact hr8_122
      have hr1_124 : (reg s124 1).val = dictPtrW.val + 1 + nDictW.val := by
        dsimp only [s124]; rw [putReg_eq_same]
        change (add (reg s123 1) (reg s123 8)).val = _
        rw [add_no_wrap _ _ (by rw [hr1_123, hr8_123]; exact hBase2Lt), hr1_123, hr8_123]
      have hr8_124 : reg s124 8 = nDictW := by
        rw [putReg_eq_other s123 (by decide : (8 : Fin 16) ≠ 1)]; exact hr8_123
      dsimp only [s125]; rw [putReg_eq_same]
      change (add (reg s124 1) (reg s124 8)).val = _
      rw [add_no_wrap _ _ (by rw [hr1_124, hr8_124]; exact hBase3Lt), hr1_124, hr8_124]
    have h125r3 : (reg s125 3).val = row := by
      rw [putReg_eq_other s124 (by decide : (3 : Fin 16) ≠ 1), putReg_eq_other s123 (by decide : (3 : Fin 16) ≠ 1),
        putReg_eq_other s122 (by decide : (3 : Fin 16) ≠ 1), putReg_eq_other s121 (by decide : (3 : Fin 16) ≠ 8),
        putReg_eq_other s120 (by decide : (3 : Fin 16) ≠ 1), putReg_eq_other s119 (by decide : (3 : Fin 16) ≠ 15),
        putReg_eq_other s118 (by decide : (3 : Fin 16) ≠ 7), h118r3]
      exact h114r3'
    have hs125 := step_add16 inp (s := s125)
      (by simp [s125, s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 11) rfl)
      (prog_pc_lt_const (by simp [s125, s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s126 := putReg rfl s125 15 (add (reg s125 1) (reg s125 3))
    have h126r15 : (reg s126 15).val = (dictPtrW.val + 1 + nDictW.val + nDictW.val) + row := by
      dsimp only [s126]; rw [putReg_eq_same]
      change (add (reg s125 1) (reg s125 3)).val = _
      rw [add_no_wrap _ _ (by rw [h125r1, h125r3]; exact hSlotAddrFit), h125r1, h125r3]
    have hs126 := step_loadInput16 inp (s := s126)
      (by simp [s126, s125, s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]; exact placedSlice_fetch hMid1Pl (k := 12) rfl)
      (by change I[(reg s126 15).val]? = _; rw [h126r15]; exact haW?)
      (prog_pc_lt_const (by simp [s126, s125, s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]; dsimp only [pc5a]; omega))
    let s127 := putReg rfl s126 2 aW
    have h127pc : s127.pc = pc5a + 127 := by
      simp [s127, s126, s125, s124, s123, s122, s121, s120, s119, putReg_pc, h118pc]
    have h127r2 : reg s127 2 = aW := putReg_eq_same s126 2 aW
    have h127r6 : reg s127 6 = oneW hTag := by
      rw [putReg_eq_other s126 (by decide : (6 : Fin 16) ≠ 2), putReg_eq_other s125 (by decide : (6 : Fin 16) ≠ 15),
        putReg_eq_other s124 (by decide : (6 : Fin 16) ≠ 1), putReg_eq_other s123 (by decide : (6 : Fin 16) ≠ 1),
        putReg_eq_other s122 (by decide : (6 : Fin 16) ≠ 1), putReg_eq_other s121 (by decide : (6 : Fin 16) ≠ 8),
        putReg_eq_other s120 (by decide : (6 : Fin 16) ≠ 1), putReg_eq_other s119 (by decide : (6 : Fin 16) ≠ 15),
        putReg_eq_other s118 (by decide : (6 : Fin 16) ≠ 7)]
      exact h118r6
    have h127r14 : reg s127 14 = descBaseW := by
      rw [putReg_eq_other s126 (by decide : (14 : Fin 16) ≠ 2), putReg_eq_other s125 (by decide : (14 : Fin 16) ≠ 15),
        putReg_eq_other s124 (by decide : (14 : Fin 16) ≠ 1), putReg_eq_other s123 (by decide : (14 : Fin 16) ≠ 1),
        putReg_eq_other s122 (by decide : (14 : Fin 16) ≠ 1), putReg_eq_other s121 (by decide : (14 : Fin 16) ≠ 8),
        putReg_eq_other s120 (by decide : (14 : Fin 16) ≠ 1), putReg_eq_other s119 (by decide : (14 : Fin 16) ≠ 15),
        putReg_eq_other s118 (by decide : (14 : Fin 16) ≠ 7)]
      exact h118r14
    have h127d : s127.data = s114.data := by
      simp [s127, s126, s125, s124, s123, s122, s121, s120, s119, putReg_data]
      rw [h118d]
      change s115.data = s114.data
      exact putReg_data _ _ _ _
    have hsMid : Steps prog inp 13 s114 s127 :=
      Steps.cons hs114 (Steps.cons hs115 (hs116_117.append (Steps.cons hs118 (Steps.cons hs119
        (Steps.cons hs120 (Steps.cons hs121 (Steps.cons hs122 (Steps.cons hs123 (Steps.cons hs124
        (Steps.cons hs125 (Steps.cons hs126 (Steps.zero s127))))))))))))
    refine ⟨?_, ?_⟩
    · intro ha0
      have hlt : (reg s127 2).val < (reg s127 6).val := by
        rw [h127r2, h127r6, hSlotEq, ha0]; exact (by decide : 0 < 1)
      have hs127 := step_branchLt16 inp (s := s127)
        (by rw [h127pc]; exact placedSlice_fetch hMid1Pl (k := 13) rfl)
        (by
          change (if (reg s127 2).val < (reg s127 6).val then okPC hI hTag else pc5a + 128) < _
          rw [ite_eq_left hlt]; exact okPC_lt hI hWork hTag)
      let t := { s127 with pc := if (reg s127 2).val < (reg s127 6).val then okPC hI hTag else pc5a + 128 }
      refine ⟨t, 14, by decide,
        hsMid.append (Steps.cons hs127 (Steps.zero t)), ?_⟩
      change (if (reg s127 2).val < (reg s127 6).val then _ else _) = _
      exact ite_eq_left hlt
    · intro haNe
      have hge : ¬ ((reg s127 2).val < (reg s127 6).val) := by
        rw [h127r2, h127r6, hSlotEq]; change ¬ (a < 1); omega
      have hs127 := step_branchLt16 inp (s := s127)
        (by rw [h127pc]; exact placedSlice_fetch hMid1Pl (k := 13) rfl)
        (by
          change (if (reg s127 2).val < (reg s127 6).val then okPC hI hTag else pc5a + 128) < _
          rw [ite_eq_right hge]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
      let s128 := { s127 with pc := if (reg s127 2).val < (reg s127 6).val then okPC hI hTag else pc5a + 128 }
      refine ⟨s128, aW, hsMid.append (Steps.cons hs127 (Steps.zero s128)), ?_, hSlotEq,
        h127r2, h127r6, h127r14, h127d⟩
      change (if (reg s127 2).val < (reg s127 6).val then _ else _) = _
      exact ite_eq_right hge
  -- Execute from pc5a + 128 onward (for a ≠ 0)
  have hAfterSlot : ∀ (row : Nat)
      (hrow : (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = some row)
      (haNe : ((ofOrderedReader ordRes).slots[row]?).getD 0 ≠ 0),
      let a := ((ofOrderedReader ordRes).slots[row]?).getD 0
      (checkedHit ordRes Pcan = none →
        ∃ t k2, k2 ≤ 47 ∧ Steps prog inp k2 s114 t ∧ t.pc = okPC hI hTag) ∧
      (checkedHit ordRes Pcan = some a →
        ∃ s167, Steps prog inp 47 s114 s167 ∧
          s167.pc = pc5a + 167 ∧
          s167.data.size = queryWorkCap ∧
          (∀ idx, idx < 14 → s167.data[idx]? = s114.data[idx]?) ∧
          s167.data[slDescBase]? = some descBaseW ∧
          s167.data[slSwapped]? = some swW ∧
          (s167.data[slHitNode]?).map Fin.val = some a ∧
          s167.data[slYLocal]? = some yW) := by
    intro row hrow haNe a
    obtain ⟨s128, aW, hp114_128, h128pc, haWVal, h128r2, h128r6, h128r14, h128d⟩ :=
      (hRowBranch row hrow).2 haNe
    obtain ⟨_, _, hHasBack⟩ := hLookupBack row hrow
    obtain ⟨q', hq'⟩ := hHasBack haNe
    have hBackQ' : wCols.back.read a = some (encodeBackPair (some q')) := (hBackRead a q').mpr hq'
    have haFstLt : a < wCols.back.tagAndFirst.size := by
      unfold BackWords.read at hBackQ'
      cases htf : wCols.back.tagAndFirst[a]? with
      | none => simp [htf] at hBackQ'
      | some _ =>
        by_cases h : a < wCols.back.tagAndFirst.size
        · exact h
        · rw [getElem?_neg wCols.back.tagAndFirst a h] at htf; cases htf
    have haSndLt : a < wCols.back.second.size := hBackSz ▸ haFstLt
    have hBackFstHdrLt : rec.descBase + descBackFst < I.size := by
      have := rec.descFits; change rec.descBase + 2 < I.size; omega
    let backFstPtrW := I[rec.descBase + descBackFst]'hBackFstHdrLt
    have hBackFstHdr? : I[rec.descBase + descBackFst]? = some backFstPtrW := getElem?_pos I _ hBackFstHdrLt
    have hBackFstPtrVal : backFstPtrW.val = rec.backFstPtr := by
      have hm := rec.hDescBackFst; rw [hBackFstHdr?, Option.map_some] at hm; exact Option.some.inj hm
    have hBackSndHdrLt : rec.descBase + descBackSnd < I.size := by
      have := rec.descFits; change rec.descBase + 3 < I.size; omega
    let backSndPtrW := I[rec.descBase + descBackSnd]'hBackSndHdrLt
    have hBackSndHdr? : I[rec.descBase + descBackSnd]? = some backSndPtrW := getElem?_pos I _ hBackSndHdrLt
    have hBackSndPtrVal : backSndPtrW.val = rec.backSndPtr := by
      have hm := rec.hDescBackSnd; rw [hBackSndHdr?, Option.map_some] at hm; exact Option.some.inj hm
    have haFstLtI : rec.backFstPtr + a < I.size := by have := hBackFst.1; omega
    have haSndLtI : rec.backSndPtr + a < I.size := by have := hBackSnd.1; omega
    let fstWord := I[rec.backFstPtr + a]'haFstLtI
    let sndWord := I[rec.backSndPtr + a]'haSndLtI
    have hFstWord? : I[rec.backFstPtr + a]? = some fstWord := getElem?_pos I _ haFstLtI
    have hSndWord? : I[rec.backSndPtr + a]? = some sndWord := getElem?_pos I _ haSndLtI
    have hFstEq : fstWord = wCols.back.tagAndFirst[a]'haFstLt := by
      have hs := hBackFst.2 a haFstLt
      rw [hFstWord?] at hs; exact Option.some.inj hs
    have hSndEq : sndWord = wCols.back.second[a]'haSndLt := by
      have hs := hBackSnd.2 a haSndLt
      rw [hSndWord?] at hs; exact Option.some.inj hs
    have hReadPair : wCols.back.read a = some (fstWord.val, sndWord.val) := by
      unfold BackWords.read
      rw [getElem?_pos wCols.back.tagAndFirst a haFstLt,
        getElem?_pos wCols.back.second a haSndLt, hFstEq, hSndEq]; rfl
    have hKey0Plus : k0W.val + 1 < 2 ^ bits := by
      have hlt : P.canonical.fst.val < P.canonical.snd.val := hCanOrd
      rw [hk0Val]; have := k1W.isLt; rw [hk1Val] at this; omega
    -- Write slHitNode, read backFst[a] into r3, k0W + 1 into r1
    obtain ⟨s130, hs128_129, h130pc, h130r, _, h130d⟩ := step_writeSlot inp slHitNode (by decide) 2 (by decide : (2 : Fin 16) ≠ 15)
      (by rw [h128pc]; exact placedSlice_fetch hMid1Pl (k := 14) rfl)
      (by rw [h128pc]; exact placedSlice_fetch hMid1Pl (k := 15) rfl)
      (prog_pc_lt_const (by rw [h128pc]; dsimp only [pc5a]; omega))
      (prog_pc_lt_const (by rw [h128pc]; dsimp only [pc5a]; omega))
    rw [h128pc] at h130pc
    have h130r2 : reg s130 2 = aW := (h130r 2 (by decide : (2 : Fin 16) ≠ 15)).trans h128r2
    have h130r6 : reg s130 6 = oneW hTag := (h130r 6 (by decide : (6 : Fin 16) ≠ 15)).trans h128r6
    have h130r14 : reg s130 14 = descBaseW := (h130r 14 (by decide : (14 : Fin 16) ≠ 15)).trans h128r14
    have hs130 := step_imm16 inp (s := s130)
      (by rw [h130pc]; exact placedSlice_fetch hMid1Pl (k := 16) rfl)
      (prog_pc_lt_const (by rw [h130pc]; dsimp only [pc5a]; omega))
    let s131 := putReg rfl s130 7 (descW hWork descBackFst (by decide))
    have hs131 := step_add16 inp (s := s131)
      (by simp [s131, putReg_pc, h130pc]; exact placedSlice_fetch hMid1Pl (k := 17) rfl)
      (prog_pc_lt_const (by simp [s131, putReg_pc, h130pc]; dsimp only [pc5a]; omega))
    let s132 := putReg rfl s131 15 (add (reg s131 14) (reg s131 7))
    have h132r15 : (reg s132 15).val = rec.descBase + descBackFst := by
      have h14 : reg s131 14 = descBaseW := by
        rw [putReg_eq_other s130 (by decide : (14 : Fin 16) ≠ 7)]; exact h130r14
      have h7 : reg s131 7 = descW hWork descBackFst (by decide) := putReg_eq_same s130 7 _
      dsimp only [s132]; rw [putReg_eq_same]
      change (add (reg s131 14) (reg s131 7)).val = _
      rw [h14, h7, add_no_wrap _ _ (by rw [hDescWVal]; change rec.descBase + 2 < 2 ^ bits; omega), hDescWVal]; rfl
    have hs132 := step_loadInput16 inp (s := s132)
      (by simp [s132, s131, putReg_pc, h130pc]; exact placedSlice_fetch hMid1Pl (k := 18) rfl)
      (by change I[(reg s132 15).val]? = _; rw [h132r15]; exact hBackFstHdr?)
      (prog_pc_lt_const (by simp [s132, s131, putReg_pc, h130pc]; dsimp only [pc5a]; omega))
    let s133 := putReg rfl s132 1 backFstPtrW
    have hs133 := step_add16 inp (s := s133)
      (by simp [s133, s132, s131, putReg_pc, h130pc]; exact placedSlice_fetch hMid1Pl (k := 19) rfl)
      (prog_pc_lt_const (by simp [s133, s132, s131, putReg_pc, h130pc]; dsimp only [pc5a]; omega))
    let s134 := putReg rfl s133 15 (add (reg s133 1) (reg s133 2))
    have h134r15 : (reg s134 15).val = rec.backFstPtr + a := by
      have h1 : reg s133 1 = backFstPtrW := putReg_eq_same s132 1 _
      have h2 : reg s133 2 = aW := by
        rw [putReg_eq_other s132 (by decide : (2 : Fin 16) ≠ 1), putReg_eq_other s131 (by decide : (2 : Fin 16) ≠ 15),
          putReg_eq_other s130 (by decide : (2 : Fin 16) ≠ 7)]
        exact h130r2
      dsimp only [s134]; rw [putReg_eq_same]
      change (add (reg s133 1) (reg s133 2)).val = _
      rw [h1, h2, add_no_wrap _ _ (by rw [hBackFstPtrVal, haWVal]; exact Nat.lt_of_lt_of_le haFstLtI hI),
        hBackFstPtrVal, haWVal]
    have hs134 := step_loadInput16 inp (s := s134)
      (by simp [s134, s133, s132, s131, putReg_pc, h130pc]; exact placedSlice_fetch hMid1Pl (k := 20) rfl)
      (by change I[(reg s134 15).val]? = _; rw [h134r15]; exact hFstWord?)
      (prog_pc_lt_const (by simp [s134, s133, s132, s131, putReg_pc, h130pc]; dsimp only [pc5a]; omega))
    let s135 := putReg rfl s134 3 fstWord
    have h130d' : s130.data = s114.data.set slHitNode aW (by rw [h114dsz]; decide) := by
      rw [h130d, h128r2]
      simp [h128d]
    have h135dK0 : s135.data[slKey0]? = some k0W := by
      simp [s135, s134, s133, s132, s131, putReg_data, h130d']
      rw [data_set_other _ _ _ _ (by decide)]
      exact h114K0
    obtain ⟨s137, hs135_136, h137pc, h137r, h137r1, _, h137d⟩ := step_readSlot (s := s135) inp slKey0 (by decide) 1 (by decide : (1 : Fin 16) ≠ 15) k0W
      h135dK0
      (by simp [s135, s134, s133, s132, s131, putReg_pc, h130pc]; exact placedSlice_fetch hMid1Pl (k := 21) rfl)
      (by simp [s135, s134, s133, s132, s131, putReg_pc, h130pc]; exact placedSlice_fetch hMid1Pl (k := 22) rfl)
      (prog_pc_lt_const (by simp [s135, s134, s133, s132, s131, putReg_pc, h130pc]; dsimp only [pc5a]; omega))
      (prog_pc_lt_const (by simp [s135, s134, s133, s132, s131, putReg_pc, h130pc]; dsimp only [pc5a]; omega))
    have h137pc' : s137.pc = pc5a + 137 := by
      simp [s135, s134, s133, s132, s131, putReg_pc, h130pc] at h137pc; exact h137pc
    have hs137 := step_add16 inp (s := s137)
      (by rw [h137pc']; exact placedSlice_fetch hMid1Pl (k := 23) rfl)
      (prog_pc_lt_const (by rw [h137pc']; dsimp only [pc5a]; omega))
    let s138 := putReg rfl s137 1 (add (reg s137 1) (reg s137 6))
    have h138pc : s138.pc = pc5a + 138 := by simp [s138, putReg_pc, h137pc']
    have h138r1 : (reg s138 1).val = k0W.val + 1 := by
      have h6 : reg s137 6 = oneW hTag := by
        rw [h137r 6 (by decide : (6 : Fin 16) ≠ 1) (by decide : (6 : Fin 16) ≠ 15),
          putReg_eq_other s134 (by decide : (6 : Fin 16) ≠ 3),
          putReg_eq_other s133 (by decide : (6 : Fin 16) ≠ 15),
          putReg_eq_other s132 (by decide : (6 : Fin 16) ≠ 1),
          putReg_eq_other s131 (by decide : (6 : Fin 16) ≠ 15),
          putReg_eq_other s130 (by decide : (6 : Fin 16) ≠ 7)]; exact h130r6
      dsimp only [s138]; rw [putReg_eq_same]
      change (add (reg s137 1) (reg s137 6)).val = _
      rw [h137r1, h6, add_no_wrap _ _ hKey0Plus]; rfl
    have h138r3 : reg s138 3 = fstWord := by
      rw [putReg_eq_other s137 (by decide : (3 : Fin 16) ≠ 1),
        h137r 3 (by decide : (3 : Fin 16) ≠ 1) (by decide : (3 : Fin 16) ≠ 15)]; exact putReg_eq_same s134 3 _
    obtain ⟨s145, hsGuard1, h145pc, h145r0, h145d⟩ :=
      lifted_pairGuard rfl (zeroW bits) (oneW hTag) rfl rfl hGuard1Pl
        (prog_pc_lt_const (by dsimp only [pc5a]; omega)) inp s138 h138pc
    have hs145 := step_imm16 inp (s := s145)
      (by rw [h145pc]; exact placedSlice_fetch hMid2Pl (k := 0) rfl)
      (prog_pc_lt_const (by rw [h145pc]; dsimp only [pc5a]; omega))
    let s146 := putReg rfl s145 6 (oneW hTag)
    have h146pc : s146.pc = pc5a + 146 := by simp [s146, putReg_pc, h145pc]
    have h146r0 : (reg s146 0).val = if fstWord.val = k0W.val + 1 then 0 else 1 := by
      rw [putReg_eq_other s145 (by decide : (0 : Fin 16) ≠ 6)]
      change (reg s145 (r16 rfl 0)).val = _
      rw [h145r0]
      change (if (reg s138 1).val = (reg s138 3).val then 0 else 1) = _
      rw [h138r1, h138r3]; simp [eq_comm]
    have h146d : s146.data = s114.data.set slHitNode aW (by rw [h114dsz]; decide) := by
      rw [putReg_data, h145d, putReg_data, h137d, putReg_data, putReg_data, putReg_data,
        putReg_data, putReg_data]
      exact h130d'
    have hp128_146 : Steps prog inp 15 s128 s146 := by
      have hs1 : Steps prog inp 7 s128 s135 :=
        hs128_129.append (Steps.cons hs130 (Steps.cons hs131 (Steps.cons hs132
          (Steps.cons hs133 (Steps.cons hs134 (Steps.zero s135))))))
      have hs2 : Steps prog inp 8 s135 s146 :=
        (hs135_136.append (Steps.cons hs137 (Steps.zero s138))).append
          (hsGuard1.append (Steps.cons hs145 (Steps.zero s146)))
      simpa only [Nat.add_assoc] using hs1.append hs2
    have hEncodeCan : encodeBackPair (some Pcan) = (k0W.val + 1, k1W.val) := by
      change (Pcan.fst.val + 1, Pcan.snd.val) = _; rw [hk0Val, hk1Val]
    -- Case split on fstWord.val = k0W.val + 1
    by_cases hEqFst : fstWord.val = k0W.val + 1
    · have hlt146 : (reg s146 0).val < (reg s146 6).val := by
        rw [h146r0, ite_eq_left hEqFst, putReg_eq_same]; exact (by decide : 0 < 1)
      have hs146 := step_branchLt16 inp (s := s146)
        (by rw [h146pc]; exact placedSlice_fetch hMid2Pl (k := 1) rfl)
        (by
          change (if (reg s146 0).val < (reg s146 6).val then pc5a + 147 else okPC hI hTag) < _
          rw [ite_eq_left hlt146]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
      let s147 := { s146 with pc := if (reg s146 0).val < (reg s146 6).val then pc5a + 147 else okPC hI hTag }
      have h147pc : s147.pc = pc5a + 147 := by
        change (if (reg s146 0).val < (reg s146 6).val then _ else _) = _; exact ite_eq_left hlt146
      have h147dDesc : s147.data[slDescBase]? = some descBaseW := by
        change s146.data[slDescBase]? = _
        rw [h146d, data_set_other _ _ _ _ (by decide)]; exact h114Desc
      have h147dHit : s147.data[slHitNode]? = some aW := by
        change s146.data[slHitNode]? = _; rw [h146d, data_set_same]
      have h147dK1 : s147.data[slKey1]? = some k1W := by
        change s146.data[slKey1]? = _
        rw [h146d, data_set_other _ _ _ _ (by decide)]; exact h114K1
      obtain ⟨s149, hs147_148, h149pc, _, h149r14, _, h149d⟩ := step_readSlot (s := s147) inp slDescBase (by decide) 14 (by decide : (14 : Fin 16) ≠ 15) descBaseW
        h147dDesc
        (by rw [h147pc]; exact placedSlice_fetch hMid2Pl (k := 2) rfl)
        (by rw [h147pc]; exact placedSlice_fetch hMid2Pl (k := 3) rfl)
        (prog_pc_lt_const (by rw [h147pc]; dsimp only [pc5a]; omega))
        (prog_pc_lt_const (by rw [h147pc]; dsimp only [pc5a]; omega))
      rw [h147pc] at h149pc
      obtain ⟨s151, hs149_150, h151pc, h151r, h151r2, _, h151d⟩ := step_readSlot (s := s149) inp slHitNode (by decide) 2 (by decide : (2 : Fin 16) ≠ 15) aW
        (by rw [h149d]; exact h147dHit)
        (by rw [h149pc]; exact placedSlice_fetch hMid2Pl (k := 4) rfl)
        (by rw [h149pc]; exact placedSlice_fetch hMid2Pl (k := 5) rfl)
        (prog_pc_lt_const (by rw [h149pc]; dsimp only [pc5a]; omega))
        (prog_pc_lt_const (by rw [h149pc]; dsimp only [pc5a]; omega))
      rw [h149pc] at h151pc
      have h151r14 : reg s151 14 = descBaseW := by
        rw [h151r 14 (by decide : (14 : Fin 16) ≠ 2) (by decide : (14 : Fin 16) ≠ 15)]; exact h149r14
      have hs151 := step_imm16 inp (s := s151)
        (by rw [h151pc]; exact placedSlice_fetch hMid2Pl (k := 6) rfl)
        (prog_pc_lt_const (by rw [h151pc]; dsimp only [pc5a]; omega))
      let s152 := putReg rfl s151 7 (descW hWork descBackSnd (by decide))
      have hs152 := step_add16 inp (s := s152)
        (by simp [s152, putReg_pc, h151pc]; exact placedSlice_fetch hMid2Pl (k := 7) rfl)
        (prog_pc_lt_const (by simp [s152, putReg_pc, h151pc]; dsimp only [pc5a]; omega))
      let s153 := putReg rfl s152 15 (add (reg s152 14) (reg s152 7))
      have h153r15 : (reg s153 15).val = rec.descBase + descBackSnd := by
        have h14 : reg s152 14 = descBaseW := by
          rw [putReg_eq_other s151 (by decide : (14 : Fin 16) ≠ 7)]; exact h151r14
        have h7 : reg s152 7 = descW hWork descBackSnd (by decide) := putReg_eq_same s151 7 _
        dsimp only [s153]; rw [putReg_eq_same]
        change (add (reg s152 14) (reg s152 7)).val = _
        rw [h14, h7, add_no_wrap _ _ (by rw [hDescWVal]; change rec.descBase + 3 < 2 ^ bits; omega), hDescWVal]; rfl
      have hs153 := step_loadInput16 inp (s := s153)
        (by simp [s153, s152, putReg_pc, h151pc]; exact placedSlice_fetch hMid2Pl (k := 8) rfl)
        (by change I[(reg s153 15).val]? = _; rw [h153r15]; exact hBackSndHdr?)
        (prog_pc_lt_const (by simp [s153, s152, putReg_pc, h151pc]; dsimp only [pc5a]; omega))
      let s154 := putReg rfl s153 1 backSndPtrW
      have hs154 := step_add16 inp (s := s154)
        (by simp [s154, s153, s152, putReg_pc, h151pc]; exact placedSlice_fetch hMid2Pl (k := 9) rfl)
        (prog_pc_lt_const (by simp [s154, s153, s152, putReg_pc, h151pc]; dsimp only [pc5a]; omega))
      let s155 := putReg rfl s154 15 (add (reg s154 1) (reg s154 2))
      have h155r15 : (reg s155 15).val = rec.backSndPtr + a := by
        have h1 : reg s154 1 = backSndPtrW := putReg_eq_same s153 1 _
        have h2 : reg s154 2 = aW := by
          rw [putReg_eq_other s153 (by decide : (2 : Fin 16) ≠ 1), putReg_eq_other s152 (by decide : (2 : Fin 16) ≠ 15),
            putReg_eq_other s151 (by decide : (2 : Fin 16) ≠ 7)]
          exact h151r2
        dsimp only [s155]; rw [putReg_eq_same]
        change (add (reg s154 1) (reg s154 2)).val = _
        rw [h1, h2, add_no_wrap _ _ (by rw [hBackSndPtrVal, haWVal]; exact Nat.lt_of_lt_of_le haSndLtI hI),
          hBackSndPtrVal, haWVal]
      have hs155 := step_loadInput16 inp (s := s155)
        (by simp [s155, s154, s153, s152, putReg_pc, h151pc]; exact placedSlice_fetch hMid2Pl (k := 10) rfl)
        (by change I[(reg s155 15).val]? = _; rw [h155r15]; exact hSndWord?)
        (prog_pc_lt_const (by simp [s155, s154, s153, s152, putReg_pc, h151pc]; dsimp only [pc5a]; omega))
      let s156 := putReg rfl s155 3 sndWord
      obtain ⟨s158, hs156_157, h158pc, h158r, h158r1, _, h158d⟩ := step_readSlot (s := s156) inp slKey1 (by decide) 1 (by decide : (1 : Fin 16) ≠ 15) k1W
        (by simp [s156, s155, s154, s153, s152, putReg_data, h151d, h149d]; exact h147dK1)
        (by simp [s156, s155, s154, s153, s152, putReg_pc, h151pc]; exact placedSlice_fetch hMid2Pl (k := 11) rfl)
        (by simp [s156, s155, s154, s153, s152, putReg_pc, h151pc]; exact placedSlice_fetch hMid2Pl (k := 12) rfl)
        (prog_pc_lt_const (by simp [s156, s155, s154, s153, s152, putReg_pc, h151pc]; dsimp only [pc5a]; omega))
        (prog_pc_lt_const (by simp [s156, s155, s154, s153, s152, putReg_pc, h151pc]; dsimp only [pc5a]; omega))
      have h158pc' : s158.pc = pc5a + 158 := by
        simp [s156, s155, s154, s153, s152, putReg_pc, h151pc] at h158pc; exact h158pc
      have h158r3 : reg s158 3 = sndWord := by
        rw [h158r 3 (by decide : (3 : Fin 16) ≠ 1) (by decide : (3 : Fin 16) ≠ 15)]; exact putReg_eq_same s155 3 _
      obtain ⟨s165, hsGuard2, h165pc, h165r0, h165d⟩ :=
        lifted_pairGuard rfl (zeroW bits) (oneW hTag) rfl rfl hGuard2Pl
          (prog_pc_lt_const (by dsimp only [pc5a]; omega)) inp s158 h158pc'
      have hs165 := step_imm16 inp (s := s165)
        (by rw [h165pc]; exact placedSlice_fetch hMid3Pl (k := 0) rfl)
        (prog_pc_lt_const (by rw [h165pc]; dsimp only [pc5a]; omega))
      let s166 := putReg rfl s165 6 (oneW hTag)
      have h166pc : s166.pc = pc5a + 166 := by simp [s166, putReg_pc, h165pc]
      have h166r0 : (reg s166 0).val = if sndWord.val = k1W.val then 0 else 1 := by
        rw [putReg_eq_other s165 (by decide : (0 : Fin 16) ≠ 6)]
        change (reg s165 (r16 rfl 0)).val = _
        rw [h165r0]
        change (if (reg s158 1).val = (reg s158 3).val then 0 else 1) = _
        rw [h158r1, h158r3]; simp [eq_comm]
      have h166d : s166.data = s146.data := by
        rw [putReg_data, h165d, h158d]; simp [s156, s155, s154, s153, s152, putReg_data, h151d, h149d]; rfl
      have hp146_166 : Steps prog inp 17 s146 s166 := by
        have hs1 : Steps prog inp 10 s146 s156 :=
          Steps.cons hs146 (hs147_148.append (hs149_150.append (Steps.cons hs151 (Steps.cons hs152
            (Steps.cons hs153 (Steps.cons hs154 (Steps.cons hs155 (Steps.zero s156))))))))
        have hs2 : Steps prog inp 7 s156 s166 :=
          hs156_157.append (hsGuard2.append (Steps.cons hs165 (Steps.zero s166)))
        simpa only [Nat.add_assoc] using hs1.append hs2
      refine ⟨?_, ?_⟩
      · intro hChNone
        have hNeSnd : sndWord.val ≠ k1W.val := by
          intro hEqSnd
          have hReadCan : wCols.back.read a = some (encodeBackPair (some Pcan)) := by
            rw [hReadPair, hEncodeCan, hEqFst, hEqSnd]
          have hBackCan : (ofOrderedReader ordRes).back[a]? = some (some Pcan) :=
            (hBackRead a Pcan).mp hReadCan
          have hSome : checkedHit ordRes Pcan = some a :=
            (checked_iff_back ordRes Pcan a).mpr hBackCan
          have : (none : Option Nat) = some a := hChNone.symm.trans hSome
          cases this
        have hge166 : ¬ ((reg s166 0).val < (reg s166 6).val) := by
          rw [h166r0, ite_eq_right hNeSnd, putReg_eq_same]; change ¬ (1 < 1); omega
        have hs166 := step_branchLt16 inp (s := s166)
          (by rw [h166pc]; exact placedSlice_fetch hMid3Pl (k := 1) rfl)
          (by
            change (if (reg s166 0).val < (reg s166 6).val then pc5a + 167 else okPC hI hTag) < _
            rw [ite_eq_right hge166]; exact okPC_lt hI hWork hTag)
        let t := { s166 with pc := if (reg s166 0).val < (reg s166 6).val then pc5a + 167 else okPC hI hTag }
        refine ⟨t, 47, by decide,
          ?_, ?_⟩
        · have hk := ((hp114_128.append hp128_146).append hp146_166).append (Steps.cons hs166 (Steps.zero t))
          simpa only [Nat.add_assoc] using hk
        · change (if (reg s166 0).val < (reg s166 6).val then _ else _) = _; exact ite_eq_right hge166
      · intro hChSome
        have hBackCan : (ofOrderedReader ordRes).back[a]? = some (some Pcan) :=
          (checked_iff_back ordRes Pcan a).mp hChSome
        have hReadCan : wCols.back.read a = some (encodeBackPair (some Pcan)) :=
          (hBackRead a Pcan).mpr hBackCan
        have hPairEq : (fstWord.val, sndWord.val) = (k0W.val + 1, k1W.val) :=
          Option.some.inj (hReadPair.symm.trans (hReadCan.trans (congrArg some hEncodeCan)))
        have hEqSnd : sndWord.val = k1W.val := congrArg Prod.snd hPairEq
        have hlt166 : (reg s166 0).val < (reg s166 6).val := by
          rw [h166r0, ite_eq_left hEqSnd, putReg_eq_same]; exact (by decide : 0 < 1)
        have hs166 := step_branchLt16 inp (s := s166)
          (by rw [h166pc]; exact placedSlice_fetch hMid3Pl (k := 1) rfl)
          (by
            change (if (reg s166 0).val < (reg s166 6).val then pc5a + 167 else okPC hI hTag) < _
            rw [ite_eq_left hlt166]; exact prog_pc_lt_const (by dsimp only [pc5a]; omega))
        let s167 := { s166 with pc := if (reg s166 0).val < (reg s166 6).val then pc5a + 167 else okPC hI hTag }
        have h167pc : s167.pc = pc5a + 167 := by
          change (if (reg s166 0).val < (reg s166 6).val then _ else _) = _; exact ite_eq_left hlt166
        have h167d : s167.data = s146.data := h166d
        refine ⟨s167, ?_, h167pc, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · have hk := ((hp114_128.append hp128_146).append hp146_166).append (Steps.cons hs166 (Steps.zero s167))
          simpa only [Nat.add_assoc] using hk
        · rw [h167d, h146d, Array.size_set, h114dsz]
        · intro idx hidx
          rw [h167d, h146d, data_set_other _ _ _ _ (by dsimp only [slHitNode]; omega)]
        · rw [h167d, h146d, data_set_other _ _ _ _ (by decide)]; exact h114Desc
        · rw [h167d, h146d, data_set_other _ _ _ _ (by decide)]; exact h114Sw
        · rw [h167d, h146d, data_set_same, Option.map_some]; exact congrArg some haWVal
        · rw [h167d, h146d, data_set_other _ _ _ _ (by decide)]; exact h114Y
    · have hge146 : ¬ ((reg s146 0).val < (reg s146 6).val) := by
        rw [h146r0, ite_eq_right hEqFst, putReg_eq_same]; change ¬ (1 < 1); omega
      have hs146 := step_branchLt16 inp (s := s146)
        (by rw [h146pc]; exact placedSlice_fetch hMid2Pl (k := 1) rfl)
        (by
          change (if (reg s146 0).val < (reg s146 6).val then pc5a + 147 else okPC hI hTag) < _
          rw [ite_eq_right hge146]; exact okPC_lt hI hWork hTag)
      let t := { s146 with pc := if (reg s146 0).val < (reg s146 6).val then pc5a + 147 else okPC hI hTag }
      refine ⟨?_, ?_⟩
      · intro _
        refine ⟨t, 30, by decide,
          ?_, ?_⟩
        · have hk := (hp114_128.append hp128_146).append (Steps.cons hs146 (Steps.zero t))
          simpa only [Nat.add_assoc] using hk
        · change (if (reg s146 0).val < (reg s146 6).val then _ else _) = _; exact ite_eq_right hge146
      · intro hChSome
        have hBackCan : (ofOrderedReader ordRes).back[a]? = some (some Pcan) :=
          (checked_iff_back ordRes Pcan a).mp hChSome
        have hReadCan : wCols.back.read a = some (encodeBackPair (some Pcan)) :=
          (hBackRead a Pcan).mpr hBackCan
        have hPairEq : (fstWord.val, sndWord.val) = (k0W.val + 1, k1W.val) :=
          Option.some.inj (hReadPair.symm.trans (hReadCan.trans (congrArg some hEncodeCan)))
        exact absurd (congrArg Prod.fst hPairEq) hEqFst
  refine ⟨?_, ?_⟩
  · intro hChNone
    cases hLk : (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 with
    | none => exact hDictMissPath hLk
    | some row =>
      by_cases ha0 : ((ofOrderedReader ordRes).slots[row]?).getD 0 = 0
      · exact (hRowBranch row hLk).1 ha0
      · exact (hAfterSlot row hLk ha0).1 hChNone
  · intro aNode hChSome
    obtain ⟨_, haNeNode, j, hj, hslot⟩ := hG.backward aNode Pcan ((checked_iff_back ordRes Pcan aNode).mp hChSome)
    have hj' : (PairLookup.lookup (ofOrderedReader ordRes).dict (orderedPairCode Pcan)).1 = some j := hj
    have haEq : ((ofOrderedReader ordRes).slots[j]?).getD 0 = aNode := hslot
    have haNe : ((ofOrderedReader ordRes).slots[j]?).getD 0 ≠ 0 := by rw [haEq]; exact haNeNode
    obtain ⟨s167, hp, hpc167, hdsz167, hfr167, hdb167, hsw167, hhit167, hy167⟩ :=
      (hAfterSlot j hj' haNe).2 (by rw [haEq]; exact hChSome)
    exact ⟨s167, 47, by decide, hp, hpc167, hdsz167, hfr167, hdb167, hsw167,
      by rw [hhit167, haEq], hy167⟩

private theorem exec_blkPairAndKnown_phase3
    {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (wCols : WordColumns bits)
    (descBase labelsPtr fEntryPtr fStopPtr aNode yVal : Nat)
    (hDescFits : descBase + 10 ≤ I.size)
    (hDescLabels : (I[descBase + descLabels]?).map Fin.val = some labelsPtr)
    (hDescFEntry : (I[descBase + descFEntry]?).map Fin.val = some fEntryPtr)
    (hDescFStop : (I[descBase + descFStop]?).map Fin.val = some fStopPtr)
    (hLabels : SliceAt I labelsPtr wCols.labels)
    (hFEntry : SliceAt I fEntryPtr wCols.entry)
    (hFStop : SliceAt I fStopPtr wCols.stop)
    (haE : aNode < wCols.entry.size) (haS : aNode < wCols.stop.size)
    (hyWL : yVal < wCols.labels.size) (hlE : wCols.labelAt yVal < wCols.entry.size)
    (s167 : State (codeLayout bits I.size hI hWork))
    (descBaseW yW : Word bits)
    (h167pc : s167.pc = pc5a + 167)
    (hDescWVal : descBaseW.val = descBase)
    (hyWv : yW.val = yVal)
    (h167Desc : s167.data[slDescBase]? = some descBaseW)
    (h167HitMap : (s167.data[slHitNode]?).map Fin.val = some aNode)
    (h167Y : s167.data[slYLocal]? = some yW) :
    let prog := oracleQueryProgram hI hWork hTag
    let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
    ∃ (sFin : State (codeLayout bits I.size hI hWork)) (k3 : Nat),
      k3 ≤ 35 ∧
      Steps prog inp k3 s167 sFin ∧
      sFin.pc = (if wCols.known aNode yVal then pc5b else okPC hI hTag) ∧
      sFin.data = s167.data := by
  intro prog inp
  have hOne : 1 < 2 ^ bits := Nat.lt_trans (by decide : 1 < 2) hTag
  have h5aPl := place_blk5a hI hWork hTag
  unfold blkPairAndKnown at h5aPl
  have hEqSz : (ThreeCalls.EqualityTail.checkedProgram hI hOne (ThreeCalls.concreteSetup bits hOne)).size = 77 :=
    ThreeCalls.EqualityTail.checkedProgram_size hI hOne (ThreeCalls.concreteSetup bits hOne)
  have hKnSz : (KnownNodeCheck.knownNodeProgram (bits := bits) hI).size = 14 := rfl
  have hMid3Pl := placedSlice_right_pc (n := pc5a + 165) (placedSlice_append_left (placedSlice_append_left h5aPl))
    (by simp [liftMap, PairGuard.rom, hEqSz, pc5a])
  have hKnownPl := placedSlice_right_pc (n := pc5a + 184) (placedSlice_append_left h5aPl)
    (by simp [liftMap, PairGuard.rom, hEqSz, pc5a])
  have hPostPl := placedSlice_right_pc (n := pc5a + 198) h5aPl
    (by simp [liftMap, PairGuard.rom, hEqSz, hKnSz, pc5a])
  let aNodeW : Word bits := ⟨aNode, by have := hFEntry.1; omega⟩
  have h167Hit : s167.data[slHitNode]? = some aNodeW := by
    cases hh : s167.data[slHitNode]? with
    | none => simp [hh] at h167HitMap
    | some w =>
      rw [hh, Option.map_some] at h167HitMap
      have hwEq : w = aNodeW := Fin.ext (Option.some.inj h167HitMap)
      exact congrArg some hwEq
  have hLabelsHdrLt : descBase + descLabels < I.size := by change descBase + 4 < I.size; omega
  have hFEntryHdrLt : descBase + descFEntry < I.size := by change descBase + 5 < I.size; omega
  have hFStopHdrLt : descBase + descFStop < I.size := by change descBase + 6 < I.size; omega
  let labelsPtrW := I[descBase + descLabels]'hLabelsHdrLt
  let fEntryPtrW := I[descBase + descFEntry]'hFEntryHdrLt
  let fStopPtrW := I[descBase + descFStop]'hFStopHdrLt
  have hLabelsHdr? : I[descBase + descLabels]? = some labelsPtrW := getElem?_pos I _ hLabelsHdrLt
  have hFEntryHdr? : I[descBase + descFEntry]? = some fEntryPtrW := getElem?_pos I _ hFEntryHdrLt
  have hFStopHdr? : I[descBase + descFStop]? = some fStopPtrW := getElem?_pos I _ hFStopHdrLt
  have hLabelsPtrVal : labelsPtrW.val = labelsPtr := by
    rw [hLabelsHdr?, Option.map_some] at hDescLabels; exact Option.some.inj hDescLabels
  have hFEntryPtrVal : fEntryPtrW.val = fEntryPtr := by
    rw [hFEntryHdr?, Option.map_some] at hDescFEntry; exact Option.some.inj hDescFEntry
  have hFStopPtrVal : fStopPtrW.val = fStopPtr := by
    rw [hFStopHdr?, Option.map_some] at hDescFStop; exact Option.some.inj hDescFStop
  obtain ⟨s169, hs167_168, h169pc, _, h169r14, _, h169d⟩ := step_readSlot (s := s167) inp slDescBase (by decide) 14 (by decide : (14 : Fin 16) ≠ 15) descBaseW
    h167Desc
    (by rw [h167pc]; exact placedSlice_fetch hMid3Pl (k := 2) rfl)
    (by rw [h167pc]; exact placedSlice_fetch hMid3Pl (k := 3) rfl)
    (prog_pc_lt_const (by rw [h167pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h167pc]; dsimp only [pc5a]; omega))
  rw [h167pc] at h169pc
  obtain ⟨s171, hs169_170, h171pc, h171r, h171r1, _, h171d⟩ := step_readSlot (s := s169) inp slHitNode (by decide) 1 (by decide : (1 : Fin 16) ≠ 15) aNodeW
    (by rw [h169d]; exact h167Hit)
    (by rw [h169pc]; exact placedSlice_fetch hMid3Pl (k := 4) rfl)
    (by rw [h169pc]; exact placedSlice_fetch hMid3Pl (k := 5) rfl)
    (prog_pc_lt_const (by rw [h169pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h169pc]; dsimp only [pc5a]; omega))
  rw [h169pc] at h171pc
  obtain ⟨s173, hs171_172, h173pc, h173r, h173r2, _, h173d⟩ := step_readSlot (s := s171) inp slYLocal (by decide) 2 (by decide : (2 : Fin 16) ≠ 15) yW
    (by rw [h171d, h169d]; exact h167Y)
    (by rw [h171pc]; exact placedSlice_fetch hMid3Pl (k := 6) rfl)
    (by rw [h171pc]; exact placedSlice_fetch hMid3Pl (k := 7) rfl)
    (prog_pc_lt_const (by rw [h171pc]; dsimp only [pc5a]; omega))
    (prog_pc_lt_const (by rw [h171pc]; dsimp only [pc5a]; omega))
  rw [h171pc] at h173pc
  have h173r1 : reg s173 1 = aNodeW := by
    rw [h173r 1 (by decide : (1 : Fin 16) ≠ 2) (by decide : (1 : Fin 16) ≠ 15)]; exact h171r1
  have h173r14 : reg s173 14 = descBaseW := by
    rw [h173r 14 (by decide : (14 : Fin 16) ≠ 2) (by decide : (14 : Fin 16) ≠ 15),
      h171r 14 (by decide : (14 : Fin 16) ≠ 1) (by decide : (14 : Fin 16) ≠ 15)]; exact h169r14
  have hs173 := step_imm16 inp (s := s173) (by rw [h173pc]; exact placedSlice_fetch hMid3Pl (k := 8) rfl)
    (prog_pc_lt_const (by rw [h173pc]; dsimp only [pc5a]; omega))
  let s174 := putReg rfl s173 7 (descW hWork descLabels (by decide))
  have hs174 := step_add16 inp (s := s174) (by simp [s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 9) rfl)
    (prog_pc_lt_const (by simp [s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s175 := putReg rfl s174 15 (add (reg s174 14) (reg s174 7))
  have h175r15 : (reg s175 15).val = descBase + descLabels := by
    have h14 : reg s174 14 = descBaseW := by
      rw [putReg_eq_other s173 (by decide : (14 : Fin 16) ≠ 7)]; exact h173r14
    have h7 : reg s174 7 = descW hWork descLabels (by decide) := putReg_eq_same s173 7 _
    dsimp only [s175]; rw [putReg_eq_same]
    change (add (reg s174 14) (reg s174 7)).val = _
    rw [h14, h7, add_no_wrap _ _ (by rw [hDescWVal]; change descBase + 4 < 2 ^ bits; omega), hDescWVal]; rfl
  have hs175 := step_loadInput16 inp (s := s175)
    (by simp [s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 10) rfl)
    (by change I[(reg s175 15).val]? = _; rw [h175r15]; exact hLabelsHdr?)
    (prog_pc_lt_const (by simp [s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s176 := putReg rfl s175 3 labelsPtrW
  have hs176 := step_imm16 inp (s := s176)
    (by simp [s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 11) rfl)
    (prog_pc_lt_const (by simp [s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s177 := putReg rfl s176 7 (descW hWork descFEntry (by decide))
  have hs177 := step_add16 inp (s := s177)
    (by simp [s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 12) rfl)
    (prog_pc_lt_const (by simp [s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s178 := putReg rfl s177 15 (add (reg s177 14) (reg s177 7))
  have h178r15 : (reg s178 15).val = descBase + descFEntry := by
    have h14 : reg s177 14 = descBaseW := by
      rw [putReg_eq_other s176 (by decide : (14 : Fin 16) ≠ 7), putReg_eq_other s175 (by decide : (14 : Fin 16) ≠ 3),
        putReg_eq_other s174 (by decide : (14 : Fin 16) ≠ 15), putReg_eq_other s173 (by decide : (14 : Fin 16) ≠ 7)]; exact h173r14
    have h7 : reg s177 7 = descW hWork descFEntry (by decide) := putReg_eq_same s176 7 _
    dsimp only [s178]; rw [putReg_eq_same]
    change (add (reg s177 14) (reg s177 7)).val = _
    rw [h14, h7, add_no_wrap _ _ (by rw [hDescWVal]; change descBase + 5 < 2 ^ bits; omega), hDescWVal]; rfl
  have hs178 := step_loadInput16 inp (s := s178)
    (by simp [s178, s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 13) rfl)
    (by change I[(reg s178 15).val]? = _; rw [h178r15]; exact hFEntryHdr?)
    (prog_pc_lt_const (by simp [s178, s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s179 := putReg rfl s178 4 fEntryPtrW
  have hs179 := step_imm16 inp (s := s179)
    (by simp [s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 14) rfl)
    (prog_pc_lt_const (by simp [s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s180 := putReg rfl s179 7 (descW hWork descFStop (by decide))
  have hs180 := step_add16 inp (s := s180)
    (by simp [s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 15) rfl)
    (prog_pc_lt_const (by simp [s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s181 := putReg rfl s180 15 (add (reg s180 14) (reg s180 7))
  have h181r15 : (reg s181 15).val = descBase + descFStop := by
    have h14 : reg s180 14 = descBaseW := by
      rw [putReg_eq_other s179 (by decide : (14 : Fin 16) ≠ 7), putReg_eq_other s178 (by decide : (14 : Fin 16) ≠ 4),
        putReg_eq_other s177 (by decide : (14 : Fin 16) ≠ 15), putReg_eq_other s176 (by decide : (14 : Fin 16) ≠ 7),
        putReg_eq_other s175 (by decide : (14 : Fin 16) ≠ 3), putReg_eq_other s174 (by decide : (14 : Fin 16) ≠ 15),
        putReg_eq_other s173 (by decide : (14 : Fin 16) ≠ 7)]; exact h173r14
    have h7 : reg s180 7 = descW hWork descFStop (by decide) := putReg_eq_same s179 7 _
    dsimp only [s181]; rw [putReg_eq_same]
    change (add (reg s180 14) (reg s180 7)).val = _
    rw [h14, h7, add_no_wrap _ _ (by rw [hDescWVal]; change descBase + 6 < 2 ^ bits; omega), hDescWVal]; rfl
  have hs181 := step_loadInput16 inp (s := s181)
    (by simp [s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 16) rfl)
    (by change I[(reg s181 15).val]? = _; rw [h181r15]; exact hFStopHdr?)
    (prog_pc_lt_const (by simp [s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s182 := putReg rfl s181 5 fStopPtrW
  have hs182 := step_imm16 inp (s := s182)
    (by simp [s182, s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 17) rfl)
    (prog_pc_lt_const (by simp [s182, s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s183 := putReg rfl s182 6 (zeroW bits)
  have hs183 := step_imm16 inp (s := s183)
    (by simp [s183, s182, s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; exact placedSlice_fetch hMid3Pl (k := 18) rfl)
    (prog_pc_lt_const (by simp [s183, s182, s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]; dsimp only [pc5a]; omega))
  let s184 := putReg rfl s183 7 (oneW hTag)
  have h184pc : s184.pc = pc5a + 184 := by
    simp [s184, s183, s182, s181, s180, s179, s178, s177, s176, s175, s174, putReg_pc, h173pc]
  have h184d : s184.data = s167.data := by
    simp [s184, s183, s182, s181, s180, s179, s178, s177, s176, s175, s174, putReg_data, h173d, h171d, h169d]
  have hp167_184 : Steps prog inp 17 s167 s184 :=
    hs167_168.append (hs169_170.append (hs171_172.append (Steps.cons hs173 (Steps.cons hs174
      (Steps.cons hs175 (Steps.cons hs176 (Steps.cons hs177 (Steps.cons hs178 (Steps.cons hs179
      (Steps.cons hs180 (Steps.cons hs181 (Steps.cons hs182 (Steps.cons hs183 (Steps.zero s184))))))))))))))
  have h184r1 : (reg s184 1).val = aNode := by
    rw [putReg_eq_other s183 (by decide : (1 : Fin 16) ≠ 7), putReg_eq_other s182 (by decide : (1 : Fin 16) ≠ 6),
      putReg_eq_other s181 (by decide : (1 : Fin 16) ≠ 5), putReg_eq_other s180 (by decide : (1 : Fin 16) ≠ 15),
      putReg_eq_other s179 (by decide : (1 : Fin 16) ≠ 7), putReg_eq_other s178 (by decide : (1 : Fin 16) ≠ 4),
      putReg_eq_other s177 (by decide : (1 : Fin 16) ≠ 15), putReg_eq_other s176 (by decide : (1 : Fin 16) ≠ 7),
      putReg_eq_other s175 (by decide : (1 : Fin 16) ≠ 3), putReg_eq_other s174 (by decide : (1 : Fin 16) ≠ 15),
      putReg_eq_other s173 (by decide : (1 : Fin 16) ≠ 7), h173r1]
  have h184r2 : (reg s184 2).val = yVal := by
    rw [putReg_eq_other s183 (by decide : (2 : Fin 16) ≠ 7), putReg_eq_other s182 (by decide : (2 : Fin 16) ≠ 6),
      putReg_eq_other s181 (by decide : (2 : Fin 16) ≠ 5), putReg_eq_other s180 (by decide : (2 : Fin 16) ≠ 15),
      putReg_eq_other s179 (by decide : (2 : Fin 16) ≠ 7), putReg_eq_other s178 (by decide : (2 : Fin 16) ≠ 4),
      putReg_eq_other s177 (by decide : (2 : Fin 16) ≠ 15), putReg_eq_other s176 (by decide : (2 : Fin 16) ≠ 7),
      putReg_eq_other s175 (by decide : (2 : Fin 16) ≠ 3), putReg_eq_other s174 (by decide : (2 : Fin 16) ≠ 15),
      putReg_eq_other s173 (by decide : (2 : Fin 16) ≠ 7), h173r2]
    exact hyWv
  have h184r3 : (reg s184 3).val = labelsPtr := by
    rw [putReg_eq_other s183 (by decide : (3 : Fin 16) ≠ 7), putReg_eq_other s182 (by decide : (3 : Fin 16) ≠ 6),
      putReg_eq_other s181 (by decide : (3 : Fin 16) ≠ 5), putReg_eq_other s180 (by decide : (3 : Fin 16) ≠ 15),
      putReg_eq_other s179 (by decide : (3 : Fin 16) ≠ 7), putReg_eq_other s178 (by decide : (3 : Fin 16) ≠ 4),
      putReg_eq_other s177 (by decide : (3 : Fin 16) ≠ 15), putReg_eq_other s176 (by decide : (3 : Fin 16) ≠ 7),
      putReg_eq_same s175 3 _]
    exact hLabelsPtrVal
  have h184r4 : (reg s184 4).val = fEntryPtr := by
    rw [putReg_eq_other s183 (by decide : (4 : Fin 16) ≠ 7), putReg_eq_other s182 (by decide : (4 : Fin 16) ≠ 6),
      putReg_eq_other s181 (by decide : (4 : Fin 16) ≠ 5), putReg_eq_other s180 (by decide : (4 : Fin 16) ≠ 15),
      putReg_eq_other s179 (by decide : (4 : Fin 16) ≠ 7), putReg_eq_same s178 4 _]
    exact hFEntryPtrVal
  have h184r5 : (reg s184 5).val = fStopPtr := by
    rw [putReg_eq_other s183 (by decide : (5 : Fin 16) ≠ 7), putReg_eq_other s182 (by decide : (5 : Fin 16) ≠ 6),
      putReg_eq_same s181 5 _]
    exact hFStopPtrVal
  have h184r6 : reg s184 6 = zeroW bits := by
    rw [putReg_eq_other s183 (by decide : (6 : Fin 16) ≠ 7)]; exact putReg_eq_same s182 6 _
  have h184r7 : reg s184 7 = oneW hTag := putReg_eq_same s183 7 _
  have hLFit : labelsPtr + wCols.labels.size ≤ I.size := hLabels.1
  have hEFit : fEntryPtr + wCols.entry.size ≤ I.size := hFEntry.1
  have hSFit : fStopPtr + wCols.stop.size ≤ I.size := hFStop.1
  obtain ⟨s198, kKnown, hkKnown, hsKnown, h198pc, h198r0eq, _, h198d⟩ :=
    lifted_knownCheck rfl hKnownPl (prog_pc_lt_const (by dsimp only [pc5a]; omega)) wCols inp s184 h184pc
      labelsPtr fEntryPtr fStopPtr aNode yVal (zeroW bits) (oneW hTag) rfl rfl
      haE haS hyWL hlE h184r1 h184r2 h184r3 h184r4 h184r5 h184r6 h184r7 hLFit hEFit hSFit
      hLabels.2 hFEntry.2 hFStop.2
  have hs198 := step_imm16 inp (s := s198)
    (by rw [h198pc]; exact placedSlice_fetch hPostPl (k := 0) rfl)
    (prog_pc_lt_const (by rw [h198pc]; dsimp only [pc5a]; omega))
  let s199 := putReg rfl s198 6 (oneW hTag)
  have h199pc : s199.pc = pc5a + 199 := by simp [s199, putReg_pc, h198pc]
  have h199r0 : reg s199 0 = if wCols.known aNode yVal then oneW hTag else zeroW bits := by
    rw [putReg_eq_other s198 (by decide : (0 : Fin 16) ≠ 6)]
    change reg s198 (r16 rfl 0) = _
    exact h198r0eq
  have hs199 := step_branchLt16 inp (s := s199)
    (by rw [h199pc]; exact placedSlice_fetch hPostPl (k := 1) rfl)
    (by
      change (if (reg s199 0).val < (reg s199 6).val then okPC hI hTag else pc5b) < _
      split
      · exact okPC_lt hI hWork hTag
      · exact prog_pc_lt_const (by dsimp only [pc5b]; omega))
  let sFin := { s199 with pc := if (reg s199 0).val < (reg s199 6).val then okPC hI hTag else pc5b }
  have hFinPC : sFin.pc = if wCols.known aNode yVal then pc5b else okPC hI hTag := by
    change (if (reg s199 0).val < (reg s199 6).val then okPC hI hTag else pc5b) = _
    rw [h199r0, putReg_eq_same]
    cases wCols.known aNode yVal
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hlt : (zeroW bits).val < (oneW hTag).val := by exact (by decide : 0 < 1)
      exact ite_eq_left hlt
    · simp only [↓reduceIte]
      have hge : ¬ ((oneW hTag).val < (oneW hTag).val) := Nat.lt_irrefl _
      exact ite_eq_right hge
  have hFinData : sFin.data = s167.data := by
    change s199.data = s167.data; rw [putReg_data, h198d, h184d]
  have hpAll : Steps prog inp (17 + kKnown + 2) s167 sFin := by
    have hk := (hp167_184.append hsKnown).append (Steps.cons hs198 (Steps.cons hs199 (Steps.zero sFin)))
    simpa only [Nat.add_assoc] using hk
  exact ⟨sFin, 17 + kKnown + 2, by omega, hpAll, hFinPC, hFinData⟩

private theorem exec_blkPairAndKnown
    {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {dDense : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr dDense)
    {large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK dDense)}
    {dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))}
    {sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense) → Nat}
    (ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large)
    (wCols : WordColumns bits)
    (hDictSlice : SliceAt I rec.dictPtr wCols.dictionary)
    (hRep : FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordRes))
    (hBackFst : SliceAt I rec.backFstPtr wCols.back.tagAndFirst)
    (hBackSnd : SliceAt I rec.backSndPtr wCols.back.second)
    (hLabels : SliceAt I rec.labelsPtr wCols.labels)
    (hFEntry : SliceAt I rec.fEntryPtr wCols.entry)
    (hFStop : SliceAt I rec.fStopPtr wCols.stop)
    (hLabelsSz : wCols.labels.size =
      (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount)
    (_hEntryStopSz : wCols.entry.size = wCols.stop.size)
    (hBackSz : wCols.back.tagAndFirst.size = wCols.back.second.size)
    (hKnownEq : ∀ a v, wCols.known a v = (ofOrderedReader ordRes).known a v)
    (hBackRead : ∀ j (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense)),
      wCols.back.read j = some (encodeBackPair (some P)) ↔
        (ofOrderedReader ordRes).back[j]? = some (some P))
    (hLabBounds : ∀ y : Fin (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount,
      wCols.labelAt y.val < wCols.entry.size)
    (hHitBounds : ∀ (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense)),
      P.fst < P.snd → ∀ aNode : Nat, checkedHit ordRes P = some aNode →
        aNode < wCols.entry.size ∧ aNode < wCols.stop.size)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (y : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc5a)
    (hDataSz : s.data.size = queryWorkCap)
    (hCD : (s.data[slD]?).map Fin.val = some dDense.val)
    (hCUL : (s.data[slULocal]?).map Fin.val = some P.fst.val)
    (hCVL : (s.data[slVLocal]?).map Fin.val = some P.snd.val)
    (hCYL : (s.data[slYLocal]?).map Fin.val = some y.val) :
    let prog := oracleQueryProgram hI hWork hTag
    let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
    let budget := 33 * (Nat.log2 ((ofOrderedReader ordRes).dict.size + 1) + 1) + 155
    (checkedHit ordRes P.canonical = none →
      ∃ t k, k ≤ budget ∧ Steps prog inp k s t ∧ t.pc = okPC hI hTag) ∧
    (∀ aNode : Nat, checkedHit ordRes P.canonical = some aNode →
      (ofOrderedReader ordRes).known aNode y.val = false →
      ∃ t k, k ≤ budget ∧ Steps prog inp k s t ∧ t.pc = okPC hI hTag) ∧
    (∀ aNode : Nat, checkedHit ordRes P.canonical = some aNode →
      (ofOrderedReader ordRes).known aNode y.val = true →
      ∃ t k, k ≤ budget ∧ Steps prog inp k s t ∧ t.pc = pc5b ∧
        t.data.size = queryWorkCap ∧
        (∀ idx, idx < 14 → t.data[idx]? = s.data[idx]?) ∧
        (t.data[slDescBase]?).map Fin.val = some rec.descBase ∧
        (t.data[slSwapped]?).map Fin.val = some (if P.fst < P.snd then 0 else 1) ∧
        (t.data[slHitNode]?).map Fin.val = some aNode) := by
  intro prog inp budget
  obtain ⟨s114, descBaseW, swW, k0W, k1W, yW, k1, hk1, hp0_114, h114pc, hDescWVal, hSwVal,
      hk0Val, hk1Val, hyWv, h114r0, h114r3, h114dsz, h114frame, h114Desc, h114Sw, h114K0, h114K1, h114Y⟩ :=
    exec_blkPairAndKnown_phase1 hI hWork hTag progress injRank q originalRows hRows rows childOK
      rec ordRes wCols hDictSlice hRep P y s hpc hDataSz hCD hCUL hCVL hCYL
  obtain ⟨hp2Miss, hp2Hit⟩ :=
    exec_blkPairAndKnown_phase2 hI hWork hTag progress injRank q originalRows hRows rows childOK
      rec ordRes wCols hDictSlice hRep hBackFst hBackSnd hBackSz hBackRead P s114
      descBaseW swW k0W k1W yW h114pc hDescWVal hk0Val hk1Val h114r0 h114r3
      h114dsz h114Desc h114Sw h114K0 h114K1 h114Y
  let Pcan := P.canonical
  have hCanOrd : Pcan.fst < Pcan.snd := by
    dsimp only [Pcan]
    by_cases hlt : P.fst < P.snd
    · simp [CutPair.canonical, hlt]
    · have hne : P.fst ≠ P.snd := P.ne
      have hgt : P.snd < P.fst := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (fun h => hne (Fin.ext h.symm))
      simp [CutPair.canonical, hlt, hgt]
  have hKnownPhase : ∀ aNode : Nat, checkedHit ordRes Pcan = some aNode →
      ∃ (sFin : State (codeLayout bits I.size hI hWork)) (kTot : Nat),
        kTot ≤ budget ∧
        Steps prog inp kTot s sFin ∧
        sFin.pc = (if (ofOrderedReader ordRes).known aNode y.val then pc5b else okPC hI hTag) ∧
        sFin.data.size = queryWorkCap ∧
        (∀ idx, idx < 14 → sFin.data[idx]? = s.data[idx]?) ∧
        (sFin.data[slDescBase]?).map Fin.val = some rec.descBase ∧
        (sFin.data[slSwapped]?).map Fin.val = some (if P.fst < P.snd then 0 else 1) ∧
        (sFin.data[slHitNode]?).map Fin.val = some aNode := by
    intro aNode hChSome
    obtain ⟨s167, k2, hk2, hp114_167, h167pc, h167dsz, h167frame, h167Desc, h167Sw, h167HitMap, h167Y⟩ :=
      hp2Hit aNode hChSome
    obtain ⟨haE, haS⟩ := hHitBounds Pcan hCanOrd aNode hChSome
    have hyWL : y.val < wCols.labels.size := by rw [hLabelsSz]; exact y.isLt
    have hlE : wCols.labelAt y.val < wCols.entry.size := hLabBounds ⟨y.val, y.isLt⟩
    obtain ⟨sFin, k3, hk3, hp167_fin, hFinPC, hFinData⟩ :=
      exec_blkPairAndKnown_phase3 hI hWork hTag wCols rec.descBase rec.labelsPtr rec.fEntryPtr rec.fStopPtr
        aNode y.val rec.descFits rec.hDescLabels rec.hDescFEntry rec.hDescFStop hLabels hFEntry hFStop
        haE haS hyWL hlE s167 descBaseW yW h167pc hDescWVal hyWv h167Desc h167HitMap h167Y
    refine ⟨sFin, k1 + k2 + k3, by dsimp only [budget]; omega,
      (hp0_114.append hp114_167).append hp167_fin, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hFinPC, hKnownEq]
    · rw [hFinData]; exact h167dsz
    · intro idx hidx; rw [hFinData]; exact (h167frame idx hidx).trans (h114frame idx hidx)
    · rw [hFinData, h167Desc, Option.map_some]; exact congrArg some hDescWVal
    · rw [hFinData, h167Sw, Option.map_some, hSwVal]
    · rw [hFinData]; exact h167HitMap
  refine ⟨?_, ?_, ?_⟩
  · intro hChNone
    obtain ⟨t, k2, hk2, hp2, hpc2⟩ := hp2Miss hChNone
    exact ⟨t, k1 + k2, by dsimp only [budget]; omega, hp0_114.append hp2, hpc2⟩
  · intro aNode hChSome hKnowF
    obtain ⟨sFin, kTot, hkTot, hp, hpcFin, _⟩ := hKnownPhase aNode hChSome
    rw [hKnowF] at hpcFin
    exact ⟨sFin, kTot, hkTot, hp, hpcFin⟩
  · intro aNode hChSome hKnowT
    obtain ⟨sFin, kTot, hkTot, hp, hpcFin, hdsz, hfr, hdb, hsw, hhit⟩ := hKnownPhase aNode hChSome
    rw [hKnowT] at hpcFin
    exact ⟨sFin, kTot, hkTot, hp, hpcFin, hdsz, hfr, hdb, hsw, hhit⟩

private def spanSurvives {n : Nat} (entry stop : Fin n → Nat)
    (a : Fin n) : EX44.Span n → Bool
  | none => false
  | some (lo, hi) =>
      !(entry a ≤ entry lo ∧ entry lo < stop a) ∨
      !(entry a ≤ entry hi ∧ entry hi < stop a)

private theorem exec_origAncestorStep {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (pc0 nextPC : Nat) (hNextLt : nextPC < (oracleQueryProgram hI hWork hTag).size)
    (hEndLt : pc0 + 26 ≤ okPC hI hTag + 3)
    (slCoord slDense : Nat) (hkCoord : slCoord < queryWorkCap) (hkDense : slDense < queryWorkCap)
    (hf0 : (oracleQueryProgram hI hWork hTag)[pc0]? = some (.imm 15 (hdrW hWork hdrOrigOfEntry (by decide))))
    (hf1 : (oracleQueryProgram hI hWork hTag)[pc0 + 1]? = some (.loadInput 14 15))
    (hf2 : (oracleQueryProgram hI hWork hTag)[pc0 + 2]? = some (.imm 15 (slotW hWork slCoord hkCoord)))
    (hf3 : (oracleQueryProgram hI hWork hTag)[pc0 + 3]? = some (.loadData 2 15))
    (hf4 : (oracleQueryProgram hI hWork hTag)[pc0 + 4]? = some (.add 15 14 2))
    (hf5 : (oracleQueryProgram hI hWork hTag)[pc0 + 5]? = some (.loadInput 2 15))
    (hf6 : (oracleQueryProgram hI hWork hTag)[pc0 + 6]? = some (.imm 15 (slotW hWork slDense hkDense)))
    (hf7 : (oracleQueryProgram hI hWork hTag)[pc0 + 7]? = some (.loadData 1 15))
    (hAnc : PlacedSlice
      (ancestorCheckBlock (L := codeLayout bits I.size hI hWork) rfl
        (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
        (zeroW bits) (oneW hTag) 1 2 (pc0 + 8) (pc0 + 24))
      (oracleQueryProgram hI hWork hTag) (pc0 + 8))
    (hf24 : (oracleQueryProgram hI hWork hTag)[pc0 + 24]? = some (.imm 6 (oneW hTag)))
    (hf25 : (oracleQueryProgram hI hWork hTag)[pc0 + 25]? = some (.branchLt 0 6 (okPC hI hTag) nextPC))
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc0)
    (coordW denseW origPtrW origElemW entryBaseW stopBaseW entryW entryX stopW : Word bits)
    (hCoord : s.data[slCoord]? = some coordW)
    (hDense : s.data[slDense]? = some denseW)
    (hOrigHdr : I[hdrOrigOfEntry]? = some origPtrW)
    (hOrigElem : I[origPtrW.val + coordW.val]? = some origElemW)
    (hEH : I[hdrEntry]? = some entryBaseW)
    (hSH : I[hdrStop]? = some stopBaseW)
    (hEW : I[entryBaseW.val + denseW.val]? = some entryW)
    (hEX : I[entryBaseW.val + origElemW.val]? = some entryX)
    (hSW : I[stopBaseW.val + denseW.val]? = some stopW) :
    ∃ t k, k ≤ 24 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
      t.pc = (if entryW.val ≤ entryX.val ∧ entryX.val < stopW.val then nextPC else okPC hI hTag) ∧
      t.data = s.data := by
  let prog := oracleQueryProgram hI hWork hTag
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have hOrigIdx : hdrOrigOfEntry < I.size := by
    by_cases h : hdrOrigOfEntry < I.size
    · exact h
    · rw [getElem?_neg I hdrOrigOfEntry h] at hOrigHdr; cases hOrigHdr
  have hOrigAddFit : origPtrW.val + coordW.val < 2 ^ bits := by
    by_cases h : origPtrW.val + coordW.val < I.size
    · exact Nat.lt_of_lt_of_le h hI
    · rw [getElem?_neg I _ h] at hOrigElem; cases hOrigElem
  have hs0 := step_imm16 inp (s := s) (by rw [hpc]; exact hf0) (prog_pc_lt _ (by rw [hpc]; omega))
  let s1 := putReg rfl s 15 (hdrW hWork hdrOrigOfEntry (by decide))
  have hs1 := step_loadInput16 inp (s := s1) (by simp [s1, putReg_pc, hpc]; exact hf1)
    (by change I[(reg s1 15).val]? = _; rw [putReg_eq_same]; exact hOrigHdr)
    (prog_pc_lt _ (by simp [s1, putReg_pc, hpc]; omega))
  let s2 := putReg rfl s1 14 origPtrW
  obtain ⟨s4, hs23, h4pc, h4r, h4r2, _, h4d⟩ := step_readSlot (s := s2) inp slCoord hkCoord 2
    (by decide : (2 : Fin 16) ≠ 15) coordW (by simp [s2, s1, putReg_data]; exact hCoord)
    (by simp [s2, s1, putReg_pc, hpc]; exact hf2)
    (by simp [s2, s1, putReg_pc, hpc]; exact hf3)
    (prog_pc_lt _ (by simp [s2, s1, putReg_pc, hpc]; omega))
    (prog_pc_lt _ (by simp [s2, s1, putReg_pc, hpc]; omega))
  have h4pc' : s4.pc = pc0 + 4 := by simp [s2, s1, putReg_pc, hpc] at h4pc; exact h4pc
  have h4r14 : reg s4 14 = origPtrW := by
    rw [h4r 14 (by decide : (14 : Fin 16) ≠ 2) (by decide : (14 : Fin 16) ≠ 15)]; exact putReg_eq_same s1 14 _
  have hs4 := step_add16 inp (s := s4) (by rw [h4pc']; exact hf4) (prog_pc_lt _ (by rw [h4pc']; omega))
  let s5 := putReg rfl s4 15 (add (reg s4 14) (reg s4 2))
  have h5r15 : (reg s5 15).val = origPtrW.val + coordW.val := by
    dsimp only [s5]; rw [putReg_eq_same]
    change (add (reg s4 14) (reg s4 2)).val = _
    rw [h4r14, h4r2, add_no_wrap _ _ hOrigAddFit]
  have hs5 := step_loadInput16 inp (s := s5) (by simp [s5, putReg_pc, h4pc']; exact hf5)
    (by change I[(reg s5 15).val]? = _; rw [h5r15]; exact hOrigElem)
    (prog_pc_lt _ (by simp [s5, putReg_pc, h4pc']; omega))
  let s6 := putReg rfl s5 2 origElemW
  obtain ⟨s8, hs67, h8pc, h8r, h8r1, _, h8d⟩ := step_readSlot (s := s6) inp slDense hkDense 1
    (by decide : (1 : Fin 16) ≠ 15) denseW
    (by simp [s6, s5, putReg_data, h4d, s2, s1]; exact hDense)
    (by simp [s6, s5, putReg_pc, h4pc']; exact hf6)
    (by simp [s6, s5, putReg_pc, h4pc']; exact hf7)
    (prog_pc_lt _ (by simp [s6, s5, putReg_pc, h4pc']; omega))
    (prog_pc_lt _ (by simp [s6, s5, putReg_pc, h4pc']; omega))
  have h8pc' : s8.pc = pc0 + 8 := by simp [s6, s5, putReg_pc, h4pc'] at h8pc; exact h8pc
  have h8r2 : reg s8 2 = origElemW := by
    rw [h8r 2 (by decide : (2 : Fin 16) ≠ 1) (by decide : (2 : Fin 16) ≠ 15)]; exact putReg_eq_same s5 2 _
  have h8d' : s8.data = s.data := by rw [h8d]; simp [s6, s5, putReg_data, h4d, s2, s1]
  obtain ⟨s24, k2, hk2, hs8_24, h24pc, h24r0, h24d⟩ := ancestorCheckBlock_spec (h16 := rfl)
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) rfl rfl 1 2 (by decide) (by decide) hAnc
    (prog_pc_lt _ (by omega)) inp s8 h8pc' hEH hSH
    (by rw [reg_r16, h8r1]; exact hEW) (by rw [reg_r16, h8r2]; exact hEX) (by rw [reg_r16, h8r1]; exact hSW)
  have hs24 := step_imm16 inp (s := s24) (by rw [h24pc]; exact hf24)
    (prog_pc_lt _ (by rw [h24pc]; omega))
  let s25 := putReg rfl s24 6 (oneW hTag)
  have h25pc : s25.pc = pc0 + 25 := by simp [s25, putReg_pc, h24pc]
  have h25r0 : (reg s25 0).val = if entryW.val ≤ entryX.val ∧ entryX.val < stopW.val then 1 else 0 := by
    rw [putReg_eq_other s24 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s24 0]; exact h24r0
  have h25r6 : reg s25 6 = oneW hTag := putReg_eq_same s24 6 _
  have hs25 := step_branchLt16 inp (s := s25) (by rw [h25pc]; exact hf25) (by
    rw [h25r0, h25r6, oneW]
    by_cases hc : entryW.val ≤ entryX.val ∧ entryX.val < stopW.val
    · simp [hc, hNextLt]
    · simp [hc, okPC_lt hI hWork hTag])
  let t := { s25 with pc := if (reg s25 0).val < (reg s25 6).val then okPC hI hTag else nextPC }
  have htpc : t.pc = if entryW.val ≤ entryX.val ∧ entryX.val < stopW.val then nextPC else okPC hI hTag := by
    change (if (reg s25 0).val < (reg s25 6).val then okPC hI hTag else nextPC) = _
    rw [h25r0, h25r6, oneW]
    by_cases hc : entryW.val ≤ entryX.val ∧ entryX.val < stopW.val <;> simp [hc]
  have htd : t.data = s.data := by
    change s25.data = s.data; rw [putReg_data, h24d, h8d']
  have hpAll : Steps prog inp (8 + k2 + 1) s s25 :=
    (((Steps.cons hs0 (Steps.cons hs1 hs23)).append (Steps.cons hs4 (Steps.cons hs5 hs67))).append hs8_24).append
      (Steps.cons hs24 (Steps.zero _))
  exact ⟨t, 8 + k2 + 2, by omega, hpAll.append (Steps.cons hs25 (Steps.zero t)), htpc, htd⟩

private theorem placedSlice_fetch_at {bits cap : Nat} {hCap : cap ≤ 2 ^ bits}
    {hWork : queryWorkCap ≤ 2 ^ bits}
    {block linked : Program (codeLayout bits cap hCap hWork)} {base k p : Nat}
    {op : Instr bits 16}
    (hpl : PlacedSlice block linked base) (hk : block[k]? = some op) (hp : p = base + k) :
    linked[p]? = some op :=
  hp ▸ placedSlice_fetch hpl hk

private theorem exec_blkExitTest_prepAndEval
    {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : DenseQuotientRows.Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {dDense : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr dDense)
    {large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK dDense)}
    {dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))}
    {sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense) → Nat}
    (_ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large)
    (wCols : WordColumns bits)
    {endpoints : Nat}
    {R : ExitMap.JumpMapRoute.StoredExit.Region bits I.size} {F : JumpForest}
    {ref : Nat → ExitMap.CheckedFold.Stored}
    {wFit : ExitMap.Retention.Width bits (max R.slots endpoints)}
    (ok : ExitMap.JumpMapRoute.StoredExit.Occupied I R F ref wFit)
    (prior : Array (Option ExitMap.Values))
    (hb : ExitMap.SealedPriorBase.BaseBound (max R.slots endpoints) prior)
    (B : ExitMap.SealedPriorBase.BaseView prior.size I.size)
    (hPlaced : ExitMap.SealedPriorBase.Placed wFit prior hb I B)
    (hLabels : SliceAt I rec.labelsPtr wCols.labels)
    (hLabelsSz : wCols.labels.size =
      (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount)
    (hLabF : ∀ y : Fin (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount,
      wCols.labelAt y.val < F.size)
    (hPriorSz : prior.size =
      (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount)
    (hRBase : R.base.val = rec.exitStoredPtr)
    (hBStart : B.start = rec.exitPriorPtr)
    (hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = rec.exitDepthPtr + x.val)
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (y : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (aNode : Nat) (haNode : aNode < F.size)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc5b)
    (hDataSz : s.data.size = queryWorkCap)
    (hDesc : (s.data[slDescBase]?).map Fin.val = some rec.descBase)
    (hSw : (s.data[slSwapped]?).map Fin.val = some (if P.fst < P.snd then 0 else 1))
    (hHit : (s.data[slHitNode]?).map Fin.val = some aNode)
    (hY : (s.data[slYLocal]?).map Fin.val = some y.val) :
    let prog := oracleQueryProgram hI hWork hTag
    let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
    let sz := exitEvalSize hI hTag
    let yIdx : Fin prior.size := ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩
    let res := ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
      yIdx (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)
    ∃ (s62 : State (codeLayout bits I.size hI hWork)) (k1 : Nat) (w0 w1 w2 w3 w4 w5 : Word bits),
      k1 ≤ 96 * (ExitMap.JumpMapRoute.StoredExit.foldStored I R wFit.tags
        (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).steps + 90 ∧
      Steps prog inp k1 s s62 ∧
      s62.pc = pc5b + 62 + sz ∧
      s62.data.size = queryWorkCap ∧
      (∀ idx, idx < 14 → s62.data[idx]? = s.data[idx]?) ∧
      ExitEval.IntervalWords hTag (if P.fst < P.snd then res.x0 else res.x1) w0 w1 w2 ∧
      ExitEval.IntervalWords hTag (if P.fst < P.snd then res.x1 else res.x0) w3 w4 w5 ∧
      s62.data[slX0Tag]? = some w0 ∧ s62.data[slX0Lo]? = some w1 ∧ s62.data[slX0Hi]? = some w2 ∧
      s62.data[slX1Tag]? = some w3 ∧ s62.data[slX1Lo]? = some w4 ∧ s62.data[slX1Hi]? = some w5 := by
  intro prog inp sz yIdx res
  have h5bPl := place_blk5b hI hWork hTag
  unfold blkExitTest at h5bPl
  have hEvalSz : (liftMap (ρ16 (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      (rfl : (ExitEval.exitEvalLayout bits I.size hI).registerCount = 16))
      (pc5b + 22) (pc5b + 22 + sz) (ExitEval.exitEvalProgram (fits := hI) hTag)).size = sz := by
    simp [liftMap, sz, exitEvalSize]
  have hPre22Pl := placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left h5bPl)))))))))
  have hEvalPl := placedSlice_right_pc (n := pc5b + 22) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h5bPl))))))))) (by simp)
  have hBig52Pl := placedSlice_right_pc (n := pc5b + 22 + sz) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left h5bPl))))))))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz]; omega)
  -- Unpack scratch & descriptor pointers
  obtain ⟨descBaseW, hDescW, hDescVal⟩ : ∃ w, s.data[slDescBase]? = some w ∧ w.val = rec.descBase := by
    cases hw : s.data[slDescBase]? with
    | none => simp [hw] at hDesc
    | some w => exact ⟨w, rfl, by simpa [hw] using hDesc⟩
  obtain ⟨swW, hSwW, hSwVal⟩ : ∃ w, s.data[slSwapped]? = some w ∧ w.val = if P.fst < P.snd then 0 else 1 := by
    cases hw : s.data[slSwapped]? with
    | none => simp [hw] at hSw
    | some w => exact ⟨w, rfl, by simpa [hw] using hSw⟩
  obtain ⟨aNodeW, hHitW, hHitVal⟩ : ∃ w, s.data[slHitNode]? = some w ∧ w.val = aNode := by
    cases hw : s.data[slHitNode]? with
    | none => simp [hw] at hHit
    | some w => exact ⟨w, rfl, by simpa [hw] using hHit⟩
  obtain ⟨yW, hYW, hYVal⟩ : ∃ w, s.data[slYLocal]? = some w ∧ w.val = y.val := by
    cases hw : s.data[slYLocal]? with
    | none => simp [hw] at hY
    | some w => exact ⟨w, rfl, by simpa [hw] using hY⟩
  have hDF : rec.descBase + 10 ≤ I.size := rec.descFits
  have hLabHdrLt : rec.descBase + descLabels < I.size := by change rec.descBase + 4 < I.size; omega
  have hDepHdrLt : rec.descBase + descExitDepth < I.size := by change rec.descBase + 7 < I.size; omega
  have hStoHdrLt : rec.descBase + descExitStored < I.size := by change rec.descBase + 8 < I.size; omega
  have hPriHdrLt : rec.descBase + descExitPrior < I.size := by change rec.descBase + 9 < I.size; omega
  let labelsPtrW := I[rec.descBase + descLabels]'hLabHdrLt
  let exitDepPtrW := I[rec.descBase + descExitDepth]'hDepHdrLt
  let exitStoPtrW := I[rec.descBase + descExitStored]'hStoHdrLt
  let exitPriPtrW := I[rec.descBase + descExitPrior]'hPriHdrLt
  have hLabHdr? : I[rec.descBase + descLabels]? = some labelsPtrW := getElem?_pos I _ hLabHdrLt
  have hDepHdr? : I[rec.descBase + descExitDepth]? = some exitDepPtrW := getElem?_pos I _ hDepHdrLt
  have hStoHdr? : I[rec.descBase + descExitStored]? = some exitStoPtrW := getElem?_pos I _ hStoHdrLt
  have hPriHdr? : I[rec.descBase + descExitPrior]? = some exitPriPtrW := getElem?_pos I _ hPriHdrLt
  have hLabPtrVal : labelsPtrW.val = rec.labelsPtr := by
    have hm := rec.hDescLabels; rw [hLabHdr?, Option.map_some] at hm; exact Option.some.inj hm
  have hDepPtrVal : exitDepPtrW.val = rec.exitDepthPtr := by
    have hm := rec.hDescExitDepth; rw [hDepHdr?, Option.map_some] at hm; exact Option.some.inj hm
  have hStoPtrVal : exitStoPtrW.val = rec.exitStoredPtr := by
    have hm := rec.hDescExitStored; rw [hStoHdr?, Option.map_some] at hm; exact Option.some.inj hm
  have hPriPtrVal : exitPriPtrW.val = rec.exitPriorPtr := by
    have hm := rec.hDescExitPrior; rw [hPriHdr?, Option.map_some] at hm; exact Option.some.inj hm
  have hyWL : y.val < wCols.labels.size := by rw [hLabelsSz]; exact y.isLt
  have hLabILt : rec.labelsPtr + y.val < I.size := by have := hLabels.1; omega
  let labW := I[rec.labelsPtr + y.val]'hLabILt
  have hLab? : I[rec.labelsPtr + y.val]? = some labW := getElem?_pos I _ hLabILt
  have hLabVal : labW.val = wCols.labelAt y.val := by
    have hs := hLabels.2 y.val hyWL
    rw [hLab?] at hs
    unfold WordColumns.labelAt
    rw [getElem?_pos wCols.labels y.val hyWL, Option.map_some, Option.getD_some]
    exact congrArg Fin.val (Option.some.inj hs)
  have haSlots : aNode < R.slots := ok.size_eq ▸ haNode
  have hDepthAddr : (R.depthAddr ⟨aNode, haSlots⟩).val = rec.exitDepthPtr + aNode :=
    hDepthContig ⟨aNode, haSlots⟩
  have hDepILt : rec.exitDepthPtr + aNode < I.size := by
    rw [← hDepthAddr]; exact R.depthMem ⟨aNode, haSlots⟩
  let depW := I[rec.exitDepthPtr + aNode]'hDepILt
  have hDep? : I[rec.exitDepthPtr + aNode]? = some depW := getElem?_pos I _ hDepILt
  have hDepVal : depW.val = ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode := by
    unfold ExitMap.JumpMapRoute.StoredExit.depthAt
    rw [dite_eq_left haSlots]
    have hEq : (R.depthAddr ⟨aNode, haSlots⟩).val = rec.exitDepthPtr + aNode := hDepthAddr
    simp only [hEq, depW]
  -- Steps 0..21: load r6, r7, r8, r9, r10, r11
  obtain ⟨s2, hs01, h2pc, _, h2r14, _, h2d⟩ := step_readSlot (s := s) inp slDescBase (by decide) 14
    (by decide : (14 : Fin 16) ≠ 15) descBaseW hDescW
    (by rw [hpc]; exact placedSlice_fetch hPre22Pl (k := 0) rfl)
    (by rw [hpc]; exact placedSlice_fetch hPre22Pl (k := 1) rfl)
    (prog_pc_lt _ (by rw [hpc]; unfold okPC pc6; dsimp only [pc5b]; omega))
    (prog_pc_lt _ (by rw [hpc]; unfold okPC pc6; dsimp only [pc5b]; omega))
  rw [hpc] at h2pc
  have hs2 := step_imm16 inp (s := s2) (by rw [h2pc]; exact placedSlice_fetch hPre22Pl (k := 2) rfl)
    (prog_pc_lt _ (by rw [h2pc]; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s3 := putReg rfl s2 7 (descW hWork descLabels (by decide))
  have hs3 := step_add16 inp (s := s3) (by simp [s3, putReg_pc, h2pc]; exact placedSlice_fetch hPre22Pl (k := 3) rfl)
    (prog_pc_lt _ (by simp [s3, putReg_pc, h2pc]; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s4 := putReg rfl s3 15 (add (reg s3 14) (reg s3 7))
  have h4r15 : (reg s4 15).val = rec.descBase + descLabels := by
    have h14 : reg s3 14 = descBaseW := by rw [putReg_eq_other s2 (by decide : (14 : Fin 16) ≠ 7)]; exact h2r14
    have h7 : reg s3 7 = descW hWork descLabels (by decide) := putReg_eq_same s2 7 _
    dsimp only [s4]; rw [putReg_eq_same]
    change (add (reg s3 14) (reg s3 7)).val = _
    rw [h14, h7, add_no_wrap _ _ (by rw [hDescVal]; change rec.descBase + 4 < 2 ^ bits; exact Nat.lt_of_lt_of_le (by omega) hI), hDescVal]; rfl
  have hs4 := step_loadInput16 inp (s := s4) (by simp [s4, s3, putReg_pc, h2pc]; exact placedSlice_fetch hPre22Pl (k := 4) rfl)
    (by change I[(reg s4 15).val]? = _; rw [h4r15]; exact hLabHdr?)
    (prog_pc_lt _ (by simp [s4, s3, putReg_pc, h2pc]; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s5 := putReg rfl s4 3 labelsPtrW
  obtain ⟨s7, hs56, h7pc, h7r, h7r8, _, h7d⟩ := step_readSlot (s := s5) inp slYLocal (by decide) 8
    (by decide : (8 : Fin 16) ≠ 15) yW (by simp [s5, s4, s3, putReg_data, h2d]; exact hYW)
    (by simp [s5, s4, s3, putReg_pc, h2pc]; exact placedSlice_fetch hPre22Pl (k := 5) rfl)
    (by simp [s5, s4, s3, putReg_pc, h2pc]; exact placedSlice_fetch hPre22Pl (k := 6) rfl)
    (prog_pc_lt _ (by simp [s5, s4, s3, putReg_pc, h2pc]; unfold okPC pc6; dsimp only [pc5b]; omega))
    (prog_pc_lt _ (by simp [s5, s4, s3, putReg_pc, h2pc]; unfold okPC pc6; dsimp only [pc5b]; omega))
  have h7pc' : s7.pc = pc5b + 7 := by simp [s5, s4, s3, putReg_pc, h2pc] at h7pc; exact h7pc
  have h7r3 : reg s7 3 = labelsPtrW := by
    rw [h7r 3 (by decide : (3 : Fin 16) ≠ 8) (by decide : (3 : Fin 16) ≠ 15)]; exact putReg_eq_same s4 3 _
  have h7r14 : reg s7 14 = descBaseW := by
    rw [h7r 14 (by decide : (14 : Fin 16) ≠ 8) (by decide : (14 : Fin 16) ≠ 15),
      putReg_eq_other s4 (by decide : (14 : Fin 16) ≠ 3),
      putReg_eq_other s3 (by decide : (14 : Fin 16) ≠ 15),
      putReg_eq_other s2 (by decide : (14 : Fin 16) ≠ 7)]
    exact h2r14
  have hs7 := step_add16 inp (s := s7) (by rw [h7pc']; exact placedSlice_fetch hPre22Pl (k := 7) rfl)
    (prog_pc_lt _ (by rw [h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s8 := putReg rfl s7 15 (add (reg s7 3) (reg s7 8))
  have h8r15 : (reg s8 15).val = rec.labelsPtr + y.val := by
    dsimp only [s8]; rw [putReg_eq_same]
    change (add (reg s7 3) (reg s7 8)).val = _
    rw [h7r3, h7r8, add_no_wrap _ _ (by rw [hLabPtrVal, hYVal]; exact Nat.lt_of_lt_of_le hLabILt hI), hLabPtrVal, hYVal]
  have hs8 := step_loadInput16 inp (s := s8) (by simp [s8, putReg_pc, h7pc']; exact placedSlice_fetch hPre22Pl (k := 8) rfl)
    (by change I[(reg s8 15).val]? = _; rw [h8r15]; exact hLab?)
    (prog_pc_lt _ (by simp [s8, putReg_pc, h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s9 := putReg rfl s8 6 labW
  have hs9 := step_imm16 inp (s := s9) (by simp [s9, s8, putReg_pc, h7pc']; exact placedSlice_fetch hPre22Pl (k := 9) rfl)
    (prog_pc_lt _ (by simp [s9, s8, putReg_pc, h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s10 := putReg rfl s9 7 (descW hWork descExitDepth (by decide))
  have hs10 := step_add16 inp (s := s10) (by simp [s10, s9, s8, putReg_pc, h7pc']; exact placedSlice_fetch hPre22Pl (k := 10) rfl)
    (prog_pc_lt _ (by simp [s10, s9, s8, putReg_pc, h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s11 := putReg rfl s10 15 (add (reg s10 14) (reg s10 7))
  have h11r14 : reg s10 14 = descBaseW := by
    rw [putReg_eq_other s9 (by decide : (14 : Fin 16) ≠ 7), putReg_eq_other s8 (by decide : (14 : Fin 16) ≠ 6),
      putReg_eq_other s7 (by decide : (14 : Fin 16) ≠ 15)]
    exact h7r14
  have h11r15 : (reg s11 15).val = rec.descBase + descExitDepth := by
    have h7 : reg s10 7 = descW hWork descExitDepth (by decide) := putReg_eq_same s9 7 _
    dsimp only [s11]; rw [putReg_eq_same]
    change (add (reg s10 14) (reg s10 7)).val = _
    rw [h11r14, h7, add_no_wrap _ _ (by rw [hDescVal]; change rec.descBase + 7 < 2 ^ bits; exact Nat.lt_of_lt_of_le (by omega) hI), hDescVal]; rfl
  have hs11 := step_loadInput16 inp (s := s11) (by simp [s11, s10, s9, s8, putReg_pc, h7pc']; exact placedSlice_fetch hPre22Pl (k := 11) rfl)
    (by change I[(reg s11 15).val]? = _; rw [h11r15]; exact hDepHdr?)
    (prog_pc_lt _ (by simp [s11, s10, s9, s8, putReg_pc, h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s12 := putReg rfl s11 9 exitDepPtrW
  obtain ⟨s14, hs1213, h14pc, h14r, h14r12, _, h14d⟩ := step_readSlot (s := s12) inp slHitNode (by decide) 12
    (by decide : (12 : Fin 16) ≠ 15) aNodeW
    (by simp [s12, s11, s10, s9, s8, putReg_data, h7d, s5, s4, s3, h2d]; exact hHitW)
    (by simp [s12, s11, s10, s9, s8, putReg_pc, h7pc']; exact placedSlice_fetch hPre22Pl (k := 12) rfl)
    (by simp [s12, s11, s10, s9, s8, putReg_pc, h7pc']; exact placedSlice_fetch hPre22Pl (k := 13) rfl)
    (prog_pc_lt _ (by simp [s12, s11, s10, s9, s8, putReg_pc, h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
    (prog_pc_lt _ (by simp [s12, s11, s10, s9, s8, putReg_pc, h7pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  have h14pc' : s14.pc = pc5b + 14 := by simp [s12, s11, s10, s9, s8, putReg_pc, h7pc'] at h14pc; exact h14pc
  have h14r6 : reg s14 6 = labW := by
    rw [h14r 6 (by decide : (6 : Fin 16) ≠ 12) (by decide : (6 : Fin 16) ≠ 15),
      putReg_eq_other s11 (by decide : (6 : Fin 16) ≠ 9),
      putReg_eq_other s10 (by decide : (6 : Fin 16) ≠ 15),
      putReg_eq_other s9 (by decide : (6 : Fin 16) ≠ 7),
      putReg_eq_same s8 6 _]
  have h14r8 : reg s14 8 = yW := by
    rw [h14r 8 (by decide : (8 : Fin 16) ≠ 12) (by decide : (8 : Fin 16) ≠ 15),
      putReg_eq_other s11 (by decide : (8 : Fin 16) ≠ 9),
      putReg_eq_other s10 (by decide : (8 : Fin 16) ≠ 15),
      putReg_eq_other s9 (by decide : (8 : Fin 16) ≠ 7),
      putReg_eq_other s8 (by decide : (8 : Fin 16) ≠ 6),
      putReg_eq_other s7 (by decide : (8 : Fin 16) ≠ 15)]
    exact h7r8
  have h14r9 : reg s14 9 = exitDepPtrW := by
    rw [h14r 9 (by decide : (9 : Fin 16) ≠ 12) (by decide : (9 : Fin 16) ≠ 15)]; exact putReg_eq_same s11 9 _
  have h14r14 : reg s14 14 = descBaseW := by
    rw [h14r 14 (by decide : (14 : Fin 16) ≠ 12) (by decide : (14 : Fin 16) ≠ 15),
      putReg_eq_other s11 (by decide : (14 : Fin 16) ≠ 9),
      putReg_eq_other s10 (by decide : (14 : Fin 16) ≠ 15)]
    exact h11r14
  have hs14 := step_add16 inp (s := s14) (by rw [h14pc']; exact placedSlice_fetch hPre22Pl (k := 14) rfl)
    (prog_pc_lt _ (by rw [h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s15 := putReg rfl s14 15 (add (reg s14 9) (reg s14 12))
  have h15r15 : (reg s15 15).val = rec.exitDepthPtr + aNode := by
    dsimp only [s15]; rw [putReg_eq_same]
    change (add (reg s14 9) (reg s14 12)).val = _
    rw [h14r9, h14r12, add_no_wrap _ _ (by rw [hDepPtrVal, hHitVal]; exact Nat.lt_of_lt_of_le hDepILt hI), hDepPtrVal, hHitVal]
  have hs15 := step_loadInput16 inp (s := s15) (by simp [s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 15) rfl)
    (by change I[(reg s15 15).val]? = _; rw [h15r15]; exact hDep?)
    (prog_pc_lt _ (by simp [s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s16 := putReg rfl s15 7 depW
  have hs16 := step_imm16 inp (s := s16) (by simp [s16, s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 16) rfl)
    (prog_pc_lt _ (by simp [s16, s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s17 := putReg rfl s16 12 (descW hWork descExitStored (by decide))
  have hs17 := step_add16 inp (s := s17) (by simp [s17, s16, s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 17) rfl)
    (prog_pc_lt _ (by simp [s17, s16, s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s18 := putReg rfl s17 15 (add (reg s17 14) (reg s17 12))
  have h18r14 : reg s17 14 = descBaseW := by
    rw [putReg_eq_other s16 (by decide : (14 : Fin 16) ≠ 12), putReg_eq_other s15 (by decide : (14 : Fin 16) ≠ 7),
      putReg_eq_other s14 (by decide : (14 : Fin 16) ≠ 15)]
    exact h14r14
  have h18r15 : (reg s18 15).val = rec.descBase + descExitStored := by
    have h12 : reg s17 12 = descW hWork descExitStored (by decide) := putReg_eq_same s16 12 _
    dsimp only [s18]; rw [putReg_eq_same]
    change (add (reg s17 14) (reg s17 12)).val = _
    rw [h18r14, h12, add_no_wrap _ _ (by rw [hDescVal]; change rec.descBase + 8 < 2 ^ bits; exact Nat.lt_of_lt_of_le (by omega) hI), hDescVal]; rfl
  have hs18 := step_loadInput16 inp (s := s18) (by simp [s18, s17, s16, s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 18) rfl)
    (by change I[(reg s18 15).val]? = _; rw [h18r15]; exact hStoHdr?)
    (prog_pc_lt _ (by simp [s18, s17, s16, s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s19 := putReg rfl s18 10 exitStoPtrW
  have hs19 := step_imm16 inp (s := s19) (by simp [s19, s18, s17, s16, s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 19) rfl)
    (prog_pc_lt _ (by simp [s19, s18, s17, s16, s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s20 := putReg rfl s19 12 (descW hWork descExitPrior (by decide))
  have hs20 := step_add16 inp (s := s20) (by simp [s20, s19, s18, s17, s16, s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 20) rfl)
    (prog_pc_lt _ (by simp [s20, s19, s18, s17, s16, s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s21 := putReg rfl s20 15 (add (reg s20 14) (reg s20 12))
  have h21r14 : reg s20 14 = descBaseW := by
    rw [putReg_eq_other s19 (by decide : (14 : Fin 16) ≠ 12), putReg_eq_other s18 (by decide : (14 : Fin 16) ≠ 10),
      putReg_eq_other s17 (by decide : (14 : Fin 16) ≠ 15)]
    exact h18r14
  have h21r15 : (reg s21 15).val = rec.descBase + descExitPrior := by
    have h12 : reg s20 12 = descW hWork descExitPrior (by decide) := putReg_eq_same s19 12 _
    dsimp only [s21]; rw [putReg_eq_same]
    change (add (reg s20 14) (reg s20 12)).val = _
    rw [h21r14, h12, add_no_wrap _ _ (by rw [hDescVal]; change rec.descBase + 9 < 2 ^ bits; exact Nat.lt_of_lt_of_le (by omega) hI), hDescVal]; rfl
  have hs21 := step_loadInput16 inp (s := s21) (by simp [s21, s20, s19, s18, s17, s16, s15, putReg_pc, h14pc']; exact placedSlice_fetch hPre22Pl (k := 21) rfl)
    (by change I[(reg s21 15).val]? = _; rw [h21r15]; exact hPriHdr?)
    (prog_pc_lt _ (by simp [s21, s20, s19, s18, s17, s16, s15, putReg_pc, h14pc']; unfold okPC pc6; dsimp only [pc5b]; omega))
  let s22 := putReg rfl s21 11 exitPriPtrW
  have h22pc : s22.pc = pc5b + 22 := by
    simp [s22, s21, s20, s19, s18, s17, s16, s15, putReg_pc, h14pc']
  have h22d : s22.data = s.data := by
    simp [s22, s21, s20, s19, s18, s17, s16, s15, putReg_data, h14d, s12, s11, s10, s9, s8, h7d, s5, s4, s3, h2d]
  have hp0_22 : Steps prog inp 22 s s22 :=
    ((hs01.append (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 hs56)))).append
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 hs1213)))))).append
      (Steps.cons hs14 (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18
        (Steps.cons hs19 (Steps.cons hs20 (Steps.cons hs21 (Steps.zero s22)))))))))
  have h22r6 : (reg s22 (r16 rfl 6)).val = wCols.labelAt y.val := by
    change (reg s22 6).val = _
    rw [putReg_eq_other s21 (by decide : (6 : Fin 16) ≠ 11), putReg_eq_other s20 (by decide : (6 : Fin 16) ≠ 15),
      putReg_eq_other s19 (by decide : (6 : Fin 16) ≠ 12), putReg_eq_other s18 (by decide : (6 : Fin 16) ≠ 10),
      putReg_eq_other s17 (by decide : (6 : Fin 16) ≠ 15), putReg_eq_other s16 (by decide : (6 : Fin 16) ≠ 12),
      putReg_eq_other s15 (by decide : (6 : Fin 16) ≠ 7), putReg_eq_other s14 (by decide : (6 : Fin 16) ≠ 15),
      h14r6]
    exact hLabVal
  have h22r7 : (reg s22 (r16 rfl 7)).val = ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode := by
    change (reg s22 7).val = _
    rw [putReg_eq_other s21 (by decide : (7 : Fin 16) ≠ 11), putReg_eq_other s20 (by decide : (7 : Fin 16) ≠ 15),
      putReg_eq_other s19 (by decide : (7 : Fin 16) ≠ 12), putReg_eq_other s18 (by decide : (7 : Fin 16) ≠ 10),
      putReg_eq_other s17 (by decide : (7 : Fin 16) ≠ 15), putReg_eq_other s16 (by decide : (7 : Fin 16) ≠ 12),
      putReg_eq_same s15 7 _]
    exact hDepVal
  have h22r8 : (reg s22 (r16 rfl 8)).val = y.val := by
    change (reg s22 8).val = _
    rw [putReg_eq_other s21 (by decide : (8 : Fin 16) ≠ 11), putReg_eq_other s20 (by decide : (8 : Fin 16) ≠ 15),
      putReg_eq_other s19 (by decide : (8 : Fin 16) ≠ 12), putReg_eq_other s18 (by decide : (8 : Fin 16) ≠ 10),
      putReg_eq_other s17 (by decide : (8 : Fin 16) ≠ 15), putReg_eq_other s16 (by decide : (8 : Fin 16) ≠ 12),
      putReg_eq_other s15 (by decide : (8 : Fin 16) ≠ 7), putReg_eq_other s14 (by decide : (8 : Fin 16) ≠ 15),
      h14r8]
    exact hYVal
  have h22r9 : (reg s22 (r16 rfl 9)).val = rec.exitDepthPtr := by
    change (reg s22 9).val = _
    rw [putReg_eq_other s21 (by decide : (9 : Fin 16) ≠ 11), putReg_eq_other s20 (by decide : (9 : Fin 16) ≠ 15),
      putReg_eq_other s19 (by decide : (9 : Fin 16) ≠ 12), putReg_eq_other s18 (by decide : (9 : Fin 16) ≠ 10),
      putReg_eq_other s17 (by decide : (9 : Fin 16) ≠ 15), putReg_eq_other s16 (by decide : (9 : Fin 16) ≠ 12),
      putReg_eq_other s15 (by decide : (9 : Fin 16) ≠ 7), putReg_eq_other s14 (by decide : (9 : Fin 16) ≠ 15),
      h14r9]
    exact hDepPtrVal
  have h22r10 : (reg s22 (r16 rfl 10)).val = R.base.val := by
    change (reg s22 10).val = _
    rw [putReg_eq_other s21 (by decide : (10 : Fin 16) ≠ 11), putReg_eq_other s20 (by decide : (10 : Fin 16) ≠ 15),
      putReg_eq_other s19 (by decide : (10 : Fin 16) ≠ 12), putReg_eq_same s18 10 _,
      hStoPtrVal, hRBase]
  have h22r11 : (reg s22 (r16 rfl 11)).val = B.start := by
    change (reg s22 11).val = _
    rw [putReg_eq_same s21 11 _, hPriPtrVal, hBStart]
  -- Run lifted_exitEval
  obtain ⟨sEval, kEval, hkEval, hsEval, hEvalPc, hIV0, hIV1, hEvalData⟩ :=
    lifted_exitEval (L := codeLayout bits I.size hI hWork) (h16 := rfl) (_hMemSz := rfl) ok prior hb B hPlaced
      hEvalPl (prog_pc_lt _ (by dsimp only [pc5b, sz]; unfold okPC pc6; omega)) inp rfl
      rec.exitDepthPtr hDepthContig (hLabF y) yIdx
      (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode) s22 h22pc
      h22r6 h22r7 h22r8 h22r9 h22r10 h22r11
  -- Store r0..r5 into slX0Tag..slX1Hi
  let x0t := reg sEval 0; let x0l := reg sEval 1; let x0h := reg sEval 2
  let x1t := reg sEval 3; let x1l := reg sEval 4; let x1h := reg sEval 5
  have hEvalDsz : sEval.data.size = queryWorkCap := by rw [hEvalData, h22d, hDataSz]
  obtain ⟨s24, hs22_23, h24pc, h24r, _, h24d⟩ := step_writeSlot (s := sEval) inp slX0Tag (by decide) 0
    (by decide : (0 : Fin 16) ≠ 15)
    (placedSlice_fetch_at hBig52Pl (k := 0) rfl (by rw [hEvalPc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 1) rfl (by rw [hEvalPc]; try omega))
    (prog_pc_lt _ (by rw [hEvalPc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [hEvalPc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [hEvalPc] at h24pc
  obtain ⟨s26, hs24_25, h26pc, h26r, _, h26d⟩ := step_writeSlot (s := s24) inp slX0Lo (by decide) 1
    (by decide : (1 : Fin 16) ≠ 15)
    (placedSlice_fetch_at hBig52Pl (k := 2) rfl (by rw [h24pc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 3) rfl (by rw [h24pc]; try omega))
    (prog_pc_lt _ (by rw [h24pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [h24pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [h24pc] at h26pc
  obtain ⟨s28, hs26_27, h28pc, h28r, _, h28d⟩ := step_writeSlot (s := s26) inp slX0Hi (by decide) 2
    (by decide : (2 : Fin 16) ≠ 15)
    (placedSlice_fetch_at hBig52Pl (k := 4) rfl (by rw [h26pc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 5) rfl (by rw [h26pc]; try omega))
    (prog_pc_lt _ (by rw [h26pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [h26pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [h26pc] at h28pc
  obtain ⟨s30, hs28_29, h30pc, h30r, _, h30d⟩ := step_writeSlot (s := s28) inp slX1Tag (by decide) 3
    (by decide : (3 : Fin 16) ≠ 15)
    (placedSlice_fetch_at hBig52Pl (k := 6) rfl (by rw [h28pc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 7) rfl (by rw [h28pc]; try omega))
    (prog_pc_lt _ (by rw [h28pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [h28pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [h28pc] at h30pc
  obtain ⟨s32, hs30_31, h32pc, h32r, _, h32d⟩ := step_writeSlot (s := s30) inp slX1Lo (by decide) 4
    (by decide : (4 : Fin 16) ≠ 15)
    (placedSlice_fetch_at hBig52Pl (k := 8) rfl (by rw [h30pc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 9) rfl (by rw [h30pc]; try omega))
    (prog_pc_lt _ (by rw [h30pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [h30pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [h30pc] at h32pc
  obtain ⟨s34, hs32_33, h34pc, h34r, _, h34d⟩ := step_writeSlot (s := s32) inp slX1Hi (by decide) 5
    (by decide : (5 : Fin 16) ≠ 15)
    (placedSlice_fetch_at hBig52Pl (k := 10) rfl (by rw [h32pc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 11) rfl (by rw [h32pc]; try omega))
    (prog_pc_lt _ (by rw [h32pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [h32pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [h32pc] at h34pc
  have h34dSw : s34.data[slSwapped]? = some swW := by
    rw [h34d, data_set_other _ _ _ _ (by decide), h32d, data_set_other _ _ _ _ (by decide),
      h30d, data_set_other _ _ _ _ (by decide), h28d, data_set_other _ _ _ _ (by decide),
      h26d, data_set_other _ _ _ _ (by decide), h24d, data_set_other _ _ _ _ (by decide),
      hEvalData, h22d]
    exact hSwW
  have h34frame : ∀ idx, idx < 14 → s34.data[idx]? = s.data[idx]? := by
    intro idx hidx
    rw [h34d, data_set_other _ _ _ _ (by dsimp only [slX1Hi]; omega),
      h32d, data_set_other _ _ _ _ (by dsimp only [slX1Lo]; omega),
      h30d, data_set_other _ _ _ _ (by dsimp only [slX1Tag]; omega),
      h28d, data_set_other _ _ _ _ (by dsimp only [slX0Hi]; omega),
      h26d, data_set_other _ _ _ _ (by dsimp only [slX0Lo]; omega),
      h24d, data_set_other _ _ _ _ (by dsimp only [slX0Tag]; omega),
      hEvalData, h22d]
  have h34dsz : s34.data.size = queryWorkCap := by
    rw [h34d, Array.size_set, h32d, Array.size_set, h30d, Array.size_set,
      h28d, Array.size_set, h26d, Array.size_set, h24d, Array.size_set, hEvalDsz]
  have h34_X0T : s34.data[slX0Tag]? = some x0t := by
    rw [h34d, data_set_other _ _ _ _ (by decide), h32d, data_set_other _ _ _ _ (by decide),
      h30d, data_set_other _ _ _ _ (by decide), h28d, data_set_other _ _ _ _ (by decide),
      h26d, data_set_other _ _ _ _ (by decide), h24d, data_set_same]
  have h34_X0L : s34.data[slX0Lo]? = some x0l := by
    rw [h34d, data_set_other _ _ _ _ (by decide), h32d, data_set_other _ _ _ _ (by decide),
      h30d, data_set_other _ _ _ _ (by decide), h28d, data_set_other _ _ _ _ (by decide),
      h26d, data_set_same, h24r 1 (by decide)]
  have h34_X0H : s34.data[slX0Hi]? = some x0h := by
    rw [h34d, data_set_other _ _ _ _ (by decide), h32d, data_set_other _ _ _ _ (by decide),
      h30d, data_set_other _ _ _ _ (by decide), h28d, data_set_same,
      h26r 2 (by decide), h24r 2 (by decide)]
  have h34_X1T : s34.data[slX1Tag]? = some x1t := by
    rw [h34d, data_set_other _ _ _ _ (by decide), h32d, data_set_other _ _ _ _ (by decide),
      h30d, data_set_same, h28r 3 (by decide),
      h26r 3 (by decide), h24r 3 (by decide)]
  have h34_X1L : s34.data[slX1Lo]? = some x1l := by
    rw [h34d, data_set_other _ _ _ _ (by decide), h32d, data_set_same,
      h30r 4 (by decide), h28r 4 (by decide),
      h26r 4 (by decide), h24r 4 (by decide)]
  have h34_X1H : s34.data[slX1Hi]? = some x1h := by
    rw [h34d, data_set_same, h32r 5 (by decide),
      h30r 5 (by decide), h28r 5 (by decide),
      h26r 5 (by decide), h24r 5 (by decide)]
  -- Read slSwapped & branch
  obtain ⟨s36, hs34_35, h36pc, h36r, h36r0, _, h36d⟩ := step_readSlot (s := s34) inp slSwapped (by decide) 0
    (by decide : (0 : Fin 16) ≠ 15) swW h34dSw
    (placedSlice_fetch_at hBig52Pl (k := 12) rfl (by rw [h34pc]; try omega))
    (placedSlice_fetch_at hBig52Pl (k := 13) rfl (by rw [h34pc]; try omega))
    (prog_pc_lt _ (by rw [h34pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    (prog_pc_lt _ (by rw [h34pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  rw [h34pc] at h36pc
  have hs36 := step_imm16 inp (s := s36) (placedSlice_fetch_at hBig52Pl (k := 14) rfl (by rw [h36pc]; try omega))
    (prog_pc_lt _ (by rw [h36pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
  let s37 := putReg rfl s36 6 (oneW hTag)
  have h37pc : s37.pc = pc5b + 37 + sz := by simp [s37, putReg_pc, h36pc]; omega
  have hp0_37 : Steps prog inp (22 + kEval + 15) s s37 := by
    have hW : Steps prog inp 12 sEval s34 :=
      hs22_23.append (hs24_25.append (hs26_27.append (hs28_29.append (hs30_31.append hs32_33))))
    have hk := ((hp0_22.append hsEval).append hW).append (hs34_35.append (Steps.cons hs36 (Steps.zero s37)))
    simpa only [Nat.add_assoc] using hk
  by_cases hlt : P.fst < P.snd
  · have hSw0 : swW.val = 0 := by rw [hSwVal, ite_eq_left hlt]
    have hlt37 : (reg s37 0).val < (reg s37 6).val := by
      rw [putReg_eq_other s36 (by decide : (0 : Fin 16) ≠ 6), putReg_eq_same s36 6 _, h36r0, hSw0]
      exact (by decide : 0 < 1)
    have hs37 := step_branchLt16 inp (s := s37) (placedSlice_fetch_at hBig52Pl (k := 15) rfl (by rw [h37pc]; omega)) (by
      change (if (reg s37 0).val < (reg s37 6).val then pc5b + 62 + sz else pc5b + 38 + sz) < _
      rw [ite_eq_left hlt37]; exact prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    let s62 := { s37 with pc := if (reg s37 0).val < (reg s37 6).val then pc5b + 62 + sz else pc5b + 38 + sz }
    have h62pc : s62.pc = pc5b + 62 + sz := by
      change (if (reg s37 0).val < (reg s37 6).val then _ else _) = _; exact ite_eq_left hlt37
    have h62d : s62.data = s34.data := by change s37.data = s34.data; rw [putReg_data, h36d]
    refine ⟨s62, 22 + kEval + 16, x0t, x0l, x0h, x1t, x1l, x1h, by omega,
      hp0_37.append (Steps.cons hs37 (Steps.zero s62)), h62pc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h62d]; exact h34dsz
    · intro idx hidx; rw [h62d]; exact h34frame idx hidx
    · rw [ite_eq_left hlt]; exact hIV0
    · rw [ite_eq_left hlt]; exact hIV1
    · rw [h62d]; exact h34_X0T
    · rw [h62d]; exact h34_X0L
    · rw [h62d]; exact h34_X0H
    · rw [h62d]; exact h34_X1T
    · rw [h62d]; exact h34_X1L
    · rw [h62d]; exact h34_X1H
  · have hSw1 : swW.val = 1 := by rw [hSwVal, ite_eq_right hlt]
    have hge37 : ¬ ((reg s37 0).val < (reg s37 6).val) := by
      rw [putReg_eq_other s36 (by decide : (0 : Fin 16) ≠ 6), putReg_eq_same s36 6 _, h36r0, hSw1]
      change ¬ (1 < 1); omega
    have hs37 := step_branchLt16 inp (s := s37) (placedSlice_fetch_at hBig52Pl (k := 15) rfl (by rw [h37pc]; omega)) (by
      change (if (reg s37 0).val < (reg s37 6).val then pc5b + 62 + sz else pc5b + 38 + sz) < _
      rw [ite_eq_right hge37]; exact prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    let s38 := { s37 with pc := if (reg s37 0).val < (reg s37 6).val then pc5b + 62 + sz else pc5b + 38 + sz }
    have h38pc : s38.pc = pc5b + 38 + sz := by
      change (if (reg s37 0).val < (reg s37 6).val then _ else _) = _; exact ite_eq_right hge37
    have h38d : s38.data = s34.data := by change s37.data = s34.data; rw [putReg_data, h36d]
    -- Read 6 slots into r0..r5 and write swapped
    obtain ⟨s40, hs38_39, h40pc, h40r, h40r0, _, h40d⟩ := step_readSlot (s := s38) inp slX0Tag (by decide) 0
      (by decide : (0 : Fin 16) ≠ 15) x0t (by rw [h38d]; exact h34_X0T)
      (placedSlice_fetch_at hBig52Pl (k := 16) rfl (by rw [h38pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 17) rfl (by rw [h38pc]; omega))
      (prog_pc_lt _ (by rw [h38pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h38pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h38pc] at h40pc
    obtain ⟨s42, hs40_41, h42pc, h42r, h42r1, _, h42d⟩ := step_readSlot (s := s40) inp slX0Lo (by decide) 1
      (by decide : (1 : Fin 16) ≠ 15) x0l (by rw [h40d, h38d]; exact h34_X0L)
      (placedSlice_fetch_at hBig52Pl (k := 18) rfl (by rw [h40pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 19) rfl (by rw [h40pc]; omega))
      (prog_pc_lt _ (by rw [h40pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h40pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h40pc] at h42pc
    obtain ⟨s44, hs42_43, h44pc, h44r, h44r2, _, h44d⟩ := step_readSlot (s := s42) inp slX0Hi (by decide) 2
      (by decide : (2 : Fin 16) ≠ 15) x0h (by rw [h42d, h40d, h38d]; exact h34_X0H)
      (placedSlice_fetch_at hBig52Pl (k := 20) rfl (by rw [h42pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 21) rfl (by rw [h42pc]; omega))
      (prog_pc_lt _ (by rw [h42pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h42pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h42pc] at h44pc
    obtain ⟨s46, hs44_45, h46pc, h46r, h46r3, _, h46d⟩ := step_readSlot (s := s44) inp slX1Tag (by decide) 3
      (by decide : (3 : Fin 16) ≠ 15) x1t (by rw [h44d, h42d, h40d, h38d]; exact h34_X1T)
      (placedSlice_fetch_at hBig52Pl (k := 22) rfl (by rw [h44pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 23) rfl (by rw [h44pc]; omega))
      (prog_pc_lt _ (by rw [h44pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h44pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h44pc] at h46pc
    obtain ⟨s48, hs46_47, h48pc, h48r, h48r4, _, h48d⟩ := step_readSlot (s := s46) inp slX1Lo (by decide) 4
      (by decide : (4 : Fin 16) ≠ 15) x1l (by rw [h46d, h44d, h42d, h40d, h38d]; exact h34_X1L)
      (placedSlice_fetch_at hBig52Pl (k := 24) rfl (by rw [h46pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 25) rfl (by rw [h46pc]; omega))
      (prog_pc_lt _ (by rw [h46pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h46pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h46pc] at h48pc
    obtain ⟨s50, hs48_49, h50pc, h50r, h50r5, _, h50d⟩ := step_readSlot (s := s48) inp slX1Hi (by decide) 5
      (by decide : (5 : Fin 16) ≠ 15) x1h (by rw [h48d, h46d, h44d, h42d, h40d, h38d]; exact h34_X1H)
      (placedSlice_fetch_at hBig52Pl (k := 26) rfl (by rw [h48pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 27) rfl (by rw [h48pc]; omega))
      (prog_pc_lt _ (by rw [h48pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h48pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h48pc] at h50pc
    have h50r0 : reg s50 0 = x0t := by
      rw [h50r 0 (by decide) (by decide), h48r 0 (by decide) (by decide), h46r 0 (by decide) (by decide),
        h44r 0 (by decide) (by decide), h42r 0 (by decide) (by decide)]; exact h40r0
    have h50r1 : reg s50 1 = x0l := by
      rw [h50r 1 (by decide) (by decide), h48r 1 (by decide) (by decide), h46r 1 (by decide) (by decide),
        h44r 1 (by decide) (by decide)]; exact h42r1
    have h50r2 : reg s50 2 = x0h := by
      rw [h50r 2 (by decide) (by decide), h48r 2 (by decide) (by decide), h46r 2 (by decide) (by decide)]; exact h44r2
    have h50r3 : reg s50 3 = x1t := by
      rw [h50r 3 (by decide) (by decide), h48r 3 (by decide) (by decide)]; exact h46r3
    have h50r4 : reg s50 4 = x1l := by
      rw [h50r 4 (by decide) (by decide)]; exact h48r4
    have h50d' : s50.data = s34.data := by rw [h50d, h48d, h46d, h44d, h42d, h40d, h38d]
    have h50dsz : s50.data.size = queryWorkCap := by rw [h50d']; exact h34dsz
    obtain ⟨s52, hs50_51, h52pc, h52r, _, h52d⟩ := step_writeSlot (s := s50) inp slX0Tag (by decide) 3 (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 28) rfl (by rw [h50pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 29) rfl (by rw [h50pc]; omega))
      (prog_pc_lt _ (by rw [h50pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h50pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h50pc] at h52pc
    obtain ⟨s54, hs52_53, h54pc, h54r, _, h54d⟩ := step_writeSlot (s := s52) inp slX0Lo (by decide) 4 (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 30) rfl (by rw [h52pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 31) rfl (by rw [h52pc]; omega))
      (prog_pc_lt _ (by rw [h52pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h52pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h52pc] at h54pc
    obtain ⟨s56, hs54_55, h56pc, h56r, _, h56d⟩ := step_writeSlot (s := s54) inp slX0Hi (by decide) 5 (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 32) rfl (by rw [h54pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 33) rfl (by rw [h54pc]; omega))
      (prog_pc_lt _ (by rw [h54pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h54pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h54pc] at h56pc
    obtain ⟨s58, hs56_57, h58pc, h58r, _, h58d⟩ := step_writeSlot (s := s56) inp slX1Tag (by decide) 0 (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 34) rfl (by rw [h56pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 35) rfl (by rw [h56pc]; omega))
      (prog_pc_lt _ (by rw [h56pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h56pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h56pc] at h58pc
    obtain ⟨s60, hs58_59, h60pc, h60r, _, h60d⟩ := step_writeSlot (s := s58) inp slX1Lo (by decide) 1 (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 36) rfl (by rw [h58pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 37) rfl (by rw [h58pc]; omega))
      (prog_pc_lt _ (by rw [h58pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h58pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h58pc] at h60pc
    obtain ⟨s62, hs60_61, h62pc, _, _, h62d⟩ := step_writeSlot (s := s60) inp slX1Hi (by decide) 2 (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 38) rfl (by rw [h60pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 39) rfl (by rw [h60pc]; omega))
      (prog_pc_lt _ (by rw [h60pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h60pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h60pc] at h62pc
    have h62pc_aux : ∀ a b : Nat, a + 38 + b + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 + 2 = a + 62 + b :=
      fun a b => by omega
    have h62pc' : s62.pc = pc5b + 62 + sz := h62pc.trans (h62pc_aux pc5b sz)
    have hk62_aux : ∀ k st : Nat, k ≤ 96 * st + 28 → 22 + k + 16 + 24 ≤ 96 * st + 90 :=
      fun k st h => by omega
    have hs38_62 : Steps prog inp 24 s38 s62 :=
      ((hs38_39.append (hs40_41.append (hs42_43.append (hs44_45.append (hs46_47.append hs48_49))))).append
       (hs50_51.append (hs52_53.append (hs54_55.append (hs56_57.append (hs58_59.append hs60_61))))))
    refine ⟨s62, 22 + kEval + 16 + 24, x1t, x1l, x1h, x0t, x0l, x0h, hk62_aux _ _ hkEval,
      ((hp0_37.append (Steps.cons hs37 (Steps.zero s38))).append hs38_62), h62pc', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h62d, Array.size_set, h60d, Array.size_set, h58d, Array.size_set,
        h56d, Array.size_set, h54d, Array.size_set, h52d, Array.size_set, h50dsz]
    · intro idx hidx
      rw [h62d, data_set_other _ _ _ _ (by dsimp only [slX1Hi]; omega),
        h60d, data_set_other _ _ _ _ (by dsimp only [slX1Lo]; omega),
        h58d, data_set_other _ _ _ _ (by dsimp only [slX1Tag]; omega),
        h56d, data_set_other _ _ _ _ (by dsimp only [slX0Hi]; omega),
        h54d, data_set_other _ _ _ _ (by dsimp only [slX0Lo]; omega),
        h52d, data_set_other _ _ _ _ (by dsimp only [slX0Tag]; omega),
        h50d']
      exact h34frame idx hidx
    · rw [ite_eq_right hlt]; exact hIV1
    · rw [ite_eq_right hlt]; exact hIV0
    · rw [h62d, data_set_other _ _ _ _ (by decide), h60d, data_set_other _ _ _ _ (by decide),
        h58d, data_set_other _ _ _ _ (by decide), h56d, data_set_other _ _ _ _ (by decide),
        h54d, data_set_other _ _ _ _ (by decide), h52d, data_set_same, h50r3]
    · rw [h62d, data_set_other _ _ _ _ (by decide), h60d, data_set_other _ _ _ _ (by decide),
        h58d, data_set_other _ _ _ _ (by decide), h56d, data_set_other _ _ _ _ (by decide),
        h54d, data_set_same, h52r 4 (by decide), h50r4]
    · rw [h62d, data_set_other _ _ _ _ (by decide), h60d, data_set_other _ _ _ _ (by decide),
        h58d, data_set_other _ _ _ _ (by decide), h56d, data_set_same,
        h54r 5 (by decide), h52r 5 (by decide), h50r5]
    · rw [h62d, data_set_other _ _ _ _ (by decide), h60d, data_set_other _ _ _ _ (by decide),
        h58d, data_set_same, h56r 0 (by decide), h54r 0 (by decide), h52r 0 (by decide), h50r0]
    · rw [h62d, data_set_other _ _ _ _ (by decide), h60d, data_set_same,
        h58r 1 (by decide), h56r 1 (by decide), h54r 1 (by decide), h52r 1 (by decide), h50r1]
    · rw [h62d, data_set_same, h60r 2 (by decide), h58r 2 (by decide), h56r 2 (by decide),
        h54r 2 (by decide), h52r 2 (by decide), h50r2]

private theorem intervalCodec_empty_tag {bits : Nat} (hTag : TagsFit bits)
    (iv : ExitMap.Interval) (hx : ExitMap.Retention.RankBound (2 ^ bits) iv) (h : iv = .empty) :
    ((ExitMap.Retention.intervalCodec hTag).encode iv hx 0).val = 0 := by
  subst h; rfl

private theorem intervalCodec_span_vals {bits : Nat} (hTag : TagsFit bits)
    (iv : ExitMap.Interval) (hx : ExitMap.Retention.RankBound (2 ^ bits) iv) {lo hi : Nat} (h : iv = .span lo hi) :
    ((ExitMap.Retention.intervalCodec hTag).encode iv hx 0).val = 1 ∧
    ((ExitMap.Retention.intervalCodec hTag).encode iv hx 1).val = lo ∧
    ((ExitMap.Retention.intervalCodec hTag).encode iv hx 2).val = hi := by
  subst h; exact ⟨rfl, rfl, rfl⟩

private theorem exec_blkExitTest
    {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : DenseQuotientRows.Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {dDense : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr dDense)
    {large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK dDense)}
    {dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))}
    {sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount}
    {rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense) → Nat}
    (_ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large)
    (wCols : WordColumns bits)
    {endpoints : Nat}
    {R : ExitMap.JumpMapRoute.StoredExit.Region bits I.size} {F : JumpForest}
    {ref : Nat → ExitMap.CheckedFold.Stored}
    {wFit : ExitMap.Retention.Width bits (max R.slots endpoints)}
    (ok : ExitMap.JumpMapRoute.StoredExit.Occupied I R F ref wFit)
    (prior : Array (Option ExitMap.Values))
    (hb : ExitMap.SealedPriorBase.BaseBound (max R.slots endpoints) prior)
    (B : ExitMap.SealedPriorBase.BaseView prior.size I.size)
    (hPlaced : ExitMap.SealedPriorBase.Placed wFit prior hb I B)
    (hLabels : SliceAt I rec.labelsPtr wCols.labels)
    (hLabelsSz : wCols.labels.size =
      (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount)
    (hLabF : ∀ y : Fin (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount,
      wCols.labelAt y.val < F.size)
    (hPriorSz : prior.size =
      (denseQuotient progress injRank q originalRows hRows rows childOK dDense).vertexCount)
    (hRBase : R.base.val = rec.exitStoredPtr)
    (hBStart : B.start = rec.exitPriorPtr)
    (hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = rec.exitDepthPtr + x.val)
    (inv : OriginalEntryInverse.Index q)
    (hOrigOfEntry : NatSliceAt I Hdr.origOfEntryBase q.count
      (fun rk => if hr : rk < q.count then (inv.slots.read ⟨rk, hr⟩).val else 0))
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (hStop : NatSliceAt I Hdr.stopBase q.count
      (fun d => if hd : d < q.count then q.reader.stop ⟨d, hd⟩ else 0))
    (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (y : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK dDense))
    (aNode : Nat) (haNode : aNode < F.size)
    (aDense bDense : Fin q.count)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc5b)
    (hDataSz : s.data.size = queryWorkCap)
    (hDesc : (s.data[slDescBase]?).map Fin.val = some rec.descBase)
    (hSw : (s.data[slSwapped]?).map Fin.val = some (if P.fst < P.snd then 0 else 1))
    (hHit : (s.data[slHitNode]?).map Fin.val = some aNode)
    (hY : (s.data[slYLocal]?).map Fin.val = some y.val)
    (hAD : (s.data[slADense]?).map Fin.val = some aDense.val)
    (hBD : (s.data[slBDense]?).map Fin.val = some bDense.val)
    (hX0Bound : ∀ lo hi, (ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
      ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).x0 =
      .span lo hi → lo < q.count ∧ hi < q.count)
    (hX1Bound : ∀ lo hi, (ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
      ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).x1 =
      .span lo hi → lo < q.count ∧ hi < q.count) :
    let prog := oracleQueryProgram hI hWork hTag
    let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
    let res := ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
      ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)
    let s0 := ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) res.x0
    let s1 := ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) res.x1
    let sp := if P.fst < P.snd then (s0, s1) else (s1, s0)
    ∃ t k,
      k ≤ 96 * (ExitMap.JumpMapRoute.StoredExit.foldStored I R wFit.tags
        (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).steps + 194 ∧
      Steps prog inp k s t ∧
      t.pc = (if spanSurvives q.reader.entry q.reader.stop aDense sp.1 ∨ spanSurvives q.reader.entry q.reader.stop bDense sp.2
              then okPC hI hTag else failPC hI hTag) := by
  intro prog inp res s0 s1 sp
  let sz := exitEvalSize hI hTag
  have h5bPl := place_blk5b hI hWork hTag
  unfold blkExitTest at h5bPl
  have hEvalSz : (liftMap (ρ16 (rfl : (codeLayout bits I.size hI hWork).registerCount = 16)
      (rfl : (ExitEval.exitEvalLayout bits I.size hI).registerCount = 16))
      (pc5b + 22) (pc5b + 22 + sz) (ExitEval.exitEvalProgram (fits := hI) hTag)).size = sz := by
    simp [liftMap, sz, exitEvalSize]
  have hA1Sz := ancestorCheckBlock_size (L := codeLayout bits I.size hI hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 74 + sz) (pc5b + 90 + sz)
  have hA2Sz := ancestorCheckBlock_size (L := codeLayout bits I.size hI hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 100 + sz) (pc5b + 116 + sz)
  have hA3Sz := ancestorCheckBlock_size (L := codeLayout bits I.size hI hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 130 + sz) (pc5b + 146 + sz)
  have hA4Sz := ancestorCheckBlock_size (L := codeLayout bits I.size hI hWork) rfl
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) 1 2 (pc5b + 156 + sz) (pc5b + 172 + sz)
  have hTail2Pl := placedSlice_right_pc (n := pc5b + 172 + sz) h5bPl
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz, hA2Sz, hA3Sz, hA4Sz]; omega)
  have hAnc4Pl := placedSlice_right_pc (n := pc5b + 156 + sz) (placedSlice_append_left h5bPl)
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz, hA2Sz, hA3Sz]; omega)
  have hMid3Pl := placedSlice_right_pc (n := pc5b + 146 + sz) (placedSlice_append_left (placedSlice_append_left h5bPl))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz, hA2Sz, hA3Sz]; omega)
  have hAnc3Pl := placedSlice_right_pc (n := pc5b + 130 + sz) (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h5bPl)))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz, hA2Sz]; omega)
  have hMid2Pl := placedSlice_right_pc (n := pc5b + 116 + sz) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left h5bPl))))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz, hA2Sz]; omega)
  have hAnc2Pl := placedSlice_right_pc (n := pc5b + 100 + sz) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h5bPl)))))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz]; omega)
  have hMid1Pl := placedSlice_right_pc (n := pc5b + 90 + sz) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h5bPl))))))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz, hA1Sz]; omega)
  have hAnc1Pl := placedSlice_right_pc (n := pc5b + 74 + sz) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left h5bPl)))))))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz]; omega)
  have hBig52Pl := placedSlice_right_pc (n := pc5b + 22 + sz) (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left (placedSlice_append_left
    (placedSlice_append_left (placedSlice_append_left h5bPl))))))))
    (by simp only [Array.size_append, List.size_toArray, List.length_cons, List.length_nil]
        rw [hEvalSz]; omega)
  -- Execute prepAndEval
  obtain ⟨s62, k1, w0, w1, w2, w3, w4, w5, hk1, hp0_62, h62pc, h62dsz, h62frame, hIVa, hIVb, hX0T, hX0L, hX0H, hX1T, hX1L, hX1H⟩ :=
    exec_blkExitTest_prepAndEval hI hWork hTag progress injRank q originalRows hRows rows childOK
      rec _ordRes wCols ok prior hb B hPlaced hLabels hLabelsSz hLabF hPriorSz hRBase hBStart hDepthContig
      P y aNode haNode s hpc hDataSz hDesc hSw hHit hY
  -- Unpack headers & scratch for aDense, bDense
  obtain ⟨aW, haW, haVal⟩ : ∃ w, s.data[slADense]? = some w ∧ w.val = aDense.val := by
    cases hw : s.data[slADense]? with
    | none => simp [hw] at hAD
    | some w => exact ⟨w, rfl, by simpa [hw] using hAD⟩
  obtain ⟨bW, hbW, hbVal⟩ : ∃ w, s.data[slBDense]? = some w ∧ w.val = bDense.val := by
    cases hw : s.data[slBDense]? with
    | none => simp [hw] at hBD
    | some w => exact ⟨w, rfl, by simpa [hw] using hBD⟩
  have h62AD : s62.data[slADense]? = some aW := by rw [h62frame slADense (by decide)]; exact haW
  have h62BD : s62.data[slBDense]? = some bW := by rw [h62frame slBDense (by decide)]; exact hbW
  have hOrigHdrLt : hdrOrigOfEntry < I.size := by
    have := Hdr.hdr_fit; unfold oracleHeaderSize hdrOrigOfEntry at *; omega
  have hEntryHdrLt : hdrEntry < I.size := by
    have := Hdr.hdr_fit; unfold oracleHeaderSize hdrEntry at *; omega
  have hStopHdrLt : hdrStop < I.size := by
    have := Hdr.hdr_fit; unfold oracleHeaderSize hdrStop at *; omega
  let origPtrW := I[hdrOrigOfEntry]'hOrigHdrLt
  let entryBaseW := I[hdrEntry]'hEntryHdrLt
  let stopBaseW := I[hdrStop]'hStopHdrLt
  have hOrigHdr? : I[hdrOrigOfEntry]? = some origPtrW := getElem?_pos I _ hOrigHdrLt
  have hEH? : I[hdrEntry]? = some entryBaseW := getElem?_pos I _ hEntryHdrLt
  have hSH? : I[hdrStop]? = some stopBaseW := getElem?_pos I _ hStopHdrLt
  have hOrigPtrVal : origPtrW.val = Hdr.origOfEntryBase := by
    have hm := Hdr.hOrigOfEntryBase; rw [hOrigHdr?, Option.map_some] at hm; exact Option.some.inj hm
  have hEntryBaseVal : entryBaseW.val = Hdr.entryBase := by
    have hm := Hdr.hEntryBase; rw [hEH?, Option.map_some] at hm; exact Option.some.inj hm
  have hStopBaseVal : stopBaseW.val = Hdr.stopBase := by
    have hm := Hdr.hStopBase; rw [hSH?, Option.map_some] at hm; exact Option.some.inj hm
  -- Helper to extract (I[entryBaseW + d], I[stopBaseW + d]) for any d : Fin q.count
  have hEntryAt : ∀ (d : Fin q.count) (w : Word bits), w.val = d.val →
      ∃ ew, I[entryBaseW.val + w.val]? = some ew ∧ ew.val = q.reader.entry d := by
    intro d w hw
    have hlt : Hdr.entryBase + d.val < I.size := by have := hEntry.1; omega
    refine ⟨I[Hdr.entryBase + d.val]'hlt, ?_, ?_⟩
    · rw [hEntryBaseVal, hw]; exact getElem?_pos I _ hlt
    · have hm := hEntry.2 d.val d.isLt; rw [getElem?_pos I _ hlt, Option.map_some] at hm
      dsimp only at hm; rw [dite_eq_left d.isLt] at hm
      exact Option.some.inj hm
  have hStopAt : ∀ (d : Fin q.count) (w : Word bits), w.val = d.val →
      ∃ sw, I[stopBaseW.val + w.val]? = some sw ∧ sw.val = q.reader.stop d := by
    intro d w hw
    have hlt : Hdr.stopBase + d.val < I.size := by have := hStop.1; omega
    refine ⟨I[Hdr.stopBase + d.val]'hlt, ?_, ?_⟩
    · rw [hStopBaseVal, hw]; exact getElem?_pos I _ hlt
    · have hm := hStop.2 d.val d.isLt; rw [getElem?_pos I _ hlt, Option.map_some] at hm
      dsimp only at hm; rw [dite_eq_left d.isLt] at hm
      exact Option.some.inj hm
  have hOrigAt : ∀ (rk : Fin q.count) (w : Word bits), w.val = rk.val →
      ∃ ow, I[origPtrW.val + w.val]? = some ow ∧ ow.val = (inv.slots.read rk).val := by
    intro rk w hw
    have hlt : Hdr.origOfEntryBase + rk.val < I.size := by have := hOrigOfEntry.1; omega
    refine ⟨I[Hdr.origOfEntryBase + rk.val]'hlt, ?_, ?_⟩
    · rw [hOrigPtrVal, hw]; exact getElem?_pos I _ hlt
    · have hm := hOrigOfEntry.2 rk.val rk.isLt; rw [getElem?_pos I _ hlt, Option.map_some] at hm
      dsimp only at hm; rw [dite_eq_left rk.isLt] at hm
      exact Option.some.inj hm
  -- Abbreviations for the two oriented intervals and spans
  let ivA := if P.fst < P.snd then res.x0 else res.x1
  let ivB := if P.fst < P.snd then res.x1 else res.x0
  have hSpA : sp.1 = ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) ivA := by
    dsimp only [sp, ivA, s0, s1]; split <;> rfl
  have hSpB : sp.2 = ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) ivB := by
    dsimp only [sp, ivB, s0, s1]; split <;> rfl
  have hIvABound : ∀ lo hi, ivA = .span lo hi → lo < q.count ∧ hi < q.count := by
    intro lo hi h
    dsimp only [ivA] at h
    by_cases hlt : P.fst < P.snd
    · rw [ite_eq_left hlt] at h; exact hX0Bound lo hi h
    · rw [ite_eq_right hlt] at h; exact hX1Bound lo hi h
  have hIvBBound : ∀ lo hi, ivB = .span lo hi → lo < q.count ∧ hi < q.count := by
    intro lo hi h
    dsimp only [ivB] at h
    by_cases hlt : P.fst < P.snd
    · rw [ite_eq_left hlt] at h; exact hX1Bound lo hi h
    · rw [ite_eq_right hlt] at h; exact hX0Bound lo hi h
  -- Helper: given s_b at pc5b + 118 + sz with s_b.data = s62.data, run Half B
  have hHalfB : ∀ (sB : State (codeLayout bits I.size hI hWork)),
      sB.pc = pc5b + 118 + sz → sB.data = s62.data →
      ∃ t kB, kB ≤ 52 ∧ Steps prog inp kB sB t ∧
        t.pc = (if spanSurvives q.reader.entry q.reader.stop bDense sp.2 then okPC hI hTag else failPC hI hTag) := by
    intro sB hBpc hBd
    obtain ⟨hxB, hT3, hL4, hH5⟩ := hIVb
    cases hIvBCase : ivB with
    | empty =>
      have hSpBNone : sp.2 = none := by rw [hSpB, hIvBCase]; rfl
      have hSurvF : spanSurvives q.reader.entry q.reader.stop bDense sp.2 = false := by rw [hSpBNone]; rfl
      have hw3z : w3.val = 0 := by
        dsimp only [ivB, res] at hIvBCase
        rw [hT3]; exact intervalCodec_empty_tag hTag _ hxB hIvBCase
      obtain ⟨sB2, hsB01, hB2pc, _, hB2r0, _, _⟩ := step_readSlot (s := sB) inp slX1Tag (by decide) 0
        (by decide : (0 : Fin 16) ≠ 15) w3 (by rw [hBd]; exact hX1T)
        (placedSlice_fetch_at hMid2Pl (k := 2) rfl (by rw [hBpc]; omega))
        (placedSlice_fetch_at hMid2Pl (k := 3) rfl (by rw [hBpc]; omega))
        (prog_pc_lt _ (by rw [hBpc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
        (prog_pc_lt _ (by rw [hBpc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      rw [hBpc] at hB2pc
      have hsB2 := step_imm16 inp (s := sB2) (placedSlice_fetch_at hMid2Pl (k := 4) rfl (by rw [hB2pc]; omega))
        (prog_pc_lt _ (by rw [hB2pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      let sB3 := putReg rfl sB2 6 (oneW hTag)
      have hB3pc : sB3.pc = pc5b + 121 + sz := by simp [sB3, putReg_pc, hB2pc]; omega
      have hltB3 : (reg sB3 0).val < (reg sB3 6).val := by
        rw [putReg_eq_other sB2 (by decide : (0 : Fin 16) ≠ 6), putReg_eq_same sB2 6 _, hB2r0, hw3z]
        exact (by decide : 0 < 1)
      have hsB3 := step_branchLt16 inp (s := sB3) (placedSlice_fetch_at hMid2Pl (k := 5) rfl (by rw [hB3pc]; omega)) (by
        change (if (reg sB3 0).val < (reg sB3 6).val then failPC hI hTag else pc5b + 122 + sz) < _
        rw [ite_eq_left hltB3]; exact failPC_lt hI hWork hTag)
      let t := { sB3 with pc := if (reg sB3 0).val < (reg sB3 6).val then failPC hI hTag else pc5b + 122 + sz }
      refine ⟨t, 4, by decide, hsB01.append (Steps.cons hsB2 (Steps.cons hsB3 (Steps.zero t))), ?_⟩
      change (if (reg sB3 0).val < (reg sB3 6).val then _ else _) = _
      rw [ite_eq_left hltB3, hSurvF]; rfl
    | span lo hi =>
      obtain ⟨hLoLt, hHiLt⟩ := hIvBBound lo hi hIvBCase
      have hSpBSome : sp.2 = some (inv.slots.read ⟨lo, hLoLt⟩, inv.slots.read ⟨hi, hHiLt⟩) := by
        rw [hSpB, hIvBCase]
        unfold ExitSpanBridge.toSpan ExitSpanBridge.readEntry
        simp [dite_eq_left hLoLt, dite_eq_left hHiLt]
      have hIvBCase' : (if P.fst < P.snd then (ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
          ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).x1
          else (ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
          ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).x0) =
          .span lo hi := by
        dsimp only [ivB, res] at hIvBCase; exact hIvBCase
      obtain ⟨hw3_1', hw4_lo', hw5_hi'⟩ := intervalCodec_span_vals hTag _ hxB hIvBCase'
      have hw3_1 : w3.val = 1 := by rw [hT3]; exact hw3_1'
      have hw4_lo : w4.val = lo := by rw [hL4]; exact hw4_lo'
      have hw5_hi : w5.val = hi := by rw [hH5]; exact hw5_hi'
      obtain ⟨sB2, hsB01, hB2pc, _, hB2r0, _, hB2d⟩ := step_readSlot (s := sB) inp slX1Tag (by decide) 0
        (by decide : (0 : Fin 16) ≠ 15) w3 (by rw [hBd]; exact hX1T)
        (placedSlice_fetch_at hMid2Pl (k := 2) rfl (by rw [hBpc]; omega))
        (placedSlice_fetch_at hMid2Pl (k := 3) rfl (by rw [hBpc]; omega))
        (prog_pc_lt _ (by rw [hBpc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
        (prog_pc_lt _ (by rw [hBpc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      rw [hBpc] at hB2pc
      have hsB2 := step_imm16 inp (s := sB2) (placedSlice_fetch_at hMid2Pl (k := 4) rfl (by rw [hB2pc]; omega))
        (prog_pc_lt _ (by rw [hB2pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      let sB3 := putReg rfl sB2 6 (oneW hTag)
      have hB3pc : sB3.pc = pc5b + 121 + sz := by simp [sB3, putReg_pc, hB2pc]; omega
      have hgeB3 : ¬ ((reg sB3 0).val < (reg sB3 6).val) := by
        rw [putReg_eq_other sB2 (by decide : (0 : Fin 16) ≠ 6), putReg_eq_same sB2 6 _, hB2r0, hw3_1]
        change ¬ (1 < 1); omega
      have hsB3 := step_branchLt16 inp (s := sB3) (placedSlice_fetch_at hMid2Pl (k := 5) rfl (by rw [hB3pc]; omega)) (by
        change (if (reg sB3 0).val < (reg sB3 6).val then failPC hI hTag else pc5b + 122 + sz) < _
        rw [ite_eq_right hgeB3]; exact prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      let sB4 := { sB3 with pc := if (reg sB3 0).val < (reg sB3 6).val then failPC hI hTag else pc5b + 122 + sz }
      have hB4pc : sB4.pc = pc5b + 122 + sz := by
        change (if (reg sB3 0).val < (reg sB3 6).val then _ else _) = _; exact ite_eq_right hgeB3
      have hB4d : sB4.data = s62.data := by change sB3.data = s62.data; rw [putReg_data, hB2d, hBd]
      obtain ⟨owLo, howLo, howLoVal⟩ := hOrigAt ⟨lo, hLoLt⟩ w4 hw4_lo
      obtain ⟨owHi, howHi, howHiVal⟩ := hOrigAt ⟨hi, hHiLt⟩ w5 hw5_hi
      obtain ⟨ebW, hebW, hebVal⟩ := hEntryAt bDense bW hbVal
      obtain ⟨sbW, hsbW, hsbVal⟩ := hStopAt bDense bW hbVal
      obtain ⟨exLo, hexLo, hexLoVal⟩ := hEntryAt (inv.slots.read ⟨lo, hLoLt⟩) owLo howLoVal
      obtain ⟨exHi, hexHi, hexHiVal⟩ := hEntryAt (inv.slots.read ⟨hi, hHiLt⟩) owHi howHiVal
      obtain ⟨sB5, kB1, hkB1, hsB5, hB5pc, hB5d⟩ := exec_origAncestorStep hI hWork hTag
        (pc5b + 122 + sz) (pc5b + 148 + sz)
        (prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
        (by unfold okPC pc6; dsimp only [pc5b, sz]; omega)
        slX1Lo slBDense (by decide) (by decide)
        (placedSlice_fetch_at hMid2Pl (k := 6) rfl (by omega)) (placedSlice_fetch_at hMid2Pl (k := 7) rfl (by omega))
        (placedSlice_fetch_at hMid2Pl (k := 8) rfl (by omega)) (placedSlice_fetch_at hMid2Pl (k := 9) rfl (by omega))
        (placedSlice_fetch_at hMid2Pl (k := 10) rfl (by omega)) (placedSlice_fetch_at hMid2Pl (k := 11) rfl (by omega))
        (placedSlice_fetch_at hMid2Pl (k := 12) rfl (by omega)) (placedSlice_fetch_at hMid2Pl (k := 13) rfl (by omega))
        (by rw [show pc5b + 122 + sz + 8 = pc5b + 130 + sz by omega, show pc5b + 122 + sz + 24 = pc5b + 146 + sz by omega]; exact hAnc3Pl)
        (placedSlice_fetch_at hMid3Pl (k := 0) rfl (by omega)) (placedSlice_fetch_at hMid3Pl (k := 1) rfl (by omega))
        sB4 hB4pc w4 bW origPtrW owLo entryBaseW stopBaseW ebW exLo sbW
        (by rw [hB4d]; exact hX1L) (by rw [hB4d]; exact h62BD)
        hOrigHdr? howLo hEH? hSH? hebW hexLo hsbW
      by_cases hc1 : ebW.val ≤ exLo.val ∧ exLo.val < sbW.val
      · have hB5pc' : sB5.pc = pc5b + 148 + sz := by rw [hB5pc, ite_eq_left hc1]
        obtain ⟨sB6, kB2, hkB2, hsB6, hB6pc, _⟩ := exec_origAncestorStep hI hWork hTag
          (pc5b + 148 + sz) (failPC hI hTag)
          (failPC_lt hI hWork hTag)
          (by unfold okPC pc6; dsimp only [pc5b, sz]; omega)
          slX1Hi slBDense (by decide) (by decide)
          (placedSlice_fetch_at hMid3Pl (k := 2) rfl (by omega)) (placedSlice_fetch_at hMid3Pl (k := 3) rfl (by omega))
          (placedSlice_fetch_at hMid3Pl (k := 4) rfl (by omega)) (placedSlice_fetch_at hMid3Pl (k := 5) rfl (by omega))
          (placedSlice_fetch_at hMid3Pl (k := 6) rfl (by omega)) (placedSlice_fetch_at hMid3Pl (k := 7) rfl (by omega))
          (placedSlice_fetch_at hMid3Pl (k := 8) rfl (by omega)) (placedSlice_fetch_at hMid3Pl (k := 9) rfl (by omega))
          (by rw [show pc5b + 148 + sz + 8 = pc5b + 156 + sz by omega, show pc5b + 148 + sz + 24 = pc5b + 172 + sz by omega]; exact hAnc4Pl)
          (placedSlice_fetch_at hTail2Pl (k := 0) rfl (by omega)) (placedSlice_fetch_at hTail2Pl (k := 1) rfl (by omega))
          sB5 hB5pc' w5 bW origPtrW owHi entryBaseW stopBaseW ebW exHi sbW
          (by rw [hB5d, hB4d]; exact hX1H) (by rw [hB5d, hB4d]; exact h62BD)
          hOrigHdr? howHi hEH? hSH? hebW hexHi hsbW
        have hSurvEq : spanSurvives q.reader.entry q.reader.stop bDense sp.2 = !(ebW.val ≤ exHi.val ∧ exHi.val < sbW.val) := by
          rw [hSpBSome]
          have hc1' : q.reader.entry bDense ≤ q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) ∧
              q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) < q.reader.stop bDense := by
            rw [← hebVal, ← hexLoVal, ← hsbVal]; exact hc1
          by_cases h1 : ebW.val ≤ exHi.val <;> by_cases h2 : exHi.val < sbW.val
          · have hc2' : q.reader.entry bDense ≤ q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) ∧
                q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) < q.reader.stop bDense := by
              rw [← hebVal, ← hexHiVal, ← hsbVal]; exact ⟨h1, h2⟩
            simp [spanSurvives, hc1', hc2', h1, h2]
          · have hc2' : ¬ (q.reader.entry bDense ≤ q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) ∧
                q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) < q.reader.stop bDense) := by
              rw [← hebVal, ← hexHiVal, ← hsbVal]; omega
            simp [spanSurvives, hc1', hc2', h1, h2]
          · have hc2' : ¬ (q.reader.entry bDense ≤ q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) ∧
                q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) < q.reader.stop bDense) := by
              rw [← hebVal, ← hexHiVal, ← hsbVal]; omega
            simp [spanSurvives, hc1', hc2', h1, h2]
          · have hc2' : ¬ (q.reader.entry bDense ≤ q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) ∧
                q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) < q.reader.stop bDense) := by
              rw [← hebVal, ← hexHiVal, ← hsbVal]; omega
            simp [spanSurvives, hc1', hc2', h1, h2]
        refine ⟨sB6, 4 + kB1 + kB2, by omega,
          ((hsB01.append (Steps.cons hsB2 (Steps.cons hsB3 (Steps.zero sB4)))).append hsB5).append hsB6, ?_⟩
        rw [hB6pc, hSurvEq]
        by_cases hc2 : ebW.val ≤ exHi.val ∧ exHi.val < sbW.val <;> simp [hc2]
      · have hB5pc' : sB5.pc = okPC hI hTag := by rw [hB5pc, ite_eq_right hc1]
        have hSurvT : spanSurvives q.reader.entry q.reader.stop bDense sp.2 = true := by
          rw [hSpBSome]
          have hc1' : ¬ (q.reader.entry bDense ≤ q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) ∧
              q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) < q.reader.stop bDense) := by
            rw [← hebVal, ← hexLoVal, ← hsbVal]; exact hc1
          simp [spanSurvives, hc1']
        refine ⟨sB5, 4 + kB1, by omega,
          (hsB01.append (Steps.cons hsB2 (Steps.cons hsB3 (Steps.zero sB4)))).append hsB5, ?_⟩
        rw [hB5pc', hSurvT]; rfl
  -- Now run Half A at s62 (pc5b + 62 + sz), then either exit okPC or enter hHalfB
  obtain ⟨hxA, hT0, hL1, hH2⟩ := hIVa
  cases hIvACase : ivA with
  | empty =>
    have hSpANone : sp.1 = none := by rw [hSpA, hIvACase]; rfl
    have hSurvAF : spanSurvives q.reader.entry q.reader.stop aDense sp.1 = false := by rw [hSpANone]; rfl
    have hw0z : w0.val = 0 := by
      dsimp only [ivA, res] at hIvACase
      rw [hT0]; exact intervalCodec_empty_tag hTag _ hxA hIvACase
    obtain ⟨s64, hs62_63, h64pc, _, h64r0, _, h64d⟩ := step_readSlot (s := s62) inp slX0Tag (by decide) 0
      (by decide : (0 : Fin 16) ≠ 15) w0 hX0T
      (placedSlice_fetch_at hBig52Pl (k := 40) rfl (by rw [h62pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 41) rfl (by rw [h62pc]; omega))
      (prog_pc_lt _ (by rw [h62pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h62pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h62pc] at h64pc
    have hs64 := step_imm16 inp (s := s64) (placedSlice_fetch_at hBig52Pl (k := 42) rfl (by rw [h64pc]; omega))
      (prog_pc_lt _ (by rw [h64pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    let s65 := putReg rfl s64 6 (oneW hTag)
    have h65pc : s65.pc = pc5b + 65 + sz := by simp [s65, putReg_pc, h64pc]; omega
    have hlt65 : (reg s65 0).val < (reg s65 6).val := by
      rw [putReg_eq_other s64 (by decide : (0 : Fin 16) ≠ 6), putReg_eq_same s64 6 _, h64r0, hw0z]
      exact (by decide : 0 < 1)
    have hs65 := step_branchLt16 inp (s := s65) (placedSlice_fetch_at hBig52Pl (k := 43) rfl (by rw [h65pc]; omega)) (by
      change (if (reg s65 0).val < (reg s65 6).val then pc5b + 118 + sz else pc5b + 66 + sz) < _
      rw [ite_eq_left hlt65]; exact prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    let sB := { s65 with pc := if (reg s65 0).val < (reg s65 6).val then pc5b + 118 + sz else pc5b + 66 + sz }
    have hBpc : sB.pc = pc5b + 118 + sz := by
      change (if (reg s65 0).val < (reg s65 6).val then _ else _) = _; exact ite_eq_left hlt65
    have hBd : sB.data = s62.data := by change s65.data = s62.data; rw [putReg_data, h64d]
    obtain ⟨t, kB, hkB, hpB, htpc⟩ := hHalfB sB hBpc hBd
    refine ⟨t, k1 + 4 + kB, by omega,
      (hp0_62.append (hs62_63.append (Steps.cons hs64 (Steps.cons hs65 (Steps.zero sB))))).append hpB, ?_⟩
    simp [htpc, hSurvAF]
  | span lo hi =>
    obtain ⟨hLoLt, hHiLt⟩ := hIvABound lo hi hIvACase
    have hSpASome : sp.1 = some (inv.slots.read ⟨lo, hLoLt⟩, inv.slots.read ⟨hi, hHiLt⟩) := by
      rw [hSpA, hIvACase]
      unfold ExitSpanBridge.toSpan ExitSpanBridge.readEntry
      simp [dite_eq_left hLoLt, dite_eq_left hHiLt]
    have hIvACase' : (if P.fst < P.snd then (ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
        ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).x0
        else (ExitMap.JumpMapRoute.StoredExit.PriorBase.run I R wFit.tags prior
        ⟨y.val, by rw [hPriorSz]; exact y.isLt⟩ (wCols.labelAt y.val) (ExitMap.JumpMapRoute.StoredExit.depthAt I R aNode)).x1) =
        .span lo hi := by
      dsimp only [ivA, res] at hIvACase; exact hIvACase
    obtain ⟨hw0_1', hw1_lo', hw2_hi'⟩ := intervalCodec_span_vals hTag _ hxA hIvACase'
    have hw0_1 : w0.val = 1 := by rw [hT0]; exact hw0_1'
    have hw1_lo : w1.val = lo := by rw [hL1]; exact hw1_lo'
    have hw2_hi : w2.val = hi := by rw [hH2]; exact hw2_hi'
    obtain ⟨s64, hs62_63, h64pc, _, h64r0, _, h64d⟩ := step_readSlot (s := s62) inp slX0Tag (by decide) 0
      (by decide : (0 : Fin 16) ≠ 15) w0 hX0T
      (placedSlice_fetch_at hBig52Pl (k := 40) rfl (by rw [h62pc]; omega))
      (placedSlice_fetch_at hBig52Pl (k := 41) rfl (by rw [h62pc]; omega))
      (prog_pc_lt _ (by rw [h62pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (prog_pc_lt _ (by rw [h62pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    rw [h62pc] at h64pc
    have hs64 := step_imm16 inp (s := s64) (placedSlice_fetch_at hBig52Pl (k := 42) rfl (by rw [h64pc]; omega))
      (prog_pc_lt _ (by rw [h64pc]; unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    let s65 := putReg rfl s64 6 (oneW hTag)
    have h65pc : s65.pc = pc5b + 65 + sz := by simp [s65, putReg_pc, h64pc]; omega
    have hge65 : ¬ ((reg s65 0).val < (reg s65 6).val) := by
      rw [putReg_eq_other s64 (by decide : (0 : Fin 16) ≠ 6), putReg_eq_same s64 6 _, h64r0, hw0_1]
      change ¬ (1 < 1); omega
    have hs65 := step_branchLt16 inp (s := s65) (placedSlice_fetch_at hBig52Pl (k := 43) rfl (by rw [h65pc]; omega)) (by
      change (if (reg s65 0).val < (reg s65 6).val then pc5b + 118 + sz else pc5b + 66 + sz) < _
      rw [ite_eq_right hge65]; exact prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
    let s66 := { s65 with pc := if (reg s65 0).val < (reg s65 6).val then pc5b + 118 + sz else pc5b + 66 + sz }
    have h66pc : s66.pc = pc5b + 66 + sz := by
      change (if (reg s65 0).val < (reg s65 6).val then _ else _) = _; exact ite_eq_right hge65
    have h66d : s66.data = s62.data := by change s65.data = s62.data; rw [putReg_data, h64d]
    obtain ⟨owLo, howLo, howLoVal⟩ := hOrigAt ⟨lo, hLoLt⟩ w1 hw1_lo
    obtain ⟨owHi, howHi, howHiVal⟩ := hOrigAt ⟨hi, hHiLt⟩ w2 hw2_hi
    obtain ⟨ebW, hebW, hebVal⟩ := hEntryAt aDense aW haVal
    obtain ⟨sbW, hsbW, hsbVal⟩ := hStopAt aDense aW haVal
    obtain ⟨exLo, hexLo, hexLoVal⟩ := hEntryAt (inv.slots.read ⟨lo, hLoLt⟩) owLo howLoVal
    obtain ⟨exHi, hexHi, hexHiVal⟩ := hEntryAt (inv.slots.read ⟨hi, hHiLt⟩) owHi howHiVal
    obtain ⟨s92, kA1, hkA1, hs92, h92pc, h92d⟩ := exec_origAncestorStep hI hWork hTag
      (pc5b + 66 + sz) (pc5b + 92 + sz)
      (prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
      (by unfold okPC pc6; dsimp only [pc5b, sz]; omega)
      slX0Lo slADense (by decide) (by decide)
      (placedSlice_fetch_at hBig52Pl (k := 44) rfl (by omega)) (placedSlice_fetch_at hBig52Pl (k := 45) rfl (by omega))
      (placedSlice_fetch_at hBig52Pl (k := 46) rfl (by omega)) (placedSlice_fetch_at hBig52Pl (k := 47) rfl (by omega))
      (placedSlice_fetch_at hBig52Pl (k := 48) rfl (by omega)) (placedSlice_fetch_at hBig52Pl (k := 49) rfl (by omega))
      (placedSlice_fetch_at hBig52Pl (k := 50) rfl (by omega)) (placedSlice_fetch_at hBig52Pl (k := 51) rfl (by omega))
      (by rw [show pc5b + 66 + sz + 8 = pc5b + 74 + sz by omega, show pc5b + 66 + sz + 24 = pc5b + 90 + sz by omega]; exact hAnc1Pl)
      (placedSlice_fetch_at hMid1Pl (k := 0) rfl (by omega)) (placedSlice_fetch_at hMid1Pl (k := 1) rfl (by omega))
      s66 h66pc w1 aW origPtrW owLo entryBaseW stopBaseW ebW exLo sbW
      (by rw [h66d]; exact hX0L) (by rw [h66d]; exact h62AD)
      hOrigHdr? howLo hEH? hSH? hebW hexLo hsbW
    by_cases hc1 : ebW.val ≤ exLo.val ∧ exLo.val < sbW.val
    · have h92pc' : s92.pc = pc5b + 92 + sz := by rw [h92pc, ite_eq_left hc1]
      obtain ⟨s118, kA2, hkA2, hs118, h118pc, h118d⟩ := exec_origAncestorStep hI hWork hTag
        (pc5b + 92 + sz) (pc5b + 118 + sz)
        (prog_pc_lt _ (by unfold okPC pc6; dsimp only [pc5b, sz]; omega))
        (by unfold okPC pc6; dsimp only [pc5b, sz]; omega)
        slX0Hi slADense (by decide) (by decide)
        (placedSlice_fetch_at hMid1Pl (k := 2) rfl (by omega)) (placedSlice_fetch_at hMid1Pl (k := 3) rfl (by omega))
        (placedSlice_fetch_at hMid1Pl (k := 4) rfl (by omega)) (placedSlice_fetch_at hMid1Pl (k := 5) rfl (by omega))
        (placedSlice_fetch_at hMid1Pl (k := 6) rfl (by omega)) (placedSlice_fetch_at hMid1Pl (k := 7) rfl (by omega))
        (placedSlice_fetch_at hMid1Pl (k := 8) rfl (by omega)) (placedSlice_fetch_at hMid1Pl (k := 9) rfl (by omega))
        (by rw [show pc5b + 92 + sz + 8 = pc5b + 100 + sz by omega, show pc5b + 92 + sz + 24 = pc5b + 116 + sz by omega]; exact hAnc2Pl)
        (placedSlice_fetch_at hMid2Pl (k := 0) rfl (by omega)) (placedSlice_fetch_at hMid2Pl (k := 1) rfl (by omega))
        s92 h92pc' w2 aW origPtrW owHi entryBaseW stopBaseW ebW exHi sbW
        (by rw [h92d, h66d]; exact hX0H) (by rw [h92d, h66d]; exact h62AD)
        hOrigHdr? howHi hEH? hSH? hebW hexHi hsbW
      by_cases hc2 : ebW.val ≤ exHi.val ∧ exHi.val < sbW.val
      · have h118pc' : s118.pc = pc5b + 118 + sz := by rw [h118pc, ite_eq_left hc2]
        have h118d' : s118.data = s62.data := by rw [h118d, h92d, h66d]
        have hSurvAF : spanSurvives q.reader.entry q.reader.stop aDense sp.1 = false := by
          rw [hSpASome]
          have hc1' : q.reader.entry aDense ≤ q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) ∧
              q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) < q.reader.stop aDense := by
            rw [← hebVal, ← hexLoVal, ← hsbVal]; exact hc1
          have hc2' : q.reader.entry aDense ≤ q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) ∧
              q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) < q.reader.stop aDense := by
            rw [← hebVal, ← hexHiVal, ← hsbVal]; exact hc2
          simp [spanSurvives, hc1', hc2']
        obtain ⟨t, kB, hkB, hpB, htpc⟩ := hHalfB s118 h118pc' h118d'
        refine ⟨t, k1 + 4 + kA1 + kA2 + kB, by omega,
          (((hp0_62.append (hs62_63.append (Steps.cons hs64 (Steps.cons hs65 (Steps.zero s66))))).append hs92).append hs118).append hpB, ?_⟩
        simp [htpc, hSurvAF]
      · have h118pc' : s118.pc = okPC hI hTag := by rw [h118pc, ite_eq_right hc2]
        have hSurvAT : spanSurvives q.reader.entry q.reader.stop aDense sp.1 = true := by
          rw [hSpASome]
          have hc2' : ¬ (q.reader.entry aDense ≤ q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) ∧
              q.reader.entry (inv.slots.read ⟨hi, hHiLt⟩) < q.reader.stop aDense) := by
            rw [← hebVal, ← hexHiVal, ← hsbVal]; exact hc2
          simp [spanSurvives, hc2']
        refine ⟨s118, k1 + 4 + kA1 + kA2, by omega,
          ((hp0_62.append (hs62_63.append (Steps.cons hs64 (Steps.cons hs65 (Steps.zero s66))))).append hs92).append hs118, ?_⟩
        simp [h118pc', hSurvAT]
    · have h92pc' : s92.pc = okPC hI hTag := by rw [h92pc, ite_eq_right hc1]
      have hSurvAT : spanSurvives q.reader.entry q.reader.stop aDense sp.1 = true := by
        rw [hSpASome]
        have hc1' : ¬ (q.reader.entry aDense ≤ q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) ∧
            q.reader.entry (inv.slots.read ⟨lo, hLoLt⟩) < q.reader.stop aDense) := by
          rw [← hebVal, ← hexLoVal, ← hsbVal]; exact hc1
        simp [spanSurvives, hc1']
      refine ⟨s92, k1 + 4 + kA1, by omega,
        (hp0_62.append (hs62_63.append (Steps.cons hs64 (Steps.cons hs65 (Steps.zero s66))))).append hs92, ?_⟩
      simp [h92pc', hSurvAT]

private theorem exec_blkTail {bits : Nat} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc6 hI hTag)
    (w xW entryBaseW stopBaseW entryW entryX stopW : Word bits)
    (hr1 : reg s 1 = w) (hx : s.data[slXDense]? = some xW)
    (hEH : I[hdrEntry]? = some entryBaseW)
    (hSH : I[hdrStop]? = some stopBaseW)
    (hEW : I[entryBaseW.val + w.val]? = some entryW)
    (hEX : I[entryBaseW.val + xW.val]? = some entryX)
    (hSW : I[stopBaseW.val + w.val]? = some stopW) :
    ∃ t k, k ≤ 18 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
      t.pc = (if entryW.val ≤ entryX.val ∧ entryX.val < stopW.val
              then failPC hI hTag else okPC hI hTag) := by
  let prog := oracleQueryProgram hI hWork hTag
  let inp : Input (codeLayout bits I.size hI hWork) := ⟨I, rfl⟩
  have h6 := place_blk6 hI hWork hTag
  have hPre : PlacedSlice
      (#[.imm 15 (slotW hWork slXDense (by decide)), .loadData 2 15] :
        Program (codeLayout bits I.size hI hWork)) prog (pc6 hI hTag) := by
    unfold blkTail at h6; exact placedSlice_append_left (placedSlice_append_left h6)
  have hAnc : PlacedSlice
      (ancestorCheckBlock (L := codeLayout bits I.size hI hWork) rfl
        (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
        (zeroW bits) (oneW hTag) 1 2 (pc6 hI hTag + 2) (pc6 hI hTag + 18))
      prog (pc6 hI hTag + 2) := by
    unfold blkTail at h6; exact placedSlice_append_right_at (placedSlice_append_left h6) rfl rfl
  have hPost := blkTail_post_placed hI hWork hTag
  obtain ⟨s1, hs1, h1pc, h1r, h1r2, _, h1d⟩ := step_readSlot inp slXDense (by decide) 2 (by decide) xW hx
    (by rw [hpc]; exact placedSlice_fetch hPre (k := 0) rfl)
    (by rw [hpc]; exact placedSlice_fetch hPre (k := 1) rfl)
    (prog_pc_lt _ (by rw [hpc]; unfold okPC; omega))
    (prog_pc_lt _ (by rw [hpc]; unfold okPC; omega))
  rw [hpc] at h1pc
  have h1r1 : reg s1 1 = w := (h1r 1 (by decide) (by decide)).trans hr1
  obtain ⟨s2, k2, hk2, hs2, h2pc, h2r0, _⟩ := ancestorCheckBlock_spec (h16 := rfl)
    (hdrW hWork hdrEntry (by decide)) (hdrW hWork hdrStop (by decide))
    (zeroW bits) (oneW hTag) rfl rfl 1 2 (by decide) (by decide) hAnc
    (prog_pc_lt _ (by unfold okPC; omega)) inp s1 h1pc hEH hSH
    (by rw [reg_r16, h1r1]; exact hEW) (by rw [reg_r16, h1r2]; exact hEX) (by rw [reg_r16, h1r1]; exact hSW)
  have hs3 := step_imm16 inp (by rw [h2pc]; exact placedSlice_fetch hPost (k := 0) rfl)
    (prog_pc_lt _ (by unfold okPC; rw [h2pc]; omega))
  let s3 := putReg (rfl : (codeLayout bits I.size hI hWork).registerCount = 16) s2 6 (oneW hTag)
  have h3pc : s3.pc = pc6 hI hTag + 19 := by rw [putReg_pc, h2pc]
  have h3r0 : (reg s3 0).val = if entryW.val ≤ entryX.val ∧ entryX.val < stopW.val then 1 else 0 := by
    rw [putReg_eq_other s2 (by decide : (0 : Fin 16) ≠ 6) _, ← reg_r16 s2 0]; exact h2r0
  have h3r6 : reg s3 6 = oneW hTag := putReg_eq_same s2 6 _
  have hs4 := step_branchLt16 inp (by rw [h3pc]; exact placedSlice_fetch hPost (k := 1) rfl) (by
      rw [h3r0, h3r6, oneW]
      by_cases hcond : entryW.val ≤ entryX.val ∧ entryX.val < stopW.val
      · simp [hcond, failPC_lt hI hWork hTag]
      · simp [hcond, okPC_lt hI hWork hTag])
  let s4 := { s3 with pc := if (reg s3 0).val < (reg s3 6).val then okPC hI hTag else failPC hI hTag }
  have h4pc : s4.pc = if entryW.val ≤ entryX.val ∧ entryX.val < stopW.val
      then failPC hI hTag else okPC hI hTag := by
    change (if (reg s3 0).val < (reg s3 6).val then _ else _) = _
    rw [h3r0, h3r6, oneW]
    by_cases hcond : entryW.val ≤ entryX.val ∧ entryX.val < stopW.val
    · simp [hcond]
    · simp [hcond]
  exact ⟨s4, 2 + k2 + 2, by omega,
    ((hs1.append hs2).append (Steps.cons hs3 (Steps.cons hs4 (Steps.zero s4)))), h4pc⟩

end PlacementAndBlocks

end FixedProgram

/-! ### 4. End-to-End Correctness & Resource Bounds (`oracleQueryProgram_spec`) -/

section EndToEndSpec

open PaperB.EX44.RetainedRouteProof.OriginalStaticConnector

theorem ValidSealedOracleIndex.tags_fit {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hVal : ValidSealedOracleIndex g r I) : TagsFit bits :=
  hVal.1

theorem ValidSealedOracleIndex.work_le {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hVal : ValidSealedOracleIndex g r I) : queryWorkCap ≤ 2 ^ bits :=
  hVal.2.1

theorem ValidSealedOracleIndex.vertexCount_lt {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hVal : ValidSealedOracleIndex g r I) : g.vertexCount < 2 ^ bits := by
  rcases hVal with ⟨_, _, _, _, _, _, _, _, _, _, _, _, Hdr, _⟩
  have hn := Hdr.hN
  cases h : I[hdrN]? with
  | none => simp [h] at hn
  | some w =>
    simp only [h, Option.map_some, Option.some.injEq] at hn
    rw [← hn]; exact w.isLt

theorem ValidSealedOracleIndex.vertexCount_le {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)} (hVal : ValidSealedOracleIndex g r I) : g.vertexCount ≤ 2 ^ bits :=
  Nat.le_of_lt hVal.vertexCount_lt

private theorem injective_fin_le :
    ∀ {m n : Nat} (f : Fin m → Fin n), Function.Injective f → m ≤ n
  | 0, _, _, _ => Nat.zero_le _
  | m + 1, 0, f, _ => Fin.elim0 (f ⟨0, Nat.zero_lt_succ m⟩)
  | m + 1, n + 1, f, hf => by
      let f0 := f ⟨0, Nat.zero_lt_succ m⟩
      let g : Fin m → Fin n := fun i =>
        let y := f ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        if hlt : y.val < f0.val then
          ⟨y.val, Nat.lt_of_lt_of_le hlt (Nat.le_of_lt_succ f0.isLt)⟩
        else
          ⟨y.val - 1, by
            have hne : y.val ≠ f0.val := fun he => by
              have hv := congrArg Fin.val (hf (Fin.ext he))
              dsimp at hv; omega
            have hy : y.val < n + 1 := y.isLt
            omega⟩
      have hg : Function.Injective g := by
        intro a b hab
        have hva : (g a).val = (g b).val := congrArg Fin.val hab
        let ya := f ⟨a.val + 1, Nat.succ_lt_succ a.isLt⟩
        let yb := f ⟨b.val + 1, Nat.succ_lt_succ b.isLt⟩
        have hna : ya.val ≠ f0.val := fun he => by
          have hv := congrArg Fin.val (hf (Fin.ext he)); dsimp at hv; omega
        have hnb : yb.val ≠ f0.val := fun he => by
          have hv := congrArg Fin.val (hf (Fin.ext he)); dsimp at hv; omega
        have hyEq : ya = yb := Fin.ext (by
          by_cases ha : ya.val < f0.val <;> by_cases hb : yb.val < f0.val <;>
            simp [g, ya, yb, ha, hb] at hva <;> omega)
        have hsucc := congrArg Fin.val (hf hyEq)
        exact Fin.ext (by dsimp at hsucc; omega)
      exact Nat.succ_le_succ (injective_fin_le g hg)

private theorem denseQuotient_vertexCount_le
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d : Fin q.count) :
    (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount ≤ q.count := by
  change rows.length d ≤ q.count
  let f : Fin (rows.length d) → Fin q.count := fun i =>
    match rows.key d i with
    | .inl _ => d
    | .inr c => c
  apply injective_fin_le f
  intro i j hij
  cases hi : rows.key d i with
  | inl di =>
    have hdi : di = d := ((rows.key_is_root_iff d di i).mp hi).2
    cases hj : rows.key d j with
    | inl dj =>
      have hdj : dj = d := ((rows.key_is_root_iff d dj j).mp hj).2
      apply rows.key_injective d
      rw [hi, hj, hdi, hdj]
    | inr cj =>
      have hmem : cj ∈ buckets.get d := (rows.occurs_iff d (.inr cj)).mp ⟨j, hj⟩
      have hne : cj ≠ d := by
        intro hcd
        have hnr := ((childOK d cj).mp hmem).1
        have hp := ((childOK d cj).mp hmem).2
        have hds := q.reader.input_ok.depth_step cj hnr
        rw [hp, hcd] at hds
        omega
      exfalso
      dsimp only [f] at hij
      rw [hi, hj] at hij
      exact hne hij.symm
  | inr ci =>
    have hmem : ci ∈ buckets.get d := (rows.occurs_iff d (.inr ci)).mp ⟨i, hi⟩
    have hne : ci ≠ d := by
      intro hcd
      have hnr := ((childOK d ci).mp hmem).1
      have hp := ((childOK d ci).mp hmem).2
      have hds := q.reader.input_ok.depth_step ci hnr
      rw [hp, hcd] at hds
      omega
    cases hj : rows.key d j with
    | inl dj =>
      exfalso
      dsimp only [f] at hij
      rw [hi, hj] at hij
      exact hne hij
    | inr cj =>
      dsimp only [f] at hij
      rw [hi, hj] at hij
      apply rows.key_injective d
      rw [hi, hj]
      exact congrArg Sum.inr hij

private theorem qSlot_root_eq_input_root {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (hr : g.InitiallyReachable r r) :
    q.slot r hr = q.input.root := by
  apply Classical.byContradiction
  intro hne
  have hds := q.reader.input_ok.depth_step (q.slot r hr) hne
  have hpar : q.ids.originals.read (q.input.parent.read (q.slot r hr)) = r := by
    rw [← q.parent_at_slot r hr]
    exact q.parentSpec.root
  have hslotEq : q.input.parent.read (q.slot r hr) = q.slot r hr := by
    apply Option.some.inj
    calc some (q.input.parent.read (q.slot r hr))
        = q.ids.find (q.ids.originals.read (q.input.parent.read (q.slot r hr))) :=
            (q.ids.slot_of_original (q.input.parent.read (q.slot r hr))).symm
      _ = q.ids.find r := by rw [hpar]
      _ = some (q.slot r hr) := q.find_slot r hr
  rw [hslotEq] at hds
  omega

private theorem exitSummary_span_lt (xs : List Nat) (N : Nat)
    (hxs : ∀ x ∈ xs, x < N) :
    (ExitSummary.summary xs = .empty) ∨
    ∃ lo hi, ExitSummary.summary xs = .span lo hi ∧ lo < N ∧ hi < N := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons x xs ih =>
    have hx : x < N := hxs x (by simp)
    have htail : ∀ z ∈ xs, z < N := fun z hz => hxs z (by simp [hz])
    rcases ih htail with he | ⟨a, b, hab, ha, hb⟩
    · right; refine ⟨x, x, ?_, hx, hx⟩
      simp [he, ExitSummary.singleton, ExitMap.Interval.join]
    · right; refine ⟨min x a, max x b, ?_, ?_, ?_⟩
      · simp [hab, ExitSummary.singleton, ExitMap.Interval.join]
      · omega
      · omega

private theorem exitSummary_span_bound (xs : List Nat) (N : Nat)
    (hxs : ∀ x ∈ xs, x < N) {lo hi : Nat}
    (h : ExitSummary.summary xs = .span lo hi) : lo < N ∧ hi < N := by
  rcases exitSummary_span_lt xs N hxs with he | ⟨a, b, hab, ha, hb⟩
  · rw [he] at h; cases h
  · rw [hab] at h; cases h; exact ⟨ha, hb⟩

private theorem originalRank_getD_lt {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r) (hq : 0 < q.count) (v : Fin g.vertexCount) :
    (OriginalEntryInverse.originalRank q v).getD 0 < q.count := by
  unfold OriginalEntryInverse.originalRank
  cases hf : q.ids.find v with
  | none => simpa using hq
  | some x =>
    simp only [Option.map_some, Option.getD_some]
    rw [← OriginalEntryInverse.entryRank_val q x]
    exact (OriginalEntryInverse.entryRank q x).isLt

private theorem L_ge_three_of_large {n m : Nat} (h3 : 3 ≤ m) (hmn : m ≤ n) :
    3 ≤ OracleContract.L n := by
  have hn : 3 ≤ n := Nat.le_trans h3 hmn
  have hlog : 2 ≤ Nat.log2 (n + 1) := by
    rw [Nat.le_log2 (by omega)]
    omega
  change 3 ≤ Nat.log2 (n + 1) + 1
  omega

private theorem nat_log2_mono {a b : Nat} (h : a ≤ b) : Nat.log2 a ≤ Nat.log2 b := by
  by_cases hb0 : b = 0
  · have ha0 : a = 0 := by omega
    subst ha0; subst hb0; exact Nat.le_refl 0
  · by_cases ha0 : a = 0
    · subst ha0
      have h0 : Nat.log2 0 = 0 := by decide
      rw [h0]; exact Nat.zero_le _
    · rw [Nat.le_log2 hb0]
      exact Nat.le_trans ((Nat.le_log2 ha0).mp (Nat.le_refl _)) h

private theorem dict_log_le_L
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (hqLe : q.count ≤ g.vertexCount) (d : Fin q.count)
    {large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount}
    {pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK d)}
    {dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d))}
    {sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount}
    {rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d) → Nat}
    (ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large) :
    Nat.log2 ((ofOrderedReader ordRes).dict.size + 1) + 1 ≤ OracleContract.L g.vertexCount := by
  have hd : (ofOrderedReader ordRes).dict.size ≤
      (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount :=
    ofOrderedReader_dict_size_le ordRes
  have hv : (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount ≤ q.count :=
    denseQuotient_vertexCount_le progress injRank q originalRows hRows rows childOK d
  have hle : (ofOrderedReader ordRes).dict.size ≤ g.vertexCount := Nat.le_trans hd (Nat.le_trans hv hqLe)
  exact Nat.succ_le_succ (nat_log2_mono (Nat.succ_le_succ hle))

private theorem observe_of_exit_pc {bits : Nat} (I : Array (Word bits))
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    (params : SealedQuery.Params bits) (fuel k : Nat) (b : Bool)
    {s : State (codeLayout bits I.size hI hWork)}
    (hk : k + 50 ≤ fuel)
    (hs : Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k
      ((oracleQueryPhase I hI hWork hTag).initialState params) s)
    (hpc : s.pc = if b then okPC hI hTag else failPC hI hTag) :
    ∃ o : SealedQuery.Observation,
      (oracleQueryPhase I hI hWork hTag).observe params fuel = some o ∧
      o.operations ≤ fuel ∧
      o.words = I.size + queryWorkCap + 16 ∧
      o.answer = b := by
  let p := oracleQueryPhase I hI hWork hTag
  have hk1 : k + 1 + 1 ≤ fuel := by omega
  by_cases hb : b = true
  · have hpc' : s.pc = okPC hI hTag := by rw [hpc, ite_eq_left hb]
    obtain ⟨u, hsu, huHalt, hu0⟩ := halt_okPC (hCap := hI) (hWork := hWork) (hTag := hTag) ⟨I, rfl⟩ hpc'
    have hrun : RamProgram.run p.code p.input fuel (p.initialState params) = some ⟨u, k + 2⟩ :=
      (Steps.halt_run_iff (hs.append hsu) huHalt).mpr ⟨hk1, rfl⟩
    have hobs : ∃ o : SealedQuery.Observation, p.observe params fuel = some o ∧
        o.answer = decide ((reg u 0).val ≠ 0) := by
      rw [SealedQueryR.Phase.observe, hrun]
      exact ⟨_, rfl, rfl⟩
    obtain ⟨o, hobsEq, hoAns⟩ := hobs
    refine ⟨o, hobsEq, ?_, ?_, ?_⟩
    · obtain ⟨res, hres, hEx, _, _, _, hOps, _, _⟩ := SealedQueryR.Phase.observe_counts p params fuel hobsEq
      rw [hrun] at hres
      cases Option.some.inj hres
      have hw : p.workCap = queryWorkCap := rfl
      have hq32 : queryWorkCap = 32 := rfl
      rw [hOps, hEx]
      dsimp only
      rw [hw, hq32]
      omega
    · obtain ⟨_, _, _, _, _, _, _, hWords, _⟩ := SealedQueryR.Phase.observe_counts p params fuel hobsEq
      exact hWords
    · rw [hoAns, hu0, oneW, hb]
      simp
  · have hbf : b = false := Bool.eq_false_iff.mpr hb
    have hpc' : s.pc = failPC hI hTag := by rw [hpc, ite_eq_right hb]
    obtain ⟨u, hsu, huHalt, hu0⟩ := halt_failPC (hCap := hI) (hWork := hWork) (hTag := hTag) ⟨I, rfl⟩ hpc'
    have hrun : RamProgram.run p.code p.input fuel (p.initialState params) = some ⟨u, k + 2⟩ :=
      (Steps.halt_run_iff (hs.append hsu) huHalt).mpr ⟨hk1, rfl⟩
    have hobs : ∃ o : SealedQuery.Observation, p.observe params fuel = some o ∧
        o.answer = decide ((reg u 0).val ≠ 0) := by
      rw [SealedQueryR.Phase.observe, hrun]
      exact ⟨_, rfl, rfl⟩
    obtain ⟨o, hobsEq, hoAns⟩ := hobs
    refine ⟨o, hobsEq, ?_, ?_, ?_⟩
    · obtain ⟨res, hres, hEx, _, _, _, hOps, _, _⟩ := SealedQueryR.Phase.observe_counts p params fuel hobsEq
      rw [hrun] at hres
      cases Option.some.inj hres
      have hw : p.workCap = queryWorkCap := rfl
      have hq32 : queryWorkCap = 32 := rfl
      rw [hOps, hEx]
      dsimp only
      rw [hw, hq32]
      omega
    · obtain ⟨_, _, _, _, _, _, _, hWords, _⟩ := SealedQueryR.Phase.observe_counts p params fuel hobsEq
      exact hWords
    · rw [hoAns, hu0, zeroW, hbf]
      rfl

private theorem natSliceAt_get {bits : Nat} {I : Array (Word bits)}
    {base n : Nat} {f : Nat → Nat} (h : NatSliceAt I base n f)
    {i : Nat} (hi : i < n) :
    ∃ w, I[base + i]? = some w ∧ w.val = f i := by
  have hlt : base + i < I.size := by have := h.1; omega
  refine ⟨I[base + i]'hlt, getElem?_pos I _ hlt, ?_⟩
  have hm := h.2 i hi
  rw [getElem?_pos I _ hlt, Option.map_some] at hm
  exact Option.some.inj hm

private theorem natSliceAt_fin {bits n : Nat} {I : Array (Word bits)} {base : Nat}
    {f : Fin n → Nat} (h : NatSliceAt I base n (fun i => if hi : i < n then f ⟨i, hi⟩ else 0))
    (i : Fin n) :
    ∃ w, I[base + i.val]? = some w ∧ w.val = f i := by
  obtain ⟨w, hw, hwV⟩ := natSliceAt_get h i.isLt
  rw [dite_eq_left i.isLt] at hwV
  exact ⟨w, hw, hwV⟩

private theorem isAncestor_eq_decide {N : Nat} {x : PackedStaticLayout.Input N}
    (r : StaticTreeReader.Reader x) (a v : Fin N) :
    r.isAncestor a v = decide (r.entry a ≤ r.entry v ∧ r.entry v < r.stop a) := by
  have h := (r.isAncestor_exact a v).trans (r.ancestor_iff_interval a v)
  by_cases ha : r.isAncestor a v = true
  · rw [ha, decide_eq_true (h.mp ha)]
  · have haf : r.isAncestor a v = false := Bool.eq_false_iff.mpr ha
    rw [haf, decide_eq_false (fun hi => ha (h.mpr hi))]

private structure UnpackedLargeOwner
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (I : Array (Word bits))
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {d : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d)
    (large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount) where
  pD : ForestDictionary.Rows (denseQuotient progress injRank q originalRows hRows rows childOK d)
  dataD : Array (Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d))
  sizeD : dataD.size = (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
  rankD : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d) → Nat
  ordRes : PaperB.OrderedReaderResult pD dataD sizeD rankD large
  wCols : WordColumns bits
  endpoints : Nat
  R : Region bits I.size
  F : JumpForest
  ref : Nat → ExitMap.CheckedFold.Stored
  wFit : Width bits (max R.slots endpoints)
  ok : Occupied I R F ref wFit
  prior : Array (Option Values)
  hb : BaseBound (max R.slots endpoints) prior
  B : BaseView prior.size I.size
  hPlaced : Placed wFit prior hb I B
  hDictSlice : SliceAt I rec.dictPtr wCols.dictionary
  hRep : FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordRes)
  hBackFst : SliceAt I rec.backFstPtr wCols.back.tagAndFirst
  hBackSnd : SliceAt I rec.backSndPtr wCols.back.second
  hLabels : SliceAt I rec.labelsPtr wCols.labels
  hFEntry : SliceAt I rec.fEntryPtr wCols.entry
  hFStop : SliceAt I rec.fStopPtr wCols.stop
  hLabelsSz : wCols.labels.size =
    (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
  hEntryStopSz : wCols.entry.size = wCols.stop.size
  hBackSz : wCols.back.tagAndFirst.size = wCols.back.second.size
  hKnownEq : ∀ a v, wCols.known a v = (ofOrderedReader ordRes).known a v
  hBackRead : ∀ j (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d)),
    wCols.back.read j = some (encodeBackPair (some P)) ↔
      (ofOrderedReader ordRes).back[j]? = some (some P)
  hVIdx : ∀ v : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d),
    (orderedConfig pD large).vertexIndex v = v.val
  hLabBounds : ∀ y : Fin (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount,
    wCols.labelAt y.val < F.size ∧ wCols.labelAt y.val < wCols.entry.size
  hHitBounds : ∀ (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d)),
    P.fst < P.snd → ∀ aNode : Nat, checkedHit ordRes P = some aNode →
      aNode < wCols.entry.size ∧ aNode < wCols.stop.size ∧
      aNode < F.size ∧ aNode < wCols.back.tagAndFirst.size ∧
      aNode < wCols.back.second.size
  hPriorSz : prior.size =
    (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
  hRBase : R.base.val = rec.exitStoredPtr
  hBStart : B.start = rec.exitPriorPtr
  hDepthContig : ∀ x : Fin R.slots, (R.depthAddr x).val = rec.exitDepthPtr + x.val
  hExitSpec : ∀ (P : CutPair (denseQuotient progress injRank q originalRows hRows rows childOK d)),
    P.fst < P.snd → ∀ aNode : Nat, checkedHit ordRes P = some aNode →
    ∀ y : Vertex (denseQuotient progress injRank q originalRows hRows rows childOK d),
    (denseQuotient progress injRank q originalRows hRows rows childOK d).ProperLoss P y →
      let u := wCols.labelAt y.val
      let dDepth := depthAt I R aNode
      (foldStored I R wFit.tags u dDepth).steps ≤ 3 * ceilLog2 (g.vertexCount + 2) ∧
      ∀ hPrior : y.val < prior.size,
        (PriorBase.run I R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x0 =
          ExitSummary.summary
            ((lemma22ExitTails (denseQuotient progress injRank q originalRows hRows rows childOK d) P P.fst y).map
              (fun v => (OriginalEntryInverse.originalRank q v).getD 0)) ∧
        (PriorBase.run I R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x1 =
          ExitSummary.summary
            ((lemma22ExitTails (denseQuotient progress injRank q originalRows hRows rows childOK d) P P.snd y).map
              (fun v => (OriginalEntryInverse.originalRank q v).getD 0))

private theorem large_spec_packed
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {progress : ∀ i j, g.HasArc i j → rank i < rank j}
    {injRank : ∀ ⦃i j⦄, rank i = rank j → i = j}
    {q : OriginalReader g r}
    {originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count))}
    {hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1}
    {buckets : ForestLayout.ChildLists q.count}
    {rows : Layout buckets}
    {childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d}
    {I : Array (Word bits)}
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {d : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d)
    (large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount) :
    Nonempty (UnpackedLargeOwner progress injRank q originalRows hRows rows childOK I rec large) := by
  rcases rec.large_spec large with
    ⟨pD, dataD, sizeD, rankD, ordRes, wCols, endpoints, R, F, ref, wFit, ok, prior, hb, B, hPlaced,
      hDictSlice, hRep, hBackFst, hBackSnd, hLabels, hFEntry, hFStop, hLabelsSz, hEntryStopSz,
      hBackSz, hKnownEq, hBackRead, hVIdx, hLabBounds, hHitBounds, hPriorSz, hRBase, hBStart,
      hDepthContig, hExitSpec⟩
  exact ⟨{
    pD := pD, dataD := dataD, sizeD := sizeD, rankD := rankD, ordRes := ordRes,
    wCols := wCols, endpoints := endpoints, R := R, F := F, ref := ref, wFit := wFit,
    ok := ok, prior := prior, hb := hb, B := B, hPlaced := hPlaced,
    hDictSlice := hDictSlice, hRep := hRep, hBackFst := hBackFst, hBackSnd := hBackSnd,
    hLabels := hLabels, hFEntry := hFEntry, hFStop := hFStop, hLabelsSz := hLabelsSz,
    hEntryStopSz := hEntryStopSz, hBackSz := hBackSz, hKnownEq := hKnownEq,
    hBackRead := hBackRead, hVIdx := hVIdx, hLabBounds := hLabBounds, hHitBounds := hHitBounds,
    hPriorSz := hPriorSz, hRBase := hRBase, hBStart := hBStart,
    hDepthContig := hDepthContig, hExitSpec := hExitSpec }⟩

private noncomputable def unpackLargeOwner
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {progress : ∀ i j, g.HasArc i j → rank i < rank j}
    {injRank : ∀ ⦃i j⦄, rank i = rank j → i = j}
    {q : OriginalReader g r}
    {originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count))}
    {hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1}
    {buckets : ForestLayout.ChildLists q.count}
    {rows : Layout buckets}
    {childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d}
    {I : Array (Word bits)}
    {Hdr : StaticHeaderSpec I g.vertexCount q.count}
    {d : Fin q.count}
    (rec : SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d)
    (large : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount) :
    UnpackedLargeOwner progress injRank q originalRows hRows rows childOK I rec large :=
  Classical.choice (large_spec_packed rec large)

private def encodeOwnerKey (qCount cap : Nat)
    (d : Fin qCount) (aNode : Nat) : Fin (qCount * (cap + 1) + 1) :=
  let stride := cap + 1
  if ha : aNode < stride then
    ⟨d.val * stride + aNode, by
      calc d.val * stride + aNode
          < d.val * stride + stride := Nat.add_lt_add_left ha (d.val * stride)
        _ = (d.val + 1) * stride := (Nat.succ_mul d.val stride).symm
        _ ≤ qCount * stride := Nat.mul_le_mul_right stride d.isLt
        _ < qCount * stride + 1 := Nat.lt_succ_self _⟩
  else ⟨0, Nat.zero_lt_succ _⟩

private def dOfOwnerKey {qCount cap : Nat} (hq : 0 < qCount)
    (key : Fin (qCount * (cap + 1) + 1)) : Fin qCount :=
  let stride := cap + 1
  if hk : key.val < qCount * stride then
    ⟨key.val / stride, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq hk (Nat.mul_comm qCount stride))⟩
  else ⟨0, hq⟩

private def nodeOfOwnerKey {qCount cap : Nat} (key : Fin (qCount * (cap + 1) + 1)) : Nat :=
  key.val % (cap + 1)

private theorem dOfOwnerKey_encode {qCount cap : Nat} (hq : 0 < qCount)
    (d : Fin qCount) (aNode : Nat) (ha : aNode < cap + 1) :
    dOfOwnerKey hq (encodeOwnerKey qCount cap d aNode) = d := by
  let stride := cap + 1
  have hlt : d.val * stride + aNode < qCount * stride := by
    calc d.val * stride + aNode
        < d.val * stride + stride := Nat.add_lt_add_left ha (d.val * stride)
      _ = (d.val + 1) * stride := (Nat.succ_mul d.val stride).symm
      _ ≤ qCount * stride := Nat.mul_le_mul_right stride d.isLt
  unfold dOfOwnerKey encodeOwnerKey
  rw [dite_eq_left ha]
  dsimp only
  rw [dite_eq_left hlt]
  apply Fin.ext
  change (d.val * stride + aNode) / stride = d.val
  rw [Nat.mul_comm d.val stride, Nat.mul_add_div (Nat.zero_lt_succ cap), Nat.div_eq_of_lt ha, Nat.add_zero]

private theorem nodeOfOwnerKey_encode {qCount cap : Nat}
    (d : Fin qCount) (aNode : Nat) (ha : aNode < cap + 1) :
    nodeOfOwnerKey (encodeOwnerKey qCount cap d aNode) = aNode := by
  let stride := cap + 1
  unfold nodeOfOwnerKey encodeOwnerKey
  rw [dite_eq_left ha]
  change (d.val * stride + aNode) % stride = aNode
  rw [Nat.mul_comm d.val stride, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

private noncomputable def buildSealedEvaluator
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount}
    {I : Array (Word bits)}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (Hdr : StaticHeaderSpec I g.vertexCount q.count)
    (recs : ∀ d : Fin q.count,
      SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d) :
    DenseOwnerExitEvaluator progress injRank q originalRows hRows rows childOK
      (q.count * (I.size + 1) + 1) 0 0 where
  pairKey d P :=
    if hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount then
      let U := unpackLargeOwner (recs d) hLarge
      ⟨(LocalOrderedChecked.query U.ordRes P).map fun h =>
          ⟨encodeOwnerKey q.count I.size d h.node, h.orientation⟩,
        0, Nat.le_refl 0⟩
    else ⟨none, 0, Nat.le_refl 0⟩
  pairMember key y :=
    let d := dOfOwnerKey Hdr.q_pos key
    let aNode := nodeOfOwnerKey key
    if hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount then
      if hy : q.input.parent.read y = d ∧ y ≠ d then
        let U := unpackLargeOwner (recs d) hLarge
        let yd := denseChild q rows childOK d y hy.1 hy.2
        ⟨(ofOrderedReader U.ordRes).known aNode yd.val, 0, Nat.le_refl 0⟩
      else ⟨false, 0, Nat.le_refl 0⟩
    else ⟨false, 0, Nat.le_refl 0⟩
  exitIntervals key y :=
    let d := dOfOwnerKey Hdr.q_pos key
    let aNode := nodeOfOwnerKey key
    if hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount then
      if hy : q.input.parent.read y = d ∧ y ≠ d then
        let U := unpackLargeOwner (recs d) hLarge
        let yd := denseChild q rows childOK d y hy.1 hy.2
        let hPrior : yd.val < U.prior.size := by rw [U.hPriorSz]; exact yd.isLt
        let res := PriorBase.run I U.R U.wFit.tags U.prior ⟨yd.val, hPrior⟩
          (U.wCols.labelAt yd.val) (depthAt I U.R aNode)
        ⟨(res.x0, res.x1), 0, Nat.le_refl 0⟩
      else ⟨(.empty, .empty), 0, Nat.le_refl 0⟩
    else ⟨(.empty, .empty), 0, Nat.le_refl 0⟩
  missing_spec d P hNone y := by
    by_cases hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
    · dsimp only at hNone
      rw [dite_eq_left hLarge] at hNone
      let U := unpackLargeOwner (recs d) hLarge
      change Option.map (fun h => ({ key := encodeOwnerKey q.count I.size d h.node, orientation := h.orientation } :
          EX44.Hit (q.count * (I.size + 1) + 1))) (LocalOrderedChecked.query U.ordRes P) = none at hNone
      have hqNone : LocalOrderedChecked.query U.ordRes P = none := by
        cases hq : LocalOrderedChecked.query U.ordRes P with
        | none => rfl
        | some hit => rw [hq] at hNone; cases hNone
      exact LocalOrderedChecked.not_properLoss_of_query_none U.ordRes P y hqNone
    · exact (SmallQuotient.cutPair_impossible_of_small (by omega) P).elim
  hit_orientation d P hit hSome := by
    by_cases hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
    · dsimp only at hSome
      rw [dite_eq_left hLarge] at hSome
      let U := unpackLargeOwner (recs d) hLarge
      change Option.map (fun h => ({ key := encodeOwnerKey q.count I.size d h.node, orientation := h.orientation } :
          EX44.Hit (q.count * (I.size + 1) + 1))) (LocalOrderedChecked.query U.ordRes P) = some hit at hSome
      cases hq : LocalOrderedChecked.query U.ordRes P with
      | none => rw [hq] at hSome; cases hSome
      | some cHit =>
        rw [hq] at hSome
        simp only [Option.map_some, Option.some.injEq] at hSome
        have hc : (⟨encodeOwnerKey q.count I.size d cHit.node, cHit.orientation⟩ :
            EX44.Hit (q.count * (I.size + 1) + 1)) = hit := hSome
        rw [← hc]
        exact ((LocalOrderedChecked.query_some_iff U.ordRes P cHit).mp hq).2
    · dsimp only at hSome; rw [dite_eq_right hLarge] at hSome; cases hSome
  member_spec d P hit hSome y hyP hyNe := by
    by_cases hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
    · dsimp only at hSome
      rw [dite_eq_left hLarge] at hSome
      let U := unpackLargeOwner (recs d) hLarge
      change Option.map (fun h => ({ key := encodeOwnerKey q.count I.size d h.node, orientation := h.orientation } :
          EX44.Hit (q.count * (I.size + 1) + 1))) (LocalOrderedChecked.query U.ordRes P) = some hit at hSome
      cases hq : LocalOrderedChecked.query U.ordRes P with
      | none => rw [hq] at hSome; cases hSome
      | some cHit =>
        rw [hq] at hSome
        simp only [Option.map_some, Option.some.injEq] at hSome
        have hc : encodeOwnerKey q.count I.size d cHit.node = hit.key :=
          congrArg EX44.Hit.key hSome
        have hHitC : checkedHit U.ordRes P.canonical = some cHit.node :=
          ((LocalOrderedChecked.query_some_iff U.ordRes P cHit).mp hq).1
        have haBound := U.hHitBounds P.canonical (CutPair.canonical_lt P) cHit.node hHitC
        have hEntSz : U.wCols.entry.size ≤ I.size := by have := U.hFEntry.1; omega
        have haStride : cHit.node < I.size + 1 := by omega
        have hdK : dOfOwnerKey Hdr.q_pos hit.key = d := by
          rw [← hc]; exact dOfOwnerKey_encode Hdr.q_pos d cHit.node haStride
        have hnK : nodeOfOwnerKey hit.key = cHit.node := by
          rw [← hc]; exact nodeOfOwnerKey_encode d cHit.node haStride
        let yd := denseChild q rows childOK d y hyP hyNe
        have hyD : q.input.parent.read y = d ∧ y ≠ d := ⟨hyP, hyNe⟩
        have hMemCongr : ∀ (d' : Fin q.count) (n' : Nat), d' = d → n' = cHit.node →
            ((if hLarge' : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d').vertexCount then
                if hy' : q.input.parent.read y = d' ∧ y ≠ d' then
                  let U' := unpackLargeOwner (recs d') hLarge'
                  let yd' := denseChild q rows childOK d' y hy'.1 hy'.2
                  ⟨(ofOrderedReader U'.ordRes).known n' yd'.val, 0, Nat.le_refl 0⟩
                else ⟨false, 0, Nat.le_refl 0⟩
              else ⟨false, 0, Nat.le_refl 0⟩ : EX44.Sample 0 Bool).value) =
              (ofOrderedReader U.ordRes).known cHit.node ((orderedConfig U.pD hLarge).vertexIndex yd) := by
          intro d' n' hdEq hnEq
          subst hdEq hnEq
          dsimp only
          rw [dite_eq_left hLarge, dite_eq_left hyD, U.hVIdx yd]
        rw [hMemCongr (dOfOwnerKey Hdr.q_pos hit.key) (nodeOfOwnerKey hit.key) hdK hnK]
        exact LocalOrderedChecked.known_true_iff_properLoss_of_query_some U.ordRes P yd cHit hq
    · dsimp only at hSome; rw [dite_eq_right hLarge] at hSome; cases hSome
  extrema_spec d P hit hSome y hyP hyNe hm := by
    by_cases hLarge : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d).vertexCount
    · dsimp only at hSome
      rw [dite_eq_left hLarge] at hSome
      let U := unpackLargeOwner (recs d) hLarge
      change Option.map (fun h => ({ key := encodeOwnerKey q.count I.size d h.node, orientation := h.orientation } :
          EX44.Hit (q.count * (I.size + 1) + 1))) (LocalOrderedChecked.query U.ordRes P) = some hit at hSome
      cases hq : LocalOrderedChecked.query U.ordRes P with
      | none => rw [hq] at hSome; cases hSome
      | some cHit =>
        rw [hq] at hSome
        simp only [Option.map_some, Option.some.injEq] at hSome
        have hc : encodeOwnerKey q.count I.size d cHit.node = hit.key :=
          congrArg EX44.Hit.key hSome
        have hHitC : checkedHit U.ordRes P.canonical = some cHit.node :=
          ((LocalOrderedChecked.query_some_iff U.ordRes P cHit).mp hq).1
        have haBound := U.hHitBounds P.canonical (CutPair.canonical_lt P) cHit.node hHitC
        have hEntSz : U.wCols.entry.size ≤ I.size := by have := U.hFEntry.1; omega
        have haStride : cHit.node < I.size + 1 := by omega
        have hdK : dOfOwnerKey Hdr.q_pos hit.key = d := by
          rw [← hc]; exact dOfOwnerKey_encode Hdr.q_pos d cHit.node haStride
        have hnK : nodeOfOwnerKey hit.key = cHit.node := by
          rw [← hc]; exact nodeOfOwnerKey_encode d cHit.node haStride
        let yd := denseChild q rows childOK d y hyP hyNe
        have hyD : q.input.parent.read y = d ∧ y ≠ d := ⟨hyP, hyNe⟩
        have hMemCongr : ∀ (d' : Fin q.count) (n' : Nat), d' = d → n' = cHit.node →
            ((if hLarge' : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d').vertexCount then
                if hy' : q.input.parent.read y = d' ∧ y ≠ d' then
                  let U' := unpackLargeOwner (recs d') hLarge'
                  let yd' := denseChild q rows childOK d' y hy'.1 hy'.2
                  ⟨(ofOrderedReader U'.ordRes).known n' yd'.val, 0, Nat.le_refl 0⟩
                else ⟨false, 0, Nat.le_refl 0⟩
              else ⟨false, 0, Nat.le_refl 0⟩ : EX44.Sample 0 Bool).value) =
              (ofOrderedReader U.ordRes).known cHit.node ((orderedConfig U.pD hLarge).vertexIndex yd) := by
          intro d' n' hdEq hnEq
          subst hdEq hnEq
          dsimp only
          rw [dite_eq_left hLarge, dite_eq_left hyD, U.hVIdx yd]
        have hMemTrue : (ofOrderedReader U.ordRes).known cHit.node ((orderedConfig U.pD hLarge).vertexIndex yd) = true := by
          rw [← hMemCongr (dOfOwnerKey Hdr.q_pos hit.key) (nodeOfOwnerKey hit.key) hdK hnK]
          exact hm
        have hLoss : (denseQuotient progress injRank q originalRows hRows rows childOK d).ProperLoss P yd :=
          (LocalOrderedChecked.known_true_iff_properLoss_of_query_some U.ordRes P yd cHit hq).mp hMemTrue
        have hLossCan := (LocalOrderedChecked.properLoss_canonical_iff P yd).mpr hLoss
        have hPrior : yd.val < U.prior.size := by rw [U.hPriorSz]; exact yd.isLt
        have hEx := (U.hExitSpec P.canonical (CutPair.canonical_lt P) cHit.node hHitC yd hLossCan).2 hPrior
        have hExCongr : ∀ (d' : Fin q.count) (n' : Nat), d' = d → n' = cHit.node →
            ((if hLarge' : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d').vertexCount then
                if hy' : q.input.parent.read y = d' ∧ y ≠ d' then
                  let U' := unpackLargeOwner (recs d') hLarge'
                  let yd' := denseChild q rows childOK d' y hy'.1 hy'.2
                  let hP' : yd'.val < U'.prior.size := by rw [U'.hPriorSz]; exact yd'.isLt
                  let res := PriorBase.run I U'.R U'.wFit.tags U'.prior ⟨yd'.val, hP'⟩
                    (U'.wCols.labelAt yd'.val) (depthAt I U'.R n')
                  ⟨(res.x0, res.x1), 0, Nat.le_refl 0⟩
                else ⟨(.empty, .empty), 0, Nat.le_refl 0⟩
              else ⟨(.empty, .empty), 0, Nat.le_refl 0⟩ : EX44.Sample 0 (ExitMap.Interval × ExitMap.Interval)).value) =
              (let res := PriorBase.run I U.R U.wFit.tags U.prior ⟨yd.val, hPrior⟩
                 (U.wCols.labelAt yd.val) (depthAt I U.R cHit.node)
               (res.x0, res.x1)) := by
          intro d' n' hdEq hnEq
          subst hdEq hnEq
          dsimp only
          rw [dite_eq_left hLarge, dite_eq_left hyD]
        rw [hExCongr (dOfOwnerKey Hdr.q_pos hit.key) (nodeOfOwnerKey hit.key) hdK hnK]
        exact hEx
    · dsimp only at hSome; rw [dite_eq_right hLarge] at hSome; cases hSome

private theorem denseChild_ne_root'
    {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (d c : Fin q.count) (hp : q.input.parent.read c = d) (hne : c ≠ d) :
    denseChild q rows childOK d c hp hne ≠
      (denseQuotient progress injRank q originalRows hRows rows childOK d).root := by
  intro hEq
  have hEq' : denseChild q rows childOK d c hp hne =
      ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) (denseChild q rows childOK d c hp hne).isLt⟩ :=
    Fin.ext (congrArg Fin.val hEq)
  have hKey := congrArg (rows.key d) hEq'
  have hL : rows.key d (denseChild q rows childOK d c hp hne) = .inr c :=
    congrArg Subtype.val (rows.decode_encode d _)
  rw [hL, rows.key_zero d] at hKey
  cases hKey

private theorem denseChild_ne'
    {g : Digraph} {r : Fin g.vertexCount}
    (q : OriginalReader g r)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    {d c₁ c₂ : Fin q.count}
    (hp₁ : q.input.parent.read c₁ = d) (hne₁ : c₁ ≠ d)
    (hp₂ : q.input.parent.read c₂ = d) (hne₂ : c₂ ≠ d)
    (hDiff : c₁ ≠ c₂) :
    denseChild q rows childOK d c₁ hp₁ hne₁ ≠ denseChild q rows childOK d c₂ hp₂ hne₂ := by
  intro hEq
  apply hDiff
  have h1 : rows.key d (denseChild q rows childOK d c₁ hp₁ hne₁) = .inr c₁ :=
    congrArg Subtype.val (rows.decode_encode d _)
  have h2 : rows.key d (denseChild q rows childOK d c₂ hp₂ hne₂) = .inr c₂ :=
    congrArg Subtype.val (rows.decode_encode d _)
  exact Sum.inr.inj (h1.symm.trans ((congrArg (rows.key d) hEq).trans h2))

private theorem runThirdExits
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (inv : OriginalEntryInverse.Index q)
    (Hdr : StaticHeaderSpec I g.vertexCount q.count)
    (hqLe : q.count ≤ g.vertexCount)
    (hOrigOfEntry : NatSliceAt I Hdr.origOfEntryBase q.count
      (fun rk => if hr : rk < q.count then (inv.slots.read ⟨rk, hr⟩).val else 0))
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (hStop : NatSliceAt I Hdr.stopBase q.count
      (fun d => if hd : d < q.count then q.reader.stop ⟨d, hd⟩ else 0))
    (recs : ∀ d : Fin q.count,
      SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d)
    (dDense aDense bDense uDense vDense yDense : Fin q.count)
    (hpU : q.input.parent.read uDense = dDense) (hneU : uDense ≠ dDense)
    (hpV : q.input.parent.read vDense = dDense) (hneV : vDense ≠ dDense)
    (hpY : q.input.parent.read yDense = dDense) (hneY : yDense ≠ dDense)
    (huv : uDense ≠ vDense)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc5a)
    (hDataSz : s.data.size = queryWorkCap)
    (hAD : (s.data[slADense]?).map Fin.val = some aDense.val)
    (hBD : (s.data[slBDense]?).map Fin.val = some bDense.val)
    (hCD : (s.data[slD]?).map Fin.val = some dDense.val)
    (hCUL : (s.data[slULocal]?).map Fin.val = some (denseChild q rows childOK dDense uDense hpU hneU).val)
    (hCVL : (s.data[slVLocal]?).map Fin.val = some (denseChild q rows childOK dDense vDense hpV hneV).val)
    (hCYL : (s.data[slYLocal]?).map Fin.val = some (denseChild q rows childOK dDense yDense hpY hneY).val) :
    let eval := buildSealedEvaluator progress injRank q originalRows hRows rows childOK Hdr recs
    let R := thirdInstalledRuntime q (eval.toBaseRuntime inv 0 (Nat.le_refl 0)) 0 (Nat.le_refl 0)
    ∃ (t : State (codeLayout bits I.size hI hWork)) (k : Nat),
      k ≤ 321 * OracleContract.L g.vertexCount + 349 ∧
      Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
      t.pc = if ((EX44.answer ((EX44.routeThird dDense uDense vDense aDense bDense yDense).run R).value).run R).value
             then okPC hI hTag else failPC hI hTag := by
  intro eval R
  let Dq := denseQuotient progress injRank q originalRows hRows rows childOK dDense
  let uLoc := denseChild q rows childOK dDense uDense hpU hneU
  let vLoc := denseChild q rows childOK dDense vDense hpV hneV
  let yLoc := denseChild q rows childOK dDense yDense hpY hneY
  let P : CutPair Dq :=
    { fst := uLoc
      snd := vLoc
      fst_ne_root := denseChild_ne_root' progress injRank q originalRows hRows rows childOK dDense uDense hpU hneU
      snd_ne_root := denseChild_ne_root' progress injRank q originalRows hRows rows childOK dDense vDense hpV hneV
      ne := denseChild_ne' q rows childOK hpU hneU hpV hneV huv }
  have hLarge : 3 ≤ Dq.vertexCount := by
    apply Classical.byContradiction
    intro hlt
    exact SmallQuotient.cutPair_impossible_of_small (by omega) P
  have hL3 : 3 ≤ OracleContract.L g.vertexCount :=
    L_ge_three_of_large hLarge
      (Nat.le_trans (denseQuotient_vertexCount_le progress injRank q originalRows hRows rows childOK dDense) hqLe)
  let U := unpackLargeOwner (recs dDense) hLarge
  have hLogLe : Nat.log2 ((ofOrderedReader U.ordRes).dict.size + 1) + 1 ≤ OracleContract.L g.vertexCount :=
    dict_log_le_L progress injRank q originalRows hRows rows childOK hqLe dDense U.ordRes
  obtain ⟨hMiss, hNonmem, hExit⟩ := exec_blkPairAndKnown hI hWork hTag progress injRank q originalRows hRows rows
    childOK (recs dDense) U.ordRes U.wCols U.hDictSlice U.hRep U.hBackFst U.hBackSnd U.hLabels
    U.hFEntry U.hFStop U.hLabelsSz U.hEntryStopSz U.hBackSz U.hKnownEq U.hBackRead
    (fun y => (U.hLabBounds y).2)
    (fun P0 hP0 aN haN => let hb := U.hHitBounds P0 hP0 aN haN; ⟨hb.1, hb.2.1⟩)
    P yLoc s hpc hDataSz hCD hCUL hCVL hCYL
  have hPairKeyVal : (R.fetch (.key dDense uDense vDense)).value =
      (LocalOrderedChecked.query U.ordRes P).map fun h =>
        ⟨encodeOwnerKey q.count I.size dDense h.node, h.orientation⟩ := by
    change ((eval.toBaseRuntime inv 0 (Nat.le_refl 0)).pairKey dDense uDense vDense).value = _
    have huP : q.input.parent.read uDense = dDense ∧ uDense ≠ dDense := ⟨hpU, hneU⟩
    have hvP : q.input.parent.read vDense = dDense ∧ vDense ≠ dDense := ⟨hpV, hneV⟩
    dsimp only [DenseOwnerExitEvaluator.toBaseRuntime, eval, buildSealedEvaluator]
    rw [dite_eq_left huP, dite_eq_left hvP, dite_eq_left huv, dite_eq_left hLarge]
  cases hHit : checkedHit U.ordRes P.canonical with
  | none =>
    have hqNone : LocalOrderedChecked.query U.ordRes P = none :=
      (LocalOrderedChecked.query_none_iff U.ordRes P).mpr hHit
    have hSurv : ((EX44.answer ((EX44.routeThird dDense uDense vDense aDense bDense yDense).run R).value).run R).value = true := by
      dsimp only [EX44.routeThird, EX44.Plan.fast_value]
      rw [hPairKeyVal, hqNone]
      rfl
    obtain ⟨t, k, hk, hst, htpc⟩ := hMiss hHit
    refine ⟨t, k, by omega, hst, by rw [htpc, hSurv]; rfl⟩
  | some aNode =>
    let cHit : LocalOrderedChecked.CheckedNode := ⟨aNode, LocalOrderedChecked.suppliedOrientation P⟩
    have hqSome : LocalOrderedChecked.query U.ordRes P = some cHit :=
      (LocalOrderedChecked.query_some_iff U.ordRes P cHit).mpr ⟨hHit, rfl⟩
    have haB := U.hHitBounds P.canonical (CutPair.canonical_lt P) aNode hHit
    have hEntSz : U.wCols.entry.size ≤ I.size := by have := U.hFEntry.1; omega
    have haStride : aNode < I.size + 1 := by omega
    have hdK : dOfOwnerKey Hdr.q_pos (encodeOwnerKey q.count I.size dDense aNode) = dDense :=
      dOfOwnerKey_encode Hdr.q_pos dDense aNode haStride
    have hnK : nodeOfOwnerKey (encodeOwnerKey q.count I.size dDense aNode) = aNode :=
      nodeOfOwnerKey_encode dDense aNode haStride
    have hMemVal : (R.fetch (.member (encodeOwnerKey q.count I.size dDense aNode) yDense)).value =
        (ofOrderedReader U.ordRes).known aNode yLoc.val := by
      change (eval.pairMember (encodeOwnerKey q.count I.size dDense aNode) yDense).value = _
      have hyD : q.input.parent.read yDense = dDense ∧ yDense ≠ dDense := ⟨hpY, hneY⟩
      have hCong : ∀ (d' : Fin q.count) (n' : Nat), d' = dDense → n' = aNode →
          ((if hLarge' : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d').vertexCount then
              if hy' : q.input.parent.read yDense = d' ∧ yDense ≠ d' then
                let U' := unpackLargeOwner (recs d') hLarge'
                let yd' := denseChild q rows childOK d' yDense hy'.1 hy'.2
                ⟨(ofOrderedReader U'.ordRes).known n' yd'.val, 0, Nat.le_refl 0⟩
              else ⟨false, 0, Nat.le_refl 0⟩
            else ⟨false, 0, Nat.le_refl 0⟩ : EX44.Sample 0 Bool).value) =
            (ofOrderedReader U.ordRes).known aNode yLoc.val := by
        intro d' n' hdEq hnEq
        subst hdEq hnEq
        dsimp only
        rw [dite_eq_left hLarge, dite_eq_left hyD]
      exact hCong (dOfOwnerKey Hdr.q_pos (encodeOwnerKey q.count I.size dDense aNode))
        (nodeOfOwnerKey (encodeOwnerKey q.count I.size dDense aNode)) hdK hnK
    cases hKn : (ofOrderedReader U.ordRes).known aNode yLoc.val with
    | false =>
      have hSurv : ((EX44.answer ((EX44.routeThird dDense uDense vDense aDense bDense yDense).run R).value).run R).value = true := by
        dsimp only [EX44.routeThird, EX44.Plan.fast_value]
        rw [hPairKeyVal, hqSome]
        dsimp only [Option.map_some, EX44.Plan.fast_value]
        rw [hMemVal, hKn]
        rfl
      obtain ⟨t, k, hk, hst, htpc⟩ := hNonmem aNode hHit hKn
      refine ⟨t, k, by omega, hst, by rw [htpc, hSurv]; rfl⟩
    | true =>
      obtain ⟨s5b, k5a, hk5a, hs5a, h5bpc, h5bDsz, h5bFrame, h5bDesc, h5bSw, h5bHit⟩ :=
        hExit aNode hHit hKn
      have h5bY : (s5b.data[slYLocal]?).map Fin.val = some yLoc.val := by
        rw [h5bFrame slYLocal (by decide)]; exact hCYL
      have h5bAD : (s5b.data[slADense]?).map Fin.val = some aDense.val := by
        rw [h5bFrame slADense (by decide)]; exact hAD
      have h5bBD : (s5b.data[slBDense]?).map Fin.val = some bDense.val := by
        rw [h5bFrame slBDense (by decide)]; exact hBD
      have hPriorY : yLoc.val < U.prior.size := by rw [U.hPriorSz]; exact yLoc.isLt
      have hLoss : Dq.ProperLoss P yLoc :=
        (LocalOrderedChecked.known_true_iff_properLoss_of_query_some U.ordRes P yLoc cHit hqSome).mp (by
          rw [U.hVIdx yLoc]; exact hKn)
      have hLossCan := (LocalOrderedChecked.properLoss_canonical_iff P yLoc).mpr hLoss
      have hFoldSpec := U.hExitSpec P.canonical (CutPair.canonical_lt P) aNode hHit yLoc hLossCan
      have hStepsBound : (foldStored I U.R U.wFit.tags (U.wCols.labelAt yLoc.val) (depthAt I U.R aNode)).steps ≤
          3 * OracleContract.L g.vertexCount := by
        have hc := ExitActualContract.ceilLog2_add_two_le_L g.vertexCount
        exact Nat.le_trans hFoldSpec.1 (Nat.mul_le_mul_left 3 hc)
      have hExt := hFoldSpec.2 hPriorY
      have hX0B : ∀ lo hi, (PriorBase.run I U.R U.wFit.tags U.prior ⟨yLoc.val, hPriorY⟩
          (U.wCols.labelAt yLoc.val) (depthAt I U.R aNode)).x0 = .span lo hi → lo < q.count ∧ hi < q.count := by
        intro lo hi hx
        rw [hExt.1] at hx
        exact exitSummary_span_bound _ q.count (fun rk hrk => by
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hrk
          exact originalRank_getD_lt q Hdr.q_pos v) hx
      have hX1B : ∀ lo hi, (PriorBase.run I U.R U.wFit.tags U.prior ⟨yLoc.val, hPriorY⟩
          (U.wCols.labelAt yLoc.val) (depthAt I U.R aNode)).x1 = .span lo hi → lo < q.count ∧ hi < q.count := by
        intro lo hi hx
        rw [hExt.2] at hx
        exact exitSummary_span_bound _ q.count (fun rk hrk => by
          obtain ⟨v, _, rfl⟩ := List.mem_map.mp hrk
          exact originalRank_getD_lt q Hdr.q_pos v) hx
      obtain ⟨t, k5b, hk5b, hs5b, htpc⟩ := exec_blkExitTest hI hWork hTag progress injRank q originalRows hRows
        rows childOK (recs dDense) U.ordRes U.wCols U.ok U.prior U.hb U.B U.hPlaced U.hLabels
        U.hLabelsSz (fun y => (U.hLabBounds y).1) U.hPriorSz U.hRBase U.hBStart U.hDepthContig inv
        hOrigOfEntry hEntry hStop P yLoc aNode haB.2.2.1 aDense bDense s5b h5bpc h5bDsz
        h5bDesc h5bSw h5bHit h5bY h5bAD h5bBD hX0B hX1B
      let res := PriorBase.run I U.R U.wFit.tags U.prior ⟨yLoc.val, hPriorY⟩
        (U.wCols.labelAt yLoc.val) (depthAt I U.R aNode)
      let sp0 := ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) res.x0
      let sp1 := ExitSpanBridge.toSpan (ExitSpanBridge.readEntry inv.slots.read some) res.x1
      let sp := if P.fst < P.snd then (sp0, sp1) else (sp1, sp0)
      have hExVal : (R.exitExtrema (encodeOwnerKey q.count I.size dDense aNode) yDense).value =
          (sp0, sp1) := by
        change (eval.exitExtrema inv (encodeOwnerKey q.count I.size dDense aNode) yDense).value = _
        have hyD : q.input.parent.read yDense = dDense ∧ yDense ≠ dDense := ⟨hpY, hneY⟩
        have hExCong : ∀ (d' : Fin q.count) (n' : Nat), d' = dDense → n' = aNode →
            ((let x01 := (if hLarge' : 3 ≤ (denseQuotient progress injRank q originalRows hRows rows childOK d').vertexCount then
                  if hy' : q.input.parent.read yDense = d' ∧ yDense ≠ d' then
                    let U' := unpackLargeOwner (recs d') hLarge'
                    let yd' := denseChild q rows childOK d' yDense hy'.1 hy'.2
                    let hP' : yd'.val < U'.prior.size := by rw [U'.hPriorSz]; exact yd'.isLt
                    let r' := PriorBase.run I U'.R U'.wFit.tags U'.prior ⟨yd'.val, hP'⟩
                      (U'.wCols.labelAt yd'.val) (depthAt I U'.R n')
                    ⟨(r'.x0, r'.x1), 0, Nat.le_refl 0⟩
                  else ⟨(.empty, .empty), 0, Nat.le_refl 0⟩
                else ⟨(.empty, .empty), 0, Nat.le_refl 0⟩ : EX44.Sample 0 (ExitMap.Interval × ExitMap.Interval)).value
              let read := ExitSpanBridge.readEntry inv.slots.read some
              (ExitSpanBridge.toSpan read x01.1, ExitSpanBridge.toSpan read x01.2)) = (sp0, sp1)) := by
          intro d' n' hdEq hnEq
          subst hdEq hnEq
          dsimp only
          rw [dite_eq_left hLarge, dite_eq_left hyD]
        exact hExCong (dOfOwnerKey Hdr.q_pos (encodeOwnerKey q.count I.size dDense aNode))
          (nodeOfOwnerKey (encodeOwnerKey q.count I.size dDense aNode)) hdK hnK
      have hOrd : (LocalOrderedChecked.suppliedOrientation P).order (sp0, sp1) = sp := by
        dsimp only [LocalOrderedChecked.suppliedOrientation, sp]
        by_cases hlt : P.fst < P.snd
        · simp [hlt, EX44.Orientation.order]
        · simp [hlt, EX44.Orientation.order]
      have hSpanEq : ∀ {f s : Nat} (a : Fin q.count) (sp' : EX44.Span q.count)
          (next : Bool → EX44.Plan g.vertexCount q.count (q.count * (I.size + 1) + 1) Bool f s),
          ((EX44.testSpan a sp' next).run R).value =
            ((next (spanSurvives q.reader.entry q.reader.stop a sp')).run R).value := by
        intro f s a sp' next
        cases sp' with
        | none => rfl
        | some lh =>
          rcases lh with ⟨lo, hi⟩
          simp only [EX44.testSpan, EX44.Plan.fast_value, spanSurvives]
          have hAnc1 : (R.fetch (.ancestor a lo)).value =
              decide (q.reader.entry a ≤ q.reader.entry lo ∧ q.reader.entry lo < q.reader.stop a) := by
            change q.reader.isAncestor a lo = _; exact isAncestor_eq_decide q.reader a lo
          have hAnc2 : (R.fetch (.ancestor a hi)).value =
              decide (q.reader.entry a ≤ q.reader.entry hi ∧ q.reader.entry hi < q.reader.stop a) := by
            change q.reader.isAncestor a hi = _; exact isAncestor_eq_decide q.reader a hi
          rw [hAnc1, hAnc2]
          by_cases h1 : q.reader.entry a ≤ q.reader.entry lo ∧ q.reader.entry lo < q.reader.stop a <;>
            by_cases h2 : q.reader.entry a ≤ q.reader.entry hi ∧ q.reader.entry hi < q.reader.stop a <;>
            simp [h1, h2]
      have hSurv : ((EX44.answer ((EX44.routeThird dDense uDense vDense aDense bDense yDense).run R).value).run R).value =
          (spanSurvives q.reader.entry q.reader.stop aDense sp.1 ||
           spanSurvives q.reader.entry q.reader.stop bDense sp.2) := by
        dsimp only [EX44.routeThird, EX44.Plan.fast_value]
        rw [hPairKeyVal, hqSome]
        dsimp only [Option.map_some, EX44.Plan.fast_value]
        rw [hMemVal, hKn]
        rw [ite_eq_left rfl, EX44.Plan.stop_value]
        dsimp only [EX44.answer]
        rw [EX44.Plan.extrema_value, hExVal, hOrd, hSpanEq, hSpanEq]
        rfl
      refine ⟨t, k5a + k5b, by omega, hs5a.append hs5b, ?_⟩
      rw [htpc, hSurv]
      simp only [Bool.or_eq_true]
      rfl

private theorem runFromPC4
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (inv : OriginalEntryInverse.Index q)
    (Hdr : StaticHeaderSpec I g.vertexCount q.count)
    (hISz : I.size < 2 ^ bits) (hqLe : q.count ≤ g.vertexCount)
    (hMapEq : ∀ d : Fin q.count, (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d)
    (hRangesValid : ∀ d : Fin q.count, StaticChildLookup.Valid (q.reader.ranges.read d))
    (hOrigOfEntry : NatSliceAt I Hdr.origOfEntryBase q.count
      (fun rk => if hr : rk < q.count then (inv.slots.read ⟨rk, hr⟩).val else 0))
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (hStop : NatSliceAt I Hdr.stopBase q.count
      (fun d => if hd : d < q.count then q.reader.stop ⟨d, hd⟩ else 0))
    (cStart : Fin (q.count + 1) → Nat)
    (hc0 : cStart ⟨0, Nat.zero_lt_succ _⟩ = 0)
    (hcStep : ∀ d : Fin q.count,
      cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
        cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + (q.reader.ranges.read d).size)
    (hcSlice : NatSliceAt I Hdr.childStartBase (q.count + 1)
      (fun idx => if hi : idx < q.count + 1 then cStart ⟨idx, hi⟩ else 0))
    (hcItems : ∀ (d : Fin q.count) (j : Nat) (hj : j < (q.reader.ranges.read d).size),
      let pos := cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j
      let ch := (q.reader.ranges.read d)[j]'hj
      pos < q.count ∧
      (I[Hdr.childEntriesBase + pos]?).map Fin.val = some ch.entry ∧
      (I[Hdr.childStopsBase + pos]?).map Fin.val = some ch.stop ∧
      (I[Hdr.childIdsBase + pos]?).map Fin.val = some ch.id.val)
    (recs : ∀ d : Fin q.count,
      SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d)
    (dDense aDense bDense xDense : Fin q.count)
    (dW aW bW xW : Word bits)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc4)
    (hdS : s.data[slD]? = some dW) (haS : s.data[slADense]? = some aW)
    (hbS : s.data[slBDense]? = some bW) (hxS : s.data[slXDense]? = some xW)
    (hdV : dW.val = dDense.val) (haV : aW.val = aDense.val)
    (hbV : bW.val = bDense.val) (hxV : xW.val = xDense.val) :
    let eval := buildSealedEvaluator progress injRank q originalRows hRows rows childOK Hdr recs
    let R := thirdInstalledRuntime q (eval.toBaseRuntime inv 0 (Nat.le_refl 0)) 0 (Nat.le_refl 0)
    ∃ (t : State (codeLayout bits I.size hI hWork)) (k : Nat),
      k ≤ 354 * OracleContract.L g.vertexCount + 541 ∧
      Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
      t.pc = if ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value
             then okPC hI hTag else failPC hI hTag := by
  intro eval R
  have hHdrFit : oracleHeaderSize ≤ I.size := Hdr.hdr_fit
  have hEHLt : hdrEntry < I.size := by unfold oracleHeaderSize hdrEntry at *; omega
  have hSHLt : hdrStop < I.size := by unfold oracleHeaderSize hdrStop at *; omega
  let entryBaseW := I[hdrEntry]'hEHLt
  let stopBaseW := I[hdrStop]'hSHLt
  have hEH? : I[hdrEntry]? = some entryBaseW := getElem?_pos I _ hEHLt
  have hSH? : I[hdrStop]? = some stopBaseW := getElem?_pos I _ hSHLt
  have hEBVal : entryBaseW.val = Hdr.entryBase := by
    have hm := Hdr.hEntryBase; rw [hEH?, Option.map_some] at hm; exact Option.some.inj hm
  have hSBVal : stopBaseW.val = Hdr.stopBase := by
    have hm := Hdr.hStopBase; rw [hSH?, Option.map_some] at hm; exact Option.some.inj hm
  obtain ⟨ewA, hewA, hewAV⟩ := natSliceAt_fin hEntry aDense
  obtain ⟨ewB, hewB, hewBV⟩ := natSliceAt_fin hEntry bDense
  obtain ⟨ewX, hewX, hewXV⟩ := natSliceAt_fin hEntry xDense
  obtain ⟨swA, hswA, hswAV⟩ := natSliceAt_fin hStop aDense
  obtain ⟨swB, hswB, hswBV⟩ := natSliceAt_fin hStop bDense
  have hewA' : I[entryBaseW.val + aDense.val]? = some ewA := by rw [hEBVal]; exact hewA
  have hewB' : I[entryBaseW.val + bDense.val]? = some ewB := by rw [hEBVal]; exact hewB
  have hewX' : I[entryBaseW.val + xDense.val]? = some ewX := by rw [hEBVal]; exact hewX
  have hswA' : I[stopBaseW.val + aDense.val]? = some swA := by rw [hSBVal]; exact hswA
  have hswB' : I[stopBaseW.val + bDense.val]? = some swB := by rw [hSBVal]; exact hswB
  obtain ⟨hcA, hcB, hcX, hcY⟩ := exec_blkRouteBlocks hI hWork hTag q rows childOK hMapEq hRangesValid
    Hdr hISz hEntry cStart hc0 hcStep hcSlice hcItems s hpc dDense aDense bDense xDense
    dW aW bW xW hdS haS hbS hxS hdV haV hbV hxV
  have hTailOf : ∀ (wDense : Fin q.count) (wW : Word bits) (ewW swW : Word bits)
      (hwV : wW.val = wDense.val)
      (hewW' : I[entryBaseW.val + wW.val]? = some ewW) (hewWV : ewW.val = q.reader.entry wDense)
      (hswW' : I[stopBaseW.val + wW.val]? = some swW) (hswWV : swW.val = q.reader.stop wDense)
      (s6 : State (codeLayout bits I.size hI hWork)),
      s6.pc = pc6 hI hTag → (reg s6 1).val = wDense.val → s6.data[slXDense]? = some xW →
      ∃ t k, k ≤ 18 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s6 t ∧
        t.pc = if !(q.reader.isAncestor wDense xDense) then okPC hI hTag else failPC hI hTag := by
    intro wDense wW ewW swW hwV hewW' hewWV hswW' hswWV s6 h6pc h6r1 h6x
    let wReg := reg s6 1
    have hwEq : wReg = wW := Fin.ext (h6r1.trans hwV.symm)
    have hewX'' : I[entryBaseW.val + xW.val]? = some ewX := by rw [hxV]; exact hewX'
    have hewW'' : I[entryBaseW.val + wReg.val]? = some ewW := by rw [hwEq]; exact hewW'
    have hswW'' : I[stopBaseW.val + wReg.val]? = some swW := by rw [hwEq]; exact hswW'
    obtain ⟨t, k6, hk6, hs6, htpc⟩ := exec_blkTail hI hWork hTag s6 h6pc wReg xW entryBaseW stopBaseW
      ewW ewX swW rfl h6x hEH? hSH? hewW'' hewX'' hswW''
    refine ⟨t, k6, hk6, hs6, ?_⟩
    have hAnc := isAncestor_eq_decide q.reader wDense xDense
    rw [htpc, hAnc, ← hewWV, ← hewXV, ← hswWV]
    by_cases hc : ewW.val ≤ ewX.val ∧ ewX.val < swW.val <;> simp [hc]
  have hFA : (R.fetch (.child dDense aDense)).value = q.reader.child dDense aDense := rfl
  have hFB : (R.fetch (.child dDense bDense)).value = q.reader.child dDense bDense := rfl
  have hFX : (R.fetch (.child dDense xDense)).value = q.reader.child dDense xDense := rfl
  cases hCA : q.reader.child dDense aDense with
  | none =>
    have hSurv : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value = false := by
      dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
      rw [hFA, hCA]; rfl
    obtain ⟨t, k4, hk4, hs4, htpc⟩ := hcA hCA
    refine ⟨t, k4, by omega, hs4, by rw [htpc, hSurv]; rfl⟩
  | some uDense =>
    cases hCB : q.reader.child dDense bDense with
    | none =>
      have hSurv : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value = false := by
        dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
        rw [hFA, hCA]
        dsimp only [EX44.Plan.fast_value]
        rw [hFB, hCB]; rfl
      obtain ⟨t, k4, hk4, hs4, htpc⟩ := hcB uDense hCA hCB
      refine ⟨t, k4, by omega, hs4, by rw [htpc, hSurv]; rfl⟩
    | some vDense =>
      cases hCX : q.reader.child dDense xDense with
      | none =>
        have hSurv : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value = true := by
          dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
          rw [hFA, hCA]; dsimp only [EX44.Plan.fast_value]
          rw [hFB, hCB]; dsimp only [EX44.Plan.fast_value]
          rw [hFX, hCX]; rfl
        obtain ⟨t, k4, hk4, hs4, htpc⟩ := hcX uDense vDense hCA hCB hCX
        refine ⟨t, k4, by omega, hs4, by rw [htpc, hSurv]; rfl⟩
      | some yDense =>
        have hcY' := hcY uDense vDense yDense hCA hCB hCX
        by_cases hyu : yDense = uDense
        · have hSurv : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value =
              !(q.reader.isAncestor aDense xDense) := by
            dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
            rw [hFA, hCA]; dsimp only [EX44.Plan.fast_value]
            rw [hFB, hCB]; dsimp only [EX44.Plan.fast_value]
            rw [hFX, hCX]
            dsimp only
            rw [ite_eq_left hyu]
            rfl
          obtain ⟨s6, k4, hk4, hs4, h6pc, h6r1, h6x⟩ := hcY'.1 hyu
          obtain ⟨t, k6, hk6, hs6, htpc⟩ := hTailOf aDense aW ewA swA haV (by rw [haV]; exact hewA') hewAV
            (by rw [haV]; exact hswA') hswAV s6 h6pc h6r1 h6x
          refine ⟨t, k4 + k6, by omega, hs4.append hs6, by rw [htpc, hSurv]⟩
        · by_cases hyv : yDense = vDense
          · have hSurv : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value =
                !(q.reader.isAncestor bDense xDense) := by
              dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
              rw [hFA, hCA]; dsimp only [EX44.Plan.fast_value]
              rw [hFB, hCB]; dsimp only [EX44.Plan.fast_value]
              rw [hFX, hCX]
              dsimp only
              rw [ite_eq_right hyu, ite_eq_left hyv]
              rfl
            obtain ⟨s6, k4, hk4, hs4, h6pc, h6r1, h6x⟩ := hcY'.2.1 hyu hyv
            obtain ⟨t, k6, hk6, hs6, htpc⟩ := hTailOf bDense bW ewB swB hbV (by rw [hbV]; exact hewB') hewBV
              (by rw [hbV]; exact hswB') hswBV s6 h6pc h6r1 h6x
            refine ⟨t, k4 + k6, by omega, hs4.append hs6, by rw [htpc, hSurv]⟩
          · by_cases huv : uDense = vDense
            · have hSurv : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value = true := by
                dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
                rw [hFA, hCA]; dsimp only [EX44.Plan.fast_value]
                rw [hFB, hCB]; dsimp only [EX44.Plan.fast_value]
                rw [hFX, hCX]
                dsimp only
                rw [ite_eq_right hyu, ite_eq_right hyv]
                dsimp only [EX44.routeThird, EX44.Plan.fast_value]
                have hNone : (R.fetch (.key dDense uDense vDense)).value = none := by
                  change ((eval.toBaseRuntime inv 0 (Nat.le_refl 0)).pairKey dDense uDense vDense).value = none
                  dsimp only [DenseOwnerExitEvaluator.toBaseRuntime]
                  by_cases hu : q.input.parent.read uDense = dDense ∧ uDense ≠ dDense
                  · by_cases hv : q.input.parent.read vDense = dDense ∧ vDense ≠ dDense
                    · simp [hv, huv]
                    · simp [hu, hv]
                  · simp [hu]
                rw [hNone]; rfl
              obtain ⟨t, k4, hk4, hs4, htpc⟩ := hcY'.2.2.1 hyu hyv huv
              refine ⟨t, k4, by omega, hs4, by rw [htpc, hSurv]; rfl⟩
            · obtain ⟨hpU, hneU, hpV, hneV, hpY, hneY, s5a, k4, hk4, hs4, h5apc, h5aDsz, h5aD, h5aAD, h5aBD, h5aUL, h5aVL, h5aYL⟩ :=
                hcY'.2.2.2 hyu hyv huv
              have hAD' : (s5a.data[slADense]?).map Fin.val = some aDense.val := by
                rw [h5aAD, Option.map_some]; exact congrArg some haV
              have hBD' : (s5a.data[slBDense]?).map Fin.val = some bDense.val := by
                rw [h5aBD, Option.map_some]; exact congrArg some hbV
              obtain ⟨t, k5, hk5, hs5, htpc⟩ := runThirdExits hI hWork hTag progress injRank q originalRows hRows
                rows childOK inv Hdr hqLe hOrigOfEntry hEntry hStop recs dDense aDense bDense uDense vDense yDense
                hpU hneU hpV hneV hpY hneY huv s5a h5apc h5aDsz hAD' hBD' h5aD h5aUL h5aVL h5aYL
              have hRtEq : ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value =
                  ((EX44.answer ((EX44.routeThird dDense uDense vDense aDense bDense yDense).run R).value).run R).value := by
                dsimp only [EX44.routeBlocks, EX44.Plan.fast_value]
                rw [hFA, hCA]; dsimp only [EX44.Plan.fast_value]
                rw [hFB, hCB]; dsimp only [EX44.Plan.fast_value]
                rw [hFX, hCX]
                dsimp only
                rw [ite_eq_right hyu, ite_eq_right hyv]
              refine ⟨t, k4 + k5, by omega, hs4.append hs5, by rw [htpc, hRtEq]⟩

private theorem runFromPC3
    {bits : Nat} {g : Digraph} {r : Fin g.vertexCount} {I : Array (Word bits)}
    (hI : I.size ≤ 2 ^ bits) (hWork : queryWorkCap ≤ 2 ^ bits) (hTag : TagsFit bits)
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (q : OriginalReader g r)
    (originalRows : EX51.Rows g.vertexCount (Digraph.GlobalSibling.Entry g (2 * q.count)))
    (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
    {buckets : ForestLayout.ChildLists q.count}
    (rows : Layout buckets)
    (childOK : ∀ d c : Fin q.count,
      c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)
    (inv : OriginalEntryInverse.Index q)
    (Hdr : StaticHeaderSpec I g.vertexCount q.count)
    (hISz : I.size < 2 ^ bits) (hqLe : q.count ≤ g.vertexCount)
    (hRootSz : q.reader.tables.size q.reader.tables.root ≤ q.count)
    (hMapEq : ∀ d : Fin q.count, (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d)
    (hRangesValid : ∀ d : Fin q.count, StaticChildLookup.Valid (q.reader.ranges.read d))
    (hHead : NatSliceAt I Hdr.headBase q.count
      (fun d => if hd : d < q.count then (q.reader.tables.head ⟨d, hd⟩).val else 0))
    (hParent : NatSliceAt I Hdr.domParentBase q.count
      (fun d => if hd : d < q.count then (q.reader.tables.parent ⟨d, hd⟩).val else 0))
    (hDepth : NatSliceAt I Hdr.domDepthBase q.count
      (fun d => if hd : d < q.count then q.reader.tables.depth ⟨d, hd⟩ else 0))
    (hOrigOfEntry : NatSliceAt I Hdr.origOfEntryBase q.count
      (fun rk => if hr : rk < q.count then (inv.slots.read ⟨rk, hr⟩).val else 0))
    (hEntry : NatSliceAt I Hdr.entryBase q.count
      (fun d => if hd : d < q.count then q.reader.entry ⟨d, hd⟩ else 0))
    (hStop : NatSliceAt I Hdr.stopBase q.count
      (fun d => if hd : d < q.count then q.reader.stop ⟨d, hd⟩ else 0))
    (cStart : Fin (q.count + 1) → Nat)
    (hc0 : cStart ⟨0, Nat.zero_lt_succ _⟩ = 0)
    (hcStep : ∀ d : Fin q.count,
      cStart ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ =
        cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + (q.reader.ranges.read d).size)
    (hcSlice : NatSliceAt I Hdr.childStartBase (q.count + 1)
      (fun idx => if hi : idx < q.count + 1 then cStart ⟨idx, hi⟩ else 0))
    (hcItems : ∀ (d : Fin q.count) (j : Nat) (hj : j < (q.reader.ranges.read d).size),
      let pos := cStart ⟨d.val, Nat.lt_succ_of_lt d.isLt⟩ + j
      let ch := (q.reader.ranges.read d)[j]'hj
      pos < q.count ∧
      (I[Hdr.childEntriesBase + pos]?).map Fin.val = some ch.entry ∧
      (I[Hdr.childStopsBase + pos]?).map Fin.val = some ch.stop ∧
      (I[Hdr.childIdsBase + pos]?).map Fin.val = some ch.id.val)
    (recs : ∀ d : Fin q.count,
      SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d)
    (aDense bDense xDense : Fin q.count)
    (aW bW xW : Word bits)
    (s : State (codeLayout bits I.size hI hWork)) (hpc : s.pc = pc3)
    (haS : s.data[slADense]? = some aW) (hbS : s.data[slBDense]? = some bW) (hxS : s.data[slXDense]? = some xW)
    (haV : aW.val = aDense.val) (hbV : bW.val = bDense.val) (hxV : xW.val = xDense.val) :
    let eval := buildSealedEvaluator progress injRank q originalRows hRows rows childOK Hdr recs
    let R := thirdInstalledRuntime q (eval.toBaseRuntime inv 0 (Nat.le_refl 0)) 0 (Nat.le_refl 0)
    ∃ (t : State (codeLayout bits I.size hI hWork)) (k : Nat),
      k ≤ 382 * OracleContract.L g.vertexCount + 621 ∧
      Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s t ∧
      t.pc = if ((EX44.answer ((EX44.routePair aDense bDense xDense).run R).value).run R).value
             then okPC hI hTag else failPC hI hTag := by
  intro eval R
  have hHdrFit : oracleHeaderSize ≤ I.size := Hdr.hdr_fit
  have hEHLt : hdrEntry < I.size := by unfold oracleHeaderSize hdrEntry at *; omega
  have hSHLt : hdrStop < I.size := by unfold oracleHeaderSize hdrStop at *; omega
  let entryBaseW := I[hdrEntry]'hEHLt
  let stopBaseW := I[hdrStop]'hSHLt
  have hEH? : I[hdrEntry]? = some entryBaseW := getElem?_pos I _ hEHLt
  have hSH? : I[hdrStop]? = some stopBaseW := getElem?_pos I _ hSHLt
  have hEBVal : entryBaseW.val = Hdr.entryBase := by
    have hm := Hdr.hEntryBase; rw [hEH?, Option.map_some] at hm; exact Option.some.inj hm
  have hSBVal : stopBaseW.val = Hdr.stopBase := by
    have hm := Hdr.hStopBase; rw [hSH?, Option.map_some] at hm; exact Option.some.inj hm
  obtain ⟨ewA, hewA, hewAV⟩ := natSliceAt_fin hEntry aDense
  obtain ⟨ewB, hewB, hewBV⟩ := natSliceAt_fin hEntry bDense
  obtain ⟨ewX, hewX, hewXV⟩ := natSliceAt_fin hEntry xDense
  obtain ⟨swA, hswA, hswAV⟩ := natSliceAt_fin hStop aDense
  obtain ⟨swB, hswB, hswBV⟩ := natSliceAt_fin hStop bDense
  obtain ⟨hc1, hc2, hc3⟩ := exec_blkRoutePair hI hWork hTag q Hdr hRootSz hHead hParent hDepth hEntry hStop
    s hpc aDense bDense aW bW xW haS hbS hxS haV hbV
  have hFAB : (R.fetch (.ancestor aDense bDense)).value = q.reader.isAncestor aDense bDense := rfl
  have hFBA : (R.fetch (.ancestor bDense aDense)).value = q.reader.isAncestor bDense aDense := rfl
  cases hab : q.reader.isAncestor aDense bDense with
  | true =>
    have hSurv : ((EX44.answer ((EX44.routePair aDense bDense xDense).run R).value).run R).value =
        !(q.reader.isAncestor aDense xDense) := by
      dsimp only [EX44.routePair, EX44.Plan.fast_value]
      rw [hFAB, hab]; rfl
    obtain ⟨s6, k3, hk3, hs3, h6pc, h6r1, h6x⟩ := hc1 hab
    let wReg := reg s6 1
    have hwEq : wReg = aW := Fin.ext (h6r1.trans haV.symm)
    have hewX' : I[entryBaseW.val + xW.val]? = some ewX := by rw [hEBVal, hxV]; exact hewX
    have hewA' : I[entryBaseW.val + wReg.val]? = some ewA := by rw [hwEq, hEBVal, haV]; exact hewA
    have hswA' : I[stopBaseW.val + wReg.val]? = some swA := by rw [hwEq, hSBVal, haV]; exact hswA
    obtain ⟨t, k6, hk6, hs6, htpc⟩ := exec_blkTail hI hWork hTag s6 h6pc wReg xW entryBaseW stopBaseW
      ewA ewX swA rfl h6x hEH? hSH? hewA' hewX' hswA'
    have hAnc := isAncestor_eq_decide q.reader aDense xDense
    have hL1 := OracleContract.one_le_L g.vertexCount
    refine ⟨t, k3 + k6, by omega, hs3.append hs6, ?_⟩
    rw [htpc, hSurv, hAnc, ← hewAV, ← hewXV, ← hswAV]
    by_cases hc : ewA.val ≤ ewX.val ∧ ewX.val < swA.val <;> simp [hc]
  | false =>
    cases hba : q.reader.isAncestor bDense aDense with
    | true =>
      have hSurv : ((EX44.answer ((EX44.routePair aDense bDense xDense).run R).value).run R).value =
          !(q.reader.isAncestor bDense xDense) := by
        dsimp only [EX44.routePair, EX44.Plan.fast_value]
        rw [hFAB, hab, ite_eq_right Bool.false_ne_true, EX44.Plan.fast_value, hFBA, hba]
        rfl
      obtain ⟨s6, k3, hk3, hs3, h6pc, h6r1, h6x⟩ := hc2 hab hba
      let wReg := reg s6 1
      have hwEq : wReg = bW := Fin.ext (h6r1.trans hbV.symm)
      have hewX' : I[entryBaseW.val + xW.val]? = some ewX := by rw [hEBVal, hxV]; exact hewX
      have hewB' : I[entryBaseW.val + wReg.val]? = some ewB := by rw [hwEq, hEBVal, hbV]; exact hewB
      have hswB' : I[stopBaseW.val + wReg.val]? = some swB := by rw [hwEq, hSBVal, hbV]; exact hswB
      obtain ⟨t, k6, hk6, hs6, htpc⟩ := exec_blkTail hI hWork hTag s6 h6pc wReg xW entryBaseW stopBaseW
        ewB ewX swB rfl h6x hEH? hSH? hewB' hewX' hswB'
      have hAnc := isAncestor_eq_decide q.reader bDense xDense
      have hL1 := OracleContract.one_le_L g.vertexCount
      refine ⟨t, k3 + k6, by omega, hs3.append hs6, ?_⟩
      rw [htpc, hSurv, hAnc, ← hewBV, ← hewXV, ← hswBV]
      by_cases hc : ewB.val ≤ ewX.val ∧ ewX.val < swB.val <;> simp [hc]
    | false =>
      obtain ⟨s4, k3, hk3, hs3, h4pc, h4D, h4AD, h4BD, h4XD, _⟩ := hc3 hab hba
      let dDense := (q.reader.lca aDense bDense).node
      obtain ⟨dW, hdW, hdWV⟩ : ∃ w, s4.data[slD]? = some w ∧ w.val = dDense.val := by
        cases hw : s4.data[slD]? with
        | none => simp [hw] at h4D
        | some w => exact ⟨w, rfl, by simpa [hw] using h4D⟩
      obtain ⟨t, k4, hk4, hs4, htpc⟩ := runFromPC4 hI hWork hTag progress injRank q originalRows hRows
        rows childOK inv Hdr hISz hqLe hMapEq hRangesValid hOrigOfEntry hEntry hStop cStart hc0 hcStep
        hcSlice hcItems recs dDense aDense bDense xDense dW aW bW xW s4 h4pc hdW h4AD h4BD h4XD
        hdWV haV hbV hxV
      have hSurvEq : ((EX44.answer ((EX44.routePair aDense bDense xDense).run R).value).run R).value =
          ((EX44.answer ((EX44.routeBlocks dDense aDense bDense xDense).run R).value).run R).value := by
        dsimp only [EX44.routePair, EX44.Plan.fast_value]
        rw [hFAB, hab, ite_eq_right Bool.false_ne_true, EX44.Plan.fast_value, hFBA, hba]
        rfl
      refine ⟨t, k3 + k4, by omega, hs3.append hs4, by rw [htpc, hSurvEq]⟩

private theorem withID_run_none {N n k B E : Nat} {α : Type} {f s : Nat}
    (R : EX44.Runtime N n k B E) (next : Option (Fin n) → EX44.Plan N n k α f s) :
    ((EX44.withID none next).run R).value = ((next none).run R).value := rfl

private theorem withID_run_some {N n k B E : Nat} {α : Type} {f s : Nat}
    (R : EX44.Runtime N n k B E) (j : Fin N) (next : Option (Fin n) → EX44.Plan N n k α f s) :
    ((EX44.withID (some j) next).run R).value = ((next (R.fetch (.translate j)).value).run R).value := rfl

/-- **EX5.3 End-to-End Sealed Word-RAM Query Specification**:
On any acyclic digraph `g`, source `r`, valid sealed index `I`, failure set `F`, and target `t`,
executing the single fixed query ROM `oracleQueryPhase I hI hWork hTag` from `Params.encode hn hTag F t`
with fuel `1200 * OracleContract.L g.vertexCount` halts cleanly with:
1. `o.operations ≤ 1200 * OracleContract.L g.vertexCount`,
2. `o.words = I.size + queryWorkCap + 16`,
3. `o.answer = true ↔ g.ReachableAvoiding F r t`. -/
theorem oracleQueryProgram_spec
    {bits : Nat} {g : Digraph} (r : Fin g.vertexCount) (acyc : g.IsAcyclic)
    (I : Array (Word bits)) (hVal : ValidSealedOracleIndex g r I)
    (hI : I.size ≤ 2 ^ bits := Nat.le_of_lt hVal.index_size_lt)
    (hWork : queryWorkCap ≤ 2 ^ bits := hVal.work_le)
    (hTag : TagsFit bits := hVal.tags_fit)
    (hn : g.vertexCount ≤ 2 ^ bits := hVal.vertexCount_le)
    (F : FailureSet g.vertexCount) (t : Fin g.vertexCount) :
    let p := oracleQueryPhase I hI hWork hTag
    let params := SealedQuery.Params.encode hn hTag F t
    ∃ o : SealedQuery.Observation,
      p.observe params (1200 * OracleContract.L g.vertexCount) = some o ∧
      o.operations ≤ 1200 * OracleContract.L g.vertexCount ∧
      o.words = I.size + queryWorkCap + 16 ∧
      (o.answer = true ↔ g.ReachableAvoiding F r t) := by
  have hValCopy := hVal
  rcases hVal with ⟨_, _, rank, progress, injRank, q, originalRows, hRows, buckets, rows, childOK,
    inv, Hdr, hRootZero, hRootSz, hRanges, hHead, hParent, hDepth, hOrigToDense, _hDenseToOrig,
    hEntry, hStop, hOrigOfEntry, hChildStart, hRecs⟩
  rcases hChildStart with ⟨cStart, hc0, hcStep, hcSlice, hcItems⟩
  have recs : ∀ d : Fin q.count,
      SealedOwnerRecord progress injRank q originalRows hRows rows childOK I Hdr d :=
    fun d => Classical.choice (hRecs d)
  have hMapEq : ∀ d : Fin q.count, (q.reader.ranges.read d).toList.map (fun c => c.id) = buckets.get d :=
    fun d => (hRanges d).1
  have hRangesValid : ∀ d : Fin q.count, StaticChildLookup.Valid (q.reader.ranges.read d) :=
    fun d => (hRanges d).2
  have hISz : I.size < 2 ^ bits := hValCopy.index_size_lt
  have hqLe : q.count ≤ g.vertexCount := by
    apply injective_fin_le q.ids.originals.read
    intro a b hab
    apply Option.some.inj
    rw [← q.ids.slot_of_original a, hab, q.ids.slot_of_original b]
  let eval := buildSealedEvaluator progress injRank q originalRows hRows rows childOK Hdr recs
  let R := thirdInstalledRuntime q (eval.toBaseRuntime inv 0 (Nat.le_refl 0)) 0 (Nat.le_refl 0)
  have hOnline := ActualOnlineOracle.online_oracle_correct_and_bounded acyc progress injRank q
    originalRows hRows rows childOK eval inv 0 (Nat.le_refl 0) F t
  let qRes := EX44.query R (failurePair F).1 (failurePair F).2 t
  have hrReach : g.InitiallyReachable r r := AvoidPath.refl r (fun h => h)
  have hSourceZero : (q.slot r hrReach).val = 0 := by
    rw [qSlot_root_eq_input_root q hrReach]; exact hRootZero
  have hRSource : R.source = q.slot r hrReach := rfl
  let p := oracleQueryPhase I hI hWork hTag
  let params := SealedQuery.Params.encode hn hTag F t
  let s0 := p.initialState params
  have hs0pc : s0.pc = 0 := rfl
  have hr0 : reg s0 ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 4) p.hR⟩ = params.reg 0 :=
    SealedQueryR.Phase.initial_abi p params 0
  have hr1 : reg s0 ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 4) p.hR⟩ = params.reg 1 :=
    SealedQueryR.Phase.initial_abi p params 1
  have hr2 : reg s0 ⟨2, Nat.lt_of_lt_of_le (by decide : 2 < 4) p.hR⟩ = params.reg 2 :=
    SealedQueryR.Phase.initial_abi p params 2
  have hr3 : reg s0 ⟨3, Nat.lt_of_lt_of_le (by decide : 3 < 4) p.hR⟩ = params.reg 3 :=
    SealedQueryR.Phase.initial_abi p params 3
  have hHdrFit : oracleHeaderSize ≤ I.size := Hdr.hdr_fit
  have hOrigHdrLt : hdrOrigToDense < I.size := by unfold oracleHeaderSize hdrOrigToDense at *; omega
  have hEHLt : hdrEntry < I.size := by unfold oracleHeaderSize hdrEntry at *; omega
  have hSHLt : hdrStop < I.size := by unfold oracleHeaderSize hdrStop at *; omega
  let origToDenseBase := I[hdrOrigToDense]'hOrigHdrLt
  let entryBaseW := I[hdrEntry]'hEHLt
  let stopBaseW := I[hdrStop]'hSHLt
  have hOrigHdr? : I[hdrOrigToDense]? = some origToDenseBase := getElem?_pos I _ hOrigHdrLt
  have hEH? : I[hdrEntry]? = some entryBaseW := getElem?_pos I _ hEHLt
  have hSH? : I[hdrStop]? = some stopBaseW := getElem?_pos I _ hSHLt
  have hOTDBVal : origToDenseBase.val = Hdr.origToDenseBase := by
    have hm := Hdr.hOrigToDenseBase; rw [hOrigHdr?, Option.map_some] at hm; exact Option.some.inj hm
  have hEBVal : entryBaseW.val = Hdr.entryBase := by
    have hm := Hdr.hEntryBase; rw [hEH?, Option.map_some] at hm; exact Option.some.inj hm
  have hSBVal : stopBaseW.val = Hdr.stopBase := by
    have hm := Hdr.hStopBase; rw [hSH?, Option.map_some] at hm; exact Option.some.inj hm
  have hMapV : ∀ v : Fin g.vertexCount, ∃ w,
      origToDenseBase.val + v.val < I.size ∧
      I[origToDenseBase.val + v.val]? = some w ∧
      w.val = match q.ids.find v with | none => 0 | some d => d.val + 1 := by
    intro v
    have hlt : Hdr.origToDenseBase + v.val < I.size := by have := hOrigToDense.1; omega
    obtain ⟨w, hw, hwV⟩ := natSliceAt_fin
      (f := fun u : Fin g.vertexCount => match q.ids.find u with | none => 0 | some d => d.val + 1)
      hOrigToDense v
    exact ⟨w, by rw [hOTDBVal]; exact hlt, by rw [hOTDBVal]; exact hw, hwV⟩
  obtain ⟨wTgt, hMapTgt, hwTgt, hwTgtV⟩ := hMapV t
  have hTgtV' : origToDenseBase.val + (params.reg 3).val < I.size ∧
      I[origToDenseBase.val + (params.reg 3).val]? = some wTgt := by
    have hp3 : (params.reg 3).val = t.val := by cases F <;> rfl
    rw [hp3]; exact ⟨hMapTgt, hwTgt⟩
  obtain ⟨hcFailTgt, hcTag0, hcTag1, hcTag2⟩ := exec_blkSaveAndTarget hI hWork hTag s0 hs0pc
    (params.reg 0) (params.reg 1) (params.reg 2) (params.reg 3) origToDenseBase wTgt
    hr0 hr1 hr2 hr3 hOrigHdr? hTgtV'.1 hTgtV'.2
  have hL1 := OracleContract.one_le_L g.vertexCount
  have hFinish : ∀ (k : Nat) {tState : State (codeLayout bits I.size hI hWork)},
      k + 50 ≤ 1200 * OracleContract.L g.vertexCount →
      Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k s0 tState →
      tState.pc = (if qRes.survives then okPC hI hTag else failPC hI hTag) →
      ∃ o : SealedQuery.Observation,
        p.observe params (1200 * OracleContract.L g.vertexCount) = some o ∧
        o.operations ≤ 1200 * OracleContract.L g.vertexCount ∧
        o.words = I.size + queryWorkCap + 16 ∧
        (o.answer = true ↔ g.ReachableAvoiding F r t) := by
    intro k tState hkBound hst htpc
    obtain ⟨o, hobs, hops, hwords, hans⟩ :=
      observe_of_exit_pc I hI hWork hTag params (1200 * OracleContract.L g.vertexCount) k qRes.survives
        hkBound hst htpc
    refine ⟨o, hobs, hops, hwords, ?_⟩
    rw [hans]
    exact hOnline.1
  -- Dispatch on failure set `F` and translated target `q.ids.find t`
  cases hFt : q.ids.find t with
  | none =>
    have hwTgt0 : wTgt.val = 0 := by rw [hwTgtV, hFt]
    have hSurvFalse : qRes.survives = false := by
      have hTr : (R.fetch (.translate t)).value = none := hFt
      cases F with
      | none =>
        dsimp only [qRes, EX44.query, EX44.route, failurePair]
        rw [withID_run_none, withID_run_none, EX44.Plan.fast_value, hTr]
        dsimp only [EX44.routeRetained]
        split
        · simp only [EX44.Plan.stop_value, EX44.answer]
        · simp only [EX44.Plan.stop_value, EX44.answer]
      | one a =>
        dsimp only [qRes, EX44.query, EX44.route, failurePair]
        rw [withID_run_some, withID_run_none, EX44.Plan.fast_value, hTr]
        dsimp only [EX44.routeRetained]
        split
        · simp only [EX44.Plan.stop_value, EX44.answer]
        · simp only [EX44.Plan.stop_value, EX44.answer]
      | two a b =>
        dsimp only [qRes, EX44.query, EX44.route, failurePair]
        rw [withID_run_some, withID_run_some, EX44.Plan.fast_value, hTr]
        dsimp only [EX44.routeRetained]
        split
        · simp only [EX44.Plan.stop_value, EX44.answer]
        · simp only [EX44.Plan.stop_value, EX44.answer]
    obtain ⟨tState, k, hk, hst, htpc⟩ := hcFailTgt hwTgt0
    exact hFinish k (by omega) hst (by rw [htpc, hSurvFalse]; rfl)
  | some xDense =>
    have hwTgtVal : wTgt.val = xDense.val + 1 := by simpa [hFt] using hwTgtV
    have hwTgtNz : wTgt.val ≠ 0 := by rw [hwTgtVal]; exact Nat.succ_ne_zero _
    have hwTgtSub : wTgt.val - 1 = xDense.val := by rw [hwTgtVal]; exact Nat.add_sub_cancel _ 1
    have hTail1 : ∀ (wDense : Fin q.count) (wReg : Word bits) (xW : Word bits)
        (s6 : State (codeLayout bits I.size hI hWork)),
        s6.pc = pc6 hI hTag → (reg s6 1).val = wDense.val →
        s6.data[slXDense]? = some xW → xW.val = xDense.val →
        ∃ tState k6, k6 ≤ 18 ∧ Steps (oracleQueryProgram hI hWork hTag) ⟨I, rfl⟩ k6 s6 tState ∧
          tState.pc = if !(q.reader.isAncestor wDense xDense) then okPC hI hTag else failPC hI hTag := by
      intro wDense wReg xW s6 h6pc h6r1 h6x hxV
      obtain ⟨ewW, hewW, hewWV⟩ := natSliceAt_fin hEntry wDense
      obtain ⟨ewX, hewX, hewXV⟩ := natSliceAt_fin hEntry xDense
      obtain ⟨swW, hswW, hswWV⟩ := natSliceAt_fin hStop wDense
      have h6r1' : reg s6 1 = reg s6 1 := rfl
      have hewW' : I[entryBaseW.val + (reg s6 1).val]? = some ewW := by rw [hEBVal, h6r1]; exact hewW
      have hewX' : I[entryBaseW.val + xW.val]? = some ewX := by rw [hEBVal, hxV]; exact hewX
      have hswW' : I[stopBaseW.val + (reg s6 1).val]? = some swW := by rw [hSBVal, h6r1]; exact hswW
      obtain ⟨tState, k6, hk6, hs6, htpc⟩ := exec_blkTail hI hWork hTag s6 h6pc (reg s6 1) xW entryBaseW stopBaseW
        ewW ewX swW h6r1' h6x hEH? hSH? hewW' hewX' hswW'
      have hAnc := isAncestor_eq_decide q.reader wDense xDense
      refine ⟨tState, k6, hk6, hs6, ?_⟩
      rw [htpc, hAnc, ← hewWV, ← hewXV, ← hswWV]
      by_cases hc : ewW.val ≤ ewX.val ∧ ewX.val < swW.val <;> simp [hc]
    cases F with
    | none =>
      have hTagZ : (params.reg 0).val = 0 := rfl
      have hSurvTrue : qRes.survives = true := by
        dsimp only [qRes, EX44.query, EX44.route, failurePair]
        have hTr : (R.fetch (.translate t)).value = some xDense := hFt
        rw [withID_run_none, withID_run_none, EX44.Plan.fast_value, hTr]
        dsimp only [EX44.routeRetained, EX44.Fails]
        simp only [reduceCtorEq, or_self, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
      obtain ⟨tState, k, hk, hst, htpc⟩ := hcTag0 hwTgtNz hTagZ
      exact hFinish k (by omega) hst (by rw [htpc, hSurvTrue]; rfl)
    | one a =>
      have hTag1 : (params.reg 0).val = 1 := rfl
      have hP1 : (params.reg 1).val = a.val := rfl
      obtain ⟨s1, k0, hk0, hs0, h1pc, _, h1f0, h1x⟩ := hcTag1 hwTgtNz hTag1
      obtain ⟨xW, hxW, hxWV⟩ : ∃ w, s1.data[slXDense]? = some w ∧ w.val = xDense.val := by
        cases hw : s1.data[slXDense]? with
        | none => simp [hw] at h1x
        | some w => exact ⟨w, rfl, by simpa [hw, hwTgtSub] using h1x⟩
      obtain ⟨wA, hMapA, hwA, hwAV⟩ := hMapV a
      have hMapA' : origToDenseBase.val + (params.reg 1).val < I.size := by rw [hP1]; exact hMapA
      have hwA' : I[origToDenseBase.val + (params.reg 1).val]? = some wA := by rw [hP1]; exact hwA
      obtain ⟨hcA0, hcA1, hcAx, hcOk⟩ := exec_blkTag1 hI hWork hTag s1 h1pc (params.reg 1) xW origToDenseBase wA
        h1f0 hxW hOrigHdr? hMapA' hwA'
      cases hFa : q.ids.find a with
      | none =>
        have hwA0 : wA.val = 0 := by rw [hwAV, hFa]
        have hSurv : qRes.survives = true := by
          dsimp only [qRes, EX44.query, EX44.route, failurePair]
          have hTa : (R.fetch (.translate a)).value = none := hFa
          have hTt : (R.fetch (.translate t)).value = some xDense := hFt
          rw [withID_run_some, hTa, withID_run_none, EX44.Plan.fast_value, hTt]
          dsimp only [EX44.routeRetained, EX44.Fails]
          simp only [reduceCtorEq, or_self, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
        obtain ⟨tState, k1, hk1, hs1, htpc⟩ := hcA0 hwA0
        exact hFinish (k0 + k1) (by omega) (hs0.append hs1) (by rw [htpc, hSurv]; rfl)
      | some aDense =>
        have hwAVal : wA.val = aDense.val + 1 := by simpa [hFa] using hwAV
        by_cases ha0 : aDense.val = 0
        · have haRoot : aDense = q.slot r hrReach := Fin.ext (ha0.trans hSourceZero.symm)
          have hwA1 : wA.val = 1 := by rw [hwAVal, ha0]
          have hSurv : qRes.survives = false := by
            dsimp only [qRes, EX44.query, EX44.route, failurePair]
            have hTa : (R.fetch (.translate a)).value = some aDense := hFa
            have hTt : (R.fetch (.translate t)).value = some xDense := hFt
            rw [withID_run_some, hTa, withID_run_none, EX44.Plan.fast_value, hTt, hRSource, haRoot]
            dsimp only [EX44.routeRetained, EX44.Fails]
            simp only [true_or, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
          obtain ⟨tState, k1, hk1, hs1, htpc⟩ := hcA1 hwA1
          exact hFinish (k0 + k1) (by omega) (hs0.append hs1) (by rw [htpc, hSurv]; rfl)
        · have hwA2 : 2 ≤ wA.val := by
            rw [hwAVal]; exact Nat.succ_le_succ (Nat.pos_of_ne_zero ha0)
          have hwASub : wA.val - 1 = aDense.val := by rw [hwAVal]; exact Nat.add_sub_cancel _ 1
          have haNeRoot : aDense ≠ q.slot r hrReach := fun e => ha0 ((congrArg Fin.val e).trans hSourceZero)
          by_cases hax : aDense = xDense
          · have hSubX : wA.val - 1 = xW.val := by rw [hwASub, hxWV, hax]
            have hSurv : qRes.survives = false := by
              dsimp only [qRes, EX44.query, EX44.route, failurePair]
              have hTa : (R.fetch (.translate a)).value = some aDense := hFa
              have hTt : (R.fetch (.translate t)).value = some xDense := hFt
              rw [withID_run_some, hTa, withID_run_none, EX44.Plan.fast_value, hTt, hax]
              dsimp only [EX44.routeRetained, EX44.Fails]
              split
              · simp only [EX44.Plan.stop_value, EX44.answer]
              · simp only [true_or, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
            obtain ⟨tState, k1, hk1, hs1, htpc⟩ := hcAx hwA2 hSubX
            exact hFinish (k0 + k1) (by omega) (hs0.append hs1) (by rw [htpc, hSurv]; rfl)
          · have hSubX : wA.val - 1 ≠ xW.val := by
              rw [hwASub, hxWV]; intro e; exact hax (Fin.ext e)
            have hSurv : qRes.survives = !(q.reader.isAncestor aDense xDense) := by
              dsimp only [qRes, EX44.query, EX44.route, failurePair]
              have hTa : (R.fetch (.translate a)).value = some aDense := hFa
              have hTt : (R.fetch (.translate t)).value = some xDense := hFt
              rw [withID_run_some, hTa, withID_run_none, EX44.Plan.fast_value, hTt, hRSource]
              dsimp only [EX44.routeRetained, EX44.Fails]
              have hnR : ¬ (some (q.slot r hrReach) = some aDense ∨
                  (some (q.slot r hrReach) : Option (Fin q.count)) = none) := by
                simp only [Option.some.injEq, reduceCtorEq, or_false]; exact Ne.symm haNeRoot
              have hnX : ¬ (some xDense = some aDense ∨ (some xDense : Option (Fin q.count)) = none) := by
                simp only [Option.some.injEq, reduceCtorEq, or_false]; exact Ne.symm hax
              rw [ite_eq_right hnR, ite_eq_right hnX, EX44.Plan.stop_value]
              dsimp only [EX44.answer, EX44.testOne]
              rw [EX44.Plan.fast_value]
              have hAncVal : (R.fetch (.ancestor aDense xDense)).value = q.reader.isAncestor aDense xDense := rfl
              rw [hAncVal, EX44.Plan.stop_value]
            obtain ⟨s6, k1, hk1, hs1, h6pc, h6r1, h6x⟩ := hcOk hwA2 hSubX
            obtain ⟨tState, k6, hk6, hs6, htpc⟩ := hTail1 aDense (reg s6 1) xW s6 h6pc (h6r1.trans hwASub) h6x hxWV
            exact hFinish (k0 + k1 + k6) (by omega) ((hs0.append hs1).append hs6) (by rw [htpc, hSurv])
    | two a b =>
      have hTag2 : (params.reg 0).val = 2 := rfl
      have hP1 : (params.reg 1).val = a.val := rfl
      have hP2 : (params.reg 2).val = b.val := rfl
      obtain ⟨s2, k0, hk0, hs0, h2pc, _, h2f0, h2f1, h2x⟩ := hcTag2 hwTgtNz hTag2
      obtain ⟨xW, hxW, hxWV⟩ : ∃ w, s2.data[slXDense]? = some w ∧ w.val = xDense.val := by
        cases hw : s2.data[slXDense]? with
        | none => simp [hw] at h2x
        | some w => exact ⟨w, rfl, by simpa [hw, hwTgtSub] using h2x⟩
      obtain ⟨wA, hMapA, hwA, hwAV⟩ := hMapV a
      obtain ⟨wB, hMapB, hwB, hwBV⟩ := hMapV b
      have hMapA' : origToDenseBase.val + (params.reg 1).val < I.size := by rw [hP1]; exact hMapA
      have hwA' : I[origToDenseBase.val + (params.reg 1).val]? = some wA := by rw [hP1]; exact hwA
      have hMapB' : origToDenseBase.val + (params.reg 2).val < I.size := by rw [hP2]; exact hMapB
      have hwB' : I[origToDenseBase.val + (params.reg 2).val]? = some wB := by rw [hP2]; exact hwB
      obtain ⟨hcFail2, hc00, hc0B, hcA0, hcAB⟩ := exec_blkTag2 hI hWork hTag s2 h2pc (params.reg 1) (params.reg 2)
        xW origToDenseBase wA wB h2f0 h2f1 hxW hOrigHdr? hMapA' hMapB' hwA' hwB'
      have hSurvFail : ∀ (oa ob : Option (Fin q.count)),
          (oa = some (q.slot r hrReach) ∨ ob = some (q.slot r hrReach) ∨ oa = some xDense ∨ ob = some xDense) →
          (R.fetch (.translate a)).value = oa → (R.fetch (.translate b)).value = ob →
          qRes.survives = false := by
        intro oa ob hCond hTa hTb
        dsimp only [qRes, EX44.query, EX44.route, failurePair]
        have hTt : (R.fetch (.translate t)).value = some xDense := hFt
        rw [withID_run_some, hTa, withID_run_some, hTb, EX44.Plan.fast_value, hTt, hRSource]
        dsimp only [EX44.routeRetained, EX44.Fails]
        rcases hCond with rfl | rfl | rfl | rfl
        · simp only [true_or, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
        · simp only [or_true, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
        · split
          · simp only [EX44.Plan.stop_value, EX44.answer]
          · simp only [true_or, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
        · split
          · simp only [EX44.Plan.stop_value, EX44.answer]
          · simp only [or_true, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
      cases hFa : q.ids.find a with
      | none =>
        have hwA0 : wA.val = 0 := by rw [hwAV, hFa]
        cases hFb : q.ids.find b with
        | none =>
          have hwB0 : wB.val = 0 := by rw [hwBV, hFb]
          have hSurv : qRes.survives = true := by
            dsimp only [qRes, EX44.query, EX44.route, failurePair]
            have hTa : (R.fetch (.translate a)).value = none := hFa
            have hTb : (R.fetch (.translate b)).value = none := hFb
            have hTt : (R.fetch (.translate t)).value = some xDense := hFt
            rw [withID_run_some, hTa, withID_run_some, hTb, EX44.Plan.fast_value, hTt]
            dsimp only [EX44.routeRetained, EX44.Fails]
            simp only [reduceCtorEq, or_self, ↓reduceIte, EX44.Plan.stop_value, EX44.answer]
          obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hc00 hwA0 hwB0
          exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
        | some bDense =>
          have hwBVal : wB.val = bDense.val + 1 := by simpa [hFb] using hwBV
          by_cases hb0 : bDense.val = 0
          · have hbRoot : bDense = q.slot r hrReach := Fin.ext (hb0.trans hSourceZero.symm)
            have hwB1 : wB.val = 1 := by rw [hwBVal, hb0]
            have hSurv := hSurvFail none (some bDense) (Or.inr (Or.inl (congrArg some hbRoot))) hFa hFb
            obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hcFail2 (Or.inr (Or.inr (Or.inl hwB1)))
            exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
          · have hwB2 : 2 ≤ wB.val := by
              rw [hwBVal]; exact Nat.succ_le_succ (Nat.pos_of_ne_zero hb0)
            have hwBSub : wB.val - 1 = bDense.val := by rw [hwBVal]; exact Nat.add_sub_cancel _ 1
            have hbNeRoot : bDense ≠ q.slot r hrReach := fun e => hb0 ((congrArg Fin.val e).trans hSourceZero)
            by_cases hbx : bDense = xDense
            · have hSubX : wB.val - 1 = xW.val := by rw [hwBSub, hxWV, hbx]
              have hSurv := hSurvFail none (some bDense) (Or.inr (Or.inr (Or.inr (congrArg some hbx)))) hFa hFb
              obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hcFail2 (Or.inr (Or.inr (Or.inr ⟨hwB2, hSubX⟩)))
              exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
            · have hSubX : wB.val - 1 ≠ xW.val := by rw [hwBSub, hxWV]; intro e; exact hbx (Fin.ext e)
              have hSurv : qRes.survives = !(q.reader.isAncestor bDense xDense) := by
                dsimp only [qRes, EX44.query, EX44.route, failurePair]
                have hTa : (R.fetch (.translate a)).value = none := hFa
                have hTb : (R.fetch (.translate b)).value = some bDense := hFb
                have hTt : (R.fetch (.translate t)).value = some xDense := hFt
                rw [withID_run_some, hTa, withID_run_some, hTb, EX44.Plan.fast_value, hTt, hRSource]
                dsimp only [EX44.routeRetained, EX44.Fails]
                have hnR : ¬ ((some (q.slot r hrReach) : Option (Fin q.count)) = none ∨
                    some (q.slot r hrReach) = some bDense) := by
                  simp only [reduceCtorEq, Option.some.injEq, false_or]; exact Ne.symm hbNeRoot
                have hnX : ¬ ((some xDense : Option (Fin q.count)) = none ∨ some xDense = some bDense) := by
                  simp only [reduceCtorEq, Option.some.injEq, false_or]; exact Ne.symm hbx
                rw [ite_eq_right hnR, ite_eq_right hnX, EX44.Plan.stop_value]
                dsimp only [EX44.answer, EX44.testOne]
                rw [EX44.Plan.fast_value]
                have hAncVal : (R.fetch (.ancestor bDense xDense)).value = q.reader.isAncestor bDense xDense := rfl
                rw [hAncVal, EX44.Plan.stop_value]
              obtain ⟨s6, k2, hk2, hs2, h6pc, h6r1, h6x⟩ := hc0B hwA0 hwB2 hSubX
              obtain ⟨tState, k6, hk6, hs6, htpc⟩ := hTail1 bDense (reg s6 1) xW s6 h6pc (h6r1.trans hwBSub) h6x hxWV
              exact hFinish (k0 + k2 + k6) (by omega) ((hs0.append hs2).append hs6) (by rw [htpc, hSurv])
      | some aDense =>
        have hwAVal : wA.val = aDense.val + 1 := by simpa [hFa] using hwAV
        by_cases ha0 : aDense.val = 0
        · have haRoot : aDense = q.slot r hrReach := Fin.ext (ha0.trans hSourceZero.symm)
          have hwA1 : wA.val = 1 := by rw [hwAVal, ha0]
          have hSurv := hSurvFail (some aDense) (q.ids.find b) (Or.inl (congrArg some haRoot)) hFa rfl
          obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hcFail2 (Or.inl hwA1)
          exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
        · have hwA2 : 2 ≤ wA.val := by
            rw [hwAVal]; exact Nat.succ_le_succ (Nat.pos_of_ne_zero ha0)
          have hwASub : wA.val - 1 = aDense.val := by rw [hwAVal]; exact Nat.add_sub_cancel _ 1
          have haNeRoot : aDense ≠ q.slot r hrReach := fun e => ha0 ((congrArg Fin.val e).trans hSourceZero)
          by_cases hax : aDense = xDense
          · have hSubX : wA.val - 1 = xW.val := by rw [hwASub, hxWV, hax]
            have hSurv := hSurvFail (some aDense) (q.ids.find b) (Or.inr (Or.inr (Or.inl (congrArg some hax)))) hFa rfl
            obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hcFail2 (Or.inr (Or.inl ⟨hwA2, hSubX⟩))
            exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
          · have hSubAX : wA.val - 1 ≠ xW.val := by rw [hwASub, hxWV]; intro e; exact hax (Fin.ext e)
            cases hFb : q.ids.find b with
            | none =>
              have hwB0 : wB.val = 0 := by rw [hwBV, hFb]
              have hSurv : qRes.survives = !(q.reader.isAncestor aDense xDense) := by
                dsimp only [qRes, EX44.query, EX44.route, failurePair]
                have hTa : (R.fetch (.translate a)).value = some aDense := hFa
                have hTb : (R.fetch (.translate b)).value = none := hFb
                have hTt : (R.fetch (.translate t)).value = some xDense := hFt
                rw [withID_run_some, hTa, withID_run_some, hTb, EX44.Plan.fast_value, hTt, hRSource]
                dsimp only [EX44.routeRetained, EX44.Fails]
                have hnR : ¬ (some (q.slot r hrReach) = some aDense ∨
                    (some (q.slot r hrReach) : Option (Fin q.count)) = none) := by
                  simp only [Option.some.injEq, reduceCtorEq, or_false]; exact Ne.symm haNeRoot
                have hnX : ¬ (some xDense = some aDense ∨ (some xDense : Option (Fin q.count)) = none) := by
                  simp only [Option.some.injEq, reduceCtorEq, or_false]; exact Ne.symm hax
                rw [ite_eq_right hnR, ite_eq_right hnX, EX44.Plan.stop_value]
                dsimp only [EX44.answer, EX44.testOne]
                rw [EX44.Plan.fast_value]
                have hAncVal : (R.fetch (.ancestor aDense xDense)).value = q.reader.isAncestor aDense xDense := rfl
                rw [hAncVal, EX44.Plan.stop_value]
              obtain ⟨s6, k2, hk2, hs2, h6pc, h6r1, h6x⟩ := hcA0 hwA2 hSubAX hwB0
              obtain ⟨tState, k6, hk6, hs6, htpc⟩ := hTail1 aDense (reg s6 1) xW s6 h6pc (h6r1.trans hwASub) h6x hxWV
              exact hFinish (k0 + k2 + k6) (by omega) ((hs0.append hs2).append hs6) (by rw [htpc, hSurv])
            | some bDense =>
              have hwBVal : wB.val = bDense.val + 1 := by simpa [hFb] using hwBV
              by_cases hb0 : bDense.val = 0
              · have hbRoot : bDense = q.slot r hrReach := Fin.ext (hb0.trans hSourceZero.symm)
                have hwB1 : wB.val = 1 := by rw [hwBVal, hb0]
                have hSurv := hSurvFail (some aDense) (some bDense) (Or.inr (Or.inl (congrArg some hbRoot))) hFa hFb
                obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hcFail2 (Or.inr (Or.inr (Or.inl hwB1)))
                exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
              · have hwB2 : 2 ≤ wB.val := by
                  rw [hwBVal]; exact Nat.succ_le_succ (Nat.pos_of_ne_zero hb0)
                have hwBSub : wB.val - 1 = bDense.val := by rw [hwBVal]; exact Nat.add_sub_cancel _ 1
                have hbNeRoot : bDense ≠ q.slot r hrReach := fun e => hb0 ((congrArg Fin.val e).trans hSourceZero)
                by_cases hbx : bDense = xDense
                · have hSubBX : wB.val - 1 = xW.val := by rw [hwBSub, hxWV, hbx]
                  have hSurv := hSurvFail (some aDense) (some bDense) (Or.inr (Or.inr (Or.inr (congrArg some hbx)))) hFa hFb
                  obtain ⟨tState, k2, hk2, hs2, htpc⟩ := hcFail2 (Or.inr (Or.inr (Or.inr ⟨hwB2, hSubBX⟩)))
                  exact hFinish (k0 + k2) (by omega) (hs0.append hs2) (by rw [htpc, hSurv]; rfl)
                · have hSubBX : wB.val - 1 ≠ xW.val := by rw [hwBSub, hxWV]; intro e; exact hbx (Fin.ext e)
                  obtain ⟨s3, k2, hk2, hs2, h3pc, _, h3AD, h3BD, h3XD⟩ := hcAB hwA2 hSubAX hwB2 hSubBX
                  obtain ⟨aW, haW, haWV⟩ : ∃ w, s3.data[slADense]? = some w ∧ w.val = aDense.val := by
                    cases hw : s3.data[slADense]? with
                    | none => simp [hw] at h3AD
                    | some w => exact ⟨w, rfl, by simpa [hw, hwASub] using h3AD⟩
                  obtain ⟨bW, hbW, hbWV⟩ : ∃ w, s3.data[slBDense]? = some w ∧ w.val = bDense.val := by
                    cases hw : s3.data[slBDense]? with
                    | none => simp [hw] at h3BD
                    | some w => exact ⟨w, rfl, by simpa [hw, hwBSub] using h3BD⟩
                  obtain ⟨tState, k3, hk3, hs3, htpc⟩ := runFromPC3 hI hWork hTag progress injRank q originalRows
                    hRows rows childOK inv Hdr hISz hqLe hRootSz hMapEq hRangesValid hHead hParent hDepth
                    hOrigOfEntry hEntry hStop cStart hc0 hcStep hcSlice hcItems recs aDense bDense xDense
                    aW bW xW s3 h3pc haW hbW h3XD haWV hbWV hxWV
                  have hSurvEq : qRes.survives =
                      ((EX44.answer ((EX44.routePair aDense bDense xDense).run R).value).run R).value := by
                    dsimp only [qRes, EX44.query, EX44.route, failurePair]
                    have hTa : (R.fetch (.translate a)).value = some aDense := hFa
                    have hTb : (R.fetch (.translate b)).value = some bDense := hFb
                    have hTt : (R.fetch (.translate t)).value = some xDense := hFt
                    rw [withID_run_some, hTa, withID_run_some, hTb, EX44.Plan.fast_value, hTt, hRSource]
                    dsimp only [EX44.routeRetained, EX44.Fails]
                    have hnR : ¬ (some (q.slot r hrReach) = some aDense ∨
                        some (q.slot r hrReach) = some bDense) := by
                      simp only [Option.some.injEq]
                      intro hOr
                      rcases hOr with hE | hE
                      · exact haNeRoot hE.symm
                      · exact hbNeRoot hE.symm
                    have hnX : ¬ (some xDense = some aDense ∨ some xDense = some bDense) := by
                      simp only [Option.some.injEq]
                      intro hOr
                      rcases hOr with hE | hE
                      · exact hax hE.symm
                      · exact hbx hE.symm
                    rw [ite_eq_right hnR, ite_eq_right hnX]
                  exact hFinish (k0 + k2 + k3) (by omega) ((hs0.append hs2).append hs3) (by rw [htpc, hSurvEq])

end EndToEndSpec

end PaperB.RamOracleQuery
