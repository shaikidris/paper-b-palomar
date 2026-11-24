module

public import PaperB.SealedBuild
public import PaperB.OracleSealedIndexLayout
public import PaperB.RamFamilyForestLoop
public import PaperB.RamStaticReaderBridge
public import PaperB.RamBuildPrefix

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.2 Sealed Index Packer (`RamSealedPacker.lean`):

Single fixed 16-register Word-RAM program (`sealedPackProgram` /
`sealedPackAndShiftProgram`) depending ONLY on `(bits, inputCap, workCap)` that
packs:
1. 16-word sealed header `header[0..15]` at `sealedBase + 0 .. + 15` using
   **0-based offsets within the sealed array `I`** (`hdrTotalWords = totalWords`),
2. global static tables (`origToDense`, `denseToOrig`, and `domParent`..`childIds`
   from `[3*n .. 4*n + Q)` and `[treeBase .. treeBase + 11 * Q)`),
3. `ownerDesc[0..Q-1]` (`10 * Q` words) plus contiguous per-owner `WordColumns`
   (`forestUsed ≤ 38 * n`) and per-owner exit summary banks
   (`[exitDepth (N_d), exitStored (18 * N_d), exitPrior (6 * n_d)]`, `exitUsed ≤ 48 * n`)
   using **0-based offsets within `I`**.

Total retained length `totalWords ≤ 128 * n` (`retainedLinearFactor * n`), running
in `O(n + m + 1)` instructions with peak words `inputCap + workCap + 16`, and
producing `ValidSealedOracleIndex g r I` via
`StaticReaderBridge.validSealedOracleIndex`.
-/

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

theorem hdrHead_eq : hdrHead = 0 := rfl
theorem hdrDomParent_eq : hdrDomParent = 1 := rfl
theorem hdrDomDepth_eq : hdrDomDepth = 2 := rfl
theorem hdrOrigToDense_eq : hdrOrigToDense = 3 := rfl
theorem hdrN_eq : hdrN = 4 := rfl
theorem hdrQCount_eq : hdrQCount = 5 := rfl
theorem hdrDenseToOrig_eq : hdrDenseToOrig = 6 := rfl
theorem hdrEntry_eq : hdrEntry = 7 := rfl
theorem hdrStop_eq : hdrStop = 8 := rfl
theorem hdrOrigOfEntry_eq : hdrOrigOfEntry = 9 := rfl
theorem hdrChildStart_eq : hdrChildStart = 10 := rfl
theorem hdrChildEntries_eq : hdrChildEntries = 11 := rfl
theorem hdrChildStops_eq : hdrChildStops = 12 := rfl
theorem hdrChildIds_eq : hdrChildIds = 13 := rfl
theorem hdrOwnerDesc_eq : hdrOwnerDesc = 14 := rfl
theorem hdrTotalWords_eq : hdrTotalWords = 15 := rfl
theorem oracleHeaderSize_eq : oracleHeaderSize = 16 := rfl
theorem descN_eq : descN = 0 := rfl
theorem descDict_eq : descDict = 1 := rfl
theorem descBackFst_eq : descBackFst = 2 := rfl
theorem descBackSnd_eq : descBackSnd = 3 := rfl
theorem descLabels_eq : descLabels = 4 := rfl
theorem descFEntry_eq : descFEntry = 5 := rfl
theorem descFStop_eq : descFStop = 6 := rfl
theorem descExitDepth_eq : descExitDepth = 7 := rfl
theorem descExitStored_eq : descExitStored = 8 := rfl
theorem descExitPrior_eq : descExitPrior = 9 := rfl
theorem ownerDescStride_eq : ownerDescStride = 10 := rfl
theorem retainedLinearFactor_eq : retainedLinearFactor = 128 := rfl

/-! ### 1. Exact 0-Based Sealed Offsets and `≤ 128 * n` Retained Size Bounds -/

section SealedLayoutBudget

def sealedOrigToDenseOff : Nat := 16
def sealedDenseToOrigOff (n : Nat) : Nat := 16 + n
def sealedDomParentOff (n Q : Nat) : Nat := 16 + n + Q
def sealedDomDepthOff (n Q : Nat) : Nat := 16 + n + 2 * Q
def sealedHeadOff (n Q : Nat) : Nat := 16 + n + 3 * Q
def sealedEntryOff (n Q : Nat) : Nat := 16 + n + 4 * Q
def sealedStopOff (n Q : Nat) : Nat := 16 + n + 5 * Q
def sealedOrigOfEntryOff (n Q : Nat) : Nat := 16 + n + 6 * Q
def sealedChildStartOff (n Q : Nat) : Nat := 16 + n + 7 * Q
def sealedChildEntriesOff (n Q : Nat) : Nat := 16 + n + 8 * Q + 1
def sealedChildStopsOff (n Q : Nat) : Nat := 16 + n + 9 * Q + 1
def sealedChildIdsOff (n Q : Nat) : Nat := 16 + n + 10 * Q + 1
def sealedOwnerDescOff (n Q : Nat) : Nat := 16 + n + 11 * Q
def sealedInitArenaOff (n Q : Nat) : Nat := 16 + n + 21 * Q

theorem foldl_childSlice_aux {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    ∀ k ≤ dense.length,
      (List.range k).foldl (fun acc d => acc + (S.childStart (d + 1) - S.childStart d)) 0 =
        S.childStart k - S.childStart 0 := by
  intro k
  induction k with
  | zero =>
    intro _
    simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih (Nat.le_of_lt hk)]
    have h0k := S.childStart_mono 0 k (Nat.zero_le k) (Nat.le_of_lt hk)
    have hks := S.childStart_mono k (k + 1) (Nat.le_succ k) hk
    omega

theorem sum_childSlice_length {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) :
    (List.range dense.length).foldl
        (fun acc d =>
          if h : d < dense.length then acc + (S.childSlice ⟨d, h⟩).length else acc) 0 =
      dense.length - 1 := by
  have hCongr :
      (List.range dense.length).foldl
          (fun acc d =>
            if h : d < dense.length then acc + (S.childSlice ⟨d, h⟩).length else acc) 0 =
        (List.range dense.length).foldl
          (fun acc d => acc + (S.childStart (d + 1) - S.childStart d)) 0 := by
    have hEq : ∀ xs : List Nat,
        (∀ d ∈ xs, d < dense.length) →
        ∀ acc,
          xs.foldl (fun a d => if h : d < dense.length then a + (S.childSlice ⟨d, h⟩).length else a) acc =
          xs.foldl (fun a d => a + (S.childStart (d + 1) - S.childStart d)) acc := by
      intro xs
      induction xs with
      | nil => intro _ acc; rfl
      | cons x xs ih =>
        intro hxs acc
        have hx : x < dense.length := hxs x (by simp)
        simp only [List.foldl_cons, dite_eq_left hx]
        have hLen : (S.childSlice ⟨x, hx⟩).length = S.childStart (x + 1) - S.childStart x := by
          simp [StaticTreeSlice.childSlice]
        rw [hLen]
        exact ih (fun y hy => hxs y (by simp [hy])) _
    exact hEq (List.range dense.length) (fun d hd => List.mem_range.mp hd) 0
  rw [hCongr, foldl_childSlice_aux S dense.length (Nat.le_refl _), S.childStart_zero,
    S.childStart_end, Nat.sub_zero]

theorem sealedTotalWords_le_128n {n Q forestWords exitWords : Nat}
    (hn : 1 ≤ n) (hQn : Q ≤ n)
    (hF : forestWords ≤ 38 * n) (hE : exitWords ≤ 48 * n) :
    sealedInitArenaOff n Q + forestWords + exitWords ≤ retainedLinearFactor * n := by
  unfold sealedInitArenaOff retainedLinearFactor
  omega

end SealedLayoutBudget

/-! ### 2. Abstract Exit Arena Contract and Transport to `ValidSealedOracleIndex` -/

section ArenaTransport

/-- Abstract contract for owner `d`'s packed `WordColumns` (from
`RamFamilyForestLoop`) and exit summary arrays `[exitDepth, exitStored, exitPrior]`
already placed inside `[exitArenaBase .. exitArenaBase + exitUsed)` and pointed
to by `forestPtrsBase + 6 * d + {0..5}` and `exitPtrsBase + 3 * d + {0..2}`. -/
def OwnerExitArenaAt {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (forestPtrsBase forestArenaBase forestUsed exitPtrsBase exitArenaBase exitUsed : Nat)
    (data : Array (Word bits)) : Prop :=
  let n_d := 1 + (S.childSlice d).length
  if large : 3 ≤ n_d then
    let H := S.ramQuotient d
    ∃ (pH : ForestDictionary.Rows H)
      (dataH : Array (Vertex H)) (sizeH : dataH.size = H.vertexCount) (rankH : Vertex H → Nat)
      (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH large)
      (wCols : WordColumns bits) (endpoints : Nat)
      (R : Region bits data.size) (F : JumpForest) (ref : Nat → CheckedFold.Stored)
      (wFit : Width bits (max R.slots endpoints))
      (_ok : Occupied data R F ref wFit)
      (prior : Array (Option Values)) (hb : BaseBound (max R.slots endpoints) prior)
      (B : BaseView prior.size data.size) (_hPlaced : Placed wFit prior hb data B)
      (fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 : Nat),
      let D := ((data[fp0]?).map Fin.val).getD 0
      (∀ i j : Fin H.vertexCount, i.val < j.val →
        rankH (EX24.PreparedSweep.orderedVertexAt dataH sizeH i) <
        rankH (EX24.PreparedSweep.orderedVertexAt dataH sizeH j)) ∧
      (∀ v : Vertex H, ∃ i : Fin H.vertexCount,
        EX24.PreparedSweep.orderedVertexAt dataH sizeH i = v) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rankH u < rankH v) ∧
      (data[forestPtrsBase + 6 * d.val]?).map Fin.val = some fp0 ∧
      (data[forestPtrsBase + 6 * d.val + 1]?).map Fin.val = some fp1 ∧
      (data[forestPtrsBase + 6 * d.val + 2]?).map Fin.val = some fp2 ∧
      (data[forestPtrsBase + 6 * d.val + 3]?).map Fin.val = some fp3 ∧
      (data[forestPtrsBase + 6 * d.val + 4]?).map Fin.val = some fp4 ∧
      (data[forestPtrsBase + 6 * d.val + 5]?).map Fin.val = some fp5 ∧
      fp1 = fp0 + (1 + 3 * D) ∧
      fp2 = fp1 + (n_d + 1) ∧
      fp3 = fp2 + (n_d + 1) ∧
      fp4 = fp3 + n_d ∧
      fp5 = fp4 + wCols.entry.size ∧
      wCols.dictionary.size = 1 + 3 * D ∧
      wCols.back.tagAndFirst.size = n_d + 1 ∧
      wCols.back.second.size = n_d + 1 ∧
      wCols.labels.size = n_d ∧
      wCols.stop.size = wCols.entry.size ∧
      wCols.entry.size ≤ n_d + 1 ∧
      wCols.wordCount ≤ 19 * n_d ∧
      forestArenaBase ≤ fp0 ∧
      fp5 + wCols.stop.size ≤ forestArenaBase + forestUsed ∧
      SliceAt data fp0 wCols.dictionary ∧
      SliceAt data fp1 wCols.back.tagAndFirst ∧
      SliceAt data fp2 wCols.back.second ∧
      SliceAt data fp3 wCols.labels ∧
      SliceAt data fp4 wCols.entry ∧
      SliceAt data fp5 wCols.stop ∧
      FlatPairDictionary.Represents wCols.dictionary (ofOrderedReader ordResH) ∧
      (∀ a v, wCols.known a v = (ofOrderedReader ordResH).known a v) ∧
      (∀ j (P : CutPair H),
        wCols.back.read j = some (encodeBackPair (some P)) ↔
          (ofOrderedReader ordResH).back[j]? = some (some P)) ∧
      (∀ v : Vertex H, (EX24.PreparedSweep.orderedConfig pH large).vertexIndex v = v.val) ∧
      (∀ y : Fin H.vertexCount, wCols.labelAt y.val < F.size ∧ wCols.labelAt y.val < wCols.entry.size) ∧
      (∀ (P : CutPair H), P.fst < P.snd → ∀ aNode : Nat, checkedHit ordResH P = some aNode →
        aNode < wCols.entry.size ∧ aNode < wCols.stop.size ∧
        aNode < F.size ∧ aNode < wCols.back.tagAndFirst.size ∧
        aNode < wCols.back.second.size) ∧
      (data[exitPtrsBase + 3 * d.val]?).map Fin.val = some ep0 ∧
      (data[exitPtrsBase + 3 * d.val + 1]?).map Fin.val = some ep1 ∧
      (data[exitPtrsBase + 3 * d.val + 2]?).map Fin.val = some ep2 ∧
      exitArenaBase ≤ ep0 ∧ ep0 + wCols.entry.size ≤ exitArenaBase + exitUsed ∧
      exitArenaBase ≤ ep1 ∧ ep1 + 18 * wCols.entry.size ≤ exitArenaBase + exitUsed ∧
      exitArenaBase ≤ ep2 ∧ ep2 + 6 * n_d ≤ exitArenaBase + exitUsed ∧
      R.slots = wCols.entry.size ∧
      prior.size = n_d ∧
      R.base.val = ep1 ∧
      B.start = ep2 ∧
      (∀ x : Fin R.slots, (R.depthAddr x).val = ep0 + x.val) ∧
      (∀ (P : CutPair H), P.fst < P.snd → ∀ aNode : Nat, checkedHit ordResH P = some aNode →
        ∀ y : Vertex H, H.ProperLoss P y →
          let u := wCols.labelAt y.val
          let dDepth := depthAt data R aNode
          (foldStored data R wFit.tags u dDepth).steps ≤ 3 * ceilLog2 (g.vertexCount + 2) ∧
          ∀ hPrior : y.val < prior.size,
            (PriorBase.run data R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x0 =
              ExitSummary.summary ((lemma22ExitTails H P P.fst y).map (denseRank S)) ∧
            (PriorBase.run data R wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x1 =
              ExitSummary.summary ((lemma22ExitTails H P P.snd y).map (denseRank S)))
  else True

private theorem sliceAt_transport {bits : Nat}
    {src dst : Array (Word bits)} {sBase dBase : Nat} {vals : Array (Word bits)}
    (hSrc : SliceAt src sBase vals) (hFit : dBase + vals.size ≤ dst.size)
    (hCopy : ∀ j < vals.size, dst[dBase + j]? = src[sBase + j]?) :
    SliceAt dst dBase vals := by
  refine ⟨hFit, fun j hj => ?_⟩
  rw [hCopy j hj]
  exact hSrc.2 j hj

theorem depthAt_exact {bits endpoints : Nat} {mem : Array (Word bits)}
    {R : Region bits mem.size} {F : JumpForest} {ref : Nat → CheckedFold.Stored}
    {w : Width bits (max R.slots endpoints)}
    (ok : Occupied mem R F ref w) {u : Nat} (hu : u < F.size) :
    depthAt mem R u = F.depthOf u := by
  have h : u < R.slots := ok.size_eq.symm ▸ hu
  simpa only [depthAt, dite_eq_left h] using ok.depth ⟨u, h⟩

private theorem ownerExitArenaAt_slices {bits : Nat}
    {srcData I : Array (Word bits)} {wCols : WordColumns bits}
    {nD dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
      fp0 fp1 fp2 fp3 fp4 fp5 : Nat}
    (hwDict : wCols.dictionary.size = fp1 - fp0)
    (hwBF : wCols.back.tagAndFirst.size = nD + 1)
    (hwBS : wCols.back.second.size = nD + 1)
    (hwLab : wCols.labels.size = nD)
    (hwStop : wCols.stop.size = wCols.entry.size)
    (hFp01 : fp0 ≤ fp1)
    (hD2 : fp2 = fp1 + (nD + 1)) (hD3 : fp3 = fp2 + (nD + 1))
    (hD4 : fp4 = fp3 + nD) (hD5 : fp5 = fp4 + wCols.entry.size)
    (hP_bf : backFstPtr = dictPtr + (fp1 - fp0))
    (hP_bs : backSndPtr = dictPtr + (fp2 - fp0))
    (hP_lb : labelsPtr = dictPtr + (fp3 - fp0))
    (hP_fe : fEntryPtr = dictPtr + (fp4 - fp0))
    (hP_fs : fStopPtr = dictPtr + (fp5 - fp0))
    (hFitFor : dictPtr + ((fp5 - fp0) + wCols.entry.size) ≤ I.size)
    (hCpFor : ∀ k < (fp5 - fp0) + wCols.entry.size, I[dictPtr + k]? = srcData[fp0 + k]?)
    (hSlD : SliceAt srcData fp0 wCols.dictionary)
    (hSlBF : SliceAt srcData fp1 wCols.back.tagAndFirst)
    (hSlBS : SliceAt srcData fp2 wCols.back.second)
    (hSlLb : SliceAt srcData fp3 wCols.labels)
    (hSlFE : SliceAt srcData fp4 wCols.entry)
    (hSlFS : SliceAt srcData fp5 wCols.stop) :
    SliceAt I dictPtr wCols.dictionary ∧
    SliceAt I backFstPtr wCols.back.tagAndFirst ∧
    SliceAt I backSndPtr wCols.back.second ∧
    SliceAt I labelsPtr wCols.labels ∧
    SliceAt I fEntryPtr wCols.entry ∧
    SliceAt I fStopPtr wCols.stop := by
  have hbD : dictPtr + wCols.dictionary.size ≤ I.size := by rw [hwDict]; omega
  have hbBF : backFstPtr + wCols.back.tagAndFirst.size ≤ I.size := by rw [hwBF]; omega
  have hbBS : backSndPtr + wCols.back.second.size ≤ I.size := by rw [hwBS]; omega
  have hbLb : labelsPtr + wCols.labels.size ≤ I.size := by rw [hwLab]; omega
  have hbFE : fEntryPtr + wCols.entry.size ≤ I.size := by omega
  have hbFS : fStopPtr + wCols.stop.size ≤ I.size := by rw [hwStop]; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sliceAt_transport hSlD hbD fun j hj => hCpFor j (by rw [hwDict] at hj; omega)
  · refine sliceAt_transport hSlBF hbBF fun j hj => ?_
    rw [hP_bf, Nat.add_assoc, hCpFor ((fp1 - fp0) + j) (by rw [hwBF] at hj; omega)]
    exact congrArg (fun idx => srcData[idx]?) (by omega)
  · refine sliceAt_transport hSlBS hbBS fun j hj => ?_
    rw [hP_bs, Nat.add_assoc, hCpFor ((fp2 - fp0) + j) (by rw [hwBS] at hj; omega)]
    exact congrArg (fun idx => srcData[idx]?) (by omega)
  · refine sliceAt_transport hSlLb hbLb fun j hj => ?_
    rw [hP_lb, Nat.add_assoc, hCpFor ((fp3 - fp0) + j) (by rw [hwLab] at hj; omega)]
    exact congrArg (fun idx => srcData[idx]?) (by omega)
  · refine sliceAt_transport hSlFE hbFE fun j hj => ?_
    rw [hP_fe, Nat.add_assoc, hCpFor ((fp4 - fp0) + j) (by omega)]
    exact congrArg (fun idx => srcData[idx]?) (by omega)
  · refine sliceAt_transport hSlFS hbFS fun j hj => ?_
    rw [hP_fs, Nat.add_assoc, hCpFor ((fp5 - fp0) + j) (by rw [hwStop] at hj; omega)]
    exact congrArg (fun idx => srcData[idx]?) (by omega)

/-- Transport an owner's `OwnerExitArenaAt` slice in `srcData` (along with its
10-word `ownerDesc[d]` and copied slices in `I`) into a `RamQuotientOwnerRecord`. -/
noncomputable def ownerExitArenaAt_to_record {bits : Nat}
    {mem srcData I : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (Hdr : StaticHeaderSpec I g.vertexCount dense.length)
    {forestPtrsBase forestArenaBase forestUsed exitPtrsBase exitArenaBase exitUsed : Nat}
    (d : Fin dense.length)
    (hArena : OwnerExitArenaAt S d forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed srcData)
    (nD : Nat) (hnD : nD = 1 + (S.childSlice d).length)
    (dictPtr backFstPtr backSndPtr labelsPtr fEntryPtr fStopPtr
      exitDepthPtr exitStoredPtr exitPriorPtr : Nat)
    (hFits : Hdr.ownerDescBase + ownerDescStride * d.val + ownerDescStride ≤ I.size)
    (hIlt : I.size ≤ 2 ^ bits)
    (hDescN : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descN]?).map Fin.val = some nD)
    (hDescDict : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descDict]?).map Fin.val = some dictPtr)
    (hDescBF : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descBackFst]?).map Fin.val = some backFstPtr)
    (hDescBS : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descBackSnd]?).map Fin.val = some backSndPtr)
    (hDescLb : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descLabels]?).map Fin.val = some labelsPtr)
    (hDescFE : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descFEntry]?).map Fin.val = some fEntryPtr)
    (hDescFS : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descFStop]?).map Fin.val = some fStopPtr)
    (hDescED : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descExitDepth]?).map Fin.val = some exitDepthPtr)
    (hDescES : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descExitStored]?).map Fin.val = some exitStoredPtr)
    (hDescEP : (I[Hdr.ownerDescBase + ownerDescStride * d.val + descExitPrior]?).map Fin.val = some exitPriorPtr)
    (hLargeCopy : ∀ (fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 N_d D : Nat),
      (srcData[forestPtrsBase + 6 * d.val]?).map Fin.val = some fp0 →
      (srcData[forestPtrsBase + 6 * d.val + 1]?).map Fin.val = some fp1 →
      (srcData[forestPtrsBase + 6 * d.val + 2]?).map Fin.val = some fp2 →
      (srcData[forestPtrsBase + 6 * d.val + 3]?).map Fin.val = some fp3 →
      (srcData[forestPtrsBase + 6 * d.val + 4]?).map Fin.val = some fp4 →
      (srcData[forestPtrsBase + 6 * d.val + 5]?).map Fin.val = some fp5 →
      ((srcData[fp0]?).map Fin.val).getD 0 = D →
      fp1 = fp0 + (1 + 3 * D) →
      fp2 = fp1 + (nD + 1) →
      fp3 = fp2 + (nD + 1) →
      fp4 = fp3 + nD →
      fp5 = fp4 + N_d →
      (srcData[exitPtrsBase + 3 * d.val]?).map Fin.val = some ep0 →
      (srcData[exitPtrsBase + 3 * d.val + 1]?).map Fin.val = some ep1 →
      (srcData[exitPtrsBase + 3 * d.val + 2]?).map Fin.val = some ep2 →
      backFstPtr = dictPtr + (fp1 - fp0) ∧
      backSndPtr = dictPtr + (fp2 - fp0) ∧
      labelsPtr = dictPtr + (fp3 - fp0) ∧
      fEntryPtr = dictPtr + (fp4 - fp0) ∧
      fStopPtr = dictPtr + (fp5 - fp0) ∧
      dictPtr + ((fp5 - fp0) + N_d) ≤ I.size ∧
      exitDepthPtr + N_d ≤ I.size ∧
      exitStoredPtr + 18 * N_d ≤ I.size ∧
      exitPriorPtr + 6 * nD ≤ I.size ∧
      (∀ k < (fp5 - fp0) + N_d, I[dictPtr + k]? = srcData[fp0 + k]?) ∧
      (∀ k < N_d, I[exitDepthPtr + k]? = srcData[ep0 + k]?) ∧
      (∀ k < 18 * N_d, I[exitStoredPtr + k]? = srcData[ep1 + k]?) ∧
      (∀ k < 6 * nD, I[exitPriorPtr + k]? = srcData[ep2 + k]?)) :
    RamQuotientOwnerRecord S I Hdr d where
  nD := nD
  nD_eq := hnD
  dictPtr := dictPtr
  backFstPtr := backFstPtr
  backSndPtr := backSndPtr
  labelsPtr := labelsPtr
  fEntryPtr := fEntryPtr
  fStopPtr := fStopPtr
  exitDepthPtr := exitDepthPtr
  exitStoredPtr := exitStoredPtr
  exitPriorPtr := exitPriorPtr
  descBase := Hdr.ownerDescBase + ownerDescStride * d.val
  descBase_val := rfl
  descFits := hFits
  hDescN := hDescN
  hDescDict := hDescDict
  hDescBackFst := hDescBF
  hDescBackSnd := hDescBS
  hDescLabels := hDescLb
  hDescFEntry := hDescFE
  hDescFStop := hDescFS
  hDescExitDepth := hDescED
  hDescExitStored := hDescES
  hDescExitPrior := hDescEP
  large_spec := by
    dsimp only
    intro large
    dsimp only [OwnerExitArenaAt] at hArena
    have hL' : 3 ≤ 1 + (S.childSlice d).length := large
    rw [dite_eq_left hL'] at hArena
    obtain ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R0, F, ref, wFit, ok0,
      prior, hb, B0, hPlaced0, fp0, fp1, fp2, fp3, fp4, fp5, ep0, ep1, ep2, hP⟩ := hArena
    rcases hP with ⟨incH, covH, rArcH, hfp0, hfp1, hfp2, hfp3, hfp4, hfp5,
      hD1, hD2, hD3, hD4, hD5, hwDict, hwBF, hwBS, hwLab, hwStop, hwLe, hwWc,
      hFA1, hFA2, hSlD, hSlBF, hSlBS, hSlLb, hSlFE, hSlFS, hRep, hKnown, hBackR,
      hVIdx, hLabB, hHitB, hep0, hep1, hep2, hEA0a, hEA0b, hEA1a, hEA1b, hEA2a, hEA2b,
      hRSlots, hPriorSz, hRBase0, hBStart0, hDepAddr0, hExitSpec0⟩
    have hD1' : fp1 = fp0 + (1 + 3 * ((srcData[fp0]?).map Fin.val).getD 0) := hD1
    have hD2' : fp2 = fp1 + (nD + 1) := by rw [hnD]; exact hD2
    have hD3' : fp3 = fp2 + (nD + 1) := by rw [hnD]; exact hD3
    have hD4' : fp4 = fp3 + nD := by rw [hnD]; exact hD4
    obtain ⟨hP_bf, hP_bs, hP_lb, hP_fe, hP_fs, hFitFor, hFitED, hFitES, hFitEP,
      hCpFor, hCpED, hCpES, hCpEP⟩ :=
      hLargeCopy fp0 fp1 fp2 fp3 fp4 fp5 ep0 ep1 ep2 wCols.entry.size
        (((srcData[fp0]?).map Fin.val).getD 0) hfp0 hfp1 hfp2 hfp3 hfp4 hfp5 rfl
        hD1' hD2' hD3' hD4' hD5 hep0 hep1 hep2
    have hwDict' : wCols.dictionary.size = fp1 - fp0 := by rw [hwDict]; omega
    have hwBF' : wCols.back.tagAndFirst.size = nD + 1 := by rw [hwBF, hnD]
    have hwBS' : wCols.back.second.size = nD + 1 := by rw [hwBS, hnD]
    have hwLab' : wCols.labels.size = nD := by rw [hwLab, hnD]
    obtain ⟨hSlD', hSlBF', hSlBS', hSlLb', hSlFE', hSlFS'⟩ :=
      ownerExitArenaAt_slices hwDict' hwBF' hwBS' hwLab' hwStop (by rw [hD1']; omega) hD2' hD3' hD4' hD5
        hP_bf hP_bs hP_lb hP_fe hP_fs hFitFor hCpFor hSlD hSlBF hSlBS hSlLb hSlFE hSlFS
    let R' : Region bits I.size :=
      { slots := R0.slots
        depthAddr := fun x => ⟨exitDepthPtr + x.val, by
          have hx := Nat.lt_of_lt_of_eq x.isLt hRSlots
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx exitDepthPtr) (Nat.le_trans hFitED hIlt)⟩
        depthMem := fun x => by
          dsimp only
          have hx := Nat.lt_of_lt_of_eq x.isLt hRSlots
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hx exitDepthPtr) hFitED
        base := ⟨exitStoredPtr, by
          have hEntryPos : 0 < wCols.entry.size :=
            Nat.lt_of_le_of_lt (Nat.zero_le _) (hLabB (S.ramQuotient d).root).2
          exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hFitES hIlt)⟩
        recordAddr := fun x => by
          dsimp only
          have hx := Nat.lt_of_lt_of_eq x.isLt hRSlots
          exact Nat.lt_of_lt_of_le (by omega) (Nat.le_trans hFitES hIlt)
        recordMem := fun x => by
          dsimp only
          have hx := Nat.lt_of_lt_of_eq x.isLt hRSlots
          exact Nat.lt_of_lt_of_le (by omega) hFitES }
    have ok' : Occupied I R' F ref wFit :=
      { size_eq := ok0.size_eq
        valid := ok0.valid
        depth := fun v => by
          have hv : v.val < wCols.entry.size := Nat.lt_of_lt_of_eq v.isLt hRSlots
          have hvI : exitDepthPtr + v.val < I.size :=
            Nat.lt_of_lt_of_le (Nat.add_lt_add_left hv exitDepthPtr) hFitED
          have hGet : (I[exitDepthPtr + v.val]?).map Fin.val =
              (srcData[ep0 + v.val]?).map Fin.val := congrArg (Option.map Fin.val) (hCpED v.val hv)
          have hI : (I[exitDepthPtr + v.val]?).map Fin.val =
              some (I[exitDepthPtr + v.val]'hvI).val := by
            rw [Array.getElem?_eq_getElem hvI, Option.map_some]
          have hvR := R0.depthMem v
          have hvE := hDepAddr0 v
          have hSrc : (srcData[ep0 + v.val]?).map Fin.val =
              some (srcData[(R0.depthAddr v).val]'hvR).val := by
            have hEqD : srcData[ep0 + v.val]? = srcData[(R0.depthAddr v).val]? :=
              congrArg (srcData[·]?) hvE.symm
            rw [hEqD, Array.getElem?_eq_getElem hvR, Option.map_some]
          have hVal := hI.symm.trans (hGet.trans hSrc)
          rw [Option.some.injEq] at hVal
          exact hVal.trans (ok0.depth v)
        parent_eq := ok0.parent_eq
        jump_eq := ok0.jump_eq
        maps := ok0.maps
        packed := fun v hr i => by
          have hv : v.val < wCols.entry.size := Nat.lt_of_lt_of_eq v.isLt hRSlots
          have hk : 18 * v.val + i.val < 18 * wCols.entry.size := by have := i.isLt; omega
          have hEq := hCpES (18 * v.val + i.val) hk
          have hIdxEq : I[R'.base.val + 18 * v.val + i.val]? =
              srcData[R0.base.val + 18 * v.val + i.val]? := by
            rw [show R'.base.val + 18 * v.val + i.val = exitStoredPtr + (18 * v.val + i.val) by dsimp [R']; omega,
              hEq, hRBase0, Nat.add_assoc]
          have hB1 : R'.base.val + 18 * v.val + i.val < I.size := by
            have hm := R'.recordMem v; have := i.isLt; omega
          have hB0 : R0.base.val + 18 * v.val + i.val < srcData.size := by
            have hm := R0.recordMem v; have := i.isLt; omega
          have hValEq : I[R'.base.val + 18 * v.val + i.val]'hB1 =
              srcData[R0.base.val + 18 * v.val + i.val]'hB0 :=
            Option.some.inj (by
              rw [← Array.getElem?_eq_getElem hB1, hIdxEq, Array.getElem?_eq_getElem hB0])
          exact hValEq.trans (ok0.packed v hr i) }
    have hPriorFits : exitPriorPtr + 6 * prior.size ≤ I.size := by
      rw [hPriorSz, ← hnD]; exact hFitEP
    let B' : BaseView prior.size I.size := ⟨exitPriorPtr, hPriorFits⟩
    have hPlaced' : Placed wFit prior hb I B' := by
      intro j
      have hj0 : j.val < 6 * prior.size := j.isLt
      have hj : j.val < 6 * nD := Nat.lt_of_lt_of_eq hj0 (by rw [hPriorSz, ← hnD])
      have hEq := hCpEP j.val hj
      have hB' : B'.start + j.val < I.size := by have := B'.fits; omega
      have hB0 : B0.start + j.val < srcData.size := by have := B0.fits; omega
      have hValEq : I[B'.start + j.val]'hB' = srcData[B0.start + j.val]'hB0 := by
        apply Option.some.inj
        have hp : srcData[ep2 + j.val]? = srcData[B0.start + j.val]? :=
          congrArg (fun k => srcData[k]?) (by omega)
        rw [← Array.getElem?_eq_getElem hB',
          show B'.start + j.val = exitPriorPtr + j.val from rfl, hEq, hp,
          Array.getElem?_eq_getElem hB0]
      exact hValEq.trans (hPlaced0 j)
    have hExitSpec' : ∀ (P : CutPair (S.ramQuotient d)), P.fst < P.snd →
        ∀ aNode : Nat, checkedHit ordResH P = some aNode →
        ∀ y : Vertex (S.ramQuotient d), (S.ramQuotient d).ProperLoss P y →
          let u := wCols.labelAt y.val
          let dDepth := depthAt I R' aNode
          (foldStored I R' wFit.tags u dDepth).steps ≤ 3 * ceilLog2 (g.vertexCount + 2) ∧
          ∀ hPrior : y.val < prior.size,
            (PriorBase.run I R' wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x0 =
              ExitSummary.summary ((lemma22ExitTails (S.ramQuotient d) P P.fst y).map (denseRank S)) ∧
            (PriorBase.run I R' wFit.tags prior ⟨y.val, hPrior⟩ u dDepth).x1 =
              ExitSummary.summary ((lemma22ExitTails (S.ramQuotient d) P P.snd y).map (denseRank S)) := by
      intro P hLt aNode hCh y hProper
      obtain ⟨hSteps0, hRun0⟩ := hExitSpec0 P hLt aNode hCh y hProper
      obtain ⟨_, _, haF, _, _⟩ := hHitB P hLt aNode hCh
      have huF : wCols.labelAt y.val < F.size := (hLabB y).1
      have hDepEq : depthAt I R' aNode = depthAt srcData R0 aNode := by
        rw [depthAt_exact ok' haF, depthAt_exact ok0 haF]
      have hFoldEq : foldStored I R' wFit.tags (wCols.labelAt y.val) (depthAt I R' aNode) =
          foldStored srcData R0 wFit.tags (wCols.labelAt y.val) (depthAt srcData R0 aNode) := by
        rw [hDepEq, foldStored_exact ok' huF, foldStored_exact ok0 huF]
      refine ⟨by rw [hFoldEq]; exact hSteps0, fun hPrior => ?_⟩
      obtain ⟨hx0, hx1⟩ := hRun0 hPrior
      have hRunEq : PriorBase.run I R' wFit.tags prior ⟨y.val, hPrior⟩ (wCols.labelAt y.val) (depthAt I R' aNode) =
          PriorBase.run srcData R0 wFit.tags prior ⟨y.val, hPrior⟩ (wCols.labelAt y.val) (depthAt srcData R0 aNode) := by
        simp only [PriorBase.run, hFoldEq]
      rw [hRunEq]
      exact ⟨hx0, hx1⟩
    exact ⟨pH, dataH, sizeH, rankH, ordResH, wCols, endpoints, R', F, ref, wFit, ok',
      prior, hb, B', hPlaced', incH, covH, rArcH, hSlD', hRep, hSlBF', hSlBS', hSlLb', hSlFE', hSlFS',
      hwLab, hwStop.symm, hwBF.trans hwBS.symm, hKnown, hBackR, hVIdx, hLabB, hHitB,
      hPriorSz, rfl, rfl, fun _ => rfl, hExitSpec'⟩

end ArenaTransport

/-! ### 3. Generic 16-Register Program Helpers and Reusable `copyLoopCode` -/

section RamPackHelpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

theorem step1 {code : Program L16} {input : Input L16} {s t : State L16}
    (hs : step code input s = some (.next t)) : Steps code input 1 s t :=
  Steps.cons hs (Steps.zero t)

def SlicePlaced (code : Program L16) (base : Nat)
    (sub : Program L16) : Prop :=
  ∀ (k : Nat) (hk : k < sub.size), code[base + k]? = some (sub[k]'hk)

private theorem SlicePlaced_of_eq {code : Program L16} {base : Nat} {sub : Program L16}
    (h : ∀ k : Fin sub.size, code[base + k.val]? = some (sub[k.val]'k.isLt)) :
    SlicePlaced code base sub :=
  fun k hk => h ⟨k, hk⟩

/-- 6-instruction forward copy loop: while `r11 < r13`, copies `data[r11]` to
`data[r12]`, increments `r11, r12`, and jumps to `loopPC`; on exit jumps to `exitPC`.
Uses ONLY `r11, r12, r13, r14`; preserves `rZero..r10` and `r15`. -/
def copyLoopCode (loopPC exitPC : Nat) : Program L16 :=
  #[.branchLt r11 r13 (loopPC + 1) exitPC,
    .loadData r14 r11,
    .storeData r12 r14,
    .add r11 r11 rOne,
    .add r12 r12 rOne,
    .goto loopPC]

private theorem copyLoopCode_size (loopPC exitPC : Nat) :
    (copyLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) loopPC exitPC).size = 6 := rfl

theorem copyLoop_slicePlaced {code : Program L16} {base loopPC exitPC : Nat}
    (h0 : code[base]? = some (.branchLt r11 r13 (loopPC + 1) exitPC))
    (h1 : code[base + 1]? = some (.loadData r14 r11))
    (h2 : code[base + 2]? = some (.storeData r12 r14))
    (h3 : code[base + 3]? = some (.add r11 r11 rOne))
    (h4 : code[base + 4]? = some (.add r12 r12 rOne))
    (h5 : code[base + 5]? = some (.goto loopPC)) :
    SlicePlaced code base (copyLoopCode loopPC exitPC) := by
  intro k hk
  have hk6 : k < 6 := by rw [copyLoopCode_size] at hk; exact hk
  match k with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | 5 => exact h5
  | k + 6 => omega

private theorem copyLoopCode_nonHalt (loopPC exitPC : Nat) :
    (copyLoopCode (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) loopPC exitPC).toList.all (@nonHalt bits L16) = true := rfl

theorem run_copyLoop {code : Program L16} {input : Input L16}
    {loopPC exitPC : Nat}
    (hPl : SlicePlaced code loopPC (copyLoopCode loopPC exitPC))
    (hExit : exitPC < code.size) (hFit : loopPC + 5 < code.size)
    (hBits : workCap < 2 ^ bits)
    {src₀ dst₀ len : Nat}
    (hSrcBound : src₀ + len ≤ workCap) (hDstBound : dst₀ + len ≤ workCap)
    (hSafe : dst₀ + len ≤ src₀ ∨ src₀ + len ≤ dst₀ ∨ dst₀ < src₀)
    {s₀ : State L16}
    (hPC : s₀.pc = loopPC) (hSz : s₀.data.size = workCap)
    (hOne : (reg s₀ rOne).val = 1)
    (hR11 : (reg s₀ r11).val = src₀) (hR12 : (reg s₀ r12).val = dst₀)
    (hR13 : (reg s₀ r13).val = src₀ + len) :
    ∃ (t : State L16) (k : Nat),
      k = 6 * len + 1 ∧
      Steps code input k s₀ t ∧
      t.pc = exitPC ∧
      t.data.size = workCap ∧
      (reg t r11).val = src₀ + len ∧
      (reg t r12).val = dst₀ + len ∧
      (reg t r13).val = src₀ + len ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r14 → reg t r = reg s₀ r) ∧
      (∀ j < len, t.data[dst₀ + j]? = s₀.data[src₀ + j]?) ∧
      (∀ addr, (addr < dst₀ ∨ dst₀ + len ≤ addr) → t.data[addr]? = s₀.data[addr]?) := by
  let inv : Nat → State L16 → Prop := fun rem s =>
    let k := len - rem
    rem ≤ len ∧
    s.pc = loopPC ∧
    s.data.size = workCap ∧
    (reg s rOne).val = 1 ∧
    (reg s r11).val = src₀ + k ∧
    (reg s r12).val = dst₀ + k ∧
    (reg s r13).val = src₀ + len ∧
    (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r14 → reg s r = reg s₀ r) ∧
    (∀ j < k, s.data[dst₀ + j]? = s₀.data[src₀ + j]?) ∧
    (∀ j, k ≤ j → j < len → s.data[src₀ + j]? = s₀.data[src₀ + j]?) ∧
    (∀ addr, (addr < dst₀ ∨ dst₀ + k ≤ addr) → s.data[addr]? = s₀.data[addr]?)
  have hStep : ∀ rem s, inv rem s →
      (rem = 0 ∧ ∃ t, step code input s = some (.next t) ∧ t.pc = exitPC ∧ t.regs = s.regs ∧ t.data = s.data) ∨
      (0 < rem ∧ ∃ s', Steps code input 6 s s' ∧ inv (rem - 1) s') := by
    intro rem s hI
    rcases hI with ⟨hRemLe, hsPC, hsSz, hsOne, hs11, hs12, hs13, hsPres, hsCp, hsSrc, hsFr⟩
    have hf0 : code[s.pc]? = some (.branchLt r11 r13 (loopPC + 1) exitPC) := by
      rw [hsPC]; exact hPl 0 (by rw [copyLoopCode_size]; decide)
    by_cases hRem0 : rem = 0
    · left
      refine ⟨hRem0, ?_⟩
      have hk : len - rem = len := by omega
      have hFalse : WordOps.ltb (reg s r11) (reg s r13) = false :=
        branchLt_false (by rw [hs11, hk, hs13]; exact Nat.le_refl _)
      have hBr := step_branchLt_at (code := code) (input := input) hf0 (by
        rw [hFalse, ite_eq_right (by decide)]; exact hExit)
      rw [hFalse, ite_eq_right (by decide)] at hBr
      exact ⟨_, hBr, rfl, rfl, rfl⟩
    · right
      have hRemPos : 0 < rem := Nat.pos_of_ne_zero hRem0
      refine ⟨hRemPos, ?_⟩
      let k := len - rem
      have hkLt : k < len := by omega
      have hTrue : WordOps.ltb (reg s r11) (reg s r13) = true :=
        branchLt_true (by rw [hs11, hs13]; exact Nat.add_lt_add_left hkLt src₀)
      have hBr := step_branchLt_at (code := code) (input := input) hf0 (by rw [hTrue, ite_eq_left rfl]; omega)
      rw [hTrue, ite_eq_left rfl] at hBr
      let s1 : State L16 := { s with pc := loopPC + 1 }
      have hs1_pc : s1.pc = loopPC + 1 := rfl
      have hSrcIdx : src₀ + k < workCap := by omega
      have hValS : s1.data[(reg s1 r11).val]? = s₀.data[src₀ + k]? := by
        change s.data[(reg s r11).val]? = s₀.data[src₀ + k]?
        rw [hs11]; exact hsSrc k (Nat.le_refl k) hkLt
      have hS0Idx : src₀ + k < s₀.data.size := by rw [hSz]; exact hSrcIdx
      obtain ⟨w0, hw0⟩ : ∃ w0, s₀.data[src₀ + k]? = some w0 :=
        ⟨s₀.data[src₀ + k]'hS0Idx, Array.getElem?_eq_getElem hS0Idx⟩
      obtain ⟨s2, hs2, hpc2, hr2_14, ho2, hd2⟩ :=
        step_loadData16 (input := input) (by rw [hs1_pc]; exact hPl 1 (by rw [copyLoopCode_size]; decide))
          (by rw [hValS, hw0]) (by rw [hs1_pc]; omega)
      have hr2_11 : (reg s2 r11).val = src₀ + k := by
        rw [ho2 r11 (by decide)]; exact hs11
      have hr2_12 : (reg s2 r12).val = dst₀ + k := by
        rw [ho2 r12 (by decide)]; exact hs12
      have hs2_sz : s2.data.size = workCap := by rw [hd2]; exact hsSz
      have hDstBound2 : (reg s2 r12).val < s2.data.size := by rw [hr2_12, hs2_sz]; omega
      obtain ⟨s3, hs3, hpc3, hregs3, hd3⟩ :=
        step_storeData16 (input := input) (by rw [hpc2, hs1_pc]; exact hPl 2 (by rw [copyLoopCode_size]; decide))
          (by rw [hpc2, hs1_pc]; omega) hDstBound2
      have hOne3 : (reg s3 rOne).val = 1 := by
        rw [reg_eq_of_regs_eq hregs3 rOne, ho2 rOne (by decide)]; exact hsOne
      have hr3_11 : (reg s3 r11).val = src₀ + k := by
        rw [reg_eq_of_regs_eq hregs3 r11]; exact hr2_11
      have hr3_12 : (reg s3 r12).val = dst₀ + k := by
        rw [reg_eq_of_regs_eq hregs3 r12]; exact hr2_12
      obtain ⟨s4, hs4, hpc4, hr4_11, ho4, hd4⟩ :=
        step_add16 (input := input) (by rw [hpc3, hpc2, hs1_pc]; exact hPl 3 (by rw [copyLoopCode_size]; decide))
          (by rw [hpc3, hpc2, hs1_pc]; omega)
      have hr4_11v : (reg s4 r11).val = src₀ + (k + 1) := by
        rw [hr4_11, add_no_wrap _ _ (by rw [hr3_11, hOne3]; omega), hr3_11, hOne3]; omega
      have hr4_12 : (reg s4 r12).val = dst₀ + k := by rw [ho4 r12 (by decide)]; exact hr3_12
      have hOne4 : (reg s4 rOne).val = 1 := by rw [ho4 rOne (by decide)]; exact hOne3
      obtain ⟨s5, hs5, hpc5, hr5_12, ho5, hd5⟩ :=
        step_add16 (input := input) (by rw [hpc4, hpc3, hpc2, hs1_pc]; exact hPl 4 (by rw [copyLoopCode_size]; decide))
          (by rw [hpc4, hpc3, hpc2, hs1_pc]; omega)
      have hr5_12v : (reg s5 r12).val = dst₀ + (k + 1) := by
        rw [hr5_12, add_no_wrap _ _ (by rw [hr4_12, hOne4]; omega), hr4_12, hOne4]; omega
      have hGo := step_goto_at (code := code) (input := input) (s := s5) (target := loopPC)
        (by rw [hpc5, hpc4, hpc3, hpc2, hs1_pc]; exact hPl 5 (by rw [copyLoopCode_size]; decide)) (by omega)
      let s6 : State L16 := { s5 with pc := loopPC }
      have hSteps6 : Steps code input 6 s s6 :=
        Steps.cons hBr (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (step1 hGo)))))
      have hd6 : s6.data = s2.data.set (reg s2 r12).val (reg s2 r14) hDstBound2 := by
        change s5.data = _; rw [hd5, hd4, hd3]
      have hkSucc : len - (rem - 1) = k + 1 := by omega
      have hReg6 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r14 → reg s6 r = reg s₀ r := by
        intro r h11 h12 h14
        change reg s5 r = reg s₀ r
        rw [ho5 r h12, ho4 r h11, reg_eq_of_regs_eq hregs3 r, ho2 r h14]
        exact hsPres r h11 h12 h14
      refine ⟨s6, hSteps6, ?_, rfl, by rw [hd6, Array.size_set]; exact hs2_sz,
        by change (reg s5 rOne).val = 1; rw [ho5 rOne (by decide)]; exact hOne4,
        by rw [hkSucc]; change (reg s5 r11).val = _; rw [ho5 r11 (by decide)]; exact hr4_11v,
        by rw [hkSucc]; exact hr5_12v,
        by change (reg s5 r13).val = _; rw [ho5 r13 (by decide), ho4 r13 (by decide),
             reg_eq_of_regs_eq hregs3 r13, ho2 r13 (by decide)]; exact hs13,
        hReg6, ?_, ?_, ?_⟩
      · omega
      · intro j hj
        rw [hd6]
        by_cases hjk : j = k
        · subst j
          have hSet : dst₀ + k = (reg s2 r12).val := hr2_12.symm
          rw [hSet, Array.getElem?_set_self, hr2_14, hw0]
        · rw [Array.getElem?_set_ne _ (by rw [hr2_12]; omega), hd2]
          exact hsCp j (by omega)
      · intro j hj1 hj2
        rw [hd6]
        have hNeq : (reg s2 r12).val ≠ src₀ + j := by
          rw [hr2_12]
          rcases hSafe with hL | hR | hF <;> omega
        rw [Array.getElem?_set_ne _ hNeq, hd2]
        exact hsSrc j (by omega) hj2
      · intro addr hAddr
        rw [hd6]
        have hNeq : (reg s2 r12).val ≠ addr := by rw [hr2_12]; omega
        rw [Array.getElem?_set_ne _ hNeq, hd2]
        exact hsFr addr (by cases hAddr with | inl h => exact Or.inl h | inr h => exact Or.inr (by omega))
  have hInd : ∀ rem s, inv rem s →
      ∃ t, Steps code input (6 * rem + 1) s t ∧
        t.pc = exitPC ∧ t.data.size = workCap ∧
        (reg t r11).val = src₀ + len ∧ (reg t r12).val = dst₀ + len ∧
        (reg t r13).val = src₀ + len ∧
        (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r14 → reg t r = reg s₀ r) ∧
        (∀ j < len, t.data[dst₀ + j]? = s₀.data[src₀ + j]?) ∧
        (∀ addr, (addr < dst₀ ∨ dst₀ + len ≤ addr) → t.data[addr]? = s₀.data[addr]?) := by
    intro rem
    induction rem with
    | zero =>
      intro s hI
      rcases hStep 0 s hI with ⟨_, t, hs, hpc, hregs, hdata⟩ | ⟨hPos, _⟩
      · rcases hI with ⟨_, _, hsSz, _, hs11, hs12, hs13, hsPres, hsCp, _, hsFr⟩
        have hk : len - 0 = len := Nat.sub_zero len
        rw [hk] at hs11 hs12 hsCp hsFr
        refine ⟨t, step1 hs, hpc, by rw [hdata]; exact hsSz,
          by rw [reg_eq_of_regs_eq hregs r11]; exact hs11,
          by rw [reg_eq_of_regs_eq hregs r12]; exact hs12,
          by rw [reg_eq_of_regs_eq hregs r13]; exact hs13,
          fun r h1 h2 h4 => by rw [reg_eq_of_regs_eq hregs r]; exact hsPres r h1 h2 h4,
          fun j hj => by rw [hdata]; exact hsCp j hj,
          fun addr hA => by rw [hdata]; exact hsFr addr hA⟩
      · exact (Nat.lt_irrefl 0 hPos).elim
    | succ rem ih =>
      intro s hI
      rcases hStep (rem + 1) s hI with ⟨h0, _⟩ | ⟨_, s', h6, hI'⟩
      · exact absurd h0 (Nat.succ_ne_zero rem)
      · obtain ⟨t, hTail, rest⟩ := ih s' (by simpa [Nat.add_sub_cancel] using hI')
        refine ⟨t, ?_, rest⟩
        exact (show 6 + (6 * rem + 1) = 6 * (rem + 1) + 1 by omega) ▸ h6.append hTail
  have hInit : inv len s₀ :=
    ⟨Nat.le_refl _, hPC, hSz, hOne,
      by rw [Nat.sub_self, Nat.add_zero]; exact hR11,
      by rw [Nat.sub_self, Nat.add_zero]; exact hR12,
      hR13, fun _ _ _ _ => rfl,
      fun j hj => by rw [Nat.sub_self] at hj; exact absurd hj (Nat.not_lt_zero j),
      fun j _ hj => rfl,
      fun addr _ => rfl⟩
  obtain ⟨t, hSteps, rest⟩ := hInd len s₀ hInit
  exact ⟨t, 6 * len + 1, rfl, hSteps, rest⟩

end RamPackHelpers

/-! ### 4. Phase 1 (`sealedHeaderPhase`): Write Header Slots & Copy Global Static Tables -/

section SealedHeaderPhases

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def writeHeaderCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[.imm r10 ⟨16, by omega⟩,
    .imm r11 ⟨hdrOrigToDense, by rw [hdrOrigToDense_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 rN,
    .imm r11 ⟨hdrDenseToOrig, by rw [hdrDenseToOrig_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .add r11 r9 rOne, .storeData r11 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrDomDepth, by rw [hdrDomDepth_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .storeData r9 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrEntry, by rw [hdrEntry_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrStop, by rw [hdrStop_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrOrigOfEntry, by rw [hdrOrigOfEntry_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrChildStart, by rw [hdrChildStart_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5, .add r10 r10 rOne,
    .imm r11 ⟨hdrChildEntries, by rw [hdrChildEntries_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrChildStops, by rw [hdrChildStops_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5,
    .imm r11 ⟨hdrChildIds, by rw [hdrChildIds_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .add r10 r10 r5, .sub r10 r10 rOne,
    .imm r11 ⟨hdrOwnerDesc, by rw [hdrOwnerDesc_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .imm r11 ⟨hdrN, by rw [hdrN_eq]; omega⟩, .add r11 r9 r11, .storeData r11 rN,
    .imm r11 ⟨hdrQCount, by rw [hdrQCount_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r5,
    .add r11 r5 r5, .add r10 r10 r11, .add r11 r11 r11, .add r11 r11 r11, .add r10 r10 r11,
    .imm r11 ⟨hdrTotalWords, by rw [hdrTotalWords_eq]; omega⟩, .add r11 r9 r11, .storeData r11 r10,
    .halt]

def writeHeaderPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (writeHeaderCode h32) 65 rfl rfl rfl

def copyOrigToDenseCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[.add r11 rN rN,
    .add r11 r11 rN,
    .imm r12 ⟨16, by omega⟩,
    .add r12 r9 r12,
    .add r13 r11 rN] ++
  copyLoopCode 5 11 ++ #[.halt]

def copyOrigToDensePhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (copyOrigToDenseCode h32) 11 rfl rfl rfl

def copyDenseToOrigCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[.add r11 rN rN,
    .add r11 r11 r11,
    .imm r12 ⟨16, by omega⟩,
    .add r12 r9 r12,
    .add r12 r12 rN,
    .add r13 r11 r5] ++
  copyLoopCode 6 12 ++ #[.halt]

def copyDenseToOrigPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (copyDenseToOrigCode h32) 12 rfl rfl rfl

def copyTreeLoCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[.mov r11 r6,
    .imm r12 ⟨16, by omega⟩,
    .add r12 r9 r12,
    .add r12 r12 rN,
    .add r12 r12 r5,
    .add r13 r5 r5,
    .add r13 r11 r13] ++
  copyLoopCode 7 13 ++ #[.halt]

def copyTreeLoPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (copyTreeLoCode h32) 13 rfl rfl rfl

def copyTreeHiCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[.add r11 r5 r5,
    .add r11 r11 r5,
    .add r13 r11 r6,
    .imm r14 ⟨16, by omega⟩,
    .add r12 r9 r14,
    .add r12 r12 rN,
    .add r12 r12 r11,
    .mov r11 r13,
    .add r14 r5 r5,
    .add r14 r14 r14,
    .add r14 r14 r14,
    .add r13 r11 r14] ++
  copyLoopCode 12 18 ++ #[.halt]

def copyTreeHiPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (copyTreeHiCode h32) 18 rfl rfl rfl

def sealedHeaderPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  pipelinePhase
    [writeHeaderPhase h32,
     copyOrigToDensePhase h32,
     copyDenseToOrigPhase h32,
     copyTreeLoPhase h32,
     copyTreeHiPhase h32]

end SealedHeaderPhases

/-! ### 5. Phase 2 (`sealedOwnersPhase`): Pack `ownerDesc[0..Q-1]` & Per-Owner Arenas -/

section SealedOwnersPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

private def soSeg0a (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[-- 0..1: outer loop `d = 0 .. Q - 1`
    .imm r10 ⟨0, by omega⟩,
    .branchLt r10 r5 2 177,
    -- 2..10: `r15 := sealedBase + ownerDescOff + 10 * d`
    .imm r15 ⟨hdrOwnerDesc, by rw [hdrOwnerDesc_eq]; omega⟩,
    .add r15 r9 r15,
    .loadData r15 r15,
    .add r15 r9 r15,
    .add r11 r10 r10,
    .add r12 r11 r11,
    .add r12 r12 r12,
    .add r11 r11 r12,
    .add r15 r15 r11,
    -- 11..24: `n_d := 1 + (childStart[d+1] - childStart[d])`, write `desc[0]`, branch `< 3`
    .add r11 r5 r5,
    .add r12 r11 r11,
    .add r12 r12 r11,
    .add r12 r12 r5,
    .add r12 r12 r6,
    .add r12 r12 r10,
    .loadData r11 r12,
    .add r12 r12 rOne,
    .loadData r12 r12,
    .sub r11 r12 r11,
    .add r11 r11 rOne,
    .storeData r15 r11,
    .imm r12 ⟨3, by omega⟩,
    .branchLt r11 r12 25 34,
    -- 25..33: small branch (`n_d < 3`): zero-fill `desc[1..9]`, `d += 1`, loop
    .add r11 r15 rOne,
    .imm r12 ⟨ownerDescStride, by rw [ownerDescStride_eq]; omega⟩,
    .add r12 r15 r12,
    .branchLt r11 r12 29 32,
    .storeData r11 rZero,
    .add r11 r11 rOne,
    .goto 28,
    .add r10 r10 rOne,
    .goto 1,
    -- 34..43: large branch (`3 ≤ n_d`): `fpBase`, `curOff`, `fp0`, write `desc[1]`
    .add r11 r10 r10,
    .add r12 r11 r11,
    .add r11 r11 r12,
    .add r11 r7 r11,
    .imm r13 ⟨hdrTotalWords, by rw [hdrTotalWords_eq]; omega⟩,
    .add r13 r9 r13,
    .loadData r12 r13,
    .loadData r13 r11,
    .add r15 r15 rOne,
    .storeData r15 r12]

private def soSeg0b (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[-- 44..73: write `desc[2..6]` from `curOff + (fp_k - fp0)` (`k = 1..5`)
    .add r11 r11 rOne, .loadData r14 r11, .sub r14 r14 r13, .add r14 r12 r14, .add r15 r15 rOne, .storeData r15 r14,
    .add r11 r11 rOne, .loadData r14 r11, .sub r14 r14 r13, .add r14 r12 r14, .add r15 r15 rOne, .storeData r15 r14,
    .add r11 r11 rOne, .loadData r14 r11, .sub r14 r14 r13, .add r14 r12 r14, .add r15 r15 rOne, .storeData r15 r14,
    .add r11 r11 rOne, .loadData r14 r11, .sub r14 r14 r13, .add r14 r12 r14, .add r15 r15 rOne, .storeData r15 r14,
    .add r11 r11 rOne, .loadData r14 r11, .sub r14 r14 r13, .add r14 r12 r14, .add r15 r15 rOne, .storeData r15 r14,
    -- 74..84: restore `r15 := descBase`, setup Forest copy `[fp0 .. fp5 + N_d) -> [sealedBase + curOff ..)`
    .imm r14 ⟨6, by omega⟩,
    .sub r15 r15 r14,
    .sub r11 r11 rOne,
    .loadData r14 r11,
    .add r11 r11 rOne,
    .loadData r11 r11,
    .sub r14 r11 r14,
    .add r14 r11 r14,
    .mov r11 r13,
    .add r12 r9 r12,
    .mov r13 r14]

private def soSeg1 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[-- 91..110: Exit Bank 0 (`exitDepth`, len `N_d`)
    .sub r12 r12 r9,
    .imm r14 ⟨descExitDepth, by rw [descExitDepth_eq]; omega⟩,
    .add r11 r15 r14,
    .storeData r11 r12,
    .add r11 r10 r10,
    .add r13 r11 r11,
    .add r11 r11 r13,
    .add r11 r7 r11,
    .imm r13 ⟨4, by omega⟩,
    .add r11 r11 r13,
    .loadData r14 r11,
    .add r11 r11 rOne,
    .loadData r11 r11,
    .sub r14 r11 r14,
    .add r11 r10 r10,
    .add r11 r11 r10,
    .add r11 r8 r11,
    .loadData r11 r11,
    .add r13 r11 r14,
    .add r12 r9 r12]

private def soSeg2 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[-- 117..142: Exit Bank 1 (`exitStored`, len `18 * N_d`)
    .sub r12 r12 r9,
    .imm r14 ⟨descExitStored, by rw [descExitStored_eq]; omega⟩,
    .add r11 r15 r14,
    .storeData r11 r12,
    .add r11 r10 r10,
    .add r13 r11 r11,
    .add r11 r11 r13,
    .add r11 r7 r11,
    .imm r13 ⟨4, by omega⟩,
    .add r11 r11 r13,
    .loadData r14 r11,
    .add r11 r11 rOne,
    .loadData r11 r11,
    .sub r14 r11 r14,
    .add r13 r14 r14,
    .add r14 r13 r13,
    .add r14 r14 r14,
    .add r14 r14 r14,
    .add r14 r14 r13,
    .add r11 r10 r10,
    .add r11 r11 r10,
    .add r11 r8 r11,
    .add r11 r11 rOne,
    .loadData r11 r11,
    .add r13 r11 r14,
    .add r12 r9 r12]

private def soSeg3 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[-- 149..164: Exit Bank 2 (`exitPrior`, len `6 * n_d`)
    .sub r12 r12 r9,
    .imm r14 ⟨descExitPrior, by rw [descExitPrior_eq]; omega⟩,
    .add r11 r15 r14,
    .storeData r11 r12,
    .loadData r14 r15,
    .add r13 r14 r14,
    .add r14 r13 r13,
    .add r14 r14 r13,
    .add r11 r10 r10,
    .add r11 r11 r10,
    .add r11 r8 r11,
    .imm r13 ⟨2, by omega⟩,
    .add r11 r11 r13,
    .loadData r11 r11,
    .add r13 r11 r14,
    .add r12 r9 r12]

private def soSeg4 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[-- 171..177: update `hdrTotalWords`, `d += 1`, loop, halt
    .sub r12 r12 r9,
    .imm r11 ⟨hdrTotalWords, by rw [hdrTotalWords_eq]; omega⟩,
    .add r11 r9 r11,
    .storeData r11 r12,
    .add r10 r10 rOne,
    .goto 1,
    .halt]

private def soPre0 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soSeg0a h32 ++ soSeg0b h32

private def soPre1 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre0 h32 ++ copyLoopCode 85 91

private def soPre2 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre1 h32 ++ soSeg1 h32

private def soPre3 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre2 h32 ++ copyLoopCode 111 117

private def soPre4 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre3 h32 ++ soSeg2 h32

private def soPre5 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre4 h32 ++ copyLoopCode 143 149

private def soPre6 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre5 h32 ++ soSeg3 h32

private def soPre7 (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre6 h32 ++ copyLoopCode 165 171

def sealedOwnersCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  soPre7 h32 ++ soSeg4 h32

private theorem soSeg0a_size (h32 : 32 ≤ 2 ^ bits) : (soSeg0a (hi := hi) (hw := hw) h32).size = 44 := rfl
private theorem soSeg0b_size (h32 : 32 ≤ 2 ^ bits) : (soSeg0b (hi := hi) (hw := hw) h32).size = 41 := rfl
private theorem soSeg1_size (h32 : 32 ≤ 2 ^ bits) : (soSeg1 (hi := hi) (hw := hw) h32).size = 20 := rfl
private theorem soSeg2_size (h32 : 32 ≤ 2 ^ bits) : (soSeg2 (hi := hi) (hw := hw) h32).size = 26 := rfl
private theorem soSeg3_size (h32 : 32 ≤ 2 ^ bits) : (soSeg3 (hi := hi) (hw := hw) h32).size = 16 := rfl
private theorem soSeg4_size (h32 : 32 ≤ 2 ^ bits) : (soSeg4 (hi := hi) (hw := hw) h32).size = 7 := rfl

private theorem soPre0_size (h32 : 32 ≤ 2 ^ bits) : (soPre0 (hi := hi) (hw := hw) h32).size = 85 := by
  rw [soPre0, Array.size_append, soSeg0a_size, soSeg0b_size]
private theorem soPre1_size (h32 : 32 ≤ 2 ^ bits) : (soPre1 (hi := hi) (hw := hw) h32).size = 91 := by
  rw [soPre1, Array.size_append, soPre0_size, copyLoopCode_size]
private theorem soPre2_size (h32 : 32 ≤ 2 ^ bits) : (soPre2 (hi := hi) (hw := hw) h32).size = 111 := by
  rw [soPre2, Array.size_append, soPre1_size, soSeg1_size]
private theorem soPre3_size (h32 : 32 ≤ 2 ^ bits) : (soPre3 (hi := hi) (hw := hw) h32).size = 117 := by
  rw [soPre3, Array.size_append, soPre2_size, copyLoopCode_size]
private theorem soPre4_size (h32 : 32 ≤ 2 ^ bits) : (soPre4 (hi := hi) (hw := hw) h32).size = 143 := by
  rw [soPre4, Array.size_append, soPre3_size, soSeg2_size]
private theorem soPre5_size (h32 : 32 ≤ 2 ^ bits) : (soPre5 (hi := hi) (hw := hw) h32).size = 149 := by
  rw [soPre5, Array.size_append, soPre4_size, copyLoopCode_size]
private theorem soPre6_size (h32 : 32 ≤ 2 ^ bits) : (soPre6 (hi := hi) (hw := hw) h32).size = 165 := by
  rw [soPre6, Array.size_append, soPre5_size, soSeg3_size]
private theorem soPre7_size (h32 : 32 ≤ 2 ^ bits) : (soPre7 (hi := hi) (hw := hw) h32).size = 171 := by
  rw [soPre7, Array.size_append, soPre6_size, copyLoopCode_size]
theorem sealedOwnersCode_size (h32 : 32 ≤ 2 ^ bits) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32).size = 178 := by
  rw [sealedOwnersCode, Array.size_append, soPre7_size, soSeg4_size]

private theorem soSeg0a_nonHalt (h32 : 32 ≤ 2 ^ bits) :
    (soSeg0a (hi := hi) (hw := hw) h32).toList.all (@nonHalt bits L16) = true := rfl
private theorem soSeg0b_nonHalt (h32 : 32 ≤ 2 ^ bits) :
    (soSeg0b (hi := hi) (hw := hw) h32).toList.all (@nonHalt bits L16) = true := rfl
private theorem soSeg1_nonHalt (h32 : 32 ≤ 2 ^ bits) :
    (soSeg1 (hi := hi) (hw := hw) h32).toList.all (@nonHalt bits L16) = true := rfl
private theorem soSeg2_nonHalt (h32 : 32 ≤ 2 ^ bits) :
    (soSeg2 (hi := hi) (hw := hw) h32).toList.all (@nonHalt bits L16) = true := rfl
private theorem soSeg3_nonHalt (h32 : 32 ≤ 2 ^ bits) :
    (soSeg3 (hi := hi) (hw := hw) h32).toList.all (@nonHalt bits L16) = true := rfl

private theorem soPre7_nonHalt (h32 : 32 ≤ 2 ^ bits) :
    (soPre7 (hi := hi) (hw := hw) h32).toList.all (@nonHalt bits L16) = true := by
  unfold soPre7 soPre6 soPre5 soPre4 soPre3 soPre2 soPre1 soPre0
  rw [Array.toList_append, List.all_append, copyLoopCode_nonHalt, Bool.and_true]
  rw [Array.toList_append, List.all_append, soSeg3_nonHalt h32, Bool.and_true]
  rw [Array.toList_append, List.all_append, copyLoopCode_nonHalt, Bool.and_true]
  rw [Array.toList_append, List.all_append, soSeg2_nonHalt h32, Bool.and_true]
  rw [Array.toList_append, List.all_append, copyLoopCode_nonHalt, Bool.and_true]
  rw [Array.toList_append, List.all_append, soSeg1_nonHalt h32, Bool.and_true]
  rw [Array.toList_append, List.all_append, copyLoopCode_nonHalt, Bool.and_true]
  rw [Array.toList_append, List.all_append, soSeg0a_nonHalt h32, soSeg0b_nonHalt h32]
  rfl

private theorem so_cpF (h32 : 32 ≤ 2 ^ bits) :
    SlicePlaced (sealedOwnersCode (hi := hi) (hw := hw) h32) 85 (copyLoopCode 85 91) := by
  intro k hk
  have hk6 : k < 6 := by rw [copyLoopCode_size] at hk; exact hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_left (by rw [soPre4_size]; omega),
    soPre4, Array.getElem?_append_left (by rw [soPre3_size]; omega),
    soPre3, Array.getElem?_append_left (by rw [soPre2_size]; omega),
    soPre2, Array.getElem?_append_left (by rw [soPre1_size]; omega),
    soPre1, Array.getElem?_append_right (by rw [soPre0_size]; omega),
    soPre0_size, Nat.add_sub_cancel_left, Array.getElem?_eq_getElem hk]

private theorem so_cpE0 (h32 : 32 ≤ 2 ^ bits) :
    SlicePlaced (sealedOwnersCode (hi := hi) (hw := hw) h32) 111 (copyLoopCode 111 117) := by
  intro k hk
  have hk6 : k < 6 := by rw [copyLoopCode_size] at hk; exact hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_left (by rw [soPre4_size]; omega),
    soPre4, Array.getElem?_append_left (by rw [soPre3_size]; omega),
    soPre3, Array.getElem?_append_right (by rw [soPre2_size]; omega),
    soPre2_size, Nat.add_sub_cancel_left, Array.getElem?_eq_getElem hk]

private theorem so_cpE1 (h32 : 32 ≤ 2 ^ bits) :
    SlicePlaced (sealedOwnersCode (hi := hi) (hw := hw) h32) 143 (copyLoopCode 143 149) := by
  intro k hk
  have hk6 : k < 6 := by rw [copyLoopCode_size] at hk; exact hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_right (by rw [soPre4_size]; omega),
    soPre4_size, Nat.add_sub_cancel_left, Array.getElem?_eq_getElem hk]

private theorem so_cpE2 (h32 : 32 ≤ 2 ^ bits) :
    SlicePlaced (sealedOwnersCode (hi := hi) (hw := hw) h32) 165 (copyLoopCode 165 171) := by
  intro k hk
  have hk6 : k < 6 := by rw [copyLoopCode_size] at hk; exact hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_right (by rw [soPre6_size]; omega),
    soPre6_size, Nat.add_sub_cancel_left, Array.getElem?_eq_getElem hk]

private theorem so_seg0a (h32 : 32 ≤ 2 ^ bits) :
    ∀ k < 44, (sealedOwnersCode (hi := hi) (hw := hw) h32)[k]? = (soSeg0a (hi := hi) (hw := hw) h32)[k]? := by
  intro k hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_left (by rw [soPre4_size]; omega),
    soPre4, Array.getElem?_append_left (by rw [soPre3_size]; omega),
    soPre3, Array.getElem?_append_left (by rw [soPre2_size]; omega),
    soPre2, Array.getElem?_append_left (by rw [soPre1_size]; omega),
    soPre1, Array.getElem?_append_left (by rw [soPre0_size]; omega),
    soPre0, Array.getElem?_append_left (by rw [soSeg0a_size]; omega)]

private theorem so_seg0b (h32 : 32 ≤ 2 ^ bits) :
    ∀ k < 41, (sealedOwnersCode (hi := hi) (hw := hw) h32)[44 + k]? = (soSeg0b (hi := hi) (hw := hw) h32)[k]? := by
  intro k hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_left (by rw [soPre4_size]; omega),
    soPre4, Array.getElem?_append_left (by rw [soPre3_size]; omega),
    soPre3, Array.getElem?_append_left (by rw [soPre2_size]; omega),
    soPre2, Array.getElem?_append_left (by rw [soPre1_size]; omega),
    soPre1, Array.getElem?_append_left (by rw [soPre0_size]; omega),
    soPre0, Array.getElem?_append_right (by rw [soSeg0a_size]; omega),
    soSeg0a_size, Nat.add_sub_cancel_left]

private theorem so_seg1 (h32 : 32 ≤ 2 ^ bits) :
    ∀ k < 20, (sealedOwnersCode (hi := hi) (hw := hw) h32)[91 + k]? = (soSeg1 (hi := hi) (hw := hw) h32)[k]? := by
  intro k hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_left (by rw [soPre4_size]; omega),
    soPre4, Array.getElem?_append_left (by rw [soPre3_size]; omega),
    soPre3, Array.getElem?_append_left (by rw [soPre2_size]; omega),
    soPre2, Array.getElem?_append_right (by rw [soPre1_size]; omega),
    soPre1_size, Nat.add_sub_cancel_left]

private theorem so_seg2 (h32 : 32 ≤ 2 ^ bits) :
    ∀ k < 26, (sealedOwnersCode (hi := hi) (hw := hw) h32)[117 + k]? = (soSeg2 (hi := hi) (hw := hw) h32)[k]? := by
  intro k hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_left (by rw [soPre5_size]; omega),
    soPre5, Array.getElem?_append_left (by rw [soPre4_size]; omega),
    soPre4, Array.getElem?_append_right (by rw [soPre3_size]; omega),
    soPre3_size, Nat.add_sub_cancel_left]

private theorem so_seg3 (h32 : 32 ≤ 2 ^ bits) :
    ∀ k < 16, (sealedOwnersCode (hi := hi) (hw := hw) h32)[149 + k]? = (soSeg3 (hi := hi) (hw := hw) h32)[k]? := by
  intro k hk
  rw [sealedOwnersCode, Array.getElem?_append_left (by rw [soPre7_size]; omega),
    soPre7, Array.getElem?_append_left (by rw [soPre6_size]; omega),
    soPre6, Array.getElem?_append_right (by rw [soPre5_size]; omega),
    soPre5_size, Nat.add_sub_cancel_left]

private theorem so_seg4 (h32 : 32 ≤ 2 ^ bits) :
    ∀ k < 7, (sealedOwnersCode (hi := hi) (hw := hw) h32)[171 + k]? = (soSeg4 (hi := hi) (hw := hw) h32)[k]? := by
  intro k hk
  rw [sealedOwnersCode, Array.getElem?_append_right (by rw [soPre7_size]; omega),
    soPre7_size, Nat.add_sub_cancel_left]

theorem so_fetch0a (h32 : 32 ≤ 2 ^ bits) {k : Nat} (hk : k < 44) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32)[k]? =
      (soSeg0a (hi := hi) (hw := hw) h32)[k]? :=
  so_seg0a h32 k hk

private theorem so_fetch0b (h32 : 32 ≤ 2 ^ bits) {pc : Nat} (hLo : 44 ≤ pc) (hHi : pc < 85) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32)[pc]? =
      (soSeg0b (hi := hi) (hw := hw) h32)[pc - 44]? := by
  have h := so_seg0b (hi := hi) (hw := hw) h32 (pc - 44) (by omega)
  rwa [Nat.add_sub_of_le hLo] at h

private theorem so_fetch1 (h32 : 32 ≤ 2 ^ bits) {pc : Nat} (hLo : 91 ≤ pc) (hHi : pc < 111) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32)[pc]? =
      (soSeg1 (hi := hi) (hw := hw) h32)[pc - 91]? := by
  have h := so_seg1 (hi := hi) (hw := hw) h32 (pc - 91) (by omega)
  rwa [Nat.add_sub_of_le hLo] at h

private theorem so_fetch2 (h32 : 32 ≤ 2 ^ bits) {pc : Nat} (hLo : 117 ≤ pc) (hHi : pc < 143) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32)[pc]? =
      (soSeg2 (hi := hi) (hw := hw) h32)[pc - 117]? := by
  have h := so_seg2 (hi := hi) (hw := hw) h32 (pc - 117) (by omega)
  rwa [Nat.add_sub_of_le hLo] at h

private theorem so_fetch3 (h32 : 32 ≤ 2 ^ bits) {pc : Nat} (hLo : 149 ≤ pc) (hHi : pc < 165) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32)[pc]? =
      (soSeg3 (hi := hi) (hw := hw) h32)[pc - 149]? := by
  have h := so_seg3 (hi := hi) (hw := hw) h32 (pc - 149) (by omega)
  rwa [Nat.add_sub_of_le hLo] at h

theorem so_fetch4 (h32 : 32 ≤ 2 ^ bits) {pc : Nat} (hLo : 171 ≤ pc) (hHi : pc < 178) :
    (sealedOwnersCode (hi := hi) (hw := hw) h32)[pc]? =
      (soSeg4 (hi := hi) (hw := hw) h32)[pc - 171]? := by
  have h := so_seg4 (hi := hi) (hw := hw) h32 (pc - 171) (by omega)
  rwa [Nat.add_sub_of_le hLo] at h

def sealedOwnersPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (sealedOwnersCode h32) 177 (sealedOwnersCode_size h32)
    (by
      rw [sealedOwnersCode, Array.getElem?_append_right (by rw [soPre7_size]; omega), soPre7_size]
      rfl)
    (by
      have hLen : (soPre7 (hi := hi) (hw := hw) h32).toList.length = 171 := by
        rw [Array.length_toList, soPre7_size]
      have hTail : ((soSeg4 (hi := hi) (hw := hw) h32).toList.take 6).all (@nonHalt bits L16) = true := rfl
      rw [sealedOwnersCode, Array.toList_append, List.take_append,
        List.take_of_length_le (by rw [hLen]; decide), hLen, List.all_append,
        soPre7_nonHalt, hTail]
      rfl)

end SealedOwnersPhase

/-! ### 6. Phase 3 (`shiftToZeroPhase`) & Master Compositions -/

section MasterPacker

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

def shiftToZeroCode (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  #[.imm r13 ⟨hdrTotalWords, by rw [hdrTotalWords_eq]; omega⟩,
    .add r13 r9 r13,
    .loadData r13 r13,
    .mov r11 r9,
    .mov r12 rZero,
    .add r13 r9 r13] ++
  copyLoopCode 6 12 ++ #[.halt]

theorem shiftToZeroCode_size (h32 : 32 ≤ 2 ^ bits) :
    (shiftToZeroCode (hi := hi) (hw := hw) h32).size = 13 := by
  unfold shiftToZeroCode
  rw [Array.size_append, Array.size_append, copyLoopCode_size]
  rfl

def shiftToZeroPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  Phase.ofLast (shiftToZeroCode h32) 12 rfl rfl rfl

def sealedPackPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  (sealedHeaderPhase h32).link (sealedOwnersPhase h32)

def sealedPackProgram (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  (sealedPackPhase (hi := hi) (hw := hw) h32).code

def sealedPackAndShiftPhase (h32 : 32 ≤ 2 ^ bits) : Phase L16 :=
  (sealedPackPhase h32).link (shiftToZeroPhase h32)

def sealedPackAndShiftProgram (h32 : 32 ≤ 2 ^ bits) : Program L16 :=
  (sealedPackAndShiftPhase (hi := hi) (hw := hw) h32).code

/-- Registers expected at entry to `sealedPackProgram` / `sealedPackAndShiftProgram`. -/
structure SealedPackEntryRegs (n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat)
    (s : State L16) : Prop where
  consts : ConstRegs n m root s
  qVal : (reg s r5).val = Q
  treeBaseVal : (reg s r6).val = treeBase
  forestPtrsVal : (reg s r7).val = forestPtrsBase
  exitPtrsVal : (reg s r8).val = exitPtrsBase
  sealedBaseVal : (reg s r9).val = sealedBase

/-- Disjointness of `[sealedBase .. sealedBase + 128 * n)` from every source region
read by `sealedPackProgram`. -/
structure SealedDisjointLayout (n Q treeBase forestPtrsBase forestArenaBase forestUsed
    exitPtrsBase exitArenaBase exitUsed sealedBase workCap : Nat) : Prop where
  sealed_fit : sealedBase + retainedLinearFactor * n ≤ workCap
  disj_orig : sealedBase + retainedLinearFactor * n ≤ 3 * n ∨ 4 * n + Q ≤ sealedBase
  disj_tree : sealedBase + retainedLinearFactor * n ≤ treeBase ∨
    treeBase + staticTreeWords Q ≤ sealedBase
  disj_fPtrs : sealedBase + retainedLinearFactor * n ≤ forestPtrsBase ∨
    forestPtrsBase + 6 * Q ≤ sealedBase
  disj_fArena : sealedBase + retainedLinearFactor * n ≤ forestArenaBase ∨
    forestArenaBase + forestUsed ≤ sealedBase
  disj_ePtrs : sealedBase + retainedLinearFactor * n ≤ exitPtrsBase ∨
    exitPtrsBase + 3 * Q ≤ sealedBase
  disj_eArena : sealedBase + retainedLinearFactor * n ≤ exitArenaBase ∨
    exitArenaBase + exitUsed ≤ sealedBase

/-- Canonical quarter-partition disjointness when `sealedBase = 5 * n`,
`treeBase = workCap / 4`, and `640 * (n + m + 1) ≤ workCap` (with all emitted
and arena sources inside `[treeBase .. workCap)`). -/
theorem canonical_quarter_disjoint {n m Q forestPtrsBase forestArenaBase forestUsed
    exitPtrsBase exitArenaBase exitUsed workCap : Nat}
    (hQ : Q ≤ n) (hCap : 640 * (n + m + 1) ≤ workCap)
    (hFP : workCap / 4 ≤ forestPtrsBase) (hFA : workCap / 4 ≤ forestArenaBase)
    (hEP : workCap / 4 ≤ exitPtrsBase) (hEA : workCap / 4 ≤ exitArenaBase) :
    SealedDisjointLayout n Q (workCap / 4) forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed (5 * n) workCap := by
  have hBound : 5 * n + retainedLinearFactor * n ≤ workCap / 4 := by
    unfold retainedLinearFactor; omega
  exact
    { sealed_fit := by omega
      disj_orig := Or.inr (by omega)
      disj_tree := Or.inl hBound
      disj_fPtrs := Or.inl (Nat.le_trans hBound hFP)
      disj_fArena := Or.inl (Nat.le_trans hBound hFA)
      disj_ePtrs := Or.inl (Nat.le_trans hBound hEP)
      disj_eArena := Or.inl (Nat.le_trans hBound hEA) }

end MasterPacker

/-! ### 7. End-to-End Execution Proofs for Header, Owners Loop, and Shift -/

section ExecutionProofs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

private theorem writeSlot_step {code : Program L16} {input : Input L16}
    {s : State L16} {pc slot : Nat} {hSlot : slot < 2 ^ bits}
    {src : Fin 16} (hNe11 : src ≠ r11)
    (hPC : s.pc = pc) (hPcFit : pc + 3 < code.size)
    (hc0 : code[pc]? = some (.imm r11 ⟨slot, hSlot⟩))
    (hc1 : code[pc + 1]? = some (.add r11 r9 r11))
    (hc2 : code[pc + 2]? = some (.storeData r11 src))
    {sealedBase : Nat} (h9 : (reg s r9).val = sealedBase)
    (hFit : sealedBase + slot < workCap) (hBits : workCap < 2 ^ bits)
    (hsSz : s.data.size = workCap) :
    ∃ t : State L16, Steps code input 3 s t ∧ t.pc = pc + 3 ∧
      t.data.size = workCap ∧
      (∀ r : Fin 16, r ≠ r11 → reg t r = reg s r) ∧
      t.data[sealedBase + slot]? = some (reg s src) ∧
      (∀ addr, addr ≠ sealedBase + slot → t.data[addr]? = s.data[addr]?) := by
  obtain ⟨sa, hsa, pca, ra11, pa, da⟩ :=
    step_imm16 (input := input) (by rw [hPC]; exact hc0) (by omega)
  have h9a : (reg sa r9).val = sealedBase := by rw [pa r9 (by decide)]; exact h9
  obtain ⟨sb, hsb, pcb, rb11, pb, db⟩ :=
    step_add16 (input := input) (by rw [pca, hPC]; exact hc1) (by omega)
  have hb11v : (reg sb r11).val = sealedBase + slot := by
    rw [rb11, add_no_wrap _ _ (by rw [h9a, ra11]; dsimp only; omega), h9a, ra11]
  have hBnd : (reg sb r11).val < sb.data.size := by
    rw [hb11v, db, da, hsSz]; exact hFit
  obtain ⟨sc, hsc, pcc, hregs_c, dc⟩ :=
    step_storeData16 (input := input) (by rw [pcb, pca, hPC]; exact hc2) (by omega) hBnd
  have hSrcB : reg sb src = reg s src := by rw [pb src hNe11, pa src hNe11]
  refine ⟨sc, Steps.cons hsa (Steps.cons hsb (step1 hsc)), by rw [pcc, pcb, pca, hPC],
    by rw [dc, Array.size_set, db, da, hsSz], ?_, ?_, ?_⟩
  · intro r hr; rw [reg_eq_of_regs_eq hregs_c r, pb r hr, pa r hr]
  · rw [dc, ← hb11v, Array.getElem?_set_self, hSrcB]
  · intro addr hNe
    rw [dc, Array.getElem?_set_ne _ (by rw [hb11v]; exact hNe.symm), db, da]

private theorem addR10_writeSlot_step {code : Program L16} {input : Input L16}
    {s : State L16} {pc slot : Nat} {hSlot : slot < 2 ^ bits}
    {incReg : Fin 16} (_hIncNe10 : incReg ≠ r10) (_hIncNe11 : incReg ≠ r11)
    {v delta : Nat} (h10 : (reg s r10).val = v) (hInc : (reg s incReg).val = delta)
    (hSumFit : v + delta < 2 ^ bits)
    (hPC : s.pc = pc) (hPcFit : pc + 4 < code.size)
    (hca : code[pc]? = some (.add r10 r10 incReg))
    (hc0 : code[pc + 1]? = some (.imm r11 ⟨slot, hSlot⟩))
    (hc1 : code[pc + 2]? = some (.add r11 r9 r11))
    (hc2 : code[pc + 3]? = some (.storeData r11 r10))
    {sealedBase : Nat} (h9 : (reg s r9).val = sealedBase)
    (hFit : sealedBase + slot < workCap) (hBits : workCap < 2 ^ bits)
    (hsSz : s.data.size = workCap) :
    ∃ t : State L16, Steps code input 4 s t ∧ t.pc = pc + 4 ∧
      t.data.size = workCap ∧
      (reg t r10).val = v + delta ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg t r = reg s r) ∧
      (t.data[sealedBase + slot]?).map Fin.val = some (v + delta) ∧
      (∀ addr, addr ≠ sealedBase + slot → t.data[addr]? = s.data[addr]?) := by
  obtain ⟨sa, hsa, pca, ra10, pa, da⟩ :=
    step_add16 (input := input) (by rw [hPC]; exact hca) (by omega)
  have ha10v : (reg sa r10).val = v + delta := by
    rw [ra10, add_no_wrap _ _ (by rw [h10, hInc]; exact hSumFit), h10, hInc]
  have h9a : (reg sa r9).val = sealedBase := by rw [pa r9 (by decide)]; exact h9
  obtain ⟨t, hSt, htpc, htsz, htp, htw, htfr⟩ :=
    writeSlot_step (code := code) (input := input) (by decide) (by rw [pca, hPC]) (by omega)
      hc0 hc1 hc2 h9a hFit hBits (by rw [da]; exact hsSz)
  refine ⟨t, Steps.cons hsa hSt, htpc, htsz,
    by rw [htp r10 (by decide)]; exact ha10v,
    fun r hr10 hr11 => by rw [htp r hr11, pa r hr10],
    by rw [htw, Option.map_some, ha10v],
    fun addr hNe => by rw [htfr addr hNe, da]⟩

private theorem run_writeHeaderPhase_part1 (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat}
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hFit : sealedBase + oracleHeaderSize ≤ workCap)
    (hSz : s₀.data.size = workCap)
    (hArenaFit : sealedInitArenaOff n Q < 2 ^ bits) :
    let code := (writeHeaderPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s33 : State L16,
      Steps code input 33 (Phase.initial s₀) s33 ∧
      s33.pc = 33 ∧
      s33.data.size = workCap ∧
      (reg s33 r10).val = 16 + n + 7 * Q ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s33 r = reg s₀ r) ∧
      (s33.data[sealedBase + hdrHead]?).map Fin.val = some (sealedHeadOff n Q) ∧
      (s33.data[sealedBase + hdrDomParent]?).map Fin.val = some (sealedDomParentOff n Q) ∧
      (s33.data[sealedBase + hdrDomDepth]?).map Fin.val = some (sealedDomDepthOff n Q) ∧
      (s33.data[sealedBase + hdrOrigToDense]?).map Fin.val = some sealedOrigToDenseOff ∧
      (s33.data[sealedBase + hdrDenseToOrig]?).map Fin.val = some (sealedDenseToOrigOff n) ∧
      (s33.data[sealedBase + hdrEntry]?).map Fin.val = some (sealedEntryOff n Q) ∧
      (s33.data[sealedBase + hdrStop]?).map Fin.val = some (sealedStopOff n Q) ∧
      (s33.data[sealedBase + hdrOrigOfEntry]?).map Fin.val = some (sealedOrigOfEntryOff n Q) ∧
      (s33.data[sealedBase + hdrChildStart]?).map Fin.val = some (sealedChildStartOff n Q) ∧
      (∀ addr, (addr < sealedBase ∨ sealedBase + oracleHeaderSize ≤ addr) →
        s33.data[addr]? = s₀.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 66 := rfl
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  have hLt2Pow : ∀ k, k ≤ 16 + n + 21 * Q → k < 2 ^ bits :=
    fun _ hk => Nat.lt_of_le_of_lt hk hArenaFit
  have hOne0 : (reg s₀ rOne).val = 1 := hRegs.consts.one
  have hN0 : (reg s₀ rN).val = n := hRegs.consts.nVal
  have hQ0 : (reg s₀ r5).val = Q := hRegs.qVal
  have hS0 : (reg s₀ r9).val = sealedBase := hRegs.sealedBaseVal
  -- 0: imm r10 16
  obtain ⟨s1, hs1, pc1, r1_10, p1, d1⟩ :=
    step_imm16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc]; rfl) (by rw [hCodeSz]; omega)
  have hr1_10 : (reg s1 r10).val = 16 := by rw [r1_10]
  have hp1 : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s1 r = reg s₀ r := fun r h _ => p1 r h
  have hd1 : s1.data.size = workCap := by rw [d1]; exact hSz
  -- 1..3: hdrOrigToDense := 16
  obtain ⟨s4, hs4, pc4, sz4, p4, w4, fr4⟩ :=
    writeSlot_step (code := code) (input := input) (s := s1) (pc := 1) (slot := hdrOrigToDense) (hSlot := by rw [hdrOrigToDense_eq]; omega)
      (src := r10) (by decide) pc1 (by rw [hCodeSz]; omega) rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp1 r9 (by decide) (by decide)]; exact hS0) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrOrigToDense_eq]; omega) hBits hd1
  rw [hdrOrigToDense_eq] at fr4
  have hp4' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s4 r = reg s₀ r :=
    fun r h10 h11 => by rw [p4 r h11, hp1 r h10 h11]
  have hw4' : (s4.data[sealedBase + hdrOrigToDense]?).map Fin.val = some sealedOrigToDenseOff := by
    rw [w4, Option.map_some, hr1_10]; rfl
  -- 4..7: r10 := 16 + n, hdrDenseToOrig
  obtain ⟨s8, hs8, pc8, sz8, r8_10, p8, w8, fr8⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s4) (pc := 4) (slot := hdrDenseToOrig) (hSlot := by rw [hdrDenseToOrig_eq]; omega)
      (by decide) (by decide) (v := 16) (delta := n)
      (by rw [p4 r10 (by decide)]; exact hr1_10)
      (by rw [hp4' rN (by decide) (by decide)]; exact hN0)
      (hLt2Pow _ (by omega)) pc4 (by rw [hCodeSz]; omega)
      rfl rfl rfl rfl (sealedBase := sealedBase) (by rw [hp4' r9 (by decide) (by decide)]; exact hS0)
      (by rw [oracleHeaderSize_eq] at hFit; rw [hdrDenseToOrig_eq]; omega) hBits sz4
  rw [hdrDenseToOrig_eq] at fr8
  have hp8' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s8 r = reg s₀ r :=
    fun r h10 h11 => by rw [p8 r h10 h11, hp4' r h10 h11]
  -- 8..10: r10 := 16 + n + Q, hdrDomParent
  obtain ⟨s9, hs9, pc9, r9_10, p9, d9⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc8]; rfl) (by rw [hCodeSz]; omega)
  have r9_10v : (reg s9 r10).val = 16 + n + Q := by
    have hQ8 : (reg s8 r5).val = Q := by rw [hp8' r5 (by decide) (by decide)]; exact hQ0
    rw [r9_10, add_no_wrap _ _ (by rw [r8_10, hQ8]; exact hLt2Pow _ (by omega)), r8_10, hQ8]
  have hp9' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s9 r = reg s₀ r :=
    fun r h10 h11 => by rw [p9 r h10, hp8' r h10 h11]
  obtain ⟨s10, hs10, pc10, r10_11, p10, d10⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc9, pc8]; rfl) (by rw [hCodeSz]; omega)
  have r10_11v : (reg s10 r11).val = sealedBase + hdrDomParent := by
    have h9_9 : (reg s9 r9).val = sealedBase := by rw [hp9' r9 (by decide) (by decide)]; exact hS0
    have h9_1 : (reg s9 rOne).val = 1 := by rw [hp9' rOne (by decide) (by decide)]; exact hOne0
    rw [r10_11, add_no_wrap _ _ (by rw [h9_9, h9_1]; rw [oracleHeaderSize_eq] at hFit; omega), h9_9, h9_1]
  have hBnd10 : (reg s10 r11).val < s10.data.size := by
    rw [r10_11v, d10, d9, sz8, hdrDomParent_eq]; rw [oracleHeaderSize_eq] at hFit; omega
  obtain ⟨s11, hs11, pc11, hregs11, d11⟩ :=
    step_storeData16 (code := code) (input := input) (by rw [pc10, pc9, pc8]; rfl) (by rw [hCodeSz]; omega) hBnd10
  have sz11 : s11.data.size = workCap := by rw [d11, Array.size_set, d10, d9, sz8]
  have hp11' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s11 r = reg s₀ r :=
    fun r h10 h11 => by rw [reg_eq_of_regs_eq hregs11 r, p10 r h11, hp9' r h10 h11]
  have r11_10v : (reg s11 r10).val = 16 + n + Q := by
    rw [reg_eq_of_regs_eq hregs11 r10, p10 r10 (by decide)]; exact r9_10v
  have w11 : (s11.data[sealedBase + hdrDomParent]?).map Fin.val = some (sealedDomParentOff n Q) := by
    rw [d11, ← r10_11v, Array.getElem?_set_self, Option.map_some, p10 r10 (by decide), r9_10v]; rfl
  have fr11 : ∀ addr, addr ≠ sealedBase + 1 → s11.data[addr]? = s8.data[addr]? := fun addr hNe => by
    rw [d11, Array.getElem?_set_ne _ (by rw [r10_11v, hdrDomParent_eq]; exact hNe.symm), d10, d9]
  -- 11..14: hdrDomDepth
  obtain ⟨s15, hs15, pc15, sz15, r15_10, p15, w15, fr15⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s11) (pc := 11) (slot := hdrDomDepth) (hSlot := by rw [hdrDomDepth_eq]; omega)
      (by decide) (by decide) (v := 16 + n + Q) (delta := Q)
      r11_10v (by rw [hp11' r5 (by decide) (by decide)]; exact hQ0) (hLt2Pow _ (by omega))
      (by rw [pc11, pc10, pc9, pc8]) (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp11' r9 (by decide) (by decide)]; exact hS0) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrDomDepth_eq]; omega) hBits sz11
  rw [hdrDomDepth_eq] at fr15
  have hr15_10 : (reg s15 r10).val = 16 + n + 2 * Q := by rw [r15_10]; omega
  have hp15' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s15 r = reg s₀ r :=
    fun r h10 h11 => by rw [p15 r h10 h11, hp11' r h10 h11]
  -- 15..16: r10 := 16 + n + 3*Q, hdrHead
  obtain ⟨s16, hs16, pc16, r16_10, p16, d16⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc15]; rfl) (by rw [hCodeSz]; omega)
  have r16_10v : (reg s16 r10).val = 16 + n + 3 * Q := by
    have hQ15 : (reg s15 r5).val = Q := by rw [hp15' r5 (by decide) (by decide)]; exact hQ0
    rw [r16_10, add_no_wrap _ _ (by rw [hr15_10, hQ15]; exact hLt2Pow _ (by omega)), hr15_10, hQ15]; omega
  have hp16' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s16 r = reg s₀ r :=
    fun r h10 h11 => by rw [p16 r h10, hp15' r h10 h11]
  have hBnd16 : (reg s16 r9).val < s16.data.size := by
    rw [hp16' r9 (by decide) (by decide), hS0, d16, sz15]; rw [oracleHeaderSize_eq] at hFit; omega
  obtain ⟨s17, hs17, pc17, hregs17, d17⟩ :=
    step_storeData16 (code := code) (input := input) (by rw [pc16, pc15]; rfl) (by rw [hCodeSz]; omega) hBnd16
  have sz17 : s17.data.size = workCap := by rw [d17, Array.size_set, d16, sz15]
  have hp17' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s17 r = reg s₀ r :=
    fun r h10 h11 => by rw [reg_eq_of_regs_eq hregs17 r, hp16' r h10 h11]
  have r17_10v : (reg s17 r10).val = 16 + n + 3 * Q := by
    rw [reg_eq_of_regs_eq hregs17 r10]; exact r16_10v
  have w17 : (s17.data[sealedBase + hdrHead]?).map Fin.val = some (sealedHeadOff n Q) := by
    have h9_16 : (reg s16 r9).val = sealedBase := by rw [hp16' r9 (by decide) (by decide)]; exact hS0
    rw [d17, hdrHead_eq, Nat.add_zero, ← h9_16, Array.getElem?_set_self, Option.map_some, r16_10v]; rfl
  have fr17 : ∀ addr, addr ≠ sealedBase + 0 → s17.data[addr]? = s15.data[addr]? := fun addr hNe => by
    have h9_16 : (reg s16 r9).val = sealedBase := by rw [hp16' r9 (by decide) (by decide)]; exact hS0
    rw [d17, Array.getElem?_set_ne _ (by rw [h9_16]; exact fun e => hNe (by omega)), d16]
  -- 17..20: hdrEntry
  obtain ⟨s21, hs21, pc21, sz21, r21_10, p21, w21, fr21⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s17) (pc := 17) (slot := hdrEntry) (hSlot := by rw [hdrEntry_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 3 * Q) (delta := Q)
      r17_10v (by rw [hp17' r5 (by decide) (by decide)]; exact hQ0) (hLt2Pow _ (by omega))
      (by rw [pc17, pc16, pc15]) (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp17' r9 (by decide) (by decide)]; exact hS0) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrEntry_eq]; omega) hBits sz17
  rw [hdrEntry_eq] at fr21
  have hr21_10 : (reg s21 r10).val = 16 + n + 4 * Q := by rw [r21_10]; omega
  have hp21' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s21 r = reg s₀ r :=
    fun r h10 h11 => by rw [p21 r h10 h11, hp17' r h10 h11]
  -- 21..24: hdrStop
  obtain ⟨s25, hs25, pc25, sz25, r25_10, p25, w25, fr25⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s21) (pc := 21) (slot := hdrStop) (hSlot := by rw [hdrStop_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 4 * Q) (delta := Q)
      hr21_10 (by rw [hp21' r5 (by decide) (by decide)]; exact hQ0) (hLt2Pow _ (by omega))
      pc21 (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp21' r9 (by decide) (by decide)]; exact hS0) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrStop_eq]; omega) hBits sz21
  rw [hdrStop_eq] at fr25
  have hr25_10 : (reg s25 r10).val = 16 + n + 5 * Q := by rw [r25_10]; omega
  have hp25' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s25 r = reg s₀ r :=
    fun r h10 h11 => by rw [p25 r h10 h11, hp21' r h10 h11]
  -- 25..28: hdrOrigOfEntry
  obtain ⟨s29, hs29, pc29, sz29, r29_10, p29, w29, fr29⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s25) (pc := 25) (slot := hdrOrigOfEntry) (hSlot := by rw [hdrOrigOfEntry_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 5 * Q) (delta := Q)
      hr25_10 (by rw [hp25' r5 (by decide) (by decide)]; exact hQ0) (hLt2Pow _ (by omega))
      pc25 (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp25' r9 (by decide) (by decide)]; exact hS0) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrOrigOfEntry_eq]; omega) hBits sz25
  rw [hdrOrigOfEntry_eq] at fr29
  have hr29_10 : (reg s29 r10).val = 16 + n + 6 * Q := by rw [r29_10]; omega
  have hp29' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s29 r = reg s₀ r :=
    fun r h10 h11 => by rw [p29 r h10 h11, hp25' r h10 h11]
  -- 29..32: hdrChildStart
  obtain ⟨s33, hs33, pc33, sz33, r33_10, p33, w33, fr33⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s29) (pc := 29) (slot := hdrChildStart) (hSlot := by rw [hdrChildStart_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 6 * Q) (delta := Q)
      hr29_10 (by rw [hp29' r5 (by decide) (by decide)]; exact hQ0) (hLt2Pow _ (by omega))
      pc29 (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp29' r9 (by decide) (by decide)]; exact hS0) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrChildStart_eq]; omega) hBits sz29
  rw [hdrChildStart_eq] at fr33
  have hr33_10 : (reg s33 r10).val = 16 + n + 7 * Q := by rw [r33_10]; omega
  have hp33' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s33 r = reg s₀ r :=
    fun r h10 h11 => by rw [p33 r h10 h11, hp29' r h10 h11]
  have hSteps33 : Steps code input 33 (Phase.initial s₀) s33 := by
    have ha : Steps code input 4 (Phase.initial s₀) s4 := Steps.cons hs1 hs4
    have hb : Steps code input 7 s4 s11 :=
      hs8.append (Steps.cons hs9 (Steps.cons hs10 (step1 hs11)))
    have hc : Steps code input 10 s11 s21 :=
      hs15.append (Steps.cons hs16 (Steps.cons hs17 hs21))
    have hd : Steps code input 12 s21 s33 :=
      hs25.append (hs29.append hs33)
    exact ha.append (hb.append (hc.append hd))
  refine ⟨s33, hSteps33, pc33, sz33, hr33_10, hp33', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdrHead_eq, fr33 _ (by omega), fr29 _ (by omega), fr25 _ (by omega), fr21 _ (by omega), ← hdrHead_eq, w17]
  · rw [hdrDomParent_eq, fr33 _ (by omega), fr29 _ (by omega), fr25 _ (by omega), fr21 _ (by omega),
      fr17 _ (by omega), fr15 _ (by omega), ← hdrDomParent_eq, w11]
  · have w15' := w15
    rw [hdrDomDepth_eq] at w15'
    rw [hdrDomDepth_eq, fr33 _ (by omega), fr29 _ (by omega), fr25 _ (by omega), fr21 _ (by omega),
      fr17 _ (by omega), w15']
    unfold sealedDomDepthOff; exact congrArg some (by omega)
  · rw [hdrOrigToDense_eq, fr33 _ (by omega), fr29 _ (by omega), fr25 _ (by omega), fr21 _ (by omega),
      fr17 _ (by omega), fr15 _ (by omega), fr11 _ (by omega), fr8 _ (by omega), ← hdrOrigToDense_eq, hw4']
  · rw [hdrDenseToOrig_eq, fr33 _ (by omega), fr29 _ (by omega), fr25 _ (by omega), fr21 _ (by omega),
      fr17 _ (by omega), fr15 _ (by omega), fr11 _ (by omega), ← hdrDenseToOrig_eq, w8]
    unfold sealedDenseToOrigOff; rfl
  · rw [hdrEntry_eq, fr33 _ (by omega), fr29 _ (by omega), fr25 _ (by omega), ← hdrEntry_eq, w21]
    unfold sealedEntryOff; exact congrArg some (by omega)
  · rw [hdrStop_eq, fr33 _ (by omega), fr29 _ (by omega), ← hdrStop_eq, w25]
    unfold sealedStopOff; exact congrArg some (by omega)
  · rw [hdrOrigOfEntry_eq, fr33 _ (by omega), ← hdrOrigOfEntry_eq, w29]
    unfold sealedOrigOfEntryOff; exact congrArg some (by omega)
  · rw [w33]; unfold sealedChildStartOff; exact congrArg some (by omega)
  · intro addr hOut
    rw [oracleHeaderSize_eq] at hOut
    rw [fr33 addr (by omega), fr29 addr (by omega), fr25 addr (by omega), fr21 addr (by omega),
      fr17 addr (by omega), fr15 addr (by omega), fr11 addr (by omega), fr8 addr (by omega), fr4 addr (by omega), d1]; rfl

private theorem run_writeHeaderPhase_part2a (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s33 : State L16}
    {n Q sealedBase : Nat} (hQPos : 1 ≤ Q)
    (hPC33 : s33.pc = 33) (hSz33 : s33.data.size = workCap)
    (hr33_10 : (reg s33 r10).val = 16 + n + 7 * Q)
    (hOne33 : (reg s33 rOne).val = 1)
    (hQ33 : (reg s33 r5).val = Q) (hS33 : (reg s33 r9).val = sealedBase)
    (hFit : sealedBase + oracleHeaderSize ≤ workCap)
    (hArenaFit : sealedInitArenaOff n Q < 2 ^ bits) :
    let code := (writeHeaderPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s51 : State L16,
      Steps code input 18 s33 s51 ∧
      s51.pc = 51 ∧
      s51.data.size = workCap ∧
      (reg s51 r10).val = 16 + n + 11 * Q ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s51 r = reg s33 r) ∧
      (s51.data[sealedBase + hdrChildEntries]?).map Fin.val = some (sealedChildEntriesOff n Q) ∧
      (s51.data[sealedBase + hdrChildStops]?).map Fin.val = some (sealedChildStopsOff n Q) ∧
      (s51.data[sealedBase + hdrChildIds]?).map Fin.val = some (sealedChildIdsOff n Q) ∧
      (s51.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q) ∧
      (∀ addr, (addr < sealedBase + 11 ∨ sealedBase + 15 ≤ addr) →
        s51.data[addr]? = s33.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 66 := rfl
  have hLt2Pow : ∀ k, k ≤ 16 + n + 21 * Q → k < 2 ^ bits :=
    fun _ hk => Nat.lt_of_le_of_lt hk hArenaFit
  have hp33' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s33 r = reg s33 r := fun _ _ _ => rfl
  obtain ⟨s34, hs34, pc34, r34_10, p34, d34⟩ :=
    step_add16 (code := code) (input := input) (by rw [hPC33]; rfl) (by rw [hCodeSz]; omega)
  have r34_10v : (reg s34 r10).val = 16 + n + 8 * Q := by
    rw [r34_10, add_no_wrap _ _ (by rw [hr33_10, hQ33]; exact hLt2Pow _ (by omega)), hr33_10, hQ33]; omega
  have hp34' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s34 r = reg s33 r :=
    fun r h10 h11 => by rw [p34 r h10, hp33' r h10 h11]
  obtain ⟨s38, hs38, pc38, sz38, r38_10, p38, w38, fr38⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s34) (pc := 34) (slot := hdrChildEntries) (hSlot := by rw [hdrChildEntries_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 8 * Q) (delta := 1)
      r34_10v (by rw [hp34' rOne (by decide) (by decide)]; exact hOne33) (hLt2Pow _ (by omega))
      (by rw [pc34, hPC33]) (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp34' r9 (by decide) (by decide)]; exact hS33) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrChildEntries_eq]; omega)
      hBits (by rw [d34]; exact hSz33)
  rw [hdrChildEntries_eq] at fr38
  have hp38' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s38 r = reg s33 r :=
    fun r h10 h11 => by rw [p38 r h10 h11, hp34' r h10 h11]
  obtain ⟨s42, hs42, pc42, sz42, r42_10, p42, w42, fr42⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s38) (pc := 38) (slot := hdrChildStops) (hSlot := by rw [hdrChildStops_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 8 * Q + 1) (delta := Q)
      r38_10 (by rw [hp38' r5 (by decide) (by decide)]; exact hQ33) (hLt2Pow _ (by omega))
      pc38 (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp38' r9 (by decide) (by decide)]; exact hS33) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrChildStops_eq]; omega) hBits sz38
  rw [hdrChildStops_eq] at fr42
  have hr42_10 : (reg s42 r10).val = 16 + n + 9 * Q + 1 := by rw [r42_10]; omega
  have hp42' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s42 r = reg s33 r :=
    fun r h10 h11 => by rw [p42 r h10 h11, hp38' r h10 h11]
  obtain ⟨s46, hs46, pc46, sz46, r46_10, p46, w46, fr46⟩ :=
    addR10_writeSlot_step (code := code) (input := input) (s := s42) (pc := 42) (slot := hdrChildIds) (hSlot := by rw [hdrChildIds_eq]; omega)
      (by decide) (by decide) (v := 16 + n + 9 * Q + 1) (delta := Q)
      hr42_10 (by rw [hp42' r5 (by decide) (by decide)]; exact hQ33) (hLt2Pow _ (by omega))
      pc42 (by rw [hCodeSz]; omega) rfl rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp42' r9 (by decide) (by decide)]; exact hS33) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrChildIds_eq]; omega) hBits sz42
  rw [hdrChildIds_eq] at fr46
  have hr46_10 : (reg s46 r10).val = 16 + n + 10 * Q + 1 := by rw [r46_10]; omega
  have hp46' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s46 r = reg s33 r :=
    fun r h10 h11 => by rw [p46 r h10 h11, hp42' r h10 h11]
  obtain ⟨s47, hs47, pc47, r47_10, p47, d47⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc46]; rfl) (by rw [hCodeSz]; omega)
  have r47_10v : (reg s47 r10).val = 16 + n + 11 * Q + 1 := by
    have hQ46 : (reg s46 r5).val = Q := by rw [hp46' r5 (by decide) (by decide)]; exact hQ33
    rw [r47_10, add_no_wrap _ _ (by rw [hr46_10, hQ46]; exact hLt2Pow _ (by omega)), hr46_10, hQ46]; omega
  have hp47' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s47 r = reg s33 r :=
    fun r h10 h11 => by rw [p47 r h10, hp46' r h10 h11]
  obtain ⟨s48, hs48, pc48, r48_10, p48, d48⟩ :=
    step_sub16 (code := code) (input := input) (by rw [pc47, pc46]; rfl) (by rw [hCodeSz]; omega)
  have r48_10v : (reg s48 r10).val = 16 + n + 11 * Q := by
    have h1_47 : (reg s47 rOne).val = 1 := by rw [hp47' rOne (by decide) (by decide)]; exact hOne33
    rw [r48_10, sub_exact _ _ (by rw [r47_10v, h1_47]; omega), r47_10v, h1_47]; omega
  have hp48' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s48 r = reg s33 r :=
    fun r h10 h11 => by rw [p48 r h10, hp47' r h10 h11]
  obtain ⟨s51, hs51, pc51, sz51, p51, w51, fr51⟩ :=
    writeSlot_step (code := code) (input := input) (s := s48) (pc := 48) (slot := hdrOwnerDesc) (hSlot := by rw [hdrOwnerDesc_eq]; omega)
      (src := r10) (by decide) (by rw [pc48, pc47, pc46]) (by rw [hCodeSz]; omega) rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp48' r9 (by decide) (by decide)]; exact hS33) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrOwnerDesc_eq]; omega)
      hBits (by rw [d48, d47]; exact sz46)
  rw [hdrOwnerDesc_eq] at fr51
  have hp51' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s51 r = reg s33 r :=
    fun r h10 h11 => by rw [p51 r h11, hp48' r h10 h11]
  have r51_10v : (reg s51 r10).val = 16 + n + 11 * Q := by rw [p51 r10 (by decide)]; exact r48_10v
  have hSteps18 : Steps code input 18 s33 s51 :=
    (Steps.cons hs34 hs38).append (hs42.append (hs46.append (Steps.cons hs47 (Steps.cons hs48 hs51))))
  refine ⟨s51, hSteps18, pc51, sz51, r51_10v, hp51', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hdrChildEntries_eq, fr51 _ (by omega), d48, d47, fr46 _ (by omega), fr42 _ (by omega), ← hdrChildEntries_eq, w38]
    unfold sealedChildEntriesOff; exact congrArg some (by omega)
  · rw [hdrChildStops_eq, fr51 _ (by omega), d48, d47, fr46 _ (by omega), ← hdrChildStops_eq, w42]
    unfold sealedChildStopsOff; exact congrArg some (by omega)
  · rw [hdrChildIds_eq, fr51 _ (by omega), d48, d47, ← hdrChildIds_eq, w46]
    unfold sealedChildIdsOff; exact congrArg some (by omega)
  · rw [w51, Option.map_some, r48_10v]; rfl
  · intro addr hOut
    rw [fr51 addr (by omega), d48, d47, fr46 addr (by omega), fr42 addr (by omega), fr38 addr (by omega), d34]

private theorem run_writeHeaderPhase_part2b (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s51 : State L16}
    {n Q sealedBase : Nat}
    (hPC51 : s51.pc = 51) (hSz51 : s51.data.size = workCap)
    (hr51_10 : (reg s51 r10).val = 16 + n + 11 * Q)
    (hN51 : (reg s51 rN).val = n) (hQ51 : (reg s51 r5).val = Q) (hS51 : (reg s51 r9).val = sealedBase)
    (hFit : sealedBase + oracleHeaderSize ≤ workCap)
    (hArenaFit : sealedInitArenaOff n Q < 2 ^ bits) :
    let code := (writeHeaderPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ t : State L16,
      Steps code input 14 s51 t ∧
      t.pc = 65 ∧
      t.data.size = workCap ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg t r = reg s51 r) ∧
      (t.data[sealedBase + hdrN]?).map Fin.val = some n ∧
      (t.data[sealedBase + hdrQCount]?).map Fin.val = some Q ∧
      (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some (sealedInitArenaOff n Q) ∧
      (∀ addr, (addr < sealedBase + 4 ∨ (sealedBase + 6 ≤ addr ∧ addr < sealedBase + 15) ∨
          sealedBase + oracleHeaderSize ≤ addr) →
        t.data[addr]? = s51.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 66 := rfl
  have hLt2Pow : ∀ k, k ≤ 16 + n + 21 * Q → k < 2 ^ bits :=
    fun _ hk => Nat.lt_of_le_of_lt hk hArenaFit
  have hp51' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s51 r = reg s51 r := fun _ _ _ => rfl
  obtain ⟨s54, hs54, pc54, sz54, p54, w54, fr54⟩ :=
    writeSlot_step (code := code) (input := input) (s := s51) (pc := 51) (slot := hdrN) (hSlot := by rw [hdrN_eq]; omega)
      (src := rN) (by decide) hPC51 (by rw [hCodeSz]; omega) rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp51' r9 (by decide) (by decide)]; exact hS51) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrN_eq]; omega) hBits hSz51
  rw [hdrN_eq] at fr54
  have hp54' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s54 r = reg s51 r :=
    fun r h10 h11 => by rw [p54 r h11, hp51' r h10 h11]
  have r54_10v : (reg s54 r10).val = 16 + n + 11 * Q := by rw [p54 r10 (by decide)]; exact hr51_10
  obtain ⟨s57, hs57, pc57, sz57, p57, w57, fr57⟩ :=
    writeSlot_step (code := code) (input := input) (s := s54) (pc := 54) (slot := hdrQCount) (hSlot := by rw [hdrQCount_eq]; omega)
      (src := r5) (by decide) pc54 (by rw [hCodeSz]; omega) rfl rfl rfl (sealedBase := sealedBase)
      (by rw [hp54' r9 (by decide) (by decide)]; exact hS51) (by rw [oracleHeaderSize_eq] at hFit; rw [hdrQCount_eq]; omega) hBits sz54
  rw [hdrQCount_eq] at fr57
  have hp57' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s57 r = reg s51 r :=
    fun r h10 h11 => by rw [p57 r h11, hp54' r h10 h11]
  have r57_10v : (reg s57 r10).val = 16 + n + 11 * Q := by rw [p57 r10 (by decide)]; exact r54_10v
  have hQ57 : (reg s57 r5).val = Q := by rw [hp57' r5 (by decide) (by decide)]; exact hQ51
  obtain ⟨s58, hs58, pc58, r58_11, p58, d58⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc57]; rfl) (by rw [hCodeSz]; omega)
  have r58_11v : (reg s58 r11).val = 2 * Q := by
    rw [r58_11, add_no_wrap _ _ (by rw [hQ57]; exact hLt2Pow _ (by omega)), hQ57]; omega
  obtain ⟨s59, hs59, pc59, r59_10, p59, d59⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc58, pc57]; rfl) (by rw [hCodeSz]; omega)
  have r59_10v : (reg s59 r10).val = 16 + n + 13 * Q := by
    have hr10 : (reg s58 r10).val = 16 + n + 11 * Q := by rw [p58 r10 (by decide)]; exact r57_10v
    rw [r59_10, add_no_wrap _ _ (by rw [hr10, r58_11v]; exact hLt2Pow _ (by omega)), hr10, r58_11v]; omega
  obtain ⟨s60, hs60, pc60, r60_11, p60, d60⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc59, pc58, pc57]; rfl) (by rw [hCodeSz]; omega)
  have r60_11v : (reg s60 r11).val = 4 * Q := by
    have hr11 : (reg s59 r11).val = 2 * Q := by rw [p59 r11 (by decide)]; exact r58_11v
    rw [r60_11, add_no_wrap _ _ (by rw [hr11]; exact hLt2Pow _ (by omega)), hr11]; omega
  obtain ⟨s61, hs61, pc61, r61_11, p61, d61⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc60, pc59, pc58, pc57]; rfl) (by rw [hCodeSz]; omega)
  have r61_11v : (reg s61 r11).val = 8 * Q := by
    rw [r61_11, add_no_wrap _ _ (by rw [r60_11v]; exact hLt2Pow _ (by omega)), r60_11v]; omega
  obtain ⟨s62, hs62, pc62, r62_10, p62, d62⟩ :=
    step_add16 (code := code) (input := input) (by rw [pc61, pc60, pc59, pc58, pc57]; rfl) (by rw [hCodeSz]; omega)
  have r62_10v : (reg s62 r10).val = 16 + n + 21 * Q := by
    have hr10 : (reg s61 r10).val = 16 + n + 13 * Q := by
      rw [p61 r10 (by decide), p60 r10 (by decide)]; exact r59_10v
    rw [r62_10, add_no_wrap _ _ (by rw [hr10, r61_11v]; exact hLt2Pow _ (by omega)), hr10, r61_11v]; omega
  have hp62' : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg s62 r = reg s51 r :=
    fun r h10 h11 => by
      rw [p62 r h10, p61 r h11, p60 r h11, p59 r h10, p58 r h11, hp57' r h10 h11]
  have sz62 : s62.data.size = workCap := by rw [d62, d61, d60, d59, d58, sz57]
  obtain ⟨t, hst, pct, tsz, pt, wt, frt⟩ :=
    writeSlot_step (code := code) (input := input) (s := s62) (pc := 62) (slot := hdrTotalWords) (hSlot := by rw [hdrTotalWords_eq]; omega)
      (src := r10) (by decide) (by rw [pc62, pc61, pc60, pc59, pc58, pc57]) (by rw [hCodeSz]; omega)
      rfl rfl rfl (sealedBase := sealedBase) (by rw [hp62' r9 (by decide) (by decide)]; exact hS51)
      (by rw [oracleHeaderSize_eq] at hFit; rw [hdrTotalWords_eq]; omega) hBits sz62
  rw [hdrTotalWords_eq] at frt
  have hpt : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg t r = reg s51 r :=
    fun r h10 h11 => by rw [pt r h11, hp62' r h10 h11]
  have hSteps14 : Steps code input 14 s51 t :=
    hs54.append (hs57.append (Steps.cons hs58 (Steps.cons hs59 (Steps.cons hs60 (Steps.cons hs61 (Steps.cons hs62 hst))))))
  refine ⟨t, hSteps14, pct, tsz, hpt, ?_, ?_, ?_, ?_⟩
  · rw [hdrN_eq, frt _ (by omega), d62, d61, d60, d59, d58, fr57 _ (by omega), ← hdrN_eq, w54,
      Option.map_some, hp51' rN (by decide) (by decide), hN51]
  · rw [hdrQCount_eq, frt _ (by omega), d62, d61, d60, d59, d58, ← hdrQCount_eq, w57,
      Option.map_some, hp54' r5 (by decide) (by decide), hQ51]
  · rw [wt, Option.map_some, r62_10v]; rfl
  · intro addr hOut
    rw [oracleHeaderSize_eq] at hOut
    rw [frt addr (by omega), d62, d61, d60, d59, d58, fr57 addr (by omega), fr54 addr (by omega)]

private theorem run_writeHeaderPhase_part2 (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s33 : State L16}
    {n Q sealedBase : Nat} (hQPos : 1 ≤ Q)
    (hPC33 : s33.pc = 33) (hSz33 : s33.data.size = workCap)
    (hr33_10 : (reg s33 r10).val = 16 + n + 7 * Q)
    (hOne33 : (reg s33 rOne).val = 1) (hN33 : (reg s33 rN).val = n)
    (hQ33 : (reg s33 r5).val = Q) (hS33 : (reg s33 r9).val = sealedBase)
    (hFit : sealedBase + oracleHeaderSize ≤ workCap)
    (hArenaFit : sealedInitArenaOff n Q < 2 ^ bits) :
    let code := (writeHeaderPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ t : State L16,
      Steps code input 32 s33 t ∧
      t.pc = 65 ∧
      t.data.size = workCap ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg t r = reg s33 r) ∧
      (t.data[sealedBase + hdrN]?).map Fin.val = some n ∧
      (t.data[sealedBase + hdrQCount]?).map Fin.val = some Q ∧
      (t.data[sealedBase + hdrChildEntries]?).map Fin.val = some (sealedChildEntriesOff n Q) ∧
      (t.data[sealedBase + hdrChildStops]?).map Fin.val = some (sealedChildStopsOff n Q) ∧
      (t.data[sealedBase + hdrChildIds]?).map Fin.val = some (sealedChildIdsOff n Q) ∧
      (t.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q) ∧
      (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some (sealedInitArenaOff n Q) ∧
      (∀ addr, (addr < sealedBase + 4 ∨ addr = sealedBase + 6 ∨
          (sealedBase + 7 ≤ addr ∧ addr < sealedBase + 11) ∨
          sealedBase + oracleHeaderSize ≤ addr) →
        t.data[addr]? = s33.data[addr]?) := by
  obtain ⟨s51, hS18, pc51, sz51, r51_10, hp51, h11, h12, h13, h14, hFr2a⟩ :=
    run_writeHeaderPhase_part2a h32 hBits hQPos hPC33 hSz33 hr33_10 hOne33 hQ33 hS33 hFit hArenaFit
  obtain ⟨t, hS14, pct, tsz, hpt, h4, h5, h15, hFr2b⟩ :=
    run_writeHeaderPhase_part2b h32 hBits pc51 sz51 r51_10
      (by rw [hp51 rN (by decide) (by decide)]; exact hN33)
      (by rw [hp51 r5 (by decide) (by decide)]; exact hQ33)
      (by rw [hp51 r9 (by decide) (by decide)]; exact hS33) hFit hArenaFit
  refine ⟨t, hS18.append hS14, pct, tsz,
    fun r h10 h11 => by rw [hpt r h10 h11, hp51 r h10 h11],
    h4, h5, ?_, ?_, ?_, ?_, h15, ?_⟩
  · rw [hdrChildEntries_eq, hFr2b _ (Or.inr (Or.inl (by omega))), ← hdrChildEntries_eq]; exact h11
  · rw [hdrChildStops_eq, hFr2b _ (Or.inr (Or.inl (by omega))), ← hdrChildStops_eq]; exact h12
  · rw [hdrChildIds_eq, hFr2b _ (Or.inr (Or.inl (by omega))), ← hdrChildIds_eq]; exact h13
  · rw [hdrOwnerDesc_eq, hFr2b _ (Or.inr (Or.inl (by omega))), ← hdrOwnerDesc_eq]; exact h14
  · intro addr hOut
    rw [oracleHeaderSize_eq] at hOut
    rw [hFr2b addr (by rcases hOut with h | h | ⟨h1, h2⟩ | h; exact Or.inl h; exact Or.inr (Or.inl (by omega)); exact Or.inr (Or.inl (by omega)); exact Or.inr (Or.inr (by rw [oracleHeaderSize_eq]; exact h))),
      hFr2a addr (by rcases hOut with h | h | ⟨h1, h2⟩ | h; exact Or.inl (by omega); exact Or.inl (by omega); exact Or.inl (by omega); exact Or.inr (by omega))]

private theorem run_writeHeaderPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat} (hQPos : 1 ≤ Q)
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hFit : sealedBase + oracleHeaderSize ≤ workCap)
    (hSz : s₀.data.size = workCap)
    (hArenaFit : sealedInitArenaOff n Q < 2 ^ bits) :
    let code := (writeHeaderPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ t : State L16,
      run code input 66 (Phase.initial s₀) = some ⟨t, 66⟩ ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (t.data[sealedBase + hdrHead]?).map Fin.val = some (sealedHeadOff n Q) ∧
      (t.data[sealedBase + hdrDomParent]?).map Fin.val = some (sealedDomParentOff n Q) ∧
      (t.data[sealedBase + hdrDomDepth]?).map Fin.val = some (sealedDomDepthOff n Q) ∧
      (t.data[sealedBase + hdrOrigToDense]?).map Fin.val = some sealedOrigToDenseOff ∧
      (t.data[sealedBase + hdrN]?).map Fin.val = some n ∧
      (t.data[sealedBase + hdrQCount]?).map Fin.val = some Q ∧
      (t.data[sealedBase + hdrDenseToOrig]?).map Fin.val = some (sealedDenseToOrigOff n) ∧
      (t.data[sealedBase + hdrEntry]?).map Fin.val = some (sealedEntryOff n Q) ∧
      (t.data[sealedBase + hdrStop]?).map Fin.val = some (sealedStopOff n Q) ∧
      (t.data[sealedBase + hdrOrigOfEntry]?).map Fin.val = some (sealedOrigOfEntryOff n Q) ∧
      (t.data[sealedBase + hdrChildStart]?).map Fin.val = some (sealedChildStartOff n Q) ∧
      (t.data[sealedBase + hdrChildEntries]?).map Fin.val = some (sealedChildEntriesOff n Q) ∧
      (t.data[sealedBase + hdrChildStops]?).map Fin.val = some (sealedChildStopsOff n Q) ∧
      (t.data[sealedBase + hdrChildIds]?).map Fin.val = some (sealedChildIdsOff n Q) ∧
      (t.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q) ∧
      (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some (sealedInitArenaOff n Q) ∧
      (∀ addr, (addr < sealedBase ∨ sealedBase + oracleHeaderSize ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  obtain ⟨s33, hSteps33, pc33, sz33, r33_10, hp33, hH0, hH1, hH2, hH3, hH6, hH7, hH8, hH9, hH10, hFr1⟩ :=
    run_writeHeaderPhase_part1 h32 hBits hRegs hFit hSz hArenaFit
  have hOne33 : (reg s33 rOne).val = 1 := by rw [hp33 rOne (by decide) (by decide)]; exact hRegs.consts.one
  have hN33 : (reg s33 rN).val = n := by rw [hp33 rN (by decide) (by decide)]; exact hRegs.consts.nVal
  have hQ33 : (reg s33 r5).val = Q := by rw [hp33 r5 (by decide) (by decide)]; exact hRegs.qVal
  have hS33 : (reg s33 r9).val = sealedBase := by rw [hp33 r9 (by decide) (by decide)]; exact hRegs.sealedBaseVal
  obtain ⟨t, hSteps32, pct, tsz, hpt, hH4, hH5, hH11, hH12, hH13, hH14, hH15, hFr2⟩ :=
    run_writeHeaderPhase_part2 h32 hBits hQPos pc33 sz33 r33_10 hOne33 hN33 hQ33 hS33 hFit hArenaFit
  have hpt0 : ∀ r : Fin 16, r ≠ r10 → r ≠ r11 → reg t r = reg s₀ r :=
    fun r h10 h11 => by rw [hpt r h10 h11, hp33 r h10 h11]
  have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [pct]; rfl)
  have hRun : run code input 66 (Phase.initial s₀) = some ⟨t, 66⟩ :=
    (hSteps33.append hSteps32).halts hHalt
  refine ⟨t, hRun, tsz, ?_, ?_, ?_, ?_, ?_, hH4, hH5, ?_, ?_, ?_, ?_, ?_, hH11, hH12, hH13, hH14, hH15, ?_⟩
  · exact
      { consts :=
          { zero := by rw [hpt0 rZero (by decide) (by decide)]; exact hRegs.consts.zero
            one := by rw [hpt0 rOne (by decide) (by decide)]; exact hRegs.consts.one
            nVal := by rw [hpt0 rN (by decide) (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [hpt0 rM (by decide) (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [hpt0 rRoot (by decide) (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [hpt0 r5 (by decide) (by decide)]; exact hRegs.qVal
        treeBaseVal := by rw [hpt0 r6 (by decide) (by decide)]; exact hRegs.treeBaseVal
        forestPtrsVal := by rw [hpt0 r7 (by decide) (by decide)]; exact hRegs.forestPtrsVal
        exitPtrsVal := by rw [hpt0 r8 (by decide) (by decide)]; exact hRegs.exitPtrsVal
        sealedBaseVal := by rw [hpt0 r9 (by decide) (by decide)]; exact hRegs.sealedBaseVal }
  · rw [hdrHead_eq, hFr2 _ (by omega), ← hdrHead_eq, hH0]
  · rw [hdrDomParent_eq, hFr2 _ (by omega), ← hdrDomParent_eq, hH1]
  · have hH2' := hH2
    rw [hdrDomDepth_eq] at hH2'
    rw [hdrDomDepth_eq, hFr2 _ (by omega), hH2']
  · rw [hdrOrigToDense_eq, hFr2 _ (by omega), ← hdrOrigToDense_eq, hH3]
  · rw [hdrDenseToOrig_eq, hFr2 _ (by omega), ← hdrDenseToOrig_eq, hH6]
  · rw [hdrEntry_eq, hFr2 _ (by omega), ← hdrEntry_eq, hH7]
  · rw [hdrStop_eq, hFr2 _ (by omega), ← hdrStop_eq, hH8]
  · rw [hdrOrigOfEntry_eq, hFr2 _ (by omega), ← hdrOrigOfEntry_eq, hH9]
  · rw [hdrChildStart_eq, hFr2 _ (by omega), ← hdrChildStart_eq, hH10]
  · intro addr hOut
    rw [oracleHeaderSize_eq] at hOut
    rw [hFr2 addr (by rcases hOut with h | h; exact Or.inl (by omega); exact Or.inr (Or.inr (Or.inr (by rw [oracleHeaderSize_eq]; exact h)))),
      hFr1 addr (by rw [oracleHeaderSize_eq]; exact hOut)]

private theorem run_copyOrigToDensePhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat}
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hSrc : 3 * n + n ≤ workCap) (hDst : sealedOrigToDenseOff + sealedBase + n ≤ workCap)
    (hDisj : sealedBase + sealedOrigToDenseOff + n ≤ 3 * n ∨ 4 * n ≤ sealedBase + sealedOrigToDenseOff) :
    let code := (copyOrigToDensePhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ (t : State L16) (steps : Nat),
      steps = 6 * n + 7 ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (∀ j < n, t.data[sealedBase + sealedOrigToDenseOff + j]? = s₀.data[3 * n + j]?) ∧
      (∀ addr, (addr < sealedBase + sealedOrigToDenseOff ∨ sealedBase + sealedOrigToDenseOff + n ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 12 := rfl
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  have hN0 : (reg (Phase.initial s₀) rN).val = n := hRegs.consts.nVal
  obtain ⟨s1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r1_11v : (reg s1 r11).val = 2 * n := by
    rw [r1_11, add_no_wrap _ _ (by rw [hN0]; omega), hN0]; omega
  obtain ⟨s2, hs2, pc2, r2_11, p2, d2⟩ := step_add16 (code := code) (input := input) (by rw [pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r2_11v : (reg s2 r11).val = 3 * n := by
    have hN1 : (reg s1 rN).val = n := by rw [p1 rN (by decide)]; exact hN0
    rw [r2_11, add_no_wrap _ _ (by rw [r1_11v, hN1]; omega), r1_11v, hN1]; omega
  obtain ⟨s3, hs3, pc3, r3_12, p3, d3⟩ := step_imm16 (code := code) (input := input) (by rw [pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  obtain ⟨s4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (code := code) (input := input) (by rw [pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r4_12v : (reg s4 r12).val = sealedBase + sealedOrigToDenseOff := by
    have h9_3 : (reg s3 r9).val = sealedBase := by rw [p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide)]; exact hRegs.sealedBaseVal
    have h12_3 : (reg s3 r12).val = 16 := by rw [r3_12]
    rw [r4_12, add_no_wrap _ _ (by rw [h9_3, h12_3]; unfold sealedOrigToDenseOff at *; omega), h9_3, h12_3]; rfl
  obtain ⟨s5, hs5, pc5, r5_13, p5, d5⟩ := step_add16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have hr4_11 : (reg s4 r11).val = 3 * n := by rw [p4 r11 (by decide), p3 r11 (by decide)]; exact r2_11v
  have hr4_N : (reg s4 rN).val = n := by rw [p4 rN (by decide), p3 rN (by decide), p2 rN (by decide), p1 rN (by decide)]; exact hN0
  have r5_13v : (reg s5 r13).val = 3 * n + n := by
    rw [r5_13, add_no_wrap _ _ (by rw [hr4_11, hr4_N]; omega), hr4_11, hr4_N]
  have hPl : SlicePlaced code 5 (copyLoopCode 5 11) := copyLoop_slicePlaced rfl rfl rfl rfl rfl rfl
  have hSafe : sealedBase + sealedOrigToDenseOff + n ≤ 3 * n ∨ 3 * n + n ≤ sealedBase + sealedOrigToDenseOff ∨
      sealedBase + sealedOrigToDenseOff < 3 * n := by
    rcases hDisj with h | h; exact Or.inl h; exact Or.inr (Or.inl (by omega))
  obtain ⟨t, kLoop, hkLoop, hLoop, pct, tsz, _, _, _, htp, htcp, htfr⟩ :=
    run_copyLoop (input := input) hPl (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits hSrc
      (by unfold sealedOrigToDenseOff at hDst ⊢; omega) hSafe
      (by rw [pc5, pc4, pc3, pc2, pc1, h0pc]) (by rw [d5, d4, d3, d2, d1]; exact hSz)
      (by rw [p5 rOne (by decide), p4 rOne (by decide), p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hRegs.consts.one)
      (by rw [p5 r11 (by decide)]; exact hr4_11) (by rw [p5 r12 (by decide)]; exact r4_12v) r5_13v
  have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [pct]; rfl)
  have hRun := ((Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (step1 hs5))))).append hLoop).halts hHalt
  have hTot : 5 + kLoop + 1 = 6 * n + 7 := by omega
  rw [hTot] at hRun
  refine ⟨t, 6 * n + 7, rfl, hRun, tsz, ?_, ?_, ?_⟩
  · have hPres : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → reg t r = reg s₀ r := by
      intro r h1 h2 h3 h4
      rw [htp r h1 h2 h4, p5 r h3, p4 r h2, p3 r h2, p2 r h1, p1 r h1]; rfl
    exact
      { consts :=
          { zero := by rw [hPres rZero (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
            one := by rw [hPres rOne (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.one
            nVal := by rw [hPres rN (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [hPres rM (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [hPres rRoot (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [hPres r5 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.qVal
        treeBaseVal := by rw [hPres r6 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.treeBaseVal
        forestPtrsVal := by rw [hPres r7 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.forestPtrsVal
        exitPtrsVal := by rw [hPres r8 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.exitPtrsVal
        sealedBaseVal := by rw [hPres r9 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.sealedBaseVal }
  · intro j hj
    rw [show sealedBase + sealedOrigToDenseOff + j = (sealedBase + sealedOrigToDenseOff) + j by omega,
      htcp j hj, d5, d4, d3, d2, d1]; rfl
  · intro addr hA
    rw [htfr addr hA, d5, d4, d3, d2, d1]; rfl

private theorem run_copyDenseToOrigPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat}
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hSrc : 4 * n + Q ≤ workCap) (hDst : sealedBase + sealedDenseToOrigOff n + Q ≤ workCap)
    (hDisj : sealedBase + sealedDenseToOrigOff n + Q ≤ 4 * n ∨ 4 * n + Q ≤ sealedBase + sealedDenseToOrigOff n) :
    let code := (copyDenseToOrigPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ (t : State L16) (steps : Nat),
      steps = 6 * Q + 8 ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (∀ j < Q, t.data[sealedBase + sealedDenseToOrigOff n + j]? = s₀.data[4 * n + j]?) ∧
      (∀ addr, (addr < sealedBase + sealedDenseToOrigOff n ∨ sealedBase + sealedDenseToOrigOff n + Q ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 13 := rfl
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  have hN0 : (reg (Phase.initial s₀) rN).val = n := hRegs.consts.nVal
  obtain ⟨s1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r1_11v : (reg s1 r11).val = 2 * n := by
    rw [r1_11, add_no_wrap _ _ (by rw [hN0]; omega), hN0]; omega
  obtain ⟨s2, hs2, pc2, r2_11, p2, d2⟩ := step_add16 (code := code) (input := input) (by rw [pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r2_11v : (reg s2 r11).val = 4 * n := by
    rw [r2_11, add_no_wrap _ _ (by rw [r1_11v]; omega), r1_11v]; omega
  obtain ⟨s3, hs3, pc3, r3_12, p3, d3⟩ := step_imm16 (code := code) (input := input) (by rw [pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  obtain ⟨s4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (code := code) (input := input) (by rw [pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r4_12v : (reg s4 r12).val = sealedBase + 16 := by
    have h9_3 : (reg s3 r9).val = sealedBase := by rw [p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide)]; exact hRegs.sealedBaseVal
    rw [r4_12, add_no_wrap _ _ (by rw [h9_3, r3_12]; dsimp only; unfold sealedDenseToOrigOff at hDst; omega), h9_3, r3_12]
  obtain ⟨s5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r5_12v : (reg s5 r12).val = sealedBase + sealedDenseToOrigOff n := by
    have hN4 : (reg s4 rN).val = n := by rw [p4 rN (by decide), p3 rN (by decide), p2 rN (by decide), p1 rN (by decide)]; exact hN0
    rw [r5_12, add_no_wrap _ _ (by rw [r4_12v, hN4]; unfold sealedDenseToOrigOff at hDst; omega), r4_12v, hN4]
    unfold sealedDenseToOrigOff; omega
  obtain ⟨s6, hs6, pc6, r6_13, p6, d6⟩ := step_add16 (code := code) (input := input) (by rw [pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have hr5_11 : (reg s5 r11).val = 4 * n := by rw [p5 r11 (by decide), p4 r11 (by decide), p3 r11 (by decide)]; exact r2_11v
  have hr5_Q : (reg s5 r5).val = Q := by rw [p5 r5 (by decide), p4 r5 (by decide), p3 r5 (by decide), p2 r5 (by decide), p1 r5 (by decide)]; exact hRegs.qVal
  have r6_13v : (reg s6 r13).val = 4 * n + Q := by
    rw [r6_13, add_no_wrap _ _ (by rw [hr5_11, hr5_Q]; omega), hr5_11, hr5_Q]
  have hPl : SlicePlaced code 6 (copyLoopCode 6 12) := copyLoop_slicePlaced rfl rfl rfl rfl rfl rfl
  have hSafe : sealedBase + sealedDenseToOrigOff n + Q ≤ 4 * n ∨
      4 * n + Q ≤ sealedBase + sealedDenseToOrigOff n ∨
      sealedBase + sealedDenseToOrigOff n < 4 * n := by
    rcases hDisj with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
  obtain ⟨t, kLoop, hkLoop, hLoop, pct, tsz, _, _, _, htp, htcp, htfr⟩ :=
    run_copyLoop (input := input) hPl (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits hSrc hDst hSafe
      (by rw [pc6, pc5, pc4, pc3, pc2, pc1, h0pc]) (by rw [d6, d5, d4, d3, d2, d1]; exact hSz)
      (by rw [p6 rOne (by decide), p5 rOne (by decide), p4 rOne (by decide), p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hRegs.consts.one)
      (by rw [p6 r11 (by decide)]; exact hr5_11) (by rw [p6 r12 (by decide)]; exact r5_12v) r6_13v
  have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [pct]; rfl)
  have hRun := ((Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (step1 hs6)))))).append hLoop).halts hHalt
  have hTot : 6 + kLoop + 1 = 6 * Q + 8 := by omega
  rw [hTot] at hRun
  refine ⟨t, 6 * Q + 8, rfl, hRun, tsz, ?_, ?_, ?_⟩
  · have hPres : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → reg t r = reg s₀ r := by
      intro r h1 h2 h3 h4
      rw [htp r h1 h2 h4, p6 r h3, p5 r h2, p4 r h2, p3 r h2, p2 r h1, p1 r h1]; rfl
    exact
      { consts :=
          { zero := by rw [hPres rZero (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
            one := by rw [hPres rOne (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.one
            nVal := by rw [hPres rN (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [hPres rM (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [hPres rRoot (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [hPres r5 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.qVal
        treeBaseVal := by rw [hPres r6 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.treeBaseVal
        forestPtrsVal := by rw [hPres r7 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.forestPtrsVal
        exitPtrsVal := by rw [hPres r8 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.exitPtrsVal
        sealedBaseVal := by rw [hPres r9 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.sealedBaseVal }
  · intro j hj
    rw [show sealedBase + sealedDenseToOrigOff n + j = (sealedBase + sealedDenseToOrigOff n) + j by omega,
      htcp j hj, d6, d5, d4, d3, d2, d1]; rfl
  · intro addr hA
    rw [htfr addr hA, d6, d5, d4, d3, d2, d1]; rfl

private theorem run_copyTreeLoPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat}
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hSrc : treeBase + 2 * Q ≤ workCap) (hDst : sealedBase + sealedDomParentOff n Q + 2 * Q ≤ workCap)
    (hDisj : sealedBase + sealedDomParentOff n Q + 2 * Q ≤ treeBase ∨
      treeBase + 2 * Q ≤ sealedBase + sealedDomParentOff n Q) :
    let code := (copyTreeLoPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ (t : State L16) (steps : Nat),
      steps = 12 * Q + 9 ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (∀ j < 2 * Q, t.data[sealedBase + sealedDomParentOff n Q + j]? = s₀.data[treeBase + j]?) ∧
      (∀ addr, (addr < sealedBase + sealedDomParentOff n Q ∨
          sealedBase + sealedDomParentOff n Q + 2 * Q ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 14 := rfl
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  have hTB0 : (reg (Phase.initial s₀) r6).val = treeBase := hRegs.treeBaseVal
  obtain ⟨s1, hs1, pc1, r1_11, p1, d1⟩ := step_mov16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r1_11v : (reg s1 r11).val = treeBase := by rw [r1_11]; exact hTB0
  obtain ⟨s2, hs2, pc2, r2_12, p2, d2⟩ := step_imm16 (code := code) (input := input) (by rw [pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  obtain ⟨s3, hs3, pc3, r3_12, p3, d3⟩ := step_add16 (code := code) (input := input) (by rw [pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r3_12v : (reg s3 r12).val = sealedBase + 16 := by
    have h9_2 : (reg s2 r9).val = sealedBase := by rw [p2 r9 (by decide), p1 r9 (by decide)]; exact hRegs.sealedBaseVal
    rw [r3_12, add_no_wrap _ _ (by rw [h9_2, r2_12]; dsimp only; unfold sealedDomParentOff at hDst; omega), h9_2, r2_12]
  obtain ⟨s4, hs4, pc4, r4_12, p4, d4⟩ := step_add16 (code := code) (input := input) (by rw [pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r4_12v : (reg s4 r12).val = sealedBase + 16 + n := by
    have hN3 : (reg s3 rN).val = n := by rw [p3 rN (by decide), p2 rN (by decide), p1 rN (by decide)]; exact hRegs.consts.nVal
    rw [r4_12, add_no_wrap _ _ (by rw [r3_12v, hN3]; unfold sealedDomParentOff at hDst; omega), r3_12v, hN3]
  obtain ⟨s5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r5_12v : (reg s5 r12).val = sealedBase + sealedDomParentOff n Q := by
    have hQ4 : (reg s4 r5).val = Q := by rw [p4 r5 (by decide), p3 r5 (by decide), p2 r5 (by decide), p1 r5 (by decide)]; exact hRegs.qVal
    rw [r5_12, add_no_wrap _ _ (by rw [r4_12v, hQ4]; unfold sealedDomParentOff at hDst; omega), r4_12v, hQ4]
    unfold sealedDomParentOff; omega
  obtain ⟨s6, hs6, pc6, r6_13, p6, d6⟩ := step_add16 (code := code) (input := input) (by rw [pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have hQ5 : (reg s5 r5).val = Q := by rw [p5 r5 (by decide), p4 r5 (by decide), p3 r5 (by decide), p2 r5 (by decide), p1 r5 (by decide)]; exact hRegs.qVal
  have r6_13v : (reg s6 r13).val = 2 * Q := by
    rw [r6_13, add_no_wrap _ _ (by rw [hQ5]; unfold sealedDomParentOff at hDst; omega), hQ5]; omega
  obtain ⟨s7, hs7, pc7, r7_13, p7, d7⟩ := step_add16 (code := code) (input := input) (by rw [pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have hr6_11 : (reg s6 r11).val = treeBase := by rw [p6 r11 (by decide), p5 r11 (by decide), p4 r11 (by decide), p3 r11 (by decide), p2 r11 (by decide)]; exact r1_11v
  have r7_13v : (reg s7 r13).val = treeBase + 2 * Q := by
    rw [r7_13, add_no_wrap _ _ (by rw [hr6_11, r6_13v]; omega), hr6_11, r6_13v]
  have hPl : SlicePlaced code 7 (copyLoopCode 7 13) := copyLoop_slicePlaced rfl rfl rfl rfl rfl rfl
  have hSafe : sealedBase + sealedDomParentOff n Q + 2 * Q ≤ treeBase ∨
      treeBase + 2 * Q ≤ sealedBase + sealedDomParentOff n Q ∨
      sealedBase + sealedDomParentOff n Q < treeBase := by
    rcases hDisj with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
  obtain ⟨t, kLoop, hkLoop, hLoop, pct, tsz, _, _, _, htp, htcp, htfr⟩ :=
    run_copyLoop (input := input) hPl (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits hSrc hDst hSafe
      (by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc]) (by rw [d7, d6, d5, d4, d3, d2, d1]; exact hSz)
      (by rw [p7 rOne (by decide), p6 rOne (by decide), p5 rOne (by decide), p4 rOne (by decide), p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hRegs.consts.one)
      (by rw [p7 r11 (by decide)]; exact hr6_11) (by rw [p7 r12 (by decide), p6 r12 (by decide)]; exact r5_12v) r7_13v
  have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [pct]; rfl)
  have hRun := ((Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (step1 hs7))))))).append hLoop).halts hHalt
  have hTot : 7 + kLoop + 1 = 12 * Q + 9 := by omega
  rw [hTot] at hRun
  refine ⟨t, 12 * Q + 9, rfl, hRun, tsz, ?_, ?_, ?_⟩
  · have hPres : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → reg t r = reg s₀ r := by
      intro r h1 h2 h3 h4
      rw [htp r h1 h2 h4, p7 r h3, p6 r h3, p5 r h2, p4 r h2, p3 r h2, p2 r h2, p1 r h1]; rfl
    exact
      { consts :=
          { zero := by rw [hPres rZero (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
            one := by rw [hPres rOne (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.one
            nVal := by rw [hPres rN (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [hPres rM (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [hPres rRoot (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [hPres r5 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.qVal
        treeBaseVal := by rw [hPres r6 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.treeBaseVal
        forestPtrsVal := by rw [hPres r7 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.forestPtrsVal
        exitPtrsVal := by rw [hPres r8 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.exitPtrsVal
        sealedBaseVal := by rw [hPres r9 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.sealedBaseVal }
  · intro j hj
    rw [show sealedBase + sealedDomParentOff n Q + j = (sealedBase + sealedDomParentOff n Q) + j by omega,
      htcp j hj, d7, d6, d5, d4, d3, d2, d1]; rfl
  · intro addr hA
    rw [htfr addr hA, d7, d6, d5, d4, d3, d2, d1]; rfl

private theorem run_copyTreeHiPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase : Nat}
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hSrc : treeBase + 11 * Q ≤ workCap) (hDst : sealedBase + sealedHeadOff n Q + 8 * Q ≤ workCap)
    (hDisj : sealedBase + sealedHeadOff n Q + 8 * Q ≤ treeBase + 3 * Q ∨
      treeBase + 11 * Q ≤ sealedBase + sealedHeadOff n Q) :
    let code := (copyTreeHiPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ (t : State L16) (steps : Nat),
      steps = 48 * Q + 14 ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (∀ j < 8 * Q, t.data[sealedBase + sealedHeadOff n Q + j]? = s₀.data[treeBase + 3 * Q + j]?) ∧
      (∀ addr, (addr < sealedBase + sealedHeadOff n Q ∨
          sealedBase + sealedHeadOff n Q + 8 * Q ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  intro code
  have hCodeSz : code.size = 19 := rfl
  have h0pc : (Phase.initial s₀).pc = 0 := rfl
  have hQ0 : (reg (Phase.initial s₀) r5).val = Q := hRegs.qVal
  obtain ⟨s1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (code := code) (input := input) (s := Phase.initial s₀) (by rw [h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r1_11v : (reg s1 r11).val = 2 * Q := by
    rw [r1_11, add_no_wrap _ _ (by rw [hQ0]; omega), hQ0]; omega
  obtain ⟨s2, hs2, pc2, r2_11, p2, d2⟩ := step_add16 (code := code) (input := input) (by rw [pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r2_11v : (reg s2 r11).val = 3 * Q := by
    have hQ1 : (reg s1 r5).val = Q := by rw [p1 r5 (by decide)]; exact hQ0
    rw [r2_11, add_no_wrap _ _ (by rw [r1_11v, hQ1]; omega), r1_11v, hQ1]; omega
  obtain ⟨s3, hs3, pc3, r3_13, p3, d3⟩ := step_add16 (code := code) (input := input) (by rw [pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r3_13v : (reg s3 r13).val = treeBase + 3 * Q := by
    have h6_2 : (reg s2 r6).val = treeBase := by rw [p2 r6 (by decide), p1 r6 (by decide)]; exact hRegs.treeBaseVal
    rw [r3_13, add_no_wrap _ _ (by rw [r2_11v, h6_2]; omega), r2_11v, h6_2]; omega
  obtain ⟨s4, hs4, pc4, r4_14, p4, d4⟩ := step_imm16 (code := code) (input := input) (by rw [pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  obtain ⟨s5, hs5, pc5, r5_12, p5, d5⟩ := step_add16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r5_12v : (reg s5 r12).val = sealedBase + 16 := by
    have h9_4 : (reg s4 r9).val = sealedBase := by rw [p4 r9 (by decide), p3 r9 (by decide), p2 r9 (by decide), p1 r9 (by decide)]; exact hRegs.sealedBaseVal
    rw [r5_12, add_no_wrap _ _ (by rw [h9_4, r4_14]; dsimp only; unfold sealedHeadOff at hDst; omega), h9_4, r4_14]
  obtain ⟨s6, hs6, pc6, r6_12, p6, d6⟩ := step_add16 (code := code) (input := input) (by rw [pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r6_12v : (reg s6 r12).val = sealedBase + 16 + n := by
    have hN5 : (reg s5 rN).val = n := by rw [p5 rN (by decide), p4 rN (by decide), p3 rN (by decide), p2 rN (by decide), p1 rN (by decide)]; exact hRegs.consts.nVal
    rw [r6_12, add_no_wrap _ _ (by rw [r5_12v, hN5]; unfold sealedHeadOff at hDst; omega), r5_12v, hN5]
  obtain ⟨s7, hs7, pc7, r7_12, p7, d7⟩ := step_add16 (code := code) (input := input) (by rw [pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r7_12v : (reg s7 r12).val = sealedBase + sealedHeadOff n Q := by
    have h11_6 : (reg s6 r11).val = 3 * Q := by rw [p6 r11 (by decide), p5 r11 (by decide), p4 r11 (by decide), p3 r11 (by decide)]; exact r2_11v
    rw [r7_12, add_no_wrap _ _ (by rw [r6_12v, h11_6]; unfold sealedHeadOff at hDst; omega), r6_12v, h11_6]
    unfold sealedHeadOff; omega
  obtain ⟨s8, hs8, pc8, r8_11, p8, d8⟩ := step_mov16 (code := code) (input := input) (by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r8_11v : (reg s8 r11).val = treeBase + 3 * Q := by
    rw [r8_11, p7 r13 (by decide), p6 r13 (by decide), p5 r13 (by decide), p4 r13 (by decide)]; exact r3_13v
  have hQ8 : (reg s8 r5).val = Q := by
    rw [p8 r5 (by decide), p7 r5 (by decide), p6 r5 (by decide), p5 r5 (by decide), p4 r5 (by decide), p3 r5 (by decide), p2 r5 (by decide), p1 r5 (by decide)]
    exact hRegs.qVal
  obtain ⟨s9, hs9, pc9, r9_14, p9, d9⟩ := step_add16 (code := code) (input := input) (by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r9_14v : (reg s9 r14).val = 2 * Q := by
    rw [r9_14, add_no_wrap _ _ (by rw [hQ8]; omega), hQ8]; omega
  obtain ⟨s10, hs10, pc10, r10_14, p10, d10⟩ := step_add16 (code := code) (input := input) (by rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r10_14v : (reg s10 r14).val = 4 * Q := by
    rw [r10_14, add_no_wrap _ _ (by rw [r9_14v]; omega), r9_14v]; omega
  obtain ⟨s11, hs11, pc11, r11_14, p11, d11⟩ := step_add16 (code := code) (input := input) (by rw [pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have r11_14v : (reg s11 r14).val = 8 * Q := by
    rw [r11_14, add_no_wrap _ _ (by rw [r10_14v]; omega), r10_14v]; omega
  obtain ⟨s12, hs12, pc12, r12_13, p12, d12⟩ := step_add16 (code := code) (input := input) (by rw [pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc]; rfl) (by rw [hCodeSz]; omega)
  have hr11_11 : (reg s11 r11).val = treeBase + 3 * Q := by
    rw [p11 r11 (by decide), p10 r11 (by decide), p9 r11 (by decide)]; exact r8_11v
  have r12_13v : (reg s12 r13).val = treeBase + 3 * Q + 8 * Q := by
    rw [r12_13, add_no_wrap _ _ (by rw [hr11_11, r11_14v]; omega), hr11_11, r11_14v]
  have hPl : SlicePlaced code 12 (copyLoopCode 12 18) := copyLoop_slicePlaced rfl rfl rfl rfl rfl rfl
  have hSafe : sealedBase + sealedHeadOff n Q + 8 * Q ≤ treeBase + 3 * Q ∨
      treeBase + 3 * Q + 8 * Q ≤ sealedBase + sealedHeadOff n Q ∨
      sealedBase + sealedHeadOff n Q < treeBase + 3 * Q := by
    rcases hDisj with h | h; exact Or.inl h; exact Or.inr (Or.inl (by omega))
  obtain ⟨t, kLoop, hkLoop, hLoop, pct, tsz, _, _, _, htp, htcp, htfr⟩ :=
    run_copyLoop (input := input) hPl (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits
      (by omega) (by unfold sealedHeadOff at hDst ⊢; omega) hSafe
      (by rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, h0pc])
      (by rw [d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]; exact hSz)
      (by rw [p12 rOne (by decide), p11 rOne (by decide), p10 rOne (by decide), p9 rOne (by decide),
              p8 rOne (by decide), p7 rOne (by decide), p6 rOne (by decide), p5 rOne (by decide),
              p4 rOne (by decide), p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hRegs.consts.one)
      (by rw [p12 r11 (by decide)]; exact hr11_11)
      (by rw [p12 r12 (by decide), p11 r12 (by decide), p10 r12 (by decide), p9 r12 (by decide), p8 r12 (by decide)]; exact r7_12v)
      r12_13v
  have hHalt : step code input t = some (.halted t) := step_halt_at (by rw [pct]; rfl)
  have hS12 : Steps code input 12 (Phase.initial s₀) s12 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (step1 hs12)))))))))))
  have hRun := (hS12.append hLoop).halts hHalt
  have hTot : 12 + kLoop + 1 = 48 * Q + 14 := by omega
  rw [hTot] at hRun
  refine ⟨t, 48 * Q + 14, rfl, hRun, tsz, ?_, ?_, ?_⟩
  · have hPres : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → reg t r = reg s₀ r := by
      intro r h1 h2 h3 h4
      rw [htp r h1 h2 h4, p12 r h3, p11 r h4, p10 r h4, p9 r h4, p8 r h1,
          p7 r h2, p6 r h2, p5 r h2, p4 r h4, p3 r h3, p2 r h1, p1 r h1]; rfl
    exact
      { consts :=
          { zero := by rw [hPres rZero (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.zero
            one := by rw [hPres rOne (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.one
            nVal := by rw [hPres rN (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.nVal
            mVal := by rw [hPres rM (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.mVal
            rootVal := by rw [hPres rRoot (by decide) (by decide) (by decide) (by decide)]; exact hRegs.consts.rootVal }
        qVal := by rw [hPres r5 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.qVal
        treeBaseVal := by rw [hPres r6 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.treeBaseVal
        forestPtrsVal := by rw [hPres r7 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.forestPtrsVal
        exitPtrsVal := by rw [hPres r8 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.exitPtrsVal
        sealedBaseVal := by rw [hPres r9 (by decide) (by decide) (by decide) (by decide)]; exact hRegs.sealedBaseVal }
  · intro j hj
    rw [show sealedBase + sealedHeadOff n Q + j = (sealedBase + sealedHeadOff n Q) + j by omega,
      htcp j hj, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]; rfl
  · intro addr hA
    rw [htfr addr hA, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3, d2, d1]; rfl

theorem run_sealedHeaderPhase (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s₀ : State L16}
    {n m root Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase : Nat}
    (hn : 1 ≤ n) (hQ : 1 ≤ Q) (hQn : Q ≤ n)
    (hRegs : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase s₀)
    (hSz : s₀.data.size = workCap)
    (hDisj : SealedDisjointLayout n Q treeBase forestPtrsBase forestArenaBase forestUsed
      exitPtrsBase exitArenaBase exitUsed sealedBase workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap) :
    let ph := sealedHeaderPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32
    ∃ (t : State L16) (states : List (State L16)) (steps : Nat),
      steps ≤ 72 * n + 105 ∧
      run ph.code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace ph.code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint L16 ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase t ∧
      (t.data[sealedBase + hdrHead]?).map Fin.val = some (sealedHeadOff n Q) ∧
      (t.data[sealedBase + hdrDomParent]?).map Fin.val = some (sealedDomParentOff n Q) ∧
      (t.data[sealedBase + hdrDomDepth]?).map Fin.val = some (sealedDomDepthOff n Q) ∧
      (t.data[sealedBase + hdrOrigToDense]?).map Fin.val = some sealedOrigToDenseOff ∧
      (t.data[sealedBase + hdrN]?).map Fin.val = some n ∧
      (t.data[sealedBase + hdrQCount]?).map Fin.val = some Q ∧
      (t.data[sealedBase + hdrDenseToOrig]?).map Fin.val = some (sealedDenseToOrigOff n) ∧
      (t.data[sealedBase + hdrEntry]?).map Fin.val = some (sealedEntryOff n Q) ∧
      (t.data[sealedBase + hdrStop]?).map Fin.val = some (sealedStopOff n Q) ∧
      (t.data[sealedBase + hdrOrigOfEntry]?).map Fin.val = some (sealedOrigOfEntryOff n Q) ∧
      (t.data[sealedBase + hdrChildStart]?).map Fin.val = some (sealedChildStartOff n Q) ∧
      (t.data[sealedBase + hdrChildEntries]?).map Fin.val = some (sealedChildEntriesOff n Q) ∧
      (t.data[sealedBase + hdrChildStops]?).map Fin.val = some (sealedChildStopsOff n Q) ∧
      (t.data[sealedBase + hdrChildIds]?).map Fin.val = some (sealedChildIdsOff n Q) ∧
      (t.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q) ∧
      (t.data[sealedBase + hdrTotalWords]?).map Fin.val = some (sealedInitArenaOff n Q) ∧
      (∀ j < n, t.data[sealedBase + sealedOrigToDenseOff + j]? = s₀.data[3 * n + j]?) ∧
      (∀ j < Q, t.data[sealedBase + sealedDenseToOrigOff n + j]? = s₀.data[4 * n + j]?) ∧
      (∀ j < 2 * Q, t.data[sealedBase + sealedDomParentOff n Q + j]? = s₀.data[treeBase + j]?) ∧
      (∀ j < 8 * Q, t.data[sealedBase + sealedHeadOff n Q + j]? = s₀.data[treeBase + 3 * Q + j]?) ∧
      (∀ addr, (addr < sealedBase ∨ sealedBase + sealedOwnerDescOff n Q ≤ addr) →
        t.data[addr]? = s₀.data[addr]?) := by
  have h128 : sealedInitArenaOff n Q ≤ retainedLinearFactor * n := by
    unfold sealedInitArenaOff retainedLinearFactor; omega
  have hFitTot := hDisj.sealed_fit
  rw [retainedLinearFactor_eq] at hFitTot
  have hDisjOrig := hDisj.disj_orig
  rw [retainedLinearFactor_eq] at hDisjOrig
  have hStaticTree : staticTreeWords Q = 11 * Q := rfl
  have hArenaFit : sealedInitArenaOff n Q < 2 ^ bits := by
    unfold sealedInitArenaOff at h128 ⊢; omega
  obtain ⟨t0, ht0, t0sz, hR0, hH0, hH1, hH2, hH3, hH4, hH5, hH6, hH7, hH8, hH9, hH10, hH11, hH12, hH13, hH14, hH15, hFr0⟩ :=
    run_writeHeaderPhase h32 hBits hQ hRegs (by unfold oracleHeaderSize; unfold sealedInitArenaOff at h128; omega) hSz hArenaFit
  have hDisj1 : sealedBase + sealedOrigToDenseOff + n ≤ 3 * n ∨ 4 * n ≤ sealedBase + sealedOrigToDenseOff := by
    rcases hDisjOrig with h | h
    · unfold sealedOrigToDenseOff at *; exact Or.inl (by omega)
    · unfold sealedOrigToDenseOff at *; exact Or.inr (by omega)
  obtain ⟨t1, k1, hk1, ht1, t1sz, hR1, hCp1, hFr1⟩ :=
    run_copyOrigToDensePhase h32 hBits hR0 t0sz (by rcases hDisjOrig <;> omega)
      (by unfold sealedOrigToDenseOff at *; omega) hDisj1
  have hDisj2 : sealedBase + sealedDenseToOrigOff n + Q ≤ 4 * n ∨ 4 * n + Q ≤ sealedBase + sealedDenseToOrigOff n := by
    rcases hDisjOrig with h | h
    · unfold sealedDenseToOrigOff at *; exact Or.inl (by omega)
    · unfold sealedDenseToOrigOff at *; exact Or.inr (by omega)
  obtain ⟨t2, k2, hk2, ht2, t2sz, hR2, hCp2, hFr2⟩ :=
    run_copyDenseToOrigPhase h32 hBits hR1 t1sz (by rcases hDisjOrig <;> omega)
      (by unfold sealedDenseToOrigOff at *; omega) hDisj2
  have hDisj3 : sealedBase + sealedDomParentOff n Q + 2 * Q ≤ treeBase ∨
      treeBase + 2 * Q ≤ sealedBase + sealedDomParentOff n Q := by
    rcases hDisj.disj_tree with h | h
    · unfold sealedDomParentOff at *; rw [retainedLinearFactor_eq] at h; exact Or.inl (by omega)
    · unfold sealedDomParentOff at *; rw [hStaticTree] at h; exact Or.inr (by omega)
  obtain ⟨t3, k3, hk3, ht3, t3sz, hR3, hCp3, hFr3⟩ :=
    run_copyTreeLoPhase h32 hBits hR2 t2sz (by omega)
      (by unfold sealedDomParentOff at *; omega) hDisj3
  have hDisj4 : sealedBase + sealedHeadOff n Q + 8 * Q ≤ treeBase + 3 * Q ∨
      treeBase + 11 * Q ≤ sealedBase + sealedHeadOff n Q := by
    rcases hDisj.disj_tree with h | h
    · unfold sealedHeadOff at *; rw [retainedLinearFactor_eq] at h; exact Or.inl (by omega)
    · unfold sealedHeadOff at *; rw [hStaticTree] at h; exact Or.inr (by omega)
  obtain ⟨t4, k4, hk4, ht4, t4sz, hR4, hCp4, hFr4⟩ :=
    run_copyTreeHiPhase h32 hBits hR3 t3sz (by rw [hStaticTree] at hTreeFit; exact hTreeFit)
      (by unfold sealedHeadOff at *; omega) hDisj4
  have hPh : PhasesRun input
      [writeHeaderPhase h32, copyOrigToDensePhase h32, copyDenseToOrigPhase h32,
       copyTreeLoPhase h32, copyTreeHiPhase h32]
      s₀ (Phase.initial t4) (66 + (k1 + (k2 + (k3 + (k4 + 1))))) :=
    PhasesRun.cons ht0 (PhasesRun.cons ht1 (PhasesRun.cons ht2 (PhasesRun.cons ht3
      (PhasesRun.cons ht4 PhasesRun.nil))))
  obtain ⟨u, states, huRegs, huData, hRun, hTrace, hPeak⟩ := run_pipeline hPh
  have hCodeEq : (sealedHeaderPhase (hi := hi) (hw := hw) h32).code =
      pipeline [writeHeaderPhase h32, copyOrigToDensePhase h32, copyDenseToOrigPhase h32,
        copyTreeLoPhase h32, copyTreeHiPhase h32] := pipelinePhase_code _
  rw [← hCodeEq] at hRun hTrace
  have hEq : ∀ addr : Nat, u.data[addr]? = t4.data[addr]? := fun addr => by rw [huData]; rfl
  have hRegEq : SealedPackEntryRegs n m root Q treeBase forestPtrsBase exitPtrsBase sealedBase u :=
    { consts :=
        { zero := by rw [reg_eq_of_regs_eq huRegs rZero]; exact hR4.consts.zero
          one := by rw [reg_eq_of_regs_eq huRegs rOne]; exact hR4.consts.one
          nVal := by rw [reg_eq_of_regs_eq huRegs rN]; exact hR4.consts.nVal
          mVal := by rw [reg_eq_of_regs_eq huRegs rM]; exact hR4.consts.mVal
          rootVal := by rw [reg_eq_of_regs_eq huRegs rRoot]; exact hR4.consts.rootVal }
      qVal := by rw [reg_eq_of_regs_eq huRegs r5]; exact hR4.qVal
      treeBaseVal := by rw [reg_eq_of_regs_eq huRegs r6]; exact hR4.treeBaseVal
      forestPtrsVal := by rw [reg_eq_of_regs_eq huRegs r7]; exact hR4.forestPtrsVal
      exitPtrsVal := by rw [reg_eq_of_regs_eq huRegs r8]; exact hR4.exitPtrsVal
      sealedBaseVal := by rw [reg_eq_of_regs_eq huRegs r9]; exact hR4.sealedBaseVal }
  refine ⟨u, states, 66 + (k1 + (k2 + (k3 + (k4 + 1)))), by omega, hRun, hTrace, hPeak,
    by rw [huData]; exact t4sz, hRegEq, ?_⟩
  have f01234 : ∀ addr < sealedBase + 16, t4.data[addr]? = t0.data[addr]? := fun addr h => by
    unfold sealedOrigToDenseOff sealedDenseToOrigOff sealedDomParentOff sealedHeadOff at *
    rw [hFr4 addr (Or.inl (by omega)), hFr3 addr (Or.inl (by omega)),
      hFr2 addr (Or.inl (by omega)), hFr1 addr (Or.inl (by omega))]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hEq, f01234 _ (by unfold hdrHead; omega)]; exact hH0
  · rw [hEq, f01234 _ (by unfold hdrDomParent; omega)]; exact hH1
  · rw [hEq, f01234 _ (by unfold hdrDomDepth; omega)]; exact hH2
  · rw [hEq, f01234 _ (by unfold hdrOrigToDense; omega)]; exact hH3
  · rw [hEq, f01234 _ (by unfold hdrN; omega)]; exact hH4
  · rw [hEq, f01234 _ (by unfold hdrQCount; omega)]; exact hH5
  · rw [hEq, f01234 _ (by unfold hdrDenseToOrig; omega)]; exact hH6
  · rw [hEq, f01234 _ (by unfold hdrEntry; omega)]; exact hH7
  · rw [hEq, f01234 _ (by unfold hdrStop; omega)]; exact hH8
  · rw [hEq, f01234 _ (by unfold hdrOrigOfEntry; omega)]; exact hH9
  · rw [hEq, f01234 _ (by unfold hdrChildStart; omega)]; exact hH10
  · rw [hEq, f01234 _ (by unfold hdrChildEntries; omega)]; exact hH11
  · rw [hEq, f01234 _ (by unfold hdrChildStops; omega)]; exact hH12
  · rw [hEq, f01234 _ (by unfold hdrChildIds; omega)]; exact hH13
  · rw [hEq, f01234 _ (by unfold hdrOwnerDesc; omega)]; exact hH14
  · rw [hEq, f01234 _ (by unfold hdrTotalWords; omega)]; exact hH15
  · intro j hj
    unfold sealedOrigToDenseOff sealedDenseToOrigOff sealedDomParentOff sealedHeadOff oracleHeaderSize at *
    rw [hEq, hFr4 _ (Or.inl (by omega)), hFr3 _ (Or.inl (by omega)),
      hFr2 _ (Or.inl (by omega)), hCp1 j hj,
      hFr0 _ (by rcases hDisjOrig with h | h; exact Or.inr (by omega); exact Or.inl (by omega))]
  · intro j hj
    unfold sealedOrigToDenseOff sealedDenseToOrigOff sealedDomParentOff sealedHeadOff oracleHeaderSize at *
    rw [hEq, hFr4 _ (Or.inl (by omega)), hFr3 _ (Or.inl (by omega)),
      hCp2 j hj,
      hFr1 _ (by rcases hDisjOrig with h | h; exact Or.inr (by omega); exact Or.inl (by omega)),
      hFr0 _ (by rcases hDisjOrig with h | h; exact Or.inr (by omega); exact Or.inl (by omega))]
  · intro j hj
    unfold sealedOrigToDenseOff sealedDenseToOrigOff sealedDomParentOff sealedHeadOff oracleHeaderSize at *
    rw [hEq, hFr4 _ (Or.inl (by omega)), hCp3 j hj,
      hFr2 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega)),
      hFr1 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega)),
      hFr0 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega))]
  · intro j hj
    unfold sealedOrigToDenseOff sealedDenseToOrigOff sealedDomParentOff sealedHeadOff oracleHeaderSize at *
    rw [hEq, hCp4 j hj,
      hFr3 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega)),
      hFr2 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega)),
      hFr1 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega)),
      hFr0 _ (by rcases hDisj.disj_tree with h | h; rw [retainedLinearFactor_eq] at h; exact Or.inr (by omega); rw [hStaticTree] at h; exact Or.inl (by omega))]
  · intro addr hOut
    unfold sealedOwnerDescOff sealedOrigToDenseOff sealedDenseToOrigOff sealedDomParentOff sealedHeadOff oracleHeaderSize at *
    rw [hEq]
    rcases hOut with h | h
    · rw [hFr4 addr (Or.inl (by omega)), hFr3 addr (Or.inl (by omega)),
        hFr2 addr (Or.inl (by omega)), hFr1 addr (Or.inl (by omega)), hFr0 addr (Or.inl (by omega))]
    · rw [hFr4 addr (Or.inr (by omega)), hFr3 addr (Or.inr (by omega)),
        hFr2 addr (Or.inr (by omega)), hFr1 addr (Or.inr (by omega)), hFr0 addr (Or.inr (by omega))]

private theorem run_zeroLoop {code : Program L16} {input : Input L16}
    (h28 : code[28]? = some (.branchLt r11 r12 29 32))
    (h29 : code[29]? = some (.storeData r11 rZero))
    (h30 : code[30]? = some (.add r11 r11 rOne))
    (h31 : code[31]? = some (.goto 28))
    (hFit : 32 < code.size) (_hBits : workCap < 2 ^ bits)
    {base : Nat} (hBnd : base + 10 ≤ workCap)
    {s₀ : State L16} (hPC : s₀.pc = 28) (hSz : s₀.data.size = workCap)
    (hZero : (reg s₀ rZero).val = 0) (hOne : (reg s₀ rOne).val = 1)
    (h11 : (reg s₀ r11).val = base + 1) (h12 : (reg s₀ r12).val = base + 10) :
    ∃ t : State L16, Steps code input 37 s₀ t ∧ t.pc = 32 ∧
      t.data.size = workCap ∧
      (∀ r : Fin 16, r ≠ r11 → reg t r = reg s₀ r) ∧
      (∀ k, 1 ≤ k → k < 10 → (t.data[base + k]?).map Fin.val = some 0) ∧
      (∀ addr, (addr < base + 1 ∨ base + 10 ≤ addr) → t.data[addr]? = s₀.data[addr]?) := by
  let inv : Nat → State L16 → Prop := fun rem s =>
    rem ≤ 9 ∧ s.pc = 28 ∧ s.data.size = workCap ∧
    (reg s rZero).val = 0 ∧ (reg s rOne).val = 1 ∧
    (reg s r11).val = base + 1 + (9 - rem) ∧ (reg s r12).val = base + 10 ∧
    (∀ r : Fin 16, r ≠ r11 → reg s r = reg s₀ r) ∧
    (∀ k, 1 ≤ k → k < 1 + (9 - rem) → (s.data[base + k]?).map Fin.val = some 0) ∧
    (∀ addr, (addr < base + 1 ∨ base + 1 + (9 - rem) ≤ addr) → s.data[addr]? = s₀.data[addr]?)
  have hStep : ∀ rem s, inv rem s →
      (rem = 0 ∧ ∃ t, step code input s = some (.next t) ∧ t.pc = 32 ∧ t.regs = s.regs ∧ t.data = s.data) ∨
      (0 < rem ∧ ∃ s', Steps code input 4 s s' ∧ inv (rem - 1) s') := by
    intro rem s ⟨hRm, hpc, hsz, hz, ho, h11s, h12s, hpres, hzero, hfr⟩
    by_cases h0 : rem = 0
    · left; refine ⟨h0, ?_⟩
      have hF : WordOps.ltb (reg s r11) (reg s r12) = false :=
        branchLt_false (by rw [h11s, h12s, h0]; omega)
      have hBr := step_branchLt_at (code := code) (input := input) (by rw [hpc]; exact h28) (by rw [hF, ite_eq_right (by decide)]; exact hFit)
      rw [hF, ite_eq_right (by decide)] at hBr; exact ⟨_, hBr, rfl, rfl, rfl⟩
    · right; refine ⟨Nat.pos_of_ne_zero h0, ?_⟩
      have hT : WordOps.ltb (reg s r11) (reg s r12) = true :=
        branchLt_true (by rw [h11s, h12s]; omega)
      have hBr := step_branchLt_at (code := code) (input := input) (by rw [hpc]; exact h28) (by rw [hT, ite_eq_left rfl]; omega)
      rw [hT, ite_eq_left rfl] at hBr
      let s1 : State L16 := { s with pc := 29 }
      have hBnd1 : (reg s1 r11).val < s1.data.size := by
        change (reg s r11).val < s.data.size; rw [h11s, hsz]; omega
      have hs1pc : s1.pc = 29 := rfl
      obtain ⟨s2, hs2, pc2, hregs2, d2⟩ :=
        step_storeData16 (code := code) (input := input) (s := s1) (by rw [hs1pc]; exact h29) (by rw [hs1pc]; omega) hBnd1
      obtain ⟨s3, hs3, pc3, r3_11, p3, d3⟩ :=
        step_add16 (code := code) (input := input) (by rw [pc2, hs1pc]; exact h30) (by rw [pc2, hs1pc]; omega)
      have hGo := step_goto_at (code := code) (input := input) (s := s3) (target := 28)
        (by rw [pc3, pc2]; exact h31) (by omega)
      let s4 : State L16 := { s3 with pc := 28 }
      have r3_11v : (reg s3 r11).val = base + 1 + (9 - (rem - 1)) := by
        have hr2_11 : (reg s2 r11).val = base + 1 + (9 - rem) := by
          rw [reg_eq_of_regs_eq hregs2 r11]; exact h11s
        have hr2_1 : (reg s2 rOne).val = 1 := by
          rw [reg_eq_of_regs_eq hregs2 rOne]; exact ho
        rw [r3_11, add_no_wrap _ _ (by rw [hr2_11, hr2_1]; omega), hr2_11, hr2_1]; omega
      have hPres4 : ∀ r : Fin 16, r ≠ r11 → reg s4 r = reg s₀ r := fun r hr => by
        change reg s3 r = reg s₀ r
        rw [p3 r hr, reg_eq_of_regs_eq hregs2 r]
        exact hpres r hr
      refine ⟨s4, Steps.cons hBr (Steps.cons hs2 (Steps.cons hs3 (step1 hGo))),
        by omega, rfl, by change s3.data.size = workCap; rw [d3, d2, Array.size_set]; exact hsz,
        by rw [hPres4 rZero (by decide)]; exact hZero,
        by rw [hPres4 rOne (by decide)]; exact hOne,
        r3_11v,
        by rw [hPres4 r12 (by decide)]; exact h12,
        hPres4, ?_, ?_⟩
      · intro k hk1 hk2
        change (s3.data[base + k]?).map Fin.val = some 0
        rw [d3, d2]
        by_cases hkk : k = 1 + (9 - rem)
        · have hSet : base + k = (reg s1 r11).val := by change _ = (reg s r11).val; rw [h11s]; omega
          rw [hSet, Array.getElem?_set_self, Option.map_some, show (reg s1 rZero).val = 0 from hz]
        · rw [Array.getElem?_set_ne _ (by change (reg s r11).val ≠ base + k; rw [h11s]; omega)]
          exact hzero k hk1 (by omega)
      · intro addr hA
        change s3.data[addr]? = s₀.data[addr]?
        rw [d3, d2]
        have hNe : (reg s1 r11).val ≠ addr := by change (reg s r11).val ≠ addr; rw [h11s]; omega
        rw [Array.getElem?_set_ne _ hNe]
        exact hfr addr (by rcases hA with h | h; exact Or.inl h; exact Or.inr (by omega))
  have hInd : ∀ rem s, inv rem s →
      ∃ t, Steps code input (4 * rem + 1) s t ∧ t.pc = 32 ∧ t.data.size = workCap ∧
        (∀ r : Fin 16, r ≠ r11 → reg t r = reg s₀ r) ∧
        (∀ k, 1 ≤ k → k < 10 → (t.data[base + k]?).map Fin.val = some 0) ∧
        (∀ addr, (addr < base + 1 ∨ base + 10 ≤ addr) → t.data[addr]? = s₀.data[addr]?) := by
    intro rem
    induction rem with
    | zero =>
      intro s hI
      rcases hStep 0 s hI with ⟨_, t, hs, hpc, hregs, hdata⟩ | ⟨hPos, _⟩
      · rcases hI with ⟨_, _, hsz, _, _, _, _, hpres, hzero, hfr⟩
        refine ⟨t, step1 hs, hpc, by rw [hdata]; exact hsz,
          fun r hr => by rw [reg_eq_of_regs_eq hregs r]; exact hpres r hr,
          fun k hk1 hk2 => by rw [hdata]; exact hzero k hk1 (by omega),
          fun addr hA => by rw [hdata]; exact hfr addr (by rcases hA with h | h; exact Or.inl h; exact Or.inr (by omega))⟩
      · exact (Nat.lt_irrefl 0 hPos).elim
    | succ rem ih =>
      intro s hI
      rcases hStep (rem + 1) s hI with ⟨h0, _⟩ | ⟨_, s', h4, hI'⟩
      · exact absurd h0 (Nat.succ_ne_zero rem)
      · obtain ⟨t, hTail, rest⟩ := ih s' (by simpa [Nat.add_sub_cancel] using hI')
        refine ⟨t, ?_, rest⟩
        exact (show 4 + (4 * rem + 1) = 4 * (rem + 1) + 1 by omega) ▸ h4.append hTail
  exact hInd 9 s₀ ⟨Nat.le_refl _, hPC, hSz, hZero, hOne, by omega, h12,
    fun _ _ => rfl, fun k hk1 hk2 => by omega, fun _ _ => rfl⟩

private theorem run_writeDescDeltaStep {code : Program L16} {input : Input L16}
    {pc fpBase dPos fp0 curOff fpVal : Nat}
    (hFit : pc + 6 < code.size) (hBits : workCap < 2 ^ bits)
    (hc0 : code[pc]? = some (.add r11 r11 rOne))
    (hc1 : code[pc + 1]? = some (.loadData r14 r11))
    (hc2 : code[pc + 2]? = some (.sub r14 r14 r13))
    (hc3 : code[pc + 3]? = some (.add r14 r12 r14))
    (hc4 : code[pc + 4]? = some (.add r15 r15 rOne))
    (hc5 : code[pc + 5]? = some (.storeData r15 r14))
    {s₀ : State L16} (hPC : s₀.pc = pc) (hSz : s₀.data.size = workCap)
    (hOne : (reg s₀ rOne).val = 1) (h11 : (reg s₀ r11).val = fpBase)
    (h12 : (reg s₀ r12).val = curOff) (h13 : (reg s₀ r13).val = fp0)
    (h15 : (reg s₀ r15).val = dPos)
    (hFpBnd : fpBase + 1 < workCap) (hFpLe : fp0 ≤ fpVal) (hSumFit : curOff + (fpVal - fp0) < 2 ^ bits)
    (hDBnd : dPos + 1 < workCap) (hVal : (s₀.data[fpBase + 1]?).map Fin.val = some fpVal) :
    ∃ t : State L16, Steps code input 6 s₀ t ∧ t.pc = pc + 6 ∧
      t.data.size = workCap ∧
      (reg t r11).val = fpBase + 1 ∧
      (reg t r15).val = dPos + 1 ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r14 → r ≠ r15 → reg t r = reg s₀ r) ∧
      (t.data[dPos + 1]?).map Fin.val = some (curOff + (fpVal - fp0)) ∧
      (∀ addr, addr ≠ dPos + 1 → t.data[addr]? = s₀.data[addr]?) := by
  obtain ⟨s1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (code := code) (input := input) (by rw [hPC]; exact hc0) (by omega)
  have r1_11v : (reg s1 r11).val = fpBase + 1 := by
    rw [r1_11, add_no_wrap _ _ (by rw [h11, hOne]; omega), h11, hOne]
  have hL : ∃ w, s1.data[(reg s1 r11).val]? = some w ∧ w.val = fpVal := by
    rw [r1_11v, d1]
    cases hG : s₀.data[fpBase + 1]? with
    | none => rw [hG] at hVal; cases hVal
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hVal; exact ⟨w, rfl, hVal⟩
  obtain ⟨w, hwS, hwV⟩ := hL
  obtain ⟨s2, hs2, pc2, r2_14, p2, d2⟩ := step_loadData16 (code := code) (input := input) (by rw [pc1, hPC]; exact hc1) hwS (by rw [pc1, hPC]; omega)
  obtain ⟨s3, hs3, pc3, r3_14, p3, d3⟩ := step_sub16 (code := code) (input := input) (by rw [pc2, pc1, hPC]; exact hc2) (by rw [pc2, pc1, hPC]; omega)
  have r3_14v : (reg s3 r14).val = fpVal - fp0 := by
    have h13_2 : (reg s2 r13).val = fp0 := by rw [p2 r13 (by decide), p1 r13 (by decide)]; exact h13
    rw [r3_14, sub_exact _ _ (by rw [r2_14, hwV, h13_2]; exact hFpLe), r2_14, hwV, h13_2]
  obtain ⟨s4, hs4, pc4, r4_14, p4, d4⟩ := step_add16 (code := code) (input := input) (by rw [pc3, pc2, pc1, hPC]; exact hc3) (by rw [pc3, pc2, pc1, hPC]; omega)
  have r4_14v : (reg s4 r14).val = curOff + (fpVal - fp0) := by
    have h12_3 : (reg s3 r12).val = curOff := by rw [p3 r12 (by decide), p2 r12 (by decide), p1 r12 (by decide)]; exact h12
    rw [r4_14, add_no_wrap _ _ (by rw [h12_3, r3_14v]; exact hSumFit), h12_3, r3_14v]
  obtain ⟨s5, hs5, pc5, r5_15, p5, d5⟩ := step_add16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, hPC]; exact hc4) (by rw [pc4, pc3, pc2, pc1, hPC]; omega)
  have r5_15v : (reg s5 r15).val = dPos + 1 := by
    have h15_4 : (reg s4 r15).val = dPos := by rw [p4 r15 (by decide), p3 r15 (by decide), p2 r15 (by decide), p1 r15 (by decide)]; exact h15
    have h1_4 : (reg s4 rOne).val = 1 := by rw [p4 rOne (by decide), p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hOne
    rw [r5_15, add_no_wrap _ _ (by rw [h15_4, h1_4]; omega), h15_4, h1_4]
  have hBnd5 : (reg s5 r15).val < s5.data.size := by
    rw [r5_15v, d5, d4, d3, d2, d1, hSz]; exact hDBnd
  obtain ⟨s6, hs6, pc6, hregs6, d6⟩ := step_storeData16 (code := code) (input := input) (by rw [pc5, pc4, pc3, pc2, pc1, hPC]; exact hc5) (by rw [pc5, pc4, pc3, pc2, pc1, hPC]; omega) hBnd5
  refine ⟨s6, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (step1 hs6))))),
    by omega, by rw [d6, Array.size_set, d5, d4, d3, d2, d1, hSz], ?_, ?_, ?_, ?_, ?_⟩
  · rw [reg_eq_of_regs_eq hregs6 r11, p5 r11 (by decide), p4 r11 (by decide), p3 r11 (by decide), p2 r11 (by decide)]; exact r1_11v
  · rw [reg_eq_of_regs_eq hregs6 r15]; exact r5_15v
  · intro r hr11 hr14 hr15
    rw [reg_eq_of_regs_eq hregs6 r, p5 r hr15, p4 r hr14, p3 r hr14, p2 r hr14, p1 r hr11]
  · rw [d6, ← r5_15v, Array.getElem?_set_self, Option.map_some, p5 r14 (by decide), r4_14v]
  · intro addr hNe
    rw [d6, Array.getElem?_set_ne _ (by rw [r5_15v]; exact hNe.symm), d5, d4, d3, d2, d1]

private theorem run_fpNStep (h32 : 32 ≤ 2 ^ bits) {code : Program L16} {input : Input L16}
    {pc d forestPtrsBase fp4 fp5 : Nat}
    (hFit : pc + 10 < code.size) (hBits : workCap < 2 ^ bits)
    (hc0 : code[pc]? = some (.add r11 r10 r10))
    (hc1 : code[pc + 1]? = some (.add r13 r11 r11))
    (hc2 : code[pc + 2]? = some (.add r11 r11 r13))
    (hc3 : code[pc + 3]? = some (.add r11 r7 r11))
    (hc4 : code[pc + 4]? = some (.imm r13 ⟨4, by omega⟩))
    (hc5 : code[pc + 5]? = some (.add r11 r11 r13))
    (hc6 : code[pc + 6]? = some (.loadData r14 r11))
    (hc7 : code[pc + 7]? = some (.add r11 r11 rOne))
    (hc8 : code[pc + 8]? = some (.loadData r11 r11))
    (hc9 : code[pc + 9]? = some (.sub r14 r11 r14))
    {s₀ : State L16} (hPC : s₀.pc = pc) (hSz : s₀.data.size = workCap)
    (hOne : (reg s₀ rOne).val = 1) (h7 : (reg s₀ r7).val = forestPtrsBase)
    (h10 : (reg s₀ r10).val = d)
    (hFBnd : forestPtrsBase + 6 * d + 6 ≤ workCap)
    (hFp4 : (s₀.data[forestPtrsBase + 6 * d + 4]?).map Fin.val = some fp4)
    (hFp5 : (s₀.data[forestPtrsBase + 6 * d + 5]?).map Fin.val = some fp5)
    (hFpLe : fp4 ≤ fp5) :
    ∃ t : State L16, Steps code input 10 s₀ t ∧ t.pc = pc + 10 ∧
      t.data = s₀.data ∧
      (reg t r14).val = fp5 - fp4 ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r13 → r ≠ r14 → reg t r = reg s₀ r) := by
  obtain ⟨s1, hs1, pc1, r1_11, p1, d1⟩ := step_add16 (code := code) (input := input) (by rw [hPC]; exact hc0) (by omega)
  have r1_11v : (reg s1 r11).val = 2 * d := by
    rw [r1_11, add_no_wrap _ _ (by rw [h10]; omega), h10]; omega
  obtain ⟨s2, hs2, pc2, r2_13, p2, d2⟩ := step_add16 (code := code) (input := input) (by rw [pc1, hPC]; exact hc1) (by omega)
  have r2_13v : (reg s2 r13).val = 4 * d := by
    rw [r2_13, add_no_wrap _ _ (by rw [r1_11v]; omega), r1_11v]; omega
  obtain ⟨s3, hs3, pc3, r3_11, p3, d3⟩ := step_add16 (code := code) (input := input) (by rw [pc2, pc1, hPC]; exact hc2) (by omega)
  have r3_11v : (reg s3 r11).val = 6 * d := by
    have hr2_11 : (reg s2 r11).val = 2 * d := by rw [p2 r11 (by decide)]; exact r1_11v
    rw [r3_11, add_no_wrap _ _ (by rw [hr2_11, r2_13v]; omega), hr2_11, r2_13v]; omega
  obtain ⟨s4, hs4, pc4, r4_11, p4, d4⟩ := step_add16 (code := code) (input := input) (by rw [pc3, pc2, pc1, hPC]; exact hc3) (by omega)
  have r4_11v : (reg s4 r11).val = forestPtrsBase + 6 * d := by
    have hr3_7 : (reg s3 r7).val = forestPtrsBase := by
      rw [p3 r7 (by decide), p2 r7 (by decide), p1 r7 (by decide)]; exact h7
    rw [r4_11, add_no_wrap _ _ (by rw [hr3_7, r3_11v]; omega), hr3_7, r3_11v]
  obtain ⟨s5, hs5, pc5, r5_13, p5, d5⟩ := step_imm16 (code := code) (input := input) (by rw [pc4, pc3, pc2, pc1, hPC]; exact hc4) (by omega)
  obtain ⟨s6, hs6, pc6, r6_11, p6, d6⟩ := step_add16 (code := code) (input := input) (by rw [pc5, pc4, pc3, pc2, pc1, hPC]; exact hc5) (by omega)
  have r6_11v : (reg s6 r11).val = forestPtrsBase + 6 * d + 4 := by
    have hr5_11 : (reg s5 r11).val = forestPtrsBase + 6 * d := by rw [p5 r11 (by decide)]; exact r4_11v
    rw [r6_11, add_no_wrap _ _ (by rw [hr5_11, r5_13]; dsimp only; omega), hr5_11, r5_13]
  have hd6 : s6.data = s₀.data := by rw [d6, d5, d4, d3, d2, d1]
  have hL4 : ∃ w4, s6.data[(reg s6 r11).val]? = some w4 ∧ w4.val = fp4 := by
    rw [hd6, r6_11v]
    cases hG : s₀.data[forestPtrsBase + 6 * d + 4]? with
    | none => rw [hG] at hFp4; cases hFp4
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hFp4; exact ⟨w, rfl, hFp4⟩
  obtain ⟨w4, hw4, hw4V⟩ := hL4
  obtain ⟨s7, hs7, pc7, r7_14, p7, d7⟩ := step_loadData16 (code := code) (input := input) (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hPC]; exact hc6) hw4 (by rw [pc6, pc5, pc4, pc3, pc2, pc1, hPC]; omega)
  obtain ⟨s8, hs8, pc8, r8_11, p8, d8⟩ := step_add16 (code := code) (input := input) (by rw [pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]; exact hc7) (by omega)
  have r8_11v : (reg s8 r11).val = forestPtrsBase + 6 * d + 5 := by
    have hr7_11 : (reg s7 r11).val = forestPtrsBase + 6 * d + 4 := by rw [p7 r11 (by decide)]; exact r6_11v
    have hr7_1 : (reg s7 rOne).val = 1 := by
      rw [p7 rOne (by decide), p6 rOne (by decide), p5 rOne (by decide), p4 rOne (by decide),
        p3 rOne (by decide), p2 rOne (by decide), p1 rOne (by decide)]; exact hOne
    rw [r8_11, add_no_wrap _ _ (by rw [hr7_11, hr7_1]; omega), hr7_11, hr7_1]
  have hd8 : s8.data = s₀.data := by rw [d8, d7, hd6]
  have hL5 : ∃ w5, s8.data[(reg s8 r11).val]? = some w5 ∧ w5.val = fp5 := by
    rw [hd8, r8_11v]
    cases hG : s₀.data[forestPtrsBase + 6 * d + 5]? with
    | none => rw [hG] at hFp5; cases hFp5
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hFp5; exact ⟨w, rfl, hFp5⟩
  obtain ⟨w5, hw5, hw5V⟩ := hL5
  obtain ⟨s9, hs9, pc9, r9_11, p9, d9⟩ := step_loadData16 (code := code) (input := input) (by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]; exact hc8) hw5 (by rw [pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]; omega)
  obtain ⟨s10, hs10, pc10, r10_14, p10, d10⟩ := step_sub16 (code := code) (input := input) (by rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, pc2, pc1, hPC]; exact hc9) (by omega)
  have r9_14v : (reg s9 r14).val = fp4 := by
    rw [p9 r14 (by decide), p8 r14 (by decide), r7_14, hw4V]
  refine ⟨s10,
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (step1 hs10))))))))),
    by omega, by rw [d10, d9, hd8], ?_, ?_⟩
  · rw [r10_14, sub_exact _ _ (by rw [r9_11, hw5V, r9_14v]; exact hFpLe), r9_11, hw5V, r9_14v]
  · intro r hr11 hr13 hr14
    rw [p10 r hr14, p9 r hr11, p8 r hr11, p7 r hr14, p6 r hr11, p5 r hr13, p4 r hr11, p3 r hr11, p2 r hr13, p1 r hr11]

theorem sealedOwners_preamble (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s : State L16}
    {n Q treeBase sealedBase d cs0 cs1 nD descBase : Nat}
    (hDescBaseEq : descBase = sealedBase + sealedOwnerDescOff n Q + ownerDescStride * d)
    (hnDEq : nD = 1 + (cs1 - cs0))
    (hOne : (reg s rOne).val = 1) (hQVal : (reg s r5).val = Q)
    (hTBVal : (reg s r6).val = treeBase) (hSBVal : (reg s r9).val = sealedBase)
    (h10Val : (reg s r10).val = d) (hdLt : d < Q)
    (hpc : s.pc = 1) (hsz : s.data.size = workCap)
    (hDescPtr : (s.data[sealedBase + hdrOwnerDesc]?).map Fin.val = some (sealedOwnerDescOff n Q))
    (hDescFit : descBase + ownerDescStride ≤ workCap)
    (hTreeFit : treeBase + staticTreeWords Q ≤ workCap)
    (hSBHdr : sealedBase + hdrOwnerDesc < workCap)
    (hCS0 : (s.data[treeBase + 7 * Q + d]?).map Fin.val = some cs0)
    (hCS1 : (s.data[treeBase + 7 * Q + d + 1]?).map Fin.val = some cs1)
    (hMonoCS : cs0 ≤ cs1) (hCS_le : cs1 - cs0 ≤ Q - 1) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s24 : State L16,
      Steps code input 23 s s24 ∧ s24.pc = 24 ∧ s24.data.size = workCap ∧
      (reg s24 r11).val = nD ∧ (reg s24 r12).val = 3 ∧ (reg s24 r15).val = descBase ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r15 → reg s24 r = reg s r) ∧
      (s24.data[descBase + descN]?).map Fin.val = some nD ∧
      (∀ addr, addr ≠ descBase → s24.data[addr]? = s.data[addr]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  have hTrue1 : WordOps.ltb (reg s r10) (reg s r5) = true :=
    branchLt_true (by rw [h10Val, hQVal]; exact hdLt)
  have hs1 := step_branchLt_at (code := code) (input := input) (by rw [hpc, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hTrue1, ite_eq_left rfl, hCodeSz]; omega)
  rw [hTrue1, ite_eq_left rfl] at hs1
  let s2 : State L16 := { s with pc := 2 }
  have hpc2 : s2.pc = 2 := rfl
  obtain ⟨s3, hs3, pc3, r3_15, p3, d3⟩ := step_imm16 (code := code) (input := input) (s := s2) (by rw [hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hpc2, hCodeSz]; omega)
  obtain ⟨s4, hs4, pc4, r4_15, p4, d4⟩ := step_add16 (code := code) (input := input) (by rw [pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hCodeSz]; omega)
  have r4_15v : (reg s4 r15).val = sealedBase + hdrOwnerDesc := by
    have h9_3 : (reg s3 r9).val = sealedBase := by rw [p3 r9 (by decide)]; exact hSBVal
    have hDFit : descBase + ownerDescStride ≤ workCap := hDescFit
    rw [hDescBaseEq, ownerDescStride_eq] at hDFit
    unfold sealedOwnerDescOff at hDFit
    rw [r4_15, add_no_wrap _ _ (by rw [h9_3, r3_15]; dsimp only; rw [hdrOwnerDesc_eq]; omega), h9_3, r3_15]
  have hd4 : s4.data = s.data := by rw [d4, d3]
  have hLDesc : ∃ wD, s4.data[(reg s4 r15).val]? = some wD ∧ wD.val = sealedOwnerDescOff n Q := by
    rw [hd4, r4_15v]
    cases hG : s.data[sealedBase + hdrOwnerDesc]? with
    | none => rw [hG] at hDescPtr; cases hDescPtr
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hDescPtr; exact ⟨w, rfl, hDescPtr⟩
  obtain ⟨wD, hwD, hwDV⟩ := hLDesc
  obtain ⟨s5, hs5, pc5, r5_15, p5, d5⟩ := step_loadData16 (code := code) (input := input) (by rw [pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) hwD (by rw [pc4, pc3, hpc2, hCodeSz]; omega)
  obtain ⟨s6, hs6, pc6, r6_15, p6, d6⟩ := step_add16 (code := code) (input := input) (by rw [pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r6_15v : (reg s6 r15).val = sealedBase + sealedOwnerDescOff n Q := by
    have h9_5 : (reg s5 r9).val = sealedBase := by rw [p5 r9 (by decide), p4 r9 (by decide), p3 r9 (by decide)]; exact hSBVal
    rw [r6_15, add_no_wrap _ _ (by rw [h9_5, r5_15, hwDV]; rw [hDescBaseEq, ownerDescStride_eq] at hDescFit; omega), h9_5, r5_15, hwDV]
  have hd6 : (reg s6 r10).val = d := by rw [p6 r10 (by decide), p5 r10 (by decide), p4 r10 (by decide), p3 r10 (by decide)]; exact h10Val
  obtain ⟨s7, hs7, pc7, r7_11, p7, d7⟩ := step_add16 (code := code) (input := input) (by rw [pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r7_11v : (reg s7 r11).val = 2 * d := by rw [r7_11, add_no_wrap _ _ (by rw [hd6]; rw [hDescBaseEq, ownerDescStride_eq] at hDescFit; omega), hd6]; omega
  obtain ⟨s8, hs8, pc8, r8_12, p8, d8⟩ := step_add16 (code := code) (input := input) (by rw [pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r8_12v : (reg s8 r12).val = 4 * d := by rw [r8_12, add_no_wrap _ _ (by rw [r7_11v]; rw [hDescBaseEq, ownerDescStride_eq] at hDescFit; omega), r7_11v]; omega
  obtain ⟨s9, hs9, pc9, r9_12, p9, d9⟩ := step_add16 (code := code) (input := input) (by rw [pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r9_12v : (reg s9 r12).val = 8 * d := by rw [r9_12, add_no_wrap _ _ (by rw [r8_12v]; rw [hDescBaseEq, ownerDescStride_eq] at hDescFit; omega), r8_12v]; omega
  obtain ⟨s10, hs10, pc10, r10_11, p10, d10⟩ := step_add16 (code := code) (input := input) (by rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r10_11v : (reg s10 r11).val = 10 * d := by
    have hr9_11 : (reg s9 r11).val = 2 * d := by rw [p9 r11 (by decide), p8 r11 (by decide)]; exact r7_11v
    rw [r10_11, add_no_wrap _ _ (by rw [hr9_11, r9_12v]; rw [hDescBaseEq, ownerDescStride_eq] at hDescFit; omega), hr9_11, r9_12v]; omega
  obtain ⟨s11, hs11, pc11, r11_15, p11, d11⟩ := step_add16 (code := code) (input := input) (by rw [pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r11_15v : (reg s11 r15).val = descBase := by
    have hr10_15 : (reg s10 r15).val = sealedBase + sealedOwnerDescOff n Q := by
      rw [p10 r15 (by decide), p9 r15 (by decide), p8 r15 (by decide), p7 r15 (by decide)]; exact r6_15v
    have hDFit : descBase + ownerDescStride ≤ workCap := hDescFit
    rw [hDescBaseEq, ownerDescStride_eq] at hDFit
    rw [r11_15, add_no_wrap _ _ (by rw [hr10_15, r10_11v]; omega), hr10_15, r10_11v, hDescBaseEq, ownerDescStride_eq]
  have hPres11 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r15 → reg s11 r = reg s r := fun r h1 h2 h5 => by
    rw [p11 r h5, p10 r h1, p9 r h2, p8 r h2, p7 r h1, p6 r h5, p5 r h5, p4 r h5, p3 r h5]; rfl
  obtain ⟨s12, hs12, pc12, r12_11, p12, d12⟩ := step_add16 (code := code) (input := input) (by rw [pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r12_11v : (reg s12 r11).val = 2 * Q := by
    have hQ11 : (reg s11 r5).val = Q := by rw [hPres11 r5 (by decide) (by decide) (by decide)]; exact hQVal
    rw [r12_11, add_no_wrap _ _ (by rw [hQ11]; unfold staticTreeWords at hTreeFit; omega), hQ11]; omega
  obtain ⟨s13, hs13, pc13, r13_12, p13, d13⟩ := step_add16 (code := code) (input := input) (by rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r13_12v : (reg s13 r12).val = 4 * Q := by rw [r13_12, add_no_wrap _ _ (by rw [r12_11v]; unfold staticTreeWords at hTreeFit; omega), r12_11v]; omega
  obtain ⟨s14, hs14, pc14, r14_12, p14, d14⟩ := step_add16 (code := code) (input := input) (by rw [pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r14_12v : (reg s14 r12).val = 6 * Q := by
    have hr13_11 : (reg s13 r11).val = 2 * Q := by rw [p13 r11 (by decide)]; exact r12_11v
    rw [r14_12, add_no_wrap _ _ (by rw [r13_12v, hr13_11]; unfold staticTreeWords at hTreeFit; omega), r13_12v, hr13_11]; omega
  obtain ⟨s15, hs15, pc15, r15_12, p15, d15⟩ := step_add16 (code := code) (input := input) (by rw [pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have hQ14 : (reg s14 r5).val = Q := by
    rw [p14 r5 (by decide), p13 r5 (by decide), p12 r5 (by decide), hPres11 r5 (by decide) (by decide) (by decide)]; exact hQVal
  have r15_12v : (reg s15 r12).val = 7 * Q := by
    rw [r15_12, add_no_wrap _ _ (by rw [r14_12v, hQ14]; unfold staticTreeWords at hTreeFit; omega), r14_12v, hQ14]; omega
  obtain ⟨s16, hs16, pc16, r16_12, p16, d16⟩ := step_add16 (code := code) (input := input) (by rw [pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have h6_15 : (reg s15 r6).val = treeBase := by
    rw [p15 r6 (by decide), p14 r6 (by decide), p13 r6 (by decide), p12 r6 (by decide), hPres11 r6 (by decide) (by decide) (by decide)]; exact hTBVal
  have r16_12v : (reg s16 r12).val = treeBase + 7 * Q := by
    rw [r16_12, add_no_wrap _ _ (by rw [r15_12v, h6_15]; unfold staticTreeWords at hTreeFit; omega), r15_12v, h6_15]; omega
  obtain ⟨s17, hs17, pc17, r17_12, p17, d17⟩ := step_add16 (code := code) (input := input) (by rw [pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have h10_16 : (reg s16 r10).val = d := by
    rw [p16 r10 (by decide), p15 r10 (by decide), p14 r10 (by decide), p13 r10 (by decide), p12 r10 (by decide), hPres11 r10 (by decide) (by decide) (by decide)]; exact h10Val
  have r17_12v : (reg s17 r12).val = treeBase + 7 * Q + d := by
    rw [r17_12, add_no_wrap _ _ (by rw [r16_12v, h10_16]; unfold staticTreeWords at hTreeFit; omega), r16_12v, h10_16]
  have hd17 : s17.data = s.data := by rw [d17, d16, d15, d14, d13, d12, d11, d10, d9, d8, d7, d6, d5, d4, d3]
  have hLCS0 : ∃ wc0, s17.data[(reg s17 r12).val]? = some wc0 ∧ wc0.val = cs0 := by
    rw [hd17, r17_12v]
    cases hG : s.data[treeBase + 7 * Q + d]? with
    | none => rw [hG] at hCS0; cases hCS0
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hCS0; exact ⟨w, rfl, hCS0⟩
  obtain ⟨wc0, hwc0, hwc0V⟩ := hLCS0
  obtain ⟨s18, hs18, pc18, r18_11, p18, d18⟩ := step_loadData16 (code := code) (input := input) (by rw [pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) hwc0 (by rw [pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  obtain ⟨s19, hs19, pc19, r19_12, p19, d19⟩ := step_add16 (code := code) (input := input) (by rw [pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have r19_12v : (reg s19 r12).val = treeBase + 7 * Q + d + 1 := by
    have hr18_12 : (reg s18 r12).val = treeBase + 7 * Q + d := by rw [p18 r12 (by decide)]; exact r17_12v
    have hr18_1 : (reg s18 rOne).val = 1 := by
      rw [p18 rOne (by decide), p17 rOne (by decide), p16 rOne (by decide), p15 rOne (by decide),
        p14 rOne (by decide), p13 rOne (by decide), p12 rOne (by decide),
        hPres11 rOne (by decide) (by decide) (by decide)]; exact hOne
    rw [r19_12, add_no_wrap _ _ (by rw [hr18_12, hr18_1]; unfold staticTreeWords at hTreeFit; omega), hr18_12, hr18_1]
  have hLCS1 : ∃ wc1, s19.data[(reg s19 r12).val]? = some wc1 ∧ wc1.val = cs1 := by
    rw [r19_12v, d19, d18, hd17]
    cases hG : s.data[treeBase + 7 * Q + d + 1]? with
    | none => rw [hG] at hCS1; cases hCS1
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hCS1; exact ⟨w, rfl, hCS1⟩
  obtain ⟨wc1, hwc1, hwc1V⟩ := hLCS1
  obtain ⟨s20, hs20, pc20, r20_12, p20, d20⟩ := step_loadData16 (code := code) (input := input) (by rw [pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) hwc1 (by rw [pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  obtain ⟨s21, hs21, pc21, r21_11, p21, d21⟩ := step_sub16 (code := code) (input := input) (by rw [pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have hr20_11 : (reg s20 r11).val = cs0 := by rw [p20 r11 (by decide), p19 r11 (by decide), r18_11, hwc0V]
  have r21_11v : (reg s21 r11).val = cs1 - cs0 := by
    rw [r21_11, sub_exact _ _ (by rw [r20_12, hwc1V, hr20_11]; exact hMonoCS), r20_12, hwc1V, hr20_11]
  obtain ⟨s22, hs22, pc22, r22_11, p22, d22⟩ := step_add16 (code := code) (input := input) (by rw [pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have hPres22 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r15 → reg s22 r = reg s r := fun r h1 h2 h5 => by
    rw [p22 r h1, p21 r h1, p20 r h2, p19 r h2, p18 r h1, p17 r h2, p16 r h2, p15 r h2, p14 r h2, p13 r h2, p12 r h1, hPres11 r h1 h2 h5]
  have h1_21 : (reg s21 rOne).val = 1 := by
    rw [p21 rOne (by decide), p20 rOne (by decide), p19 rOne (by decide), p18 rOne (by decide),
      p17 rOne (by decide), p16 rOne (by decide), p15 rOne (by decide), p14 rOne (by decide),
      p13 rOne (by decide), p12 rOne (by decide), hPres11 rOne (by decide) (by decide) (by decide)]; exact hOne
  have r22_11v : (reg s22 r11).val = nD := by
    rw [r22_11, add_no_wrap _ _ (by rw [r21_11v, h1_21]; unfold staticTreeWords at hTreeFit; omega), r21_11v, h1_21, hnDEq]; omega
  have hr22_15 : (reg s22 r15).val = descBase := by
    rw [p22 r15 (by decide), p21 r15 (by decide), p20 r15 (by decide), p19 r15 (by decide),
      p18 r15 (by decide), p17 r15 (by decide), p16 r15 (by decide), p15 r15 (by decide),
      p14 r15 (by decide), p13 r15 (by decide), p12 r15 (by decide)]; exact r11_15v
  have hBnd22 : (reg s22 r15).val < s22.data.size := by
    rw [hr22_15, d22, d21, d20, d19, d18, hd17, hsz]; rw [ownerDescStride_eq] at hDescFit; omega
  obtain ⟨s23, hs23, pc23, hregs23, d23⟩ :=
    step_storeData16 (code := code) (input := input) (by rw [pc22, pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl)
      (by rw [pc22, pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega) hBnd22
  obtain ⟨s24, hs24, pc24, r24_12, p24, d24⟩ := step_imm16 (code := code) (input := input) (by rw [pc23, pc22, pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc23, pc22, pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2, hCodeSz]; omega)
  have hS24Entry : Steps code input 23 s s24 :=
    Steps.cons hs1 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7
      (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13
        (Steps.cons hs14 (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (Steps.cons hs19
          (Steps.cons hs20 (Steps.cons hs21 (Steps.cons hs22 (Steps.cons hs23 (step1 hs24))))))))))))))))))))))
  refine ⟨s24, hS24Entry, by rw [pc24, pc23, pc22, pc21, pc20, pc19, pc18, pc17, pc16, pc15, pc14, pc13, pc12, pc11, pc10, pc9, pc8, pc7, pc6, pc5, pc4, pc3, hpc2],
    by rw [d24, d23, Array.size_set, d22, d21, d20, d19, d18, hd17, hsz],
    by rw [p24 r11 (by decide), reg_eq_of_regs_eq hregs23 r11]; exact r22_11v,
    by rw [r24_12],
    by rw [p24 r15 (by decide), reg_eq_of_regs_eq hregs23 r15]; exact hr22_15,
    fun r h1 h2 h5 => by rw [p24 r h2, reg_eq_of_regs_eq hregs23 r, hPres22 r h1 h2 h5],
    ?_, ?_⟩
  · rw [d24, d23, descN_eq, Nat.add_zero, ← hr22_15, Array.getElem?_set_self, Option.map_some, r22_11v]
  · intro addr hNe
    rw [d24, d23, Array.getElem?_set_ne _ (by rw [hr22_15]; exact hNe.symm), d22, d21, d20, d19, d18, hd17]

theorem sealedOwners_small_step (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s24 : State L16}
    {d nD descBase : Nat}
    (hpc24 : s24.pc = 24) (hsz24 : s24.data.size = workCap)
    (hZero24 : (reg s24 rZero).val = 0) (hOne24 : (reg s24 rOne).val = 1)
    (h10_24 : (reg s24 r10).val = d) (h11_24 : (reg s24 r11).val = nD)
    (h12_24 : (reg s24 r12).val = 3) (h15_24 : (reg s24 r15).val = descBase)
    (hSmall : nD < 3) (hDescFit : descBase + ownerDescStride ≤ workCap) (hd1 : d + 1 < workCap) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ sNext : State L16,
      Steps code input 43 s24 sNext ∧ sNext.pc = 1 ∧ sNext.data.size = workCap ∧
      (reg sNext r10).val = d + 1 ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → r ≠ r12 → r ≠ r15 → reg sNext r = reg s24 r) ∧
      (∀ k, 1 ≤ k → k < 10 → (sNext.data[descBase + k]?).map Fin.val = some 0) ∧
      (∀ addr, (addr < descBase + 1 ∨ descBase + 10 ≤ addr) → sNext.data[addr]? = s24.data[addr]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  have hT24 : WordOps.ltb (reg s24 r11) (reg s24 r12) = true :=
    branchLt_true (by rw [h11_24, h12_24]; exact hSmall)
  have hs25 := step_branchLt_at (code := code) (input := input) (by rw [hpc24, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hT24, ite_eq_left rfl, hCodeSz]; omega)
  rw [hT24, ite_eq_left rfl] at hs25
  let s25 : State L16 := { s24 with pc := 25 }
  have hpc25 : s25.pc = 25 := rfl
  obtain ⟨s26, hs26, pc26, r26_11, p26, d26⟩ := step_add16 (code := code) (input := input) (s := s25) (by rw [hpc25, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hpc25, hCodeSz]; omega)
  have r26_11v : (reg s26 r11).val = descBase + 1 := by
    rw [r26_11, add_no_wrap _ _ (by change (reg s24 r15).val + (reg s24 rOne).val < 2 ^ bits; rw [h15_24, hOne24, ownerDescStride_eq] at *; omega)]
    change (reg s24 r15).val + (reg s24 rOne).val = _; rw [h15_24, hOne24]
  obtain ⟨s27, hs27, pc27, r27_12, p27, d27⟩ := step_imm16 (code := code) (input := input) (by rw [pc26, hpc25, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc26, hpc25, hCodeSz]; omega)
  obtain ⟨s28, hs28, pc28, r28_12, p28, d28⟩ := step_add16 (code := code) (input := input) (by rw [pc27, pc26, hpc25, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc27, pc26, hpc25, hCodeSz]; omega)
  have r28_12v : (reg s28 r12).val = descBase + 10 := by
    have hr27_15 : (reg s27 r15).val = descBase := by rw [p27 r15 (by decide), p26 r15 (by decide)]; exact h15_24
    rw [r28_12, add_no_wrap _ _ (by rw [hr27_15, r27_12]; dsimp only; rw [ownerDescStride_eq] at hDescFit ⊢; omega), hr27_15, r27_12]
  have hPres28 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r15 → reg s28 r = reg s24 r := fun r h1 h2 _ => by
    rw [p28 r h2, p27 r h2, p26 r h1]; rfl
  obtain ⟨s32, hs32, pc32, sz32, p32, wz32, frz32⟩ :=
    run_zeroLoop (code := code) (input := input)
      (by rw [hCodeEq, so_fetch0a h32 (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch0a h32 (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch0a h32 (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch0a h32 (by decide)]; rfl)
      (by rw [hCodeSz]; omega) hBits
      (base := descBase) (by rw [ownerDescStride_eq] at hDescFit; exact hDescFit)
      (by rw [pc28, pc27, pc26, hpc25]) (by rw [d28, d27, d26]; exact hsz24)
      (by rw [hPres28 rZero (by decide) (by decide) (by decide)]; exact hZero24)
      (by rw [hPres28 rOne (by decide) (by decide) (by decide)]; exact hOne24)
      (by rw [p28 r11 (by decide), p27 r11 (by decide)]; exact r26_11v) r28_12v
  obtain ⟨s33, hs33, pc33, r33_10, p33, d33⟩ := step_add16 (code := code) (input := input) (by rw [pc32, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc32, hCodeSz]; omega)
  have r33_10v : (reg s33 r10).val = d + 1 := by
    have h10_32 : (reg s32 r10).val = d := by rw [p32 r10 (by decide), hPres28 r10 (by decide) (by decide) (by decide)]; exact h10_24
    have h1_32 : (reg s32 rOne).val = 1 := by rw [p32 rOne (by decide), hPres28 rOne (by decide) (by decide) (by decide)]; exact hOne24
    rw [r33_10, add_no_wrap _ _ (by rw [h10_32, h1_32]; omega), h10_32, h1_32]
  have hGo33 := step_goto_at (code := code) (input := input) (s := s33) (target := 1) (by rw [pc33, pc32, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hCodeSz]; omega)
  let sNext : State L16 := { s33 with pc := 1 }
  refine ⟨sNext, Steps.cons hs25 (Steps.cons hs26 (Steps.cons hs27 (Steps.cons hs28 (hs32.append (Steps.cons hs33 (step1 hGo33)))))),
    rfl, by change s33.data.size = workCap; rw [d33]; exact sz32, r33_10v,
    fun r h0 h1 h2 h5 => by change reg s33 r = reg s24 r; rw [p33 r h0, p32 r h1]; exact hPres28 r h1 h2 h5,
    fun k hk1 hk2 => by change (s33.data[descBase + k]?).map Fin.val = some 0; rw [d33]; exact wz32 k hk1 hk2,
    fun addr hOut => by change s33.data[addr]? = s24.data[addr]?; rw [d33, frz32 addr hOut, d28, d27, d26]⟩

private theorem sealedOwners_large_write5DescDeltas (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s44 : State L16}
    {descBase fpBase curOff fp0 fp1 fp2 fp3 fp4 fp5 : Nat}
    (hpc44 : s44.pc = 44) (hSz44 : s44.data.size = workCap)
    (hOne44 : (reg s44 rOne).val = 1) (hr44_11 : (reg s44 r11).val = fpBase)
    (hr44_12 : (reg s44 r12).val = curOff) (hr44_13 : (reg s44 r13).val = fp0)
    (hr44_15 : (reg s44 r15).val = descBase + 1)
    (hDescFit : descBase + ownerDescStride ≤ workCap)
    (hFPBnd : fpBase + 6 ≤ workCap)
    (hFpLe1 : fp0 ≤ fp1) (hFpLe2 : fp0 ≤ fp2) (hFpLe3 : fp0 ≤ fp3)
    (hFpLe4 : fp0 ≤ fp4) (hFpLe5 : fp0 ≤ fp5)
    (hSum1 : curOff + (fp1 - fp0) < 2 ^ bits) (hSum2 : curOff + (fp2 - fp0) < 2 ^ bits)
    (hSum3 : curOff + (fp3 - fp0) < 2 ^ bits) (hSum4 : curOff + (fp4 - fp0) < 2 ^ bits)
    (hSum5 : curOff + (fp5 - fp0) < 2 ^ bits)
    (hFPDisj : ∀ k ≤ 5, fpBase + k < descBase + 1 ∨ descBase + 7 ≤ fpBase + k)
    (hFpRd1 : (s44.data[fpBase + 1]?).map Fin.val = some fp1)
    (hFpRd2 : (s44.data[fpBase + 2]?).map Fin.val = some fp2)
    (hFpRd3 : (s44.data[fpBase + 3]?).map Fin.val = some fp3)
    (hFpRd4 : (s44.data[fpBase + 4]?).map Fin.val = some fp4)
    (hFpRd5 : (s44.data[fpBase + 5]?).map Fin.val = some fp5) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s74 : State L16,
      Steps code input 30 s44 s74 ∧ s74.pc = 74 ∧ s74.data.size = workCap ∧
      (reg s74 r11).val = fpBase + 5 ∧ (reg s74 r15).val = descBase + 6 ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r14 → r ≠ r15 → reg s74 r = reg s44 r) ∧
      (s74.data[descBase + descBackFst]?).map Fin.val = some (curOff + (fp1 - fp0)) ∧
      (s74.data[descBase + descBackSnd]?).map Fin.val = some (curOff + (fp2 - fp0)) ∧
      (s74.data[descBase + descLabels]?).map Fin.val = some (curOff + (fp3 - fp0)) ∧
      (s74.data[descBase + descFEntry]?).map Fin.val = some (curOff + (fp4 - fp0)) ∧
      (s74.data[descBase + descFStop]?).map Fin.val = some (curOff + (fp5 - fp0)) ∧
      (∀ addr, (addr < descBase + 2 ∨ descBase + 7 ≤ addr) → s74.data[addr]? = s44.data[addr]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  have hc44 : code[44]? = some (.add r11 r11 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc45 : code[45]? = some (.loadData r14 r11) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc46 : code[46]? = some (.sub r14 r14 r13) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc47 : code[47]? = some (.add r14 r12 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc48 : code[48]? = some (.add r15 r15 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc49 : code[49]? = some (.storeData r15 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  obtain ⟨s50, hs50, pc50, sz50, r50_11, r50_15, p50, w50, fr50⟩ :=
    run_writeDescDeltaStep (code := code) (input := input) (pc := 44) (fpBase := fpBase) (dPos := descBase + 1)
      (fp0 := fp0) (curOff := curOff) (fpVal := fp1) (by rw [hCodeSz]; omega) hBits
      hc44 hc45 hc46 hc47 hc48 hc49 hpc44 hSz44 hOne44 hr44_11 hr44_12 hr44_13 hr44_15
      (by omega) hFpLe1 hSum1 (by rw [ownerDescStride_eq] at hDescFit; omega) hFpRd1
  have hc50 : code[50]? = some (.add r11 r11 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc51 : code[51]? = some (.loadData r14 r11) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc52 : code[52]? = some (.sub r14 r14 r13) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc53 : code[53]? = some (.add r14 r12 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc54 : code[54]? = some (.add r15 r15 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc55 : code[55]? = some (.storeData r15 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  obtain ⟨s56, hs56, pc56, sz56, r56_11, r56_15, p56, w56, fr56⟩ :=
    run_writeDescDeltaStep (code := code) (input := input) (pc := 50) (fpBase := fpBase + 1) (dPos := descBase + 2)
      (fp0 := fp0) (curOff := curOff) (fpVal := fp2) (by rw [hCodeSz]; omega) hBits
      hc50 hc51 hc52 hc53 hc54 hc55 pc50 sz50
      (by rw [p50 rOne (by decide) (by decide) (by decide)]; exact hOne44)
      r50_11 (by rw [p50 r12 (by decide) (by decide) (by decide)]; exact hr44_12)
      (by rw [p50 r13 (by decide) (by decide) (by decide)]; exact hr44_13) r50_15
      (by omega) hFpLe2 hSum2 (by rw [ownerDescStride_eq] at hDescFit; omega)
      (by change (s50.data[fpBase + 2]?).map Fin.val = some fp2
          rw [fr50 _ (by rcases hFPDisj 2 (by decide) with h | h <;> omega)]; exact hFpRd2)
  have hc56 : code[56]? = some (.add r11 r11 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc57 : code[57]? = some (.loadData r14 r11) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc58 : code[58]? = some (.sub r14 r14 r13) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc59 : code[59]? = some (.add r14 r12 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc60 : code[60]? = some (.add r15 r15 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc61 : code[61]? = some (.storeData r15 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  obtain ⟨s62, hs62, pc62, sz62, r62_11, r62_15, p62, w62, fr62⟩ :=
    run_writeDescDeltaStep (code := code) (input := input) (pc := 56) (fpBase := fpBase + 2) (dPos := descBase + 3)
      (fp0 := fp0) (curOff := curOff) (fpVal := fp3) (by rw [hCodeSz]; omega) hBits
      hc56 hc57 hc58 hc59 hc60 hc61 pc56 sz56
      (by rw [p56 rOne (by decide) (by decide) (by decide), p50 rOne (by decide) (by decide) (by decide)]; exact hOne44)
      r56_11 (by rw [p56 r12 (by decide) (by decide) (by decide), p50 r12 (by decide) (by decide) (by decide)]; exact hr44_12)
      (by rw [p56 r13 (by decide) (by decide) (by decide), p50 r13 (by decide) (by decide) (by decide)]; exact hr44_13) r56_15
      (by omega) hFpLe3 hSum3 (by rw [ownerDescStride_eq] at hDescFit; omega)
      (by change (s56.data[fpBase + 3]?).map Fin.val = some fp3
          rw [fr56 _ (by rcases hFPDisj 3 (by decide) with h | h <;> omega),
            fr50 _ (by rcases hFPDisj 3 (by decide) with h | h <;> omega)]; exact hFpRd3)
  have hc62 : code[62]? = some (.add r11 r11 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc63 : code[63]? = some (.loadData r14 r11) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc64 : code[64]? = some (.sub r14 r14 r13) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc65 : code[65]? = some (.add r14 r12 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc66 : code[66]? = some (.add r15 r15 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc67 : code[67]? = some (.storeData r15 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  obtain ⟨s68, hs68, pc68, sz68, r68_11, r68_15, p68, w68, fr68⟩ :=
    run_writeDescDeltaStep (code := code) (input := input) (pc := 62) (fpBase := fpBase + 3) (dPos := descBase + 4)
      (fp0 := fp0) (curOff := curOff) (fpVal := fp4) (by rw [hCodeSz]; omega) hBits
      hc62 hc63 hc64 hc65 hc66 hc67 pc62 sz62
      (by rw [p62 rOne (by decide) (by decide) (by decide), p56 rOne (by decide) (by decide) (by decide), p50 rOne (by decide) (by decide) (by decide)]; exact hOne44)
      r62_11 (by rw [p62 r12 (by decide) (by decide) (by decide), p56 r12 (by decide) (by decide) (by decide), p50 r12 (by decide) (by decide) (by decide)]; exact hr44_12)
      (by rw [p62 r13 (by decide) (by decide) (by decide), p56 r13 (by decide) (by decide) (by decide), p50 r13 (by decide) (by decide) (by decide)]; exact hr44_13) r62_15
      (by omega) hFpLe4 hSum4 (by rw [ownerDescStride_eq] at hDescFit; omega)
      (by change (s62.data[fpBase + 4]?).map Fin.val = some fp4
          rw [fr62 _ (by rcases hFPDisj 4 (by decide) with h | h <;> omega),
            fr56 _ (by rcases hFPDisj 4 (by decide) with h | h <;> omega),
            fr50 _ (by rcases hFPDisj 4 (by decide) with h | h <;> omega)]; exact hFpRd4)
  have hc68 : code[68]? = some (.add r11 r11 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc69 : code[69]? = some (.loadData r14 r11) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc70 : code[70]? = some (.sub r14 r14 r13) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc71 : code[71]? = some (.add r14 r12 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc72 : code[72]? = some (.add r15 r15 rOne) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  have hc73 : code[73]? = some (.storeData r15 r14) := by rw [hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl
  obtain ⟨s74, hs74, pc74, sz74, r74_11, r74_15, p74, w74, fr74⟩ :=
    run_writeDescDeltaStep (code := code) (input := input) (pc := 68) (fpBase := fpBase + 4) (dPos := descBase + 5)
      (fp0 := fp0) (curOff := curOff) (fpVal := fp5) (by rw [hCodeSz]; omega) hBits
      hc68 hc69 hc70 hc71 hc72 hc73 pc68 sz68
      (by rw [p68 rOne (by decide) (by decide) (by decide), p62 rOne (by decide) (by decide) (by decide), p56 rOne (by decide) (by decide) (by decide), p50 rOne (by decide) (by decide) (by decide)]; exact hOne44)
      r68_11 (by rw [p68 r12 (by decide) (by decide) (by decide), p62 r12 (by decide) (by decide) (by decide), p56 r12 (by decide) (by decide) (by decide), p50 r12 (by decide) (by decide) (by decide)]; exact hr44_12)
      (by rw [p68 r13 (by decide) (by decide) (by decide), p62 r13 (by decide) (by decide) (by decide), p56 r13 (by decide) (by decide) (by decide), p50 r13 (by decide) (by decide) (by decide)]; exact hr44_13) r68_15
      (by omega) hFpLe5 hSum5 (by rw [ownerDescStride_eq] at hDescFit; omega)
      (by change (s68.data[fpBase + 5]?).map Fin.val = some fp5
          rw [fr68 _ (by rcases hFPDisj 5 (by decide) with h | h <;> omega),
            fr62 _ (by rcases hFPDisj 5 (by decide) with h | h <;> omega),
            fr56 _ (by rcases hFPDisj 5 (by decide) with h | h <;> omega),
            fr50 _ (by rcases hFPDisj 5 (by decide) with h | h <;> omega)]; exact hFpRd5)
  refine ⟨s74, hs50.append (hs56.append (hs62.append (hs68.append hs74))), pc74, sz74, r74_11, r74_15,
    fun r h1 h4 h5 => by rw [p74 r h1 h4 h5, p68 r h1 h4 h5, p62 r h1 h4 h5, p56 r h1 h4 h5, p50 r h1 h4 h5],
    ?_, ?_, ?_, ?_, w74, fun addr hOut => by
      rw [fr74 addr (by omega), fr68 addr (by omega), fr62 addr (by omega), fr56 addr (by omega), fr50 addr (by omega)]⟩
  · rw [fr74 _ (by rw [descBackFst_eq]; omega), fr68 _ (by rw [descBackFst_eq]; omega),
      fr62 _ (by rw [descBackFst_eq]; omega), fr56 _ (by rw [descBackFst_eq]; omega), descBackFst_eq]
    exact w50
  · rw [fr74 _ (by rw [descBackSnd_eq]; omega), fr68 _ (by rw [descBackSnd_eq]; omega),
      fr62 _ (by rw [descBackSnd_eq]; omega), descBackSnd_eq]
    exact w56
  · rw [fr74 _ (by rw [descLabels_eq]; omega), fr68 _ (by rw [descLabels_eq]; omega), descLabels_eq]
    exact w62
  · rw [fr74 _ (by rw [descFEntry_eq]; omega), descFEntry_eq]
    exact w68

set_option maxHeartbeats 2000000 in
theorem sealedOwners_large_forest (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s24 : State L16}
    {d nD descBase forestPtrsBase sealedBase curOff fp0 fp1 fp2 fp3 fp4 fp5 N_d D wc : Nat}
    (hpc24 : s24.pc = 24) (hsz24 : s24.data.size = workCap)
    (hOne24 : (reg s24 rOne).val = 1) (h7_24 : (reg s24 r7).val = forestPtrsBase)
    (h9_24 : (reg s24 r9).val = sealedBase) (h10_24 : (reg s24 r10).val = d)
    (h11_24 : (reg s24 r11).val = nD) (h12_24 : (reg s24 r12).val = 3)
    (h15_24 : (reg s24 r15).val = descBase)
    (hLarge : 3 ≤ nD) (hDescFit : descBase + ownerDescStride ≤ workCap)
    (hDescBefore : descBase + 7 ≤ sealedBase + curOff)
    (hFPBnd : forestPtrsBase + 6 * d + 6 ≤ workCap)
    (hTotFit : sealedBase + hdrTotalWords < workCap)
    (hTot24 : (s24.data[sealedBase + hdrTotalWords]?).map Fin.val = some curOff)
    (hFP0 : (s24.data[forestPtrsBase + 6 * d]?).map Fin.val = some fp0)
    (hFP1 : (s24.data[forestPtrsBase + 6 * d + 1]?).map Fin.val = some fp1)
    (hFP2 : (s24.data[forestPtrsBase + 6 * d + 2]?).map Fin.val = some fp2)
    (hFP3 : (s24.data[forestPtrsBase + 6 * d + 3]?).map Fin.val = some fp3)
    (hFP4 : (s24.data[forestPtrsBase + 6 * d + 4]?).map Fin.val = some fp4)
    (hFP5 : (s24.data[forestPtrsBase + 6 * d + 5]?).map Fin.val = some fp5)
    (hD1 : fp1 = fp0 + (1 + 3 * D)) (hD2 : fp2 = fp1 + (nD + 1)) (hD3 : fp3 = fp2 + (nD + 1))
    (hD4 : fp4 = fp3 + nD) (hD5 : fp5 = fp4 + N_d)
    (hWcEq : wc = (fp5 - fp0) + N_d)
    (hFPFit : fp0 + wc ≤ workCap) (hDstFit : sealedBase + curOff + wc ≤ workCap)
    (hFPDisj : ∀ k ≤ 5, forestPtrsBase + 6 * d + k < descBase + 1 ∨ descBase + 7 ≤ forestPtrsBase + 6 * d + k)
    (hFPArenaDisj : ∀ k < wc, fp0 + k < descBase + 1 ∨ descBase + 7 ≤ fp0 + k)
    (hSafeF : sealedBase + curOff + wc ≤ fp0 ∨ fp0 + wc ≤ sealedBase + curOff ∨ sealedBase + curOff < fp0) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s91 : State L16,
      Steps code input (52 + (6 * wc + 1)) s24 s91 ∧ s91.pc = 91 ∧ s91.data.size = workCap ∧
      (reg s91 r12).val = sealedBase + (curOff + wc) ∧ (reg s91 r15).val = descBase ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s91 r = reg s24 r) ∧
      (s91.data[descBase + descDict]?).map Fin.val = some curOff ∧
      (s91.data[descBase + descBackFst]?).map Fin.val = some (curOff + (fp1 - fp0)) ∧
      (s91.data[descBase + descBackSnd]?).map Fin.val = some (curOff + (fp2 - fp0)) ∧
      (s91.data[descBase + descLabels]?).map Fin.val = some (curOff + (fp3 - fp0)) ∧
      (s91.data[descBase + descFEntry]?).map Fin.val = some (curOff + (fp4 - fp0)) ∧
      (s91.data[descBase + descFStop]?).map Fin.val = some (curOff + (fp5 - fp0)) ∧
      (∀ addr, (addr < descBase + 1 ∨ descBase + 7 ≤ addr) →
        (addr < sealedBase + curOff ∨ sealedBase + curOff + wc ≤ addr) →
        s91.data[addr]? = s24.data[addr]?) ∧
      (∀ k < wc, s91.data[sealedBase + curOff + k]? = s24.data[fp0 + k]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  have hF24 : WordOps.ltb (reg s24 r11) (reg s24 r12) = false :=
    branchLt_false (by rw [h11_24, h12_24]; exact hLarge)
  have hs25 := step_branchLt_at (code := code) (input := input) (by rw [hpc24, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hF24, ite_eq_right (by decide), hCodeSz]; omega)
  rw [hF24, ite_eq_right (by decide)] at hs25
  let s34 : State L16 := { s24 with pc := 34 }
  have hpc34 : s34.pc = 34 := rfl
  obtain ⟨s35, hs35, pc35, r35_11, p35, d35⟩ := step_add16 (code := code) (input := input) (s := s34) (by rw [hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [hpc34, hCodeSz]; omega)
  have r35_11v : (reg s35 r11).val = 2 * d := by
    have hr10_34 : (reg s34 r10).val = d := h10_24
    rw [r35_11, add_no_wrap _ _ (by rw [hr10_34]; omega), hr10_34]; omega
  obtain ⟨s36, hs36, pc36, r36_12, p36, d36⟩ := step_add16 (code := code) (input := input) (by rw [pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc35, hpc34, hCodeSz]; omega)
  have r36_12v : (reg s36 r12).val = 4 * d := by rw [r36_12, add_no_wrap _ _ (by rw [r35_11v]; omega), r35_11v]; omega
  obtain ⟨s37, hs37, pc37, r37_11, p37, d37⟩ := step_add16 (code := code) (input := input) (by rw [pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc36, pc35, hpc34, hCodeSz]; omega)
  have r37_11v : (reg s37 r11).val = 6 * d := by
    have hr36_11 : (reg s36 r11).val = 2 * d := by rw [p36 r11 (by decide)]; exact r35_11v
    rw [r37_11, add_no_wrap _ _ (by rw [hr36_11, r36_12v]; omega), hr36_11, r36_12v]; omega
  obtain ⟨s38, hs38, pc38, r38_11, p38, d38⟩ := step_add16 (code := code) (input := input) (by rw [pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc37, pc36, pc35, hpc34, hCodeSz]; omega)
  have h7_37 : (reg s37 r7).val = forestPtrsBase := by
    rw [p37 r7 (by decide), p36 r7 (by decide), p35 r7 (by decide)]; exact h7_24
  let fpBase := forestPtrsBase + 6 * d
  have r38_11v : (reg s38 r11).val = fpBase := by
    rw [r38_11, add_no_wrap _ _ (by rw [h7_37, r37_11v]; omega), h7_37, r37_11v]
  obtain ⟨s39, hs39, pc39, r39_13, p39, d39⟩ := step_imm16 (code := code) (input := input) (by rw [pc38, pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc38, pc37, pc36, pc35, hpc34, hCodeSz]; omega)
  obtain ⟨s40, hs40, pc40, r40_13, p40, d40⟩ := step_add16 (code := code) (input := input) (by rw [pc39, pc38, pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc39, pc38, pc37, pc36, pc35, hpc34, hCodeSz]; omega)
  have r40_13v : (reg s40 r13).val = sealedBase + hdrTotalWords := by
    have h9_39 : (reg s39 r9).val = sealedBase := by
      rw [p39 r9 (by decide), p38 r9 (by decide), p37 r9 (by decide), p36 r9 (by decide), p35 r9 (by decide)]; exact h9_24
    have hTFit := hTotFit
    rw [hdrTotalWords_eq] at hTFit
    rw [r40_13, add_no_wrap _ _ (by rw [h9_39, r39_13]; dsimp only; rw [hdrTotalWords_eq]; omega), h9_39, r39_13]
  have hd40 : s40.data = s24.data := by rw [d40, d39, d38, d37, d36, d35]
  have hLCur : ∃ wC, s40.data[(reg s40 r13).val]? = some wC ∧ wC.val = curOff := by
    rw [hd40, r40_13v]
    cases hG : s24.data[sealedBase + hdrTotalWords]? with
    | none => rw [hG] at hTot24; cases hTot24
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hTot24; exact ⟨w, rfl, hTot24⟩
  obtain ⟨wC, hwC, hwCV⟩ := hLCur
  obtain ⟨s41, hs41, pc41, r41_12, p41, d41⟩ := step_loadData16 (code := code) (input := input) (by rw [pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) hwC (by rw [pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeSz]; omega)
  have hr41_11 : (reg s41 r11).val = fpBase := by rw [p41 r11 (by decide), p40 r11 (by decide), p39 r11 (by decide)]; exact r38_11v
  have hLFp0 : ∃ w0, s41.data[(reg s41 r11).val]? = some w0 ∧ w0.val = fp0 := by
    rw [d41, hd40, hr41_11]
    cases hG : s24.data[forestPtrsBase + 6 * d]? with
    | none => rw [hG] at hFP0; cases hFP0
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hFP0; exact ⟨w, rfl, hFP0⟩
  obtain ⟨w0, hw0, hw0V⟩ := hLFp0
  obtain ⟨s42, hs42, pc42, r42_13, p42, d42⟩ := step_loadData16 (code := code) (input := input) (by rw [pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) hw0 (by rw [pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeSz]; omega)
  obtain ⟨s43, hs43, pc43, r43_15, p43, d43⟩ := step_add16 (code := code) (input := input) (by rw [pc42, pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc42, pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeSz]; omega)
  have r43_15v : (reg s43 r15).val = descBase + 1 := by
    have hr42_15 : (reg s42 r15).val = descBase := by
      rw [p42 r15 (by decide), p41 r15 (by decide), p40 r15 (by decide), p39 r15 (by decide),
        p38 r15 (by decide), p37 r15 (by decide), p36 r15 (by decide), p35 r15 (by decide)]; exact h15_24
    have hr42_1 : (reg s42 rOne).val = 1 := by
      rw [p42 rOne (by decide), p41 rOne (by decide), p40 rOne (by decide), p39 rOne (by decide),
        p38 rOne (by decide), p37 rOne (by decide), p36 rOne (by decide), p35 rOne (by decide)]; exact hOne24
    rw [r43_15, add_no_wrap _ _ (by rw [hr42_15, hr42_1, ownerDescStride_eq] at *; omega), hr42_15, hr42_1]
  have hBnd43 : (reg s43 r15).val < s43.data.size := by
    rw [r43_15v, d43, d42, d41, hd40, hsz24]; rw [ownerDescStride_eq] at hDescFit; omega
  obtain ⟨s44, hs44, pc44, hregs44, d44⟩ := step_storeData16 (code := code) (input := input) (by rw [pc43, pc42, pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeEq, so_fetch0a h32 (by decide)]; rfl) (by rw [pc43, pc42, pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34, hCodeSz]; omega) hBnd43
  have hPres44 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r15 → reg s44 r = reg s24 r := fun r h1 h2 h3 h5 => by
    rw [reg_eq_of_regs_eq hregs44 r, p43 r h5, p42 r h3, p41 r h2, p40 r h3, p39 r h3, p38 r h1, p37 r h1, p36 r h2, p35 r h1]
    rfl
  have hd44 : s44.data = s24.data.set (descBase + 1) (reg s43 r12) (by rw [hsz24]; rw [ownerDescStride_eq] at hDescFit; omega) := by
    have hArr : s43.data = s24.data := by rw [d43, d42, d41, hd40]
    rw [d44]; clear d44; revert hBnd43; rw [r43_15v, hArr]; intro _; rfl
  have hr44_11 : (reg s44 r11).val = fpBase := by rw [reg_eq_of_regs_eq hregs44 r11, p43 r11 (by decide), p42 r11 (by decide)]; exact hr41_11
  have hr44_12 : (reg s44 r12).val = curOff := by rw [reg_eq_of_regs_eq hregs44 r12, p43 r12 (by decide), p42 r12 (by decide), r41_12, hwCV]
  have hr44_13 : (reg s44 r13).val = fp0 := by rw [reg_eq_of_regs_eq hregs44 r13, p43 r13 (by decide), r42_13, hw0V]
  have hSz44 : s44.data.size = workCap := by rw [hd44, Array.size_set, hsz24]
  have hOne44 : (reg s44 rOne).val = 1 := by rw [hPres44 rOne (by decide) (by decide) (by decide) (by decide)]; exact hOne24
  have hFpRd1 : (s44.data[fpBase + 1]?).map Fin.val = some fp1 := by
    rw [hd44, Array.getElem?_set_ne _ (by have := hFPDisj 1 (by decide); omega)]; exact hFP1
  have hFpRd2 : (s44.data[fpBase + 2]?).map Fin.val = some fp2 := by
    rw [hd44, Array.getElem?_set_ne _ (by have := hFPDisj 2 (by decide); omega)]; exact hFP2
  have hFpRd3 : (s44.data[fpBase + 3]?).map Fin.val = some fp3 := by
    rw [hd44, Array.getElem?_set_ne _ (by have := hFPDisj 3 (by decide); omega)]; exact hFP3
  have hFpRd4 : (s44.data[fpBase + 4]?).map Fin.val = some fp4 := by
    rw [hd44, Array.getElem?_set_ne _ (by have := hFPDisj 4 (by decide); omega)]; exact hFP4
  have hFpRd5 : (s44.data[fpBase + 5]?).map Fin.val = some fp5 := by
    rw [hd44, Array.getElem?_set_ne _ (by have := hFPDisj 5 (by decide); omega)]; exact hFP5
  have hFpLe1 : fp0 ≤ fp1 := by rw [hD1]; omega
  have hFpLe2 : fp0 ≤ fp2 := by rw [hD2, hD1]; omega
  have hFpLe3 : fp0 ≤ fp3 := by rw [hD3, hD2, hD1]; omega
  have hFpLe4 : fp0 ≤ fp4 := by rw [hD4, hD3, hD2, hD1]; omega
  have hFpLe5 : fp0 ≤ fp5 := by rw [hD5, hD4, hD3, hD2, hD1]; omega
  have hSum5 : curOff + (fp5 - fp0) < 2 ^ bits := by
    have : fp5 - fp0 ≤ wc := by rw [hWcEq]; omega
    omega
  have hSum1 : curOff + (fp1 - fp0) < 2 ^ bits := by
    have : fp1 ≤ fp5 := by rw [hD5, hD4, hD3, hD2]; omega
    omega
  have hSum2 : curOff + (fp2 - fp0) < 2 ^ bits := by
    have : fp2 ≤ fp5 := by rw [hD5, hD4, hD3]; omega
    omega
  have hSum3 : curOff + (fp3 - fp0) < 2 ^ bits := by
    have : fp3 ≤ fp5 := by rw [hD5, hD4]; omega
    omega
  have hSum4 : curOff + (fp4 - fp0) < 2 ^ bits := by
    have : fp4 ≤ fp5 := by rw [hD5]; omega
    omega
  obtain ⟨s74, hs74_seg, pc74, sz74, r74_11, r74_15, hPres74, w50, w56, w62, w68, w74, hFr74⟩ :=
    sealedOwners_large_write5DescDeltas h32 hBits
      (by rw [pc44, pc43, pc42, pc41, pc40, pc39, pc38, pc37, pc36, pc35, hpc34]) hSz44
      hOne44 hr44_11 hr44_12 hr44_13 (by rw [reg_eq_of_regs_eq hregs44 r15]; exact r43_15v)
      hDescFit (by dsimp only [fpBase]; omega) hFpLe1 hFpLe2 hFpLe3 hFpLe4 hFpLe5
      hSum1 hSum2 hSum3 hSum4 hSum5 hFPDisj hFpRd1 hFpRd2 hFpRd3 hFpRd4 hFpRd5
  obtain ⟨s75, hs75, pc75, r75_14, p75, d75⟩ := step_imm16 (code := code) (input := input) (by rw [pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc74, hCodeSz]; omega)
  obtain ⟨s76, hs76, pc76, r76_15, p76, d76⟩ := step_sub16 (code := code) (input := input) (by rw [pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc75, pc74, hCodeSz]; omega)
  have r76_15v : (reg s76 r15).val = descBase := by
    have hr75_15 : (reg s75 r15).val = descBase + 6 := by rw [p75 r15 (by decide)]; exact r74_15
    have hr75_14 : (reg s75 r14).val = 6 := congrArg Fin.val r75_14
    rw [r76_15, sub_exact _ _ (by rw [hr75_15, hr75_14]; omega), hr75_15, hr75_14]
    omega
  obtain ⟨s77, hs77, pc77, r77_11, p77, d77⟩ := step_sub16 (code := code) (input := input) (by rw [pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc76, pc75, pc74, hCodeSz]; omega)
  have r77_11v : (reg s77 r11).val = fpBase + 4 := by
    have hr76_11 : (reg s76 r11).val = fpBase + 5 := by rw [p76 r11 (by decide), p75 r11 (by decide)]; exact r74_11
    have hr76_1 : (reg s76 rOne).val = 1 := by rw [p76 rOne (by decide), p75 rOne (by decide), hPres74 rOne (by decide) (by decide) (by decide)]; exact hOne44
    rw [r77_11, sub_exact _ _ (by rw [hr76_11, hr76_1]; omega), hr76_11, hr76_1]; omega
  have hLFp4 : ∃ w4, s77.data[(reg s77 r11).val]? = some w4 ∧ w4.val = fp4 := by
    rw [r77_11v, d77, d76, d75, hFr74 _ (by have := hFPDisj 4 (by decide); omega), hd44,
      Array.getElem?_set_ne _ (by have := hFPDisj 4 (by decide); omega)]
    cases hG : s24.data[forestPtrsBase + 6 * d + 4]? with
    | none => rw [hG] at hFP4; cases hFP4
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hFP4; exact ⟨w, rfl, hFP4⟩
  obtain ⟨w4f, hw4f, hw4fV⟩ := hLFp4
  obtain ⟨s78, hs78, pc78, r78_14, p78, d78⟩ := step_loadData16 (code := code) (input := input) (by rw [pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) hw4f (by rw [pc77, pc76, pc75, pc74, hCodeSz]; omega)
  obtain ⟨s79, hs79, pc79, r79_11, p79, d79⟩ := step_add16 (code := code) (input := input) (by rw [pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  have r79_11v : (reg s79 r11).val = fpBase + 5 := by
    have hr78_11 : (reg s78 r11).val = fpBase + 4 := by rw [p78 r11 (by decide)]; exact r77_11v
    have hr78_1 : (reg s78 rOne).val = 1 := by rw [p78 rOne (by decide), p77 rOne (by decide), p76 rOne (by decide), p75 rOne (by decide), hPres74 rOne (by decide) (by decide) (by decide)]; exact hOne44
    rw [r79_11, add_no_wrap _ _ (by rw [hr78_11, hr78_1]; omega), hr78_11, hr78_1]
  have hLFp5 : ∃ w5, s79.data[(reg s79 r11).val]? = some w5 ∧ w5.val = fp5 := by
    rw [r79_11v, d79, d78, d77, d76, d75, hFr74 _ (by have := hFPDisj 5 (by decide); omega), hd44,
      Array.getElem?_set_ne _ (by have := hFPDisj 5 (by decide); omega)]
    cases hG : s24.data[forestPtrsBase + 6 * d + 5]? with
    | none => rw [hG] at hFP5; cases hFP5
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hFP5; exact ⟨w, rfl, hFP5⟩
  obtain ⟨w5f, hw5f, hw5fV⟩ := hLFp5
  obtain ⟨s80, hs80, pc80, r80_11, p80, d80⟩ := step_loadData16 (code := code) (input := input) (by rw [pc79, pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) hw5f (by rw [pc79, pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  obtain ⟨s81, hs81, pc81, r81_14, p81, d81⟩ := step_sub16 (code := code) (input := input) (by rw [pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  have r81_14v : (reg s81 r14).val = N_d := by
    have hr80_14 : (reg s80 r14).val = fp4 := by rw [p80 r14 (by decide), p79 r14 (by decide), r78_14, hw4fV]
    rw [r81_14, sub_exact _ _ (by rw [r80_11, hw5fV, hr80_14]; omega), r80_11, hw5fV, hr80_14]; omega
  obtain ⟨s82, hs82, pc82, r82_14, p82, d82⟩ := step_add16 (code := code) (input := input) (by rw [pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  have r82_14v : (reg s82 r14).val = fp0 + wc := by
    have hr81_11 : (reg s81 r11).val = fp5 := by rw [p81 r11 (by decide), r80_11, hw5fV]
    rw [r82_14, add_no_wrap _ _ (by rw [hr81_11, r81_14v]; omega), hr81_11, r81_14v, hWcEq]; omega
  obtain ⟨s83, hs83, pc83, r83_11, p83, d83⟩ := step_mov16 (code := code) (input := input) (by rw [pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  have r83_11v : (reg s83 r11).val = fp0 := by
    rw [r83_11, p82 r13 (by decide), p81 r13 (by decide), p80 r13 (by decide), p79 r13 (by decide), p78 r13 (by decide),
      p77 r13 (by decide), p76 r13 (by decide), p75 r13 (by decide), hPres74 r13 (by decide) (by decide) (by decide)]; exact hr44_13
  obtain ⟨s84, hs84, pc84, r84_12, p84, d84⟩ := step_add16 (code := code) (input := input) (by rw [pc83, pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc83, pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  have r84_12v : (reg s84 r12).val = sealedBase + curOff := by
    have h9_83 : (reg s83 r9).val = sealedBase := by
      rw [p83 r9 (by decide), p82 r9 (by decide), p81 r9 (by decide), p80 r9 (by decide), p79 r9 (by decide), p78 r9 (by decide),
        p77 r9 (by decide), p76 r9 (by decide), p75 r9 (by decide), hPres74 r9 (by decide) (by decide) (by decide), hPres44 r9 (by decide) (by decide) (by decide) (by decide)]
      exact h9_24
    have h12_83 : (reg s83 r12).val = curOff := by
      rw [p83 r12 (by decide), p82 r12 (by decide), p81 r12 (by decide), p80 r12 (by decide), p79 r12 (by decide), p78 r12 (by decide),
        p77 r12 (by decide), p76 r12 (by decide), p75 r12 (by decide), hPres74 r12 (by decide) (by decide) (by decide)]; exact hr44_12
    rw [r84_12, add_no_wrap _ _ (by rw [h9_83, h12_83]; omega), h9_83, h12_83]
  obtain ⟨s85, hs85, pc85, r85_13, p85, d85⟩ := step_mov16 (code := code) (input := input) (by rw [pc84, pc83, pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeEq, so_fetch0b h32 (by decide) (by decide)]; rfl) (by rw [pc84, pc83, pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74, hCodeSz]; omega)
  have r85_13v : (reg s85 r13).val = fp0 + wc := by rw [r85_13, p84 r14 (by decide), p83 r14 (by decide)]; exact r82_14v
  have hPres85 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s85 r = reg s24 r := fun r h1 h2 h3 h4 h5 => by
    rw [p85 r h3, p84 r h2, p83 r h1, p82 r h4, p81 r h4, p80 r h1, p79 r h1, p78 r h4, p77 r h1, p76 r h5, p75 r h4,
      hPres74 r h1 h4 h5, hPres44 r h1 h2 h3 h5]
  have hr85_15 : (reg s85 r15).val = descBase := by
    rw [p85 r15 (by decide), p84 r15 (by decide), p83 r15 (by decide), p82 r15 (by decide), p81 r15 (by decide),
      p80 r15 (by decide), p79 r15 (by decide), p78 r15 (by decide), p77 r15 (by decide)]; exact r76_15v
  have hd85 : s85.data = s74.data := by rw [d85, d84, d83, d82, d81, d80, d79, d78, d77, d76, d75]
  have hSz85 : s85.data.size = workCap := by rw [hd85]; exact sz74
  have hPlF : SlicePlaced code 85 (copyLoopCode 85 91) := so_cpF h32
  obtain ⟨s91, kF, hkF, hLoopF, pc91, sz91, _, r91_12, _, p91, cpF, frF⟩ :=
    run_copyLoop (code := code) (input := input) hPlF (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits
      hFPFit hDstFit hSafeF (by rw [pc85, pc84, pc83, pc82, pc81, pc80, pc79, pc78, pc77, pc76, pc75, pc74])
      hSz85 (by rw [hPres85 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne24)
      (by rw [p85 r11 (by decide), p84 r11 (by decide)]; exact r83_11v) (by rw [p85 r12 (by decide)]; exact r84_12v) r85_13v
  have hS44 : Steps code input 11 s24 s44 :=
    Steps.cons hs25 (Steps.cons hs35 (Steps.cons hs36 (Steps.cons hs37 (Steps.cons hs38 (Steps.cons hs39
      (Steps.cons hs40 (Steps.cons hs41 (Steps.cons hs42 (Steps.cons hs43 (step1 hs44))))))))))
  have hS85 : Steps code input 41 s44 s85 :=
    hs74_seg.append
      (Steps.cons hs75 (Steps.cons hs76 (Steps.cons hs77 (Steps.cons hs78 (Steps.cons hs79
        (Steps.cons hs80 (Steps.cons hs81 (Steps.cons hs82 (Steps.cons hs83 (Steps.cons hs84 (step1 hs85)))))))))))
  have hSteps52 : Steps code input (52 + (6 * wc + 1)) s24 s91 := by
    have hEq := hS44.append (hS85.append (hkF ▸ hLoopF))
    simpa only [← Nat.add_assoc] using hEq
  refine ⟨s91, hSteps52, pc91, sz91, by simpa only [Nat.add_assoc] using r91_12,
    by rw [p91 r15 (by decide) (by decide) (by decide)]; exact hr85_15,
    fun r h1 h2 h3 h4 h5 => by rw [p91 r h1 h2 h4]; exact hPres85 r h1 h2 h3 h4 h5,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frF _ (Or.inl (by rw [descDict_eq]; omega)), hd85, hFr74 _ (by rw [descDict_eq]; omega),
      hd44, descDict_eq, Array.getElem?_set_self, Option.map_some, p43 r12 (by decide), p42 r12 (by decide), r41_12, hwCV]
  · rw [frF _ (Or.inl (by rw [descBackFst_eq]; omega)), hd85]; exact w50
  · rw [frF _ (Or.inl (by rw [descBackSnd_eq]; omega)), hd85]; exact w56
  · rw [frF _ (Or.inl (by rw [descLabels_eq]; omega)), hd85]; exact w62
  · rw [frF _ (Or.inl (by rw [descFEntry_eq]; omega)), hd85]; exact w68
  · rw [frF _ (Or.inl (by rw [descFStop_eq]; omega)), hd85]; exact w74
  · intro addr hOutD hOutA
    rw [frF addr hOutA, hd85, hFr74 addr (by omega), hd44, Array.getElem?_set_ne _ (by omega)]
  · intro k hk
    rw [cpF k hk, hd85, hFr74 _ (by have := hFPArenaDisj k hk; omega), hd44,
      Array.getElem?_set_ne _ (by have := hFPArenaDisj k hk; omega)]

theorem sealedOwners_large_exit0 (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s91 : State L16}
    {d descBase forestPtrsBase exitPtrsBase sealedBase cur1 fp4 fp5 ep0 N_d : Nat}
    (hpc91 : s91.pc = 91) (hsz91 : s91.data.size = workCap)
    (hOne91 : (reg s91 rOne).val = 1) (h7_91 : (reg s91 r7).val = forestPtrsBase)
    (h8_91 : (reg s91 r8).val = exitPtrsBase) (h9_91 : (reg s91 r9).val = sealedBase)
    (h10_91 : (reg s91 r10).val = d) (h12_91 : (reg s91 r12).val = sealedBase + cur1)
    (h15_91 : (reg s91 r15).val = descBase)
    (hDescFit : descBase + ownerDescStride ≤ workCap)
    (hFPBnd : forestPtrsBase + 6 * d + 6 ≤ workCap)
    (hEPBnd : exitPtrsBase + 3 * d + 3 ≤ workCap)
    (hFpLe : fp4 ≤ fp5) (hNdEq : N_d = fp5 - fp4)
    (hEPFit : ep0 + N_d ≤ workCap) (hDstFit : sealedBase + cur1 + N_d ≤ workCap)
    (hDescLtCur : descBase + descExitDepth < sealedBase + cur1)
    (hFP4 : (s91.data[forestPtrsBase + 6 * d + 4]?).map Fin.val = some fp4)
    (hFP5 : (s91.data[forestPtrsBase + 6 * d + 5]?).map Fin.val = some fp5)
    (hEP0 : (s91.data[exitPtrsBase + 3 * d]?).map Fin.val = some ep0)
    (hFPNeDesc : ∀ k, 4 ≤ k → k ≤ 5 → forestPtrsBase + 6 * d + k ≠ descBase + descExitDepth)
    (hEPNeDesc : exitPtrsBase + 3 * d ≠ descBase + descExitDepth)
    (hEA0NeDesc : ∀ k < N_d, ep0 + k ≠ descBase + descExitDepth)
    (hSafeE0 : sealedBase + cur1 + N_d ≤ ep0 ∨ ep0 + N_d ≤ sealedBase + cur1 ∨ sealedBase + cur1 < ep0) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s117 : State L16,
      Steps code input (20 + (6 * N_d + 1)) s91 s117 ∧ s117.pc = 117 ∧ s117.data.size = workCap ∧
      (reg s117 r12).val = sealedBase + (cur1 + N_d) ∧ (reg s117 r15).val = descBase ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s117 r = reg s91 r) ∧
      (s117.data[descBase + descExitDepth]?).map Fin.val = some cur1 ∧
      (∀ addr, addr ≠ descBase + descExitDepth →
        (addr < sealedBase + cur1 ∨ sealedBase + cur1 + N_d ≤ addr) →
        s117.data[addr]? = s91.data[addr]?) ∧
      (∀ k < N_d, s117.data[sealedBase + cur1 + k]? = s91.data[ep0 + k]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  obtain ⟨s92, hs92, pc92, r92_12, p92, d92⟩ := step_sub16 (code := code) (input := input) (by rw [hpc91, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [hpc91, hCodeSz]; omega)
  have r92_12v : (reg s92 r12).val = cur1 := by
    rw [r92_12, sub_exact _ _ (by rw [h12_91, h9_91]; omega), h12_91, h9_91]; omega
  obtain ⟨s93, hs93, pc93, r93_14, p93, d93⟩ := step_imm16 (code := code) (input := input) (by rw [pc92, hpc91, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc92, hpc91, hCodeSz]; omega)
  obtain ⟨s94, hs94, pc94, r94_11, p94, d94⟩ := step_add16 (code := code) (input := input) (by rw [pc93, pc92, hpc91, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc93, pc92, hpc91, hCodeSz]; omega)
  have r94_11v : (reg s94 r11).val = descBase + descExitDepth := by
    have hr93_15 : (reg s93 r15).val = descBase := by rw [p93 r15 (by decide), p92 r15 (by decide)]; exact h15_91
    rw [r94_11, add_no_wrap _ _ (by rw [hr93_15, r93_14]; dsimp only; rw [descExitDepth_eq]; rw [ownerDescStride_eq] at hDescFit; omega), hr93_15, r93_14]
  have hBnd94 : (reg s94 r11).val < s94.data.size := by
    rw [r94_11v, d94, d93, d92, hsz91]; rw [descExitDepth_eq]; rw [ownerDescStride_eq] at hDescFit; omega
  obtain ⟨s95, hs95, pc95, hregs95, d95⟩ := step_storeData16 (code := code) (input := input) (by rw [pc94, pc93, pc92, hpc91, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc94, pc93, pc92, hpc91, hCodeSz]; omega) hBnd94
  have hPres95 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s95 r = reg s91 r := fun r h1 h2 _ h4 _ => by
    rw [reg_eq_of_regs_eq hregs95 r, p94 r h1, p93 r h4, p92 r h2]
  have hr95_12 : (reg s95 r12).val = cur1 := by rw [reg_eq_of_regs_eq hregs95 r12, p94 r12 (by decide), p93 r12 (by decide)]; exact r92_12v
  have hr95_15 : (reg s95 r15).val = descBase := by rw [reg_eq_of_regs_eq hregs95 r15, p94 r15 (by decide), p93 r15 (by decide), p92 r15 (by decide)]; exact h15_91
  have hSz95 : s95.data.size = workCap := by rw [d95, Array.size_set, d94, d93, d92, hsz91]
  have hFpRd95 : ∀ k, 4 ≤ k → k ≤ 5 → (s95.data[forestPtrsBase + 6 * d + k]?).map Fin.val = (s91.data[forestPtrsBase + 6 * d + k]?).map Fin.val := fun k hk1 hk2 => by
    rw [d95, Array.getElem?_set_ne _ (by rw [r94_11v]; exact (hFPNeDesc k hk1 hk2).symm), d94, d93, d92]
  obtain ⟨s105, hs105, pc105, d105, r105_14, p105⟩ :=
    run_fpNStep h32 (code := code) (input := input) (pc := 95) (by rw [hCodeSz]; omega) hBits
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc95, pc94, pc93, pc92, hpc91]) hSz95
      (by rw [hPres95 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne91)
      (by rw [hPres95 r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7_91)
      (by rw [hPres95 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_91)
      hFPBnd (by rw [hFpRd95 4 (by decide) (by decide)]; exact hFP4) (by rw [hFpRd95 5 (by decide) (by decide)]; exact hFP5) hFpLe
  obtain ⟨s106, hs106, pc106, r106_11, p106, d106⟩ := step_add16 (code := code) (input := input) (by rw [pc105, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc105, hCodeSz]; omega)
  have r106_11v : (reg s106 r11).val = 2 * d := by
    have hr105_10 : (reg s105 r10).val = d := by rw [p105 r10 (by decide) (by decide) (by decide), hPres95 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_91
    rw [r106_11, add_no_wrap _ _ (by rw [hr105_10]; omega), hr105_10]; omega
  obtain ⟨s107, hs107, pc107, r107_11, p107, d107⟩ := step_add16 (code := code) (input := input) (by rw [pc106, pc105, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc106, pc105, hCodeSz]; omega)
  have r107_11v : (reg s107 r11).val = 3 * d := by
    have hr106_10 : (reg s106 r10).val = d := by rw [p106 r10 (by decide), p105 r10 (by decide) (by decide) (by decide), hPres95 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_91
    rw [r107_11, add_no_wrap _ _ (by rw [r106_11v, hr106_10]; omega), r106_11v, hr106_10]; omega
  obtain ⟨s108, hs108, pc108, r108_11, p108, d108⟩ := step_add16 (code := code) (input := input) (by rw [pc107, pc106, pc105, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc107, pc106, pc105, hCodeSz]; omega)
  have r108_11v : (reg s108 r11).val = exitPtrsBase + 3 * d := by
    have h8_107 : (reg s107 r8).val = exitPtrsBase := by
      rw [p107 r8 (by decide), p106 r8 (by decide), p105 r8 (by decide) (by decide) (by decide), hPres95 r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8_91
    rw [r108_11, add_no_wrap _ _ (by rw [h8_107, r107_11v]; omega), h8_107, r107_11v]
  have hd108 : s108.data = s95.data := by rw [d108, d107, d106, d105]
  have hLEp0 : ∃ we0, s108.data[(reg s108 r11).val]? = some we0 ∧ we0.val = ep0 := by
    rw [hd108, r108_11v, d95, Array.getElem?_set_ne _ (by rw [r94_11v]; exact hEPNeDesc.symm), d94, d93, d92]
    cases hG : s91.data[exitPtrsBase + 3 * d]? with
    | none => rw [hG] at hEP0; cases hEP0
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hEP0; exact ⟨w, rfl, hEP0⟩
  obtain ⟨we0, hwe0, hwe0V⟩ := hLEp0
  obtain ⟨s109, hs109, pc109, r109_11, p109, d109⟩ := step_loadData16 (code := code) (input := input) (by rw [pc108, pc107, pc106, pc105, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) hwe0 (by rw [pc108, pc107, pc106, pc105, hCodeSz]; omega)
  obtain ⟨s110, hs110, pc110, r110_13, p110, d110⟩ := step_add16 (code := code) (input := input) (by rw [pc109, pc108, pc107, pc106, pc105, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc109, pc108, pc107, pc106, pc105, hCodeSz]; omega)
  have r110_13v : (reg s110 r13).val = ep0 + N_d := by
    have hr109_14 : (reg s109 r14).val = N_d := by rw [p109 r14 (by decide), p108 r14 (by decide), p107 r14 (by decide), p106 r14 (by decide), r105_14, hNdEq]
    rw [r110_13, add_no_wrap _ _ (by rw [r109_11, hwe0V, hr109_14]; omega), r109_11, hwe0V, hr109_14]
  obtain ⟨s111, hs111, pc111, r111_12, p111, d111⟩ := step_add16 (code := code) (input := input) (by rw [pc110, pc109, pc108, pc107, pc106, pc105, hCodeEq, so_fetch1 h32 (by decide) (by decide)]; rfl) (by rw [pc110, pc109, pc108, pc107, pc106, pc105, hCodeSz]; omega)
  have hPres111 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s111 r = reg s91 r := fun r h1 h2 h3 h4 h5 => by
    rw [p111 r h2, p110 r h3, p109 r h1, p108 r h1, p107 r h1, p106 r h1, p105 r h1 h3 h4, hPres95 r h1 h2 h3 h4 h5]
  have r111_12v : (reg s111 r12).val = sealedBase + cur1 := by
    have h9_110 : (reg s110 r9).val = sealedBase := by
      rw [p110 r9 (by decide), p109 r9 (by decide), p108 r9 (by decide), p107 r9 (by decide), p106 r9 (by decide), p105 r9 (by decide) (by decide) (by decide), hPres95 r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9_91
    have h12_110 : (reg s110 r12).val = cur1 := by
      rw [p110 r12 (by decide), p109 r12 (by decide), p108 r12 (by decide), p107 r12 (by decide), p106 r12 (by decide), p105 r12 (by decide) (by decide) (by decide)]; exact hr95_12
    rw [r111_12, add_no_wrap _ _ (by rw [h9_110, h12_110]; omega), h9_110, h12_110]
  have hr111_15 : (reg s111 r15).val = descBase := by
    rw [p111 r15 (by decide), p110 r15 (by decide), p109 r15 (by decide), p108 r15 (by decide), p107 r15 (by decide), p106 r15 (by decide), p105 r15 (by decide) (by decide) (by decide)]; exact hr95_15
  have hd111 : s111.data = s95.data := by rw [d111, d110, d109, hd108]
  have hPlE0 : SlicePlaced code 111 (copyLoopCode 111 117) := so_cpE0 h32
  obtain ⟨s117, kE0, hkE0, hLoopE0, pc117, sz117, _, r117_12, _, p117, cpE0, frE0⟩ :=
    run_copyLoop (code := code) (input := input) hPlE0 (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits
      hEPFit hDstFit hSafeE0 (by rw [pc111, pc110, pc109, pc108, pc107, pc106, pc105])
      (by rw [hd111]; exact hSz95) (by rw [hPres111 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne91)
      (by rw [p111 r11 (by decide), p110 r11 (by decide), r109_11, hwe0V]) r111_12v
      (by rw [p111 r13 (by decide)]; exact r110_13v)
  have hS111 : Steps code input 20 s91 s111 :=
    Steps.cons hs92 (Steps.cons hs93 (Steps.cons hs94 (Steps.cons hs95 (hs105.append
      (Steps.cons hs106 (Steps.cons hs107 (Steps.cons hs108 (Steps.cons hs109 (Steps.cons hs110 (step1 hs111))))))))))
  refine ⟨s117, (hkE0 ▸ hS111.append hLoopE0), pc117, sz117,
    by rw [r117_12, Nat.add_assoc],
    by rw [p117 r15 (by decide) (by decide) (by decide)]; exact hr111_15,
    fun r h1 h2 h3 h4 h5 => by rw [p117 r h1 h2 h4]; exact hPres111 r h1 h2 h3 h4 h5,
    ?_, ?_, ?_⟩
  · rw [frE0 _ (Or.inl hDescLtCur), hd111, d95, ← r94_11v, Array.getElem?_set_self, Option.map_some, p94 r12 (by decide), p93 r12 (by decide), r92_12v]
  · intro addr hNeD hOutA
    rw [frE0 addr hOutA, hd111, d95, Array.getElem?_set_ne _ (by rw [r94_11v]; exact hNeD.symm), d94, d93, d92]
  · intro k hk
    rw [cpE0 k hk, hd111, d95, Array.getElem?_set_ne _ (by rw [r94_11v]; exact (hEA0NeDesc k hk).symm), d94, d93, d92]

theorem sealedOwners_large_exit1 (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s117 : State L16}
    {d descBase forestPtrsBase exitPtrsBase sealedBase cur2 fp4 fp5 ep1 N_d : Nat}
    (hpc117 : s117.pc = 117) (hsz117 : s117.data.size = workCap)
    (hOne117 : (reg s117 rOne).val = 1) (h7_117 : (reg s117 r7).val = forestPtrsBase)
    (h8_117 : (reg s117 r8).val = exitPtrsBase) (h9_117 : (reg s117 r9).val = sealedBase)
    (h10_117 : (reg s117 r10).val = d) (h12_117 : (reg s117 r12).val = sealedBase + cur2)
    (h15_117 : (reg s117 r15).val = descBase)
    (hDescFit : descBase + ownerDescStride ≤ workCap)
    (hFPBnd : forestPtrsBase + 6 * d + 6 ≤ workCap)
    (hEPBnd : exitPtrsBase + 3 * d + 3 ≤ workCap)
    (hFpLe : fp4 ≤ fp5) (hNdEq : N_d = fp5 - fp4)
    (hEPFit : ep1 + 18 * N_d ≤ workCap) (hDstFit : sealedBase + cur2 + 18 * N_d ≤ workCap)
    (hDescLtCur : descBase + descExitStored < sealedBase + cur2)
    (hFP4 : (s117.data[forestPtrsBase + 6 * d + 4]?).map Fin.val = some fp4)
    (hFP5 : (s117.data[forestPtrsBase + 6 * d + 5]?).map Fin.val = some fp5)
    (hEP1 : (s117.data[exitPtrsBase + 3 * d + 1]?).map Fin.val = some ep1)
    (hFPNeDesc : ∀ k, 4 ≤ k → k ≤ 5 → forestPtrsBase + 6 * d + k ≠ descBase + descExitStored)
    (hEPNeDesc : exitPtrsBase + 3 * d + 1 ≠ descBase + descExitStored)
    (hEA1NeDesc : ∀ k < 18 * N_d, ep1 + k ≠ descBase + descExitStored)
    (hSafeE1 : sealedBase + cur2 + 18 * N_d ≤ ep1 ∨ ep1 + 18 * N_d ≤ sealedBase + cur2 ∨ sealedBase + cur2 < ep1) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ s149 : State L16,
      Steps code input (26 + (6 * (18 * N_d) + 1)) s117 s149 ∧ s149.pc = 149 ∧ s149.data.size = workCap ∧
      (reg s149 r12).val = sealedBase + (cur2 + 18 * N_d) ∧ (reg s149 r15).val = descBase ∧
      (∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s149 r = reg s117 r) ∧
      (s149.data[descBase + descExitStored]?).map Fin.val = some cur2 ∧
      (∀ addr, addr ≠ descBase + descExitStored →
        (addr < sealedBase + cur2 ∨ sealedBase + cur2 + 18 * N_d ≤ addr) →
        s149.data[addr]? = s117.data[addr]?) ∧
      (∀ k < 18 * N_d, s149.data[sealedBase + cur2 + k]? = s117.data[ep1 + k]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  obtain ⟨s118, hs118, pc118, r118_12, p118, d118⟩ := step_sub16 (code := code) (input := input) (by rw [hpc117, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [hpc117, hCodeSz]; omega)
  have r118_12v : (reg s118 r12).val = cur2 := by
    rw [r118_12, sub_exact _ _ (by rw [h12_117, h9_117]; omega), h12_117, h9_117]; omega
  obtain ⟨s119, hs119, pc119, r119_14, p119, d119⟩ := step_imm16 (code := code) (input := input) (by rw [pc118, hpc117, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc118, hpc117, hCodeSz]; omega)
  obtain ⟨s120, hs120, pc120, r120_11, p120, d120⟩ := step_add16 (code := code) (input := input) (by rw [pc119, pc118, hpc117, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc119, pc118, hpc117, hCodeSz]; omega)
  have r120_11v : (reg s120 r11).val = descBase + descExitStored := by
    have hr119_15 : (reg s119 r15).val = descBase := by rw [p119 r15 (by decide), p118 r15 (by decide)]; exact h15_117
    rw [r120_11, add_no_wrap _ _ (by rw [hr119_15, r119_14]; dsimp only; rw [descExitStored_eq]; rw [ownerDescStride_eq] at hDescFit; omega), hr119_15, r119_14]
  have hBnd120 : (reg s120 r11).val < s120.data.size := by
    rw [r120_11v, d120, d119, d118, hsz117]; rw [descExitStored_eq]; rw [ownerDescStride_eq] at hDescFit; omega
  obtain ⟨s121, hs121, pc121, hregs121, d121⟩ := step_storeData16 (code := code) (input := input) (by rw [pc120, pc119, pc118, hpc117, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc120, pc119, pc118, hpc117, hCodeSz]; omega) hBnd120
  have hPres121 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s121 r = reg s117 r := fun r h1 h2 _ h4 _ => by
    rw [reg_eq_of_regs_eq hregs121 r, p120 r h1, p119 r h4, p118 r h2]
  have hr121_12 : (reg s121 r12).val = cur2 := by rw [reg_eq_of_regs_eq hregs121 r12, p120 r12 (by decide), p119 r12 (by decide)]; exact r118_12v
  have hr121_15 : (reg s121 r15).val = descBase := by rw [reg_eq_of_regs_eq hregs121 r15, p120 r15 (by decide), p119 r15 (by decide), p118 r15 (by decide)]; exact h15_117
  have hSz121 : s121.data.size = workCap := by rw [d121, Array.size_set, d120, d119, d118, hsz117]
  have hFpRd121 : ∀ k, 4 ≤ k → k ≤ 5 → (s121.data[forestPtrsBase + 6 * d + k]?).map Fin.val = (s117.data[forestPtrsBase + 6 * d + k]?).map Fin.val := fun k hk1 hk2 => by
    rw [d121, Array.getElem?_set_ne _ (by rw [r120_11v]; exact (hFPNeDesc k hk1 hk2).symm), d120, d119, d118]
  obtain ⟨s131, hs131, pc131, d131, r131_14, p131⟩ :=
    run_fpNStep h32 (code := code) (input := input) (pc := 121) (by rw [hCodeSz]; omega) hBits
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl)
      (by rw [hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc121, pc120, pc119, pc118, hpc117]) hSz121
      (by rw [hPres121 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne117)
      (by rw [hPres121 r7 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7_117)
      (by rw [hPres121 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_117)
      hFPBnd (by rw [hFpRd121 4 (by decide) (by decide)]; exact hFP4) (by rw [hFpRd121 5 (by decide) (by decide)]; exact hFP5) hFpLe
  have r131_14v : (reg s131 r14).val = N_d := by rw [r131_14, hNdEq]
  obtain ⟨s132, hs132, pc132, r132_13, p132, d132⟩ := step_add16 (code := code) (input := input) (by rw [pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc131, hCodeSz]; omega)
  have r132_13v : (reg s132 r13).val = 2 * N_d := by rw [r132_13, add_no_wrap _ _ (by rw [r131_14v]; omega), r131_14v]; omega
  obtain ⟨s133, hs133, pc133, r133_14, p133, d133⟩ := step_add16 (code := code) (input := input) (by rw [pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc132, pc131, hCodeSz]; omega)
  have r133_14v : (reg s133 r14).val = 4 * N_d := by rw [r133_14, add_no_wrap _ _ (by rw [r132_13v]; omega), r132_13v]; omega
  obtain ⟨s134, hs134, pc134, r134_14, p134, d134⟩ := step_add16 (code := code) (input := input) (by rw [pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc133, pc132, pc131, hCodeSz]; omega)
  have r134_14v : (reg s134 r14).val = 8 * N_d := by rw [r134_14, add_no_wrap _ _ (by rw [r133_14v]; omega), r133_14v]; omega
  obtain ⟨s135, hs135, pc135, r135_14, p135, d135⟩ := step_add16 (code := code) (input := input) (by rw [pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have r135_14v : (reg s135 r14).val = 16 * N_d := by rw [r135_14, add_no_wrap _ _ (by rw [r134_14v]; omega), r134_14v]; omega
  obtain ⟨s136, hs136, pc136, r136_14, p136, d136⟩ := step_add16 (code := code) (input := input) (by rw [pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have r136_14v : (reg s136 r14).val = 18 * N_d := by
    have hr135_13 : (reg s135 r13).val = 2 * N_d := by rw [p135 r13 (by decide), p134 r13 (by decide), p133 r13 (by decide)]; exact r132_13v
    rw [r136_14, add_no_wrap _ _ (by rw [r135_14v, hr135_13]; omega), r135_14v, hr135_13]; omega
  obtain ⟨s137, hs137, pc137, r137_11, p137, d137⟩ := step_add16 (code := code) (input := input) (by rw [pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have hr136_10 : (reg s136 r10).val = d := by
    rw [p136 r10 (by decide), p135 r10 (by decide), p134 r10 (by decide), p133 r10 (by decide), p132 r10 (by decide),
      p131 r10 (by decide) (by decide) (by decide), hPres121 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_117
  have r137_11v : (reg s137 r11).val = 2 * d := by rw [r137_11, add_no_wrap _ _ (by rw [hr136_10]; omega), hr136_10]; omega
  obtain ⟨s138, hs138, pc138, r138_11, p138, d138⟩ := step_add16 (code := code) (input := input) (by rw [pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have hr137_10 : (reg s137 r10).val = d := by rw [p137 r10 (by decide)]; exact hr136_10
  have r138_11v : (reg s138 r11).val = 3 * d := by rw [r138_11, add_no_wrap _ _ (by rw [r137_11v, hr137_10]; omega), r137_11v, hr137_10]; omega
  obtain ⟨s139, hs139, pc139, r139_11, p139, d139⟩ := step_add16 (code := code) (input := input) (by rw [pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have r139_11v : (reg s139 r11).val = exitPtrsBase + 3 * d := by
    have hr138_8 : (reg s138 r8).val = exitPtrsBase := by
      rw [p138 r8 (by decide), p137 r8 (by decide), p136 r8 (by decide), p135 r8 (by decide), p134 r8 (by decide),
        p133 r8 (by decide), p132 r8 (by decide), p131 r8 (by decide) (by decide) (by decide), hPres121 r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8_117
    rw [r139_11, add_no_wrap _ _ (by rw [hr138_8, r138_11v]; omega), hr138_8, r138_11v]
  obtain ⟨s140, hs140, pc140, r140_11, p140, d140⟩ := step_add16 (code := code) (input := input) (by rw [pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have hOne139 : (reg s139 rOne).val = 1 := by
    rw [p139 rOne (by decide), p138 rOne (by decide), p137 rOne (by decide), p136 rOne (by decide), p135 rOne (by decide),
      p134 rOne (by decide), p133 rOne (by decide), p132 rOne (by decide), p131 rOne (by decide) (by decide) (by decide),
      hPres121 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne117
  have r140_11v : (reg s140 r11).val = exitPtrsBase + 3 * d + 1 := by
    rw [r140_11, add_no_wrap _ _ (by rw [r139_11v, hOne139]; omega), r139_11v, hOne139]
  have hd140 : s140.data = s121.data := by rw [d140, d139, d138, d137, d136, d135, d134, d133, d132, d131]
  have hLEp1 : ∃ we1, s140.data[(reg s140 r11).val]? = some we1 ∧ we1.val = ep1 := by
    rw [hd140, r140_11v, d121, Array.getElem?_set_ne _ (by rw [r120_11v]; exact hEPNeDesc.symm), d120, d119, d118]
    cases hG : s117.data[exitPtrsBase + 3 * d + 1]? with
    | none => rw [hG] at hEP1; cases hEP1
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hEP1; exact ⟨w, rfl, hEP1⟩
  obtain ⟨we1, hwe1, hwe1V⟩ := hLEp1
  obtain ⟨s141, hs141, pc141, r141_11, p141, d141⟩ := step_loadData16 (code := code) (input := input) (by rw [pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) hwe1 (by rw [pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  obtain ⟨s142, hs142, pc142, r142_13, p142, d142⟩ := step_add16 (code := code) (input := input) (by rw [pc141, pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc141, pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have r142_13v : (reg s142 r13).val = ep1 + 18 * N_d := by
    have hr141_14 : (reg s141 r14).val = 18 * N_d := by
      rw [p141 r14 (by decide), p140 r14 (by decide), p139 r14 (by decide), p138 r14 (by decide), p137 r14 (by decide)]; exact r136_14v
    rw [r142_13, add_no_wrap _ _ (by rw [r141_11, hwe1V, hr141_14]; omega), r141_11, hwe1V, hr141_14]
  obtain ⟨s143, hs143, pc143, r143_12, p143, d143⟩ := step_add16 (code := code) (input := input) (by rw [pc142, pc141, pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeEq, so_fetch2 h32 (by decide) (by decide)]; rfl) (by rw [pc142, pc141, pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131, hCodeSz]; omega)
  have hPres143 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s143 r = reg s117 r := fun r h1 h2 h3 h4 h5 => by
    rw [p143 r h2, p142 r h3, p141 r h1, p140 r h1, p139 r h1, p138 r h1, p137 r h1, p136 r h4, p135 r h4, p134 r h4,
      p133 r h4, p132 r h3, p131 r h1 h3 h4, hPres121 r h1 h2 h3 h4 h5]
  have r143_12v : (reg s143 r12).val = sealedBase + cur2 := by
    have h9_142 : (reg s142 r9).val = sealedBase := by
      rw [p142 r9 (by decide), p141 r9 (by decide), p140 r9 (by decide), p139 r9 (by decide), p138 r9 (by decide), p137 r9 (by decide),
        p136 r9 (by decide), p135 r9 (by decide), p134 r9 (by decide), p133 r9 (by decide), p132 r9 (by decide),
        p131 r9 (by decide) (by decide) (by decide), hPres121 r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9_117
    have h12_142 : (reg s142 r12).val = cur2 := by
      rw [p142 r12 (by decide), p141 r12 (by decide), p140 r12 (by decide), p139 r12 (by decide), p138 r12 (by decide), p137 r12 (by decide),
        p136 r12 (by decide), p135 r12 (by decide), p134 r12 (by decide), p133 r12 (by decide), p132 r12 (by decide),
        p131 r12 (by decide) (by decide) (by decide)]; exact hr121_12
    rw [r143_12, add_no_wrap _ _ (by rw [h9_142, h12_142]; omega), h9_142, h12_142]
  have hr143_15 : (reg s143 r15).val = descBase := by
    rw [p143 r15 (by decide), p142 r15 (by decide), p141 r15 (by decide), p140 r15 (by decide), p139 r15 (by decide), p138 r15 (by decide),
      p137 r15 (by decide), p136 r15 (by decide), p135 r15 (by decide), p134 r15 (by decide), p133 r15 (by decide),
      p132 r15 (by decide), p131 r15 (by decide) (by decide) (by decide)]; exact hr121_15
  have hd143 : s143.data = s121.data := by rw [d143, d142, d141, hd140]
  have hPlE1 : SlicePlaced code 143 (copyLoopCode 143 149) := so_cpE1 h32
  obtain ⟨s149, kE1, hkE1, hLoopE1, pc149, sz149, _, r149_12, _, p149, cpE1, frE1⟩ :=
    run_copyLoop (code := code) (input := input) hPlE1 (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits
      hEPFit hDstFit hSafeE1 (by rw [pc143, pc142, pc141, pc140, pc139, pc138, pc137, pc136, pc135, pc134, pc133, pc132, pc131])
      (by rw [hd143]; exact hSz121) (by rw [hPres143 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne117)
      (by rw [p143 r11 (by decide), p142 r11 (by decide), r141_11, hwe1V]) r143_12v
      (by rw [p143 r13 (by decide)]; exact r142_13v)
  have hS143 : Steps code input 26 s117 s143 :=
    Steps.cons hs118 (Steps.cons hs119 (Steps.cons hs120 (Steps.cons hs121 (hs131.append
      (Steps.cons hs132 (Steps.cons hs133 (Steps.cons hs134 (Steps.cons hs135 (Steps.cons hs136
        (Steps.cons hs137 (Steps.cons hs138 (Steps.cons hs139 (Steps.cons hs140 (Steps.cons hs141
          (Steps.cons hs142 (step1 hs143))))))))))))))))
  refine ⟨s149, (hkE1 ▸ hS143.append hLoopE1), pc149, sz149,
    by rw [r149_12, Nat.add_assoc],
    by rw [p149 r15 (by decide) (by decide) (by decide)]; exact hr143_15,
    fun r h1 h2 h3 h4 h5 => by rw [p149 r h1 h2 h4]; exact hPres143 r h1 h2 h3 h4 h5,
    ?_, ?_, ?_⟩
  · rw [frE1 _ (Or.inl hDescLtCur), hd143, d121, ← r120_11v, Array.getElem?_set_self, Option.map_some, p120 r12 (by decide), p119 r12 (by decide), r118_12v]
  · intro addr hNeD hOutA
    rw [frE1 addr hOutA, hd143, d121, Array.getElem?_set_ne _ (by rw [r120_11v]; exact hNeD.symm), d120, d119, d118]
  · intro k hk
    rw [cpE1 k hk, hd143, d121, Array.getElem?_set_ne _ (by rw [r120_11v]; exact (hEA1NeDesc k hk).symm), d120, d119, d118]

theorem sealedOwners_large_exit2 (h32 : 32 ≤ 2 ^ bits) (hBits : workCap < 2 ^ bits)
    {input : Input L16} {s149 : State L16}
    {d descBase exitPtrsBase sealedBase cur3 ep2 nD : Nat}
    (hpc149 : s149.pc = 149) (hsz149 : s149.data.size = workCap)
    (hOne149 : (reg s149 rOne).val = 1) (h8_149 : (reg s149 r8).val = exitPtrsBase)
    (h9_149 : (reg s149 r9).val = sealedBase) (h10_149 : (reg s149 r10).val = d)
    (h12_149 : (reg s149 r12).val = sealedBase + cur3) (h15_149 : (reg s149 r15).val = descBase)
    (hDescFit : descBase + ownerDescStride ≤ workCap)
    (hEPBnd : exitPtrsBase + 3 * d + 3 ≤ workCap)
    (hEPFit : ep2 + 6 * nD ≤ workCap) (hDstFit : sealedBase + (cur3 + 6 * nD) ≤ workCap)
    (hTotFit : sealedBase + hdrTotalWords < workCap)
    (hDescLtCur : descBase + descExitPrior < sealedBase + cur3)
    (hTotLtDesc : sealedBase + hdrTotalWords < descBase)
    (hTotLtCur : sealedBase + hdrTotalWords < sealedBase + cur3)
    (hDesc0 : (s149.data[descBase + descN]?).map Fin.val = some nD)
    (hEP2 : (s149.data[exitPtrsBase + 3 * d + 2]?).map Fin.val = some ep2)
    (hEPNeDesc : exitPtrsBase + 3 * d + 2 ≠ descBase + descExitPrior)
    (hEA2NeDesc : ∀ k < 6 * nD, ep2 + k ≠ descBase + descExitPrior)
    (hSafeE2 : sealedBase + cur3 + 6 * nD ≤ ep2 ∨ ep2 + 6 * nD ≤ sealedBase + cur3 ∨ sealedBase + cur3 < ep2) :
    let code := (sealedOwnersPhase (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) h32).code
    ∃ sNext : State L16,
      Steps code input (22 + (6 * (6 * nD) + 1)) s149 sNext ∧ sNext.pc = 1 ∧ sNext.data.size = workCap ∧
      (reg sNext r10).val = d + 1 ∧
      (∀ r : Fin 16, r ≠ r10 → r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg sNext r = reg s149 r) ∧
      (sNext.data[descBase + descExitPrior]?).map Fin.val = some cur3 ∧
      (sNext.data[sealedBase + hdrTotalWords]?).map Fin.val = some (cur3 + 6 * nD) ∧
      (∀ addr, addr ≠ sealedBase + hdrTotalWords → addr ≠ descBase + descExitPrior →
        (addr < sealedBase + cur3 ∨ sealedBase + (cur3 + 6 * nD) ≤ addr) →
        sNext.data[addr]? = s149.data[addr]?) ∧
      (∀ k < 6 * nD, sNext.data[sealedBase + cur3 + k]? = s149.data[ep2 + k]?) := by
  intro code
  have hCodeEq : code = sealedOwnersCode h32 := rfl
  have hCodeSz : code.size = 178 := sealedOwnersCode_size h32
  let cur4 := cur3 + 6 * nD
  obtain ⟨s150, hs150, pc150, r150_12, p150, d150⟩ := step_sub16 (code := code) (input := input) (by rw [hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [hpc149, hCodeSz]; omega)
  have r150_12v : (reg s150 r12).val = cur3 := by
    rw [r150_12, sub_exact _ _ (by rw [h12_149, h9_149]; omega), h12_149, h9_149]; omega
  obtain ⟨s151, hs151, pc151, r151_14, p151, d151⟩ := step_imm16 (code := code) (input := input) (by rw [pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc150, hpc149, hCodeSz]; omega)
  obtain ⟨s152, hs152, pc152, r152_11, p152, d152⟩ := step_add16 (code := code) (input := input) (by rw [pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc151, pc150, hpc149, hCodeSz]; omega)
  have r152_11v : (reg s152 r11).val = descBase + descExitPrior := by
    have hr151_15 : (reg s151 r15).val = descBase := by rw [p151 r15 (by decide), p150 r15 (by decide)]; exact h15_149
    rw [r152_11, add_no_wrap _ _ (by rw [hr151_15, r151_14]; dsimp only; rw [descExitPrior_eq]; rw [ownerDescStride_eq] at hDescFit; omega), hr151_15, r151_14]
  have hBnd152 : (reg s152 r11).val < s152.data.size := by
    rw [r152_11v, d152, d151, d150, hsz149]; rw [descExitPrior_eq]; rw [ownerDescStride_eq] at hDescFit; omega
  obtain ⟨s153, hs153, pc153, hregs153, d153⟩ := step_storeData16 (code := code) (input := input) (by rw [pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc152, pc151, pc150, hpc149, hCodeSz]; omega) hBnd152
  have hr153_15 : (reg s153 r15).val = descBase := by
    rw [reg_eq_of_regs_eq hregs153 r15, p152 r15 (by decide), p151 r15 (by decide), p150 r15 (by decide)]; exact h15_149
  have hDesc0_153 : (s153.data[(reg s153 r15).val]?).map Fin.val = some nD := by
    rw [hr153_15, d153, Array.getElem?_set_ne _ (by rw [r152_11v]; rw [descExitPrior_eq]; omega), d152, d151, d150]
    rw [descN_eq, Nat.add_zero] at hDesc0; exact hDesc0
  have hLND : ∃ wND, s153.data[(reg s153 r15).val]? = some wND ∧ wND.val = nD := by
    cases hG : s153.data[(reg s153 r15).val]? with
    | none => rw [hG] at hDesc0_153; cases hDesc0_153
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hDesc0_153; exact ⟨w, rfl, hDesc0_153⟩
  obtain ⟨wND, hwND, hwNDV⟩ := hLND
  obtain ⟨s154, hs154, pc154, r154_14, p154, d154⟩ := step_loadData16 (code := code) (input := input) (by rw [pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) hwND (by rw [pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have r154_14v : (reg s154 r14).val = nD := by rw [r154_14, hwNDV]
  obtain ⟨s155, hs155, pc155, r155_13, p155, d155⟩ := step_add16 (code := code) (input := input) (by rw [pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have r155_13v : (reg s155 r13).val = 2 * nD := by rw [r155_13, add_no_wrap _ _ (by rw [r154_14v]; omega), r154_14v]; omega
  obtain ⟨s156, hs156, pc156, r156_14, p156, d156⟩ := step_add16 (code := code) (input := input) (by rw [pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have r156_14v : (reg s156 r14).val = 4 * nD := by rw [r156_14, add_no_wrap _ _ (by rw [r155_13v]; omega), r155_13v]; omega
  obtain ⟨s157, hs157, pc157, r157_14, p157, d157⟩ := step_add16 (code := code) (input := input) (by rw [pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have r157_14v : (reg s157 r14).val = 6 * nD := by
    have hr156_13 : (reg s156 r13).val = 2 * nD := by rw [p156 r13 (by decide)]; exact r155_13v
    rw [r157_14, add_no_wrap _ _ (by rw [r156_14v, hr156_13]; omega), r156_14v, hr156_13]; omega
  have hPres157 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s157 r = reg s149 r := fun r h1 h2 h3 h4 _ => by
    rw [p157 r h4, p156 r h4, p155 r h3, p154 r h4, reg_eq_of_regs_eq hregs153 r, p152 r h1, p151 r h4, p150 r h2]
  obtain ⟨s158, hs158, pc158, r158_11, p158, d158⟩ := step_add16 (code := code) (input := input) (by rw [pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have hr157_10 : (reg s157 r10).val = d := by rw [hPres157 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_149
  have r158_11v : (reg s158 r11).val = 2 * d := by rw [r158_11, add_no_wrap _ _ (by rw [hr157_10]; omega), hr157_10]; omega
  obtain ⟨s159, hs159, pc159, r159_11, p159, d159⟩ := step_add16 (code := code) (input := input) (by rw [pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have hr158_10 : (reg s158 r10).val = d := by rw [p158 r10 (by decide)]; exact hr157_10
  have r159_11v : (reg s159 r11).val = 3 * d := by rw [r159_11, add_no_wrap _ _ (by rw [r158_11v, hr158_10]; omega), r158_11v, hr158_10]; omega
  obtain ⟨s160, hs160, pc160, r160_11, p160, d160⟩ := step_add16 (code := code) (input := input) (by rw [pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have hr159_8 : (reg s159 r8).val = exitPtrsBase := by
    rw [p159 r8 (by decide), p158 r8 (by decide), hPres157 r8 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8_149
  have r160_11v : (reg s160 r11).val = exitPtrsBase + 3 * d := by rw [r160_11, add_no_wrap _ _ (by rw [hr159_8, r159_11v]; omega), hr159_8, r159_11v]
  obtain ⟨s161, hs161, pc161, r161_13, p161, d161⟩ := step_imm16 (code := code) (input := input) (by rw [pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  obtain ⟨s162, hs162, pc162, r162_11, p162, d162⟩ := step_add16 (code := code) (input := input) (by rw [pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have r162_11v : (reg s162 r11).val = exitPtrsBase + 3 * d + 2 := by
    have hr161_11 : (reg s161 r11).val = exitPtrsBase + 3 * d := by rw [p161 r11 (by decide)]; exact r160_11v
    rw [r162_11, add_no_wrap _ _ (by rw [hr161_11, r161_13]; dsimp only; omega), hr161_11, r161_13]
  have hd162 : s162.data = s153.data := by rw [d162, d161, d160, d159, d158, d157, d156, d155, d154]
  have hLEp2 : ∃ we2, s162.data[(reg s162 r11).val]? = some we2 ∧ we2.val = ep2 := by
    rw [hd162, r162_11v, d153, Array.getElem?_set_ne _ (by rw [r152_11v]; exact hEPNeDesc.symm), d152, d151, d150]
    cases hG : s149.data[exitPtrsBase + 3 * d + 2]? with
    | none => rw [hG] at hEP2; cases hEP2
    | some w => rw [hG, Option.map_some, Option.some.injEq] at hEP2; exact ⟨w, rfl, hEP2⟩
  obtain ⟨we2, hwe2, hwe2V⟩ := hLEp2
  obtain ⟨s163, hs163, pc163, r163_11, p163, d163⟩ := step_loadData16 (code := code) (input := input) (by rw [pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) hwe2 (by rw [pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  obtain ⟨s164, hs164, pc164, r164_13, p164, d164⟩ := step_add16 (code := code) (input := input) (by rw [pc163, pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc163, pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have hr163_14 : (reg s163 r14).val = 6 * nD := by
    rw [p163 r14 (by decide), p162 r14 (by decide), p161 r14 (by decide), p160 r14 (by decide), p159 r14 (by decide), p158 r14 (by decide)]; exact r157_14v
  have r164_13v : (reg s164 r13).val = ep2 + 6 * nD := by
    rw [r164_13, add_no_wrap _ _ (by rw [r163_11, hwe2V, hr163_14]; omega), r163_11, hwe2V, hr163_14]
  obtain ⟨s165, hs165, pc165, r165_12, p165, d165⟩ := step_add16 (code := code) (input := input) (by rw [pc164, pc163, pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeEq, so_fetch3 h32 (by decide) (by decide)]; rfl) (by rw [pc164, pc163, pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149, hCodeSz]; omega)
  have hPres165 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s165 r = reg s149 r := fun r h1 h2 h3 h4 h5 => by
    rw [p165 r h2, p164 r h3, p163 r h1, p162 r h1, p161 r h3, p160 r h1, p159 r h1, p158 r h1, hPres157 r h1 h2 h3 h4 h5]
  have r165_12v : (reg s165 r12).val = sealedBase + cur3 := by
    have h9_164 : (reg s164 r9).val = sealedBase := by
      rw [p164 r9 (by decide), p163 r9 (by decide), p162 r9 (by decide), p161 r9 (by decide), p160 r9 (by decide), p159 r9 (by decide), p158 r9 (by decide), hPres157 r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9_149
    have h12_164 : (reg s164 r12).val = cur3 := by
      rw [p164 r12 (by decide), p163 r12 (by decide), p162 r12 (by decide), p161 r12 (by decide), p160 r12 (by decide), p159 r12 (by decide), p158 r12 (by decide), p157 r12 (by decide), p156 r12 (by decide), p155 r12 (by decide), p154 r12 (by decide), reg_eq_of_regs_eq hregs153 r12, p152 r12 (by decide), p151 r12 (by decide)]; exact r150_12v
    rw [r165_12, add_no_wrap _ _ (by rw [h9_164, h12_164]; omega), h9_164, h12_164]
  have hd165 : s165.data = s153.data := by rw [d165, d164, d163, hd162]
  have hSz165 : s165.data.size = workCap := by rw [hd165, d153, Array.size_set, d152, d151, d150, hsz149]
  have hPlE2 : SlicePlaced code 165 (copyLoopCode 165 171) := so_cpE2 h32
  obtain ⟨s171, kE2, hkE2, hLoopE2, pc171, sz171, _, r171_12, _, p171, cpE2, frE2⟩ :=
    run_copyLoop (code := code) (input := input) hPlE2 (by rw [hCodeSz]; omega) (by rw [hCodeSz]; omega) hBits
      hEPFit (by omega) hSafeE2 (by rw [pc165, pc164, pc163, pc162, pc161, pc160, pc159, pc158, pc157, pc156, pc155, pc154, pc153, pc152, pc151, pc150, hpc149])
      hSz165 (by rw [hPres165 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne149)
      (by rw [p165 r11 (by decide), p164 r11 (by decide), r163_11, hwe2V]) r165_12v
      (by rw [p165 r13 (by decide)]; exact r164_13v)
  have hPres171 : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → r ≠ r14 → r ≠ r15 → reg s171 r = reg s149 r := fun r h1 h2 h3 h4 h5 => by
    rw [p171 r h1 h2 h4]; exact hPres165 r h1 h2 h3 h4 h5
  obtain ⟨s172, hs172, pc172, r172_12, p172, d172⟩ := step_sub16 (code := code) (input := input) (by rw [pc171, hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl) (by rw [pc171, hCodeSz]; omega)
  have r172_12v : (reg s172 r12).val = cur4 := by
    have h9_171 : (reg s171 r9).val = sealedBase := by rw [hPres171 r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9_149
    rw [r172_12, sub_exact _ _ (by rw [r171_12, h9_171]; omega), r171_12, h9_171]; unfold cur4; omega
  obtain ⟨s173, hs173, pc173, r173_11, p173, d173⟩ := step_imm16 (code := code) (input := input) (by rw [pc172, pc171, hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl) (by rw [pc172, pc171, hCodeSz]; omega)
  obtain ⟨s174, hs174, pc174, r174_11, p174, d174⟩ := step_add16 (code := code) (input := input) (by rw [pc173, pc172, pc171, hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl) (by rw [pc173, pc172, pc171, hCodeSz]; omega)
  have r174_11v : (reg s174 r11).val = sealedBase + hdrTotalWords := by
    have h9_173 : (reg s173 r9).val = sealedBase := by rw [p173 r9 (by decide), p172 r9 (by decide), hPres171 r9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9_149
    rw [r174_11, add_no_wrap _ _ (by rw [h9_173, r173_11]; dsimp only; rw [hdrTotalWords_eq] at hTotFit; omega), h9_173, r173_11]
  have hBnd174 : (reg s174 r11).val < s174.data.size := by rw [r174_11v, d174, d173, d172, sz171]; exact hTotFit
  obtain ⟨s175, hs175, pc175, hregs175, d175⟩ := step_storeData16 (code := code) (input := input) (by rw [pc174, pc173, pc172, pc171, hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl) (by rw [pc174, pc173, pc172, pc171, hCodeSz]; omega) hBnd174
  obtain ⟨s176, hs176, pc176, r176_10, p176, d176⟩ := step_add16 (code := code) (input := input) (by rw [pc175, pc174, pc173, pc172, pc171, hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl) (by rw [pc175, pc174, pc173, pc172, pc171, hCodeSz]; omega)
  have hGo176 := step_goto_at (code := code) (input := input) (s := s176) (target := 1) (by rw [pc176, pc175, pc174, pc173, pc172, pc171, hCodeEq, so_fetch4 h32 (by decide) (by decide)]; rfl) (by rw [hCodeSz]; omega)
  let sNext : State L16 := { s176 with pc := 1 }
  have rNext_10v : (reg sNext r10).val = d + 1 := by
    change (reg s176 r10).val = d + 1
    have h10_175 : (reg s175 r10).val = d := by
      rw [reg_eq_of_regs_eq hregs175 r10, p174 r10 (by decide), p173 r10 (by decide), p172 r10 (by decide),
        hPres171 r10 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10_149
    have h1_175 : (reg s175 rOne).val = 1 := by
      rw [reg_eq_of_regs_eq hregs175 rOne, p174 rOne (by decide), p173 rOne (by decide), p172 rOne (by decide),
        hPres171 rOne (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hOne149
    rw [r176_10, add_no_wrap _ _ (by rw [h10_175, h1_175]; omega), h10_175, h1_175]
  have hS165 : Steps code input 16 s149 s165 :=
    Steps.cons hs150 (Steps.cons hs151 (Steps.cons hs152 (Steps.cons hs153 (Steps.cons hs154
      (Steps.cons hs155 (Steps.cons hs156 (Steps.cons hs157 (Steps.cons hs158 (Steps.cons hs159
        (Steps.cons hs160 (Steps.cons hs161 (Steps.cons hs162 (Steps.cons hs163 (Steps.cons hs164 (step1 hs165)))))))))))))))
  have hS176 : Steps code input 6 s171 sNext :=
    Steps.cons hs172 (Steps.cons hs173 (Steps.cons hs174 (Steps.cons hs175 (Steps.cons hs176 (step1 hGo176)))))
  have hSteps : Steps code input (22 + (6 * (6 * nD) + 1)) s149 sNext := by
    have hEq := hS165.append ((hkE2 ▸ hLoopE2).append hS176)
    exact (show 16 + (6 * (6 * nD) + 1 + 6) = 22 + (6 * (6 * nD) + 1) by omega) ▸ hEq
  refine ⟨sNext, hSteps, rfl, by change s176.data.size = workCap; rw [d176, d175, Array.size_set, d174, d173, d172, sz171],
    rNext_10v,
    fun r h0 h1 h2 h3 h4 h5 => by
      change reg s176 r = reg s149 r
      rw [p176 r h0, reg_eq_of_regs_eq hregs175 r, p174 r h1, p173 r h1, p172 r h2]; exact hPres171 r h1 h2 h3 h4 h5,
    ?_, ?_, ?_, ?_⟩
  · change (s176.data[descBase + descExitPrior]?).map Fin.val = some cur3
    rw [d176, d175, Array.getElem?_set_ne _ (by rw [r174_11v]; rw [descExitPrior_eq]; omega), d174, d173, d172,
      frE2 _ (Or.inl hDescLtCur), hd165, d153, ← r152_11v, Array.getElem?_set_self, Option.map_some, p152 r12 (by decide), p151 r12 (by decide), r150_12v]
  · change (s176.data[sealedBase + hdrTotalWords]?).map Fin.val = some cur4
    rw [d176, d175, ← r174_11v, Array.getElem?_set_self, Option.map_some, p174 r12 (by decide), p173 r12 (by decide), r172_12v]
  · intro addr hNeT hNeD hOutA
    change s176.data[addr]? = s149.data[addr]?
    rw [d176, d175, Array.getElem?_set_ne _ (by rw [r174_11v]; exact hNeT.symm), d174, d173, d172,
      frE2 addr (by rcases hOutA with h | h; exact Or.inl h; exact Or.inr (by omega)), hd165, d153, Array.getElem?_set_ne _ (by rw [r152_11v]; exact hNeD.symm), d152, d151, d150]
  · intro k hk
    change s176.data[sealedBase + cur3 + k]? = s149.data[ep2 + k]?
    rw [d176, d175, Array.getElem?_set_ne _ (by rw [r174_11v]; omega), d174, d173, d172,
      cpE2 k hk, hd165, d153, Array.getElem?_set_ne _ (by rw [r152_11v]; exact (hEA2NeDesc k hk).symm), d152, d151, d150]

theorem so_wc_arith (fp0 d n e : Nat) :
    (1 + 3 * d) + (n + 1) + (n + 1) + n + e + e =
      (fp0 + (1 + 3 * d) + (n + 1) + (n + 1) + n + e - fp0) + e := by
  omega

theorem so_cur_arith (cs : Nat) (hcs : 2 ≤ cs) :
    19 * (1 + cs) + (1 + cs + 1 + 18 * (1 + cs + 1) + 6 * (1 + cs)) ≤ 19 + 66 * cs := by
  omega

theorem so_budget_arith (cs : Nat) (hcs : 2 ≤ cs) :
    23 + (52 + (6 * (19 * (1 + cs)) + 1)) + (20 + (6 * (1 + cs + 1) + 1)) +
      (26 + (6 * (18 * (1 + cs + 1)) + 1)) + (22 + (6 * (6 * (1 + cs)) + 1)) ≤ 100 + 480 * cs := by
  omega

theorem so_small_budget_arith (Q d D f0 cs : Nat) (hd : d < Q) (_hcs : f0 + cs ≤ D - 1) :
    66 + (100 * (Q - (d + 1)) + 480 * (D - 1 - (f0 + cs)) + 2) ≤
      100 * (Q - d) + 480 * (D - 1 - f0) + 2 := by
  omega

theorem so_small_cur_arith (base curOff d f0 cs : Nat) (h1 : curOff ≤ base + 19 * d + 66 * f0) :
    curOff ≤ base + 19 * (d + 1) + 66 * (f0 + cs) := by
  omega

theorem so_cur128_arith (n Q d f0 cs : Nat) (hn : 1 ≤ n) (hQn : Q ≤ n) (hd : d < Q)
    (hp : f0 + cs ≤ Q - 1) :
    (16 + n + 21 * Q + 19 * d + 66 * f0) + (19 + 66 * cs) ≤ 128 * n := by
  omega

theorem so_large_budget_arith (kTot Q d D f0 cs : Nat)
    (hk : kTot ≤ 100 + 480 * cs) (hd : d < Q) (hcs : f0 + cs ≤ D - 1) :
    kTot + (100 * (Q - (d + 1)) + 480 * (D - 1 - (f0 + cs)) + 2) ≤
      100 * (Q - d) + 480 * (D - 1 - f0) + 2 := by
  omega

theorem so_large_cur_arith (base curOff delta d f0 cs : Nat)
    (h1 : curOff ≤ base + 19 * d + 66 * f0) (h2 : delta ≤ 19 + 66 * cs) :
    curOff + delta ≤ base + 19 * (d + 1) + 66 * (f0 + cs) := by
  omega

end ExecutionProofs

end PaperB.RamSealedPacker
