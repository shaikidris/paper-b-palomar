module

public import PaperB.RamExitSummaryBuild
public import PaperB.RamExitFamilyProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxRecDepth 2048
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



open PaperB.ExitMap.Retention (Width rankBound_mono)
open PaperB.ExitMap
open PaperB.ExitMap.SealedPriorBase
open PaperB.ExitMap.JumpMapRoute.StoredExit

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L16" => layout16 bits inputCap workCap hi hw

/-- Sealed data and its certificate after the verified submachine halts. -/
theorem run_exitSummaryBuild_certificate
    (h100 : 100 ≤ 2 ^ bits)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    (flat : H.IsFlat)
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {sizeData : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (inc : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data sizeData i) < rank (orderedVertexAt data sizeData j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt data sizeData i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {ord : PaperB.OrderedReaderResult p data sizeData rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    {subInCap subWorkCap : Nat}
    {hsi : subInCap ≤ 2 ^ bits} {hsw : subWorkCap ≤ 2 ^ bits}
    {subIn : Input (RamForestProgram.layout bits subInCap subWorkCap hsi hsw)}
    (s0 : State (RamForestProgram.layout bits subInCap subWorkCap hsi hsw))
    (hIn : ExitBuildInput subIn H ord entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ subWorkCap) :
    let N := ord.out.tables.next
    ∃ (u : State (RamForestProgram.layout bits subInCap subWorkCap hsi hsw)) (subSteps : Nat),
      subSteps ≤ 3000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount ∧
      run (exitSummaryBuildProgram (hi := hsi) (hw := hsw) h100) subIn subSteps (Phase.initial s0) =
        some ⟨u, subSteps⟩ ∧
      ∃ (C : ActualSealedContract H p data sizeData rank large ord entryRank rankArc flat bits nGlobal)
        (hFit : 19 * N ≤ u.data.size) (hBits : 19 * N ≤ 2 ^ bits)
        (hSeal : 19 * N + 6 * C.built.bases.data.size ≤ u.data.size),
        Occupied u.data (ramBankRegion u.data N hFit hBits) C.built.bundle.F C.built.ref C.wFit ∧
        DecodedOccupied u.data (ramBankRegion u.data N hFit hBits) C.built.bundle.F
          C.built.ref C.wFit.tags C.built.live ∧
        SealedPriorBase.Placed C.wFit C.built.bases.data
          (fun v => ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
            rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩) u.data ⟨19 * N, hSeal⟩ := by
  intro N
  obtain ⟨subSteps, u, _, hSubCost, hRun, _, _, huSz, hOcc, hDec, _, hSeal⟩ :=
    run_exitSummaryBuild flat inc covers rankArc h100 hIn hWork s0
  have hNext : N ≤ H.vertexCount + 1 := (B_next_pos flat inc covers rankArc ord).2
  have hLayout : N + 18 * N ≤ 2 ^ bits := by unfold exitWorkCap at hWork; omega
  have hnG : nGlobal < 2 ^ bits := by
    obtain ⟨w, _, hv⟩ := Option.map_eq_some_iff.mp hIn.hdr_nGlobal
    rw [← hv]
    exact w.isLt
  let wFit : Width bits (max N nGlobal) := ⟨Nat.max_le.mpr ⟨by omega, Nat.le_of_lt hnG⟩,
    by unfold TagsFit; omega⟩
  let C := buildActualSealedContract H flat inc covers rankArc ord entryRank hIn.hRank_lt wFit hLayout
  have hFit : 19 * N ≤ u.data.size := by
    change 19 * N + 6 * H.vertexCount ≤ u.data.size at huSz
    omega
  have hBitsFit : 19 * N ≤ 2 ^ bits := by omega
  have hSealFit : 19 * N + 6 * C.built.bases.data.size ≤ u.data.size := by
    rw [C.built.bases.size_data]
    exact huSz
  exact ⟨u, subSteps, hSubCost, hRun, C, hFit, hBitsFit, hSealFit, hOcc, hDec,
    (hSeal hSealFit).2.1⟩

end PaperB.RamExitFamilyLoop
