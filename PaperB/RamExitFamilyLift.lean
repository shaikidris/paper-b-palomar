module

public import PaperB.RamExitSummaryCertificate
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

private theorem liftRunWithPayload {bits : Nat} {subL bigL : Layout bits}
    (hSub : subL.registerCount = 15) (hBig : bigL.registerCount = 16)
    {subCode : Program subL} {subIn : Input subL} {subStart : State subL}
    {code : Program bigL} (input : Input bigL) {bigStart : State bigL}
    {inPtr dataPtr : Word bits} {inBase dataBase base : Nat}
    {bound : Nat} {valid : Array (Word bits) → Prop}
    (hResult : ∃ (u : State subL) (steps : Nat),
      steps ≤ bound ∧ run subCode subIn steps (Phase.initial subStart) = some ⟨u, steps⟩ ∧
      valid u.data)
    (hZero : Phase.initial subStart = subStart)
    (hCfg : SliceConfig subL bigL inPtr dataPtr inBase dataBase subIn bigStart.data)
    (hSim : SliceSim hSub hBig dataBase base bigStart.data subStart bigStart)
    (hBody : BodyRelocated hBig inPtr dataPtr (hSub ▸ subCode) code base)
    (hExitLt : base + 4 * subCode.size < code.size) :
    ∃ (t : State bigL) (mem : Array (Word bits)) (k : Nat),
      k ≤ 4 * bound ∧ Steps code input k bigStart t ∧
      t.pc = base + 4 * subCode.size ∧
      (∀ j < subL.workCap, t.data[dataBase + j]? = mem[j]?) ∧
      (∀ addr, (addr < dataBase ∨ dataBase + subL.workCap ≤ addr) →
        t.data[addr]? = bigStart.data[addr]?) ∧ valid mem := by
  obtain ⟨u, steps, hBound, hRun, hValid⟩ := hResult
  rw [hZero] at hRun
  obtain ⟨k, t, hk, hSteps, hPC, _, hData, hFr⟩ :=
    liftProgram_relocated_steps hSub hBig subCode subIn code input inPtr dataPtr
      inBase dataBase base steps subStart ⟨u, steps⟩ bigStart hRun hCfg hBody hExitLt hSim
  exact ⟨t, u.data, k, Nat.le_trans hk (Nat.mul_le_mul_left 4 hBound),
    hSteps, hPC, hData, hFr, hValid⟩

/-- Run the verified exit builder inside an outer RAM slice and retain the
semantic certificate of its output words along with the relocation frame. -/
theorem run_exitSub_lifted
    (h100 : 100 ≤ 2 ^ bits) {code : Program L16} (input : Input L16)
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
    {subStart : State (RamForestProgram.layout bits subInCap subWorkCap hsi hsw)}
    {bigStart : State L16} {inBase dataBase base : Nat}
    {inPtr dataPtr : Word bits}
    (hIn : ExitBuildInput subIn H ord entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ subWorkCap)
    (hZero : Phase.initial subStart = subStart)
    (hCfg : SliceConfig _ L16 inPtr dataPtr inBase dataBase subIn bigStart.data)
    (hSim : SliceSim rfl rfl dataBase base bigStart.data subStart bigStart)
    (hBody : BodyRelocated rfl inPtr dataPtr
      (exitSummaryBuildProgram (hi := hsi) (hw := hsw) h100) code base)
    (hExitLt : base + 4 * (exitSummaryBuildProgram (hi := hsi) (hw := hsw) h100).size < code.size) :
    let N := ord.out.tables.next
    ∃ (t : State L16) (mem : Array (Word bits)) (k : Nat),
      k ≤ 12000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount ∧
      Steps code input k bigStart t ∧
      t.pc = base + 4 * (exitSummaryBuildProgram (hi := hsi) (hw := hsw) h100).size ∧
      (∀ j < subWorkCap, t.data[dataBase + j]? = mem[j]?) ∧
      (∀ addr, (addr < dataBase ∨ dataBase + subWorkCap ≤ addr) →
        t.data[addr]? = bigStart.data[addr]?) ∧
      ∃ (C : ActualSealedContract H p data sizeData rank large ord entryRank rankArc flat bits nGlobal)
        (hFit : 19 * N ≤ mem.size) (hBits : 19 * N ≤ 2 ^ bits)
        (hSeal : 19 * N + 6 * C.built.bases.data.size ≤ mem.size),
        Occupied mem (ramBankRegion mem N hFit hBits) C.built.bundle.F C.built.ref C.wFit ∧
        DecodedOccupied mem (ramBankRegion mem N hFit hBits) C.built.bundle.F
          C.built.ref C.wFit.tags C.built.live ∧
        SealedPriorBase.Placed C.wFit C.built.bases.data
          (fun v => ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
            rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩) mem ⟨19 * N, hSeal⟩ := by
  intro N
  let valid (mem : Array (Word bits)) : Prop :=
      ∃ (C : ActualSealedContract H p data sizeData rank large ord entryRank rankArc flat bits nGlobal)
        (hFit : 19 * N ≤ mem.size) (hBits : 19 * N ≤ 2 ^ bits)
        (hSeal : 19 * N + 6 * C.built.bases.data.size ≤ mem.size),
        Occupied mem (ramBankRegion mem N hFit hBits) C.built.bundle.F C.built.ref C.wFit ∧
        DecodedOccupied mem (ramBankRegion mem N hFit hBits) C.built.bundle.F
          C.built.ref C.wFit.tags C.built.live ∧
        SealedPriorBase.Placed C.wFit C.built.bases.data
          (fun v => ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
            rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩) mem ⟨19 * N, hSeal⟩
  have hResult := run_exitSummaryBuild_certificate h100 flat inc covers rankArc subStart hIn hWork
  have hLift := liftRunWithPayload (valid := valid)
    (bound := 3000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount)
    rfl rfl input hResult hZero hCfg hSim hBody hExitLt
  have hScale :
      4 * (3000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount) =
        12000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount := by
    rw [← Nat.mul_assoc, ← Nat.mul_assoc] <;> rfl
  rw [hScale] at hLift
  exact hLift

end PaperB.RamExitFamilyLoop
