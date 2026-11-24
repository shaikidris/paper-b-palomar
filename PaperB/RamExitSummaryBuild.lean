module

public import PaperB.RamExitSummarySealBridge
public import PaperB.RamExitSummarySweepRun
public import PaperB.RamExitSummarySweepROM
public import PaperB.RamExitSummarySweepCount
public import PaperB.RamExitSummarySweepBRun
public import PaperB.RamExitSummarySweepARun
public import PaperB.RamExitSummaryStage3

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 8192

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

/-! ### 11. Stage 4 outer loop (`stage4Phase`) -/



/-! ### 12. Linked Word-RAM Program (`exitSummaryBuildProgram`) & End-to-End Correctness -/

section LinkedProgram

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def exitSummaryBuildPhases (h100 : 100 ≤ 2 ^ bits) : List (Phase DomL) :=
  setupPhases (hi := hi) (hw := hw) h100 ++ [stage4Phase (hi := hi) (hw := hw) h100]

def exitSummaryBuildProgram (h100 : 100 ≤ 2 ^ bits) : Program DomL :=
  (linkNonEmpty (initMetaPhase (hi := hi) (hw := hw) h100)
    (stage1Phases (hi := hi) (hw := hw) h100 ++
      csrKahnPhases (hi := hi) (hw := hw) h100 ++
      stage3Phases (hi := hi) (hw := hw) h100 ++
      [stage4Phase (hi := hi) (hw := hw) h100])).code

private theorem phaseChain_to_phasesExec {input : Input DomL} :
    ∀ {ps : List (Phase DomL)} {s t : State DomL} {w : Nat},
      PhaseChain input ps s t w → PhasesExec input ps s t w
  | [], _, _, _, .nil s => PhasesExec.nil s
  | _ :: _, _, _, _, .cons hFirst hTail =>
      PhasesExec.cons hFirst (phaseChain_to_phasesExec hTail)



theorem run_exitSummaryBuild {input : Input DomL}
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
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL) :
    let N := r.out.tables.next
    let hNLe : N ≤ H.vertexCount + 1 := (B_next_pos flat increasing covers rankArc r).2
    let hnGLt : nGlobal < 2 ^ bits := by
      obtain ⟨w3, _, hw3⟩ := Option.map_eq_some_iff.mp hIn.hdr_nGlobal
      rw [← hw3]; exact w3.isLt
    let hLayout : N + 18 * N ≤ 2 ^ bits := by
      unfold exitWorkCap at hWork; have : workCap ≤ 2 ^ bits := hw; omega
    let wFit : Width bits (max N nGlobal) := ⟨by omega, by unfold TagsFit; omega⟩
    let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
      (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    ∃ steps u states,
      steps ≤ 3000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount ∧
      run (exitSummaryBuildProgram (hi := hi) (hw := hw) h100) input steps (Phase.initial s0) =
        some ⟨u, steps⟩ ∧
      SuccessfulTrace (exitSummaryBuildProgram (hi := hi) (hw := hw) h100) input
        (Phase.initial s0) states ⟨u, steps⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 ∧
      19 * N + 6 * H.vertexCount ≤ u.data.size ∧
      let R := ramBankRegion u.data N
        (by unfold exitWorkCap at hWork; rw [u.data_size]; exact Nat.le_trans (by omega) hWork)
        (by unfold exitWorkCap at hWork; have : workCap ≤ 2 ^ bits := hw; omega)
      Occupied u.data R C.built.bundle.F C.built.ref wFit ∧
      DecodedOccupied u.data R C.built.bundle.F C.built.ref wFit.tags C.built.live ∧
      LiveStoreOK C.built.bundle.F C.built.ref C.built.live ∧
      (∀ (hBnd : 19 * N + 6 * C.built.bases.data.size ≤ u.data.size),
        let sealView : SealedPriorBase.BaseView C.built.bases.data.size u.data.size :=
          ⟨19 * N, hBnd⟩
        let hbMax : SealedPriorBase.BaseBound (max N nGlobal) C.built.bases.data := fun v =>
          ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
            rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩
        SealedPriorBase.Placed C.wEndpoints C.built.bases.data C.baseBound u.data sealView ∧
        SealedPriorBase.Placed wFit C.built.bases.data hbMax u.data sealView ∧
        (∀ j : Fin (6 * H.vertexCount),
          u.data[19 * N + j.val]'(by
            have hSz := C.built.bases.size_data; have := j.isLt; omega) =
          C.sealed[j.val]'(by rw [C.sealed_size]; exact j.isLt)) ∧
        (∀ (Bcut : CutPair H), Bcut.fst < Bcut.snd →
          ∀ y : Vertex H, H.ProperLoss Bcut y →
            ∃ u0 d : Nat, u0 < N ∧
              SealedPriorBase.run u.data R wFit.tags u.data sealView
                ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d =
                C.built.model.ref Bcut y ∧
              (foldStored u.data R wFit.tags u0 d).steps ≤ 3 * ceilLog2 (H.vertexCount + 2))) := by
  intro N hNLe hnGLt hLayout wFit C
  have hRankLtBits : ∀ x : Fin H.origVertexCount, entryRank x < 2 ^ bits := fun x =>
    Nat.lt_trans (hIn.hRank_lt x) hnGLt
  obtain ⟨kSetup, orderKahn, sizeKahn, rankKahn, buckets, s3, hkSetup, hSetupChain, hS3⟩ :=
    run_setupPhases flat increasing covers rankArc h100 hIn hWork s0
  obtain ⟨k4, t4, hk4, hRun4, _, hDep4, hSt4, hPrior4⟩ :=
    run_stage4 flat increasing covers rankArc h100 hIn hWork hRankLtBits hS3 (wFit := wFit) hLayout
  have hAllChain : PhaseChain input
      (initMetaPhase (hi := hi) (hw := hw) h100 ::
        (stage1Phases (hi := hi) (hw := hw) h100 ++
          csrKahnPhases (hi := hi) (hw := hw) h100 ++
          stage3Phases (hi := hi) (hw := hw) h100 ++
          [stage4Phase (hi := hi) (hw := hw) h100]))
      s0 t4 (kSetup + k4) := by
    have hEqList : initMetaPhase (hi := hi) (hw := hw) h100 ::
        (stage1Phases (hi := hi) (hw := hw) h100 ++
          csrKahnPhases (hi := hi) (hw := hw) h100 ++
          stage3Phases (hi := hi) (hw := hw) h100 ++
          [stage4Phase (hi := hi) (hw := hw) h100]) =
        setupPhases (hi := hi) (hw := hw) h100 ++ [stage4Phase (hi := hi) (hw := hw) h100] := by
      simp only [setupPhases, List.cons_append, List.append_assoc, List.nil_append]
    rw [hEqList]
    exact hSetupChain.append (PhaseChain.cons hRun4 (PhaseChain.nil t4))
  obtain ⟨u, states, _, hUData, hRunProg, hTrace, hPeak⟩ :=
    run_linkNonEmpty _ (initMetaPhase (hi := hi) (hw := hw) h100) (phaseChain_to_phasesExec hAllChain)
  have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
  have hStepsBound : kSetup + k4 ≤ 3000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount := by
    have hSetupLe : kSetup ≤ 450 * (H.vertexCount + H.arcCount + 1) := by have := large; omega
    have hSetupMul : kSetup ≤ 450 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount := by
      have h1 := Nat.mul_le_mul_left (450 * (H.vertexCount + H.arcCount + 1)) hLGe1
      omega
    have hTotalMul : 450 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount +
        2400 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount ≤
        3000 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount := by
      rw [← Nat.add_mul, ← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    omega
  have hDataSize : u.data.size = workCap := u.data_size
  have hMemWork : 19 * N + 6 * H.vertexCount ≤ workCap := by
    unfold exitWorkCap at hWork; omega
  have hMemSize : 19 * N + 6 * H.vertexCount ≤ u.data.size := by rw [hDataSize]; exact hMemWork
  have hBitsWork : workCap ≤ 2 ^ bits := hw
  let R := ramBankRegion u.data N (by omega) (by omega)
  have hMapsEnd : ∀ v < N, MapBound nGlobal (C.built.ref v).parentMap ∧
      MapBound nGlobal (C.built.ref v).jumpMap :=
    fun v hv => buildActualDirectBank_mapBounds H flat increasing covers rankArc r entryRank
      (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout v
      (by change v < (buildActualSweepBundle H flat increasing covers rankArc r).F.size
          rw [(buildActualSweepBundle H flat increasing covers rankArc r).G.size_eq]
          exact hv)
  have hWord (j : Nat) : u.data[j]? = t4.data[j]? := congrArg (fun a => a[j]?) hUData
  have hOcc : Occupied u.data R C.built.bundle.F C.built.ref wFit := by
    refine
      { size_eq := C.built.bundle.G.size_eq.symm
        valid := C.built.bundle.G.layout.valid
        depth := fun v => by
          have hv : (t4.data[v.val]?).map Fin.val = some (C.built.bundle.F.depthOf v.val) := hDep4 v
          have hm : v.val < u.data.size := R.depthMem v
          change (u.data[v.val]'hm).val = _
          have ha : (u.data[v.val]?).map Fin.val = some (C.built.bundle.F.depthOf v.val) :=
            (congrArg (Option.map Fin.val) (hWord v.val)).trans hv
          rw [Array.getElem?_eq_getElem hm, Option.map_some] at ha
          exact Option.some.inj ha
        parent_eq := fun v hv => C.built.decoded.parent_eq v (C.built.all_live v hv)
        jump_eq := fun v hv => C.built.decoded.jump_eq v (C.built.all_live v hv)
        maps := fun v => hMapsEnd v.val v.isLt
        packed := fun v hr i => by
          have hStV := hSt4 v
          have hLiveV := C.built.all_live v.val (C.built.bundle.G.size_eq.symm ▸ v.isLt)
          have hpLt : (C.built.ref v.val).parent < N := by
            rw [C.built.decoded.parent_eq v.val hLiveV]
            change C.built.bundle.F.parentOf v.val < r.out.tables.next
            rw [← C.built.bundle.G.size_eq]
            exact C.built.bundle.G.layout.valid.parentOf_lt_size (C.built.bundle.G.size_eq.symm ▸ v.isLt)
          have hjLt : (C.built.ref v.val).jump < N := by
            rw [C.built.decoded.jump_eq v.val hLiveV]
            change C.built.bundle.F.jumpOf v.val < r.out.tables.next
            rw [← C.built.bundle.G.size_eq]
            exact C.built.bundle.G.layout.valid.jumpOf_lt_size (C.built.bundle.G.size_eq.symm ▸ v.isLt)
          have hMapV := hMapsEnd v.val v.isLt
          have hPMBits : MapBound (2 ^ bits) (C.built.ref v.val).parentMap :=
            ⟨rankBound_mono (by omega) hMapV.1.1, rankBound_mono (by omega) hMapV.1.2⟩
          have hJMBits : MapBound (2 ^ bits) (C.built.ref v.val).jumpMap :=
            ⟨rankBound_mono (by omega) hMapV.2.1, rankBound_mono (by omega) hMapV.2.2⟩
          have h0 : (u.data[N + 18 * v.val]?).map Fin.val = some (C.built.ref v.val).parent := by
            rw [hWord]; exact hStV.1
          have h1 : (u.data[N + 18 * v.val + 1]?).map Fin.val = some (C.built.ref v.val).jump := by
            rw [hWord]; exact hStV.2.1
          have hPM : MapWordsAt u.data (N + 18 * v.val + 2) (C.built.ref v.val).parentMap := by
            exact mapWordsAt_frame (fun _ _ => hWord _) hStV.2.2.1
          have hJM : MapWordsAt u.data (N + 18 * v.val + 10) (C.built.ref v.val).jumpMap := by
            exact mapWordsAt_frame (fun _ _ => hWord _) hStV.2.2.2
          exact packed_of_storedWords wFit.tags (by omega) (by omega) hPMBits hJMBits hr
            (by exact R.recordMem v) h0 h1 hPM hJM i }
  have hPart : PartialOccupied u.data R C.built.bundle.F C.built.ref wFit C.built.live :=
    { size_le := Nat.le_of_eq hOcc.size_eq.symm
      valid := hOcc.valid
      live_lt_size := C.built.decoded.live_lt_size
      depth := fun v _ => hOcc.depth v
      parent_eq := fun u0 hu => C.built.decoded.parent_eq u0 hu
      jump_eq := fun u0 hu => C.built.decoded.jump_eq u0 hu
      parent_live := fun u0 hu => C.built.decoded.parent_live u0 hu
      jump_live := fun u0 hu => C.built.decoded.jump_live u0 hu
      maps := fun v _ => hOcc.maps v
      packed := fun v _ hr i => hOcc.packed v hr i }
  have hDec : DecodedOccupied u.data R C.built.bundle.F C.built.ref wFit.tags C.built.live :=
    hPart.toDecoded
  refine ⟨kSetup + k4, u, states, hStepsBound, hRunProg, hTrace, by rw [hPeak]; rfl,
    hMemSize, hOcc, hDec, C.built.liveOK, ?_⟩
  intro hBnd
  let sealView : SealedPriorBase.BaseView C.built.bases.data.size u.data.size := ⟨19 * N, hBnd⟩
  let hbMax : SealedPriorBase.BaseBound (max N nGlobal) C.built.bases.data := fun v =>
    ⟨rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).1,
      rankBound_mono (Nat.le_max_right _ _) (C.baseBound v).2⟩
  have hBaseEq : ∀ y : Fin C.built.bases.data.size,
      (C.built.bases.data[y.val]'(y.isLt)).getD BuiltExit.zero =
        C.built.model.wantBase ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data⟩ := by
    intro y
    have hb := C.built.bases_exact ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data⟩
    change C.built.bases.data[y.val]'(y.isLt) = some _ at hb
    rw [hb]
    rfl
  have hValsBases : ∀ y : Fin C.built.bases.data.size,
      ValuesWordsAt u.data (19 * N + 6 * y.val)
        ((C.built.bases.data[y.val]'(y.isLt)).getD BuiltExit.zero) := by
    intro y
    rw [hBaseEq y]
    exact valuesWordsAt_frame (fun _ _ => hWord _)
      (hPrior4 ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data⟩)
  have hPlaced : SealedPriorBase.Placed C.wEndpoints C.built.bases.data C.baseBound u.data sealView :=
    sealedPlaced_of_valuesWords C.wEndpoints C.built.bases.data C.baseBound
      (by exact hBnd) hValsBases
  have hPlacedMax : SealedPriorBase.Placed wFit C.built.bases.data hbMax u.data sealView :=
    sealedPlaced_of_valuesWords wFit C.built.bases.data hbMax (by exact hBnd) hValsBases
  have hSealedEq : ∀ j : Fin (6 * H.vertexCount),
      u.data[19 * N + j.val]'(by have hSz := C.built.bases.size_data; have := j.isLt; omega) =
        C.sealed[j.val]'(by rw [C.sealed_size]; exact j.isLt) := by
    intro j
    let jFin : Fin (6 * C.built.bases.data.size) :=
      ⟨j.val, by rw [C.built.bases.size_data]; exact j.isLt⟩
    have hP := hPlaced jFin
    have hGet : C.sealed[j.val]'(by rw [C.sealed_size]; exact j.isLt) =
        (SealedPriorBase.serialize C.wEndpoints C.built.bases.data C.baseBound)[j.val]'(by
          rw [SealedPriorBase.seal_size, C.built.bases.size_data]; exact j.isLt) := by
      apply Option.some.inj
      rw [← Array.getElem?_eq_getElem, ← Array.getElem?_eq_getElem, C.sealed_eq]
    exact hP.trans hGet.symm
  refine ⟨hPlaced, hPlacedMax, hSealedEq, ?_⟩
  intro Bcut hCan y hProp
  obtain ⟨u0, d, _, hu0Lt, hRunC, _⟩ := query_canonical_exact C Bcut hCan y hProp
  have hLiveU0 : C.built.live u0 := C.built.all_live u0 hu0Lt
  have hRunEq : SealedPriorBase.run u.data R wFit.tags u.data sealView
      ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d = C.built.model.ref Bcut y := by
    have h1 := SealedPriorBase.run_eq_priorBase u.data R C.wEndpoints C.built.bases.data C.baseBound
      u.data sealView hPlaced ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d
    have h2 : PriorBase.run u.data R wFit.tags C.built.bases.data
        ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d =
      Map.eval (PriorBase.accumulated (foldFused C.built.bundle.F C.built.ref u0 d))
        ((C.built.bases.data[y.val]'(Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm)).getD BuiltExit.zero) :=
      hDec.run_exact_fold_live hLiveU0 d C.built.bases.data
        ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩
    have h3 : PriorBase.run C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
        C.wFit.tags C.built.bases.data
        ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d =
      Map.eval (PriorBase.accumulated (foldFused C.built.bundle.F C.built.ref u0 d))
        ((C.built.bases.data[y.val]'(Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm)).getD BuiltExit.zero) :=
      C.built.decoded.run_exact_fold_live hLiveU0 d C.built.bases.data
        ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩
    have h4 := SealedPriorBase.run_eq_priorBase C.built.bank.mem
      (actualBankRegion r.out.tables.next C.hLayout C.built.bank) C.wEndpoints
      C.built.bases.data C.baseBound C.sealed
      ⟨C.sealView.start, by simpa only [C.built.bases.size_data] using C.sealView.fits⟩ C.placed ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d
    have hTagsEq : C.wEndpoints.tags = wFit.tags := rfl
    have hTagsEqC : C.wEndpoints.tags = C.wFit.tags := rfl
    have h5 : SealedPriorBase.run C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
        C.wFit.tags C.sealed C.sealView y u0 d =
      SealedPriorBase.run C.built.bank.mem
        (actualBankRegion r.out.tables.next C.hLayout C.built.bank)
        C.wFit.tags C.sealed
        ⟨C.sealView.start, by simpa only [C.built.bases.size_data] using C.sealView.fits⟩
        ⟨y.val, Nat.lt_of_lt_of_eq y.isLt C.built.bases.size_data.symm⟩ u0 d := rfl
    rw [← hTagsEq] at h2
    rw [← hTagsEqC] at h3
    rw [← h5, hRunC] at h4
    exact h1.trans (h2.trans (h3.symm.trans h4.symm))
  have hStepsLe : (foldStored u.data R wFit.tags u0 d).steps ≤ 3 * ceilLog2 (H.vertexCount + 2) :=
    live_foldStored_steps_le hDec C.built.liveOK hLiveU0 (bundle_numInserted_le C.built.bundle) d
  exact ⟨u0, d, by change u0 < r.out.tables.next; exact C.built.bundle.G.size_eq ▸ hu0Lt, hRunEq, hStepsLe⟩

end LinkedProgram

end PaperB.RamProgram.ExitSummaryBuild
