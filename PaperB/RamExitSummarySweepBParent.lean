module

public import PaperB.RamExitSummarySweepBParentPrepare
public import PaperB.RamExitSummarySweepBFresh
public import PaperB.RamExitSummarySweepAJoin
public import PaperB.RamExitSummarySweepBParentWrite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 4096

/-! Correctness and operation count for the cached parent-map update. -/

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

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem step4B_parentMap_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4BOneNodeInstrs (bits := bits) basePc h100))
    (hSz : basePc + 1039 < code.size)
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
    {wFit : Width bits (max r.out.tables.next nGlobal)}
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    {rankKahn : Vertex H → Nat}
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    (idx : Nat) (w : Nat) (hwLt : w < r.out.tables.next)
    (Pc : CutPair H) (hBackW : r.out.tables.back[w]? = some (some Pc))
    (hTrW : max (rankKahn Pc.fst) (rankKahn Pc.snd) = idx)
    (ref : Store)
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∀ (hParPos : 0 < B.F.parentOf w)
    (ok : LiveStoreOK B.F ref (liveBefore flat increasing covers rankArc r rankKahn idx))
    (hRefLive : ∀ u, liveBefore flat increasing covers rankArc r rankKahn idx u → ref u = C.built.ref u)
    (st : State DomL) (hpc : st.pc = basePc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hCur : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCCursor]?).map Fin.val = some w)
    (hParW : (st.data[storedBase r.out.tables.next + 18 * w]?).map Fin.val = some (B.F.parentOf w))
    (hJumpW : (st.data[storedBase r.out.tables.next + 18 * w + 1]?).map Fin.val = some (B.F.jumpOf w))
    (hDepth : ∀ u : Fin r.out.tables.next, (st.data[u.val]?).map Fin.val = some (B.F.depthOf u.val))
    (hStored : ∀ u : Fin r.out.tables.next, liveBefore flat increasing covers rankArc r rankKahn idx u.val →
      (st.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (ref u.val).parent ∧
      (st.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (ref u.val).jump ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 2) (ref u.val).parentMap ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 10) (ref u.val).jumpMap)
    (hPrior : ∀ q : Fin H.vertexCount, rankKahn q ≤ idx →
      ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q)),
    ∃ (Pp : CutPair H) (i : Fin (exitTransferDrivers r).size) (k : Nat) (t : State DomL),
      k ≤ 1350 * OracleContract.L H.vertexCount ∧
      Steps code input k st t ∧ t.pc = basePc + 703 ∧
      r.out.tables.back[B.F.parentOf w]? = some (some Pp) ∧
      C.built.slotOf (C.built.model.child i) = w ∧
      C.built.model.child i = Pc ∧ C.built.model.parent i = Pp ∧
      liveBefore flat increasing covers rankArc r rankKahn idx (B.F.parentOf w) ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      MapWordsAt t.data (storedBase r.out.tables.next + 18 * w + 2) (C.built.model.wantMap i) ∧
      (t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48]?).map Fin.val = some (B.F.parentOf w) ∧
      (t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 49]?).map Fin.val = some (B.F.jumpOf w) ∧
      (t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 55]?).map Fin.val =
        some (storedBase r.out.tables.next + 18 * w) ∧
      (∀ j, (j < storedBase r.out.tables.next + 18 * w + 2 ∨
          (storedBase r.out.tables.next + 18 * w + 10 ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEvalU) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 56 ≤ j) →
        t.data[j]? = st.data[j]?) := by
  intro C B hParPos ok hRefLive st hpc hMeta hCur hParW hJumpW hDepth hStored hPrior
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let metaBase := metaArrBase n m N
  have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hBoundMeta : metaBase + 64 ≤ workCap := by
    dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
  have hInCap : 4 + n + 4 * N + 3 * m ≤ inputCap := hIn.cap_ge
  have hInFit : inputCap ≤ 2 ^ bits := hi
  have hMod : C.built.model = actualModel B entryRank rankArc flat := C.built.model_eq
  have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
  obtain ⟨Pp, i, hBackP, hSlotW, hChildI, hParentI, hLiveP, hPMWant⟩ :=
    step4B_wantMap flat increasing covers rankArc r entryRank
      (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout rankKahn rankArcKahn idx
      hRefLive hwLt hParPos hBackW hTrW
  let pN := B.F.parentOf w
  let jN := B.F.jumpOf w
  have hwSize : w < B.F.size := by rw [B.G.size_eq]; exact hwLt
  have hpLt : pN < N := by
    change pN < r.out.tables.next
    rw [← B.G.size_eq]
    exact B.G.layout.valid.parentOf_lt_size hwSize
  -- Phase 1 (`0..61`, 62 steps): load `w`, `baseW`, `p`, `jW`, `a`, `b`, `pFst`, `pSnd`, `dp` into `metaBase + 48..55`!
  obtain ⟨hRecord, hChild, hParent, hLiftFirst, hLiftSecond, hJoin, hWriteFirst, hWriteSecond⟩ :=
    step4B_parent_placed hPl
  have hRecordEnd : storedBase N + 18 * w + 18 ≤ metaBase := by unfold storedBase; omega
  have hRecordsFit : storedBase N + 18 * N ≤ metaBase := by unfold storedBase; omega
  have hDepthFit : N ≤ metaBase := by omega
  have hLowDepth (u : Fin N) : u.val < metaBase :=
    Nat.lt_of_lt_of_le u.isLt hDepthFit
  have hLowRecord (u : Fin N) (i : Nat) (hi : i < 18) :
      storedBase N + 18 * u.val + i < metaBase :=
    Nat.lt_of_lt_of_le (by have := u.isLt; omega) hRecordsFit
  have hOffsetLt (off : Nat) (hOff : off < 64) : metaBase + off < workCap := by omega
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (hOffsetLt off hOff) hw
  obtain ⟨s34, hSteps34, hpc34, hMeta34, h48_34, h49_34, h50_34, h51_34, h52_34,
    h53_34, h54_34, h55_34, hData34⟩ := step4B_prepareParent_spec (input := input)
      basePc h100 hRecord hChild hParent (by omega) hIn w pN jN hwLt hpLt Pc Pp hBackW hBackP
      B.F.depthOf st hpc hMeta hBoundMeta hCur hParW hJumpW hDepth

  change ∀ j, j < metaBase + 48 ∨ metaBase + 56 ≤ j → s34.data[j]? = st.data[j]? at hData34
  have mkEndpointOK : ∀ z : Vertex H, rankKahn z ≤ idx →
      (z.val = Pc.fst.val ∨ z.val = Pc.snd.val) →
      z.val ≠ Pp.fst.val → z.val ≠ Pp.snd.val →
      ValuesWordsAt s34.data (priorBase N + 6 * z.val) (C.built.model.wantBase z) ∧
      liveBefore flat increasing covers rankArc r rankKahn idx ((selectors (orderedConfig p large) r.out).label z) := by
    intro z hRkZ hzEnd hNe1 hNe2
    have hP34 := hPrior z hRkZ
    have hPriorEq : ∀ i < 6, s34.data[priorBase N + 6 * z.val + i]? = st.data[priorBase N + 6 * z.val + i]? := fun i hi =>
      hData34 _ (Or.inl (by change _ < metaBase + _; unfold priorBase; omega))
    have hValsZ := valuesWordsAt_frame hPriorEq hP34
    have hLost : H.Lost Pp z := by
      have hwF : w < B.F.size := B.G.size_eq.symm ▸ hwLt
      have hPcKey : (buildProperLossForest H rank).nodeKey? (B.E.image ⟨w, hwF⟩) = some Pc :=
        Option.some.inj ((B.E.back_eq ⟨w, hwF⟩).symm.trans hBackW)
      have hpF : pN < B.F.size := B.G.layout.valid.parentOf_lt_size hwF
      have hPpKey : (buildProperLossForest H rank).nodeKey?
          ((buildProperLossForest H rank).parent (B.E.image ⟨w, hwF⟩)) = some Pp := by
        rw [← B.E.parent_eq ⟨w, hwF⟩]
        have hUpEq : B.up ⟨w, hwF⟩ = ⟨pN, hpF⟩ := Fin.ext (B.hUp ⟨w, hwF⟩)
        rw [hUpEq]
        exact Option.some.inj ((B.E.back_eq ⟨pN, hpF⟩).symm.trans hBackP)
      exact buildProperLossForest_edge_endpoints_lost rankArc flat hPcKey hPpKey z
        (by rcases hzEnd with h | h; exact Or.inl (Fin.ext h); exact Or.inr (Fin.ext h))
    have hNotMem : ¬ Pp.Mem z := by
      intro hM; rcases hM with rfl | rfl
      · exact hNe1 rfl
      · exact hNe2 rfl
    have hProp : H.ProperLoss Pp z := ⟨hLost, hNotMem⟩
    have hpPos : 0 < pN := hParPos
    have hpF : pN < B.F.size := B.G.layout.valid.parentOf_lt_size (B.G.size_eq.symm ▸ hwLt)
    have hPpKey : (buildProperLossForest H rank).nodeKey? (B.E.image ⟨pN, hpF⟩) = some Pp :=
      Option.some.inj ((B.E.back_eq ⟨pN, hpF⟩).symm.trans hBackP)
    have hvPos := ((properLoss_iff_ramTest flat increasing covers rankArc r hpPos hpLt hPpKey z).mp hProp).1
    obtain ⟨Az, hOwnZ, hBackZ, _, _⟩ :=
      owner_eq_some_of_label_pos flat increasing covers rankArc r entryRank z hvPos
    have hTrZ := Nat.lt_of_lt_of_le
      (trigger_lt_properLoss flat rankKahn rankArcKahn
        ((actualModel B entryRank rankArc flat).ownerProper z Az hOwnZ)) hRkZ
    exact ⟨hValsZ, ⟨B.G.size_eq ▸ B.E.label_lt z True.intro, Or.inr (Or.inr ⟨Az, hBackZ, hTrZ⟩)⟩⟩
  -- Run `step4BFresh` for `a = Pc.fst` (`zOff = 50`) then copy `36..41 -> 30..35`:
  have hPlF0 : Placed code (basePc + 62) (step4BFreshInstrs (bits := bits) (basePc + 62) 50 (by omega) h100) := by
    unfold step4BOneNode_firstLift at hLiftFirst
    exact Placed_append_left (Placed_append_left hLiftFirst)
  obtain ⟨kF0, s35, hkF0, hs35, hpc35, hMeta35, hFresh0, hFr35⟩ := run_step4BFresh (input := input) (basePc + 62) 50 (by omega) h100
    hPlF0 (by omega) flat increasing covers rankArc hIn hWork ok B.G.size_eq B rfl Pc.fst Pp.fst Pp.snd (B.F.depthOf pN)
    (C.built.model.wantBase Pc.fst) s34 hpc34 hMeta34 h50_34 h52_34 h53_34 h54_34
    (fun u => by rw [hData34 u.val (Or.inl (Nat.lt_of_lt_of_le (hLowDepth u) (Nat.le_add_right _ _)))]; exact hDepth u)
    (fun u huL => by
      have hSeg : ∀ i < 18, s34.data[storedBase N + 18 * u.val + i]? = st.data[storedBase N + 18 * u.val + i]? := fun i hi =>
        hData34 (storedBase N + 18 * u.val + i) (Or.inl (Nat.lt_of_lt_of_le (hLowRecord u i hi) (Nat.le_add_right _ _)))
      have ho := hStored u huL
      have hSeg0 := hSeg 0 (by decide)
      simp only [Nat.add_zero] at hSeg0
      refine ⟨by rw [hSeg0]; exact ho.1, by rw [hSeg 1 (by decide)]; exact ho.2.1,
        mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (2 + i) (by omega)) ho.2.2.1,
        mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (10 + i) (by omega)) ho.2.2.2⟩)
    (fun h1 h2 => mkEndpointOK Pc.fst (hTrW ▸ Nat.le_max_left _ _) (Or.inl rfl) h1 h2)
  have hData35 : ∀ j, (j < metaBase + mIdxEvalU ∨
      (metaBase + (mIdxEvalD + 1) ≤ j ∧ j < metaBase + mIdxEval0) ∨
      metaBase + 48 ≤ j) → s35.data[j]? = s34.data[j]? := hFr35
  -- Copy `36..41 -> 30..35` (`basePc + 300..325`):
  have hPlC6 : Placed code (basePc + 304) (copy6Instrs (bits := bits) reg2 reg3 reg4) := by
    unfold step4BOneNode_firstLift at hLiftFirst
    simpa only [List.length_append, step4BFreshInstrs_length, List.length_cons, List.length_nil,
      Nat.reduceAdd] using Placed_append_right hLiftFirst
  have hCopySetup : Placed code (basePc + 300)
      [.imm reg2 ⟨30, by omega⟩, .add reg2 rMeta reg2,
       .imm reg3 ⟨36, by omega⟩, .add reg3 rMeta reg3] := by
    unfold step4BOneNode_firstLift at hLiftFirst
    simpa only [step4BFreshInstrs_length] using Placed_append_right (Placed_append_left hLiftFirst)
  have haI300 : code[s35.pc]? = some (.imm reg2 ⟨30, by omega⟩) := by rw [hpc35]; exact hCopySetup 0 _ rfl
  obtain ⟨s36, hs36Raw, hpc36, h2_36, ho36, hd36⟩ := step_imm_at (input := input) haI300 (by omega)
  have hs36 := steps_1_of_step hs36Raw
  have haA301 : code[s36.pc]? = some (.add reg2 rMeta reg2) := by rw [hpc36, hpc35]; exact hCopySetup 1 _ rfl
  obtain ⟨s37, hs37Raw, hpc37, h2_37, ho37, hd37⟩ := step_add_at (input := input) haA301 (by omega)
  have hs37 := steps_1_of_step hs37Raw
  have h2Val37 : (reg s37 reg2).val = metaBase + mIdxAcc0 := by
    rw [h2_37, add_no_wrap _ _ (by rw [ho36 rMeta (by intro h; cases h), hMeta35.rMeta_eq, h2_36]; exact hOffsetFit 30 (by decide)),
      ho36 rMeta (by intro h; cases h), hMeta35.rMeta_eq, h2_36]
  have haI302 : code[s37.pc]? = some (.imm reg3 ⟨36, by omega⟩) := by rw [hpc37, hpc36, hpc35]; exact hCopySetup 2 _ rfl
  obtain ⟨s38, hs38Raw, hpc38, h3_38, ho38, hd38⟩ := step_imm_at (input := input) haI302 (by omega)
  have hs38 := steps_1_of_step hs38Raw
  have haA303 : code[s38.pc]? = some (.add reg3 rMeta reg3) := by rw [hpc38, hpc37, hpc36, hpc35]; exact hCopySetup 3 _ rfl
  obtain ⟨s39, hs39Raw, hpc39, h3_39, ho39, hd39⟩ := step_add_at (input := input) haA303 (by omega)
  have hs39 := steps_1_of_step hs39Raw
  have hM_39 : (reg s39 rMeta).val = metaBase := by
    rw [ho39 rMeta (by intro h; cases h), ho38 rMeta (by intro h; cases h), ho37 rMeta (by intro h; cases h),
      ho36 rMeta (by intro h; cases h), hMeta35.rMeta_eq]
  have h3Val39 : (reg s39 reg3).val = metaBase + mIdxEval0 := by
    rw [h3_39, add_no_wrap _ _ (by rw [ho38 rMeta (by intro h; cases h), ho37 rMeta (by intro h; cases h),
      ho36 rMeta (by intro h; cases h), hMeta35.rMeta_eq, h3_38]; exact hOffsetFit 36 (by decide)),
      ho38 rMeta (by intro h; cases h), ho37 rMeta (by intro h; cases h),
      ho36 rMeta (by intro h; cases h), hMeta35.rMeta_eq, h3_38]
  have h2Val39 : (reg s39 reg2).val = metaBase + mIdxAcc0 := by
    rw [ho39 reg2 (by intro h; cases h), ho38 reg2 (by intro h; cases h), h2Val37]
  have h1_39 : (reg s39 reg1).val = 1 := by
    rw [ho39 reg1 (by intro h; cases h), ho38 reg1 (by intro h; cases h), ho37 reg1 (by intro h; cases h),
      ho36 reg1 (by intro h; cases h), hMeta35.r1_one]
  have h0_39 : (reg s39 reg0).val = 0 := by
    rw [ho39 reg0 (by intro h; cases h), ho38 reg0 (by intro h; cases h), ho37 reg0 (by intro h; cases h),
      ho36 reg0 (by intro h; cases h), hMeta35.r0_zero]
  have hd39' : s39.data = s35.data := by rw [hd39, hd38, hd37, hd36]
  let fresh0 := if Pc.fst.val = Pp.fst.val ∨ Pc.fst.val = Pp.snd.val then zero
    else Map.eval (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label Pc.fst) (B.F.depthOf pN)).composed
      (C.built.model.wantBase Pc.fst)
  obtain ⟨s40, hs40, hpc40, hAcc0_40, hPres40, hFr40⟩ := run_copy6 (input := input) (basePc + 304) reg2 reg3 reg4
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPlC6 (by omega) (metaBase + mIdxEval0) (metaBase + mIdxAcc0) fresh0
    (by dsimp only [mIdxEval0]; omega) (by dsimp only [mIdxAcc0]; omega) (by dsimp only [mIdxAcc0]; omega)
    (Or.inl (by dsimp only [mIdxAcc0, mIdxEval0]; omega))
    s39 (by rw [hpc39, hpc38, hpc37, hpc36, hpc35]) h1_39 h3Val39 h2Val39 (by rw [hd39']; exact hFresh0)
  have hM_40 : (reg s40 rMeta).val = metaBase := by
    rw [hPres40 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM_39]
  have h0_40 : (reg s40 reg0).val = 0 := by
    rw [hPres40 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_39]
  have h1_40 : (reg s40 reg1).val = 1 := by
    rw [hPres40 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_39]
  have hData40 : ∀ j, (j < metaBase + mIdxEvalU ∨ metaBase + 48 ≤ j) → s40.data[j]? = s34.data[j]? := fun j hj => by
    rw [hFr40 j (by dsimp only [mIdxAcc0, mIdxEvalU] at *; rcases hj with h | h <;> omega), hd39']
    exact hData35 j (by dsimp only [mIdxEvalU] at *; rcases hj with h | h <;> omega)
  have hMeta40 : MetaReady s40 n m N nGlobal :=
    hMeta34.preserve hM_40 h0_40 h1_40 (fun i hi => hData40 (metaBase + i) (Or.inl (by dsimp only [mIdxEvalU]; omega)))
  -- Run `step4BFresh` for `b = Pc.snd` (`zOff = 51`) -> `mIdxEval0` (`36..41`):
  have hPlF1 : Placed code (basePc + 326) (step4BFreshInstrs (bits := bits) (basePc + 326) 51 (by omega) h100) :=
    hLiftSecond
  obtain ⟨kF1, s41, hkF1, hs41, hpc41, hMeta41, hFresh1, hFr41⟩ := run_step4BFresh (input := input) (basePc + 326) 51 (by omega) h100
    hPlF1 (by omega) flat increasing covers rankArc hIn hWork ok B.G.size_eq B rfl Pc.snd Pp.fst Pp.snd (B.F.depthOf pN)
    (C.built.model.wantBase Pc.snd) s40 hpc40 hMeta40
    (by rw [hData40 (metaBase + 51) (Or.inr (by omega))]; exact h51_34)
    (by rw [hData40 (metaBase + 52) (Or.inr (by omega))]; exact h52_34)
    (by rw [hData40 (metaBase + 53) (Or.inr (by omega))]; exact h53_34)
    (by rw [hData40 (metaBase + 54) (Or.inr (by omega))]; exact h54_34)
    (fun u => by rw [hData40 u.val (Or.inl (by have := hLowDepth u; omega)), hData34 u.val (Or.inl (Nat.lt_of_lt_of_le (hLowDepth u) (Nat.le_add_right _ _)))]; exact hDepth u)
    (fun u huL => by
      have hSeg : ∀ i < 18, s40.data[storedBase N + 18 * u.val + i]? = st.data[storedBase N + 18 * u.val + i]? := fun i hi => by
        rw [hData40 (storedBase N + 18 * u.val + i) (Or.inl (by have := hLowRecord u i hi; omega)),
            hData34 (storedBase N + 18 * u.val + i) (Or.inl (Nat.lt_of_lt_of_le (hLowRecord u i hi) (Nat.le_add_right _ _)))]
      have ho := hStored u huL
      have hSeg0 := hSeg 0 (by decide)
      simp only [Nat.add_zero] at hSeg0
      refine ⟨by rw [hSeg0]; exact ho.1, by rw [hSeg 1 (by decide)]; exact ho.2.1,
        mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (2 + i) (by omega)) ho.2.2.1,
        mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg (10 + i) (by omega)) ho.2.2.2⟩)
    (fun h1 h2 => by
      have hEP := mkEndpointOK Pc.snd (hTrW ▸ Nat.le_max_right _ _) (Or.inr rfl) h1 h2
      refine ⟨?_, hEP.2⟩
      have hEq6 : ∀ i < 6, s40.data[priorBase N + 6 * Pc.snd.val + i]? = s34.data[priorBase N + 6 * Pc.snd.val + i]? := fun i hi =>
        hData40 _ (Or.inl (by change _ < metaBase + _; unfold priorBase; omega))
      exact valuesWordsAt_frame hEq6 hEP.1)
  change ∀ j, (j < metaBase + mIdxEvalU ∨
    (metaBase + (mIdxEvalD + 1) ≤ j ∧ j < metaBase + mIdxEval0) ∨ metaBase + 48 ≤ j) →
    s41.data[j]? = s40.data[j]? at hFr41
  let fresh1 := if Pc.snd.val = Pp.fst.val ∨ Pc.snd.val = Pp.snd.val then zero
    else Map.eval (foldFused B.F ref ((selectors (orderedConfig p large) r.out).label Pc.snd) (B.F.depthOf pN)).composed
      (C.built.model.wantBase Pc.snd)
  have hAcc0_41 : ValuesWordsAt s41.data (metaBase + mIdxAcc0) fresh0 := by
    have hEq6 : ∀ i < 6, s41.data[metaBase + mIdxAcc0 + i]? = s40.data[metaBase + mIdxAcc0 + i]? := fun i hi =>
      hFr41 (metaBase + mIdxAcc0 + i) (Or.inr (Or.inl ⟨by dsimp only [mIdxEvalD, mIdxAcc0]; omega, by dsimp only [mIdxAcc0, mIdxEval0]; omega⟩))
    exact valuesWordsAt_frame hEq6 hAcc0_40
  have hJoin0Placed : Placed code (basePc + 564)
      (step4A_joinAtInstrs (bits := bits) (basePc + 564) 30 36 (by omega) (by omega)) := by
    exact Placed_window hJoin 0 rfl
  obtain ⟨kJ0, s47, hkJ0, hs47, hpc47, h0_47, h1_47, hM_47, hJoin0, hFr47⟩ :=
    step4A_joinAt_spec (input := input) (basePc + 564) metaBase 30 36 h100 (by decide) (by decide)
      hBoundMeta hJoin0Placed (by omega) s41 hpc41 hMeta41.r0_zero hMeta41.r1_one hMeta41.rMeta_eq
      fresh0.x0 fresh1.x0 hAcc0_41.1 hFresh1.1
  have hJoin1Placed : Placed code (basePc + 594)
      (step4A_joinAtInstrs (bits := bits) (basePc + 594) 33 39 (by omega) (by omega)) := by
    exact Placed_window hJoin 30 rfl
  have hAcc1_47 : IntervalWordsAt s47.data (metaBase + 33) fresh0.x1 :=
    intervalWordsAt_frame (fun i hi => hFr47 _ (Or.inr (by omega))) hAcc0_41.2
  have hFresh1_47 : IntervalWordsAt s47.data (metaBase + 39) fresh1.x1 :=
    intervalWordsAt_frame (fun i hi => hFr47 _ (Or.inr (by omega))) hFresh1.2
  obtain ⟨kJ1, s53, hkJ1, hs53, hpc53, h0_53, h1_53, hM_53, hJoin1, hFr53⟩ :=
    step4A_joinAt_spec (input := input) (basePc + 594) metaBase 33 39 h100 (by decide) (by decide)
      hBoundMeta hJoin1Placed (by omega) s47 hpc47 h0_47 h1_47 hM_47 fresh0.x1 fresh1.x1 hAcc1_47 hFresh1_47
  have hData53 : ∀ j, (j < metaBase + mIdxEvalU ∨ metaBase + 48 ≤ j) → s53.data[j]? = s34.data[j]? := fun j hj => by
    rw [hFr53 j (by dsimp only [mIdxEvalU] at *; rcases hj with h | h <;> omega),
      hFr47 j (by dsimp only [mIdxEvalU] at *; rcases hj with h | h <;> omega),
      hFr41 j (by dsimp only [mIdxEvalU, mIdxEvalD, mIdxEval0] at *; rcases hj with h | h <;> omega)]
    exact hData40 j hj
  have hC53 : ValuesWordsAt s53.data (metaBase + mIdxAcc0) (vjoin fresh0 fresh1) :=
    ⟨intervalWordsAt_frame (fun i hi => hFr53 (metaBase + 30 + i) (Or.inl (by omega))) hJoin0, hJoin1⟩
  have hNe : Pc.fst.val ≠ Pc.snd.val := fun heq => Pc.ne (Fin.ext heq)
  obtain ⟨kP, t, hkP, hsP, hpcT, h0T, h1T, hMT, hMap, hFrP⟩ :=
    step4B_writeParent_spec (input := input) basePc h100 hWriteFirst hWriteSecond (by omega)
      n m N w Pc.fst.val Pc.snd.val Pp.fst.val Pp.snd.val hwLt hNe hBoundMeta
      (vjoin fresh0 fresh1) s53 hpc53 h0_53 h1_53 hM_53
      (by rw [hData53 (metaBase + 50) (Or.inr (by omega))]; exact h50_34)
      (by rw [hData53 (metaBase + 51) (Or.inr (by omega))]; exact h51_34)
      (by rw [hData53 (metaBase + 52) (Or.inr (by omega))]; exact h52_34)
      (by rw [hData53 (metaBase + 53) (Or.inr (by omega))]; exact h53_34)
      (by rw [hData53 (metaBase + 55) (Or.inr (by omega))]; exact h55_34) hC53
  have hFrAll : ∀ j, (j < storedBase N + 18 * w + 2 ∨
      (storedBase N + 18 * w + 10 ≤ j ∧ j < metaBase + mIdxEvalU) ∨
      metaBase + 56 ≤ j) → t.data[j]? = st.data[j]? := fun j hj => by
    rw [hFrP j (by rcases hj with h | ⟨h, _⟩ | h <;> omega)]
    rcases hj with h | ⟨_, h2⟩ | h
    · rw [hData53 j (Or.inl (by dsimp only [mIdxEvalU]; omega))]
      exact hData34 j (Or.inl (by omega))
    · rw [hData53 j (Or.inl h2)]
      exact hData34 j (Or.inl (by change j < metaBase + 48; dsimp only [mIdxEvalU] at h2; omega))
    · rw [hData53 j (Or.inr (by omega))]
      exact hData34 j (Or.inr h)
  have hMapT : MapWordsAt t.data (storedBase N + 18 * w + 2) (C.built.model.wantMap i) := by
    rw [← hPMWant]
    exact hMap
  have hCopySteps : Steps code input (4 + 22) s35 s40 :=
    (hs36.append hs37).append ((hs38.append hs39).append hs40)
  have hLiftSteps : Steps code input (62 + kF0 + (4 + 22) + kF1) st s41 :=
    ((hSteps34.append hs35).append hCopySteps).append hs41
  have hStepsAll : Steps code input (62 + kF0 + (4 + 22) + kF1 + kJ0 + kJ1 + kP) st t :=
    ((hLiftSteps.append hs47).append hs53).append hsP
  have hPre48_55 : ∀ j, metaBase + 48 ≤ j → t.data[j]? = s34.data[j]? := fun j hj => by
    rw [hFrP j (Or.inr (by omega)), hData53 j (Or.inr hj)]
  exact ⟨Pp, i, _, t, by omega, hStepsAll, hpcT, hBackP, hSlotW, hChildI, hParentI,
    hLiveP, hMeta.preserve hMT h0T h1T (fun k hk =>
      hFrAll (metaBase + k) (Or.inr (Or.inl ⟨by omega, by dsimp only [mIdxEvalU]; omega⟩))),
    hMapT,
    by rw [hPre48_55 (metaBase + 48) (by omega)]; exact h48_34,
    by rw [hPre48_55 (metaBase + 49) (by omega)]; exact h49_34,
    by rw [hPre48_55 (metaBase + 55) (by omega)]; exact h55_34,
    hFrAll⟩

end PaperB.RamProgram.ExitSummaryBuild
