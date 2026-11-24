module

public import PaperB.RamExitSummarySweepALoop
public import PaperB.RamExitSummarySweepAOwner
public import PaperB.RamExitSummarySweepZero
public import PaperB.RamExitSummarySweepAWrite

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

/-! The per-vertex prior-base sweep, including setup and writeback. -/

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

private theorem step4A_setup_placed {code : Program DomL} {pc : Nat}
    {h100 : 100 ≤ 2 ^ bits} (h : Placed code pc (step4ASetupInstrs pc (pc + 520) h100)) :
    Placed code pc (step4ASetup_selector pc (pc + 520) h100) ∧
    Placed code (pc + 9) (step4ASetup_backPointers h100) ∧
    Placed code (pc + 29) (step4ASetup_interval h100) ∧
    Placed code (pc + 45) (step4ASetup_accumulators h100) ∧
    Placed code (pc + 67) (step4ASetup_arcs h100) := by
  unfold step4ASetupInstrs at h
  have hAcc := Placed_append_left h
  have hInterval := Placed_append_left hAcc
  have hBack := Placed_append_left hInterval
  have hSelector := Placed_append_left hBack
  have hLen0 : (step4ASetup_selector pc (pc + 520) h100).length = 9 := by
    simp [step4ASetup_selector, metaLoadInstrs]
  have hLen1 : (step4ASetup_backPointers h100).length = 20 := by
    simp [step4ASetup_backPointers, metaLoadInstrs, metaStoreInstrs]
  have hLen2 : (step4ASetup_interval h100).length = 16 := by
    simp [step4ASetup_interval, metaLoadInstrs, metaStoreInstrs]
  have hLen3 : (step4ASetup_accumulators h100).length = 22 := by
    simp [step4ASetup_accumulators, metaStoreInstrs]
  refine ⟨hSelector, ?_, ?_, ?_, ?_⟩
  · simpa only [hLen0] using Placed_append_right hBack
  · simpa only [List.length_append, hLen0, hLen1, Nat.reduceAdd] using Placed_append_right hInterval
  · simpa only [List.length_append, hLen0, hLen1, hLen2, Nat.reduceAdd] using Placed_append_right hAcc
  · simpa only [List.length_append, hLen0, hLen1, hLen2, hLen3, Nat.reduceAdd] using Placed_append_right h

private theorem writePrior_frame {b d j : Nat} (hD : d + 6 ≤ b)
    (hj : j < d ∨ (d + 6 ≤ j ∧ j < b + 24) ∨ b + 55 ≤ j) :
    (j < d ∨ d + 6 ≤ j) ∧
      (j < b + 25 ∨ (b + 48 ≤ j ∧ j < b + 53) ∨ b + 55 ≤ j) ∧
      j ≠ b + 24 ∧ j ≠ b + 25 ∧ j ≠ b + 26 ∧
      (j < b + 30 ∨ (b + 36 ≤ j ∧ j < b + 48) ∨ b + 53 ≤ j) := by
  omega

private theorem owner_frame {b j : Nat}
    (h : j < b + 30 ∨ (b + 36 ≤ j ∧ j < b + 48) ∨ b + 53 ≤ j) :
    (j < b + 30 ∨ b + 30 + 6 ≤ j) ∧
      j ≠ b + 48 ∧ j ≠ b + 49 ∧ j ≠ b + 50 ∧ j ≠ b + 51 ∧ j ≠ b + 52 := by
  omega

theorem run_step4A {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4AInstrs (bits := bits) basePc h100))
    (hSz : basePc + 520 < code.size)
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
    {rankKahn : Vertex H → Nat}
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    (_hRkLt : ∀ v : Vertex H, rankKahn v < H.vertexCount)
    {wFit : Width bits (max r.out.tables.next nGlobal)}
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    (y : Vertex H)
    {ref : Store} {live : Nat → Prop}
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∀ (ok : LiveStoreOK B.F ref live)
    (hRefLive : ∀ w, live w → ref w = C.built.ref w)
    (hLiveBefore : ∀ w, liveBefore flat increasing covers rankArc r rankKahn (rankKahn y) w → live w)
    (st : State DomL) (hpc : st.pc = basePc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hCurY : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCurY]?).map Fin.val = some y.val)
    (hInStart : ∀ i ≤ H.vertexCount, (st.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i))
    (hInArcs : ∀ v < H.vertexCount, ∀ k : Fin (degIn H v),
      (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + k.val)]?).map Fin.val =
        some ((inArcsPrefix H H.arcCount v)[k.val]'(by rw [inArcsPrefix_length]; exact k.isLt)))
    (hDepth : ∀ w : Fin r.out.tables.next, (st.data[w.val]?).map Fin.val = some (B.F.depthOf w.val))
    (hStored : ∀ w : Fin r.out.tables.next, live w.val →
      (st.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
      (st.data[storedBase r.out.tables.next + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 2) (ref w.val).parentMap ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 10) (ref w.val).jumpMap)
    (hPriorPred : ∀ q : Fin H.vertexCount, rankKahn q < rankKahn y →
      ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q))
    (hPriorSelf : ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * y.val) zero),
    ∃ k t, k ≤ 700 * (degIn H y.val + 1) * OracleContract.L H.vertexCount ∧
      Steps code input k st t ∧ t.pc = basePc + 520 ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      ValuesWordsAt t.data (priorBase r.out.tables.next + 6 * y.val) (C.built.model.wantBase y) ∧
      (∀ j, (j < priorBase r.out.tables.next + 6 * y.val ∨
          (priorBase r.out.tables.next + 6 * y.val + 6 ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCurOwner) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 55 ≤ j) →
        t.data[j]? = st.data[j]?) := by
  intro C B ok hRefLive hLiveBefore st hpc hMeta hCurY hInStart hInArcs hDepth hStored hPriorPred hPriorSelf
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let metaBase := metaArrBase n m N
  have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hBoundMeta : metaBase + 64 ≤ workCap := by
    unfold exitWorkCap at hWork
    omega
  have hOffsetLt (off : Nat) (hOff : off < 64) : metaBase + off < workCap := by
    omega
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (hOffsetLt off hOff) hWorkFit
  have hInCap : 4 + n + 4 * N + 3 * m ≤ inputCap := hIn.cap_ge
  have hInFit : inputCap ≤ 2 ^ bits := hi
  have hMod : C.built.model = actualModel B entryRank rankArc flat := C.built.model_eq
  have hRM := hMeta.rMeta_eq
  unfold step4AInstrs at hPl
  have hBeforeWrite := Placed_append_left hPl
  have hPlSetup := Placed_append_left hBeforeWrite
  have hPlLoop : Placed code (basePc + 80) (step4ALoopInstrs (bits := bits) (basePc + 80) h100) := by
    simpa only [step4ASetupInstrs_length] using Placed_append_right hBeforeWrite
  have hPlWrite : Placed code (basePc + 486) (step4AWritePriorInstrs (bits := bits) h100) := by
    simpa only [List.length_append, step4ASetupInstrs_length, step4ALoopInstrs_length, Nat.reduceAdd]
      using Placed_append_right hPl
  obtain ⟨hSelector, hBack, hInterval, hAccumulator, hArcs⟩ := step4A_setup_placed hPlSetup
  -- First 9 instructions: load `y`, `labelsInBase`, read `ownerSlot`, branch!
  have hPl0 : Placed code basePc (metaLoadInstrs (bits := bits) reg2 reg3 mIdxCurY (by dsimp only [mIdxCurY]; omega)) :=
    Placed_window hSelector 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) hpc hRM (hOffsetFit mIdxCurY (by decide)) hCurY
  have hRM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hRM]
  have hPl1 : Placed code (basePc + 3) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxLabelsInBase (by dsimp only [mIdxLabelsInBase]; omega)) :=
    Placed_window hSelector 3 rfl
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc1 hRM1 (hOffsetFit mIdxLabelsInBase (by decide))
    (by rw [hd1]; exact hMeta.meta_labelsIn)
  have h2_2 : (reg s2 reg2).val = y.val := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have haAddL : code[s2.pc]? = some (.add reg3 reg3 reg2) := by rw [hpc2]; exact hSelector 6 _ rfl
  obtain ⟨s3, hs3Raw, hpc3, h3_3, ho3, hd3⟩ := step_add_at (input := input) haAddL (by omega)
  have hs3 := steps_1_of_step hs3Raw
  have h3Val3 : (reg s3 reg3).val = 4 + y.val := by rw [h3_3, add_no_wrap _ _ (by rw [h3_2, h2_2]; omega), h3_2, h2_2]
  let ownerSlot := (selectors (orderedConfig p large) r.out).label y
  obtain ⟨wOwn, hwOwn, hwOwnV⟩ := Option.map_eq_some_iff.mp (hIn.labels_at y)
  have haLoadL : code[s3.pc]? = some (.loadInput reg3 reg3) := by rw [hpc3, hpc2]; exact hSelector 7 _ rfl
  obtain ⟨s4, hs4Raw, hpc4, h3_4, ho4, hd4⟩ := step_loadInput_at (input := input) haLoadL (by omega)
    (by rw [h3Val3]; exact hwOwn)
  have hs4 := steps_1_of_step hs4Raw
  have hOwnVal : (reg s4 reg3).val = ownerSlot := by rw [h3_4, hwOwnV]
  have h0_4 : (reg s4 reg0).val = 0 := by
    rw [ho4 reg0 (by intro h; cases h), ho3 reg0 (by intro h; cases h),
      hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero]
  have h1_4 : (reg s4 reg1).val = 1 := by
    rw [ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h),
      hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one]
  have hM_4 : (reg s4 rMeta).val = metaBase := by
    rw [ho4 rMeta (by intro h; cases h), ho3 rMeta (by intro h; cases h),
      hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hRM1]
  have h2_4 : (reg s4 reg2).val = y.val := by
    rw [ho4 reg2 (by intro h; cases h), ho3 reg2 (by intro h; cases h), h2_2]
  have hd4' : s4.data = st.data := by rw [hd4, hd3, hd2, hd1]
  have haBrOwn : code[s4.pc]? = some (.branchLt reg0 reg3 (basePc + 9) (basePc + 520)) := by
    rw [hpc4, hpc3, hpc2]; exact hSelector 8 _ rfl
  obtain ⟨s5, hs5Raw, hpc5, hr5, hd5⟩ := step_branchLt_at (input := input) haBrOwn (by split <;> omega)
  have hs5 := steps_1_of_step hs5Raw
  have hr5F := reg_of_regs_eq hr5
  have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
  by_cases hOwnPos : 0 < ownerSlot
  · rw [ite_eq_left (by rw [h0_4, hOwnVal]; exact hOwnPos)] at hpc5
    have hOwnLt : ownerSlot < r.out.tables.next := by
      rw [← B.G.size_eq]
      exact B.E.label_lt y True.intro
    obtain ⟨Bcut, hOwnB, hBackB, hCanB, hNodeB⟩ :=
      owner_eq_some_of_label_pos flat increasing covers rankArc r entryRank y hOwnPos
    have h0_5 : (reg s5 reg0).val = 0 := by rw [hr5F, h0_4]
    have h1_5 : (reg s5 reg1).val = 1 := by rw [hr5F, h1_4]
    have hM_5 : (reg s5 rMeta).val = metaBase := by rw [hr5F, hM_4]
    have h2_5 : (reg s5 reg2).val = y.val := by rw [hr5F, h2_4]
    have h3_5 : (reg s5 reg3).val = ownerSlot := by rw [hr5F, hOwnVal]
    have hd5' : s5.data = st.data := by rw [hd5, hd4']
    have hMeta5 : MetaReady s5 n m N nGlobal :=
      hMeta.preserve hM_5 h0_5 h1_5 (fun _ _ => by rw [hd5'])
    obtain ⟨s25, hOwnerTrace, hpc25, h0_25, h1_25, hM_25, h2_25,
        hOwnerFst, hOwnerSnd, hOwnerEntry, hOwnerStop, hOwnerDepth, hFrOwner⟩ :=
      step4A_ownerFields_spec (input := input) basePc h100 hSz hBack hInterval hAccumulator hIn
        y.val ownerSlot (B.F.depthOf ownerSlot) hOwnLt Bcut hBackB s5 hpc5 hMeta5
        h2_5 h3_5 hBoundMeta (by rw [hd5']; exact hDepth ⟨ownerSlot, hOwnLt⟩)
    have hPlClear : Placed code (basePc + 49) (clearWordsInstrs (bits := bits) reg5 30 6 (by omega)) :=
      Placed_window hAccumulator 4 rfl
    obtain ⟨s31, hClearTrace, hpc31, hZero31, hFrClear, hReg31⟩ :=
      clearValues_run (input := input) (tmp := reg5) (by decide) (by decide)
        (basePc + 49) 30 metaBase (by omega) hPlClear (by omega) s25 hpc25 hM_25 h0_25
    have hM_31 : (reg s31 rMeta).val = metaBase := by rw [hReg31 rMeta (by decide), hM_25]
    have h2_31 : (reg s31 reg2).val = y.val := by rw [hReg31 reg2 (by decide), h2_25]
    have h1_31 : (reg s31 reg1).val = 1 := by rw [hReg31 reg1 (by decide), h1_25]
    have h0_31 : (reg s31 reg0).val = 0 := by rw [hReg31 reg0 (by decide), h0_25]
    have hData31 : ∀ j, j ≠ metaBase + mIdxCurOwner →
        (j < metaBase + 30 ∨ (metaBase + 36 ≤ j ∧ j < metaBase + 48) ∨ metaBase + 53 ≤ j) →
        s31.data[j]? = st.data[j]? := by
      intro j hOwner hj
      obtain ⟨hClear, h48, h49, h50, h51, h52⟩ := owner_frame hj
      rw [hFrClear j hClear, hFrOwner j hOwner h48 h49 h50 h51 h52, hd5']
    have hBelow31 : ∀ j, j < metaBase → s31.data[j]? = st.data[j]? := by
      intro j hj
      exact hData31 j (by dsimp only [mIdxCurOwner]; omega) (Or.inl (by omega))
    have hStartBelow (i : Nat) (hi : i ≤ n) : inStartArrBase n N + i < metaBase := by
      unfold metaBase metaArrBase inArcIdArrBase
      omega
    -- Step 67..79: read `inStart[y]` and `inStart[y+1]`, store `mIdxArcPtr`, `mIdxArcEnd`:
    have hPlIS : Placed code (basePc + 67) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxInStartBase (by dsimp only [mIdxInStartBase]; omega)) :=
      Placed_window hArcs 0 rfl
    obtain ⟨s32, hs32, hpc32, hd32, h4_32, hPres32⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlIS (by omega) hpc31 hM_31 (hOffsetFit mIdxInStartBase (by decide))
      (by rw [hData31 _ (by dsimp only [mIdxInStartBase, mIdxCurOwner]; omega) (Or.inl (by dsimp only [mIdxInStartBase]; omega))]
          exact hMeta.meta_inStartBase)
    have h2_32 : (reg s32 reg2).val = y.val := by rw [hPres32 reg2 (by intro h; cases h) (by intro h; cases h), h2_31]
    have haAIS : code[s32.pc]? = some (.add reg4 reg4 reg2) := by rw [hpc32]; exact hArcs 3 _ rfl
    obtain ⟨s33, hs33Raw, hpc33, h4_33, ho33, hd33⟩ := step_add_at (input := input) haAIS (by omega)
    have hs33 := steps_1_of_step hs33Raw
    have h4Val33 : (reg s33 reg4).val = inStartArrBase n N + y.val := by
      rw [h4_33, add_no_wrap _ _ (by rw [h4_32, h2_32]; dsimp only [inStartArrBase, trigNextArrBase, trigHeadArrBase, topoRankArrBase, orderArrBase, priorBase, storedBase]; omega), h4_32, h2_32]
    obtain ⟨wis0, hwis0, hwis0V⟩ := Option.map_eq_some_iff.mp (hInStart y.val (Nat.le_of_lt y.isLt))
    have haLIS0 : code[s33.pc]? = some (.loadData reg5 reg4) := by rw [hpc33, hpc32]; exact hArcs 4 _ rfl
    obtain ⟨s34, hs34Raw, hpc34, h5_34, ho34, hd34⟩ := step_loadData_at (input := input) haLIS0 (by omega)
      (by rw [h4Val33, hd33, hd32, hBelow31 _ (hStartBelow y.val (Nat.le_of_lt y.isLt))]
          exact hwis0)
    have hs34 := steps_1_of_step hs34Raw
    have hM_34 : (reg s34 rMeta).val = metaBase := by
      rw [ho34 rMeta (by intro h; cases h), ho33 rMeta (by intro h; cases h),
        hPres32 rMeta (by intro h; cases h) (by intro h; cases h), hM_31]
    have hPlSAP : Placed code (basePc + 72) (metaStoreInstrs (bits := bits) reg5 reg6 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega)) :=
      Placed_window hArcs 5 rfl
    obtain ⟨s35, hs35, hpc35, hAt35, hFr35, hPres35⟩ := run_metaStore_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlSAP (by omega) (by rw [hpc34, hpc33, hpc32])
      hM_34 (hOffsetFit mIdxArcPtr (by decide)) (lt_data_size (hOffsetLt mIdxArcPtr (by decide)))
    have h4_35 : (reg s35 reg4).val = inStartArrBase n N + y.val := by
      rw [hPres35 reg4 (by intro h; cases h), ho34 reg4 (by intro h; cases h), h4Val33]
    have h1_35 : (reg s35 reg1).val = 1 := by
      rw [hPres35 reg1 (by intro h; cases h), ho34 reg1 (by intro h; cases h), ho33 reg1 (by intro h; cases h),
        hPres32 reg1 (by intro h; cases h) (by intro h; cases h), h1_31]
    have haAIS1 : code[s35.pc]? = some (.add reg4 reg4 reg1) := by rw [hpc35]; exact hArcs 8 _ rfl
    obtain ⟨s36, hs36Raw, hpc36, h4_36, ho36, hd36⟩ := step_add_at (input := input) haAIS1 (by omega)
    have hs36 := steps_1_of_step hs36Raw
    have h4Val36 : (reg s36 reg4).val = inStartArrBase n N + (y.val + 1) := by
      rw [h4_36, add_no_wrap _ _ (by rw [h4_35, h1_35]; dsimp only [inStartArrBase, trigNextArrBase, trigHeadArrBase, topoRankArrBase, orderArrBase, priorBase, storedBase]; omega), h4_35, h1_35]
      omega
    obtain ⟨wis1, hwis1, hwis1V⟩ := Option.map_eq_some_iff.mp (hInStart (y.val + 1) y.isLt)
    have haLIS1 : code[s36.pc]? = some (.loadData reg5 reg4) := by rw [hpc36, hpc35]; exact hArcs 9 _ rfl
    obtain ⟨s37, hs37Raw, hpc37, h5_37, ho37, hd37⟩ := step_loadData_at (input := input) haLIS1 (by omega)
      (by
        have hLow := hStartBelow (y.val + 1) y.isLt
        rw [h4Val36, hd36, hFr35 (inStartArrBase n N + (y.val + 1)) (by dsimp only [mIdxArcPtr]; omega),
          hd34, hd33, hd32, hBelow31 _ hLow]
        exact hwis1)
    have hs37 := steps_1_of_step hs37Raw
    have hM_37 : (reg s37 rMeta).val = metaBase := by
      rw [ho37 rMeta (by intro h; cases h), ho36 rMeta (by intro h; cases h),
        hPres35 rMeta (by intro h; cases h), hM_34]
    have hPlSAE : Placed code (basePc + 77) (metaStoreInstrs (bits := bits) reg5 reg6 mIdxArcEnd (by dsimp only [mIdxArcEnd]; omega)) :=
      Placed_window hArcs 10 rfl
    obtain ⟨s38, hs38, hpc38, hAt38, hFr38, hPres38⟩ := run_metaStore_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlSAE (by omega) (by rw [hpc37, hpc36, hpc35])
      hM_37 (hOffsetFit mIdxArcEnd (by decide)) (lt_data_size (hOffsetLt mIdxArcEnd (by decide)))
    have hM_38 : (reg s38 rMeta).val = metaBase := by rw [hPres38 rMeta (by intro h; cases h), hM_37]
    have h0_38 : (reg s38 reg0).val = 0 := by
      rw [hPres38 reg0 (by intro h; cases h), ho37 reg0 (by intro h; cases h), ho36 reg0 (by intro h; cases h),
        hPres35 reg0 (by intro h; cases h), ho34 reg0 (by intro h; cases h), ho33 reg0 (by intro h; cases h),
        hPres32 reg0 (by intro h; cases h) (by intro h; cases h), h0_31]
    have h1_38 : (reg s38 reg1).val = 1 := by
      rw [hPres38 reg1 (by intro h; cases h), ho37 reg1 (by intro h; cases h), ho36 reg1 (by intro h; cases h), h1_35]
    have hData38 : ∀ j, j ≠ metaBase + mIdxCurOwner → j ≠ metaBase + mIdxArcPtr → j ≠ metaBase + mIdxArcEnd →
        (j < metaBase + 30 ∨ (metaBase + 36 ≤ j ∧ j < metaBase + 48) ∨ metaBase + 53 ≤ j) →
        s38.data[j]? = st.data[j]? := fun j h0 h1 h2 hj => by
      rw [hFr38 j h2, hd37, hd36, hFr35 j h1, hd34, hd33, hd32, hData31 j h0 hj]
    have hArcsFr : ∀ j, j ≠ metaBase + mIdxArcEnd → j ≠ metaBase + mIdxArcPtr →
        s38.data[j]? = s31.data[j]? := by
      intro j hEnd hPtr
      rw [hFr38 j hEnd, hd37, hd36, hFr35 j hPtr, hd34, hd33, hd32]
    have hZero38 : ValuesWordsAt s38.data (metaBase + mIdxAcc0) zero :=
      valuesWordsAt_frame (fun i hi =>
        hArcsFr (metaBase + 30 + i) (by dsimp only [mIdxArcEnd]; omega)
          (by dsimp only [mIdxArcPtr]; omega)) hZero31
    have hBelow38 : ∀ j, j < metaBase → s38.data[j]? = st.data[j]? := by
      intro j hj
      exact hData38 j (by dsimp only [mIdxCurOwner]; omega)
        (by dsimp only [mIdxArcPtr]; omega) (by dsimp only [mIdxArcEnd]; omega) (Or.inl (by omega))
    have hInStartY : prefixIn H y.val + degIn H y.val = prefixIn H (y.val + 1) := rfl
    have hEndLe : prefixIn H (y.val + 1) ≤ m := by
      change prefixIn H (y.val + 1) ≤ H.arcCount
      rw [← prefixIn_vertexCount H]
      exact prefixIn_mono H y.isLt
    have hLoopBases : ∀ q : Fin H.vertexCount, q.val < H.vertexCount →
        ValuesWordsAt s38.data (priorBase N + 6 * q.val) (C.built.model.wantBase q) ∨
          ¬ (∃ e ∈ (inArcsPrefix H m y.val).drop 0, ∃ he : e < m, (rawOccurrence H ⟨e, he⟩).1 = q) := by
      intro q hqLt
      by_cases hMem : ∃ e ∈ (inArcsPrefix H m y.val).drop 0, ∃ he : e < m, (rawOccurrence H ⟨e, he⟩).1 = q
      · left
        obtain ⟨e, heDrop, heLt, hOcc⟩ := hMem
        rw [List.drop_zero] at heDrop
        have hHd : rawHead H ⟨e, heLt⟩ = y := incomingArc_head heDrop _
        have hArcH : H.HasQuotientArc q y :=
          (rawOccurrence_membership H q y).mp ⟨⟨e, heLt⟩, hOcc, hHd⟩
        have hRkQ : rankKahn q < rankKahn y := rankArcKahn q y hArcH
        have hPriorQ := hPriorPred q hRkQ
        exact valuesWordsAt_frame (fun i hi => hBelow38 (priorBase N + 6 * q.val + i)
          (by unfold priorBase; omega)) hPriorQ
      · exact Or.inr hMem
    have hLoopLives : ∀ e ∈ (inArcsPrefix H m y.val).drop 0, ∃ he : e < m,
        let u := (rawOccurrence H ⟨e, he⟩).1
        let v := (selectors (orderedConfig p large) r.out).label u
        let hvLt : v < r.out.tables.next := B.G.size_eq ▸ B.E.label_lt u True.intro
        u.val ≠ Bcut.fst.val → u.val ≠ Bcut.snd.val → 0 < v →
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) ≤
          r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) →
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) <
          r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) →
        live v := by
      intro e heDrop
      rw [List.drop_zero] at heDrop
      have heLt : e < m := inArcsPrefix_lt H H.arcCount y.val e heDrop
      have hHd : rawHead H ⟨e, heLt⟩ = y := incomingArc_head heDrop _
      refine ⟨heLt, fun _ _ hvPos hEn hSt => ?_⟩
      let u := (rawOccurrence H ⟨e, heLt⟩).1
      let v := (selectors (orderedConfig p large) r.out).label u
      have hArcH : H.HasQuotientArc u y :=
        (rawOccurrence_membership H u y).mp ⟨⟨e, heLt⟩, rfl, hHd⟩
      have hRkU : rankKahn u < rankKahn y := rankArcKahn u y hArcH
      obtain ⟨Au, hOwnU, hBackU, _, _⟩ :=
        owner_eq_some_of_label_pos flat increasing covers rankArc r entryRank u hvPos
      have hTrU : max (rankKahn Au.fst) (rankKahn Au.snd) < rankKahn y :=
        Nat.lt_trans (trigger_lt_properLoss flat rankKahn rankArcKahn
          ((actualModel B entryRank rankArc flat).ownerProper u Au hOwnU)) hRkU
      exact hLiveBefore v ⟨B.G.size_eq ▸ B.E.label_lt u True.intro, Or.inr (Or.inr ⟨Au, hBackU, hTrU⟩)⟩
    have hOwnerFr : ∀ j, metaBase + 48 ≤ j → j < metaBase + 53 →
        s38.data[j]? = s25.data[j]? := by
      intro j hlo hhi
      rw [hArcsFr j (by dsimp only [mIdxArcEnd]; omega) (by dsimp only [mIdxArcPtr]; omega)]
      exact hFrClear j (Or.inr (by omega))
    have h48_38 : (s38.data[metaBase + 48]?).map Fin.val = some Bcut.fst.val := by
      rw [hOwnerFr _ (by omega) (by omega)]
      exact hOwnerFst
    have h49_38 : (s38.data[metaBase + 49]?).map Fin.val = some Bcut.snd.val := by
      rw [hOwnerFr _ (by omega) (by omega)]
      exact hOwnerSnd
    have h50_38 : (s38.data[metaBase + 50]?).map Fin.val =
        some (r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) := by
      rw [hOwnerFr _ (by omega) (by omega)]
      exact hOwnerEntry
    have h51_38 : (s38.data[metaBase + 51]?).map Fin.val =
        some (r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) := by
      rw [hOwnerFr _ (by omega) (by omega)]
      exact hOwnerStop
    have h52_38 : (s38.data[metaBase + 52]?).map Fin.val = some (B.F.depthOf ownerSlot) := by
      rw [hOwnerFr _ (by omega) (by omega)]
      exact hOwnerDepth
    have hFrameMeta (off : Nat) (hOff : off < 22) :
        s38.data[metaBase + off]? = st.data[metaBase + off]? :=
      hData38 (metaBase + off) (by dsimp only [mIdxCurOwner]; omega)
        (by dsimp only [mIdxArcPtr]; omega) (by dsimp only [mIdxArcEnd]; omega) (Or.inl (by omega))
    have hPtr38 : (s38.data[metaBase + mIdxArcPtr]?).map Fin.val = some (prefixIn H y.val) := by
      rw [hFr38 (metaBase + mIdxArcPtr) (by dsimp only [mIdxArcPtr, mIdxArcEnd]; omega),
        hd37, hd36, hAt35, Option.map_some, h5_34, hwis0V]
    have hArcBelow (k : Fin (degIn H y.val)) :
        inArcIdArrBase n N + (prefixIn H y.val + k.val) < metaBase := by
      have := k.isLt
      change _ < inArcIdArrBase n N + m
      omega
    obtain ⟨kL, s39, hkL, hs39, hpc39, hMeta39, hAcc39, hFr39⟩ := step4A_loop_spec (input := input)
      (basePc + 80) h100 hPlLoop (by omega) flat increasing covers rankArc hIn hWork hFitRank
      ok (B.G.size_eq) (B := B) rfl y ownerSlot hOwnPos hOwnLt Bcut C.built.model.wantBase hInStartY hEndLe
      (degIn H y.val) 0 zero s38 (Nat.zero_add _) hpc38
      (hMeta.preserve hM_38 h0_38 h1_38 hFrameMeta)
      (by simpa only [Nat.add_zero] using hPtr38)
      (by rw [hAt38, Option.map_some, h5_37, hwis1V])
      h48_38 h49_38 h50_38 h51_38 h52_38 hZero38 hLoopBases
      (fun k => by rw [hBelow38 _ (hArcBelow k)]; exact hInArcs y.val y.isLt k)
      (fun w => by rw [hBelow38 w.val (by have := w.isLt; omega)]; exact hDepth w)
      (fun w hwL => by
        have hEq18 : ∀ i < 18, s38.data[storedBase N + 18 * w.val + i]? =
            st.data[storedBase N + 18 * w.val + i]? := fun i hi =>
          hBelow38 _ (by have := w.isLt; unfold storedBase; omega)
        have ho := hStored w hwL
        have hp := hEq18 0 (by decide)
        rw [Nat.add_zero] at hp
        refine ⟨by rw [hp]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
          mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hEq18 (2 + i) (by omega)) ho.2.2.1,
          mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hEq18 (10 + i) (by omega)) ho.2.2.2⟩)
      hLoopLives
    change ∀ j, (j < metaBase + mIdxArcPtr ∨
      (metaBase + 48 ≤ j ∧ j < metaBase + 53) ∨ metaBase + 55 ≤ j) →
      s39.data[j]? = s38.data[j]? at hFr39
    rw [List.drop_zero] at hAcc39
    have hWantYEq : (inArcsPrefix H m y.val).foldl
        (ramArcStep r entryRank B.F ref ownerSlot (B.F.depthOf ownerSlot) Bcut C.built.model.wantBase) zero =
        C.built.model.wantBase y :=
      wantBase_eq_ramArcStep_foldl flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout rankKahn rankArcKahn y
        hOwnPos rfl hNodeB
        (fun u hu => hRefLive u (hLiveBefore u hu))
        (fun _ _ => rfl)
    rw [hWantYEq] at hAcc39
    have hPriorY : priorBase N + 6 * y.val + 6 ≤ metaBase := by
      have := y.isLt
      unfold priorBase
      omega
    have hCurY39 : (s39.data[metaBase + mIdxCurY]?).map Fin.val = some y.val := by
      rw [hFr39 (metaBase + mIdxCurY) (Or.inl (by dsimp only [mIdxCurY, mIdxArcPtr]; omega)),
        hData38 (metaBase + mIdxCurY) (by dsimp only [mIdxCurY, mIdxCurOwner]; omega)
          (by dsimp only [mIdxCurY, mIdxArcPtr]; omega) (by dsimp only [mIdxCurY, mIdxArcEnd]; omega)
          (Or.inl (by dsimp only [mIdxCurY]; omega))]
      exact hCurY
    obtain ⟨t, hStepsWrite, hpct, h0T, h1T, hMT, hValsT, hFrT⟩ :=
      step4A_writePrior_spec (input := input) (basePc + 486) n m N nGlobal y.val h100
        hPlWrite (by omega) hBoundMeta hPriorY s39 hpc39 hMeta39 hCurY39
        (C.built.model.wantBase y) hAcc39
    have hFrAll : ∀ j, (j < priorBase N + 6 * y.val ∨
        (priorBase N + 6 * y.val + 6 ≤ j ∧ j < metaBase + mIdxCurOwner) ∨
        metaBase + 55 ≤ j) → t.data[j]? = st.data[j]? := by
      intro j hj
      obtain ⟨hD, hLoop, hOwner, hPtr, hEnd, hSetup⟩ := writePrior_frame hPriorY hj
      rw [hFrT j hD, hFr39 j hLoop, hData38 j hOwner hPtr hEnd hSetup]
    have hHead : Steps code input 9 st s5 :=
      hs1.append (hs2.append (hs3.append (hs4.append hs5)))
    have hArcOffsets : Steps code input 13 s31 s38 :=
      hs32.append (hs33.append (hs34.append (hs35.append (hs36.append (hs37.append hs38)))))
    have hStepsSetup : Steps code input 80 st s38 :=
      hHead.append (hOwnerTrace.append (hClearTrace.append hArcOffsets))
    have hMulAdd : 700 * (degIn H y.val + 1) * OracleContract.L H.vertexCount =
        700 * degIn H y.val * OracleContract.L H.vertexCount + 700 * OracleContract.L H.vertexCount := by
      rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
    refine ⟨80 + kL + 34, t, by omega, (hStepsSetup.append hs39).append hStepsWrite, hpct,
      hMeta.preserve hMT h0T h1T ?_, hValsT, hFrAll⟩
    intro i hi
    apply hFrAll (metaBase + i) (Or.inr (Or.inl ⟨?_, ?_⟩))
    · exact Nat.le_trans hPriorY (Nat.le_add_right _ _)
    · exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hi (by decide : 22 ≤ mIdxCurOwner)) _
  · rw [ite_eq_right (by rw [h0_4, hOwnVal]; exact hOwnPos)] at hpc5
    have hOwn0 : ownerSlot = 0 := by omega
    have hOwnW : (actualModel B entryRank rankArc flat).owner y = none :=
      owner_eq_none_of_label_zero flat increasing covers rankArc r entryRank y hOwn0
    have hWant0 : C.built.model.wantBase y = zero := by
      rw [hMod]; unfold BuiltExit.Model.wantBase; rw [hOwnW]
    have hd5' : s5.data = st.data := by rw [hd5, hd4']
    have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
    have hPos : 1 ≤ (degIn H y.val + 1) * OracleContract.L H.vertexCount :=
      Nat.mul_pos (Nat.succ_pos _) hLGe1
    have h700 : 700 ≤ 700 * ((degIn H y.val + 1) * OracleContract.L H.vertexCount) := by
      simpa using Nat.mul_le_mul_left 700 hPos
    refine ⟨9, s5, by rw [Nat.mul_assoc]; omega, (hs1.append hs2).append (hs3.append (hs4.append hs5)), hpc5,
      hMeta.preserve (by rw [hr5F, hM_4]) (by rw [hr5F, h0_4]) (by rw [hr5F, h1_4]) (fun i hi => by rw [hd5']),
      by rw [hWant0, hd5']; exact hPriorSelf, fun _ _ => by rw [hd5']⟩

end PaperB.RamProgram.ExitSummaryBuild
