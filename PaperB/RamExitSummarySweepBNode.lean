module

public import PaperB.RamExitSummarySweepBParent
public import PaperB.RamExitSummarySweepBJump

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

/-! Correctness and operation count for one complete map update. -/

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

theorem run_step4BOneNode {code : Program DomL} {input : Input DomL}
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
    (idx : Nat) (w : Nat) (hwPos : 0 < w) (hwLt : w < r.out.tables.next)
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
    ∃ k t, k ≤ 1600 * OracleContract.L H.vertexCount ∧
      Steps code input k st t ∧ t.pc = basePc + 1039 ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (t.data[storedBase r.out.tables.next + 18 * w]?).map Fin.val = some (C.built.ref w).parent ∧
      (t.data[storedBase r.out.tables.next + 18 * w + 1]?).map Fin.val = some (C.built.ref w).jump ∧
      MapWordsAt t.data (storedBase r.out.tables.next + 18 * w + 2) (C.built.ref w).parentMap ∧
      MapWordsAt t.data (storedBase r.out.tables.next + 18 * w + 10) (C.built.ref w).jumpMap ∧
      (∀ j, (j < storedBase r.out.tables.next + 18 * w + 2 ∨
          (storedBase r.out.tables.next + 18 * w + 18 ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEvalU) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 64 ≤ j) →
        t.data[j]? = st.data[j]?) := by
  intro C B hParPos ok hRefLive st hpc hMeta hCur hParW hJumpW hDepth hStored hPrior
  let N := r.out.tables.next
  let metaBase := metaArrBase H.vertexCount H.arcCount N
  obtain ⟨_, i, k1, s1, hk1, hs1, hpc1, _, hSlotW, _, _,
      hLiveP, hMeta1, hPM1, h48_1, h49_1, h55_1, hFr1⟩ :=
    step4B_parentMap_spec (input := input) basePc h100 hPl hSz flat increasing covers rankArc hIn hWork
      hLayout rankArcKahn idx w hwLt Pc hBackW hTrW ref hParPos ok hRefLive st hpc hMeta hCur hParW hJumpW
      hDepth hStored hPrior
  change ∀ j, (j < storedBase N + 18 * w + 2 ∨
    (storedBase N + 18 * w + 10 ≤ j ∧ j < metaBase + mIdxEvalU) ∨ metaBase + 56 ≤ j) →
      s1.data[j]? = st.data[j]? at hFr1
  have hMetaEq : metaBase = 20 * N + 10 * H.vertexCount + H.arcCount + 1 := metaArrBase_eq _ _ _
  have hRecordLimit : storedBase N + 18 * N ≤ metaBase := by unfold storedBase; omega
  have hRecordEnd : storedBase N + 18 * w + 18 ≤ metaBase := by omega
  have hStored1 : ∀ u : Fin N, liveBefore flat increasing covers rankArc r rankKahn idx u.val →
      (s1.data[storedBase N + 18 * u.val]?).map Fin.val = some (ref u.val).parent ∧
      (s1.data[storedBase N + 18 * u.val + 1]?).map Fin.val = some (ref u.val).jump ∧
      MapWordsAt s1.data (storedBase N + 18 * u.val + 2) (ref u.val).parentMap ∧
      MapWordsAt s1.data (storedBase N + 18 * u.val + 10) (ref u.val).jumpMap := by
    intro u huL
    have huNeW : u.val ≠ w := by
      intro heq; subst heq
      rcases huL.2 with hz | hpz | ⟨P0, hP0, hM0⟩
      · omega
      · exact Nat.ne_of_gt hParPos hpz
      · rw [Option.some.inj (Option.some.inj (hP0.symm.trans hBackW))] at hM0
        omega
    have hEq18 : ∀ k < 18, s1.data[storedBase N + 18 * u.val + k]? = st.data[storedBase N + 18 * u.val + k]? := fun k hk => by
      by_cases hLtW : u.val < w
      · exact hFr1 (storedBase N + 18 * u.val + k) (Or.inl (by omega))
      · have hGtW : w < u.val := by omega
        exact hFr1 (storedBase N + 18 * u.val + k) (Or.inr (Or.inl
          ⟨by omega, by have := u.isLt; omega⟩))
    have ho := hStored u huL
    have h0 := hEq18 0 (by decide)
    simp only [Nat.add_zero] at h0
    refine ⟨by rw [h0]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
      mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (2 + k) (by omega)) ho.2.2.1,
      mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (10 + k) (by omega)) ho.2.2.2⟩
  have hLiveAJ := ok.jump_live (B.F.parentOf w) hLiveP
  have haJLt : B.F.jumpOf (B.F.parentOf w) < N := hLiveAJ.1
  have hJumpAnc := hStored1 ⟨_, haJLt⟩ hLiveAJ
  have hJumpParent := hStored1 ⟨_, hLiveP.1⟩ hLiveP
  have hJumpAddress : (s1.data[storedBase N + 18 * B.F.parentOf w + 1]?).map Fin.val =
      some (B.F.jumpOf (B.F.parentOf w)) := by
    rw [← ok.jump_eq _ hLiveP]
    exact hJumpParent.2.1
  have hMetaLt : metaBase + 64 ≤ workCap := by
    have hNLe : N ≤ H.vertexCount + 1 := (B_next_pos flat increasing covers rankArc r).2
    unfold exitWorkCap at hWork
    omega
  obtain ⟨k2, t, hk2, hs2, hpct, hMetaT, hJMT, hFr2⟩ :=
    step4B_jumpMap_spec (input := input) basePc h100 hPl hSz H.vertexCount H.arcCount N nGlobal
      w (B.F.parentOf w) (B.F.jumpOf w) (B.F.jumpOf (B.F.parentOf w)) hwLt hLiveP.1 haJLt hMetaLt
      (C.built.model.wantMap i) (ref (B.F.parentOf w)).jumpMap (ref (B.F.jumpOf (B.F.parentOf w))).jumpMap
      s1 hpc1 hMeta1 h48_1 h49_1 h55_1 hPM1 hJumpAddress hJumpParent.2.2.2 hJumpAnc.2.2.2
  change ∀ j, (j < storedBase N + 18 * w + 10 ∨
    (storedBase N + 18 * w + 18 ≤ j ∧ j < metaBase + 56) ∨ metaBase + 64 ≤ j) →
      t.data[j]? = s1.data[j]? at hFr2
  have hFrAll : ∀ j, (j < storedBase N + 18 * w + 2 ∨
      (storedBase N + 18 * w + 18 ≤ j ∧ j < metaBase + mIdxEvalU) ∨
      metaBase + 64 ≤ j) → t.data[j]? = st.data[j]? := fun j hj => by
    rw [hFr2 j (by dsimp only [mIdxEvalU] at hj; rcases hj with h | ⟨h1, h2⟩ | h <;> omega)]
    exact hFr1 j (by rcases hj with h | ⟨h1, h2⟩ | h <;> omega)
  have hwLiveC : C.built.live w := C.built.all_live w (B.G.size_eq.symm ▸ hwLt)
  have hParEqC : (C.built.ref w).parent = B.F.parentOf w := C.built.liveOK.parent_eq w hwLiveC
  have hJumpEqC : (C.built.ref w).jump = B.F.jumpOf w := C.built.liveOK.jump_eq w hwLiveC
  have hPMEqC : (C.built.ref w).parentMap = C.built.model.wantMap i := by
    rw [← hSlotW]; exact C.built.edges.parentMap i True.intro
  have hJMEqC : (C.built.ref w).jumpMap =
      if B.F.jumpOf w = B.F.parentOf w then C.built.model.wantMap i
      else Map.compose (C.built.model.wantMap i)
        (Map.compose (ref (B.F.parentOf w)).jumpMap (ref (B.F.jumpOf (B.F.parentOf w))).jumpMap) := by
    let pN := B.F.parentOf w
    have hLiveAJ := ok.jump_live pN hLiveP
    have haJLt : B.F.jumpOf pN < B.F.size := ok.live_lt _ hLiveAJ
    have hEqP : ref pN = C.built.ref pN := hRefLive pN hLiveP
    have hEqAJ : ref (B.F.jumpOf pN) = C.built.ref (B.F.jumpOf pN) := hRefLive _ hLiveAJ
    have hLivePC : C.built.live pN := C.built.all_live pN (B.G.size_eq.symm ▸ hLiveP.1)
    have hLiveAJC : C.built.live (B.F.jumpOf pN) := C.built.all_live _ haJLt
    have hDown : B.F.depthOf (C.built.ref w).parent < B.F.depthOf w := by
      rw [← hSlotW, C.built.edges.parent i True.intro]
      exact C.built.edges.down i True.intro
    have hPathC : ParentPath C.built.ref B.F.depthOf w (B.F.jumpOf w) (C.built.ref w).jumpMap := by
      have hp : JumpOK C.built.ref B.F.depthOf w := C.built.liveOK.hops.jump_path w hwLiveC
      unfold JumpOK at hp
      rwa [hJumpEqC] at hp
    by_cases hEqJP : B.F.jumpOf w = pN
    · rw [ite_eq_left hEqJP]
      have hPathPO : ParentPath C.built.ref B.F.depthOf w pN (C.built.model.wantMap i) := by
        have hp : ParentPath C.built.ref B.F.depthOf w (C.built.ref w).parent (C.built.ref w).parentMap :=
          C.built.liveOK.hops.parent_path w hwLiveC
        rwa [hParEqC, hPMEqC] at hp
      exact ParentPath.unique (by rwa [hEqJP] at hPathC) hPathPO
    · rw [ite_eq_right hEqJP]
      have hSkew := validJumpForest_skew_rule B.G.layout.valid w hwPos (B.G.size_eq.symm ▸ hwLt)
      change B.F.jumpOf w = if 0 < B.F.depthOf pN - B.F.depthOf (B.F.jumpOf pN) ∧
          B.F.depthOf pN - B.F.depthOf (B.F.jumpOf pN) =
            B.F.depthOf (B.F.jumpOf pN) - B.F.depthOf (B.F.jumpOf (B.F.jumpOf pN))
        then B.F.jumpOf (B.F.jumpOf pN) else pN at hSkew
      have hCond : 0 < B.F.depthOf pN - B.F.depthOf (B.F.jumpOf pN) ∧
          B.F.depthOf pN - B.F.depthOf (B.F.jumpOf pN) =
            B.F.depthOf (B.F.jumpOf pN) - B.F.depthOf (B.F.jumpOf (B.F.jumpOf pN)) := by
        refine Classical.byContradiction fun hNot => ?_
        rw [ite_eq_right hNot] at hSkew
        exact hEqJP hSkew
      rw [ite_eq_left hCond] at hSkew
      have hPathP : ParentPath C.built.ref B.F.depthOf pN (B.F.jumpOf pN) (C.built.ref pN).jumpMap := by
        have hp : JumpOK C.built.ref B.F.depthOf pN := C.built.liveOK.hops.jump_path pN hLivePC
        have he : (C.built.ref pN).jump = B.F.jumpOf pN := C.built.liveOK.jump_eq pN hLivePC
        unfold JumpOK at hp
        rwa [he] at hp
      have hPathAJ : ParentPath C.built.ref B.F.depthOf (B.F.jumpOf pN) (B.F.jumpOf (B.F.jumpOf pN))
          (C.built.ref (B.F.jumpOf pN)).jumpMap := by
        have hp : JumpOK C.built.ref B.F.depthOf (B.F.jumpOf pN) := C.built.liveOK.hops.jump_path (B.F.jumpOf pN) hLiveAJC
        have he : (C.built.ref (B.F.jumpOf pN)).jump = B.F.jumpOf (B.F.jumpOf pN) := C.built.liveOK.jump_eq (B.F.jumpOf pN) hLiveAJC
        unfold JumpOK at hp
        rwa [he] at hp
      have hPathComb := ParentPath.cons w hDown
        (by simpa only [hParEqC] using ParentPath.append hPathP hPathAJ)
      rw [hPMEqC, ← hSkew] at hPathComb
      change _ = Map.compose (C.built.model.wantMap i) (Map.compose (ref pN).jumpMap (ref (B.F.jumpOf pN)).jumpMap)
      rw [hEqP, hEqAJ]
      exact ParentPath.unique hPathC hPathComb
  have hPMT : MapWordsAt t.data (storedBase N + 18 * w + 2) (C.built.ref w).parentMap := by
    rw [hPMEqC]
    exact mapWordsAt_frame (fun k hk => hFr2 _ (Or.inl (by omega))) hPM1
  have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
  refine ⟨k1 + k2, t, by omega, hs1.append hs2, hpct, hMetaT,
    by rw [hParEqC, hFrAll (storedBase N + 18 * w) (Or.inl (by omega))]; exact hParW,
    by rw [hJumpEqC, hFrAll (storedBase N + 18 * w + 1) (Or.inl (by omega))]; exact hJumpW,
    hPMT, by rw [hJMEqC]; exact hJMT, hFrAll⟩

end PaperB.RamProgram.ExitSummaryBuild
