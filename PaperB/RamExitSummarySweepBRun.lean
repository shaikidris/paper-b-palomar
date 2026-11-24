module

public import PaperB.RamExitSummarySweepBNode

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3400000
set_option maxRecDepth 4096

/-! Traversal and accounting for a trigger bucket. -/

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

private theorem step4B_bucketLoop_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4BInstrs (bits := bits) basePc h100))
    (hSz : basePc + 1069 < code.size)
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
    (idx : Nat) (buckets : List Nat) (hNodup : buckets.Nodup)
    (hSpec : ∀ w ∈ buckets, w < r.out.tables.next ∧
      0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w ∧
      ∃ Pc : CutPair H, r.out.tables.back[w]? = some (some Pc) ∧
        max (rankKahn Pc.fst) (rankKahn Pc.snd) = idx)
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∀ (hOK0 : LiveStoreOK B.F C.built.ref (liveBefore flat increasing covers rankArc r rankKahn idx))
    (remNodes : List Nat) (done : List Nat) (hd : Nat) (st : State DomL),
      done ++ remNodes = buckets →
      st.pc = basePc + 11 →
      MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCCursor]?).map Fin.val = some hd →
      ListLinked st.data (trigNextArrBase H.vertexCount r.out.tables.next) r.out.tables.next hd remNodes →
      (∀ u : Fin r.out.tables.next, (st.data[u.val]?).map Fin.val = some (B.F.depthOf u.val)) →
      (∀ u : Fin r.out.tables.next,
        (liveBefore flat increasing covers rankArc r rankKahn idx u.val ∨ u.val ∈ done) →
        (st.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (st.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap) →
      (∀ w ∈ remNodes,
        (st.data[storedBase r.out.tables.next + 18 * w]?).map Fin.val = some (B.F.parentOf w) ∧
        (st.data[storedBase r.out.tables.next + 18 * w + 1]?).map Fin.val = some (B.F.jumpOf w)) →
      (∀ q : Fin H.vertexCount, rankKahn q ≤ idx →
        ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q)) →
      ∃ k t, k ≤ 1620 * remNodes.length * OracleContract.L H.vertexCount + 7 ∧
        Steps code input k st t ∧ t.pc = basePc + 1069 ∧
        MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
        (∀ u : Fin r.out.tables.next,
          (liveBefore flat increasing covers rankArc r rankKahn idx u.val ∨ u.val ∈ buckets) →
          (t.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
          (t.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
          MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
          MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap) ∧
        (∀ j, (j < storedBase r.out.tables.next ∨
            (priorBase r.out.tables.next ≤ j ∧
              j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCCursor) ∨
            metaArrBase H.vertexCount H.arcCount r.out.tables.next + 64 ≤ j) →
          t.data[j]? = st.data[j]?) ∧
        (∀ x < r.out.tables.next, ∀ k < 2,
          t.data[storedBase r.out.tables.next + 18 * x + k]? =
            st.data[storedBase r.out.tables.next + 18 * x + k]?) := by
  intro C B hOK0 remNodes
  induction remNodes with
  | nil =>
    intro done hd st hApp hpc hMeta hCur hLk hDep hSt hRemPJ hPrior
    have hHdEq : hd = r.out.tables.next := by cases hLk; rfl
    have hDoneEq : done = buckets := by simpa using hApp
    subst hDoneEq
    let N := r.out.tables.next
    let metaBase := metaArrBase H.vertexCount H.arcCount N
    have hNLe : N ≤ H.vertexCount + 1 := (B_next_pos flat increasing covers rankArc r).2
    have hMetaEq : metaBase = 20 * N + 10 * H.vertexCount + H.arcCount + 1 := metaArrBase_eq _ _ _
    have hBoundMeta : metaBase + 64 ≤ workCap := by
      dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
    have hWorkFit : workCap ≤ 2 ^ bits := hw
    have hOffsetFit (off : Nat) (hoff : off < 64) : metaBase + off < 2 ^ bits := by omega
    have hPlC : Placed code (basePc + 11) (metaLoadInstrs (bits := bits) reg2 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega)) := by
      exact Placed_window hPl 11 rfl
    obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlC (by omega) hpc hMeta.rMeta_eq (hOffsetFit mIdxCCursor (by decide))
      (by rw [hHdEq] at hCur; exact hCur)
    have hM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hMeta.rMeta_eq]
    have hPlNH : Placed code (basePc + 14) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxNH (by dsimp only [mIdxNH]; omega)) := by
      exact Placed_window hPl 14 rfl
    obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlNH (by omega) hpc1 hM1 (hOffsetFit mIdxNH (by decide)) (by rw [hd1]; exact hMeta.meta_NH)
    have h2_2 : (reg s2 reg2).val = N := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
    have haBr : code[s2.pc]? = some (.branchLt reg2 reg3 (basePc + 18) (basePc + 1069)) := by
      rw [hpc2]; exact hPl 17 _ rfl
    obtain ⟨t, htRaw, hpct, hrt, hdt⟩ := step_branchLt_at (input := input) haBr (by split <;> omega)
    have ht := steps_1_of_step htRaw
    rw [ite_eq_right (by rw [h2_2, h3_2]; exact Nat.lt_irrefl _)] at hpct
    have hrTF := reg_of_regs_eq hrt
    have hdT : t.data = st.data := by rw [hdt, hd2, hd1]
    refine ⟨7, t, by omega, (hs1.append hs2).append ht, hpct,
      hMeta.preserve (by rw [hrTF, hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1])
        (by rw [hrTF, hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero])
        (by rw [hrTF, hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one])
        (fun i hi => by rw [hdT]),
      fun u hu => by rw [hdT]; exact hSt u hu,
      fun _ _ => by rw [hdT],
      fun _ _ _ _ => by rw [hdT]⟩
  | cons w remTail ih =>
    intro done hd st hApp hpc hMeta hCur hLk hDep hSt hRemPJ hPrior
    rcases hLk with ⟨hwEq, _, nxt, hNextW, hLkTail⟩
    subst hd
    let N := r.out.tables.next
    let metaBase := metaArrBase H.vertexCount H.arcCount N
    have hNLe : N ≤ H.vertexCount + 1 := (B_next_pos flat increasing covers rankArc r).2
    have hMetaEq : metaBase = 20 * N + 10 * H.vertexCount + H.arcCount + 1 := metaArrBase_eq _ _ _
    have hBoundMeta : metaBase + 64 ≤ workCap := by
      dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
    have hWorkFit : workCap ≤ 2 ^ bits := hw
    have hOffsetFit (off : Nat) (hoff : off < 64) : metaBase + off < 2 ^ bits := by omega
    have hOffWord (off : Nat) (hoff : off < 64) : off < 2 ^ bits := by omega
    have hRecords : storedBase N + 18 * N = priorBase N := by unfold storedBase priorBase; omega
    have hStoredBase : storedBase N = N := rfl
    have hPriorFits : priorBase N + 6 * H.vertexCount ≤ metaBase := by unfold priorBase; omega
    have hTrNextLo : priorBase N ≤ trigNextArrBase H.vertexCount N := by unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase; omega
    have hTrNextHi : trigNextArrBase H.vertexCount N + N ≤ metaBase := by
      unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase; omega
    have hRecFits (x k : Nat) (hx : x < N) (hk : k < 18) : storedBase N + 18 * x + k < metaBase := by omega
    have hDepthFits (x : Nat) (hx : x < N) : x < metaBase := by unfold priorBase at hPriorFits; omega
    have hPriFits (x k : Nat) (hx : x < H.vertexCount) (hk : k < 6) : priorBase N + 6 * x + k < metaBase := by omega
    have hTrigFits (x : Nat) (hx : x < N) : trigNextArrBase H.vertexCount N + x < metaBase := by omega
    have hwMemB : w ∈ buckets := by rw [← hApp]; exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
    obtain ⟨hwLt, hParPos, Pc, hBackW, hTrW⟩ := hSpec w hwMemB
    have hwPos : 0 < w := by
      refine Classical.byContradiction fun h0 => ?_
      have hz : w = 0 := by omega
      change 0 < B.F.parentOf w at hParPos
      rw [hz, (validJumpForest_root_zero B.G.layout.valid).1] at hParPos
      omega
    -- Header check `11..17`:
    have hPlC : Placed code (basePc + 11) (metaLoadInstrs (bits := bits) reg2 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega)) := by
      exact Placed_window hPl 11 rfl
    obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlC (by omega) hpc hMeta.rMeta_eq (hOffsetFit mIdxCCursor (by decide)) hCur
    have hM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hMeta.rMeta_eq]
    have hPlNH : Placed code (basePc + 14) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxNH (by dsimp only [mIdxNH]; omega)) := by
      exact Placed_window hPl 14 rfl
    obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlNH (by omega) hpc1 hM1 (hOffsetFit mIdxNH (by decide)) (by rw [hd1]; exact hMeta.meta_NH)
    have h2_2 : (reg s2 reg2).val = w := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
    have haBr : code[s2.pc]? = some (.branchLt reg2 reg3 (basePc + 18) (basePc + 1069)) := by
      rw [hpc2]; exact hPl 17 _ rfl
    obtain ⟨s3, hs3Raw, hpc3, hr3, hd3⟩ := step_branchLt_at (input := input) haBr (by split <;> omega)
    have hs3 := steps_1_of_step hs3Raw
    rw [ite_eq_left (by rw [h2_2, h3_2]; exact hwLt)] at hpc3
    have hr3F := reg_of_regs_eq hr3
    have hd3' : s3.data = st.data := by rw [hd3, hd2, hd1]
    have hMeta3 : MetaReady s3 H.vertexCount H.arcCount N nGlobal :=
      hMeta.preserve (by rw [hr3F, hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1])
        (by rw [hr3F, hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero])
        (by rw [hr3F, hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one])
        (fun i hi => by rw [hd3'])
    have hwPJ := hRemPJ w (List.mem_cons_self)
    have hPlOne : Placed code (basePc + 18) (step4BOneNodeInstrs (bits := bits) (basePc + 18) h100) := by
      unfold step4BInstrs at hPl
      have hA := Placed_append_left (Placed_append_left (Placed_append_left
        (Placed_append_left (Placed_append_left hPl))))
      simpa only [List.length_append, metaLoadInstrs, metaStoreInstrs, List.length_cons,
        List.length_nil, Nat.reduceAdd] using Placed_append_right hA
    obtain ⟨kOne, s4, hkOne, hs4, hpc4, hMeta4, hPar4, hJump4, hPM4, hJM4, hFr4⟩ :=
      run_step4BOneNode (input := input) (basePc + 18) h100 hPlOne (by omega) flat increasing covers rankArc
        hIn hWork hLayout rankArcKahn idx w hwPos hwLt Pc hBackW hTrW C.built.ref hParPos hOK0
        (fun _ _ => rfl) s3 hpc3 hMeta3
        (by rw [hd3']; exact hCur) (by rw [hd3']; exact hwPJ.1) (by rw [hd3']; exact hwPJ.2)
        (fun u => by rw [hd3']; exact hDep u)
        (fun u huL => by
          have hS := hSt u (Or.inl huL)
          refine ⟨by rw [hd3']; exact hS.1, by rw [hd3']; exact hS.2.1,
            mapWordsAt_frame (fun _ _ => by rw [hd3']) hS.2.2.1,
            mapWordsAt_frame (fun _ _ => by rw [hd3']) hS.2.2.2⟩)
        (fun q hq => by
          have hP := hPrior q hq
          have hEq6 : ∀ i < 6, s3.data[priorBase N + 6 * q.val + i]? = st.data[priorBase N + 6 * q.val + i]? := fun i _ => by rw [hd3']
          exact valuesWordsAt_frame hEq6 hP)
    change ∀ j, (j < storedBase N + 18 * w + 2 ∨
      (storedBase N + 18 * w + 18 ≤ j ∧ j < metaBase + mIdxEvalU) ∨ metaBase + 64 ≤ j) →
        s4.data[j]? = s3.data[j]? at hFr4
    have hWEnd : storedBase N + 18 * w + 18 ≤ priorBase N := by omega
    let tail : List (Instr bits 15) :=
      metaLoadInstrs reg2 reg3 mIdxCCursor (hOffWord mIdxCCursor (by decide)) ++
      metaLoadInstrs reg3 reg4 mIdxTrigNextBase (hOffWord mIdxTrigNextBase (by decide)) ++
      [.add reg3 reg3 reg2, .loadData reg3 reg3] ++
      metaStoreInstrs reg3 reg4 mIdxCCursor (hOffWord mIdxCCursor (by decide)) ++
      [.goto (basePc + 11)]
    have hTail : Placed code (basePc + 1057) tail := by
      unfold step4BInstrs at hPl
      let prefixOps := metaLoadInstrs (bits := bits) reg2 reg3 mIdxKCursor (hOffWord mIdxKCursor (by decide)) ++
        metaLoadInstrs reg3 reg4 mIdxTrigHeadBase (hOffWord mIdxTrigHeadBase (by decide)) ++
        [.add reg3 reg3 reg2, .loadData reg3 reg3] ++
        metaStoreInstrs reg3 reg4 mIdxCCursor (hOffWord mIdxCCursor (by decide)) ++
        metaLoadInstrs reg2 reg4 mIdxCCursor (hOffWord mIdxCCursor (by decide)) ++
        metaLoadInstrs reg3 reg4 mIdxNH (hOffWord mIdxNH (by decide)) ++
        [.branchLt reg2 reg3 (basePc + 18) (basePc + 1069)] ++
        step4BOneNodeInstrs (basePc + 18) h100
      have ht : Placed code basePc (prefixOps ++ tail) := by
        simpa only [prefixOps, tail, List.append_assoc] using hPl
      have hLen : prefixOps.length = 1057 := by
        simp [prefixOps, metaLoadInstrs, metaStoreInstrs, step4BOneNodeInstrs_length]
      simpa only [hLen] using Placed_append_right ht
    -- Advance bucket cursor (`basePc + 1057 .. 1068`, 12 steps):
    have hPlA0 : Placed code (basePc + 1057) (metaLoadInstrs (bits := bits) reg2 reg3 mIdxCCursor (by dsimp only [mIdxCCursor]; omega)) := by
      exact Placed_window hTail 0 rfl
    obtain ⟨s5, hs5, hpc5, hd5, h2_5, hPres5⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlA0 (by omega) hpc4 hMeta4.rMeta_eq (hOffsetFit mIdxCCursor (by decide))
      (by rw [hFr4 (metaBase + mIdxCCursor) (Or.inr (Or.inl
        ⟨by unfold priorBase at hPriorFits; omega, by dsimp only [mIdxCCursor, mIdxEvalU]; omega⟩)), hd3']; exact hCur)
    have hM5 : (reg s5 rMeta).val = metaBase := by
      rw [hPres5 rMeta (by intro h; cases h) (by intro h; cases h), hMeta4.rMeta_eq]
    have hPlA1 : Placed code (basePc + 1060) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxTrigNextBase (by dsimp only [mIdxTrigNextBase]; omega)) := by
      exact Placed_window hTail 3 rfl
    obtain ⟨s6, hs6, hpc6, hd6, h3_6, hPres6⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlA1 (by omega) hpc5 hM5 (hOffsetFit mIdxTrigNextBase (by decide))
      (by rw [hd5]; exact hMeta4.meta_trigNextBase)
    have h2_6 : (reg s6 reg2).val = w := by rw [hPres6 reg2 (by intro h; cases h) (by intro h; cases h), h2_5]
    have haATN : code[s6.pc]? = some (.add reg3 reg3 reg2) := by rw [hpc6]; exact hTail 6 _ rfl
    obtain ⟨s7, hs7Raw, hpc7, h3_7, ho7, hd7⟩ := step_add_at (input := input) haATN (by omega)
    have hs7 := steps_1_of_step hs7Raw
    have h3Val7 : (reg s7 reg3).val = trigNextArrBase H.vertexCount N + w := by
      rw [h3_7, add_no_wrap _ _ (by rw [h3_6, h2_6]; unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase priorBase storedBase at *; omega), h3_6, h2_6]
    obtain ⟨wn, hwn, hwnV⟩ := Option.map_eq_some_iff.mp hNextW
    have haLTN : code[s7.pc]? = some (.loadData reg3 reg3) := by rw [hpc7, hpc6]; exact hTail 7 _ rfl
    obtain ⟨s8, hs8Raw, hpc8, h3_8, ho8, hd8⟩ := step_loadData_at (input := input) haLTN (by omega)
      (by rw [h3Val7, hd7, hd6, hd5, hFr4 (trigNextArrBase H.vertexCount N + w) (Or.inr (Or.inl
        ⟨by omega, Nat.lt_of_lt_of_le (hTrigFits w hwLt) (Nat.le_add_right _ _)⟩)), hd3']; exact hwn)
    have hs8 := steps_1_of_step hs8Raw
    have hNxtVal8 : (reg s8 reg3).val = nxt := by rw [h3_8, hwnV]
    have hM8 : (reg s8 rMeta).val = metaBase := by
      rw [ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h),
        hPres6 rMeta (by intro h; cases h) (by intro h; cases h), hM5]
    have hPlSC : Placed code (basePc + 1065) (metaStoreInstrs (bits := bits) reg3 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega)) := by
      exact Placed_window hTail 8 rfl
    obtain ⟨s9, hs9, hpc9, hAt9, hFr9, hPres9⟩ := run_metaStore_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlSC (by omega) (by rw [hpc8, hpc7, hpc6]) hM8 (hOffsetFit mIdxCCursor (by decide))
      (lt_data_size (by change metaBase + mIdxCCursor < workCap; dsimp only [mIdxCCursor]; omega))
    have haGoL : code[s9.pc]? = some (.goto (basePc + 11)) := by rw [hpc9]; exact hTail 11 _ rfl
    obtain ⟨s10, hs10Raw, hpc10, hr10, hd10⟩ := step_goto_at (input := input) haGoL (by omega)
    have hs10 := steps_1_of_step hs10Raw
    have hr10F := reg_of_regs_eq hr10
    have hFr10_4 : ∀ j, j ≠ metaBase + mIdxCCursor → s10.data[j]? = s4.data[j]? := fun j hj => by
      rw [hd10, hFr9 j hj, hd8, hd7, hd6, hd5]
    have hFr10_0 : ∀ j, (j < storedBase N + 18 * w + 2 ∨
        (storedBase N + 18 * w + 18 ≤ j ∧ j < metaBase + mIdxCCursor) ∨
        metaBase + 64 ≤ j) → s10.data[j]? = st.data[j]? := fun j hj => by
      rw [hFr10_4 j (by
        have hEnd : storedBase N + 18 * w + 2 ≤ metaBase := by omega
        dsimp only [mIdxCCursor] at *
        rcases hj with h | ⟨_, h⟩ | h <;> omega),
        hFr4 j (by dsimp only [mIdxCCursor, mIdxEvalU] at *; rcases hj with h | ⟨h1, h2⟩ | h <;> omega), hd3']
    have hM10 : (reg s10 rMeta).val = metaBase := by
      rw [hr10F, hPres9 rMeta (by intro h; cases h), hM8]
    have h0_10 : (reg s10 reg0).val = 0 := by
      rw [hr10F, hPres9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h),
        hPres6 reg0 (by intro h; cases h) (by intro h; cases h), hPres5 reg0 (by intro h; cases h) (by intro h; cases h), hMeta4.r0_zero]
    have h1_10 : (reg s10 reg1).val = 1 := by
      rw [hr10F, hPres9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h),
        hPres6 reg1 (by intro h; cases h) (by intro h; cases h), hPres5 reg1 (by intro h; cases h) (by intro h; cases h), hMeta4.r1_one]
    have hMeta10 : MetaReady s10 H.vertexCount H.arcCount N nGlobal :=
      hMeta.preserve hM10 h0_10 h1_10 (fun i hi =>
        hFr10_0 (metaBase + i) (Or.inr (Or.inl ⟨by omega, by dsimp only [mIdxCCursor]; omega⟩)))
    -- Apply `ih` on `remTail` with `done ++ [w]`:
    have hApp' : (done ++ [w]) ++ remTail = buckets := by simp [← hApp]
    have hDisjDone : ∀ u ∈ done, u ≠ w := by
      intro u hu heq; subst u
      have hNd := hNodup; rw [← hApp, List.nodup_append] at hNd
      exact hNd.2.2 w hu w (List.mem_cons_self) rfl
    have hDisjTail : ∀ u ∈ remTail, u ≠ w := by
      intro u hu heq; subst u
      have hNd := hNodup; rw [← hApp, List.nodup_append] at hNd
      exact (List.nodup_cons.mp hNd.2.1).1 hu
    have hSt10 : ∀ u : Fin N, (liveBefore flat increasing covers rankArc r rankKahn idx u.val ∨ u.val ∈ done ++ [w]) →
        (s10.data[storedBase N + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (s10.data[storedBase N + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt s10.data (storedBase N + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt s10.data (storedBase N + 18 * u.val + 10) (C.built.ref u.val).jumpMap := by
      intro u hu
      by_cases huW : u.val = w
      · rw [huW]
        have hEq18 : ∀ k < 18, s10.data[storedBase N + 18 * w + k]? = s4.data[storedBase N + 18 * w + k]? := fun k _ =>
          hFr10_4 (storedBase N + 18 * w + k) (Nat.ne_of_lt
            (Nat.lt_of_lt_of_le (hRecFits w k hwLt ‹k < 18›) (Nat.le_add_right _ _)))
        have hAddr0 := hEq18 0 (by decide)
        simp only [Nat.add_zero] at hAddr0
        refine ⟨by rw [hAddr0]; exact hPar4, by rw [hEq18 1 (by decide)]; exact hJump4,
          mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (2 + k) (by omega)) hPM4,
          mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (10 + k) (by omega)) hJM4⟩
      · have huOld : liveBefore flat increasing covers rankArc r rankKahn idx u.val ∨ u.val ∈ done := by
          rcases hu with h | h
          · exact Or.inl h
          · rcases List.mem_append.mp h with h1 | h1
            · exact Or.inr h1
            · exact False.elim (huW (List.mem_singleton.mp h1))
        have hEq18 : ∀ k < 18, s10.data[storedBase N + 18 * u.val + k]? = st.data[storedBase N + 18 * u.val + k]? := fun k hk => by
          by_cases hLt : u.val < w
          · exact hFr10_0 _ (Or.inl (by omega))
          · exact hFr10_0 _ (Or.inr (Or.inl
              ⟨by omega, Nat.lt_of_lt_of_le (hRecFits u.val k u.isLt hk) (Nat.le_add_right _ _)⟩))
        have ho := hSt u huOld
        have hAddr0 := hEq18 0 (by decide)
        simp only [Nat.add_zero] at hAddr0
        refine ⟨by rw [hAddr0]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
          mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (2 + k) (by omega)) ho.2.2.1,
          mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (10 + k) (by omega)) ho.2.2.2⟩
    obtain ⟨kRest, t, hkRest, hsRest, hpct, hMetaT, hStT, hFrRest, hPJRest⟩ := ih (done ++ [w]) nxt s10 hApp' hpc10 hMeta10
      (by rw [hd10, hAt9, Option.map_some, hNxtVal8])
      (ListLinked.frame (fun z hz => by
        have hzLt : z < N := (hSpec z (by rw [← hApp]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hz)))).1
        exact hFr10_0 (trigNextArrBase H.vertexCount N + z) (Or.inr (Or.inl
          ⟨by omega, Nat.lt_of_lt_of_le (hTrigFits z hzLt) (Nat.le_add_right _ _)⟩))) hLkTail)
      (fun u => by rw [hFr10_0 u.val (Or.inl (by have := u.isLt; omega))]; exact hDep u)
      hSt10
      (fun x hx => by
        have hxLt : x < N := (hSpec x (by rw [← hApp]; exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hx)))).1
        have hxNe : x ≠ w := hDisjTail x hx
        have hEq2 : ∀ k < 2, s10.data[storedBase N + 18 * x + k]? = st.data[storedBase N + 18 * x + k]? := fun k hk => by
          by_cases hLt : x < w
          · exact hFr10_0 _ (Or.inl (by omega))
          · exact hFr10_0 _ (Or.inr (Or.inl
              ⟨by omega, Nat.lt_of_lt_of_le (hRecFits x k hxLt (by omega)) (Nat.le_add_right _ _)⟩))
        have hxOld := hRemPJ x (List.mem_cons_of_mem _ hx)
        have hAddr0 := hEq2 0 (by decide)
        simp only [Nat.add_zero] at hAddr0
        exact ⟨by rw [hAddr0]; exact hxOld.1, by rw [hEq2 1 (by decide)]; exact hxOld.2⟩)
      (fun q hq => by
        have hEq6 : ∀ i < 6, s10.data[priorBase N + 6 * q.val + i]? = st.data[priorBase N + 6 * q.val + i]? := fun i hi =>
          hFr10_0 _ (Or.inr (Or.inl
            ⟨by omega, Nat.lt_of_lt_of_le (hPriFits q.val i q.isLt hi) (Nat.le_add_right _ _)⟩))
        have hP := hPrior q hq
        exact valuesWordsAt_frame hEq6 hP)
    have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
    have hStepsCur : Steps code input (7 + kOne + 12) st s10 :=
      (((hs1.append hs2).append hs3).append hs4).append
        ((hs5.append (hs6.append (hs7.append hs8))).append (hs9.append hs10))
    refine ⟨(7 + kOne + 12) + kRest, t, ?_, hStepsCur.append hsRest, hpct, hMetaT, hStT, fun j hj => ?_, fun x hx k hk => ?_⟩
    · have hMulCons : 1620 * (w :: remTail).length * OracleContract.L H.vertexCount =
          1620 * remTail.length * OracleContract.L H.vertexCount + 1620 * OracleContract.L H.vertexCount := by
        simp only [List.length_cons]
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
      omega
    · rw [hFrRest j hj]
      rcases hj with h | ⟨h1, h2⟩ | h
      · change j < storedBase N at h
        exact hFr10_0 j (Or.inl (by omega))
      · change priorBase N ≤ j at h1
        exact hFr10_0 j (Or.inr (Or.inl ⟨by omega, h2⟩))
      · exact hFr10_0 j (Or.inr (Or.inr h))
    · rw [hPJRest x hx k hk]
      change x < N at hx
      by_cases hxW : x ≤ w
      · exact hFr10_0 (storedBase N + 18 * x + k) (Or.inl (by omega))
      · exact hFr10_0 (storedBase N + 18 * x + k) (Or.inr (Or.inl
          ⟨by omega, Nat.lt_of_lt_of_le (hRecFits x k hx (by omega)) (Nat.le_add_right _ _)⟩))

theorem run_step4B {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (step4BInstrs (bits := bits) basePc h100))
    (hSz : basePc + 1069 < code.size)
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
    (idx : Nat) (hIdxLt : idx < H.vertexCount) (buckets : List Nat) (hNodup : buckets.Nodup)
    (hSpec : ∀ w ∈ buckets, w < r.out.tables.next ∧
      0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w ∧
      ∃ Pc : CutPair H, r.out.tables.back[w]? = some (some Pc) ∧
        max (rankKahn Pc.fst) (rankKahn Pc.snd) = idx)
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∀ (hOK0 : LiveStoreOK B.F C.built.ref (liveBefore flat increasing covers rankArc r rankKahn idx))
    (st : State DomL) (hpc : st.pc = basePc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hKCur : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor]?).map Fin.val = some idx)
    (hd : Nat)
    (hHead : (st.data[trigHeadArrBase H.vertexCount r.out.tables.next + idx]?).map Fin.val = some hd)
    (hLk : ListLinked st.data (trigNextArrBase H.vertexCount r.out.tables.next) r.out.tables.next hd buckets)
    (hDep : ∀ u : Fin r.out.tables.next, (st.data[u.val]?).map Fin.val = some (B.F.depthOf u.val))
    (hSt : ∀ u : Fin r.out.tables.next, liveBefore flat increasing covers rankArc r rankKahn idx u.val →
      (st.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
      (st.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
      MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap)
    (hRemPJ : ∀ w ∈ buckets,
      (st.data[storedBase r.out.tables.next + 18 * w]?).map Fin.val = some (B.F.parentOf w) ∧
      (st.data[storedBase r.out.tables.next + 18 * w + 1]?).map Fin.val = some (B.F.jumpOf w))
    (hPrior : ∀ q : Fin H.vertexCount, rankKahn q ≤ idx →
      ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q)),
    ∃ k t, k ≤ 1620 * buckets.length * OracleContract.L H.vertexCount + 18 ∧
      Steps code input k st t ∧ t.pc = basePc + 1069 ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ u : Fin r.out.tables.next,
        (liveBefore flat increasing covers rankArc r rankKahn idx u.val ∨ u.val ∈ buckets) →
        (t.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (t.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap) ∧
      (∀ j, (j < storedBase r.out.tables.next ∨
          (priorBase r.out.tables.next ≤ j ∧
            j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCCursor) ∨
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + 64 ≤ j) →
        t.data[j]? = st.data[j]?) ∧
      (∀ x < r.out.tables.next, ∀ k < 2,
        t.data[storedBase r.out.tables.next + 18 * x + k]? =
          st.data[storedBase r.out.tables.next + 18 * x + k]?) := by
  intro C B hOK0 st hpc hMeta hKCur hd hHead hLk hDep hSt hRemPJ hPrior
  let N := r.out.tables.next
  let metaBase := metaArrBase H.vertexCount H.arcCount N
  have hNLe : N ≤ H.vertexCount + 1 := (B_next_pos flat increasing covers rankArc r).2
  have hMetaEq : metaBase = 20 * N + 10 * H.vertexCount + H.arcCount + 1 := metaArrBase_eq _ _ _
  have hBoundMeta : metaBase + 64 ≤ workCap := by
    dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hOffsetFit (off : Nat) (hoff : off < 64) : metaBase + off < 2 ^ bits := by omega
  have hOffWord (off : Nat) (hoff : off < 64) : off < 2 ^ bits := by omega
  have hRecords : storedBase N + 18 * N = priorBase N := by unfold storedBase priorBase; omega
  have hStoredBase : storedBase N = N := rfl
  have hPriorFits : priorBase N + 6 * H.vertexCount ≤ metaBase := by unfold priorBase; omega
  have hTrNextLo : priorBase N ≤ trigNextArrBase H.vertexCount N := by unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase; omega
  have hTrNextHi : trigNextArrBase H.vertexCount N + N ≤ metaBase := by
    unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase; omega
  have hRecFits (x k : Nat) (hx : x < N) (hk : k < 18) : storedBase N + 18 * x + k < metaBase := by omega
  have hDepthFits (x : Nat) (hx : x < N) : x < metaBase := by unfold priorBase at hPriorFits; omega
  have hPriFits (x k : Nat) (hx : x < H.vertexCount) (hk : k < 6) : priorBase N + 6 * x + k < metaBase := by omega
  have hTrigFits (x : Nat) (hx : x < N) : trigNextArrBase H.vertexCount N + x < metaBase := by omega
  have hPl0 : Placed code basePc (metaLoadInstrs (bits := bits) reg2 reg3 mIdxKCursor (by dsimp only [mIdxKCursor]; omega)) :=
    Placed_window hPl 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) hpc hMeta.rMeta_eq (hOffsetFit mIdxKCursor (by decide)) hKCur
  have hM1 : (reg s1 rMeta).val = metaBase := by rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hMeta.rMeta_eq]
  have hPl1 : Placed code (basePc + 3) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxTrigHeadBase (by dsimp only [mIdxTrigHeadBase]; omega)) := by
    exact Placed_window hPl 3 rfl
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc1 hM1 (hOffsetFit mIdxTrigHeadBase (by decide)) (by rw [hd1]; exact hMeta.meta_trigHeadBase)
  have h2_2 : (reg s2 reg2).val = idx := by rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have haA6 : code[s2.pc]? = some (.add reg3 reg3 reg2) := by rw [hpc2]; exact hPl 6 _ rfl
  obtain ⟨s3, hs3Raw, hpc3, h3_3, ho3, hd3⟩ := step_add_at (input := input) haA6 (by omega)
  have hs3 := steps_1_of_step hs3Raw
  have h3Val3 : (reg s3 reg3).val = trigHeadArrBase H.vertexCount N + idx := by
    rw [h3_3, add_no_wrap _ _ (by rw [h3_2, h2_2]; unfold trigHeadArrBase trigNextArrBase topoRankArrBase orderArrBase priorBase storedBase at *; omega), h3_2, h2_2]
  obtain ⟨whd, hwhd, hwhdV⟩ := Option.map_eq_some_iff.mp hHead
  have haL7 : code[s3.pc]? = some (.loadData reg3 reg3) := by rw [hpc3, hpc2]; exact hPl 7 _ rfl
  obtain ⟨s4, hs4Raw, hpc4, h3_4, ho4, hd4⟩ := step_loadData_at (input := input) haL7 (by omega)
    (by rw [h3Val3, hd3, hd2, hd1]; exact hwhd)
  have hs4 := steps_1_of_step hs4Raw
  have hHdVal : (reg s4 reg3).val = hd := by rw [h3_4, hwhdV]
  have hM4 : (reg s4 rMeta).val = metaBase := by
    rw [ho4 rMeta (by intro h; cases h), ho3 rMeta (by intro h; cases h),
      hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1]
  have hPlS : Placed code (basePc + 8) (metaStoreInstrs (bits := bits) reg3 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega)) := by
    exact Placed_window hPl 8 rfl
  obtain ⟨s5, hs5, hpc5, hAt5, hFr5, hPres5⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS (by omega) (by rw [hpc4, hpc3, hpc2]) hM4 (hOffsetFit mIdxCCursor (by decide))
    (lt_data_size (by change metaBase + mIdxCCursor < workCap; dsimp only [mIdxCCursor]; omega))
  have hFr5' : ∀ j, j ≠ metaBase + mIdxCCursor → s5.data[j]? = st.data[j]? := fun j hj => by
    rw [hFr5 j hj, hd4, hd3, hd2, hd1]
  have hMeta5 : MetaReady s5 H.vertexCount H.arcCount N nGlobal :=
    hMeta.preserve (by rw [hPres5 rMeta (by intro h; cases h), hM4])
      (by rw [hPres5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h), ho3 reg0 (by intro h; cases h),
        hPres2 reg0 (by intro h; cases h) (by intro h; cases h), hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero])
      (by rw [hPres5 reg1 (by intro h; cases h), ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h),
        hPres2 reg1 (by intro h; cases h) (by intro h; cases h), hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one])
      (fun i hi => hFr5' (metaBase + i) (fun he => (by dsimp only [mIdxCCursor]; omega : i ≠ mIdxCCursor) (Nat.add_left_cancel he)))
  obtain ⟨kL, t, hkL, hsL, hpct, hMetaT, hStT, hFrL, hPJL⟩ := step4B_bucketLoop_spec (input := input) basePc h100 hPl hSz
    flat increasing covers rankArc hIn hWork (wFit := wFit) hLayout rankArcKahn idx buckets hNodup hSpec hOK0
    buckets [] hd s5 (List.nil_append _) hpc5 hMeta5 (by rw [hAt5, Option.map_some, hHdVal])
    (ListLinked.frame (fun z hz => hFr5' _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le
      (hTrigFits z (hSpec z hz).1) (Nat.le_add_right _ _)))) hLk)
    (fun u => by rw [hFr5' u.val (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hDepthFits u.val u.isLt) (Nat.le_add_right _ _)))]; exact hDep u)
    (fun u hu => by
      have hOld : liveBefore flat increasing covers rankArc r rankKahn idx u.val :=
        hu.elim id (fun h => False.elim (List.not_mem_nil h))
      have hEq18 : ∀ k < 18, s5.data[storedBase N + 18 * u.val + k]? = st.data[storedBase N + 18 * u.val + k]? := fun k hk =>
        hFr5' _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hRecFits u.val k u.isLt hk) (Nat.le_add_right _ _)))
      have ho := hSt u hOld
      have hAddr0 := hEq18 0 (by decide)
      simp only [Nat.add_zero] at hAddr0
      refine ⟨by rw [hAddr0]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
        mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (2 + k) (by omega)) ho.2.2.1,
        mapWordsAt_frame (fun k hk => by rw [Nat.add_assoc]; exact hEq18 (10 + k) (by omega)) ho.2.2.2⟩)
    (fun w hw => by
      have hEq2 : ∀ k < 2, s5.data[storedBase N + 18 * w + k]? = st.data[storedBase N + 18 * w + k]? := fun k hk =>
        hFr5' _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hRecFits w k (hSpec w hw).1 (by omega)) (Nat.le_add_right _ _)))
      have ho := hRemPJ w hw
      have hAddr0 := hEq2 0 (by decide)
      simp only [Nat.add_zero] at hAddr0
      exact ⟨by rw [hAddr0]; exact ho.1, by rw [hEq2 1 (by decide)]; exact ho.2⟩)
    (fun q hq => by
      have hEq6 : ∀ i < 6, s5.data[priorBase N + 6 * q.val + i]? = st.data[priorBase N + 6 * q.val + i]? := fun i hi =>
        hFr5' _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hPriFits q.val i q.isLt hi) (Nat.le_add_right _ _)))
      have hP := hPrior q hq
      exact valuesWordsAt_frame hEq6 hP)
  exact ⟨11 + kL, t, by omega, ((hs1.append hs2).append (hs3.append (hs4.append hs5))).append hsL,
    hpct, hMetaT, hStT, fun j hj => by
      rw [hFrL j hj]
      change j < storedBase N ∨ (priorBase N ≤ j ∧ j < metaBase + mIdxCCursor) ∨ metaBase + 64 ≤ j at hj
      exact hFr5' j (by dsimp only [mIdxCCursor] at *; rcases hj with h | ⟨_, h⟩ | h <;> omega),
    fun x hx k hk => by
      rw [hPJL x hx k hk]
      exact hFr5' _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le (hRecFits x k hx (by omega)) (Nat.le_add_right _ _)))⟩

end PaperB.RamProgram.ExitSummaryBuild
