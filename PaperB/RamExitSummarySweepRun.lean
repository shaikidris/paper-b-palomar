module

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
set_option linter.unusedSimpArgs false
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

section Stage4Phase





section Stage4LoopProof

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private theorem seed_maps_to_mapWordsAt {mem : Array (Word bits)} {addr : Nat}
    (h : ∀ i < 16, (mem[addr + i]?).map Fin.val =
      some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0)) :
    MapWordsAt mem addr Map.identity ∧ MapWordsAt mem (addr + 8) Map.identity := by
  refine ⟨⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩,
    ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩⟩
  · simpa using h 0 (by decide)
  · simpa using h 1 (by decide)
  · simpa using h 2 (by decide)
  · simpa [Map.identity] using h 3 (by decide)
  · simpa using h 4 (by decide)
  · simpa using h 5 (by decide)
  · simpa using h 6 (by decide)
  · simpa [Map.identity] using h 7 (by decide)
  · simpa [Nat.add_assoc] using h 8 (by decide)
  · simpa [Nat.add_assoc] using h 9 (by decide)
  · simpa [Nat.add_assoc] using h 10 (by decide)
  · simpa [Nat.add_assoc, Map.identity] using h 11 (by decide)
  · simpa [Nat.add_assoc] using h 12 (by decide)
  · simpa [Nat.add_assoc] using h 13 (by decide)
  · simpa [Nat.add_assoc] using h 14 (by decide)
  · simpa [Nat.add_assoc, Map.identity] using h 15 (by decide)

private theorem liveStoreOK_liveBefore {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (entryRank : Fin H.origVertexCount → Nat)
    {bits endpoints : Nat}
    (hRank : ∀ x : Fin H.origVertexCount, entryRank x < endpoints)
    (wFit : Width bits (max r.out.tables.next endpoints))
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    (rankKahn : Vertex H → Nat)
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    (idx : Nat) :
    let C := buildActualSealedContract H flat increasing covers rankArc r entryRank hRank wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    LiveStoreOK B.F C.built.ref (liveBefore flat increasing covers rankArc r rankKahn idx) := by
  intro C B
  have hPJ := liveBefore_parent_and_jump flat increasing covers rankArc r rankKahn rankArcKahn idx
  have hAll : ∀ u, liveBefore flat increasing covers rankArc r rankKahn idx u → C.built.live u :=
    fun u hu => C.built.all_live u (B.G.size_eq.symm ▸ hu.1)
  refine
    { live_lt := fun u hu => B.G.size_eq.symm ▸ hu.1
      parent_eq := fun u hu => C.built.liveOK.parent_eq u (hAll u hu)
      jump_eq := fun u hu => C.built.liveOK.jump_eq u (hAll u hu)
      parent_live := fun u hu => (hPJ u hu).1
      jump_live := fun u hu => (hPJ u hu).2
      parent_down := fun u hu hd => C.built.liveOK.parent_down u (hAll u hu) hd
      hops :=
        { parent_path := fun u hu => C.built.liveOK.hops.parent_path u (hAll u hu)
          jump_path := fun u hu => C.built.liveOK.hops.jump_path u (hAll u hu) } }

private theorem liveBefore_step {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (rankKahn : Vertex H → Nat) (buckets : Nat → List Nat)
    (hCover : ∀ w < r.out.tables.next,
      0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w →
      ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
        w ∈ buckets (max (rankKahn P.fst) (rankKahn P.snd)))
    (idx u : Nat) :
    liveBefore flat increasing covers rankArc r rankKahn (idx + 1) u →
      liveBefore flat increasing covers rankArc r rankKahn idx u ∨ u ∈ buckets idx := by
  intro ⟨huLt, huCond⟩
  rcases huCond with h0 | hp0 | ⟨Pc, hBack, hMax⟩
  · exact Or.inl ⟨huLt, Or.inl h0⟩
  · exact Or.inl ⟨huLt, Or.inr (Or.inl hp0)⟩
  · by_cases hLt : max (rankKahn Pc.fst) (rankKahn Pc.snd) < idx
    · exact Or.inl ⟨huLt, Or.inr (Or.inr ⟨Pc, hBack, hLt⟩)⟩
    · have hEq : max (rankKahn Pc.fst) (rankKahn Pc.snd) = idx := by omega
      by_cases hpPos : 0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf u
      · obtain ⟨P2, hBack2, hMem⟩ := hCover u huLt hpPos
        have hPEq : Pc = P2 := Option.some.inj (Option.some.inj (hBack.symm.trans hBack2))
        rw [← hPEq, hEq] at hMem
        exact Or.inr hMem
      · exact Or.inl ⟨huLt, Or.inr (Or.inl (by omega))⟩

private theorem stage4Loop_spec {code : Program DomL} {input : Input DomL}
    (h100 : 100 ≤ 2 ^ bits)
    (hPlLoop : Placed code 3 (stage4LoopInstrs (bits := bits) h100))
    (hSz : 1615 < code.size)
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
    {orderKahn : Array (Vertex H)} {sizeKahn : orderKahn.size = H.vertexCount}
    {rankKahn : Vertex H → Nat} {buckets : Nat → List Nat}
    (hOrdCov : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt orderKahn sizeKahn i = v)
    (hRkAt : ∀ i : Fin H.vertexCount, rankKahn (orderedVertexAt orderKahn sizeKahn i) = i.val)
    (rankArcKahn : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v)
    (hBucketsSpec : ∀ tr < H.vertexCount, (buckets tr).Nodup ∧ ∀ w ∈ buckets tr,
      w < r.out.tables.next ∧
      0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w ∧
      ∃ Pc : CutPair H, r.out.tables.back[w]? = some (some Pc) ∧
        max (rankKahn Pc.fst) (rankKahn Pc.snd) = tr)
    (hBucketsCover : ∀ w < r.out.tables.next,
      0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w →
      ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
        w ∈ buckets (max (rankKahn P.fst) (rankKahn P.snd)))
    {wFit : Width bits (max r.out.tables.next nGlobal)}
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∀ (rem idx : Nat) (st : State DomL),
      idx + rem = H.vertexCount →
      st.pc = 3 →
      MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor]?).map Fin.val =
        some idx →
      (∀ i : Fin H.vertexCount,
        (st.data[orderArrBase H.vertexCount r.out.tables.next + i.val]?).map Fin.val =
          some (orderedVertexAt orderKahn sizeKahn i).val) →
      (∀ i ≤ H.vertexCount,
        (st.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val =
          some (prefixIn H i)) →
      (∀ v < H.vertexCount, ∀ k : Fin (degIn H v),
        (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + k.val)]?).map Fin.val =
          some ((inArcsPrefix H H.arcCount v)[k.val]'(by rw [inArcsPrefix_length]; exact k.isLt))) →
      (∀ tr < H.vertexCount, ∃ hd : Nat,
        (st.data[trigHeadArrBase H.vertexCount r.out.tables.next + tr]?).map Fin.val = some hd ∧
        ListLinked st.data (trigNextArrBase H.vertexCount r.out.tables.next) r.out.tables.next hd
          (buckets tr)) →
      (∀ u : Fin r.out.tables.next,
        (st.data[u.val]?).map Fin.val = some (B.F.depthOf u.val)) →
      (∀ u : Fin r.out.tables.next,
        (st.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (B.F.parentOf u.val) ∧
        (st.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (B.F.jumpOf u.val)) →
      (∀ u : Fin r.out.tables.next,
        liveBefore flat increasing covers rankArc r rankKahn idx u.val →
        (st.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (st.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt st.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap) →
      (∀ q : Fin H.vertexCount, rankKahn q < idx →
        ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q)) →
      (∀ q : Fin H.vertexCount, idx ≤ rankKahn q →
        ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) zero) →
      ∃ steps t,
        steps ≤ (750 * (remDegIn H orderKahn sizeKahn idx rem + rem) +
            1620 * remBucketsLen buckets idx rem) * OracleContract.L H.vertexCount + 7 ∧
        Steps code input steps st t ∧ t.pc = 1615 ∧
        MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
        (∀ u : Fin r.out.tables.next,
          (t.data[u.val]?).map Fin.val = some (B.F.depthOf u.val)) ∧
        (∀ u : Fin r.out.tables.next,
          (t.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
          (t.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
          MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
          MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap) ∧
        (∀ q : Fin H.vertexCount,
          ValuesWordsAt t.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q)) := by
  intro C B rem
  induction rem with
  | zero =>
    intro idx st hSum hpc hMeta hKCur hOrd hInStart hInArcs hTrig hDep hPJ hSt hPriorDone hPriorZero
    have hIdxEq : idx = H.vertexCount := by omega
    subst hIdxEq
    let n := H.vertexCount
    let m := H.arcCount
    let N := r.out.tables.next
    let metaBase := metaArrBase n m N
    have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
    have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
    have hBoundMeta : metaBase + 64 ≤ workCap := by
      dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
    have hWorkFit : workCap ≤ 2 ^ bits := hw
    have hOffsetFit (off : Nat) (hof : off < 64) : metaBase + off < 2 ^ bits := by omega
    have hPl3 : Placed code 3 (metaLoadInstrs (bits := bits) reg2 reg4 mIdxKCursor
        (by dsimp only [mIdxKCursor]; omega)) :=
      Placed_append_left (by unfold stage4LoopInstrs at hPlLoop; exact hPlLoop)
    have hPlRest3 := Placed_append_right (by unfold stage4LoopInstrs at hPlLoop; exact hPlLoop)
    rw [show (metaLoadInstrs (bits := bits) reg2 reg4 mIdxKCursor (by dsimp only [mIdxKCursor]; omega)).length = 3 by rfl] at hPlRest3
    have hPl6 : Placed code 6 (metaLoadInstrs (bits := bits) reg3 reg4 mIdxN
        (by dsimp only [mIdxN]; omega)) :=
      Placed_append_left hPlRest3
    have hPlRest6 := Placed_append_right hPlRest3
    rw [show (metaLoadInstrs (bits := bits) reg3 reg4 mIdxN (by dsimp only [mIdxN]; omega)).length = 3 by rfl] at hPlRest6
    obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl3 (by omega) hpc hMeta.rMeta_eq (hOffsetFit mIdxKCursor (by decide)) hKCur
    have hM1 : (reg s1 rMeta).val = metaBase := by
      rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hMeta.rMeta_eq]
    obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl6 (by omega) hpc1 hM1 (hOffsetFit mIdxN (by decide))
      (by rw [hd1]; exact hMeta.meta_n)
    have h2_2 : (reg s2 reg2).val = n := by
      rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
    have haBr : code[s2.pc]? = some (.branchLt reg2 reg3 10 1615) := by
      rw [hpc2]; exact hPlRest6 0 _ rfl
    obtain ⟨t, htRaw, hpct, hrt, hdt⟩ := step_branchLt_at (input := input) haBr (by split <;> omega)
    have ht := steps_1_of_step htRaw
    rw [ite_eq_right (by rw [h2_2, h3_2]; exact Nat.lt_irrefl _)] at hpct
    have hrTF := reg_of_regs_eq hrt
    have hdT : t.data = st.data := by rw [hdt, hd2, hd1]
    have hRkLt : ∀ q : Fin H.vertexCount, rankKahn q < H.vertexCount := by
      intro q
      obtain ⟨j, hj⟩ := hOrdCov q
      rw [← hj, hRkAt j]
      exact j.isLt
    have hLiveFin : ∀ u : Fin N, liveBefore flat increasing covers rankArc r rankKahn H.vertexCount u.val :=
      fun u => (liveBefore_final_iff flat increasing covers rankArc r rankKahn hRkLt u.val).mpr u.isLt
    refine ⟨7, t, by omega, (hs1.append hs2).append ht, hpct,
      hMeta.preserve
        (by rw [hrTF, hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1])
        (by rw [hrTF, hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero])
        (by rw [hrTF, hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one])
        (fun i hi => by rw [hdT]),
      fun u => by rw [hdT]; exact hDep u,
      fun u => by rw [hdT]; exact hSt u (hLiveFin u),
      fun q => by rw [hdT]; exact hPriorDone q (hRkLt q)⟩
  | succ rem ih =>
    intro idx st hSum hpc hMeta hKCur hOrd hInStart hInArcs hTrig hDep hPJ hSt hPriorDone hPriorZero
    have hIdxLt : idx < H.vertexCount := by omega
    let n := H.vertexCount
    let m := H.arcCount
    let N := r.out.tables.next
    let metaBase := metaArrBase n m N
    have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
    have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
    have hBoundMeta : metaBase + 64 ≤ workCap := by
      dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
    have hWorkFit : workCap ≤ 2 ^ bits := hw
    have hOffsetFit (off : Nat) (hof : off < 64) : metaBase + off < 2 ^ bits := by omega
    have hRkLt : ∀ v : Vertex H, rankKahn v < n := by
      intro v
      obtain ⟨j, hj⟩ := hOrdCov v
      rw [← hj, hRkAt j]
      exact j.isLt
    have hReadOff (j : Nat) (hj : j < metaBase) (off : Nat) : j ≠ metaBase + off := by omega
    have hRecordLimit : storedBase N + 18 * N = priorBase N := by
      unfold storedBase priorBase
      omega
    have hRecordLt (u : Fin N) (j : Nat) (hj : j < 18) :
        storedBase N + 18 * u.val + j < priorBase N := by
      have := u.isLt
      omega
    have hPreviousLt (q : Fin n) (j : Nat) (hj : j < 6) :
        priorBase N + 6 * q.val + j < orderArrBase n N := by
      have := q.isLt
      unfold priorBase orderArrBase
      omega
    have hPreviousMeta : orderArrBase n N ≤ metaBase := by unfold orderArrBase; omega
    have hPriorMeta : priorBase N ≤ metaBase := by unfold priorBase; omega
    have hOrderMeta (i : Fin n) : orderArrBase n N + i.val < metaBase := by
      have := i.isLt
      unfold orderArrBase
      omega
    have hHeadMeta (i : Nat) (hi : i < n) : trigHeadArrBase n N + i < metaBase := by
      unfold trigHeadArrBase topoRankArrBase orderArrBase
      omega
    have hNextMeta (i : Nat) (hi : i < N) : trigNextArrBase n N + i < metaBase := by
      unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
      omega
    have hStartMeta (i : Nat) (hi : i ≤ n) : inStartArrBase n N + i < metaBase := by
      unfold inStartArrBase trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
      omega
    have hArcMeta (v : Nat) (hv : v < n) (k : Fin (degIn H v)) :
        inArcIdArrBase n N + (prefixIn H v + k.val) < metaBase := by
      have hPrefix := prefixIn_mono H (show v + 1 ≤ H.vertexCount by change v + 1 ≤ n; omega)
      rw [prefixIn_vertexCount] at hPrefix
      change prefixIn H v + degIn H v ≤ m at hPrefix
      have hk := k.isLt
      unfold inArcIdArrBase inStartArrBase trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
      omega
    -- Extract placed sub-blocks from `hPlLoop` without unfolding `step4AInstrs`/`step4BInstrs`:
    have hPl3 : Placed code 3 (metaLoadInstrs (bits := bits) reg2 reg4 mIdxKCursor
        (by dsimp only [mIdxKCursor]; omega)) :=
      Placed_append_left (by unfold stage4LoopInstrs at hPlLoop; exact hPlLoop)
    have hPlR6 := Placed_append_right (by unfold stage4LoopInstrs at hPlLoop; exact hPlLoop)
    rw [show (metaLoadInstrs (bits := bits) reg2 reg4 mIdxKCursor (by dsimp only [mIdxKCursor]; omega)).length = 3 by rfl] at hPlR6
    have hPl6 : Placed code 6 (metaLoadInstrs (bits := bits) reg3 reg4 mIdxN
        (by dsimp only [mIdxN]; omega)) :=
      Placed_append_left hPlR6
    have hPlR9 := Placed_append_right hPlR6
    rw [show (metaLoadInstrs (bits := bits) reg3 reg4 mIdxN (by dsimp only [mIdxN]; omega)).length = 3 by rfl] at hPlR9
    have hPlR10 := Placed_append_right hPlR9
    rw [show ([ .branchLt reg2 reg3 10 1615 ] : List (Instr bits 15)).length = 1 by rfl] at hPlR10
    have hPl10 : Placed code 10 (metaLoadInstrs (bits := bits) reg3 reg4 mIdxOrderBase
        (by dsimp only [mIdxOrderBase]; omega)) :=
      Placed_append_left hPlR10
    have hPlR13 := Placed_append_right hPlR10
    rw [show (metaLoadInstrs (bits := bits) reg3 reg4 mIdxOrderBase (by dsimp only [mIdxOrderBase]; omega)).length = 3 by rfl] at hPlR13
    have hPlR15 := Placed_append_right hPlR13
    rw [show ([ .add reg3 reg3 reg2, .loadData reg3 reg3 ] : List (Instr bits 15)).length = 2 by rfl] at hPlR15
    have hPl15 : Placed code 15 (metaStoreInstrs (bits := bits) reg3 reg4 mIdxCurY
        (by dsimp only [mIdxCurY]; omega)) :=
      Placed_append_left hPlR15
    have hPlR18 := Placed_append_right hPlR15
    rw [show (metaStoreInstrs (bits := bits) reg3 reg4 mIdxCurY (by dsimp only [mIdxCurY]; omega)).length = 3 by rfl] at hPlR18
    have hPl18 : Placed code 18 (step4AInstrs (bits := bits) 18 h100) := Placed_append_left hPlR18
    have hPlR538 := Placed_append_right hPlR18
    rw [step4AInstrs_length] at hPlR538
    have hPl538 : Placed code 538 (step4BInstrs (bits := bits) 538 h100) := Placed_append_left hPlR538
    have hPlR1607 := Placed_append_right hPlR538
    rw [step4BInstrs_length] at hPlR1607
    have hPl1607 : Placed code 1607 (metaLoadInstrs (bits := bits) reg2 reg4 mIdxKCursor
        (by dsimp only [mIdxKCursor]; omega)) :=
      Placed_append_left hPlR1607
    have hPlR1610 := Placed_append_right hPlR1607
    rw [show (metaLoadInstrs (bits := bits) reg2 reg4 mIdxKCursor (by dsimp only [mIdxKCursor]; omega)).length = 3 by rfl] at hPlR1610
    have hPlR1611 := Placed_append_right hPlR1610
    rw [show ([ .add reg2 reg2 reg1 ] : List (Instr bits 15)).length = 1 by rfl] at hPlR1611
    have hPl1611 : Placed code 1611 (metaStoreInstrs (bits := bits) reg2 reg4 mIdxKCursor
        (by dsimp only [mIdxKCursor]; omega)) :=
      Placed_append_left hPlR1611
    have hPlR1614 := Placed_append_right hPlR1611
    rw [show (metaStoreInstrs (bits := bits) reg2 reg4 mIdxKCursor (by dsimp only [mIdxKCursor]; omega)).length = 3 by rfl] at hPlR1614
    -- Steps `3..17`: branch `< n`, load `y = orderKahn[idx]`, store `mIdxCurY := y`.
    let y : Vertex H := orderedVertexAt orderKahn sizeKahn ⟨idx, hIdxLt⟩
    have hRkY : rankKahn y = idx := hRkAt ⟨idx, hIdxLt⟩
    obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl3 (by omega) hpc hMeta.rMeta_eq (hOffsetFit mIdxKCursor (by decide)) hKCur
    have hM1 : (reg s1 rMeta).val = metaBase := by
      rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hMeta.rMeta_eq]
    obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl6 (by omega) hpc1 hM1 (hOffsetFit mIdxN (by decide))
      (by rw [hd1]; exact hMeta.meta_n)
    have h2_2 : (reg s2 reg2).val = idx := by
      rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
    have haBr : code[s2.pc]? = some (.branchLt reg2 reg3 10 1615) := by
      rw [hpc2]; exact hPlR9 0 _ rfl
    obtain ⟨s3, hs3Raw, hpc3, hr3, hd3⟩ := step_branchLt_at (input := input) haBr (by split <;> omega)
    have hs3 := steps_1_of_step hs3Raw
    rw [ite_eq_left (by rw [h2_2, h3_2]; exact hIdxLt)] at hpc3
    have hM3 : (reg s3 rMeta).val = metaBase := by
      rw [reg_of_regs_eq hr3, hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hM1]
    have h2_3 : (reg s3 reg2).val = idx := by rw [reg_of_regs_eq hr3, h2_2]
    obtain ⟨s4, hs4, hpc4, hd4, h3_4, hPres4⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl10 (by omega) hpc3 hM3 (hOffsetFit mIdxOrderBase (by decide))
      (by rw [hd3, hd2, hd1]; exact hMeta.meta_orderBase)
    have h2_4 : (reg s4 reg2).val = idx := by
      rw [hPres4 reg2 (by intro h; cases h) (by intro h; cases h), h2_3]
    have haAdd : code[s4.pc]? = some (.add reg3 reg3 reg2) := by
      rw [hpc4]; exact hPlR13 0 _ rfl
    obtain ⟨s5, hs5Raw, hpc5, h3_5, ho5, hd5⟩ := step_add_at (input := input) haAdd (by omega)
    have hs5 := steps_1_of_step hs5Raw
    have hOrdBnd : orderArrBase n N + idx < 2 ^ bits := by
      simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega
    have h3Val5 : (reg s5 reg3).val = orderArrBase n N + idx := by
      rw [h3_5, add_no_wrap _ _ (by rw [h3_4, h2_4]; exact hOrdBnd), h3_4, h2_4]
    obtain ⟨wy, hwy, hwyV⟩ := Option.map_eq_some_iff.mp (hOrd ⟨idx, hIdxLt⟩)
    have haLd : code[s5.pc]? = some (.loadData reg3 reg3) := by
      rw [hpc5, hpc4]; exact hPlR13 1 _ rfl
    obtain ⟨s6, hs6Raw, hpc6, h3_6, ho6, hd6⟩ := step_loadData_at (input := input) haLd (by omega)
      (by rw [h3Val5, hd5, hd4, hd3, hd2, hd1]; exact hwy)
    have hs6 := steps_1_of_step hs6Raw
    have h3Val6 : (reg s6 reg3).val = y.val := by rw [h3_6, hwyV]
    have hM6 : (reg s6 rMeta).val = metaBase := by
      rw [ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h),
        hPres4 rMeta (by intro h; cases h) (by intro h; cases h), hM3]
    obtain ⟨s7, hs7, hpc7, hAt7, hFr7, hPres7⟩ := run_metaStore_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl15 (by omega) (by rw [hpc6, hpc5, hpc4]) hM6
      (hOffsetFit mIdxCurY (by decide)) (lt_data_size (by dsimp only [mIdxCurY]; omega))
    have hFr7' : ∀ j, j ≠ metaBase + mIdxCurY → s7.data[j]? = st.data[j]? := fun j hj => by
      rw [hFr7 j hj, hd6, hd5, hd4, hd3, hd2, hd1]
    have h0_7 : (reg s7 reg0).val = 0 := by
      rw [hPres7 reg0 (by intro h; cases h), ho6 reg0 (by intro h; cases h),
        ho5 reg0 (by intro h; cases h), hPres4 reg0 (by intro h; cases h) (by intro h; cases h),
        reg_of_regs_eq hr3, hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
        hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero]
    have h1_7 : (reg s7 reg1).val = 1 := by
      rw [hPres7 reg1 (by intro h; cases h), ho6 reg1 (by intro h; cases h),
        ho5 reg1 (by intro h; cases h), hPres4 reg1 (by intro h; cases h) (by intro h; cases h),
        reg_of_regs_eq hr3, hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
        hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one]
    have hM7 : (reg s7 rMeta).val = metaBase := by rw [hPres7 rMeta (by intro h; cases h), hM6]
    have hMeta7 : MetaReady s7 n m N nGlobal :=
      hMeta.preserve hM7 h0_7 h1_7 (fun i hi => hFr7' (metaBase + i) (fun he => (by dsimp only [mIdxCurY]; omega : i ≠ mIdxCurY) (Nat.add_left_cancel he)))
    have hPreLen : Steps code input 15 st s7 :=
      ((hs1.append hs2).append hs3).append (((hs4.append hs5).append hs6).append hs7)
    -- Step `4A` (`18..537`):
    have hOKidx : LiveStoreOK B.F C.built.ref (liveBefore flat increasing covers rankArc r rankKahn idx) :=
      liveStoreOK_liveBefore flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout rankKahn rankArcKahn idx
    obtain ⟨kA, sA, hkA, hsA, hpcA, hMetaA, hValsY, hFrA⟩ := run_step4A (input := input)
      18 h100 hPl18 (by omega) flat increasing covers rankArc hIn hWork hFitRank rankArcKahn hRkLt
      (wFit := wFit) hLayout y hOKidx (fun _ _ => rfl)
      (fun w hw => by rw [hRkY] at hw; exact hw) s7 hpc7 hMeta7
      (by rw [hAt7, Option.map_some, h3Val6])
      (fun i hi => by
        rw [hFr7' (inStartArrBase n N + i) (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]
        exact hInStart i hi)
      (fun v hv k => by
        rw [hFr7' _ (hReadOff _ (hArcMeta v hv k) _)]
        exact hInArcs v hv k)
      (fun w => by
        rw [hFr7' _ (by have := w.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]
        exact hDep w)
      (fun w hw => by
        have hEq18 : ∀ j < 18, s7.data[storedBase N + 18 * w.val + j]? =
            st.data[storedBase N + 18 * w.val + j]? := fun j _ =>
          hFr7' _ (by have := w.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)
        have ho := hSt w hw
        have hAddr0 := hEq18 0 (by decide)
        simp only [Nat.add_zero] at hAddr0
        refine ⟨by rw [hAddr0]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
          mapWordsAt_frame (fun j _ => by rw [Nat.add_assoc]; exact hEq18 (2 + j) (by omega)) ho.2.2.1,
          mapWordsAt_frame (fun j _ => by rw [Nat.add_assoc]; exact hEq18 (10 + j) (by omega)) ho.2.2.2⟩)
      (fun q hq => by
        have hNeY : q.val ≠ y.val := by intro heq; have hqEq : q = y := Fin.ext heq; rw [hqEq, hRkY] at hq; omega
        have hEq6 : ∀ j < 6, s7.data[priorBase N + 6 * q.val + j]? = st.data[priorBase N + 6 * q.val + j]? := fun j _ =>
          hFr7' _ (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)
        have ho := hPriorDone q (by rw [hRkY] at hq; exact hq)
        exact valuesWordsAt_frame hEq6 ho)
      (by
        have hEq6 : ∀ j < 6, s7.data[priorBase N + 6 * y.val + j]? = st.data[priorBase N + 6 * y.val + j]? := fun j _ =>
          hFr7' _ (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)
        have ho := hPriorZero y (by rw [hRkY]; exact Nat.le_refl _)
        exact valuesWordsAt_frame hEq6 ho)
    -- Frame combining `st -> s7 -> sA`:
    have hFrA' : ∀ j, (j < priorBase N + 6 * y.val ∨
        (priorBase N + 6 * y.val + 6 ≤ j ∧ j < metaBase + mIdxCurY) ∨
        metaBase + 55 ≤ j) → sA.data[j]? = st.data[j]? := fun j hj => by
      rw [hFrA j (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; rcases hj with h | ⟨_, h⟩ | h <;> omega)]
      exact hFr7' j (by dsimp only [mIdxCurY] at *; rcases hj with h | ⟨_, h⟩ | h <;> unfold priorBase at * <;> omega)
    -- Step `4B` (`538..1606`):
    obtain ⟨hd, hHead, hLk⟩ := hTrig idx hIdxLt
    have hBeforeRead : priorBase N + 6 * y.val + 6 ≤ orderArrBase n N := by
      have := y.isLt
      unfold priorBase orderArrBase
      omega
    have hReadA (j : Nat) (hlo : orderArrBase n N ≤ j) (hhi : j < metaBase + mIdxCurY) :
        sA.data[j]? = st.data[j]? :=
      hFrA' j (Or.inr (Or.inl ⟨Nat.le_trans hBeforeRead hlo, hhi⟩))
    have hHeadA : (sA.data[trigHeadArrBase n N + idx]?).map Fin.val = some hd := by
      rw [hReadA _ (by unfold trigHeadArrBase topoRankArrBase; omega)
        (Nat.lt_of_lt_of_le (hHeadMeta idx hIdxLt) (Nat.le_add_right _ _))]
      exact hHead
    have hLkA : ListLinked sA.data (trigNextArrBase n N) N hd (buckets idx) :=
      ListLinked.frame (fun z hz =>
        hReadA _ (by unfold trigNextArrBase trigHeadArrBase topoRankArrBase; omega)
          (Nat.lt_of_lt_of_le (hNextMeta z ((hBucketsSpec idx hIdxLt).2 z hz).1)
            (Nat.le_add_right _ _))) hLk
    have hDepA : ∀ u : Fin N, (sA.data[u.val]?).map Fin.val = some (B.F.depthOf u.val) := fun u => by
      rw [hFrA' _ (Or.inl (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega))]; exact hDep u
    have hStA : ∀ u : Fin N, liveBefore flat increasing covers rankArc r rankKahn idx u.val →
        (sA.data[storedBase N + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (sA.data[storedBase N + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt sA.data (storedBase N + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt sA.data (storedBase N + 18 * u.val + 10) (C.built.ref u.val).jumpMap := fun u hu => by
      have hEq18 : ∀ j < 18, sA.data[storedBase N + 18 * u.val + j]? =
          st.data[storedBase N + 18 * u.val + j]? := fun j _ =>
        hFrA' _ (Or.inl (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega))
      have ho := hSt u hu
      have hAddr0 := hEq18 0 (by decide)
      simp only [Nat.add_zero] at hAddr0
      refine ⟨by rw [hAddr0]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
        mapWordsAt_frame (fun j _ => by rw [Nat.add_assoc]; exact hEq18 (2 + j) (by omega)) ho.2.2.1,
        mapWordsAt_frame (fun j _ => by rw [Nat.add_assoc]; exact hEq18 (10 + j) (by omega)) ho.2.2.2⟩
    have hPriorA : ∀ q : Fin n, rankKahn q ≤ idx →
        ValuesWordsAt sA.data (priorBase N + 6 * q.val) (C.built.model.wantBase q) := fun q hq => by
      by_cases hEqIdx : rankKahn q = idx
      · obtain ⟨jq, hjq⟩ := hOrdCov q
        have hJVal : jq.val = idx := by rw [← hRkAt jq, hjq, hEqIdx]
        have hJFin : jq = ⟨idx, hIdxLt⟩ := Fin.ext hJVal
        have hEqY : q = y := by rw [← hjq, hJFin]
        rw [hEqY]; exact hValsY
      · have hLtIdx : rankKahn q < idx := by omega
        have hNeY : q.val ≠ y.val := by intro heq; have hqEq : q = y := Fin.ext heq; rw [hqEq, hRkY] at hLtIdx; omega
        have hEq6 : ∀ j < 6, sA.data[priorBase N + 6 * q.val + j]? = st.data[priorBase N + 6 * q.val + j]? := fun j _ => by
          by_cases hLt : q.val < y.val
          · exact hFrA' _ (Or.inl (by omega))
          · exact hFrA' _ (Or.inr (Or.inl ⟨by omega, by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega⟩))
        have ho := hPriorDone q hLtIdx
        exact valuesWordsAt_frame hEq6 ho
    obtain ⟨kB, sB, hkB, hsB, hpcB, hMetaB, hStB, hFrB, hPJB⟩ := run_step4B (input := input)
      538 h100 hPl538 (by omega) flat increasing covers rankArc hIn hWork (wFit := wFit) hLayout
      rankArcKahn idx hIdxLt (buckets idx) (hBucketsSpec idx hIdxLt).1
      (fun w hw => (hBucketsSpec idx hIdxLt).2 w hw) hOKidx sA hpcA hMetaA
      (by rw [hReadA (metaBase + mIdxKCursor) (by omega) (by dsimp only [mIdxKCursor, mIdxCurY]; omega)]; exact hKCur)
      hd hHeadA hLkA hDepA hStA
      (fun w hw => by
        have hwLt := ((hBucketsSpec idx hIdxLt).2 w hw).1
        have hEq2 : ∀ k < 2, sA.data[storedBase N + 18 * w + k]? = st.data[storedBase N + 18 * w + k]? := fun k _ =>
          hFrA' _ (Or.inl (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega))
        have ho := hPJ ⟨w, hwLt⟩
        have hAddr0 := hEq2 0 (by decide)
        simp only [Nat.add_zero] at hAddr0
        exact ⟨by rw [hAddr0]; exact ho.1, by rw [hEq2 1 (by decide)]; exact ho.2⟩)
      hPriorA
    -- Increment `mIdxKCursor` and jump to loop start `3` (`1607..1614`, 8 steps):
    have hFrB' : ∀ j, (j < storedBase N ∨
        (priorBase N ≤ j ∧ j < metaBase + mIdxCCursor) ∨ metaBase + 64 ≤ j) →
          sB.data[j]? = sA.data[j]? := hFrB
    obtain ⟨s8, hs8, hpc8, hd8, h2_8, hPres8⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl1607 (by omega) hpcB hMetaB.rMeta_eq (hOffsetFit mIdxKCursor (by decide))
      (by
        rw [hFrB' (metaBase + mIdxKCursor) (Or.inr (Or.inl ⟨by omega, by dsimp only [mIdxKCursor, mIdxCCursor]; omega⟩)),
          hReadA (metaBase + mIdxKCursor) (by omega) (by dsimp only [mIdxKCursor, mIdxCurY]; omega)]
        exact hKCur)
    have hM8 : (reg s8 rMeta).val = metaBase := by
      rw [hPres8 rMeta (by intro h; cases h) (by intro h; cases h), hMetaB.rMeta_eq]
    have h1_8 : (reg s8 reg1).val = 1 := by
      rw [hPres8 reg1 (by intro h; cases h) (by intro h; cases h), hMetaB.r1_one]
    have h0_8 : (reg s8 reg0).val = 0 := by
      rw [hPres8 reg0 (by intro h; cases h) (by intro h; cases h), hMetaB.r0_zero]
    have haInc : code[s8.pc]? = some (.add reg2 reg2 reg1) := by
      rw [hpc8]; exact hPlR1610 0 _ rfl
    obtain ⟨s9, hs9Raw, hpc9, h2_9, ho9, hd9⟩ := step_add_at (input := input) haInc (by omega)
    have hs9 := steps_1_of_step hs9Raw
    have h2Val9 : (reg s9 reg2).val = idx + 1 := by
      rw [h2_9, add_no_wrap _ _ (by rw [h2_8, h1_8]; omega), h2_8, h1_8]
    have hM9 : (reg s9 rMeta).val = metaBase := by
      rw [ho9 rMeta (by intro h; cases h), hM8]
    obtain ⟨s10, hs10, hpc10, hAt10, hFr10, hPres10⟩ := run_metaStore_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl1611 (by omega) (by rw [hpc9, hpc8]) hM9
      (hOffsetFit mIdxKCursor (by decide)) (lt_data_size (by dsimp only [mIdxKCursor]; omega))
    have haGoto : code[s10.pc]? = some (.goto 3) := by
      rw [hpc10]; exact hPlR1614 0 _ rfl
    obtain ⟨s11, hs11Raw, hpc11, hr11, hd11⟩ := step_goto_at (input := input) haGoto (by omega)
    have hs11 := steps_1_of_step hs11Raw
    have hFr11_B : ∀ j, j ≠ metaBase + mIdxKCursor → s11.data[j]? = sB.data[j]? := fun j hj => by
      rw [hd11, hFr10 j hj, hd9, hd8]
    have hMeta11 : MetaReady s11 n m N nGlobal :=
      hMetaB.preserve
        (by rw [reg_of_regs_eq hr11, hPres10 rMeta (by intro h; cases h), hM9])
        (by rw [reg_of_regs_eq hr11, hPres10 reg0 (by intro h; cases h), ho9 reg0 (by intro h; cases h), h0_8])
        (by rw [reg_of_regs_eq hr11, hPres10 reg1 (by intro h; cases h), ho9 reg1 (by intro h; cases h), h1_8])
        (fun i hi => hFr11_B (metaBase + i) (fun he => (by dsimp only [mIdxKCursor]; omega : i ≠ mIdxKCursor) (Nat.add_left_cancel he)))
    -- Apply `ih` at `(rem, idx + 1, s11)`:
    have hReadAB (j : Nat) (hlo : orderArrBase n N ≤ j) (hhi : j < metaBase) :
        s11.data[j]? = st.data[j]? := by
      rw [hFr11_B j (hReadOff j hhi _),
        hFrB' j (Or.inr (Or.inl ⟨by unfold priorBase orderArrBase at *; omega,
          Nat.lt_of_lt_of_le hhi (Nat.le_add_right _ _)⟩)),
        hReadA j hlo (Nat.lt_of_lt_of_le hhi (Nat.le_add_right _ _))]
    have hPriorAB (q : Fin n) (j : Nat) (hj : j < 6) :
        s11.data[priorBase N + 6 * q.val + j]? = sA.data[priorBase N + 6 * q.val + j]? := by
      have hlt := Nat.lt_of_lt_of_le (hPreviousLt q j hj) hPreviousMeta
      rw [hFr11_B _ (hReadOff _ hlt _),
        hFrB' _ (Or.inr (Or.inl ⟨by omega, Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)⟩))]
    have hSt11 : ∀ u : Fin N, liveBefore flat increasing covers rankArc r rankKahn (idx + 1) u.val →
        (s11.data[storedBase N + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (s11.data[storedBase N + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt s11.data (storedBase N + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt s11.data (storedBase N + 18 * u.val + 10) (C.built.ref u.val).jumpMap := fun u hu => by
      have hu' := liveBefore_step flat increasing covers rankArc r rankKahn buckets hBucketsCover idx u.val hu
      have hEq18 : ∀ j < 18, s11.data[storedBase N + 18 * u.val + j]? =
          sB.data[storedBase N + 18 * u.val + j]? := fun j _ =>
        hFr11_B _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)
      have ho := hStB u hu'
      have hAddr0 := hEq18 0 (by decide)
      simp only [Nat.add_zero] at hAddr0
      refine ⟨by rw [hAddr0]; exact ho.1, by rw [hEq18 1 (by decide)]; exact ho.2.1,
        mapWordsAt_frame (fun j _ => by rw [Nat.add_assoc]; exact hEq18 (2 + j) (by omega)) ho.2.2.1,
        mapWordsAt_frame (fun j _ => by rw [Nat.add_assoc]; exact hEq18 (10 + j) (by omega)) ho.2.2.2⟩
    have hPriorDone11 : ∀ q : Fin n, rankKahn q < idx + 1 →
        ValuesWordsAt s11.data (priorBase N + 6 * q.val) (C.built.model.wantBase q) := fun q hq =>
      valuesWordsAt_frame (hPriorAB q) (hPriorA q (by omega))
    have hPriorZero11 : ∀ q : Fin n, idx + 1 ≤ rankKahn q →
        ValuesWordsAt s11.data (priorBase N + 6 * q.val) zero := fun q hq => by
      have hNeY : q.val ≠ y.val := by intro heq; have hqEq : q = y := Fin.ext heq; rw [hqEq, hRkY] at hq; omega
      have hEq6 : ∀ j < 6, s11.data[priorBase N + 6 * q.val + j]? =
          st.data[priorBase N + 6 * q.val + j]? := fun j hj => by
        rw [hPriorAB q j hj]
        by_cases hLt : q.val < y.val
        · exact hFrA' _ (Or.inl (by omega))
        · exact hFrA' _ (Or.inr (Or.inl ⟨by omega, by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega⟩))
      have ho := hPriorZero q (by omega)
      exact valuesWordsAt_frame hEq6 ho
    obtain ⟨kRest, t, hkRest, hsRest, hpct, hMetaT, hDepT, hStT, hPriorT⟩ := ih (idx + 1) s11
      (by omega) hpc11 hMeta11
      (by rw [hd11, hAt10, Option.map_some, h2Val9])
      (fun i => by rw [hReadAB _ (by omega) (hOrderMeta i)]; exact hOrd i)
      (fun i hi => by
        rw [hReadAB _ (by unfold inStartArrBase trigNextArrBase trigHeadArrBase topoRankArrBase; omega)
          (hStartMeta i hi)]
        exact hInStart i hi)
      (fun v hv k => by
        rw [hReadAB _ (by unfold inArcIdArrBase inStartArrBase trigNextArrBase trigHeadArrBase topoRankArrBase; omega)
          (hArcMeta v hv k)]
        exact hInArcs v hv k)
      (fun tr htr => by
        obtain ⟨hdTr, hHeadTr, hLkTr⟩ := hTrig tr htr
        refine ⟨hdTr, ?_, ListLinked.frame (fun z hz => ?_) hLkTr⟩
        · rw [hReadAB _ (by unfold trigHeadArrBase topoRankArrBase; omega) (hHeadMeta tr htr)]
          exact hHeadTr
        · exact hReadAB (trigNextArrBase n N + z)
            (by unfold trigNextArrBase trigHeadArrBase topoRankArrBase; omega)
            (hNextMeta z ((hBucketsSpec tr htr).2 z hz).1))
      (fun u => by
        rw [hFr11_B _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega),
          hFrB _ (Or.inl (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega))]
        exact hDepA u)
      (fun u => by
        have hEq2 : ∀ j < 2, s11.data[storedBase N + 18 * u.val + j]? =
            st.data[storedBase N + 18 * u.val + j]? := fun j hj => by
          rw [hFr11_B _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega),
            hPJB u.val u.isLt j hj,
            hFrA' _ (Or.inl (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega))]
        have ho := hPJ u
        have hAddr0 := hEq2 0 (by decide)
        simp only [Nat.add_zero] at hAddr0
        exact ⟨by rw [hAddr0]; exact ho.1, by rw [hEq2 1 (by decide)]; exact ho.2⟩)
      hSt11 hPriorDone11 hPriorZero11
    have hBodySteps : Steps code input (15 + kA + kB + 8) st s11 :=
      ((hPreLen.append hsA).append hsB).append (((hs8.append hs9).append hs10).append hs11)
    have hLGe1 : 1 ≤ OracleContract.L H.vertexCount := OracleContract.one_le_L H.vertexCount
    have hSumDeg : remDegIn H orderKahn sizeKahn idx (rem + 1) =
        degIn H y.val + remDegIn H orderKahn sizeKahn (idx + 1) rem := by
      rw [remDegIn, dite_eq_left hIdxLt]
    have hSumBkt : remBucketsLen buckets idx (rem + 1) =
        (buckets idx).length + remBucketsLen buckets (idx + 1) rem := by
      rw [remBucketsLen]
    have hStepBound : (15 + kA + kB + 8) + kRest ≤
        (750 * (remDegIn H orderKahn sizeKahn idx (rem + 1) + (rem + 1)) +
          1620 * remBucketsLen buckets idx (rem + 1)) * OracleContract.L H.vertexCount + 7 := by
      rw [hSumDeg, hSumBkt]
      have hMulA : 700 * (degIn H y.val + 1) * OracleContract.L n + 50 * OracleContract.L n =
          (700 * (degIn H y.val + 1) + 50) * OracleContract.L n := by
        rw [Nat.add_mul]
      have h50Ge41 : 41 ≤ 50 * OracleContract.L n := by
        exact Nat.le_trans (by decide : 41 ≤ 50 * 1) (Nat.mul_le_mul_left 50 hLGe1)
      have hLe750 : 700 * (degIn H y.val + 1) * OracleContract.L n + 41 ≤
          750 * (degIn H y.val + 1) * OracleContract.L n := by
        have hInc : 700 * (degIn H y.val + 1) + 50 ≤ 750 * (degIn H y.val + 1) := by
          have : 1 ≤ degIn H y.val + 1 := Nat.succ_pos _
          omega
        exact Nat.le_trans (by rw [← hMulA]; omega) (Nat.mul_le_mul_right _ hInc)
      have hSplit :
          (750 * (degIn H y.val + remDegIn H orderKahn sizeKahn (idx + 1) rem + (rem + 1)) +
            1620 * ((buckets idx).length + remBucketsLen buckets (idx + 1) rem)) *
              OracleContract.L n =
          750 * (degIn H y.val + 1) * OracleContract.L n +
          1620 * (buckets idx).length * OracleContract.L n +
          (750 * (remDegIn H orderKahn sizeKahn (idx + 1) rem + rem) +
            1620 * remBucketsLen buckets (idx + 1) rem) * OracleContract.L n := by
        have h1 : degIn H y.val + remDegIn H orderKahn sizeKahn (idx + 1) rem + (rem + 1) =
            (degIn H y.val + 1) + (remDegIn H orderKahn sizeKahn (idx + 1) rem + rem) := by omega
        simp only [h1, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      change _ ≤ (750 * (degIn H y.val + remDegIn H orderKahn sizeKahn (idx + 1) rem + (rem + 1)) +
        1620 * ((buckets idx).length + remBucketsLen buckets (idx + 1) rem)) * OracleContract.L n + 7
      rw [hSplit]
      change kA ≤ 700 * (degIn H y.val + 1) * OracleContract.L n at hkA
      change kB ≤ 1620 * (buckets idx).length * OracleContract.L n + 18 at hkB
      change kRest ≤ (750 * (remDegIn H orderKahn sizeKahn (idx + 1) rem + rem) +
        1620 * remBucketsLen buckets (idx + 1) rem) * OracleContract.L n + 7 at hkRest
      omega
    exact ⟨(15 + kA + kB + 8) + kRest, t, hStepBound, hBodySteps.append hsRest,
      hpct, hMetaT, hDepT, hStT, hPriorT⟩

theorem run_stage4 {input : Input DomL}
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
    (hFitRank : ∀ x : Fin H.origVertexCount, entryRank x < 2 ^ bits)
    {orderKahn : Array (Vertex H)} {sizeKahn : orderKahn.size = H.vertexCount}
    {rankKahn : Vertex H → Nat} {buckets : Nat → List Nat}
    {st0 : State DomL}
    (hS3 : Stage3Ready st0 flat increasing covers rankArc r nGlobal orderKahn sizeKahn rankKahn buckets)
    {wFit : Width bits (max r.out.tables.next nGlobal)}
    (hLayout : r.out.tables.next + 18 * r.out.tables.next ≤ 2 ^ bits)
    : let C := buildActualSealedContract H flat increasing covers rankArc r entryRank
        (fun x => by have := hIn.hRank_lt x; omega) wFit hLayout
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    ∃ steps t,
      steps ≤ 2400 * (H.vertexCount + H.arcCount + 1) * OracleContract.L H.vertexCount ∧
      run (stage4Phase (hi := hi) (hw := hw) h100).code input steps (Phase.initial st0) =
        some ⟨t, steps⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ u : Fin r.out.tables.next,
        (t.data[u.val]?).map Fin.val = some (B.F.depthOf u.val)) ∧
      (∀ u : Fin r.out.tables.next,
        (t.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
        (t.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
        MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
        MapWordsAt t.data (storedBase r.out.tables.next + 18 * u.val + 10) (C.built.ref u.val).jumpMap) ∧
      (∀ q : Fin H.vertexCount,
        ValuesWordsAt t.data (priorBase r.out.tables.next + 6 * q.val) (C.built.model.wantBase q)) := by
  intro C B
  let ph := stage4Phase (hi := hi) (hw := hw) h100
  have hCodeLen : ph.code.size = 1616 := by
    dsimp only [ph, stage4Phase]
    rw [codeSize_mkHaltPhase, stage4Instrs_length]
  have hPlFull : Placed ph.code 0 (stage4Instrs (bits := bits) h100) :=
    Placed_mkHaltPhase _ _
  have hPl0 : Placed ph.code 0 (metaStoreInstrs (bits := bits) reg0 reg2 mIdxKCursor
      (by dsimp only [mIdxKCursor]; omega)) :=
    Placed_append_left (by unfold stage4Instrs at hPlFull; exact hPlFull)
  have hPlLoop : Placed ph.code 3 (stage4LoopInstrs (bits := bits) h100) :=
    Placed_append_right (by unfold stage4Instrs at hPlFull; exact hPlFull)
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let metaBase := metaArrBase n m N
  have hNLe : N ≤ n + 1 := (B_next_pos flat increasing covers rankArc r).2
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hBoundMeta : metaBase + 64 ≤ workCap := by
    dsimp only [metaBase] at hMetaEq ⊢; unfold exitWorkCap at hWork; omega
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hOffsetFit (off : Nat) (hof : off < 64) : metaBase + off < 2 ^ bits := by omega
  have hReadOff (j : Nat) (hj : j < metaBase) (off : Nat) : j ≠ metaBase + off := by omega
  have hRecordLimit : storedBase N + 18 * N = priorBase N := by
    unfold storedBase priorBase
    omega
  have hRecordLt (u : Fin N) (j : Nat) (hj : j < 18) :
      storedBase N + 18 * u.val + j < priorBase N := by
    have := u.isLt
    omega
  have hPreviousLt (q : Fin n) (j : Nat) (hj : j < 6) :
      priorBase N + 6 * q.val + j < orderArrBase n N := by
    have := q.isLt
    unfold priorBase orderArrBase
    omega
  have hPreviousMeta : orderArrBase n N ≤ metaBase := by unfold orderArrBase; omega
  have hPriorMeta : priorBase N ≤ metaBase := by unfold priorBase; omega
  have hOrderMeta (i : Fin n) : orderArrBase n N + i.val < metaBase := by
    have := i.isLt
    unfold orderArrBase
    omega
  have hHeadMeta (i : Nat) (hi : i < n) : trigHeadArrBase n N + i < metaBase := by
    unfold trigHeadArrBase topoRankArrBase orderArrBase
    omega
  have hNextMeta (i : Nat) (hi : i < N) : trigNextArrBase n N + i < metaBase := by
    unfold trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
    omega
  have hStartMeta (i : Nat) (hi : i ≤ n) : inStartArrBase n N + i < metaBase := by
    unfold inStartArrBase trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
    omega
  have hArcMeta (v : Nat) (hv : v < n) (k : Fin (degIn H v)) :
      inArcIdArrBase n N + (prefixIn H v + k.val) < metaBase := by
    have hPrefix := prefixIn_mono H (show v + 1 ≤ H.vertexCount by change v + 1 ≤ n; omega)
    rw [prefixIn_vertexCount] at hPrefix
    change prefixIn H v + degIn H v ≤ m at hPrefix
    have hk := k.isLt
    unfold inArcIdArrBase inStartArrBase trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
    omega
  have hK := hS3.kahn_ready
  have hF := hK.forest_ready
  have hMInit : MetaReady (Phase.initial st0) n m N nGlobal :=
    hF.meta_ready.preserve hF.meta_ready.rMeta_eq hF.meta_ready.r0_zero hF.meta_ready.r1_one
      (fun _ _ => rfl)
  obtain ⟨s1, hs1, hpc1, hAt1, hFr1, hPres1⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) rfl hMInit.rMeta_eq (hOffsetFit mIdxKCursor (by decide))
    (lt_data_size (by dsimp only [mIdxKCursor]; omega))
  have hMeta1 : MetaReady s1 n m N nGlobal :=
    hMInit.preserve (by rw [hPres1 rMeta (by intro h; cases h), hMInit.rMeta_eq])
      (by rw [hPres1 reg0 (by intro h; cases h), hMInit.r0_zero])
      (by rw [hPres1 reg1 (by intro h; cases h), hMInit.r1_one])
      (fun i hi => hFr1 (metaBase + i) (fun he => (by dsimp only [mIdxKCursor]; omega : i ≠ mIdxKCursor) (Nat.add_left_cancel he)))
  have hMod : C.built.model = actualModel B entryRank rankArc flat := C.built.model_eq
  have hSt1 : ∀ u : Fin N, liveBefore flat increasing covers rankArc r rankKahn 0 u.val →
      (s1.data[storedBase N + 18 * u.val]?).map Fin.val = some (C.built.ref u.val).parent ∧
      (s1.data[storedBase N + 18 * u.val + 1]?).map Fin.val = some (C.built.ref u.val).jump ∧
      MapWordsAt s1.data (storedBase N + 18 * u.val + 2) (C.built.ref u.val).parentMap ∧
      MapWordsAt s1.data (storedBase N + 18 * u.val + 10) (C.built.ref u.val).jumpMap := by
    intro u ⟨huLt, huCond⟩
    have hSeed : u.val = 0 ∨ B.F.parentOf u.val = 0 := by
      rcases huCond with h | h | ⟨Pc, _, hLt⟩
      · exact Or.inl h
      · exact Or.inr h
      · omega
    have hRefSeed : C.built.ref u.val = seedRecord :=
      actualOld_seed (r := r) B n u.val hSeed
    have hLiveU := C.built.all_live u.val (B.G.size_eq.symm ▸ huLt)
    have hParEq : (C.built.ref u.val).parent = B.F.parentOf u.val :=
      C.built.decoded.parent_eq u.val hLiveU
    have hJumpEq : (C.built.ref u.val).jump = B.F.jumpOf u.val :=
      C.built.decoded.jump_eq u.val hLiveU
    have hPM : (C.built.ref u.val).parentMap = Map.identity := by rw [hRefSeed]; rfl
    have hJM : (C.built.ref u.val).jumpMap = Map.identity := by rw [hRefSeed]; rfl
    have hMaps := seed_maps_to_mapWordsAt (addr := storedBase N + 18 * u.val + 2) (fun i hi => by
      have hlt : storedBase N + 18 * u.val + 2 + i < metaBase := by
        have hRecord := hRecordLt u (2 + i) (by omega)
        rw [Nat.add_assoc]
        exact Nat.lt_of_lt_of_le hRecord hPriorMeta
      rw [hFr1 _ (hReadOff _ hlt _)]
      exact hS3.seed_maps u.val u.isLt i hi)
    refine ⟨?_, ?_, by rw [hPM]; exact hMaps.1, by rw [hJM]; exact hMaps.2⟩
    · rw [hParEq, hFr1 _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]
      exact hF.parent_at u
    · rw [hJumpEq, hFr1 _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]
      exact hF.jump_at u
  obtain ⟨kLoop, t, hkLoop, hsLoop, hpct, hMetaT, hDepT, hStT, hPriorT⟩ := stage4Loop_spec (input := input)
    h100 hPlLoop (by omega) flat increasing covers rankArc hIn hWork hFitRank
    hK.order_covers hK.rank_at hK.rank_arc hS3.buckets_spec hS3.buckets_cover
    (wFit := wFit) hLayout n 0 s1 (by simp [n]) hpc1 hMeta1
    (by rw [hAt1, Option.map_some, hMInit.r0_zero])
    (fun i => by rw [hFr1 _ (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]; exact hK.order_mem i)
    (fun i hi => by rw [hFr1 _ (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]; exact hK.inStart_mem i hi)
    (fun v hv k => by rw [hFr1 _ (hReadOff _ (hArcMeta v hv k) _)]; exact hK.inArcId_mem v hv k)
    (fun tr htr => by
      obtain ⟨hdTr, hHeadTr, hLkTr⟩ := hS3.buckets_linked tr htr
      refine ⟨hdTr, ?_, ListLinked.frame (fun z hz => ?_) hLkTr⟩
      · rw [hFr1 _ (hReadOff _ (hHeadMeta tr htr) _)]
        exact hHeadTr
      · exact hFr1 _ (hReadOff _ (hNextMeta z ((hS3.buckets_spec tr htr).2 z hz).1) _))
    (fun u => by rw [hFr1 _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]; exact hF.depth_at u)
    (fun u => by
      rw [hFr1 _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega),
        hFr1 _ (by have := u.isLt; simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)]
      exact ⟨hF.parent_at u, hF.jump_at u⟩)
    hSt1 (fun q hq => by omega)
    (fun q _ => by
      have hEq6 : ∀ i < 6, s1.data[priorBase N + 6 * q.val + i]? =
          st0.data[priorBase N + 6 * q.val + i]? := fun i _ =>
        hFr1 _ (by simp only [metaBase, n, m, N, storedBase, priorBase, orderArrBase, topoRankArrBase, trigHeadArrBase, trigNextArrBase, inStartArrBase, inArcIdArrBase, metaArrBase, mIdxCCursor, mIdxKCursor, mIdxCurY, mIdxCurOwner, mIdxEvalU, mIdxN] at *; omega)
      have hAddr0 := hEq6 0 (by decide)
      simp only [Nat.add_zero] at hAddr0
      refine ⟨⟨by rw [hAddr0]; exact hS3.prior_zero q.val q.isLt 0 (by decide),
          by rw [hEq6 1 (by decide)]; exact hS3.prior_zero q.val q.isLt 1 (by decide),
          by rw [hEq6 2 (by decide)]; exact hS3.prior_zero q.val q.isLt 2 (by decide)⟩,
        ⟨by rw [hEq6 3 (by decide)]; exact hS3.prior_zero q.val q.isLt 3 (by decide),
          by rw [hEq6 4 (by decide)]; exact hS3.prior_zero q.val q.isLt 4 (by decide),
          by rw [hEq6 5 (by decide)]; exact hS3.prior_zero q.val q.isLt 5 (by decide)⟩⟩)
  have hHalt := haltAt_mkHaltPhase (hi := hi) (hw := hw)
    (stage4Instrs (bits := bits) h100) (stage4Instrs_nonHalt (bits := bits) h100)
    (by rw [hpct, stage4Instrs_length]) (input := input)
  have hDegSum : remDegIn H orderKahn sizeKahn 0 n ≤ m :=
    remDegIn_le_arcCount orderKahn sizeKahn hK.order_nodup
  have hBktSum : remBucketsLen buckets 0 n ≤ N :=
    remBucketsLen_le_next r rankKahn buckets (fun tr htr =>
      ⟨(hS3.buckets_spec tr htr).1, fun w hw =>
        ⟨((hS3.buckets_spec tr htr).2 w hw).1, ((hS3.buckets_spec tr htr).2 w hw).2.2⟩⟩)
  have hLGe1 : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hAllSteps : 3 + kLoop + 1 ≤ 2400 * (n + m + 1) * OracleContract.L n := by
    have hCoef : 750 * (remDegIn H orderKahn sizeKahn 0 n + n) +
        1620 * remBucketsLen buckets 0 n + 11 ≤ 2400 * (n + m + 1) := by
      have := large
      omega
    have hMul := Nat.mul_le_mul_right (OracleContract.L n) hCoef
    have h11 : 11 ≤ 11 * OracleContract.L n := by simpa using Nat.mul_le_mul_left 11 hLGe1
    have h10 : 10 ≤ 10 * OracleContract.L n := by simpa using Nat.mul_le_mul_left 10 hLGe1
    have hDistrib : (750 * (remDegIn H orderKahn sizeKahn 0 n + n) +
        1620 * remBucketsLen buckets 0 n + 11) * OracleContract.L n =
        (750 * (remDegIn H orderKahn sizeKahn 0 n + n) +
          1620 * remBucketsLen buckets 0 n) * OracleContract.L n + 11 * OracleContract.L n := by
      rw [Nat.add_mul]
    change kLoop ≤ (750 * (remDegIn H orderKahn sizeKahn 0 n + n) +
      1620 * remBucketsLen buckets 0 n) * OracleContract.L n + 7 at hkLoop
    omega
  exact ⟨3 + kLoop + 1, t, hAllSteps, (hs1.append hsLoop).halts hHalt, hMetaT, hDepT, hStT, hPriorT⟩

end Stage4LoopProof

end Stage4Phase

end PaperB.RamProgram.ExitSummaryBuild
