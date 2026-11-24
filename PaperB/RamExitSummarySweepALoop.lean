module

public import PaperB.RamExitSummarySweepAArcFull

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

/-! Induction through the incoming-arc fold at one quotient vertex. -/

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

private theorem list_drop_eq_cons {α : Type} :
    ∀ (xs : List α) (j : Nat) (hj : j < xs.length),
      xs.drop j = xs[j] :: xs.drop (j + 1)
  | [], _, hj => False.elim (Nat.not_lt_zero _ hj)
  | _ :: _, 0, _ => rfl
  | _ :: xs, j + 1, hj => by
    simp only [List.drop_succ_cons, List.getElem_cons_succ]
    exact list_drop_eq_cons xs j (Nat.lt_of_succ_lt_succ hj)

theorem step4A_loop_spec {code : Program DomL} {input : Input DomL}
    (loopPc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code loopPc (step4ALoopInstrs (bits := bits) loopPc h100))
    (hSz : loopPc + 406 < code.size)
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
    {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (ok : LiveStoreOK F ref live)
    (hFSize : F.size = r.out.tables.next)
    (B := buildActualSweepBundle H flat increasing covers rankArc r)
    (hFEq : F = B.F)
    (y : Vertex H) (ownerSlot : Nat) (hOwnPos : 0 < ownerSlot) (hOwnLt : ownerSlot < r.out.tables.next)
    (Bcut : CutPair H) (baseFn : Vertex H → Values)
    (hInStartY : prefixIn H y.val + degIn H y.val = prefixIn H (y.val + 1))
    (hEndLe : prefixIn H (y.val + 1) ≤ H.arcCount) :
    ∀ (rem j : Nat) (acc : Values) (st : State DomL),
      j + rem = degIn H y.val →
      st.pc = loopPc →
      MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr]?).map Fin.val =
        some (prefixIn H y.val + j) →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcEnd]?).map Fin.val =
        some (prefixIn H (y.val + 1)) →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48]?).map Fin.val = some Bcut.fst.val →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 49]?).map Fin.val = some Bcut.snd.val →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 50]?).map Fin.val =
        some (r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 51]?).map Fin.val =
        some (r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + 52]?).map Fin.val =
        some (F.depthOf ownerSlot) →
      ValuesWordsAt st.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0) acc →
      (∀ q : Fin H.vertexCount, q.val < H.vertexCount → ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * q.val) (baseFn q) ∨
        ¬ (∃ e ∈ (inArcsPrefix H H.arcCount y.val).drop j, ∃ he : e < H.arcCount, (rawOccurrence H ⟨e, he⟩).1 = q)) →
      (∀ k : Fin (degIn H y.val),
        (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H y.val + k.val)]?).map Fin.val =
          some ((inArcsPrefix H H.arcCount y.val)[k.val]'(by rw [inArcsPrefix_length]; exact k.isLt))) →
      (∀ w : Fin r.out.tables.next, (st.data[w.val]?).map Fin.val = some (F.depthOf w.val)) →
      (∀ w : Fin r.out.tables.next, live w.val →
        (st.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
        (st.data[storedBase r.out.tables.next + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
        MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 2) (ref w.val).parentMap ∧
        MapWordsAt st.data (storedBase r.out.tables.next + 18 * w.val + 10) (ref w.val).jumpMap) →
      (∀ e ∈ (inArcsPrefix H H.arcCount y.val).drop j, ∃ he : e < H.arcCount,
        let u := (rawOccurrence H ⟨e, he⟩).1
        let v := (selectors (orderedConfig p large) r.out).label u
        let hvLt : v < r.out.tables.next := B.G.size_eq ▸ B.E.label_lt u True.intro
        u.val ≠ Bcut.fst.val → u.val ≠ Bcut.snd.val → 0 < v →
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) ≤
          r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) →
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) <
          r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) →
        live v) →
      ∃ steps t, steps ≤ 700 * rem * OracleContract.L H.vertexCount + 7 ∧
        Steps code input steps st t ∧ t.pc = loopPc + 406 ∧
        MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
        ValuesWordsAt t.data (metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxAcc0)
          (((inArcsPrefix H H.arcCount y.val).drop j).foldl
            (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn) acc) ∧
        (∀ w, (w < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr ∨
            (metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ w ∧
              w < metaArrBase H.vertexCount H.arcCount r.out.tables.next + 53) ∨
            metaArrBase H.vertexCount H.arcCount r.out.tables.next + 55 ≤ w) →
          t.data[w]? = st.data[w]?) := by
  intro rem
  induction rem with
  | zero =>
    intro j acc st hSum hpc hMeta hPtr hEnd h48 h49 h50 h51 h52 hAcc hBases hArcIds hDep hSt hLives
    have hLen : (inArcsPrefix H H.arcCount y.val).length ≤ j := by
      rw [inArcsPrefix_length]; change degIn H y.val ≤ j; omega
    rw [List.drop_eq_nil_of_le hLen, List.foldl_nil]
    have hMetaBase : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 64 ≤ workCap := by
      have hM := metaArrBase_eq H.vertexCount H.arcCount r.out.tables.next
      have hNLe := (B_next_pos flat increasing covers rankArc r).2
      unfold exitWorkCap at hWork; omega
    have hWorkFit : workCap ≤ 2 ^ bits := hw
    have hRM := hMeta.rMeta_eq
    have hDecode := step4A_decode_placed hPl
    have hPl0 : Placed code loopPc (metaLoadInstrs (bits := bits) reg2 reg4 mIdxArcPtr (by dsimp only [mIdxArcPtr]; omega)) :=
      Placed_window hDecode 0 rfl
    obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl0 (by omega) hpc hRM (by dsimp only [mIdxArcPtr]; omega) hPtr
    have hRM1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hRM]
    have hPl1 : Placed code (loopPc + 3) (metaLoadInstrs (bits := bits) reg3 reg4 mIdxArcEnd (by dsimp only [mIdxArcEnd]; omega)) :=
      Placed_window hDecode 3 rfl
    obtain ⟨s2, hs2, hpc2, hd2, h3_2, hPres2⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc1 hRM1 (by dsimp only [mIdxArcEnd]; omega) (by rw [hd1]; exact hEnd)
    have h2_2 : (reg s2 reg2).val = prefixIn H y.val + j := by
      rw [hPres2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
    have haBr : code[s2.pc]? = some (.branchLt reg2 reg3 (loopPc + 7) (loopPc + 406)) := by
      rw [hpc2]; exact hDecode 6 _ rfl
    obtain ⟨t, ht, hpct, hrt, hdt⟩ := step_branchLt_at (input := input) haBr (by split <;> omega)
    rw [ite_eq_right (by rw [h2_2, h3_2]; omega)] at hpct
    have hrTF := reg_of_regs_eq hrt
    have hdT : t.data = st.data := by rw [hdt, hd2, hd1]
    refine ⟨7, t, by omega, (hs1.append hs2).append (steps_1_of_step ht), hpct,
      hMeta.preserve (by rw [hrTF, hPres2 rMeta (by intro h; cases h) (by intro h; cases h), hRM1])
        (by rw [hrTF, hPres2 reg0 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero])
        (by rw [hrTF, hPres2 reg1 (by intro h; cases h) (by intro h; cases h),
          hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one])
        (fun i hi => by rw [hdT]),
      by rw [hdT]; exact hAcc, fun _ _ => by rw [hdT]⟩
  | succ rem ih =>
    intro j acc st hSum hpc hMeta hPtr hEnd h48 h49 h50 h51 h52 hAcc hBases hArcIds hDep hSt hLives
    have hjLt : j < degIn H y.val := by omega
    let e := (inArcsPrefix H H.arcCount y.val)[j]'(by rw [inArcsPrefix_length]; exact hjLt)
    have heMem : e ∈ inArcsPrefix H H.arcCount y.val := List.getElem_mem _
    have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount y.val e heMem
    have hDrop : (inArcsPrefix H H.arcCount y.val).drop j =
        e :: (inArcsPrefix H H.arcCount y.val).drop (j + 1) :=
      list_drop_eq_cons _ j (by rw [inArcsPrefix_length]; exact hjLt)
    have heMemDrop : e ∈ (inArcsPrefix H H.arcCount y.val).drop j := by
      rw [hDrop]; exact List.mem_cons_self
    have hBaseU : ValuesWordsAt st.data (priorBase r.out.tables.next + 6 * (rawOccurrence H ⟨e, heLt⟩).1.val)
        (baseFn (rawOccurrence H ⟨e, heLt⟩).1) := by
      rcases hBases (rawOccurrence H ⟨e, heLt⟩).1 (rawOccurrence H ⟨e, heLt⟩).1.isLt with h | hNot
      · exact h
      · exact False.elim (hNot ⟨e, heMemDrop, heLt, rfl⟩)
    obtain ⟨_, heLive⟩ := hLives e heMemDrop
    have hArcIdJ : (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H y.val + j)]?).map Fin.val = some e :=
      hArcIds ⟨j, hjLt⟩
    obtain ⟨k1, s1, hk1, hs1, hpc1, hMeta1, hPtr1, hAcc1, hFr1⟩ :=
      step4A_arc_spec (input := input) loopPc h100 hPl hSz flat increasing covers rankArc hIn hWork hFitRank
        ok hFSize (B := B) hFEq ownerSlot hOwnPos hOwnLt Bcut baseFn (prefixIn H y.val + j)
        (prefixIn H (y.val + 1)) e heLt (by omega) hEndLe st hpc hMeta hPtr hEnd hArcIdJ
        h48 h49 h50 h51 h52 acc hAcc hDep hSt hBaseU (fun h1 h2 h3 h4 h5 => heLive h1 h2 h3 h4 h5)
    have hMetaBaseEq := metaArrBase_eq H.vertexCount H.arcCount r.out.tables.next
    have hSegFr : ∀ w, (w < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxArcPtr ∨
        (metaArrBase H.vertexCount H.arcCount r.out.tables.next + (mIdxArcPtr + 1) ≤ w ∧
          w < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxEvalU) ∨
        (metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ w ∧
          w < metaArrBase H.vertexCount H.arcCount r.out.tables.next + 53) ∨
        metaArrBase H.vertexCount H.arcCount r.out.tables.next + 55 ≤ w) → s1.data[w]? = st.data[w]? := hFr1
    have hTailLives : ∀ e' ∈ (inArcsPrefix H H.arcCount y.val).drop (j + 1), ∃ he' : e' < H.arcCount,
        let u := (rawOccurrence H ⟨e', he'⟩).1
        let v := (selectors (orderedConfig p large) r.out).label u
        let hvLt : v < r.out.tables.next := B.G.size_eq ▸ B.E.label_lt u True.intro
        u.val ≠ Bcut.fst.val → u.val ≠ Bcut.snd.val → 0 < v →
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) ≤
          r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) →
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨v, hvLt⟩) <
          r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩) →
        live v := fun e' he' => hLives e' (by rw [hDrop]; exact List.mem_cons_of_mem _ he')
    have hTailBases : ∀ q : Fin H.vertexCount, q.val < H.vertexCount →
        ValuesWordsAt s1.data (priorBase r.out.tables.next + 6 * q.val) (baseFn q) ∨
          ¬ (∃ e' ∈ (inArcsPrefix H H.arcCount y.val).drop (j + 1),
            ∃ he' : e' < H.arcCount, (rawOccurrence H ⟨e', he'⟩).1 = q) := by
      intro q hqLt
      rcases hBases q hqLt with hB | hNot
      · left
        apply valuesWordsAt_frame ?_ hB
        intro i hi
        apply hSegFr _ (Or.inl ?_)
        have hBase := metaArrBase_eq H.vertexCount H.arcCount r.out.tables.next
        have := q.isLt
        unfold priorBase
        omega
      · right; intro ⟨e', he', he'Lt, hOcc⟩; apply hNot
        exact ⟨e', by rw [hDrop]; exact List.mem_cons_of_mem _ he', he'Lt, hOcc⟩
    obtain ⟨k2, t, hk2, hs2, hpct, hMetaT, hAccT, hFr2⟩ := ih (j + 1)
      (ramArcStep r entryRank F ref ownerSlot (F.depthOf ownerSlot) Bcut baseFn acc e) s1
      (by omega) hpc1 hMeta1
      (by rw [show prefixIn H y.val + (j + 1) = (prefixIn H y.val + j) + 1 by omega]; exact hPtr1)
      (by rw [hSegFr _ (Or.inr (Or.inl ⟨by dsimp only [mIdxArcPtr, mIdxArcEnd]; omega, by dsimp only [mIdxArcEnd, mIdxEvalU]; omega⟩))]; exact hEnd)
      (by rw [hSegFr _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h48)
      (by rw [hSegFr _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h49)
      (by rw [hSegFr _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h50)
      (by rw [hSegFr _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h51)
      (by rw [hSegFr _ (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))]; exact h52)
      hAcc1 hTailBases
      (fun k => by
        rw [hSegFr _ (Or.inl (by unfold metaArrBase inArcIdArrBase; omega))]
        exact hArcIds k)
      (fun w => by
        rw [hSegFr _ (Or.inl (by have := w.isLt; omega))]
        exact hDep w)
      (fun w hwL => by
        have hSeg18 : ∀ i < 18, s1.data[storedBase r.out.tables.next + 18 * w.val + i]? =
            st.data[storedBase r.out.tables.next + 18 * w.val + i]? := fun i hi =>
          hSegFr _ (Or.inl (by have := w.isLt; unfold storedBase; omega))
        have ho := hSt w hwL
        refine ⟨by have hf := hSeg18 0 (by decide); rw [Nat.add_zero] at hf; rw [hf]; exact ho.1, by rw [hSeg18 1 (by decide)]; exact ho.2.1,
          mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg18 (2 + i) (by omega)) ho.2.2.1,
          mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hSeg18 (10 + i) (by omega)) ho.2.2.2⟩)
      hTailLives
    refine ⟨k1 + k2, t, ?_, hs1.append hs2, hpct, hMetaT, ?_, fun w hw => ?_⟩
    · have hMulSucc : 700 * (rem + 1) * OracleContract.L H.vertexCount =
          700 * rem * OracleContract.L H.vertexCount + 700 * OracleContract.L H.vertexCount := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
      omega
    · rw [hDrop, List.foldl_cons]; exact hAccT
    · rw [hFr2 w hw]
      exact hSegFr w (hw.imp id (Or.inr : _ → _))

end PaperB.RamProgram.ExitSummaryBuild
