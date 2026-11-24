module

public import PaperB.RamExitSummarySweepBParentHeader
public import PaperB.RamExitSummarySweepBPair

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

/-! Load and decode the metadata for a cached parent-map update. -/

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

theorem step4B_prepareParent_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hRecord : Placed code (basePc + 0) (step4BOneNode_record h100))
    (hChild : Placed code (basePc + 24) (step4BOneNode_cutEndpoints h100))
    (hParent : Placed code (basePc + 41) (step4BOneNode_parentEndpoints h100))
    (hSz : basePc + 62 < code.size)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (w pN jN : Nat) (hwLt : w < r.out.tables.next) (hpLt : pN < r.out.tables.next)
    (Pc Pp : CutPair H)
    (hBackW : r.out.tables.back[w]? = some (some Pc))
    (hBackP : r.out.tables.back[pN]? = some (some Pp))
    (depth : Nat → Nat)
    (st : State DomL) (hpc : st.pc = basePc)
    (hMeta : MetaReady st H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hBoundMeta : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 64 ≤ workCap)
    (hCur : (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxCCursor]?).map Fin.val = some w)
    (hParW : (st.data[storedBase r.out.tables.next + 18 * w]?).map Fin.val = some pN)
    (hJumpW : (st.data[storedBase r.out.tables.next + 18 * w + 1]?).map Fin.val = some jN)
    (hDepth : ∀ u : Fin r.out.tables.next, (st.data[u.val]?).map Fin.val = some (depth u.val)) :
    let N := r.out.tables.next
    let metaBase := metaArrBase H.vertexCount H.arcCount N
    ∃ t, Steps code input 62 st t ∧ t.pc = basePc + 62 ∧
      MetaReady t H.vertexCount H.arcCount N nGlobal ∧
      (t.data[metaBase + 48]?).map Fin.val = some pN ∧
      (t.data[metaBase + 49]?).map Fin.val = some jN ∧
      (t.data[metaBase + 50]?).map Fin.val = some Pc.fst.val ∧
      (t.data[metaBase + 51]?).map Fin.val = some Pc.snd.val ∧
      (t.data[metaBase + 52]?).map Fin.val = some Pp.fst.val ∧
      (t.data[metaBase + 53]?).map Fin.val = some Pp.snd.val ∧
      (t.data[metaBase + 54]?).map Fin.val = some (depth pN) ∧
      (t.data[metaBase + 55]?).map Fin.val = some (storedBase N + 18 * w) ∧
      (∀ j, j < metaBase + 48 ∨ metaBase + 56 ≤ j → t.data[j]? = st.data[j]?) := by
  intro N metaBase
  let n := H.vertexCount
  let m := H.arcCount
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hInCap : 4 + n + 4 * N + 3 * m ≤ inputCap := hIn.cap_ge
  have hInFit : inputCap ≤ 2 ^ bits := hi
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  change metaBase + 64 ≤ workCap at hBoundMeta
  have hOffNe {a b : Nat} (hne : a ≠ b) : metaBase + a ≠ metaBase + b :=
    fun he => hne (Nat.add_left_cancel he)
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits := by omega
  obtain ⟨s14, hs14, hpc14, h0_14, h1_14, hM_14, h2_14, h5_14,
    h48_14, h49_14, h55_14, hData14⟩ :=
    step4B_parentHeader_spec (input := input) basePc h100 hRecord (by omega)
      n m N nGlobal w pN jN hwLt st hpc hMeta hBoundMeta hCur hParW hJumpW
  have hBackFst (u : Fin N) (P : CutPair H) (hBack : r.out.tables.back[u.val]? = some (some P)) :
      (input.words[4 + n + u.val]?).map Fin.val = some (1 + P.fst.val) ∧
      (input.words[4 + n + N + u.val]?).map Fin.val = some P.snd.val := by
    obtain ⟨o, ho, hf, hs⟩ := hIn.back_at u
    rw [Option.some.inj (ho.symm.trans hBack)] at hf hs
    refine ⟨?_, hs⟩
    simpa [encodeBackPair, RetainedProperLoss.backPairFields, OptionalFinPair.encode, Nat.add_comm] using hf
  have hPairW := hBackFst ⟨w, hwLt⟩ Pc hBackW
  have hPairP := hBackFst ⟨pN, hpLt⟩ Pp hBackP
  have hBaseFst : (s14.data[metaBase + mIdxBackFstInBase]?).map Fin.val = some (4 + n) := by
    rw [hData14 _ (hOffNe (by decide)) (hOffNe (by decide)) (hOffNe (by decide))]
    exact hMeta.meta_backFstIn
  have hBaseSnd : (s14.data[metaBase + mIdxBackSndInBase]?).map Fin.val = some (4 + n + N) := by
    rw [hData14 _ (hOffNe (by decide)) (hOffNe (by decide)) (hOffNe (by decide))]
    exact hMeta.meta_backSndIn
  have hPCut : Placed code (basePc + 24)
      (step4B_decodePairInstrs (bits := bits) reg2 50 51 (by omega) (by omega) h100) := hChild
  obtain ⟨s23, hs23, hpc23, h50_23, h51_23, hData23, hPres23⟩ :=
    step4B_decodePair_spec (input := input) (basePc + 24) h100 reg2 50 51
      (by intro h; cases h) (by intro h; cases h) (by decide) (by decide) (by decide) (by decide)
      hPCut (by omega) n N metaBase w Pc.fst.val Pc.snd.val hBoundMeta (by omega) (by omega)
      s14 hpc14 hM_14 h1_14 h2_14 hBaseFst hBaseSnd hPairW.1 hPairW.2
  have hPres23' (rr : Fin 15) (h6 : rr ≠ reg6) (h7 : rr ≠ reg7) := hPres23 rr h6 h7
  have hPPar : Placed code (basePc + 41)
      (step4B_decodePairInstrs (bits := bits) reg5 52 53 (by omega) (by omega) h100) :=
    Placed_window hParent 0 rfl
  obtain ⟨s32, hs32, hpc32, h52_32, h53_32, hData32, hPres32⟩ :=
    step4B_decodePair_spec (input := input) (basePc + 41) h100 reg5 52 53
      (by intro h; cases h) (by intro h; cases h) (by decide) (by decide) (by decide) (by decide)
      hPPar (by omega) n N metaBase pN Pp.fst.val Pp.snd.val hBoundMeta (by omega) (by omega)
      s23 hpc23
      (by rw [hPres23' rMeta (by intro h; cases h) (by intro h; cases h), hM_14])
      (by rw [hPres23' reg1 (by intro h; cases h) (by intro h; cases h), h1_14])
      (by rw [hPres23' reg5 (by intro h; cases h) (by intro h; cases h), h5_14])
      (by rw [hData23 _ (hOffNe (by decide)) (hOffNe (by decide))]; exact hBaseFst)
      (by rw [hData23 _ (hOffNe (by decide)) (hOffNe (by decide))]; exact hBaseSnd)
      hPairP.1 hPairP.2
  have hPresAll (rr : Fin 15) (h6 : rr ≠ reg6) (h7 : rr ≠ reg7) :
      reg s32 rr = reg s14 rr := (hPres32 rr h6 h7).trans (hPres23 rr h6 h7)
  have h5_32 : (reg s32 reg5).val = pN := by
    rw [hPresAll reg5 (by intro h; cases h) (by intro h; cases h), h5_14]
  have hM_32 : (reg s32 rMeta).val = metaBase := by
    rw [hPresAll rMeta (by intro h; cases h) (by intro h; cases h), hM_14]
  have hLowHigh32 (j : Nat) (hj : j < metaBase + 48 ∨ metaBase + 56 ≤ j) :
      s32.data[j]? = st.data[j]? := by
    have hNe (off : Nat) (hl : 48 ≤ off) (hh : off < 56) : j ≠ metaBase + off := by
      rcases hj with hj | hj <;> omega
    rw [hData32 j (hNe 52 (by decide) (by decide)) (hNe 53 (by decide) (by decide)),
      hData23 j (hNe 50 (by decide) (by decide)) (hNe 51 (by decide) (by decide)),
      hData14 j (hNe 48 (by decide) (by decide)) (hNe 49 (by decide) (by decide))
        (hNe 55 (by decide) (by decide))]
  obtain ⟨wdp, hwdp, hwdpV⟩ := Option.map_eq_some_iff.mp (hDepth ⟨pN, hpLt⟩)
  have haLD : code[s32.pc]? = some (.loadData reg6 reg5) := by rw [hpc32]; exact hParent 17 _ rfl
  obtain ⟨s33, hs33Raw, hpc33, h6_33, ho33, hd33⟩ := step_loadData_at (input := input) haLD (by omega)
    (by rw [h5_32, hLowHigh32 _ (Or.inl (by omega))]; exact hwdp)
  have hs33 := steps_1_of_step hs33Raw
  have hM_33 : (reg s33 rMeta).val = metaBase := by
    rw [ho33 rMeta (by intro h; cases h), hM_32]
  have hPlS54 : Placed code (basePc + 59) (metaStoreInstrs (bits := bits) reg6 reg7 54 (by omega)) :=
    Placed_window hParent 18 rfl
  obtain ⟨s34, hs34, hpc34, hAt34, hFr34, hPres34⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS54 (by omega) (by rw [hpc33, hpc32]) hM_33 (by omega)
    (by exact lt_data_size (by omega))
  have hSteps34 : Steps code input 62 st s34 :=
    ((hs14.append hs23).append hs32).append (hs33.append hs34)
  have hData34 : ∀ j, j < metaBase + 48 ∨ metaBase + 56 ≤ j → s34.data[j]? = st.data[j]? := fun j hj => by
    rw [hFr34 j (by rcases hj with h | h <;> omega), hd33]
    exact hLowHigh32 j hj
  have h0_34 : (reg s34 reg0).val = 0 := by
    rw [hPres34 reg0 (by intro h; cases h), ho33 reg0 (by intro h; cases h),
      hPresAll reg0 (by intro h; cases h) (by intro h; cases h), h0_14]
  have h1_34 : (reg s34 reg1).val = 1 := by
    rw [hPres34 reg1 (by intro h; cases h), ho33 reg1 (by intro h; cases h),
      hPresAll reg1 (by intro h; cases h) (by intro h; cases h), h1_14]
  have hM_34 : (reg s34 rMeta).val = metaBase := by rw [hPres34 rMeta (by intro h; cases h), hM_33]
  have hOuter (i : Nat) (h54 : i ≠ 54) : s34.data[metaBase + i]? = s32.data[metaBase + i]? := by
    rw [hFr34 (metaBase + i) (hOffNe h54), hd33]
  have hMid (i : Nat) (h52 : i ≠ 52) (h53 : i ≠ 53) :
      s32.data[metaBase + i]? = s23.data[metaBase + i]? :=
    hData32 _ (hOffNe h52) (hOffNe h53)
  have hInner (i : Nat) (h50 : i ≠ 50) (h51 : i ≠ 51) :
      s23.data[metaBase + i]? = s14.data[metaBase + i]? :=
    hData23 _ (hOffNe h50) (hOffNe h51)
  have h54_34 : (s34.data[metaBase + 54]?).map Fin.val = some (depth pN) := by
    rw [hAt34, Option.map_some, h6_33, hwdpV]
  have hMeta34 : MetaReady s34 n m N nGlobal :=
    hMeta.preserve hM_34 h0_34 h1_34 (fun i hi => hData34 (metaBase + i) (Or.inl (by omega)))
  refine ⟨s34, hSteps34, hpc34, hMeta34, ?_, ?_, ?_, ?_, ?_, ?_, h54_34, ?_, hData34⟩
  · rw [hOuter 48 (by decide), hMid 48 (by decide) (by decide), hInner 48 (by decide) (by decide)]
    exact h48_14
  · rw [hOuter 49 (by decide), hMid 49 (by decide) (by decide), hInner 49 (by decide) (by decide)]
    exact h49_14
  · rw [hOuter 50 (by decide), hMid 50 (by decide) (by decide)]
    exact h50_23
  · rw [hOuter 51 (by decide), hMid 51 (by decide) (by decide)]
    exact h51_23
  · rw [hOuter 52 (by decide)]
    exact h52_32
  · rw [hOuter 53 (by decide)]
    exact h53_32
  · rw [hOuter 55 (by decide), hMid 55 (by decide) (by decide), hInner 55 (by decide) (by decide)]
    exact h55_14

end PaperB.RamProgram.ExitSummaryBuild
