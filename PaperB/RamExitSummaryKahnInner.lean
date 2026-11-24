module

public import PaperB.RamExitSummaryKahnSeed

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 2000000

/-!
The outgoing-arc loop of the word-RAM Kahn traversal.
-/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
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


section Stage2CsrKahn

section KahnLoop

variable {bits : Nat}

def kahnLoopSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg13 mIdxTempBase (by dsimp only [mIdxTempBase]; omega) ++
  (metaLoadInstrs reg13 reg12 mIdxN (by dsimp only [mIdxN]; omega) ++
  ([ .add reg7 reg6 reg13
   , .add reg9 reg7 reg13
   , .add reg9 reg9 reg1
   , .add reg8 reg9 reg13
   ] ++
  (metaLoadInstrs reg3 reg13 mIdxKCursor (by dsimp only [mIdxKCursor]; omega) ++
  (metaLoadInstrs reg4 reg13 mIdxOrderBase (by dsimp only [mIdxOrderBase]; omega) ++
  (metaLoadInstrs reg10 reg13 mIdxQHeadInBase (by dsimp only [mIdxQHeadInBase]; omega) ++
  [ .mov reg2 reg0 ])))))

def kahnLoopOuterInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .branchLt reg2 reg3 21 51
  , .add reg11 reg9 reg2
  , .loadData reg11 reg11
  , .add reg12 reg4 reg2
  , .storeData reg12 reg11
  ] ++
  (metaLoadInstrs reg12 reg13 mIdxTopoRankBase (by dsimp only [mIdxTopoRankBase]; omega) ++
  [ .add reg12 reg12 reg11
  , .storeData reg12 reg2
  , .add reg12 reg7 reg11
  , .loadData reg11 reg12
  , .add reg12 reg12 reg1
  , .loadData reg12 reg12
  , .add reg2 reg2 reg1
  ])

def kahnLoopInnerInstrs : List (Instr bits 15) :=
  [ .branchLt reg11 reg12 36 20
  , .add reg13 reg8 reg11
  , .loadData reg13 reg13
  , .add reg13 reg10 reg13
  , .loadInput reg13 reg13
  , .add reg5 reg6 reg13
  , .loadData reg13 reg5
  , .sub reg13 reg13 reg1
  , .storeData reg5 reg13
  , .branchLt reg0 reg13 49 45
  , .sub reg5 reg5 reg6
  , .add reg13 reg9 reg3
  , .storeData reg13 reg5
  , .add reg3 reg3 reg1
  , .add reg11 reg11 reg1
  , .goto 35
  ]

def kahnLoopInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  kahnLoopSetupInstrs h100 ++ (kahnLoopOuterInstrs h100 ++ kahnLoopInnerInstrs)

end KahnLoop

section KahnLoopPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem kahnLoopInstrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (kahnLoopInstrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  unfold kahnLoopInstrs
  refine list_all_append_true _ _ _ ?_ (list_all_append_true _ _ _ ?_ ?_)
  · unfold kahnLoopSetupInstrs
    simp only [List.all_append, List.all_cons, List.all_nil, metaLoadInstrs_nonHalt, nonHalt, Bool.and_true]
  · unfold kahnLoopOuterInstrs
    simp only [List.all_append, List.all_cons, List.all_nil, metaLoadInstrs_nonHalt, nonHalt, Bool.and_true]
  · unfold kahnLoopInnerInstrs
    simp only [List.all_cons, List.all_nil, nonHalt, Bool.and_true]

def kahnLoopPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (kahnLoopInstrs h100) (kahnLoopInstrs_nonHalt h100)

theorem kahnLoopInner_spec {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap)
    (_hWorkFit : workCap ≤ 2 ^ bits)
    (hPl : Placed code 35 (kahnLoopInnerInstrs (bits := bits)))
    (hSz : 51 < code.size)
    (popped : List Nat) (u : Nat) (huNotPopped : u ∉ popped)
    (_hInputFit : inputCap ≤ 2 ^ bits)
    (hQHeadBase : 0 < H.arcCount →
      4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + H.arcCount ≤ inputCap) :
    ∀ (rem j : Nat) (q0 : List Nat) (st : State DomL),
      j + rem = degOut H u →
      popped.length + 1 ≤ q0.length →
      q0.length ≤ H.vertexCount →
      q0.Nodup →
      (∀ x ∈ q0, x < H.vertexCount) →
      (∀ x ∈ popped, x ∈ q0) →
      u ∈ q0 →
      (∀ v, v < H.vertexCount → (v ∈ q0 ↔
        remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v = 0)) →
      st.pc = 35 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg2).val = popped.length + 1 →
      (reg st reg3).val = q0.length →
      (reg st reg4).val = orderArrBase H.vertexCount r.out.tables.next →
      (reg st reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount →
      (reg st reg8).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 →
      (reg st reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 →
      (0 < H.arcCount → (reg st reg10).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount) →
      (reg st reg11).val = prefixOut H u + j →
      (reg st reg12).val = prefixOut H u + degOut H u →
      (∀ v, v < H.vertexCount →
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v)) →
      (∀ i (hi : i < q0.length),
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i]?).map Fin.val =
          some (q0[i]'hi)) →
      (∀ k (hk : k < degOut H u),
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + k)]?).map Fin.val =
          some ((outArcsPrefix H H.arcCount u)[k]'(by rw [outArcsPrefix_length]; exact hk))) →
      ∃ steps : Nat, ∃ q1 : List Nat, ∃ t : State DomL,
        steps ≤ 16 * rem + 1 ∧
        Steps code input steps st t ∧
        t.pc = 20 ∧
        popped.length + 1 ≤ q1.length ∧
        q1.length ≤ H.vertexCount ∧
        q1.Nodup ∧
        (∀ x ∈ q1, x < H.vertexCount) ∧
        (∀ x ∈ popped, x ∈ q1) ∧
        u ∈ q1 ∧
        (∀ i, i < popped.length + 1 → q1[i]? = q0[i]?) ∧
        (∀ v, v < H.vertexCount → (v ∈ q1 ↔
          remInCount H popped (outArcsPrefix H H.arcCount u) v = 0)) ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
        (reg t reg2).val = popped.length + 1 ∧
        (reg t reg3).val = q1.length ∧
        (reg t reg4).val = orderArrBase H.vertexCount r.out.tables.next ∧
        (reg t reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next ∧
        (reg t reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ∧
        (reg t reg8).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ∧
        (reg t reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 ∧
        (0 < H.arcCount → (reg t reg10).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount) ∧
        (∀ v, v < H.vertexCount →
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
            some (remInCount H popped (outArcsPrefix H H.arcCount u) v)) ∧
        (∀ i (hi : i < q1.length),
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i]?).map Fin.val =
            some (q1[i]'hi)) ∧
        (∀ a, (a < tempArrBase H.vertexCount H.arcCount r.out.tables.next ∨
            (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ≤ a ∧
              a < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1) ∨
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤ a) →
          t.data[a]? = st.data[a]?) := by
  intro rem
  induction rem with
  | zero =>
    intro j q0 st hSum hPopLe hLenLe hNd hBound hPopMem huMem hZeroIff hpc
      h0 h1 hMeta h2 h3 h4 h6 h7 h8 h9 h10 h11 h12 hIndeg hQMem hOutArc
    have hjEq : j = degOut H u := by omega
    obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg11).val < (reg st reg12).val := by rw [h11, h12, hjEq]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpct
    have hrtF := reg_of_regs_eq hrt
    have hTakeEq : (outArcsPrefix H H.arcCount u).take j = outArcsPrefix H H.arcCount u := by
      rw [hjEq]; exact List.take_of_length_le (Nat.le_of_eq (by rw [outArcsPrefix_length]; rfl))
    rw [hTakeEq] at hZeroIff hIndeg
    refine ⟨1, q0, t, by omega, steps_1_of_step hs, hpct,
      hPopLe, hLenLe, hNd, hBound, hPopMem, huMem, fun _ _ => rfl, hZeroIff,
      by rw [hrtF, h0], by rw [hrtF, h1], by rw [hrtF, hMeta], by rw [hrtF, h2],
      by rw [hrtF, h3], by rw [hrtF, h4], by rw [hrtF, h6], by rw [hrtF, h7],
      by rw [hrtF, h8], by rw [hrtF, h9], fun hm => by rw [hrtF, h10 hm],
      fun v hv => by rw [hdt]; exact hIndeg v hv,
      fun i hi => by rw [hdt]; exact hQMem i hi,
      fun _ _ => by rw [hdt]⟩
  | succ rem ih =>
    intro j q0 st hSum hPopLe hLenLe hNd hBound hPopMem huMem hZeroIff hpc
      h0 h1 hMeta h2 h3 h4 h6 h7 h8 h9 h10 h11 h12 hIndeg hQMem hOutArc
    have hjLt : j < degOut H u := by omega
    have hCmp : (reg st reg11).val < (reg st reg12).val := by rw [h11, h12]; omega
    obtain ⟨s1, hs1, hpc1, hrt1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    rw [ite_eq_left hCmp] at hpc1
    have hr1 := reg_of_regs_eq hrt1
    let e0 := (outArcsPrefix H H.arcCount u)[j]'(by rw [outArcsPrefix_length]; exact hjLt)
    have he0Lt : e0 < H.arcCount := outArcsPrefix_lt H H.arcCount u e0 (List.getElem_mem _)
    have hmPos : 0 < H.arcCount := Nat.lt_of_le_of_lt (Nat.zero_le e0) he0Lt
    let e0Fin : Fin H.arcCount := ⟨e0, he0Lt⟩
    let v0 := (rawHead H e0Fin).val
    have hv0Lt : v0 < H.vertexCount := (rawHead H e0Fin).isLt
    have huLt : u < H.vertexCount := by
      have hm := (mem_outArcsPrefix_iff H H.arcCount u e0).mp (List.getElem_mem _)
      rw [← hm.2.2]; exact (rawOccurrence H e0Fin).1.isLt
    have hPrefLe : prefixOut H u + j < H.arcCount := by
      have : prefixOut H u + degOut H u = prefixOut H (u + 1) := rfl
      have : prefixOut H (u + 1) ≤ prefixOut H H.vertexCount := prefixOut_mono H huLt
      rw [prefixOut_vertexCount H] at this
      omega
    have ha1 : code[s1.pc]? = some (.add reg13 reg8 reg11) := by rw [hpc1]; exact hPl 1 _ rfl
    have hFit1 : (reg s1 reg8).val + (reg s1 reg11).val < 2 ^ bits := by
      rw [hr1, hr1, h8, h11]; omega
    obtain ⟨s2, hs2, hpc2, h13_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by omega)
    have hAddr1 : (reg s2 reg13).val =
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j) := by
      rw [h13_2, add_no_wrap _ _ hFit1, hr1, hr1, h8, h11]
    obtain ⟨wE, hwE, hwEV⟩ := Option.map_eq_some_iff.mp (hOutArc j hjLt)
    have hMemE : s2.data[(reg s2 reg13).val]? = some wE := by
      rw [hAddr1, hd2, hd1]; exact hwE
    have hl1 : code[s2.pc]? = some (.loadData reg13 reg13) := by rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, hpc3, h13_3, ho3, hd3⟩ := step_loadData_at (input := input) hl1 (by omega) hMemE
    have hEVal : (reg s3 reg13).val = e0 := by rw [h13_3, hwEV]
    have h10_3 : (reg s3 reg10).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount := by
      rw [ho3 reg10 (by intro h; cases h), ho2 reg10 (by intro h; cases h), hr1, h10 hmPos]
    have ha2 : code[s3.pc]? = some (.add reg13 reg10 reg13) := by rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
    have hFit2 : (reg s3 reg10).val + (reg s3 reg13).val < 2 ^ bits := by
      have := hQHeadBase hmPos
      rw [h10_3, hEVal]; omega
    obtain ⟨s4, hs4, hpc4, h13_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by omega)
    have hAddr2 : (reg s4 reg13).val =
        4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + e0 := by
      rw [h13_4, add_no_wrap _ _ hFit2, h10_3, hEVal]
    obtain ⟨wV, hwV, hwVV⟩ := Option.map_eq_some_iff.mp (hIn.qHead_at e0Fin)
    have hMemV : input.words[(reg s4 reg13).val]? = some wV := by rw [hAddr2]; exact hwV
    have hl2 : code[s4.pc]? = some (.loadInput reg13 reg13) := by
      rw [hpc4, hpc3, hpc2, hpc1]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, hpc5, h13_5, ho5, hd5⟩ := step_loadInput_at (input := input) hl2 (by omega) hMemV
    have hVVal : (reg s5 reg13).val = v0 := by rw [h13_5, hwVV]
    have h6_5 : (reg s5 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho5 reg6 (by intro h; cases h), ho4 reg6 (by intro h; cases h), ho3 reg6 (by intro h; cases h),
        ho2 reg6 (by intro h; cases h), hr1, h6]
    have ha3 : code[s5.pc]? = some (.add reg5 reg6 reg13) := by
      rw [hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 5 _ rfl
    have hFit3 : (reg s5 reg6).val + (reg s5 reg13).val < 2 ^ bits := by
      rw [h6_5, hVVal]; omega
    obtain ⟨s6, hs6, hpc6, h5_6, ho6, hd6⟩ := step_add_at (input := input) ha3 (by omega)
    have hAddrIndeg : (reg s6 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v0 := by
      rw [h5_6, add_no_wrap _ _ hFit3, h6_5, hVVal]
    have hd6' : s6.data = st.data := by rw [hd6, hd5, hd4, hd3, hd2, hd1]
    obtain ⟨wOld, hwOld, hwOldV⟩ := Option.map_eq_some_iff.mp (hIndeg v0 hv0Lt)
    have hMemOld : s6.data[(reg s6 reg5).val]? = some wOld := by rw [hAddrIndeg, hd6']; exact hwOld
    have hl3 : code[s6.pc]? = some (.loadData reg13 reg5) := by
      rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 6 _ rfl
    obtain ⟨s7, hs7, hpc7, h13_7, ho7, hd7⟩ := step_loadData_at (input := input) hl3 (by omega) hMemOld
    have hOldVal : (reg s7 reg13).val =
        remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v0 := by
      rw [h13_7, hwOldV]
    have h1_7 : (reg s7 reg1).val = 1 := by
      rw [ho7 reg1 (by intro h; cases h), ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h),
        ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), hr1, h1]
    have hStepRel := remInCount_relax_step H popped u j huLt huNotPopped hjLt
    have hOldEq : remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v0 =
        remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v0 + 1 := hStepRel.1
    have hOldGe1 : 1 ≤ remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v0 := by omega
    have hs1_8 : code[s7.pc]? = some (.sub reg13 reg13 reg1) := by
      rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 7 _ rfl
    obtain ⟨s8, hs8, hpc8, h13_8, ho8, hd8⟩ := step_sub_at (input := input) hs1_8 (by omega)
    have hNewVal : (reg s8 reg13).val =
        remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v0 := by
      rw [h13_8, sub_exact (by rw [hOldVal, h1_7]; exact hOldGe1), hOldVal, h1_7, hOldEq]; omega
    have h5_8 : (reg s8 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v0 := by
      rw [ho8 reg5 (by intro h; cases h), ho7 reg5 (by intro h; cases h), hAddrIndeg]
    have hLt8 : (reg s8 reg5).val < s8.data.size := lt_data_size (by rw [h5_8]; omega)
    have hst1 : code[s8.pc]? = some (.storeData reg5 reg13) := by
      rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 8 _ rfl
    obtain ⟨s9, hs9, hpc9, hreg9, hd9⟩ := step_storeData_opaque (input := input) hst1 hLt8 (by omega)
    have hr9 := reg_of_regs_eq hreg9
    have hd8' : s8.data = st.data := by rw [hd8, hd7, hd6']
    have hLt8St : (reg s8 reg5).val < st.data.size := by rw [← hd8']; exact hLt8
    have hs9Data : s9.data = st.data.set (reg s8 reg5).val (reg s8 reg13) hLt8St := by
      rw [hd9]; exact array_set_eq_of_data_eq hd8' hLt8 hLt8St
    have hPres9 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg13 → reg s9 r = reg st r := fun r hr5 hr13 => by
      rw [hr9, ho8 r hr13, ho7 r hr13, ho6 r hr5, ho5 r hr13, ho4 r hr13, ho3 r hr13, ho2 r hr13, hr1]
    have h0_9 : (reg s9 reg0).val = 0 := by
      rw [hPres9 reg0 (by intro h; cases h) (by intro h; cases h), h0]
    have h13_9 : (reg s9 reg13).val =
        remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v0 := by
      rw [hr9, hNewVal]
    have hbr : code[s9.pc]? = some (.branchLt reg0 reg13 49 45) := by
      rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 9 _ rfl
    obtain ⟨s10, hs10, hpc10, hrt10, hd10⟩ := step_branchLt_at (input := input) hbr (by split <;> omega)
    have hr10 := reg_of_regs_eq hrt10
    have hIndeg9 : ∀ v, v < H.vertexCount →
        (s9.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v) := by
      intro v hv
      by_cases hvv0 : v = v0
      · subst hvv0
        rw [hs9Data, ← h5_8, Array.getElem?_set_self hLt8St, Option.map_some, hNewVal]
      · have hNe : tempArrBase H.vertexCount H.arcCount r.out.tables.next + v ≠ (reg s8 reg5).val := by
          rw [h5_8]; omega
        rw [hs9Data, Array.getElem?_set_ne hLt8St hNe.symm, hStepRel.2 v hvv0]
        exact hIndeg v hv
    by_cases hNewPos : 0 < remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v0
    · rw [ite_eq_left (by rw [h0_9, h13_9]; exact hNewPos)] at hpc10
      have haIncP : code[s10.pc]? = some (.add reg11 reg11 reg1) := by rw [hpc10]; exact hPl 14 _ rfl
      have h11_10 : (reg s10 reg11).val = prefixOut H u + j := by
        rw [hr10, hPres9 reg11 (by intro h; cases h) (by intro h; cases h), h11]
      have h1_10 : (reg s10 reg1).val = 1 := by
        rw [hr10, hPres9 reg1 (by intro h; cases h) (by intro h; cases h), h1]
      have hFitP : (reg s10 reg11).val + (reg s10 reg1).val < 2 ^ bits := by
        rw [h11_10, h1_10]; omega
      obtain ⟨s11, hs11, hpc11, h11_11, ho11, hd11⟩ := step_add_at (input := input) haIncP (by omega)
      have hg11 : code[s11.pc]? = some (.goto 35) := by rw [hpc11, hpc10]; exact hPl 15 _ rfl
      obtain ⟨s12, hs12, hpc12, hrt12, hd12⟩ := step_goto_at (input := input) hg11 (by omega)
      have hr12 := reg_of_regs_eq hrt12
      have hd12' : s12.data = s9.data := by rw [hd12, hd11, hd10]
      have hPres12 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg11 → r ≠ reg13 → reg s12 r = reg st r :=
        fun r hr5 hr11 hr13 => by rw [hr12, ho11 r hr11, hr10, hPres9 r hr5 hr13]
      have hZeroIffNext : ∀ v, v < H.vertexCount →
          (v ∈ q0 ↔ remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v = 0) := by
        intro v hv
        by_cases hvv0 : v = v0
        · subst hvv0; rw [hZeroIff v0 hv0Lt]; omega
        · rw [hStepRel.2 v hvv0]; exact hZeroIff v hv
      have hStep12 : Steps code input 12 st s12 :=
        Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
          (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (Steps.cons hs11 (steps_1_of_step hs12)))))))))))
      obtain ⟨kRest, q1, t, hkRest, hStepsRest, hpct, hPop1, hLen1, hNd1, hBound1, hPopMem1,
          huMem1, hTake1, hZero1, ht0, ht1, htMeta, ht2, ht3, ht4, ht6, ht7, ht8, ht9, ht10,
          htIndeg, htQMem, htFr⟩ :=
        ih (j + 1) q0 s12 (by omega) hPopLe hLenLe hNd hBound hPopMem huMem hZeroIffNext hpc12
          (by rw [hPres12 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
          (by rw [hPres12 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
          (by rw [hPres12 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
          (by rw [hPres12 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2])
          (by rw [hPres12 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3])
          (by rw [hPres12 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4])
          (by rw [hPres12 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6])
          (by rw [hPres12 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7])
          (by rw [hPres12 reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h8])
          (by rw [hPres12 reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h9])
          (fun hm => by rw [hPres12 reg10 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h10 hm])
          (by rw [hr12, h11_11, add_no_wrap _ _ hFitP, h11_10, h1_10]; omega)
          (by rw [hPres12 reg12 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h12])
          (fun v hv => by rw [hd12']; exact hIndeg9 v hv)
          (fun i hi => by
            have hNe : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i ≠
                (reg s8 reg5).val := by rw [h5_8]; omega
            rw [hd12', hs9Data, Array.getElem?_set_ne hLt8St hNe.symm]
            exact hQMem i hi)
          (fun k hk => by
            have hNe : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + k) ≠
                (reg s8 reg5).val := by rw [h5_8]; omega
            rw [hd12', hs9Data, Array.getElem?_set_ne hLt8St hNe.symm]
            exact hOutArc k hk)
      refine ⟨12 + kRest, q1, t, by omega, hStep12.append hStepsRest, hpct,
        hPop1, hLen1, hNd1, hBound1, hPopMem1, huMem1, hTake1, hZero1,
        ht0, ht1, htMeta, ht2, ht3, ht4, ht6, ht7, ht8, ht9, ht10, htIndeg, htQMem, fun a ha => ?_⟩
      rw [htFr a ha, hd12', hs9Data]
      have hNe : a ≠ (reg s8 reg5).val := by
        rw [h5_8]
        rcases ha with h | ⟨h1, _⟩ | h
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
        · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hv0Lt _) h1)
        · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hv0Lt _) (by omega)) h)
      exact Array.getElem?_set_ne hLt8St hNe.symm
    · have hNewZ : remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v0 = 0 := by omega
      rw [ite_eq_right (by rw [h0_9, h13_9]; exact hNewPos)] at hpc10
      have hv0NotInQ : v0 ∉ q0 := by
        rw [hZeroIff v0 hv0Lt]; omega
      have hQNextNd : (q0 ++ [v0]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hNd, (by simp : [v0].Nodup), fun a ha b hb hab => by
          simp only [List.mem_singleton] at hb; subst hb; subst hab; exact hv0NotInQ ha⟩
      have hQNextBound : ∀ x ∈ q0 ++ [v0], x < H.vertexCount := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hBound x h
        · simp only [List.mem_singleton] at h; subst h; exact hv0Lt
      have hQNextLen : (q0 ++ [v0]).length ≤ H.vertexCount :=
        list_nodup_length_le_fin (q0 ++ [v0]) hQNextNd hQNextBound
      have hQLtN : q0.length < H.vertexCount := by simp at hQNextLen; omega
      have hsV : code[s10.pc]? = some (.sub reg5 reg5 reg6) := by rw [hpc10]; exact hPl 10 _ rfl
      have h5_10 : (reg s10 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v0 := by
        rw [hr10, hr9, h5_8]
      have h6_10 : (reg s10 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
        rw [hr10, hPres9 reg6 (by intro h; cases h) (by intro h; cases h), h6]
      obtain ⟨s11, hs11, hpc11, h5_11, ho11, hd11⟩ := step_sub_at (input := input) hsV (by omega)
      have h5Val11 : (reg s11 reg5).val = v0 := by
        rw [h5_11, sub_exact (by rw [h5_10, h6_10]; exact Nat.le_add_right _ _), h5_10, h6_10]
        omega
      have h9_11 : (reg s11 reg9).val =
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 := by
        rw [ho11 reg9 (by intro h; cases h), hr10, hPres9 reg9 (by intro h; cases h) (by intro h; cases h), h9]
      have h3_11 : (reg s11 reg3).val = q0.length := by
        rw [ho11 reg3 (by intro h; cases h), hr10, hPres9 reg3 (by intro h; cases h) (by intro h; cases h), h3]
      have haQ : code[s11.pc]? = some (.add reg13 reg9 reg3) := by rw [hpc11, hpc10]; exact hPl 11 _ rfl
      have hFitQ : (reg s11 reg9).val + (reg s11 reg3).val < 2 ^ bits := by
        rw [h9_11, h3_11]; omega
      obtain ⟨s12, hs12, hpc12, h13_12, ho12, hd12⟩ := step_add_at (input := input) haQ (by omega)
      have hAddrQ : (reg s12 reg13).val =
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + q0.length := by
        rw [h13_12, add_no_wrap _ _ hFitQ, h9_11, h3_11]
      have hLtQ12 : (reg s12 reg13).val < s12.data.size := lt_data_size (by rw [hAddrQ]; omega)
      have hstQ : code[s12.pc]? = some (.storeData reg13 reg5) := by
        rw [hpc12, hpc11, hpc10]; exact hPl 12 _ rfl
      obtain ⟨s13, hs13, hpc13, hreg13, hd13⟩ := step_storeData_opaque (input := input) hstQ hLtQ12 (by omega)
      have hr13 := reg_of_regs_eq hreg13
      have h3_13 : (reg s13 reg3).val = q0.length := by
        rw [hr13, ho12 reg3 (by intro h; cases h), h3_11]
      have h1_13 : (reg s13 reg1).val = 1 := by
        rw [hr13, ho12 reg1 (by intro h; cases h), ho11 reg1 (by intro h; cases h), hr10,
          hPres9 reg1 (by intro h; cases h) (by intro h; cases h), h1]
      have hFitQTail : (reg s13 reg3).val + (reg s13 reg1).val < 2 ^ bits := by
        rw [h3_13, h1_13]; omega
      have haQT : code[s13.pc]? = some (.add reg3 reg3 reg1) := by
        rw [hpc13, hpc12, hpc11, hpc10]; exact hPl 13 _ rfl
      obtain ⟨s14, hs14, hpc14, h3_14, ho14, hd14⟩ := step_add_at (input := input) haQT (by omega)
      have h11_14 : (reg s14 reg11).val = prefixOut H u + j := by
        rw [ho14 reg11 (by intro h; cases h), hr13, ho12 reg11 (by intro h; cases h),
          ho11 reg11 (by intro h; cases h), hr10,
          hPres9 reg11 (by intro h; cases h) (by intro h; cases h), h11]
      have h1_14 : (reg s14 reg1).val = 1 := by rw [ho14 reg1 (by intro h; cases h), h1_13]
      have hFitP : (reg s14 reg11).val + (reg s14 reg1).val < 2 ^ bits := by
        rw [h11_14, h1_14]; omega
      have haIncP : code[s14.pc]? = some (.add reg11 reg11 reg1) := by
        rw [hpc14, hpc13, hpc12, hpc11, hpc10]; exact hPl 14 _ rfl
      obtain ⟨s15, hs15, hpc15, h11_15, ho15, hd15⟩ := step_add_at (input := input) haIncP (by omega)
      have hg15 : code[s15.pc]? = some (.goto 35) := by
        rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10]; exact hPl 15 _ rfl
      obtain ⟨s16, hs16, hpc16, hrt16, hd16⟩ := step_goto_at (input := input) hg15 (by omega)
      have hr16 := reg_of_regs_eq hrt16
      have hd12' : s12.data = s9.data := by rw [hd12, hd11, hd10]
      have hLtQ12S9 : (reg s12 reg13).val < s9.data.size := by rw [← hd12']; exact hLtQ12
      have hs16Data : s16.data = s9.data.set (reg s12 reg13).val (reg s12 reg5) hLtQ12S9 := by
        rw [hd16, hd15, hd14, hd13]
        exact array_set_eq_of_data_eq hd12' hLtQ12 hLtQ12S9
      have hPres16 : ∀ r : Fin 15, r ≠ reg3 → r ≠ reg5 → r ≠ reg11 → r ≠ reg13 → reg s16 r = reg st r :=
        fun r hr3 hr5 hr11 hr13' => by
          rw [hr16, ho15 r hr11, ho14 r hr3, hr13, ho12 r hr13', ho11 r hr5, hr10, hPres9 r hr5 hr13']
      have hZeroIffNext : ∀ v, v < H.vertexCount →
          (v ∈ q0 ++ [v0] ↔ remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v = 0) := by
        intro v hv
        rw [List.mem_append, List.mem_singleton]
        by_cases hvv0 : v = v0
        · subst hvv0; constructor
          · intro _; exact hNewZ
          · intro _; exact Or.inr rfl
        · rw [hStepRel.2 v hvv0, hZeroIff v hv]
          constructor
          · rintro (h | rfl)
            · exact h
            · exact absurd rfl hvv0
          · intro h; exact Or.inl h
      have hStep16 : Steps code input 16 st s16 :=
        Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
          (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13
              (Steps.cons hs14 (Steps.cons hs15 (steps_1_of_step hs16)))))))))))))))
      obtain ⟨kRest, q1, t, hkRest, hStepsRest, hpct, hPop1, hLen1, hNd1, hBound1, hPopMem1,
          huMem1, hTake1, hZero1, ht0, ht1, htMeta, ht2, ht3, ht4, ht6, ht7, ht8, ht9, ht10,
          htIndeg, htQMem, htFr⟩ :=
        ih (j + 1) (q0 ++ [v0]) s16 (by omega) (by simp; omega) hQNextLen hQNextNd hQNextBound
          (fun x hx => List.mem_append.mpr (Or.inl (hPopMem x hx)))
          (List.mem_append.mpr (Or.inl huMem)) hZeroIffNext hpc16
          (by rw [hPres16 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
          (by rw [hPres16 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
          (by rw [hPres16 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
          (by rw [hPres16 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2])
          (by rw [hr16, ho15 reg3 (by intro h; cases h), h3_14, add_no_wrap _ _ hFitQTail, h3_13, h1_13]; simp)
          (by rw [hPres16 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4])
          (by rw [hPres16 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6])
          (by rw [hPres16 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7])
          (by rw [hPres16 reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h8])
          (by rw [hPres16 reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h9])
          (fun hm => by rw [hPres16 reg10 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h10 hm])
          (by rw [hr16, h11_15, add_no_wrap _ _ hFitP, h11_14, h1_14]; omega)
          (by rw [hPres16 reg12 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h12])
          (fun v hv => by
            have hNe : tempArrBase H.vertexCount H.arcCount r.out.tables.next + v ≠ (reg s12 reg13).val := by
              rw [hAddrQ]; omega
            rw [hs16Data, Array.getElem?_set_ne hLtQ12S9 hNe.symm]
            exact hIndeg9 v hv)
          (fun i hi => by
            simp only [List.length_append, List.length_singleton] at hi
            by_cases hiLast : i = q0.length
            · subst hiLast
              rw [hs16Data, ← hAddrQ, Array.getElem?_set_self hLtQ12S9, Option.map_some]
              simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton]
              exact congrArg some (by rw [ho12 reg5 (by intro h; cases h), h5Val11])
            · have hiLt : i < q0.length := by omega
              have hNe1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i ≠
                  (reg s12 reg13).val := by rw [hAddrQ]; omega
              have hNe2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i ≠
                  (reg s8 reg5).val := by rw [h5_8]; omega
              rw [hs16Data, Array.getElem?_set_ne hLtQ12S9 hNe1.symm, hs9Data,
                Array.getElem?_set_ne hLt8St hNe2.symm, List.getElem_append_left hiLt]
              exact hQMem i hiLt)
          (fun k hk => by
            have hNe1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + k) ≠
                (reg s12 reg13).val := by rw [hAddrQ]; omega
            have hNe2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + k) ≠
                (reg s8 reg5).val := by rw [h5_8]; omega
            rw [hs16Data, Array.getElem?_set_ne hLtQ12S9 hNe1.symm, hs9Data,
              Array.getElem?_set_ne hLt8St hNe2.symm]
            exact hOutArc k hk)
      refine ⟨16 + kRest, q1, t, by omega, hStep16.append hStepsRest, hpct,
        hPop1, hLen1, hNd1, hBound1, hPopMem1, huMem1, fun i hi => ?_, hZero1,
        ht0, ht1, htMeta, ht2, ht3, ht4, ht6, ht7, ht8, ht9, ht10, htIndeg, htQMem, fun a ha => ?_⟩
      · rw [hTake1 i hi, List.getElem?_append_left (Nat.lt_of_lt_of_le hi hPopLe)]
      · rw [htFr a ha, hs16Data]
        have hNe1 : a ≠ (reg s12 reg13).val := by
          rw [hAddrQ]
          rcases ha with h | ⟨_, h2⟩ | h
          · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h (by omega))
          · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2 (Nat.le_add_right _ _))
          · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hQLtN _) (by omega))
        rw [Array.getElem?_set_ne hLtQ12S9 hNe1.symm, hs9Data]
        have hNe2 : a ≠ (reg s8 reg5).val := by
          rw [h5_8]
          rcases ha with h | ⟨h1, _⟩ | h
          · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
          · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hv0Lt _) h1)
          · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hv0Lt _) (by omega)) h)
        exact Array.getElem?_set_ne hLt8St hNe2.symm

end KahnLoopPhase

end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
