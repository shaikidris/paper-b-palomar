module

public import PaperB.RamExitSummarySetup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 / EX5.2 Word-RAM exit-summary Stage 2 CSR count/prefix/scatter (`PaperB/RamExitSummaryCsr.lean`).

Contains:
1. Input/output memory layout (`exitWorkCap n m ≤ 48 * (n + m + 1)`, metadata slots,
   `ExitBuildInput`).
2. Mathematical specification bridges:
   - DFS `(fEntry, fStop)` stack reconstruction matching `B.F.parentOf`,
     `B.F.depthOf`, and `B.F.jumpOf`;
   - Topological trigger ordering (`triggerRank parent < triggerRank child` and
     `triggerRank owner < topoRank y`);
   - `Occupied` / `DecodedOccupied` / `LiveStoreOK` / `RouteSlotEdges` bridges.
3. 15-register Word-RAM execution helpers, `PhasesExec`, `linkNonEmpty`,
   `initMetaPhase`, Stage 1 (`forestReconPhase`), Stage 2 (`csrKahnPhase`),
   Stage 3 (`seedAndTriggerPhase`), and reusable Stage 4 slices (`intervalJoin`,
   `mapEval`, `eval15`, `mapCompose`, `buildOneSlot`).
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

section CsrCount

variable {bits : Nat}

def csrCountSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg9 mIdxM (by change 1 < 2 ^ bits; omega) ++
  ([.branchLt reg0 reg2 4 40] ++
  (metaLoadInstrs reg3 reg9 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg4 reg9 mIdxN (by change 0 < 2 ^ bits; omega) ++
  ([.add reg4 reg3 reg4] ++
  (metaLoadInstrs reg5 reg9 mIdxInStartBase (by change 10 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg6 reg9 mIdxQSrcInBase (by change 14 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg7 reg9 mIdxQHeadInBase (by change 15 < 2 ^ bits; omega) ++
  [.mov reg8 reg0])))))))

def csrCountLoopInstrs : List (Instr bits 15) :=
  [ .branchLt reg8 reg2 22 40
  , .add reg9 reg6 reg8
  , .loadInput reg9 reg9
  , .add reg9 reg4 reg9
  , .loadData reg10 reg9
  , .add reg10 reg10 reg1
  , .storeData reg9 reg10
  , .add reg9 reg7 reg8
  , .loadInput reg9 reg9
  , .add reg10 reg5 reg9
  , .loadData reg11 reg10
  , .add reg11 reg11 reg1
  , .storeData reg10 reg11
  , .add reg10 reg3 reg9
  , .loadData reg11 reg10
  , .add reg11 reg11 reg1
  , .storeData reg10 reg11
  , .add reg8 reg8 reg1
  , .goto 21
  ]

def csrCountInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  csrCountSetupInstrs h100 ++ csrCountLoopInstrs

end CsrCount

section CsrCountPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def csrCountPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (csrCountInstrs (bits := bits) h100)
    (by simp [csrCountInstrs, csrCountSetupInstrs, csrCountLoopInstrs, metaLoadInstrs, nonHalt])

private theorem csrCountLoop_spec {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hPl : Placed code 21 csrCountLoopInstrs) (hSz : 40 < code.size)
    (k : Nat) (hkLe : k ≤ H.arcCount)
    (st : State DomL) (hpc : st.pc = 21)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hMeta : (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hM : (reg st reg2).val = H.arcCount)
    (hTemp : (reg st reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hOutS : (reg st reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount)
    (hInS : (reg st reg5).val = inStartArrBase H.vertexCount r.out.tables.next)
    (hQSrc : (reg st reg6).val = 4 + H.vertexCount + 4 * r.out.tables.next)
    (hQHead : (reg st reg7).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount)
    (hIdx : (reg st reg8).val = k)
    (hOutArr : ∀ u < H.vertexCount,
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
        some (outCountPrefix H k u))
    (hInArr : ∀ v < H.vertexCount,
      (st.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
        some (inCountPrefix H k v))
    (hIndegArr : ∀ v < H.vertexCount,
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (inCountPrefix H k v)) :
    ∃ steps : Nat, ∃ t : State DomL,
      steps ≤ 19 * (H.arcCount - k) + 1 ∧
      Steps code input steps st t ∧ t.pc = 40 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
      (∀ u < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
          some (degOut H u)) ∧
      (∀ v < H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
          some (degIn H v)) ∧
      (∀ v < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (degIn H v)) ∧
      (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≤ j) →
        t.data[j]? = st.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB1 : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) =
      inArcIdArrBase H.vertexCount r.out.tables.next := rfl
  have hB2 : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
  suffices hMain : ∀ d k st, H.arcCount - k = d → k ≤ H.arcCount → st.pc = 21 →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg2).val = H.arcCount →
      (reg st reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount →
      (reg st reg5).val = inStartArrBase H.vertexCount r.out.tables.next →
      (reg st reg6).val = 4 + H.vertexCount + 4 * r.out.tables.next →
      (reg st reg7).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount →
      (reg st reg8).val = k →
      (∀ u < H.vertexCount,
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
          some (outCountPrefix H k u)) →
      (∀ v < H.vertexCount,
        (st.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
          some (inCountPrefix H k v)) →
      (∀ v < H.vertexCount,
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (inCountPrefix H k v)) →
      ∃ steps : Nat, ∃ t : State DomL,
        steps ≤ 19 * (H.arcCount - k) + 1 ∧
        Steps code input steps st t ∧ t.pc = 40 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
        (∀ u < H.vertexCount,
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
            some (degOut H u)) ∧
        (∀ v < H.vertexCount,
          (t.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
            some (degIn H v)) ∧
        (∀ v < H.vertexCount,
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
            some (degIn H v)) ∧
        (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
            (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ j ∧
              j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≤ j) →
          t.data[j]? = st.data[j]?) by
    exact hMain (H.arcCount - k) k st rfl hkLe hpc h0 h1 hMeta hM hTemp hOutS hInS hQSrc hQHead hIdx hOutArr hInArr hIndegArr
  intro d
  induction d with
  | zero =>
    intro k st hd hkLe hpc h0 h1 hMeta hM hTemp hOutS hInS hQSrc hQHead hIdx hOutArr hInArr hIndegArr
    have hkEq : k = H.arcCount := by omega
    have hCmp : code[st.pc]? = some (.branchLt reg8 reg2 22 40) := by rw [hpc]; exact hPl 0 _ rfl
    have hFalse : ¬ ((reg st reg8).val < (reg st reg2).val) := by
      rw [hIdx, hM, hkEq]; exact Nat.lt_irrefl _
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp
      (by rw [ite_eq_right hFalse]; exact hSz)
    rw [ite_eq_right hFalse] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    refine ⟨1, s1, by omega, steps_1_of_step hs1, hpc1,
      by rw [hr1, h0], by rw [hr1, h1], by rw [hr1, hMeta],
      fun u hu => by rw [hd1]; simpa [degOut, hkEq] using hOutArr u hu,
      fun v hv => by rw [hd1]; simpa [degIn, hkEq] using hInArr v hv,
      fun v hv => by rw [hd1]; simpa [degIn, hkEq] using hIndegArr v hv,
      fun j _ => by rw [hd1]⟩
  | succ d ih =>
    intro k st hd hkLe hpc h0 h1 hMeta hM hTemp hOutS hInS hQSrc hQHead hIdx hOutArr hInArr hIndegArr
    have hkLt : k < H.arcCount := by omega
    have hK1Lt : k + 1 < workCap := by omega
    have hCmp : code[st.pc]? = some (.branchLt reg8 reg2 22 40) := by rw [hpc]; exact hPl 0 _ rfl
    have hTrue : (reg st reg8).val < (reg st reg2).val := by rw [hIdx, hM]; exact hkLt
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp
      (by rw [ite_eq_left hTrue]; omega)
    rw [ite_eq_left hTrue] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    have ha1 : code[s1.pc]? = some (.add reg9 reg6 reg8) := by rw [hpc1]; exact hPl 1 _ rfl
    obtain ⟨s2, hs2, hpc2, hr9_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by rw [hpc1]; omega)
    have hAddrSrc : (reg s2 reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + k := by
      have h6 : (reg s1 reg6).val = 4 + H.vertexCount + 4 * r.out.tables.next := by rw [hr1, hQSrc]
      have h8 : (reg s1 reg8).val = k := by rw [hr1, hIdx]
      rw [hr9_2, add_no_wrap _ _ (by rw [h6, h8]; exact Nat.lt_of_lt_of_le (by have := hIn.cap_ge; omega) hi), h6, h8]
    obtain ⟨wSrc, hwSrc, hwSrcV⟩ := Option.map_eq_some_iff.mp (hIn.qSrc_at ⟨k, hkLt⟩)
    have hInSrc : input.words[(reg s2 reg9).val]? = some wSrc := by rw [hAddrSrc]; exact hwSrc
    have hl1 : code[s2.pc]? = some (.loadInput reg9 reg9) := by rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, hpc3, hr9_3, ho3, hd3⟩ := step_loadInput_at (input := input) hl1 (by rw [hpc2, hpc1]; omega) hInSrc
    let u := (rawOccurrence H ⟨k, hkLt⟩).1.val
    have huLt : u < H.vertexCount := (rawOccurrence H ⟨k, hkLt⟩).1.isLt
    have hu3 : (reg s3 reg9).val = u := by rw [hr9_3, hwSrcV]
    have ha2 : code[s3.pc]? = some (.add reg9 reg4 reg9) := by rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, hpc4, hr9_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by rw [hpc3, hpc2, hpc1]; omega)
    have hr4_3 : (reg s3 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      rw [ho3 reg4 (by intro h; cases h), ho2 reg4 (by intro h; cases h), hr1, hOutS]
    have hAddrOut : (reg s4 reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
      rw [hr9_4, add_no_wrap _ _ (by rw [hr4_3, hu3]; exact Nat.lt_of_lt_of_le (by omega) hw), hr4_3, hu3]
    obtain ⟨wOut, hwOut, hwOutV⟩ := Option.map_eq_some_iff.mp (hOutArr u huLt)
    have hMemOut : s4.data[(reg s4 reg9).val]? = some wOut := by
      rw [hAddrOut, hd4, hd3, hd2, hd1]; exact hwOut
    have hl2 : code[s4.pc]? = some (.loadData reg10 reg9) := by rw [hpc4, hpc3, hpc2, hpc1]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, hpc5, hr10_5, ho5, hd5⟩ := step_loadData_at (input := input) hl2 (by rw [hpc4, hpc3, hpc2, hpc1]; omega) hMemOut
    have hOutLeK : outCountPrefix H k u ≤ k := outCountPrefix_le H k u
    have h10_5 : (reg s5 reg10).val = outCountPrefix H k u := by rw [hr10_5, hwOutV]
    have ha3 : code[s5.pc]? = some (.add reg10 reg10 reg1) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 5 _ rfl
    obtain ⟨s6, hs6, hpc6, hr10_6, ho6, hd6⟩ := step_add_at (input := input) ha3 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; omega)
    have hr1_5 : (reg s5 reg1).val = 1 := by
      rw [ho5 reg1 (by intro h; cases h), ho4 reg1 (by intro h; cases h),
        ho3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), hr1, h1]
    have h10_6 : (reg s6 reg10).val = outCountPrefix H k u + 1 := by
      rw [hr10_6, add_no_wrap _ _ (by rw [h10_5, hr1_5]; exact Nat.lt_of_lt_of_le (by omega) hw), h10_5, hr1_5]
    have hr9_6 : (reg s6 reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
      rw [ho6 reg9 (by intro h; cases h), ho5 reg9 (by intro h; cases h), hAddrOut]
    have hLtOut6 : (reg s6 reg9).val < s6.data.size := lt_data_size (by rw [hr9_6]; omega)
    have hst1 : code[s6.pc]? = some (.storeData reg9 reg10) := by
      rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 6 _ rfl
    obtain ⟨s7, hs7, hpc7, hreg7, hd7⟩ := step_storeData_opaque (input := input) hst1 hLtOut6
      (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1]; omega)
    have hr7 : ∀ r : Fin 15, reg s7 r = reg s6 r := reg_of_regs_eq hreg7
    have ha4 : code[s7.pc]? = some (.add reg9 reg7 reg8) := by
      rw [show s7.pc = 21 + 7 by omega]; exact hPl 7 _ rfl
    obtain ⟨s8, hs8, hpc8, hr9_8, ho8, hd8⟩ := step_add_at (input := input) ha4
      (by omega)
    have h7_7 : (reg s7 reg7).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount := by
      rw [hr7, ho6 reg7 (by intro h; cases h), ho5 reg7 (by intro h; cases h),
        ho4 reg7 (by intro h; cases h), ho3 reg7 (by intro h; cases h),
        ho2 reg7 (by intro h; cases h), hr1, hQHead]
    have h8_7 : (reg s7 reg8).val = k := by
      rw [hr7, ho6 reg8 (by intro h; cases h), ho5 reg8 (by intro h; cases h),
        ho4 reg8 (by intro h; cases h), ho3 reg8 (by intro h; cases h),
        ho2 reg8 (by intro h; cases h), hr1, hIdx]
    have hAddrHead : (reg s8 reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + k := by
      rw [hr9_8, add_no_wrap _ _ (by rw [h7_7, h8_7]; exact Nat.lt_of_lt_of_le (by have := hIn.cap_ge; omega) hi), h7_7, h8_7]
    obtain ⟨wHead, hwHead, hwHeadV⟩ := Option.map_eq_some_iff.mp (hIn.qHead_at ⟨k, hkLt⟩)
    have hInHead : input.words[(reg s8 reg9).val]? = some wHead := by rw [hAddrHead]; exact hwHead
    have hl3 : code[s8.pc]? = some (.loadInput reg9 reg9) := by
      rw [show s8.pc = 21 + 8 by omega]; exact hPl 8 _ rfl
    obtain ⟨s9, hs9, hpc9, hr9_9, ho9, hd9⟩ := step_loadInput_at (input := input) hl3 (by omega) hInHead
    let v := (rawHead H ⟨k, hkLt⟩).val
    have hvLt : v < H.vertexCount := (rawHead H ⟨k, hkLt⟩).isLt
    have hInAddrLt : inStartArrBase H.vertexCount r.out.tables.next + v < workCap := by omega
    have hIndegAddrLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + v < workCap := by omega
    have hInLeK : inCountPrefix H k v ≤ k := inCountPrefix_le H k v
    have hInK1Lt : inCountPrefix H k v + 1 < workCap := by omega
    have hv9 : (reg s9 reg9).val = v := by rw [hr9_9, hwHeadV]
    have ha5 : code[s9.pc]? = some (.add reg10 reg5 reg9) := by
      rw [show s9.pc = 21 + 9 by omega]; exact hPl 9 _ rfl
    obtain ⟨s10, hs10, hpc10, hr10_10, ho10, hd10⟩ := step_add_at (input := input) ha5
      (by rw [show s9.pc = 21 + 9 by omega]; exact Nat.lt_trans (by decide) hSz)
    have hpc10' : s10.pc = 21 + 10 := by rw [hpc10]; omega
    have h5_9 : (reg s9 reg5).val = inStartArrBase H.vertexCount r.out.tables.next := by
      rw [ho9 reg5 (by intro h; cases h), ho8 reg5 (by intro h; cases h), hr7,
        ho6 reg5 (by intro h; cases h), ho5 reg5 (by intro h; cases h),
        ho4 reg5 (by intro h; cases h), ho3 reg5 (by intro h; cases h),
        ho2 reg5 (by intro h; cases h), hr1, hInS]
    have hLtInS10 : (reg s9 reg5).val + (reg s9 reg9).val < 2 ^ bits := by
      rw [h5_9, hv9]; exact Nat.lt_of_lt_of_le hInAddrLt hw
    have hAddrInS : (reg s10 reg10).val = inStartArrBase H.vertexCount r.out.tables.next + v := by
      rw [hr10_10, add_no_wrap _ _ hLtInS10, h5_9, hv9]
    have hDisj7 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u ≠
        inStartArrBase H.vertexCount r.out.tables.next + v := by omega
    obtain ⟨wIn, hwIn, hwInV⟩ := Option.map_eq_some_iff.mp (hInArr v hvLt)
    have hMemIn : s10.data[(reg s10 reg10).val]? = some wIn := by
      rw [hAddrInS, hd10, hd9, hd8, hd7,
        Array.getElem?_set_ne hLtOut6 (by rw [hr9_6]; exact hDisj7),
        hd6, hd5, hd4, hd3, hd2, hd1]
      exact hwIn
    have hl4 : code[s10.pc]? = some (.loadData reg11 reg10) := by
      rw [hpc10']; exact hPl 10 _ rfl
    obtain ⟨s11, hs11, hpc11, hr11_11, ho11, hd11⟩ := step_loadData_at (input := input) hl4
      (by rw [hpc10']; exact Nat.lt_trans (by decide) hSz) hMemIn
    have hpc11' : s11.pc = 21 + 11 := by rw [hpc11, hpc10']
    have h11_11 : (reg s11 reg11).val = inCountPrefix H k v := by rw [hr11_11, hwInV]
    have ha6 : code[s11.pc]? = some (.add reg11 reg11 reg1) := by
      rw [hpc11']; exact hPl 11 _ rfl
    obtain ⟨s12, hs12, hpc12, hr11_12, ho12, hd12⟩ := step_add_at (input := input) ha6
      (by rw [hpc11']; exact Nat.lt_trans (by decide) hSz)
    have hpc12' : s12.pc = 21 + 12 := by rw [hpc12, hpc11']
    have h1_11 : (reg s11 reg1).val = 1 := by
      rw [ho11 reg1 (by intro h; cases h), ho10 reg1 (by intro h; cases h),
        ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h), hr7,
        ho6 reg1 (by intro h; cases h), hr1_5]
    have hLt12 : (reg s11 reg11).val + (reg s11 reg1).val < 2 ^ bits := by
      rw [h11_11, h1_11]; exact Nat.lt_of_lt_of_le hInK1Lt hw
    have h11_12 : (reg s12 reg11).val = inCountPrefix H k v + 1 := by
      rw [hr11_12, add_no_wrap _ _ hLt12, h11_11, h1_11]
    have h10_12 : (reg s12 reg10).val = inStartArrBase H.vertexCount r.out.tables.next + v := by
      rw [ho12 reg10 (by intro h; cases h), ho11 reg10 (by intro h; cases h), hAddrInS]
    have hLtIn12 : (reg s12 reg10).val < s12.data.size := lt_data_size (by rw [h10_12]; exact hInAddrLt)
    have hst2 : code[s12.pc]? = some (.storeData reg10 reg11) := by
      rw [hpc12']; exact hPl 12 _ rfl
    obtain ⟨s13, hs13, hpc13, hreg13, hd13⟩ := step_storeData_opaque (input := input) hst2 hLtIn12
      (by rw [hpc12']; exact Nat.lt_trans (by decide) hSz)
    have hpc13' : s13.pc = 21 + 13 := by rw [hpc13, hpc12']
    have hr13 : ∀ r : Fin 15, reg s13 r = reg s12 r := reg_of_regs_eq hreg13
    have ha7 : code[s13.pc]? = some (.add reg10 reg3 reg9) := by
      rw [hpc13']; exact hPl 13 _ rfl
    obtain ⟨s14, hs14, hpc14, hr10_14, ho14, hd14⟩ := step_add_at (input := input) ha7
      (by rw [hpc13']; exact Nat.lt_trans (by decide) hSz)
    have hpc14' : s14.pc = 21 + 14 := by rw [hpc14, hpc13']
    have h3_13 : (reg s13 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [hr13, ho12 reg3 (by intro h; cases h), ho11 reg3 (by intro h; cases h),
        ho10 reg3 (by intro h; cases h), ho9 reg3 (by intro h; cases h), ho8 reg3 (by intro h; cases h),
        hr7, ho6 reg3 (by intro h; cases h), ho5 reg3 (by intro h; cases h),
        ho4 reg3 (by intro h; cases h), ho3 reg3 (by intro h; cases h),
        ho2 reg3 (by intro h; cases h), hr1, hTemp]
    have hv13 : (reg s13 reg9).val = v := by
      rw [hr13, ho12 reg9 (by intro h; cases h), ho11 reg9 (by intro h; cases h),
        ho10 reg9 (by intro h; cases h), hv9]
    have hLtInd14 : (reg s13 reg3).val + (reg s13 reg9).val < 2 ^ bits := by
      rw [h3_13, hv13]; exact Nat.lt_of_lt_of_le hIndegAddrLt hw
    have hAddrIndeg : (reg s14 reg10).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
      rw [hr10_14, add_no_wrap _ _ hLtInd14, h3_13, hv13]
    have hDisj13 : inStartArrBase H.vertexCount r.out.tables.next + v ≠
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
      have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ v)))
    have hDisj7b : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u ≠
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
      rw [Nat.add_assoc]
      exact Nat.ne_of_gt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hvLt (Nat.le_add_right H.vertexCount u)) _)
    obtain ⟨wInd, hwInd, hwIndV⟩ := Option.map_eq_some_iff.mp (hIndegArr v hvLt)
    have hMemInd : s14.data[(reg s14 reg10).val]? = some wInd := by
      rw [hAddrIndeg, hd14, hd13,
        Array.getElem?_set_ne hLtIn12 (by rw [h10_12]; exact hDisj13),
        hd12, hd11, hd10, hd9, hd8, hd7,
        Array.getElem?_set_ne hLtOut6 (by rw [hr9_6]; exact hDisj7b),
        hd6, hd5, hd4, hd3, hd2, hd1]
      exact hwInd
    have hl5 : code[s14.pc]? = some (.loadData reg11 reg10) := by
      rw [hpc14']; exact hPl 14 _ rfl
    obtain ⟨s15, hs15, hpc15, hr11_15, ho15, hd15⟩ := step_loadData_at (input := input) hl5
      (by rw [hpc14']; exact Nat.lt_trans (by decide) hSz) hMemInd
    have hpc15' : s15.pc = 21 + 15 := by rw [hpc15, hpc14']
    have ha8 : code[s15.pc]? = some (.add reg11 reg11 reg1) := by
      rw [hpc15']; exact hPl 15 _ rfl
    obtain ⟨s16, hs16, hpc16, hr11_16, ho16, hd16⟩ := step_add_at (input := input) ha8
      (by rw [hpc15']; exact Nat.lt_trans (by decide) hSz)
    have hpc16' : s16.pc = 21 + 16 := by rw [hpc16, hpc15']
    have h11_15 : (reg s15 reg11).val = inCountPrefix H k v := by rw [hr11_15, hwIndV]
    have h1_15 : (reg s15 reg1).val = 1 := by
      rw [ho15 reg1 (by intro h; cases h), ho14 reg1 (by intro h; cases h),
        hr13, ho12 reg1 (by intro h; cases h), h1_11]
    have hLt16 : (reg s15 reg11).val + (reg s15 reg1).val < 2 ^ bits := by
      rw [h11_15, h1_15]; exact Nat.lt_of_lt_of_le hInK1Lt hw
    have h11_16 : (reg s16 reg11).val = inCountPrefix H k v + 1 := by
      rw [hr11_16, add_no_wrap _ _ hLt16, h11_15, h1_15]
    have h10_16 : (reg s16 reg10).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
      rw [ho16 reg10 (by intro h; cases h), ho15 reg10 (by intro h; cases h), hAddrIndeg]
    have hLtInd16 : (reg s16 reg10).val < s16.data.size := lt_data_size (by rw [h10_16]; exact hIndegAddrLt)
    have hst3 : code[s16.pc]? = some (.storeData reg10 reg11) := by
      rw [hpc16']; exact hPl 16 _ rfl
    obtain ⟨s17, hs17, hpc17, hreg17, hd17⟩ := step_storeData_opaque (input := input) hst3 hLtInd16
      (by rw [hpc16']; exact Nat.lt_trans (by decide) hSz)
    have hpc17' : s17.pc = 21 + 17 := by rw [hpc17, hpc16']
    have hr17 : ∀ r : Fin 15, reg s17 r = reg s16 r := reg_of_regs_eq hreg17
    have ha9 : code[s17.pc]? = some (.add reg8 reg8 reg1) := by
      rw [hpc17']; exact hPl 17 _ rfl
    obtain ⟨s18, hs18, hpc18, hr8_18, ho18, hd18⟩ := step_add_at (input := input) ha9
      (by rw [hpc17']; exact Nat.lt_trans (by decide) hSz)
    have hpc18' : s18.pc = 21 + 18 := by rw [hpc18, hpc17']
    have h8_17 : (reg s17 reg8).val = k := by
      rw [hr17, ho16 reg8 (by intro h; cases h), ho15 reg8 (by intro h; cases h),
        ho14 reg8 (by intro h; cases h), hr13, ho12 reg8 (by intro h; cases h),
        ho11 reg8 (by intro h; cases h), ho10 reg8 (by intro h; cases h),
        ho9 reg8 (by intro h; cases h), ho8 reg8 (by intro h; cases h), h8_7]
    have h1_17 : (reg s17 reg1).val = 1 := by
      rw [hr17, ho16 reg1 (by intro h; cases h), h1_15]
    have hk1Val : (reg s18 reg8).val = k + 1 := by
      rw [hr8_18, add_no_wrap _ _ (by rw [h8_17, h1_17]; exact Nat.lt_of_lt_of_le hK1Lt hw), h8_17, h1_17]
    have hJmp : code[s18.pc]? = some (.goto 21) := by
      rw [hpc18']; exact hPl 18 _ rfl
    obtain ⟨s19, hs19, hpc19, hreg19, hd19⟩ := step_goto_at (input := input) hJmp
      (by exact Nat.lt_trans (by decide) hSz)
    have hr19 : ∀ r : Fin 15, reg s19 r = reg s18 r := reg_of_regs_eq hreg19
    have hKeep19 : ∀ r : Fin 15,
        r ≠ reg8 → r ≠ reg9 → r ≠ reg10 → r ≠ reg11 → reg s19 r = reg st r := by
      intro r hr8 hr9 hr10 hr11
      rw [hr19, ho18 r hr8, hr17, ho16 r hr11, ho15 r hr11, ho14 r hr10, hr13,
        ho12 r hr11, ho11 r hr11, ho10 r hr10, ho9 r hr9, ho8 r hr9, hr7,
        ho6 r hr10, ho5 r hr10, ho4 r hr9, ho3 r hr9, ho2 r hr9, hr1]
    have hStep19 : Steps code input 19 st s19 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12
      (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17
      (Steps.cons hs18 (steps_1_of_step hs19))))))))))))))))))
    have hData19 : ∀ j,
        s19.data[j]? =
          if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v then some (reg s16 reg11)
          else if j = inStartArrBase H.vertexCount r.out.tables.next + v then some (reg s12 reg11)
          else if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u then some (reg s6 reg10)
          else st.data[j]? := by
      intro j
      rw [hd19, hd18, hd17]
      by_cases hA : j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + v
      · subst hA; rw [ite_eq_left rfl, ← h10_16]; simp [hLtInd16]
      · rw [ite_eq_right hA, Array.getElem?_set_ne hLtInd16 (by rw [h10_16]; exact fun hh => hA hh.symm),
          hd16, hd15, hd14, hd13]
        by_cases hB : j = inStartArrBase H.vertexCount r.out.tables.next + v
        · subst hB; rw [ite_eq_left rfl, ← h10_12]; simp [hLtIn12]
        · rw [ite_eq_right hB, Array.getElem?_set_ne hLtIn12 (by rw [h10_12]; exact fun hh => hB hh.symm),
            hd12, hd11, hd10, hd9, hd8, hd7]
          by_cases hC : j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u
          · subst hC; rw [ite_eq_left rfl, ← hr9_6]; simp [hLtOut6]
          · rw [ite_eq_right hC, Array.getElem?_set_ne hLtOut6 (by rw [hr9_6]; exact fun hh => hC hh.symm),
              hd6, hd5, hd4, hd3, hd2, hd1]
    have hSubEq : H.arcCount - (k + 1) = d := by rw [← Nat.sub_sub, hd]; rfl
    have hOutNext : ∀ u' < H.vertexCount,
        (s19.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u']?).map Fin.val =
          some (outCountPrefix H (k + 1) u') := by
      intro u' hu'
      rw [hData19 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u')]
      have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
        rw [Nat.add_assoc]; exact Nat.ne_of_gt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hvLt (Nat.le_add_right _ _)) _)
      have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
          inStartArrBase H.vertexCount r.out.tables.next + v := by
        have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
        rw [Nat.add_assoc]
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
      rw [ite_eq_right hn1, ite_eq_right hn2]
      simp only [outCountPrefix, dite_eq_left hkLt]
      by_cases huEq : u' = u
      · subst huEq; rw [ite_eq_left rfl, ite_eq_left rfl, Option.map_some, h10_6]
      · have hne : u ≠ u' := fun h => huEq h.symm
        have hneAddr : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u :=
          fun h => huEq (Nat.add_left_cancel h)
        rw [ite_eq_right hneAddr, ite_eq_right hne, Nat.add_zero]
        exact hOutArr u' hu'
    have hInNext : ∀ v' < H.vertexCount,
        (s19.data[inStartArrBase H.vertexCount r.out.tables.next + v']?).map Fin.val =
          some (inCountPrefix H (k + 1) v') := by
      intro v' hv'
      rw [hData19 (inStartArrBase H.vertexCount r.out.tables.next + v')]
      have hn1 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
        have h1 := Nat.add_lt_add_left hv' (inStartArrBase H.vertexCount r.out.tables.next)
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
      rw [ite_eq_right hn1]
      simp only [inCountPrefix, dite_eq_left hkLt]
      by_cases hvEq : v' = v
      · subst hvEq; rw [ite_eq_left rfl, ite_eq_left rfl, Option.map_some, h11_12]
      · have hne : v ≠ v' := fun h => hvEq h.symm
        have hn2 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
            inStartArrBase H.vertexCount r.out.tables.next + v :=
          fun h => hvEq (Nat.add_left_cancel h)
        have hn3 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
          have h1 := Nat.add_lt_add_left hv' (inStartArrBase H.vertexCount r.out.tables.next)
          rw [Nat.add_assoc]
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
        rw [ite_eq_right hn2, ite_eq_right hn3, ite_eq_right hne, Nat.add_zero]
        exact hInArr v' hv'
    have hIndNext : ∀ v' < H.vertexCount,
        (s19.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v']?).map Fin.val =
          some (inCountPrefix H (k + 1) v') := by
      intro v' hv'
      rw [hData19 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + v')]
      simp only [inCountPrefix, dite_eq_left hkLt]
      by_cases hvEq : v' = v
      · subst hvEq; rw [ite_eq_left rfl, ite_eq_left rfl, Option.map_some, h11_16]
      · have hne : v ≠ v' := fun h => hvEq h.symm
        have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + v' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + v :=
          fun h => hvEq (Nat.add_left_cancel h)
        have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + v' ≠
            inStartArrBase H.vertexCount r.out.tables.next + v := by
          have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
          exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
        have hn3 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + v' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
          rw [Nat.add_assoc]
          exact Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hv' (Nat.le_add_right _ _)) _)
        rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_right hn3, ite_eq_right hne, Nat.add_zero]
        exact hIndegArr v' hv'
    obtain ⟨kRest, t, hkRest, hStepsRest, hpcT, h0T, h1T, hMetaT, hOutT, hInT, hIndT, hFrT⟩ :=
      ih (k + 1) s19 hSubEq hkLt hpc19
        (by rw [hKeep19 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hKeep19 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hKeep19 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
        (by rw [hKeep19 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM])
        (by rw [hKeep19 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hTemp])
        (by rw [hKeep19 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hOutS])
        (by rw [hKeep19 reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hInS])
        (by rw [hKeep19 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hQSrc])
        (by rw [hKeep19 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hQHead])
        (by rw [hr19, hk1Val])
        hOutNext hInNext hIndNext
    have hkRes : 19 + kRest ≤ 19 * (H.arcCount - k) + 1 := by
      rw [hd]; rw [hSubEq] at hkRest
      exact Nat.le_trans (Nat.add_le_add_left hkRest 19)
        (by rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 19, Nat.add_assoc]; exact Nat.le_refl _)
    refine ⟨19 + kRest, t, hkRes, hStep19.append hStepsRest, hpcT, h0T, h1T, hMetaT,
      hOutT, hInT, hIndT, fun j hj => ?_⟩
    rw [hFrT j hj, hData19 j]
    have hVlt2N : v < 2 * H.vertexCount := by
      rw [Nat.two_mul]; exact Nat.lt_of_lt_of_le hvLt (Nat.le_add_right _ _)
    have hNuLt2N : H.vertexCount + u < 2 * H.vertexCount := by
      rw [Nat.two_mul]; exact Nat.add_lt_add_left huLt _
    have hNe1 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + v := by
      rcases hj with h | ⟨_, h2⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hGapInTemp (Nat.le_add_right _ _))))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2 (Nat.le_add_right _ _))
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hVlt2N _) h)
    have hNe2 : j ≠ inStartArrBase H.vertexCount r.out.tables.next + v := by
      rcases hj with h | ⟨h1, _⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hvLt _) h1)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hvLt _) (Nat.le_trans hGapInTemp (Nat.le_add_right _ _))) h)
    have hNe3 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
      rw [Nat.add_assoc]
      rcases hj with h | ⟨_, h2⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hGapInTemp (Nat.le_add_right _ _))))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2 (Nat.le_add_right _ _))
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hNuLt2N _) h)
    rw [ite_eq_right hNe1, ite_eq_right hNe2, ite_eq_right hNe3]

theorem run_csrCount {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hInZ : ∀ i ≤ H.vertexCount,
      (s0.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some 0)
    (hTempZ : ∀ i < 2 * H.vertexCount + 1,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + i]?).map Fin.val = some 0) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 19 * H.arcCount + 25 ∧
      run (csrCountPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ u < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
          some (degOut H u)) ∧
      (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
        some 0 ∧
      (∀ v < H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
          some (degIn H v)) ∧
      (t.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
        some 0 ∧
      (∀ v < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (degIn H v)) ∧
      (∀ j, j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≤ j →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB1 : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) =
      inArcIdArrBase H.vertexCount r.out.tables.next := rfl
  have hB2 : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
  have hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ 2 ^ bits := by omega
  let ph := csrCountPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (csrCountInstrs (bits := bits) h100).length = 40 := by
    simp [csrCountInstrs, csrCountSetupInstrs, csrCountLoopInstrs, metaLoadInstrs]
  have hCodeSize : ph.code.size = 41 := by
    dsimp [ph, csrCountPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (csrCountInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold csrCountInstrs at hPlFull; exact hPlFull)
  have hPlLoop := Placed_append_right (by unfold csrCountInstrs at hPlFull; exact hPlFull)
  rw [show (csrCountSetupInstrs (bits := bits) h100).length = 21 by
    simp [csrCountSetupInstrs, metaLoadInstrs]] at hPlLoop
  have hPlM := Placed_append_left (by unfold csrCountSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold csrCountSetupInstrs at hPlSetup; exact hPlSetup)
  rw [hLml] at hPlS1
  have hPlBr := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1
  rw [show ([Instr.branchLt reg0 reg2 4 40] : List (Instr bits 15)).length = 1 by rfl] at hPlS2
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlM (by omega)
    rfl hMeta.rMeta_eq (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) hMeta.meta_m
  have h0_1 : (reg s1 reg0).val = 0 := by rw [ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_1 : (reg s1 reg1).val = 1 := by rw [ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  have hBr : ph.code[s1.pc]? = some (.branchLt reg0 reg2 4 40) := by rw [hpc1]; exact hPlBr 0 _ rfl
  by_cases hmZero : H.arcCount = 0
  · have hFalse : ¬ ((reg s1 reg0).val < (reg s1 reg2).val) := by rw [h0_1, h2_1, hmZero]; exact Nat.lt_irrefl _
    obtain ⟨s2, hs2, hpc2, hreg2, hd2⟩ := step_branchLt_at (input := input) hBr (by rw [ite_eq_right hFalse]; omega)
    rw [ite_eq_right hFalse] at hpc2
    have hr2 : ∀ r : Fin 15, reg s2 r = reg s1 r := reg_of_regs_eq hreg2
    have hAllSteps : Steps ph.code input 4 (Phase.initial s0) s2 := hs1.append (steps_1_of_step hs2)
    have hHalt : step ph.code input s2 = some (.halted s2) :=
      haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrCountInstrs (bits := bits) h100) _
        (by rw [hpc2, hCodeLen]) (input := input)
    have hDegOut0 : ∀ u, degOut H u = 0 := fun u => by simp [degOut, hmZero, outCountPrefix]
    have hDegIn0 : ∀ v, degIn H v = 0 := fun v => by simp [degIn, hmZero, inCountPrefix]
    refine ⟨4 + 1, s2, by omega, hAllSteps.halts hHalt, ?_,
      fun u hu => by rw [hd2, hd1, data_initial, hDegOut0 u, Nat.add_assoc]; exact hTempZ (H.vertexCount + u) (by omega),
      by rw [hd2, hd1, data_initial]; exact hTempZ (2 * H.vertexCount) (by omega),
      fun v hv => by rw [hd2, hd1, data_initial, hDegIn0 v]; exact hInZ v (by omega),
      by rw [hd2, hd1, data_initial]; exact hInZ H.vertexCount (by omega),
      fun v hv => by rw [hd2, hd1, data_initial, hDegIn0 v]; exact hTempZ v (by omega),
      fun j _ => by rw [hd2, hd1, data_initial]⟩
    · apply hMeta.preserve
      · rw [hr2, hMeta1]
      · rw [hr2, h0_1]
      · rw [hr2, h1_1]
      · intro i _; rw [hd2, hd1, data_initial]
  · have hmPos : 0 < H.arcCount := Nat.pos_of_ne_zero hmZero
    have hTrue : (reg s1 reg0).val < (reg s1 reg2).val := by rw [h0_1, h2_1]; exact hmPos
    obtain ⟨s2, hs2, hpc2, hreg2, hd2⟩ := step_branchLt_at (input := input) hBr (by rw [ite_eq_left hTrue]; omega)
    rw [ite_eq_left hTrue] at hpc2
    have hr2 : ∀ r : Fin 15, reg s2 r = reg s1 r := reg_of_regs_eq hreg2
    have hPlTemp := Placed_append_left hPlS2
    have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
    have hPlN := Placed_append_left hPlS3
    have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
    have hPlAdd := Placed_append_left hPlS4
    have hPlS5 := Placed_append_right hPlS4
    rw [show ([Instr.add reg4 reg3 reg4] : List (Instr bits 15)).length = 1 by rfl] at hPlS5
    have hPlInS := Placed_append_left hPlS5
    have hPlS6 := Placed_append_right hPlS5; rw [hLml] at hPlS6
    have hPlQSrc := Placed_append_left hPlS6
    have hPlS7 := Placed_append_right hPlS6; rw [hLml] at hPlS7
    have hPlQHead := Placed_append_left hPlS7
    have hPlMov := Placed_append_right hPlS7; rw [hLml] at hPlMov
    have hMeta2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by rw [hr2, hMeta1]
    have hd2' : s2.data = s0.data := by rw [hd2, hd1, data_initial]
    obtain ⟨s3, hs3, hpc3, hd3, h3_3, ho3⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlTemp (by omega)
      (by omega) hMeta2 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd2']; exact hMeta.meta_tempBase)
    have hMeta3 : (reg s3 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho3 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta2
    obtain ⟨s4, hs4, hpc4, hd4, h4_4, ho4⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlN (by omega)
      hpc3 hMeta3 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd3, hd2']; exact hMeta.meta_n)
    have h3_4 : (reg s4 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho4 reg3 (by intro h; cases h) (by intro h; cases h), h3_3]
    have hAdd : ph.code[s4.pc]? = some (.add reg4 reg3 reg4) := by rw [hpc4]; exact hPlAdd 0 _ rfl
    obtain ⟨s5, hs5, hpc5, h4_5, ho5, hd5⟩ := step_add_at (input := input) hAdd (by omega)
    have hOutS5 : (reg s5 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      rw [h4_5, add_no_wrap _ _ (by rw [h3_4, h4_4]; exact Nat.lt_of_lt_of_le (by omega) hw), h3_4, h4_4]
    have hMeta5 : (reg s5 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho5 rMeta (by intro h; cases h), ho4 rMeta (by intro h; cases h) (by intro h; cases h), hMeta3]
    have hd5' : s5.data = s0.data := by rw [hd5, hd4, hd3, hd2']
    obtain ⟨s6, hs6, hpc6, hd6, h5_6, ho6⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlInS (by omega)
      (by omega) hMeta5 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd5']; exact hMeta.meta_inStartBase)
    have hMeta6 : (reg s6 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho6 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta5
    obtain ⟨s7, hs7, hpc7, hd7, h6_7, ho7⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlQSrc (by omega)
      hpc6 hMeta6 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd6, hd5']; exact hMeta.meta_qSrcIn hmPos)
    have hMeta7 : (reg s7 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho7 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta6
    obtain ⟨s8, hs8, hpc8, hd8, h7_8, ho8⟩ := run_metaLoad_slice (input := input)
      (by intro h; cases h) (by intro h; cases h) hPlQHead (by omega)
      hpc7 hMeta7 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd7, hd6, hd5']; exact hMeta.meta_qHeadIn hmPos)
    have hMov : ph.code[s8.pc]? = some (.mov reg8 reg0) := by rw [hpc8]; exact hPlMov 0 _ rfl
    obtain ⟨s9, hs9, hpc9, h8_9, ho9, hd9⟩ := step_mov_at (input := input) hMov (by omega)
    have hd9' : s9.data = s0.data := by rw [hd9, hd8, hd7, hd6, hd5']
    have h0_9 : (reg s9 reg0).val = 0 := by
      rw [ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h) (by intro h; cases h),
        ho7 reg0 (by intro h; cases h) (by intro h; cases h), ho6 reg0 (by intro h; cases h) (by intro h; cases h),
        ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h) (by intro h; cases h),
        ho3 reg0 (by intro h; cases h) (by intro h; cases h), hr2, h0_1]
    have h1_9 : (reg s9 reg1).val = 1 := by
      rw [ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h) (by intro h; cases h),
        ho7 reg1 (by intro h; cases h) (by intro h; cases h), ho6 reg1 (by intro h; cases h) (by intro h; cases h),
        ho5 reg1 (by intro h; cases h), ho4 reg1 (by intro h; cases h) (by intro h; cases h),
        ho3 reg1 (by intro h; cases h) (by intro h; cases h), hr2, h1_1]
    have hMeta9 : (reg s9 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h) (by intro h; cases h), hMeta7]
    have h2_9 : (reg s9 reg2).val = H.arcCount := by
      rw [ho9 reg2 (by intro h; cases h), ho8 reg2 (by intro h; cases h) (by intro h; cases h),
        ho7 reg2 (by intro h; cases h) (by intro h; cases h), ho6 reg2 (by intro h; cases h) (by intro h; cases h),
        ho5 reg2 (by intro h; cases h), ho4 reg2 (by intro h; cases h) (by intro h; cases h),
        ho3 reg2 (by intro h; cases h) (by intro h; cases h), hr2, h2_1]
    have h3_9 : (reg s9 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
      rw [ho9 reg3 (by intro h; cases h), ho8 reg3 (by intro h; cases h) (by intro h; cases h),
        ho7 reg3 (by intro h; cases h) (by intro h; cases h), ho6 reg3 (by intro h; cases h) (by intro h; cases h),
        ho5 reg3 (by intro h; cases h), h3_4]
    have h4_9 : (reg s9 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      rw [ho9 reg4 (by intro h; cases h), ho8 reg4 (by intro h; cases h) (by intro h; cases h),
        ho7 reg4 (by intro h; cases h) (by intro h; cases h), ho6 reg4 (by intro h; cases h) (by intro h; cases h),
        hOutS5]
    have h5_9 : (reg s9 reg5).val = inStartArrBase H.vertexCount r.out.tables.next := by
      rw [ho9 reg5 (by intro h; cases h), ho8 reg5 (by intro h; cases h) (by intro h; cases h),
        ho7 reg5 (by intro h; cases h) (by intro h; cases h), h5_6]
    have h6_9 : (reg s9 reg6).val = 4 + H.vertexCount + 4 * r.out.tables.next := by
      rw [ho9 reg6 (by intro h; cases h), ho8 reg6 (by intro h; cases h) (by intro h; cases h), h6_7]
    have h7_9 : (reg s9 reg7).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount := by
      rw [ho9 reg7 (by intro h; cases h), h7_8]
    have h8_9' : (reg s9 reg8).val = 0 := by rw [h8_9, ← ho9 reg0 (by intro h; cases h), h0_9]
    obtain ⟨kLoop, t, hkLoop, hStepsLoop, hpcT, h0T, h1T, hMetaT, hOutT, hInT, hIndT, hFrT⟩ :=
      csrCountLoop_spec hIn hWork hPlLoop (by omega) 0 (Nat.zero_le _) s9 (by omega)
        h0_9 h1_9 hMeta9 h2_9 h3_9 h4_9 h5_9 h6_9 h7_9 h8_9'
        (fun u hu => by
          change (s9.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val = some 0
          rw [hd9', Nat.add_assoc]; exact hTempZ (H.vertexCount + u) (by omega))
        (fun v hv => by
          change (s9.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val = some 0
          rw [hd9']; exact hInZ v (by omega))
        (fun v hv => by
          change (s9.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val = some 0
          rw [hd9']; exact hTempZ v (by omega))
    have hSetupSteps : Steps ph.code input 21 (Phase.initial s0) s9 :=
      hs1.append ((steps_1_of_step hs2).append (hs3.append (hs4.append
        ((steps_1_of_step hs5).append (hs6.append (hs7.append (hs8.append (steps_1_of_step hs9))))))))
    have hHalt : step ph.code input t = some (.halted t) :=
      haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrCountInstrs (bits := bits) h100) _
        (by rw [hpcT, hCodeLen]) (input := input)
    have hMetaFrame : ∀ i < 22,
        inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
          metaArrBase H.vertexCount H.arcCount r.out.tables.next + i ∧
        metaArrBase H.vertexCount H.arcCount r.out.tables.next + i <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := fun i hi22 => by omega
    have hInNFrame :
        inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
          inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ∧
        inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
    have hTemp2NGe :
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≤
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount := Nat.le_refl _
    have h2NLe : 2 * H.vertexCount < 2 * H.vertexCount + 1 := Nat.lt_succ_self _
    have hNLeN : H.vertexCount ≤ H.vertexCount := Nat.le_refl _
    have hkRes : 21 + kLoop + 1 ≤ 19 * H.arcCount + 25 := by
      simp only [Nat.sub_zero] at hkLoop; omega
    refine ⟨21 + kLoop + 1, t, hkRes, (hSetupSteps.append hStepsLoop).halts hHalt, ?_,
      hOutT,
      by
        rw [hFrT (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount)
          (Or.inr (Or.inr hTemp2NGe)), hd9']
        exact hTempZ (2 * H.vertexCount) h2NLe,
      hInT,
      by
        rw [hFrT (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount)
          (Or.inr (Or.inl hInNFrame)), hd9']
        exact hInZ H.vertexCount hNLeN,
      hIndT,
      fun j hj => by rw [hFrT j hj, hd9']⟩
    · apply hMeta.preserve hMetaT h0T h1T
      intro i hi22
      rw [hFrT (metaArrBase H.vertexCount H.arcCount r.out.tables.next + i)
        (Or.inr (Or.inl (hMetaFrame i hi22))), hd9']

end CsrCountPhase

section CsrPrefix

variable {bits : Nat}

def csrPrefixSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg8 mIdxN (by change 0 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg3 reg8 mIdxInStartBase (by change 10 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg4 reg8 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  [ .add reg4 reg4 reg2
  , .add reg2 reg2 reg1
  , .mov reg5 reg0
  , .mov reg6 reg0
  , .mov reg7 reg0
  ]))

def csrPrefixLoopInstrs : List (Instr bits 15) :=
  [ .branchLt reg5 reg2 15 25
  , .add reg8 reg3 reg5
  , .loadData reg9 reg8
  , .storeData reg8 reg6
  , .add reg6 reg6 reg9
  , .add reg8 reg4 reg5
  , .loadData reg9 reg8
  , .storeData reg8 reg7
  , .add reg7 reg7 reg9
  , .add reg5 reg5 reg1
  , .goto 14
  ]

def csrPrefixInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  csrPrefixSetupInstrs h100 ++ csrPrefixLoopInstrs

end CsrPrefix

section CsrPrefixPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def csrPrefixPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (csrPrefixInstrs (bits := bits) h100)
    (by simp [csrPrefixInstrs, csrPrefixSetupInstrs, csrPrefixLoopInstrs, metaLoadInstrs, nonHalt])

private theorem degIn_vertexCount (H : LabelledQuotient) : degIn H H.vertexCount = 0 := by
  unfold degIn
  induction H.arcCount with
  | zero => rfl
  | succ a iha =>
    simp only [inCountPrefix]
    by_cases ha : a < H.arcCount
    · rw [dite_eq_left ha]
      have hne : (rawHead H ⟨a, ha⟩).val ≠ H.vertexCount := Nat.ne_of_lt (rawHead H ⟨a, ha⟩).isLt
      rw [ite_eq_right hne]; exact iha
    · rw [dite_eq_right ha]; exact iha

private theorem degOut_vertexCount (H : LabelledQuotient) : degOut H H.vertexCount = 0 := by
  unfold degOut
  induction H.arcCount with
  | zero => rfl
  | succ a iha =>
    simp only [outCountPrefix]
    by_cases ha : a < H.arcCount
    · rw [dite_eq_left ha]
      have hne : (rawOccurrence H ⟨a, ha⟩).1.val ≠ H.vertexCount :=
        Nat.ne_of_lt (rawOccurrence H ⟨a, ha⟩).1.isLt
      rw [ite_eq_right hne]; exact iha
    · rw [dite_eq_right ha]; exact iha

private theorem csrPrefixLoop_spec {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hPl : Placed code 14 csrPrefixLoopInstrs) (hSz : 25 < code.size)
    (k : Nat) (hkLe : k ≤ H.vertexCount + 1)
    (st : State DomL) (hpc : st.pc = 14)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hMeta : (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hN1 : (reg st reg2).val = H.vertexCount + 1)
    (hInS : (reg st reg3).val = inStartArrBase H.vertexCount r.out.tables.next)
    (hOutS : (reg st reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount)
    (hIdx : (reg st reg5).val = k)
    (hAccIn : (reg st reg6).val = prefixIn H k)
    (hAccOut : (reg st reg7).val = prefixOut H k)
    (hInDone : ∀ i < k,
      (st.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i))
    (hInTodo : ∀ i, k ≤ i → i ≤ H.vertexCount →
      (st.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val =
        some (if i < H.vertexCount then degIn H i else 0))
    (hOutDone : ∀ i < k,
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i))
    (hOutTodo : ∀ i, k ≤ i → i ≤ H.vertexCount →
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (if i < H.vertexCount then degOut H i else 0)) :
    ∃ steps : Nat, ∃ t : State DomL,
      steps ≤ 11 * (H.vertexCount + 1 - k) + 1 ∧
      Steps code input steps st t ∧ t.pc = 25 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
      (∀ i ≤ H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)) ∧
      (∀ i ≤ H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (prefixOut H i)) ∧
      (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) ≤ j) →
        t.data[j]? = st.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB1 : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) =
      inArcIdArrBase H.vertexCount r.out.tables.next := rfl
  have hB2 : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
  suffices hMain : ∀ d k st, H.vertexCount + 1 - k = d → k ≤ H.vertexCount + 1 → st.pc = 14 →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg2).val = H.vertexCount + 1 →
      (reg st reg3).val = inStartArrBase H.vertexCount r.out.tables.next →
      (reg st reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount →
      (reg st reg5).val = k →
      (reg st reg6).val = prefixIn H k →
      (reg st reg7).val = prefixOut H k →
      (∀ i < k,
        (st.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)) →
      (∀ i, k ≤ i → i ≤ H.vertexCount →
        (st.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val =
          some (if i < H.vertexCount then degIn H i else 0)) →
      (∀ i < k,
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (prefixOut H i)) →
      (∀ i, k ≤ i → i ≤ H.vertexCount →
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (if i < H.vertexCount then degOut H i else 0)) →
      ∃ steps : Nat, ∃ t : State DomL,
        steps ≤ 11 * (H.vertexCount + 1 - k) + 1 ∧
        Steps code input steps st t ∧ t.pc = 25 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
        (∀ i ≤ H.vertexCount,
          (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)) ∧
        (∀ i ≤ H.vertexCount,
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
            some (prefixOut H i)) ∧
        (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
            (inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) ≤ j ∧
              j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) ≤ j) →
          t.data[j]? = st.data[j]?) by
    exact hMain (H.vertexCount + 1 - k) k st rfl hkLe hpc h0 h1 hMeta hN1 hInS hOutS hIdx hAccIn hAccOut hInDone hInTodo hOutDone hOutTodo
  intro d
  induction d with
  | zero =>
    intro k st hd hkLe hpc h0 h1 hMeta hN1 hInS hOutS hIdx hAccIn hAccOut hInDone hInTodo hOutDone hOutTodo
    have hkEq : k = H.vertexCount + 1 := by omega
    have hCmp : code[st.pc]? = some (.branchLt reg5 reg2 15 25) := by rw [hpc]; exact hPl 0 _ rfl
    have hFalse : ¬ ((reg st reg5).val < (reg st reg2).val) := by
      rw [hIdx, hN1, hkEq]; exact Nat.lt_irrefl _
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp (by rw [ite_eq_right hFalse]; exact hSz)
    rw [ite_eq_right hFalse] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    refine ⟨1, s1, by omega, steps_1_of_step hs1, hpc1,
      by rw [hr1, h0], by rw [hr1, h1], by rw [hr1, hMeta],
      fun i hi => by rw [hd1]; exact hInDone i (by omega),
      fun i hi => by rw [hd1]; exact hOutDone i (by omega),
      fun j _ => by rw [hd1]⟩
  | succ d ih =>
    intro k st hd hkLe hpc h0 h1 hMeta hN1 hInS hOutS hIdx hAccIn hAccOut hInDone hInTodo hOutDone hOutTodo
    have hkLt : k < H.vertexCount + 1 := by omega
    have hkLeN : k ≤ H.vertexCount := by omega
    have hPrefInLe : prefixIn H (k + 1) ≤ H.arcCount := by
      by_cases hk : k < H.vertexCount
      · calc prefixIn H (k + 1) ≤ prefixIn H H.vertexCount := prefixIn_mono H hk
          _ = H.arcCount := prefixIn_vertexCount H
      · have hkEqN : k = H.vertexCount := by omega
        rw [hkEqN]
        change prefixIn H H.vertexCount + degIn H H.vertexCount ≤ H.arcCount
        rw [prefixIn_vertexCount H, degIn_vertexCount H]; omega
    have hPrefOutLe : prefixOut H (k + 1) ≤ H.arcCount := by
      by_cases hk : k < H.vertexCount
      · calc prefixOut H (k + 1) ≤ prefixOut H H.vertexCount := prefixOut_mono H hk
          _ = H.arcCount := prefixOut_vertexCount H
      · have hkEqN : k = H.vertexCount := by omega
        rw [hkEqN]
        change prefixOut H H.vertexCount + degOut H H.vertexCount ≤ H.arcCount
        rw [prefixOut_vertexCount H, degOut_vertexCount H]; omega
    have hCmp : code[st.pc]? = some (.branchLt reg5 reg2 15 25) := by rw [hpc]; exact hPl 0 _ rfl
    have hTrue : (reg st reg5).val < (reg st reg2).val := by rw [hIdx, hN1]; exact hkLt
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp (by rw [ite_eq_left hTrue]; omega)
    rw [ite_eq_left hTrue] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    have ha1 : code[s1.pc]? = some (.add reg8 reg3 reg5) := by rw [hpc1]; exact hPl 1 _ rfl
    obtain ⟨s2, hs2, hpc2, hr8_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by rw [hpc1]; omega)
    have hAddrIn : (reg s2 reg8).val = inStartArrBase H.vertexCount r.out.tables.next + k := by
      have h3 : (reg s1 reg3).val = inStartArrBase H.vertexCount r.out.tables.next := by rw [hr1, hInS]
      have h5 : (reg s1 reg5).val = k := by rw [hr1, hIdx]
      rw [hr8_2, add_no_wrap _ _ (by rw [h3, h5]; exact Nat.lt_of_lt_of_le (by omega) hw), h3, h5]
    obtain ⟨wIn, hwIn, hwInV⟩ := Option.map_eq_some_iff.mp (hInTodo k (Nat.le_refl _) hkLeN)
    have hMemIn : s2.data[(reg s2 reg8).val]? = some wIn := by rw [hAddrIn, hd2, hd1]; exact hwIn
    have hl1 : code[s2.pc]? = some (.loadData reg9 reg8) := by rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, hpc3, hr9_3, ho3, hd3⟩ := step_loadData_at (input := input) hl1 (by rw [hpc2, hpc1]; omega) hMemIn
    have h9_3 : (reg s3 reg9).val = if k < H.vertexCount then degIn H k else 0 := by rw [hr9_3, hwInV]
    have hr8_3 : (reg s3 reg8).val = inStartArrBase H.vertexCount r.out.tables.next + k := by
      rw [ho3 reg8 (by intro h; cases h), hAddrIn]
    have hLtIn3 : (reg s3 reg8).val < s3.data.size := lt_data_size (by rw [hr8_3]; omega)
    have hst1 : code[s3.pc]? = some (.storeData reg8 reg6) := by rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
    obtain ⟨hs4, hpc4, _⟩ := step_storeData_at (input := input) hst1 hLtIn3 (by rw [hpc3, hpc2, hpc1]; omega)
    let s4 : State DomL :=
      { s3 with
        data := s3.data.set (reg s3 reg8).val (reg s3 reg6) hLtIn3
        pc := s3.pc + 1
        data_size := by simp only [Array.size_set, s3.data_size] }
    have hpc4 : s4.pc = s3.pc + 1 := rfl
    have ha2 : code[s4.pc]? = some (.add reg6 reg6 reg9) := by
      rw [show s4.pc = 14 + 4 by omega]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, hpc5, hr6_5, ho5, hd5⟩ := step_add_at (input := input) ha2 (by omega)
    have h6_4 : (reg s4 reg6).val = prefixIn H k := by
      change (reg s3 reg6).val = _
      rw [ho3 reg6 (by intro h; cases h), ho2 reg6 (by intro h; cases h), hr1, hAccIn]
    have hAccInNext : (reg s5 reg6).val = prefixIn H (k + 1) := by
      have hSum : prefixIn H k + (if k < H.vertexCount then degIn H k else 0) = prefixIn H (k + 1) := by
        by_cases hk : k < H.vertexCount
        · rw [ite_eq_left hk]; rfl
        · have hkEqN : k = H.vertexCount := by omega
          rw [ite_eq_right hk, hkEqN]
          change prefixIn H H.vertexCount + 0 = prefixIn H H.vertexCount + degIn H H.vertexCount
          rw [degIn_vertexCount H]
      have hr9_4 : (reg s4 reg9).val = if k < H.vertexCount then degIn H k else 0 := h9_3
      rw [hr6_5, add_no_wrap _ _ (by rw [h6_4, hr9_4, hSum]; exact Nat.lt_of_lt_of_le (by omega) hw), h6_4, hr9_4, hSum]
    have ha3 : code[s5.pc]? = some (.add reg8 reg4 reg5) := by
      rw [show s5.pc = 14 + 5 by omega]; exact hPl 5 _ rfl
    obtain ⟨s6, hs6, hpc6, hr8_6, ho6, hd6⟩ := step_add_at (input := input) ha3 (by omega)
    have h4_5 : (reg s5 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      rw [ho5 reg4 (by intro h; cases h)]
      change (reg s3 reg4).val = _
      rw [ho3 reg4 (by intro h; cases h), ho2 reg4 (by intro h; cases h), hr1, hOutS]
    have h5_5 : (reg s5 reg5).val = k := by
      rw [ho5 reg5 (by intro h; cases h)]
      change (reg s3 reg5).val = _
      rw [ho3 reg5 (by intro h; cases h), ho2 reg5 (by intro h; cases h), hr1, hIdx]
    have hAddrOut : (reg s6 reg8).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by
      rw [hr8_6, add_no_wrap _ _ (by rw [h4_5, h5_5]; exact Nat.lt_of_lt_of_le (by omega) hw), h4_5, h5_5]
    have hDisj4 : inStartArrBase H.vertexCount r.out.tables.next + k ≠
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by omega
    obtain ⟨wOut, hwOut, hwOutV⟩ := Option.map_eq_some_iff.mp (hOutTodo k (Nat.le_refl _) hkLeN)
    have hMemOut : s6.data[(reg s6 reg8).val]? = some wOut := by
      rw [hAddrOut, hd6, hd5]
      change (s3.data.set (reg s3 reg8).val (reg s3 reg6) hLtIn3)[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k]? = some wOut
      rw [Array.getElem?_set_ne hLtIn3 (by rw [hr8_3]; exact hDisj4), hd3, hd2, hd1]
      exact hwOut
    have hl2 : code[s6.pc]? = some (.loadData reg9 reg8) := by
      rw [show s6.pc = 14 + 6 by omega]; exact hPl 6 _ rfl
    obtain ⟨s7, hs7, hpc7, hr9_7, ho7, hd7⟩ := step_loadData_at (input := input) hl2 (by omega) hMemOut
    have h9_7 : (reg s7 reg9).val = if k < H.vertexCount then degOut H k else 0 := by rw [hr9_7, hwOutV]
    have hr8_7 : (reg s7 reg8).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by
      rw [ho7 reg8 (by intro h; cases h), hAddrOut]
    have hLtOut7 : (reg s7 reg8).val < s7.data.size := lt_data_size (by rw [hr8_7]; omega)
    have hst2 : code[s7.pc]? = some (.storeData reg8 reg7) := by
      rw [show s7.pc = 14 + 7 by omega]; exact hPl 7 _ rfl
    obtain ⟨hs8, hpc8, _⟩ := step_storeData_at (input := input) hst2 hLtOut7 (by omega)
    let s8 : State DomL :=
      { s7 with
        data := s7.data.set (reg s7 reg8).val (reg s7 reg7) hLtOut7
        pc := s7.pc + 1
        data_size := by simp only [Array.size_set, s7.data_size] }
    have hpc8 : s8.pc = s7.pc + 1 := rfl
    have ha4 : code[s8.pc]? = some (.add reg7 reg7 reg9) := by
      rw [show s8.pc = 14 + 8 by omega]; exact hPl 8 _ rfl
    obtain ⟨s9, hs9, hpc9, hr7_9, ho9, hd9⟩ := step_add_at (input := input) ha4 (by omega)
    have h7_8 : (reg s8 reg7).val = prefixOut H k := by
      change (reg s7 reg7).val = _
      rw [ho7 reg7 (by intro h; cases h), ho6 reg7 (by intro h; cases h), ho5 reg7 (by intro h; cases h)]
      change (reg s3 reg7).val = _
      rw [ho3 reg7 (by intro h; cases h), ho2 reg7 (by intro h; cases h), hr1, hAccOut]
    have hAccOutNext : (reg s9 reg7).val = prefixOut H (k + 1) := by
      have hSum : prefixOut H k + (if k < H.vertexCount then degOut H k else 0) = prefixOut H (k + 1) := by
        by_cases hk : k < H.vertexCount
        · rw [ite_eq_left hk]; rfl
        · have hkEqN : k = H.vertexCount := by omega
          rw [ite_eq_right hk, hkEqN]
          change prefixOut H H.vertexCount + 0 = prefixOut H H.vertexCount + degOut H H.vertexCount
          rw [degOut_vertexCount H]
      have hr9_8 : (reg s8 reg9).val = if k < H.vertexCount then degOut H k else 0 := h9_7
      rw [hr7_9, add_no_wrap _ _ (by rw [h7_8, hr9_8, hSum]; exact Nat.lt_of_lt_of_le (by omega) hw), h7_8, hr9_8, hSum]
    have ha5 : code[s9.pc]? = some (.add reg5 reg5 reg1) := by
      rw [show s9.pc = 14 + 9 by omega]; exact hPl 9 _ rfl
    obtain ⟨s10, hs10, hpc10, hr5_10, ho10, hd10⟩ := step_add_at (input := input) ha5 (by omega)
    have h5_9 : (reg s9 reg5).val = k := by
      rw [ho9 reg5 (by intro h; cases h)]
      change (reg s7 reg5).val = _
      rw [ho7 reg5 (by intro h; cases h), ho6 reg5 (by intro h; cases h),
        ho5 reg5 (by intro h; cases h)]
      change (reg s3 reg5).val = _
      rw [ho3 reg5 (by intro h; cases h), ho2 reg5 (by intro h; cases h), hr1, hIdx]
    have h1_9 : (reg s9 reg1).val = 1 := by
      rw [ho9 reg1 (by intro h; cases h)]
      change (reg s7 reg1).val = _
      rw [ho7 reg1 (by intro h; cases h), ho6 reg1 (by intro h; cases h),
        ho5 reg1 (by intro h; cases h)]
      change (reg s3 reg1).val = _
      rw [ho3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), hr1, h1]
    have hk1Val : (reg s10 reg5).val = k + 1 := by
      rw [hr5_10, add_no_wrap _ _ (by rw [h5_9, h1_9]; exact Nat.lt_of_lt_of_le (by omega) hw), h5_9, h1_9]
    have hJmp : code[s10.pc]? = some (.goto 14) := by
      rw [show s10.pc = 14 + 10 by omega]; exact hPl 10 _ rfl
    obtain ⟨s11, hs11, hpc11, hreg11, hd11⟩ := step_goto_at (input := input) hJmp (by omega)
    have hr11 : ∀ r : Fin 15, reg s11 r = reg s10 r := reg_of_regs_eq hreg11
    have hKeep11 : ∀ r : Fin 15,
        r ≠ reg5 → r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg9 → reg s11 r = reg st r := by
      intro r hr5 hr6 hr7 hr8 hr9
      rw [hr11, ho10 r hr5, ho9 r hr7]
      change reg s7 r = reg st r
      rw [ho7 r hr9, ho6 r hr8, ho5 r hr6]
      change reg s3 r = reg st r
      rw [ho3 r hr9, ho2 r hr8, hr1]
    have hData11 : ∀ j,
        s11.data[j]? =
          if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k then some (reg s7 reg7)
          else if j = inStartArrBase H.vertexCount r.out.tables.next + k then some (reg s3 reg6)
          else st.data[j]? := by
      intro j
      rw [hd11, hd10, hd9]
      change (s7.data.set (reg s7 reg8).val (reg s7 reg7) hLtOut7)[j]? = _
      by_cases hA : j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k
      · subst hA; rw [ite_eq_left rfl, ← hr8_7]; simp [hLtOut7]
      · rw [ite_eq_right hA, Array.getElem?_set_ne hLtOut7 (by rw [hr8_7]; exact fun hh => hA hh.symm),
          hd7, hd6, hd5]
        change (s3.data.set (reg s3 reg8).val (reg s3 reg6) hLtIn3)[j]? = _
        by_cases hB : j = inStartArrBase H.vertexCount r.out.tables.next + k
        · subst hB; rw [ite_eq_left rfl, ← hr8_3]; simp [hLtIn3]
        · rw [ite_eq_right hB, Array.getElem?_set_ne hLtIn3 (by rw [hr8_3]; exact fun hh => hB hh.symm),
            hd3, hd2, hd1]
    have hStep11 : Steps code input 11 st s11 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (steps_1_of_step hs11))))))))))
    obtain ⟨kRest, t, hkRest, hStepsRest, hpcT, h0T, h1T, hMetaT, hInRes, hOutRes, hFrT⟩ :=
      ih (k + 1) s11 (by omega) hkLt hpc11
        (by rw [hKeep11 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hKeep11 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hKeep11 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
        (by rw [hKeep11 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hN1])
        (by rw [hKeep11 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hInS])
        (by rw [hKeep11 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hOutS])
        (by rw [hr11, hk1Val])
        (by rw [hr11, ho10 reg6 (by intro h; cases h), ho9 reg6 (by intro h; cases h)]
            change (reg s7 reg6).val = _
            rw [ho7 reg6 (by intro h; cases h), ho6 reg6 (by intro h; cases h), hAccInNext])
        (by rw [hr11, ho10 reg7 (by intro h; cases h), hAccOutNext])
        (fun i hik => by
          rw [hData11 (inStartArrBase H.vertexCount r.out.tables.next + i)]
          have hn1 : inStartArrBase H.vertexCount r.out.tables.next + i ≠
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by omega
          rw [ite_eq_right hn1]
          by_cases hiEq : i = k
          · subst hiEq; rw [ite_eq_left rfl]
            change Option.map Fin.val (some (reg s3 reg6)) = _
            rw [Option.map_some, Option.some.injEq, ho3 reg6 (by intro h; cases h), ho2 reg6 (by intro h; cases h), hr1, hAccIn]
          · rw [ite_eq_right (by omega)]; exact hInDone i (by omega))
        (fun i hki hin => by
          rw [hData11 (inStartArrBase H.vertexCount r.out.tables.next + i)]
          have hn1 : inStartArrBase H.vertexCount r.out.tables.next + i ≠
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by omega
          have hn2 : inStartArrBase H.vertexCount r.out.tables.next + i ≠
              inStartArrBase H.vertexCount r.out.tables.next + k := by omega
          rw [ite_eq_right hn1, ite_eq_right hn2]; exact hInTodo i (by omega) hin)
        (fun i hik => by
          rw [hData11 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i)]
          by_cases hiEq : i = k
          · subst hiEq; rw [ite_eq_left rfl]
            rw [Option.map_some, Option.some.injEq, ho7 reg7 (by intro h; cases h), ho6 reg7 (by intro h; cases h),
              ho5 reg7 (by intro h; cases h)]
            change (reg s3 reg7).val = _
            rw [ho3 reg7 (by intro h; cases h), ho2 reg7 (by intro h; cases h), hr1, hAccOut]
          · have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i ≠
                tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by omega
            have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i ≠
                inStartArrBase H.vertexCount r.out.tables.next + k := by omega
            rw [ite_eq_right hn1, ite_eq_right hn2]; exact hOutDone i (by omega))
        (fun i hki hin => by
          rw [hData11 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i)]
          have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i ≠
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by omega
          have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i ≠
              inStartArrBase H.vertexCount r.out.tables.next + k := by omega
          rw [ite_eq_right hn1, ite_eq_right hn2]; exact hOutTodo i (by omega) hin)
    refine ⟨11 + kRest, t, by omega, hStep11.append hStepsRest, hpcT, h0T, h1T, hMetaT,
      hInRes, hOutRes, fun j hj => ?_⟩
    rw [hFrT j hj, hData11 j]
    have hNe1 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by
      rcases hj with h | ⟨_, h⟩ | h <;> omega
    have hNe2 : j ≠ inStartArrBase H.vertexCount r.out.tables.next + k := by
      rcases hj with h | ⟨h, _⟩ | h <;> omega
    rw [ite_eq_right hNe1, ite_eq_right hNe2]

theorem run_csrPrefix {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {_entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hOutDeg : ∀ u < H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
        some (degOut H u))
    (hOutZ : (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
      some 0)
    (hInDeg : ∀ v < H.vertexCount,
      (s0.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v))
    (hInZ : (s0.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
      some 0) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 11 * H.vertexCount + 30 ∧
      run (csrPrefixPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ i ≤ H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)) ∧
      (∀ i ≤ H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (prefixOut H i)) ∧
      (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB1 : inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) =
      inArcIdArrBase H.vertexCount r.out.tables.next := rfl
  have hB2 : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := by omega
  have hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ 2 ^ bits := by omega
  let ph := csrPrefixPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (csrPrefixInstrs (bits := bits) h100).length = 25 := by
    simp [csrPrefixInstrs, csrPrefixSetupInstrs, csrPrefixLoopInstrs, metaLoadInstrs]
  have hCodeSize : ph.code.size = 26 := by
    dsimp [ph, csrPrefixPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (csrPrefixInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold csrPrefixInstrs at hPlFull; exact hPlFull)
  have hPlLoop := Placed_append_right (by unfold csrPrefixInstrs at hPlFull; exact hPlFull)
  rw [show (csrPrefixSetupInstrs (bits := bits) h100).length = 14 by
    simp [csrPrefixSetupInstrs, metaLoadInstrs]] at hPlLoop
  have hPlN := Placed_append_left (by unfold csrPrefixSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold csrPrefixSetupInstrs at hPlSetup; exact hPlSetup)
  rw [hLml] at hPlS1
  have hPlInS := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
  have hPlTemp := Placed_append_left hPlS2
  have hPlTail := Placed_append_right hPlS2; rw [hLml] at hPlTail
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlN (by omega)
    rfl hMeta.rMeta_eq (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) hMeta.meta_n
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlInS (by omega)
    hpc1 hMeta1 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd1]; exact hMeta.meta_inStartBase)
  have hMeta2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho2 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta1
  obtain ⟨s3, hs3, hpc3, hd3, h4_3, ho3⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlTemp (by omega)
    hpc2 hMeta2 (by dsimp only [mIdxN, mIdxM, mIdxInStartBase, mIdxInArcIdBase, mIdxTempBase, mIdxQSrcInBase, mIdxQHeadInBase]; omega) (by rw [hd2, hd1]; exact hMeta.meta_tempBase)
  have h2_3 : (reg s3 reg2).val = H.vertexCount := by
    rw [ho3 reg2 (by intro h; cases h) (by intro h; cases h),
      ho2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h3_3 : (reg s3 reg3).val = inStartArrBase H.vertexCount r.out.tables.next := by
    rw [ho3 reg3 (by intro h; cases h) (by intro h; cases h), h3_2]
  have h0_3 : (reg s3 reg0).val = 0 := by
    rw [ho3 reg0 (by intro h; cases h) (by intro h; cases h),
      ho2 reg0 (by intro h; cases h) (by intro h; cases h),
      ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_3 : (reg s3 reg1).val = 1 := by
    rw [ho3 reg1 (by intro h; cases h) (by intro h; cases h),
      ho2 reg1 (by intro h; cases h) (by intro h; cases h),
      ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have hMeta3 : (reg s3 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho3 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta2
  have ha1 : ph.code[s3.pc]? = some (.add reg4 reg4 reg2) := by rw [hpc3]; exact hPlTail 0 _ rfl
  obtain ⟨s4, hs4, hpc4, h4_4, ho4, hd4⟩ := step_add_at (input := input) ha1 (by omega)
  have h4Val : (reg s4 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [h4_4, add_no_wrap _ _ (by rw [h4_3, h2_3]; exact Nat.lt_of_lt_of_le (by omega) hw), h4_3, h2_3]
  have ha2 : ph.code[s4.pc]? = some (.add reg2 reg2 reg1) := by rw [hpc4, hpc3]; exact hPlTail 1 _ rfl
  obtain ⟨s5, hs5, hpc5, h2_5, ho5, hd5⟩ := step_add_at (input := input) ha2 (by omega)
  have h2Val : (reg s5 reg2).val = H.vertexCount + 1 := by
    have hr2_4 : (reg s4 reg2).val = H.vertexCount := by rw [ho4 reg2 (by intro h; cases h), h2_3]
    have hr1_4 : (reg s4 reg1).val = 1 := by rw [ho4 reg1 (by intro h; cases h), h1_3]
    rw [h2_5, add_no_wrap _ _ (by rw [hr2_4, hr1_4]; exact Nat.lt_of_lt_of_le (by omega) hw), hr2_4, hr1_4]
  have hm1 : ph.code[s5.pc]? = some (.mov reg5 reg0) := by rw [show s5.pc = 0 + 3 + 3 + 3 + 2 by omega]; exact hPlTail 2 _ rfl
  obtain ⟨s6, hs6, hpc6, h5_6, ho6, hd6⟩ := step_mov_at (input := input) hm1 (by omega)
  have hm2 : ph.code[s6.pc]? = some (.mov reg6 reg0) := by rw [show s6.pc = 0 + 3 + 3 + 3 + 3 by omega]; exact hPlTail 3 _ rfl
  obtain ⟨s7, hs7, hpc7, h6_7, ho7, hd7⟩ := step_mov_at (input := input) hm2 (by omega)
  have hm3 : ph.code[s7.pc]? = some (.mov reg7 reg0) := by rw [show s7.pc = 0 + 3 + 3 + 3 + 4 by omega]; exact hPlTail 4 _ rfl
  obtain ⟨s8, hs8, hpc8, h7_8, ho8, hd8⟩ := step_mov_at (input := input) hm3 (by omega)
  have hd8' : s8.data = s0.data := by rw [hd8, hd7, hd6, hd5, hd4, hd3, hd2, hd1, data_initial]
  have h0_8 : (reg s8 reg0).val = 0 := by
    rw [ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h),
      ho6 reg0 (by intro h; cases h), ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h), h0_3]
  have h1_8 : (reg s8 reg1).val = 1 := by
    rw [ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h),
      ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h), ho4 reg1 (by intro h; cases h), h1_3]
  have hMeta8 : (reg s8 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h),
      ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h), ho4 rMeta (by intro h; cases h), hMeta3]
  have h2_8 : (reg s8 reg2).val = H.vertexCount + 1 := by
    rw [ho8 reg2 (by intro h; cases h), ho7 reg2 (by intro h; cases h), ho6 reg2 (by intro h; cases h), h2Val]
  have h3_8 : (reg s8 reg3).val = inStartArrBase H.vertexCount r.out.tables.next := by
    rw [ho8 reg3 (by intro h; cases h), ho7 reg3 (by intro h; cases h),
      ho6 reg3 (by intro h; cases h), ho5 reg3 (by intro h; cases h), ho4 reg3 (by intro h; cases h), h3_3]
  have h4_8 : (reg s8 reg4).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [ho8 reg4 (by intro h; cases h), ho7 reg4 (by intro h; cases h),
      ho6 reg4 (by intro h; cases h), ho5 reg4 (by intro h; cases h), h4Val]
  have h5_8 : (reg s8 reg5).val = 0 := by
    rw [ho8 reg5 (by intro h; cases h), ho7 reg5 (by intro h; cases h), h5_6,
      ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h), h0_3]
  have h6_8 : (reg s8 reg6).val = 0 := by
    rw [ho8 reg6 (by intro h; cases h), h6_7,
      ho6 reg0 (by intro h; cases h), ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h), h0_3]
  have h7_8' : (reg s8 reg7).val = 0 := by rw [h7_8, ← ho8 reg0 (by intro h; cases h), h0_8]
  obtain ⟨kLoop, t, hkLoop, hStepsLoop, hpcT, h0T, h1T, hMetaT, hInRes, hOutRes, hFrT⟩ :=
    csrPrefixLoop_spec (H := H) (r := r) hWork hPlLoop (by omega) 0 (Nat.zero_le _) s8 (by omega)
      h0_8 h1_8 hMeta8 h2_8 h3_8 h4_8 h5_8 h6_8 h7_8'
      (fun i hi0 => absurd hi0 (Nat.not_lt_zero _))
      (fun i _ hin => by
        rw [hd8']; by_cases hi : i < H.vertexCount
        · rw [ite_eq_left hi]; exact hInDeg i hi
        · have hiEqN : i = H.vertexCount := by omega
          rw [ite_eq_right hi, hiEqN]; exact hInZ)
      (fun i hi0 => absurd hi0 (Nat.not_lt_zero _))
      (fun i _ hin => by
        rw [hd8']; by_cases hi : i < H.vertexCount
        · rw [ite_eq_left hi]; exact hOutDeg i hi
        · have hiEqN : i = H.vertexCount := by omega
          rw [ite_eq_right hi, hiEqN,
            show tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + H.vertexCount =
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount by omega]
          exact hOutZ)
  have hSetupSteps : Steps ph.code input 14 (Phase.initial s0) s8 :=
    hs1.append (hs2.append (hs3.append (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (steps_1_of_step hs8)))))))
  have hHalt : step ph.code input t = some (.halted t) :=
    haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrPrefixInstrs (bits := bits) h100) _
      (by rw [hpcT, hCodeLen]) (input := input)
  refine ⟨14 + kLoop + 1, t, by omega, (hSetupSteps.append hStepsLoop).halts hHalt, ?_,
    hInRes, hOutRes, fun j hj => by rw [hFrT j hj, hd8']⟩
  · apply hMeta.preserve hMetaT h0T h1T
    intro i hi22; rw [hFrT _ (Or.inr (Or.inl ⟨by omega, by omega⟩)), hd8']

end CsrPrefixPhase


end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
