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
The exit-summary CSR count loop and its transition proof.
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

theorem csrCountLoop_spec {code : Program DomL} {input : Input DomL}
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

end CsrCountPhase


end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
