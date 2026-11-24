module

public import PaperB.RamExitSummaryCsrCount

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
The exit-summary CSR prefix phase and its execution proof.
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
