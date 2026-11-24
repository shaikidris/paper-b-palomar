module

public import PaperB.RamExitSummaryCsr

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

section CsrScatter

variable {bits : Nat}

def csrScatterSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg11 mIdxM (by change 1 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg3 reg11 mIdxN (by change 0 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg4 reg11 mIdxInStartBase (by change 10 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg5 reg11 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  ([ .add reg7 reg5 reg3
   , .add reg7 reg7 reg3
   , .add reg7 reg7 reg3
   , .add reg7 reg7 reg1
   , .add reg5 reg5 reg3
   ] ++
  (metaLoadInstrs reg6 reg11 mIdxInArcIdBase (by change 11 < 2 ^ bits; omega) ++
  ([ .branchLt reg0 reg2 21 47 ] ++
  (metaLoadInstrs reg8 reg11 mIdxQSrcInBase (by change 14 < 2 ^ bits; omega) ++
  (metaLoadInstrs reg9 reg11 mIdxQHeadInBase (by change 15 < 2 ^ bits; omega) ++
  [ .mov reg10 reg0 ]))))))))

def csrScatterLoop1Instrs : List (Instr bits 15) :=
  [ .branchLt reg10 reg2 29 47
  , .add reg11 reg8 reg10
  , .loadInput reg11 reg11
  , .add reg11 reg5 reg11
  , .loadData reg12 reg11
  , .add reg13 reg7 reg12
  , .storeData reg13 reg10
  , .add reg12 reg12 reg1
  , .storeData reg11 reg12
  , .add reg11 reg9 reg10
  , .loadInput reg11 reg11
  , .add reg11 reg4 reg11
  , .loadData reg12 reg11
  , .add reg13 reg6 reg12
  , .storeData reg13 reg10
  , .add reg12 reg12 reg1
  , .storeData reg11 reg12
  , .add reg10 reg10 reg1
  , .goto 28
  ]

def csrScatterLoop2Instrs : List (Instr bits 15) :=
  [ .branchLt reg0 reg3 48 59
  , .sub reg8 reg3 reg1
  , .add reg9 reg4 reg8
  , .loadData reg10 reg9
  , .add reg9 reg4 reg3
  , .storeData reg9 reg10
  , .add reg9 reg5 reg8
  , .loadData reg10 reg9
  , .add reg9 reg5 reg3
  , .storeData reg9 reg10
  , .mov reg3 reg8
  , .goto 47
  , .storeData reg4 reg0
  , .storeData reg5 reg0
  ]

def csrScatterInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  csrScatterSetupInstrs h100 ++ (csrScatterLoop1Instrs ++ csrScatterLoop2Instrs)

end CsrScatter

section CsrScatterPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def csrScatterPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (csrScatterInstrs (bits := bits) h100)
    (by simp [csrScatterInstrs, csrScatterSetupInstrs, csrScatterLoop1Instrs, csrScatterLoop2Instrs, metaLoadInstrs, nonHalt])

private theorem csrScatterLoop1_bounds
    {n m N workCap inputCap k u v prefOut outCnt prefIn inCnt tb isb iaib : Nat}
    (_hNLe : N ≤ n + 1)
    (hCapIn : 4 + n + 4 * N + 2 * m ≤ inputCap)
    (hTempCap : tb + (3 * n + 2 + m) ≤ workCap)
    (hB1 : isb + (n + 1) = iaib)
    (hB2 : iaib + m = tb - 48)
    (hB3 : tb - 48 + 48 = tb)
    (_hGap : isb + n ≤ tb)
    (hkLt : k < m) (huLt : u < n) (hvLt : v < n)
    (hOutBound : prefOut + outCnt < m) (hInBound : prefIn + inCnt < m) :
    (4 + n + 4 * N + m + k < inputCap) ∧
    (4 + n + 4 * N + k < inputCap) ∧
    (tb + n + u < workCap) ∧
    (tb + 3 * n + 1 + (prefOut + outCnt) < workCap) ∧
    (isb + v < workCap) ∧
    (iaib + (prefIn + inCnt) < workCap) ∧
    (prefOut + outCnt + 1 < workCap) ∧
    (prefIn + inCnt + 1 < workCap) ∧
    (k + 1 < workCap) := by
  have h48 : 48 ≤ tb := by
    have : 48 ≤ isb + (n + 1) + m + 48 := by omega
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

private theorem csrScatterLoop1_exec19 {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hPl : Placed code 28 csrScatterLoop1Instrs) (hSz : 47 < code.size)
    (k : Nat) (hkLt : k < H.arcCount)
    (st : State DomL) (hpc : st.pc = 28)
    (_h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (_hMeta : (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hM : (reg st reg2).val = H.arcCount)
    (_hN : (reg st reg3).val = H.vertexCount)
    (hInS : (reg st reg4).val = inStartArrBase H.vertexCount r.out.tables.next)
    (hOutS : (reg st reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount)
    (hInArc : (reg st reg6).val = inArcIdArrBase H.vertexCount r.out.tables.next)
    (hOutArc : (reg st reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1)
    (hQSrc : (reg st reg8).val = 4 + H.vertexCount + 4 * r.out.tables.next)
    (hQHead : (reg st reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount)
    (hIdx : (reg st reg10).val = k)
    (hOutCur : (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (rawOccurrence H ⟨k, hkLt⟩).1.val]?).map Fin.val =
      some (prefixOut H (rawOccurrence H ⟨k, hkLt⟩).1.val + outCountPrefix H k (rawOccurrence H ⟨k, hkLt⟩).1.val))
    (hInCur : (st.data[inStartArrBase H.vertexCount r.out.tables.next + (rawHead H ⟨k, hkLt⟩).val]?).map Fin.val =
      some (prefixIn H (rawHead H ⟨k, hkLt⟩).val + inCountPrefix H k (rawHead H ⟨k, hkLt⟩).val))
    (hGapInTemp : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hHeadCap : 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + k < inputCap)
    (hSrcCap : 4 + H.vertexCount + 4 * r.out.tables.next + k < inputCap)
    (hOutSAddrLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (rawOccurrence H ⟨k, hkLt⟩).1.val < workCap)
    (hOutArcAddrLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
      (prefixOut H (rawOccurrence H ⟨k, hkLt⟩).1.val + outCountPrefix H k (rawOccurrence H ⟨k, hkLt⟩).1.val) < workCap)
    (hInSAddrLt : inStartArrBase H.vertexCount r.out.tables.next + (rawHead H ⟨k, hkLt⟩).val < workCap)
    (hInArcAddrLt : inArcIdArrBase H.vertexCount r.out.tables.next +
      (prefixIn H (rawHead H ⟨k, hkLt⟩).val + inCountPrefix H k (rawHead H ⟨k, hkLt⟩).val) < workCap)
    (hOutK1Lt : prefixOut H (rawOccurrence H ⟨k, hkLt⟩).1.val + outCountPrefix H k (rawOccurrence H ⟨k, hkLt⟩).1.val + 1 < workCap)
    (hInK1Lt : prefixIn H (rawHead H ⟨k, hkLt⟩).val + inCountPrefix H k (rawHead H ⟨k, hkLt⟩).val + 1 < workCap)
    (hK1Lt : k + 1 < workCap) :
    let u := (rawOccurrence H ⟨k, hkLt⟩).1.val
    let v := (rawHead H ⟨k, hkLt⟩).val
    ∃ (s19 : State DomL) (wInC wInV wOutC wOutV : Word bits),
      Steps code input 19 st s19 ∧ s19.pc = 28 ∧
      wInC.val = prefixIn H v + inCountPrefix H k v + 1 ∧
      wInV.val = k ∧
      wOutC.val = prefixOut H u + outCountPrefix H k u + 1 ∧
      wOutV.val = k ∧
      (reg s19 reg10).val = k + 1 ∧
      (∀ r : Fin 15, r ≠ reg10 → r ≠ reg11 → r ≠ reg12 → r ≠ reg13 → reg s19 r = reg st r) ∧
      (∀ j, s19.data[j]? =
        if j = inStartArrBase H.vertexCount r.out.tables.next + v then some wInC
        else if j = inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) then some wInV
        else if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u then some wOutC
        else if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + outCountPrefix H k u) then some wOutV
        else st.data[j]?) := by
  let u := (rawOccurrence H ⟨k, hkLt⟩).1.val
  let v := (rawHead H ⟨k, hkLt⟩).val
  have hvLt : v < H.vertexCount := (rawHead H ⟨k, hkLt⟩).isLt
  have hCmp : code[st.pc]? = some (.branchLt reg10 reg2 29 47) := by rw [hpc]; exact hPl 0 _ rfl
  have hTrue : (reg st reg10).val < (reg st reg2).val := by rw [hIdx, hM]; exact hkLt
  obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp (by rw [ite_eq_left hTrue]; omega)
  rw [ite_eq_left hTrue] at hpc1
  have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
  have ha1 : code[s1.pc]? = some (.add reg11 reg8 reg10) := by rw [hpc1]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hr11_2, ho2, hd2⟩ := step_add_at (input := input) ha1
    (by rw [hpc1]; exact Nat.lt_trans (by decide) hSz)
  have hpc2' : s2.pc = 28 + 2 := by rw [hpc2, hpc1]
  have hAddrSrc : (reg s2 reg11).val = 4 + H.vertexCount + 4 * r.out.tables.next + k := by
    have h8 : (reg s1 reg8).val = 4 + H.vertexCount + 4 * r.out.tables.next := by rw [hr1, hQSrc]
    have h10 : (reg s1 reg10).val = k := by rw [hr1, hIdx]
    have hLtSrc : (reg s1 reg8).val + (reg s1 reg10).val < 2 ^ bits := by
      rw [h8, h10]; exact Nat.lt_of_lt_of_le hSrcCap hi
    rw [hr11_2, add_no_wrap _ _ hLtSrc, h8, h10]
  obtain ⟨wSrc, hwSrc, hwSrcV⟩ := Option.map_eq_some_iff.mp (hIn.qSrc_at ⟨k, hkLt⟩)
  have hl1 : code[s2.pc]? = some (.loadInput reg11 reg11) := by rw [hpc2']; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hr11_3, ho3, hd3⟩ := step_loadInput_at (input := input) hl1
    (by rw [hpc2']; exact Nat.lt_trans (by decide) hSz) (by rw [hAddrSrc]; exact hwSrc)
  have hpc3' : s3.pc = 28 + 3 := by rw [hpc3, hpc2']
  have hu3 : (reg s3 reg11).val = u := by rw [hr11_3, hwSrcV]
  have ha2 : code[s3.pc]? = some (.add reg11 reg5 reg11) := by rw [hpc3']; exact hPl 3 _ rfl
  obtain ⟨s4, hs4, hpc4, hr11_4, ho4, hd4⟩ := step_add_at (input := input) ha2
    (by rw [hpc3']; exact Nat.lt_trans (by decide) hSz)
  have hpc4' : s4.pc = 28 + 4 := by rw [hpc4, hpc3']
  have h5_3 : (reg s3 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [ho3 reg5 (by intro h; cases h), ho2 reg5 (by intro h; cases h), hr1, hOutS]
  have hLtOutS4 : (reg s3 reg5).val + (reg s3 reg11).val < 2 ^ bits := by
    rw [h5_3, hu3]; exact Nat.lt_of_lt_of_le hOutSAddrLt hw
  have hAddrOutS : (reg s4 reg11).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
    rw [hr11_4, add_no_wrap _ _ hLtOutS4, h5_3, hu3]
  obtain ⟨wPosO, hwPosO, hwPosOV⟩ := Option.map_eq_some_iff.mp hOutCur
  have hl2 : code[s4.pc]? = some (.loadData reg12 reg11) := by rw [hpc4']; exact hPl 4 _ rfl
  obtain ⟨s5, hs5, hpc5, hr12_5, ho5, hd5⟩ := step_loadData_at (input := input) hl2
    (by rw [hpc4']; exact Nat.lt_trans (by decide) hSz) (by rw [hAddrOutS, hd4, hd3, hd2, hd1]; exact hwPosO)
  have hpc5' : s5.pc = 28 + 5 := by rw [hpc5, hpc4']
  have hPosOVal : (reg s5 reg12).val = prefixOut H u + outCountPrefix H k u := by rw [hr12_5, hwPosOV]
  have ha3 : code[s5.pc]? = some (.add reg13 reg7 reg12) := by rw [hpc5']; exact hPl 5 _ rfl
  obtain ⟨s6, hs6, hpc6, hr13_6, ho6, hd6⟩ := step_add_at (input := input) ha3
    (by rw [hpc5']; exact Nat.lt_trans (by decide) hSz)
  have hpc6' : s6.pc = 28 + 6 := by rw [hpc6, hpc5']
  have h7_5 : (reg s5 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 := by
    rw [ho5 reg7 (by intro h; cases h), ho4 reg7 (by intro h; cases h),
      ho3 reg7 (by intro h; cases h), ho2 reg7 (by intro h; cases h), hr1, hOutArc]
  have hLtOutA6 : (reg s5 reg7).val + (reg s5 reg12).val < 2 ^ bits := by
    rw [h7_5, hPosOVal]; exact Nat.lt_of_lt_of_le hOutArcAddrLt hw
  have hAddrOutArc : (reg s6 reg13).val =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + outCountPrefix H k u) := by
    rw [hr13_6, add_no_wrap _ _ hLtOutA6, h7_5, hPosOVal]
  have hLtOutArc : (reg s6 reg13).val < s6.data.size := lt_data_size (by rw [hAddrOutArc]; exact hOutArcAddrLt)
  have hst1 : code[s6.pc]? = some (.storeData reg13 reg10) := by rw [hpc6']; exact hPl 6 _ rfl
  obtain ⟨s7, hs7, hpc7, hreg7, hd7⟩ := step_storeData_opaque (input := input) hst1 hLtOutArc
    (by rw [hpc6']; exact Nat.lt_trans (by decide) hSz)
  have hpc7' : s7.pc = 28 + 7 := by rw [hpc7, hpc6']
  have hr7 : ∀ r : Fin 15, reg s7 r = reg s6 r := reg_of_regs_eq hreg7
  have ha4 : code[s7.pc]? = some (.add reg12 reg12 reg1) := by rw [hpc7']; exact hPl 7 _ rfl
  obtain ⟨s8, hs8, hpc8, hr12_8, ho8, hd8⟩ := step_add_at (input := input) ha4
    (by rw [hpc7']; exact Nat.lt_trans (by decide) hSz)
  have hpc8' : s8.pc = 28 + 8 := by rw [hpc8, hpc7']
  have h12_7 : (reg s7 reg12).val = prefixOut H u + outCountPrefix H k u := by
    rw [hr7, ho6 reg12 (by intro h; cases h), hPosOVal]
  have h1_7 : (reg s7 reg1).val = 1 := by
    rw [hr7, ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h),
      ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), hr1, h1]
  have hLt12_8 : (reg s7 reg12).val + (reg s7 reg1).val < 2 ^ bits := by
    rw [h12_7, h1_7]; exact Nat.lt_of_lt_of_le hOutK1Lt hw
  have h12_8Val : (reg s8 reg12).val = prefixOut H u + outCountPrefix H k u + 1 := by
    rw [hr12_8, add_no_wrap _ _ hLt12_8, h12_7, h1_7]
  have h11_8 : (reg s8 reg11).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
    rw [ho8 reg11 (by intro h; cases h), hr7,
      ho6 reg11 (by intro h; cases h), ho5 reg11 (by intro h; cases h), hAddrOutS]
  have hLtOutS8 : (reg s8 reg11).val < s8.data.size := lt_data_size (by rw [h11_8]; exact hOutSAddrLt)
  have hst2 : code[s8.pc]? = some (.storeData reg11 reg12) := by rw [hpc8']; exact hPl 8 _ rfl
  obtain ⟨s9, hs9, hpc9, hreg9, hd9⟩ := step_storeData_opaque (input := input) hst2 hLtOutS8
    (by rw [hpc8']; exact Nat.lt_trans (by decide) hSz)
  have hpc9' : s9.pc = 28 + 9 := by rw [hpc9, hpc8']
  have hr9 : ∀ r : Fin 15, reg s9 r = reg s8 r := reg_of_regs_eq hreg9
  have ha5 : code[s9.pc]? = some (.add reg11 reg9 reg10) := by rw [hpc9']; exact hPl 9 _ rfl
  obtain ⟨s10, hs10, hpc10, hr11_10, ho10, hd10⟩ := step_add_at (input := input) ha5
    (by rw [hpc9']; exact Nat.lt_trans (by decide) hSz)
  have hpc10' : s10.pc = 28 + 10 := by rw [hpc10, hpc9']
  have h9_9 : (reg s9 reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount := by
    rw [hr9, ho8 reg9 (by intro h; cases h), hr7,
      ho6 reg9 (by intro h; cases h), ho5 reg9 (by intro h; cases h),
      ho4 reg9 (by intro h; cases h), ho3 reg9 (by intro h; cases h), ho2 reg9 (by intro h; cases h), hr1, hQHead]
  have h10_9 : (reg s9 reg10).val = k := by
    rw [hr9, ho8 reg10 (by intro h; cases h), hr7,
      ho6 reg10 (by intro h; cases h), ho5 reg10 (by intro h; cases h),
      ho4 reg10 (by intro h; cases h), ho3 reg10 (by intro h; cases h), ho2 reg10 (by intro h; cases h), hr1, hIdx]
  have hLtHead10 : (reg s9 reg9).val + (reg s9 reg10).val < 2 ^ bits := by
    rw [h9_9, h10_9]; exact Nat.lt_of_lt_of_le hHeadCap hi
  have hAddrHead : (reg s10 reg11).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + k := by
    rw [hr11_10, add_no_wrap _ _ hLtHead10, h9_9, h10_9]
  obtain ⟨wHead, hwHead, hwHeadV⟩ := Option.map_eq_some_iff.mp (hIn.qHead_at ⟨k, hkLt⟩)
  have hl3 : code[s10.pc]? = some (.loadInput reg11 reg11) := by rw [hpc10']; exact hPl 10 _ rfl
  obtain ⟨s11, hs11, hpc11, hr11_11, ho11, hd11⟩ := step_loadInput_at (input := input) hl3
    (by rw [hpc10']; exact Nat.lt_trans (by decide) hSz) (by rw [hAddrHead]; exact hwHead)
  have hpc11' : s11.pc = 28 + 11 := by rw [hpc11, hpc10']
  have hv11 : (reg s11 reg11).val = v := by rw [hr11_11, hwHeadV]
  have ha6 : code[s11.pc]? = some (.add reg11 reg4 reg11) := by rw [hpc11']; exact hPl 11 _ rfl
  obtain ⟨s12, hs12, hpc12, hr11_12, ho12, hd12⟩ := step_add_at (input := input) ha6
    (by rw [hpc11']; exact Nat.lt_trans (by decide) hSz)
  have hpc12' : s12.pc = 28 + 12 := by rw [hpc12, hpc11']
  have h4_11 : (reg s11 reg4).val = inStartArrBase H.vertexCount r.out.tables.next := by
    rw [ho11 reg4 (by intro h; cases h), ho10 reg4 (by intro h; cases h), hr9,
      ho8 reg4 (by intro h; cases h), hr7,
      ho6 reg4 (by intro h; cases h), ho5 reg4 (by intro h; cases h),
      ho4 reg4 (by intro h; cases h), ho3 reg4 (by intro h; cases h), ho2 reg4 (by intro h; cases h), hr1, hInS]
  have hLtInS12 : (reg s11 reg4).val + (reg s11 reg11).val < 2 ^ bits := by
    rw [h4_11, hv11]; exact Nat.lt_of_lt_of_le hInSAddrLt hw
  have hAddrInS : (reg s12 reg11).val = inStartArrBase H.vertexCount r.out.tables.next + v := by
    rw [hr11_12, add_no_wrap _ _ hLtInS12, h4_11, hv11]
  have hDisj9a : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u ≠
      inStartArrBase H.vertexCount r.out.tables.next + v := by
    have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
    rw [Nat.add_assoc]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
  have hDisj7a : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
      (prefixOut H u + outCountPrefix H k u) ≠ inStartArrBase H.vertexCount r.out.tables.next + v := by
    have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
    rw [Nat.add_assoc, Nat.add_assoc]
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
  obtain ⟨wPosI, hwPosI, hwPosIV⟩ := Option.map_eq_some_iff.mp hInCur
  have hMemInS : s12.data[(reg s12 reg11).val]? = some wPosI := by
    rw [hAddrInS, hd12, hd11, hd10, hd9,
      Array.getElem?_set_ne hLtOutS8 (by rw [h11_8]; exact hDisj9a), hd8, hd7,
      Array.getElem?_set_ne hLtOutArc (by rw [hAddrOutArc]; exact hDisj7a), hd6, hd5, hd4, hd3, hd2, hd1]
    exact hwPosI
  have hl4 : code[s12.pc]? = some (.loadData reg12 reg11) := by rw [hpc12']; exact hPl 12 _ rfl
  obtain ⟨s13, hs13, hpc13, hr12_13, ho13, hd13⟩ := step_loadData_at (input := input) hl4
    (by rw [hpc12']; exact Nat.lt_trans (by decide) hSz) hMemInS
  have hpc13' : s13.pc = 28 + 13 := by rw [hpc13, hpc12']
  have hPosIVal : (reg s13 reg12).val = prefixIn H v + inCountPrefix H k v := by rw [hr12_13, hwPosIV]
  have ha7 : code[s13.pc]? = some (.add reg13 reg6 reg12) := by rw [hpc13']; exact hPl 13 _ rfl
  obtain ⟨s14, hs14, hpc14, hr13_14, ho14, hd14⟩ := step_add_at (input := input) ha7
    (by rw [hpc13']; exact Nat.lt_trans (by decide) hSz)
  have hpc14' : s14.pc = 28 + 14 := by rw [hpc14, hpc13']
  have h6_13 : (reg s13 reg6).val = inArcIdArrBase H.vertexCount r.out.tables.next := by
    rw [ho13 reg6 (by intro h; cases h), ho12 reg6 (by intro h; cases h),
      ho11 reg6 (by intro h; cases h), ho10 reg6 (by intro h; cases h), hr9,
      ho8 reg6 (by intro h; cases h), hr7,
      ho6 reg6 (by intro h; cases h), ho5 reg6 (by intro h; cases h),
      ho4 reg6 (by intro h; cases h), ho3 reg6 (by intro h; cases h), ho2 reg6 (by intro h; cases h), hr1, hInArc]
  have hLtInArc14 : (reg s13 reg6).val + (reg s13 reg12).val < 2 ^ bits := by
    rw [h6_13, hPosIVal]; exact Nat.lt_of_lt_of_le hInArcAddrLt hw
  have hAddrInArc : (reg s14 reg13).val =
      inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) := by
    rw [hr13_14, add_no_wrap _ _ hLtInArc14, h6_13, hPosIVal]
  have hLtInArc : (reg s14 reg13).val < s14.data.size := lt_data_size (by rw [hAddrInArc]; exact hInArcAddrLt)
  have hst3 : code[s14.pc]? = some (.storeData reg13 reg10) := by rw [hpc14']; exact hPl 14 _ rfl
  obtain ⟨s15, hs15, hpc15, hreg15, hd15⟩ := step_storeData_opaque (input := input) hst3 hLtInArc
    (by rw [hpc14']; exact Nat.lt_trans (by decide) hSz)
  have hpc15' : s15.pc = 28 + 15 := by rw [hpc15, hpc14']
  have hr15 : ∀ r : Fin 15, reg s15 r = reg s14 r := reg_of_regs_eq hreg15
  have ha8 : code[s15.pc]? = some (.add reg12 reg12 reg1) := by rw [hpc15']; exact hPl 15 _ rfl
  obtain ⟨s16, hs16, hpc16, hr12_16, ho16, hd16⟩ := step_add_at (input := input) ha8
    (by rw [hpc15']; exact Nat.lt_trans (by decide) hSz)
  have hpc16' : s16.pc = 28 + 16 := by rw [hpc16, hpc15']
  have h12_15 : (reg s15 reg12).val = prefixIn H v + inCountPrefix H k v := by
    rw [hr15, ho14 reg12 (by intro h; cases h), hPosIVal]
  have h1_15 : (reg s15 reg1).val = 1 := by
    rw [hr15, ho14 reg1 (by intro h; cases h), ho13 reg1 (by intro h; cases h),
      ho12 reg1 (by intro h; cases h), ho11 reg1 (by intro h; cases h), ho10 reg1 (by intro h; cases h),
      hr9, ho8 reg1 (by intro h; cases h), h1_7]
  have hLt12_16 : (reg s15 reg12).val + (reg s15 reg1).val < 2 ^ bits := by
    rw [h12_15, h1_15]; exact Nat.lt_of_lt_of_le hInK1Lt hw
  have h12_16Val : (reg s16 reg12).val = prefixIn H v + inCountPrefix H k v + 1 := by
    rw [hr12_16, add_no_wrap _ _ hLt12_16, h12_15, h1_15]
  have h11_16 : (reg s16 reg11).val = inStartArrBase H.vertexCount r.out.tables.next + v := by
    rw [ho16 reg11 (by intro h; cases h), hr15,
      ho14 reg11 (by intro h; cases h), ho13 reg11 (by intro h; cases h), hAddrInS]
  have hLtInS16 : (reg s16 reg11).val < s16.data.size := lt_data_size (by rw [h11_16]; exact hInSAddrLt)
  have hst4 : code[s16.pc]? = some (.storeData reg11 reg12) := by rw [hpc16']; exact hPl 16 _ rfl
  obtain ⟨s17, hs17, hpc17, hreg17, hd17⟩ := step_storeData_opaque (input := input) hst4 hLtInS16
    (by rw [hpc16']; exact Nat.lt_trans (by decide) hSz)
  have hpc17' : s17.pc = 28 + 17 := by rw [hpc17, hpc16']
  have hr17 : ∀ r : Fin 15, reg s17 r = reg s16 r := reg_of_regs_eq hreg17
  have ha9 : code[s17.pc]? = some (.add reg10 reg10 reg1) := by rw [hpc17']; exact hPl 17 _ rfl
  obtain ⟨s18, hs18, hpc18, hr10_18, ho18, hd18⟩ := step_add_at (input := input) ha9
    (by rw [hpc17']; exact Nat.lt_trans (by decide) hSz)
  have hpc18' : s18.pc = 28 + 18 := by rw [hpc18, hpc17']
  have h10_17 : (reg s17 reg10).val = k := by
    rw [hr17, ho16 reg10 (by intro h; cases h), hr15,
      ho14 reg10 (by intro h; cases h), ho13 reg10 (by intro h; cases h),
      ho12 reg10 (by intro h; cases h), ho11 reg10 (by intro h; cases h), ho10 reg10 (by intro h; cases h), h10_9]
  have h1_17 : (reg s17 reg1).val = 1 := by
    rw [hr17, ho16 reg1 (by intro h; cases h), h1_15]
  have hk1Val : (reg s18 reg10).val = k + 1 := by
    rw [hr10_18, add_no_wrap _ _ (by rw [h10_17, h1_17]; exact Nat.lt_of_lt_of_le hK1Lt hw), h10_17, h1_17]
  have hJmp : code[s18.pc]? = some (.goto 28) := by rw [hpc18']; exact hPl 18 _ rfl
  obtain ⟨s19, hs19, hpc19, hreg19, hd19⟩ := step_goto_at (input := input) hJmp
    (by exact Nat.lt_trans (by decide) hSz)
  have hr19 : ∀ r : Fin 15, reg s19 r = reg s18 r := reg_of_regs_eq hreg19
  have hKeep19 : ∀ r : Fin 15,
      r ≠ reg10 → r ≠ reg11 → r ≠ reg12 → r ≠ reg13 → reg s19 r = reg st r := by
    intro r hr10 hr11 hr12 hr13
    rw [hr19, ho18 r hr10, hr17, ho16 r hr12, hr15,
      ho14 r hr13, ho13 r hr12, ho12 r hr11, ho11 r hr11, ho10 r hr11, hr9,
      ho8 r hr12, hr7, ho6 r hr13, ho5 r hr12, ho4 r hr11, ho3 r hr11, ho2 r hr11, hr1]
  have hr10_6 : (reg s6 reg10).val = k := by
    rw [ho6 reg10 (by intro h; cases h), ho5 reg10 (by intro h; cases h),
      ho4 reg10 (by intro h; cases h), ho3 reg10 (by intro h; cases h),
      ho2 reg10 (by intro h; cases h), hr1, hIdx]
  have hr10_14 : (reg s14 reg10).val = k := by
    rw [ho14 reg10 (by intro h; cases h), ho13 reg10 (by intro h; cases h),
      ho12 reg10 (by intro h; cases h), ho11 reg10 (by intro h; cases h),
      ho10 reg10 (by intro h; cases h), h10_9]
  have hStep19 : Steps code input 19 st s19 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
    (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12
    (Steps.cons hs13 (Steps.cons hs14 (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17
    (Steps.cons hs18 (steps_1_of_step hs19))))))))))))))))))
  have hData19 : ∀ j,
      s19.data[j]? =
        if j = inStartArrBase H.vertexCount r.out.tables.next + v then some (reg s16 reg12)
        else if j = inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) then some (reg s14 reg10)
        else if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u then some (reg s8 reg12)
        else if j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + outCountPrefix H k u) then some (reg s6 reg10)
        else st.data[j]? := by
    intro j
    rw [hd19, hd18, hd17]
    by_cases hA : j = inStartArrBase H.vertexCount r.out.tables.next + v
    · subst hA; rw [ite_eq_left rfl, ← h11_16]; simp [hLtInS16]
    · rw [ite_eq_right hA, Array.getElem?_set_ne hLtInS16 (by rw [h11_16]; exact fun hh => hA hh.symm),
        hd16, hd15]
      by_cases hB : j = inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v)
      · subst hB; rw [ite_eq_left rfl, ← hAddrInArc]; simp [hLtInArc]
      · rw [ite_eq_right hB, Array.getElem?_set_ne hLtInArc (by rw [hAddrInArc]; exact fun hh => hB hh.symm),
          hd14, hd13, hd12, hd11, hd10, hd9]
        by_cases hC : j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u
        · subst hC; rw [ite_eq_left rfl, ← h11_8]; simp [hLtOutS8]
        · rw [ite_eq_right hC, Array.getElem?_set_ne hLtOutS8 (by rw [h11_8]; exact fun hh => hC hh.symm),
            hd8, hd7]
          by_cases hD : j = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
              (prefixOut H u + outCountPrefix H k u)
          · subst hD; rw [ite_eq_left rfl, ← hAddrOutArc]; simp [hLtOutArc]
          · rw [ite_eq_right hD, Array.getElem?_set_ne hLtOutArc (by rw [hAddrOutArc]; exact fun hh => hD hh.symm),
              hd6, hd5, hd4, hd3, hd2, hd1]
  refine ⟨s19, reg s16 reg12, reg s14 reg10, reg s8 reg12, reg s6 reg10,
    hStep19, hpc19, h12_16Val, hr10_14, h12_8Val, hr10_6, ?_, hKeep19, hData19⟩
  rw [hr19, hk1Val]

private theorem csrScatterLoop1_spec {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hPl : Placed code 28 csrScatterLoop1Instrs) (hSz : 47 < code.size)
    (k : Nat) (hkLe : k ≤ H.arcCount)
    (st : State DomL) (hpc : st.pc = 28)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hMeta : (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hM : (reg st reg2).val = H.arcCount)
    (hN : (reg st reg3).val = H.vertexCount)
    (hInS : (reg st reg4).val = inStartArrBase H.vertexCount r.out.tables.next)
    (hOutS : (reg st reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount)
    (hInArc : (reg st reg6).val = inArcIdArrBase H.vertexCount r.out.tables.next)
    (hOutArc : (reg st reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1)
    (hQSrc : (reg st reg8).val = 4 + H.vertexCount + 4 * r.out.tables.next)
    (hQHead : (reg st reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount)
    (hIdx : (reg st reg10).val = k)
    (hOutCur : ∀ u < H.vertexCount,
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
        some (prefixOut H u + outCountPrefix H k u))
    (hOutN : (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
      some H.arcCount)
    (hInCur : ∀ v < H.vertexCount,
      (st.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
        some (prefixIn H v + inCountPrefix H k v))
    (hInN : (st.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
      some H.arcCount)
    (hOutSl : ∀ u < H.vertexCount, ∀ j : Fin (outCountPrefix H k u),
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val)]?).map Fin.val =
        some ((outArcsPrefix H k u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt)))
    (hInSl : ∀ v < H.vertexCount, ∀ j : Fin (inCountPrefix H k v),
      (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
        some ((inArcsPrefix H k v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))) :
    ∃ steps : Nat, ∃ t : State DomL,
      steps ≤ 19 * (H.arcCount - k) + 1 ∧
      Steps code input steps st t ∧ t.pc = 47 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
      (reg t reg3).val = H.vertexCount ∧
      (reg t reg4).val = inStartArrBase H.vertexCount r.out.tables.next ∧
      (reg t reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ∧
      (∀ u < H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
          some (prefixOut H (u + 1))) ∧
      (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
        some H.arcCount ∧
      (∀ v < H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
          some (prefixIn H (v + 1))) ∧
      (t.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
        some H.arcCount ∧
      (∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val)]?).map Fin.val =
          some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) ∧
      (∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
        (t.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
          some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))) ∧
      (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
          (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + H.arcCount ≤ j) →
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
  suffices hMain : ∀ d k st, H.arcCount - k = d → k ≤ H.arcCount → st.pc = 28 →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg2).val = H.arcCount →
      (reg st reg3).val = H.vertexCount →
      (reg st reg4).val = inStartArrBase H.vertexCount r.out.tables.next →
      (reg st reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount →
      (reg st reg6).val = inArcIdArrBase H.vertexCount r.out.tables.next →
      (reg st reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 →
      (reg st reg8).val = 4 + H.vertexCount + 4 * r.out.tables.next →
      (reg st reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount →
      (reg st reg10).val = k →
      (∀ u < H.vertexCount,
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
          some (prefixOut H u + outCountPrefix H k u)) →
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
        some H.arcCount →
      (∀ v < H.vertexCount,
        (st.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
          some (prefixIn H v + inCountPrefix H k v)) →
      (st.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
        some H.arcCount →
      (∀ u < H.vertexCount, ∀ j : Fin (outCountPrefix H k u),
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val)]?).map Fin.val =
          some ((outArcsPrefix H k u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) →
      (∀ v < H.vertexCount, ∀ j : Fin (inCountPrefix H k v),
        (st.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
          some ((inArcsPrefix H k v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))) →
      ∃ steps : Nat, ∃ t : State DomL,
        steps ≤ 19 * (H.arcCount - k) + 1 ∧
        Steps code input steps st t ∧ t.pc = 47 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
        (reg t reg3).val = H.vertexCount ∧
        (reg t reg4).val = inStartArrBase H.vertexCount r.out.tables.next ∧
        (reg t reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ∧
        (∀ u < H.vertexCount,
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val =
            some (prefixOut H (u + 1))) ∧
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
          some H.arcCount ∧
        (∀ v < H.vertexCount,
          (t.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val =
            some (prefixIn H (v + 1))) ∧
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
          some H.arcCount ∧
        (∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
          (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val)]?).map Fin.val =
            some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) ∧
        (∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
          (t.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
            some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))) ∧
        (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
            (inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount ≤ j ∧
              j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
            (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 ≤ j ∧
              j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1) ∨
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + H.arcCount ≤ j) →
          t.data[j]? = st.data[j]?) by
    exact hMain (H.arcCount - k) k st rfl hkLe hpc h0 h1 hMeta hM hN hInS hOutS hInArc hOutArc hQSrc hQHead hIdx
      hOutCur hOutN hInCur hInN hOutSl hInSl
  intro d
  induction d with
  | zero =>
    intro k st hd hkLe hpc h0 h1 hMeta hM hN hInS hOutS hInArc hOutArc hQSrc hQHead hIdx
      hOutCur hOutN hInCur hInN hOutSl hInSl
    have hkEq : k = H.arcCount := by omega
    have hCmp : code[st.pc]? = some (.branchLt reg10 reg2 29 47) := by rw [hpc]; exact hPl 0 _ rfl
    have hFalse : ¬ ((reg st reg10).val < (reg st reg2).val) := by
      rw [hIdx, hM, hkEq]; exact Nat.lt_irrefl _
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp (by rw [ite_eq_right hFalse]; exact hSz)
    rw [ite_eq_right hFalse] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    refine ⟨1, s1, by omega, steps_1_of_step hs1, hpc1,
      by rw [hr1, h0], by rw [hr1, h1], by rw [hr1, hMeta], by rw [hr1, hN],
      by rw [hr1, hInS], by rw [hr1, hOutS],
      fun u hu => by rw [hd1]; simpa [hkEq, degOut, prefixOut] using hOutCur u hu,
      by rw [hd1]; exact hOutN,
      fun v hv => by rw [hd1]; simpa [hkEq, degIn, prefixIn] using hInCur v hv,
      by rw [hd1]; exact hInN,
      fun u hu j => by rw [hd1]; subst hkEq; exact hOutSl u hu j,
      fun v hv j => by rw [hd1]; subst hkEq; exact hInSl v hv j,
      fun j _ => by rw [hd1]⟩
  | succ d ih =>
    intro k st hd hkLe hpc h0 h1 hMeta hM hN hInS hOutS hInArc hOutArc hQSrc hQHead hIdx
      hOutCur hOutN hInCur hInN hOutSl hInSl
    have hkLt : k < H.arcCount := by omega
    let u := (rawOccurrence H ⟨k, hkLt⟩).1.val
    let v := (rawHead H ⟨k, hkLt⟩).val
    have huLt : u < H.vertexCount := (rawOccurrence H ⟨k, hkLt⟩).1.isLt
    have hvLt : v < H.vertexCount := (rawHead H ⟨k, hkLt⟩).isLt
    have hOutBound : prefixOut H u + outCountPrefix H k u < H.arcCount := by
      have huEq : (rawOccurrence H ⟨k, hkLt⟩).1.val = u := rfl
      have h1_lt : outCountPrefix H k u + 1 ≤ outCountPrefix H (k + 1) u := by
        simp only [outCountPrefix, dite_eq_left hkLt, ite_eq_left huEq]; exact Nat.le_refl _
      have h2_lt : outCountPrefix H (k + 1) u ≤ degOut H u := outCountPrefix_mono H hkLt u
      have h3_lt : prefixOut H (u + 1) ≤ prefixOut H H.vertexCount := prefixOut_mono H huLt
      rw [← prefixOut_vertexCount H]
      have h4 : prefixOut H u + degOut H u = prefixOut H (u + 1) := rfl
      omega
    have hInBound : prefixIn H v + inCountPrefix H k v < H.arcCount := by
      have hvEq : (rawHead H ⟨k, hkLt⟩).val = v := rfl
      have h1_lt : inCountPrefix H k v + 1 ≤ inCountPrefix H (k + 1) v := by
        simp only [inCountPrefix, dite_eq_left hkLt, ite_eq_left hvEq]; exact Nat.le_refl _
      have h2_lt : inCountPrefix H (k + 1) v ≤ degIn H v := inCountPrefix_mono H hkLt v
      have h3_lt : prefixIn H (v + 1) ≤ prefixIn H H.vertexCount := prefixIn_mono H hvLt
      rw [← prefixIn_vertexCount H]
      have h4 : prefixIn H v + degIn H v = prefixIn H (v + 1) := rfl
      omega
    obtain ⟨hHeadCap, hSrcCap, hOutSAddrLt, hOutArcAddrLt, hInSAddrLt, hInArcAddrLt,
        hOutK1Lt, hInK1Lt, hK1Lt⟩ :=
      csrScatterLoop1_bounds hNLe (inputCap := inputCap) (Nat.le_trans (by omega) hIn.cap_ge) hTempCap hB1 hB2 hB3 hGapInTemp
        hkLt huLt hvLt hOutBound hInBound
    obtain ⟨s19, wInC, wInV, wOutC, wOutV, hStep19, hpc19,
        h12_16Val, hr10_14, h12_8Val, hr10_6, hk1Val, hKeep19, hData19⟩ :=
      csrScatterLoop1_exec19 hIn hPl hSz k hkLt st hpc
        h0 h1 hMeta hM hN hInS hOutS hInArc hOutArc hQSrc hQHead hIdx
        (hOutCur u huLt) (hInCur v hvLt) hGapInTemp
        hHeadCap hSrcCap hOutSAddrLt hOutArcAddrLt hInSAddrLt hInArcAddrLt hOutK1Lt hInK1Lt hK1Lt
    have hSubEq : H.arcCount - (k + 1) = d := by rw [← Nat.sub_sub, hd]; rfl
    have hOutCurNext : ∀ u' < H.vertexCount,
        (s19.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u']?).map Fin.val =
          some (prefixOut H u' + outCountPrefix H (k + 1) u') := by
      intro u' hu'
      rw [hData19 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u')]
      have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
          inStartArrBase H.vertexCount r.out.tables.next + v := by
        have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
        rw [Nat.add_assoc]
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
      have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
          inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) := by
        have h1 : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
          rw [← hB3, ← hB2]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hInBound _) (Nat.le_add_right _ 48)
        rw [Nat.add_assoc]
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
      rw [ite_eq_right hn1, ite_eq_right hn2]
      simp only [outCountPrefix, dite_eq_left hkLt]
      by_cases huEq : u' = u
      · subst huEq; rw [ite_eq_left rfl, ite_eq_left rfl, Option.map_some, h12_8Val, Nat.add_assoc]
      · have hn3 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u :=
          fun h => huEq (Nat.add_left_cancel h)
        have hn4 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
              (prefixOut H u + outCountPrefix H k u) := by
          have h1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u' <
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 := by omega
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
        have hne : u ≠ u' := fun h => huEq h.symm
        rw [ite_eq_right hn3, ite_eq_right hn4, ite_eq_right hne, Nat.add_zero]
        exact hOutCur u' hu'
    have hOutNNext :
        (s19.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val =
          some H.arcCount := by
      rw [hData19 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount)]
      have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≠
          inStartArrBase H.vertexCount r.out.tables.next + v := by
        have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
      have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≠
          inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) := by
        have h1 : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
          rw [← hB3, ← hB2]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hInBound _) (Nat.le_add_right _ 48)
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
      have hn3 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by omega
      have hn4 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + outCountPrefix H k u) := by omega
      rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_right hn3, ite_eq_right hn4]; exact hOutN
    have hInCurNext : ∀ v' < H.vertexCount,
        (s19.data[inStartArrBase H.vertexCount r.out.tables.next + v']?).map Fin.val =
          some (prefixIn H v' + inCountPrefix H (k + 1) v') := by
      intro v' hv'
      rw [hData19 (inStartArrBase H.vertexCount r.out.tables.next + v')]
      simp only [inCountPrefix, dite_eq_left hkLt]
      by_cases hvEq : v' = v
      · subst hvEq; rw [ite_eq_left rfl, ite_eq_left rfl, Option.map_some, h12_16Val, Nat.add_assoc]
      · have hn1 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
            inStartArrBase H.vertexCount r.out.tables.next + v :=
          fun h => hvEq (Nat.add_left_cancel h)
        have hn2 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
            inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) := by
          rw [← hB1, Nat.add_assoc]
          exact Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hv' (Nat.le_trans (Nat.le_succ _) (Nat.le_add_right _ _))) _)
        have hn3 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
          have h1 := Nat.add_lt_add_left hv' (inStartArrBase H.vertexCount r.out.tables.next)
          rw [Nat.add_assoc]
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
        have hn4 : inStartArrBase H.vertexCount r.out.tables.next + v' ≠
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
              (prefixOut H u + outCountPrefix H k u) := by
          have h1 := Nat.add_lt_add_left hv' (inStartArrBase H.vertexCount r.out.tables.next)
          rw [Nat.add_assoc, Nat.add_assoc]
          exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
        have hne : v ≠ v' := fun h => hvEq h.symm
        rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_right hn3, ite_eq_right hn4, ite_eq_right hne, Nat.add_zero]
        exact hInCur v' hv'
    have hInNNext :
        (s19.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val =
          some H.arcCount := by
      rw [hData19 (inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount)]
      have hn1 : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≠
          inStartArrBase H.vertexCount r.out.tables.next + v :=
        Nat.ne_of_gt (Nat.add_lt_add_left hvLt _)
      have hn2 : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≠
          inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) := by
        rw [← hB1, Nat.add_assoc]
        exact Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)) _)
      have hn3 : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u :=
        Nat.ne_of_lt (Nat.lt_of_le_of_lt hGapInTemp
          (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (by decide) large)) (Nat.le_add_right _ u)))
      have hn4 : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + outCountPrefix H k u) := by
        have hMid : tempArrBase H.vertexCount H.arcCount r.out.tables.next <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 :=
          Nat.lt_of_le_of_lt (Nat.le_add_right _ _) (Nat.lt_add_of_pos_right (Nat.succ_pos 0))
        exact Nat.ne_of_lt (Nat.lt_of_le_of_lt hGapInTemp (Nat.lt_of_lt_of_le hMid (Nat.le_add_right _ _)))
      rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_right hn3, ite_eq_right hn4]; exact hInN
    have hOutSlNext : ∀ u' < H.vertexCount, ∀ j : Fin (outCountPrefix H (k + 1) u'),
        (s19.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u' + j.val)]?).map Fin.val =
          some ((outArcsPrefix H (k + 1) u')[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt)) := by
      intro u' hu' j
      rw [hData19 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u' + j.val))]
      have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u' + j.val) ≠ inStartArrBase H.vertexCount r.out.tables.next + v := by
        have h1 := Nat.add_lt_add_left hvLt (inStartArrBase H.vertexCount r.out.tables.next)
        rw [Nat.add_assoc, Nat.add_assoc]
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_trans hGapInTemp (Nat.le_add_right _ _)))
      have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u' + j.val) ≠ inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) := by
        have h1 : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
          rw [← hB3, ← hB2]
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hInBound _) (Nat.le_add_right _ 48)
        rw [Nat.add_assoc, Nat.add_assoc]
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
      have hn3 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u' + j.val) ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by omega
      rw [ite_eq_right hn1, ite_eq_right hn2, ite_eq_right hn3]
      by_cases huEq : u' = u
      · subst huEq
        have huEq' : (rawOccurrence H ⟨k, hkLt⟩).1.val = u := rfl
        have hListEq : outArcsPrefix H (k + 1) u = outArcsPrefix H k u ++ [k] := by
          simp only [outArcsPrefix, dite_eq_left hkLt]
          exact ite_eq_left huEq'
        by_cases hjEq : j.val = outCountPrefix H k u
        · rw [ite_eq_left (by rw [hjEq])]
          change Option.map Fin.val (some wOutV) = _
          rw [Option.map_some, hr10_6]
          apply congrArg some
          symm
          have hSubLen : (outArcsPrefix H k u).length ≤ j.val := by rw [outArcsPrefix_length, hjEq]; exact Nat.le_refl _
          simp only [hListEq]
          rw [List.getElem_append_right hSubLen]
          simp only [outArcsPrefix_length, hjEq, Nat.sub_self, List.getElem_cons_zero]
        · have hjLt : j.val < outCountPrefix H k u := by
            have := j.isLt
            simp only [outCountPrefix, dite_eq_left hkLt] at this
            rw [ite_eq_left huEq'] at this
            omega
          rw [huEq']
          rw [ite_eq_right (fun h => hjEq (Nat.add_left_cancel (Nat.add_left_cancel h)))]
          have hOld := hOutSl u hu' ⟨j.val, hjLt⟩
          rw [hOld]
          apply congrArg some
          have hLtLen : j.val < (outArcsPrefix H k u).length := by rw [outArcsPrefix_length]; exact hjLt
          simp only [hListEq]
          rw [List.getElem_append_left hLtLen]
      · have hjLtK : j.val < outCountPrefix H k u' := by
          have := j.isLt
          simp only [outCountPrefix, dite_eq_left hkLt] at this
          have hne : (rawOccurrence H ⟨k, hkLt⟩).1.val ≠ u' := fun h => huEq h.symm
          rw [ite_eq_right hne] at this; omega
        have hjLeU' : j.val < degOut H u' := Nat.lt_of_lt_of_le hjLtK (outCountPrefix_mono H (Nat.le_of_lt hkLt) u')
        have hDisjSlot : prefixOut H u' + j.val ≠ prefixOut H u + outCountPrefix H k u := by
          by_cases hlt : u' < u
          · have hpu : prefixOut H (u' + 1) ≤ prefixOut H u := prefixOut_mono H hlt
            have : prefixOut H u' + degOut H u' = prefixOut H (u' + 1) := rfl
            omega
          · have hpu : prefixOut H (u + 1) ≤ prefixOut H u' := prefixOut_mono H (by omega)
            have h1p : prefixOut H u + degOut H u = prefixOut H (u + 1) := rfl
            have h2p : outCountPrefix H k u < degOut H u := by
              have huEq' : (rawOccurrence H ⟨k, hkLt⟩).1.val = u := rfl
              have ha : outCountPrefix H k u + 1 ≤ outCountPrefix H (k + 1) u := by
                simp only [outCountPrefix, dite_eq_left hkLt]
                rw [ite_eq_left huEq']
                exact Nat.le_refl _
              have hb : outCountPrefix H (k + 1) u ≤ degOut H u := outCountPrefix_mono H hkLt u
              omega
            omega
        rw [ite_eq_right (fun h => hDisjSlot (Nat.add_left_cancel h))]
        have hListEq : outArcsPrefix H (k + 1) u' = outArcsPrefix H k u' := by
          simp only [outArcsPrefix, dite_eq_left hkLt]
          have hne : (rawOccurrence H ⟨k, hkLt⟩).1.val ≠ u' := fun h => huEq h.symm
          rw [ite_eq_right hne]
        have hOld := hOutSl u' hu' ⟨j.val, hjLtK⟩
        rw [hOld]
        congr 1; congr 1; symm
        simp only [hListEq]
    have hInSlNext : ∀ v' < H.vertexCount, ∀ j : Fin (inCountPrefix H (k + 1) v'),
        (s19.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v' + j.val)]?).map Fin.val =
          some ((inArcsPrefix H (k + 1) v')[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt)) := by
      intro v' hv' j
      have hjInBound : prefixIn H v' + j.val < H.arcCount := by
        have hle1 : j.val < degIn H v' := Nat.lt_of_lt_of_le j.isLt (inCountPrefix_mono H hkLt v')
        have h1p : prefixIn H v' + degIn H v' = prefixIn H (v' + 1) := rfl
        have hle2 : prefixIn H (v' + 1) ≤ prefixIn H H.vertexCount := prefixIn_mono H hv'
        rw [prefixIn_vertexCount H] at hle2
        omega
      rw [hData19 (inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v' + j.val))]
      have hn1 : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v' + j.val) ≠
          inStartArrBase H.vertexCount r.out.tables.next + v := by
        rw [← hB1, Nat.add_assoc]
        exact Nat.ne_of_gt (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hvLt (Nat.le_trans (Nat.le_succ _) (Nat.le_add_right _ _))) _)
      have hLessTb : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v' + j.val) <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
        rw [← hB3, ← hB2]
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hjInBound _) (Nat.le_add_right _ 48)
      have hn3 : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v' + j.val) ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u :=
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hLessTb (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
      have hn4 : inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v' + j.val) ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + outCountPrefix H k u) :=
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hLessTb
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))))
      rw [ite_eq_right hn1]
      by_cases hvEq : v' = v
      · subst hvEq
        have hvEq' : (rawHead H ⟨k, hkLt⟩).val = v := rfl
        have hListEq : inArcsPrefix H (k + 1) v = inArcsPrefix H k v ++ [k] := by
          simp only [inArcsPrefix, dite_eq_left hkLt]
          exact ite_eq_left hvEq'
        by_cases hjEq : j.val = inCountPrefix H k v
        · rw [ite_eq_left (by rw [hjEq])]
          change Option.map Fin.val (some wInV) = _
          rw [Option.map_some, hr10_14]
          apply congrArg some
          symm
          have hSubLen : (inArcsPrefix H k v).length ≤ j.val := by rw [inArcsPrefix_length, hjEq]; exact Nat.le_refl _
          simp only [hListEq]
          rw [List.getElem_append_right hSubLen]
          simp only [inArcsPrefix_length, hjEq, Nat.sub_self, List.getElem_cons_zero]
        · have hjLt : j.val < inCountPrefix H k v := by
            have := j.isLt
            simp only [inCountPrefix, dite_eq_left hkLt] at this
            rw [ite_eq_left hvEq'] at this
            omega
          rw [ite_eq_right (fun h => hjEq (Nat.add_left_cancel (Nat.add_left_cancel h))), ite_eq_right hn3, ite_eq_right hn4]
          have hOld := hInSl v hv' ⟨j.val, hjLt⟩
          rw [hOld]
          apply congrArg some
          have hLtLen : j.val < (inArcsPrefix H k v).length := by rw [inArcsPrefix_length]; exact hjLt
          simp only [hListEq]
          rw [List.getElem_append_left hLtLen]
      · have hjLtK : j.val < inCountPrefix H k v' := by
          have := j.isLt
          simp only [inCountPrefix, dite_eq_left hkLt] at this
          have hne : (rawHead H ⟨k, hkLt⟩).val ≠ v' := fun h => hvEq h.symm
          rw [ite_eq_right hne] at this; omega
        have hjLeV' : j.val < degIn H v' := Nat.lt_of_lt_of_le hjLtK (inCountPrefix_mono H (Nat.le_of_lt hkLt) v')
        have hDisjSlot : prefixIn H v' + j.val ≠ prefixIn H v + inCountPrefix H k v := by
          by_cases hlt : v' < v
          · have hpv : prefixIn H (v' + 1) ≤ prefixIn H v := prefixIn_mono H hlt
            have : prefixIn H v' + degIn H v' = prefixIn H (v' + 1) := rfl
            omega
          · have hpv : prefixIn H (v + 1) ≤ prefixIn H v' := prefixIn_mono H (by omega)
            have h1p : prefixIn H v + degIn H v = prefixIn H (v + 1) := rfl
            have h2p : inCountPrefix H k v < degIn H v := by
              have hvEq' : (rawHead H ⟨k, hkLt⟩).val = v := rfl
              have ha : inCountPrefix H k v + 1 ≤ inCountPrefix H (k + 1) v := by
                simp only [inCountPrefix, dite_eq_left hkLt]
                rw [ite_eq_left hvEq']
                exact Nat.le_refl _
              have hb : inCountPrefix H (k + 1) v ≤ degIn H v := inCountPrefix_mono H hkLt v
              omega
            omega
        rw [ite_eq_right (fun h => hDisjSlot (Nat.add_left_cancel h)), ite_eq_right hn3, ite_eq_right hn4]
        have hListEq : inArcsPrefix H (k + 1) v' = inArcsPrefix H k v' := by
          simp only [inArcsPrefix, dite_eq_left hkLt]
          have hne : (rawHead H ⟨k, hkLt⟩).val ≠ v' := fun h => hvEq h.symm
          rw [ite_eq_right hne]
        have hOld := hInSl v' hv' ⟨j.val, hjLtK⟩
        rw [hOld]
        congr 1; congr 1; symm
        simp only [hListEq]
    obtain ⟨kRest, t, hkRest, hStepsRest, hpcT, h0T, h1T, hMetaT, h3T, h4T, h5T,
      hOutT, hOutNT, hInT, hInNT, hOutSlT, hInSlT, hFrT⟩ :=
      ih (k + 1) s19 hSubEq hkLt hpc19
        (by rw [hKeep19 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hKeep19 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hKeep19 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
        (by rw [hKeep19 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM])
        (by rw [hKeep19 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hN])
        (by rw [hKeep19 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hInS])
        (by rw [hKeep19 reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hOutS])
        (by rw [hKeep19 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hInArc])
        (by rw [hKeep19 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hOutArc])
        (by rw [hKeep19 reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hQSrc])
        (by rw [hKeep19 reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hQHead])
        hk1Val
        hOutCurNext hOutNNext hInCurNext hInNNext hOutSlNext hInSlNext
    have hkRes : 19 + kRest ≤ 19 * (H.arcCount - k) + 1 := by
      rw [hd]; rw [hSubEq] at hkRest
      exact Nat.le_trans (Nat.add_le_add_left hkRest 19)
        (by rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.add_comm 19, Nat.add_assoc]; exact Nat.le_refl _)
    refine ⟨19 + kRest, t, hkRes, hStep19.append hStepsRest, hpcT, h0T, h1T, hMetaT,
      h3T, h4T, h5T, hOutT, hOutNT, hInT, hInNT, hOutSlT, hInSlT, fun j hj => ?_⟩
    rw [hFrT j hj, hData19 j]
    have hjNotIn12 : ∀ a, inStartArrBase H.vertexCount r.out.tables.next ≤ a →
        a < inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount → j ≠ a := by
      intro a haL haR
      have haL2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ≥ a := by
        have h1 : a < tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
          rw [← hB3, ← hB2]; exact Nat.lt_of_lt_of_le haR (Nat.le_add_right _ 48)
        exact Nat.le_of_lt (Nat.lt_of_lt_of_le h1 (Nat.le_add_right _ _))
      rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h haL)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le haR h1)
      · have hStepTb : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 := by omega
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt haL2 hStepTb) h1)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt haL2 (by omega)) h)
    have hNe1 : j ≠ inStartArrBase H.vertexCount r.out.tables.next + v :=
      hjNotIn12 _ (Nat.le_add_right _ _) (by rw [← hB1]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_lt hvLt) _) (Nat.le_add_right _ _))
    have hNe2 : j ≠ inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + inCountPrefix H k v) :=
      hjNotIn12 _ (by rw [← hB1]; exact Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)) (Nat.add_lt_add_left hInBound _)
    have hNe3 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := by
      have haL : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ≤
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u := Nat.le_add_right _ _
      have haR : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) := by omega
      rcases hj with h | ⟨_, h2⟩ | ⟨h1, _⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h (Nat.le_trans (Nat.le_add_right _ _) hGapInTemp)) (Nat.le_trans (Nat.le_add_right _ _) haL))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2 haL)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le haR h1)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le haR (by omega)) h)
    have hNe4 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
        (prefixOut H u + outCountPrefix H k u) := by
      have haL : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + outCountPrefix H k u) := Nat.le_add_right _ _
      have haR : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u + outCountPrefix H k u) <
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + H.arcCount :=
        Nat.add_lt_add_left hOutBound _
      rcases hj with h | ⟨_, h2⟩ | ⟨_, h2⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h (Nat.le_trans (Nat.le_add_right _ _) hGapInTemp))
          (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ (3 * H.vertexCount)) (Nat.le_add_right _ 1)) haL))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2
          (Nat.le_trans (Nat.le_trans (Nat.add_le_add_left (by omega : H.vertexCount ≤ 3 * H.vertexCount) _) (Nat.le_add_right _ 1)) haL))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h2 haL)
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le haR h)
    rw [ite_eq_right hNe1, ite_eq_right hNe2, ite_eq_right hNe3, ite_eq_right hNe4]

private theorem csrScatterLoop2_step12 {code : Program DomL} {input : Input DomL}
    {isb outBase k wInVal wOutVal : Nat}
    (hPl : Placed code 47 csrScatterLoop2Instrs) (hSz : 61 < code.size)
    (hInFit : isb + (k + 1) < workCap)
    (hOutFit : outBase + (k + 1) < workCap)
    (hDisj : isb + (k + 1) ≠ outBase + k)
    (st : State DomL) (hpc : st.pc = 47)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hK : (reg st reg3).val = k + 1)
    (hInS : (reg st reg4).val = isb)
    (hOutS : (reg st reg5).val = outBase)
    (hInPrev : (st.data[isb + k]?).map Fin.val = some wInVal)
    (hOutPrev : (st.data[outBase + k]?).map Fin.val = some wOutVal) :
    ∃ (s12 : State DomL) (wIn wOut : Word bits),
      Steps code input 12 st s12 ∧ s12.pc = 47 ∧
      (reg s12 reg3).val = k ∧
      wIn.val = wInVal ∧ wOut.val = wOutVal ∧
      (∀ r : Fin 15, r ≠ reg3 → r ≠ reg8 → r ≠ reg9 → r ≠ reg10 → reg s12 r = reg st r) ∧
      (∀ j, s12.data[j]? =
        if j = outBase + (k + 1) then some wOut
        else if j = isb + (k + 1) then some wIn
        else st.data[j]?) := by
  have hCmp : code[st.pc]? = some (.branchLt reg0 reg3 48 59) := by rw [hpc]; exact hPl 0 _ rfl
  have hTrue : (reg st reg0).val < (reg st reg3).val := by rw [h0, hK]; exact Nat.succ_pos k
  obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp
    (by rw [ite_eq_left hTrue]; exact Nat.lt_trans (by decide) hSz)
  rw [ite_eq_left hTrue] at hpc1
  have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
  have hSub : code[s1.pc]? = some (.sub reg8 reg3 reg1) := by rw [hpc1]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, hr8_2, ho2, hd2⟩ := step_sub_at (input := input) hSub
    (by rw [hpc1]; exact Nat.lt_trans (by decide) hSz)
  have h3_1 : (reg s1 reg3).val = k + 1 := by rw [hr1, hK]
  have h1_1 : (reg s1 reg1).val = 1 := by rw [hr1, h1]
  have hk2 : (reg s2 reg8).val = k := by
    rw [hr8_2, sub_no_wrap _ _ (by rw [h1_1, h3_1]; omega), h3_1, h1_1]; omega
  have ha1 : code[s2.pc]? = some (.add reg9 reg4 reg8) := by
    rw [hpc2, hpc1]; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, hr9_3, ho3, hd3⟩ := step_add_at (input := input) ha1
    (by rw [hpc2, hpc1]; exact Nat.lt_trans (by decide) hSz)
  have h4_2 : (reg s2 reg4).val = isb := by rw [ho2 reg4 (by intro h; cases h), hr1, hInS]
  have hAddrInPrev : (reg s3 reg9).val = isb + k := by
    rw [hr9_3, add_no_wrap _ _ (by rw [h4_2, hk2]; exact Nat.lt_of_lt_of_le (by omega) hw), h4_2, hk2]
  obtain ⟨wIn, hwIn, hwInV⟩ := Option.map_eq_some_iff.mp hInPrev
  have hl1 : code[s3.pc]? = some (.loadData reg10 reg9) := by
    rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
  obtain ⟨s4, hs4, hpc4, hr10_4, ho4, hd4⟩ := step_loadData_at (input := input) hl1
    (by rw [hpc3, hpc2, hpc1]; exact Nat.lt_trans (by decide) hSz)
    (by rw [hAddrInPrev, hd3, hd2, hd1]; exact hwIn)
  have ha2 : code[s4.pc]? = some (.add reg9 reg4 reg3) := by
    rw [hpc4, hpc3, hpc2, hpc1]; exact hPl 4 _ rfl
  obtain ⟨s5, hs5, hpc5, hr9_5, ho5, hd5⟩ := step_add_at (input := input) ha2
    (by rw [hpc4, hpc3, hpc2, hpc1]; exact Nat.lt_trans (by decide) hSz)
  have h4_4 : (reg s4 reg4).val = isb := by
    rw [ho4 reg4 (by intro h; cases h), ho3 reg4 (by intro h; cases h), h4_2]
  have h3_4 : (reg s4 reg3).val = k + 1 := by
    rw [ho4 reg3 (by intro h; cases h), ho3 reg3 (by intro h; cases h),
      ho2 reg3 (by intro h; cases h), h3_1]
  have hAddrInCur : (reg s5 reg9).val = isb + (k + 1) := by
    rw [hr9_5, add_no_wrap _ _ (by rw [h4_4, h3_4]; exact Nat.lt_of_lt_of_le hInFit hw), h4_4, h3_4]
  have hLtIn5 : (reg s5 reg9).val < s5.data.size := by
    rw [s5.data_size, hAddrInCur]; exact hInFit
  have hst1 : code[s5.pc]? = some (.storeData reg9 reg10) := by
    rw [hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPl 5 _ rfl
  obtain ⟨hs6, hpc6, _⟩ := step_storeData_at (input := input) hst1 hLtIn5
    (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]; exact Nat.lt_trans (by decide) hSz)
  let s6 : State DomL :=
    { s5 with
      data := s5.data.set (reg s5 reg9).val (reg s5 reg10) hLtIn5
      pc := s5.pc + 1
      data_size := by simp only [Array.size_set, s5.data_size] }
  have hpc6 : s6.pc = 47 + 6 := by dsimp only [s6]; rw [hpc5, hpc4, hpc3, hpc2, hpc1]
  have ha3 : code[s6.pc]? = some (.add reg9 reg5 reg8) := by rw [hpc6]; exact hPl 6 _ rfl
  obtain ⟨s7, hs7, hpc7, hr9_7, ho7, hd7⟩ := step_add_at (input := input) ha3
    (by rw [hpc6]; exact Nat.lt_trans (by decide) hSz)
  have h5_6 : (reg s6 reg5).val = outBase := by
    change (reg s5 reg5).val = _
    rw [ho5 reg5 (by intro h; cases h), ho4 reg5 (by intro h; cases h), ho3 reg5 (by intro h; cases h),
      ho2 reg5 (by intro h; cases h), hr1, hOutS]
  have h8_6 : (reg s6 reg8).val = k := by
    change (reg s5 reg8).val = _
    rw [ho5 reg8 (by intro h; cases h), ho4 reg8 (by intro h; cases h), ho3 reg8 (by intro h; cases h), hk2]
  have hAddrOutPrev : (reg s7 reg9).val = outBase + k := by
    rw [hr9_7, add_no_wrap _ _ (by rw [h5_6, h8_6]; exact Nat.lt_of_lt_of_le (by omega) hw), h5_6, h8_6]
  obtain ⟨wOut, hwOut, hwOutV⟩ := Option.map_eq_some_iff.mp hOutPrev
  have hl2 : code[s7.pc]? = some (.loadData reg10 reg9) := by
    rw [hpc7, hpc6]; exact hPl 7 _ rfl
  obtain ⟨s8, hs8, hpc8, hr10_8, ho8, hd8⟩ := step_loadData_at (input := input) hl2
    (by rw [hpc7, hpc6]; exact Nat.lt_trans (by decide) hSz)
    (by
      rw [hAddrOutPrev, hd7]
      change (s5.data.set (reg s5 reg9).val (reg s5 reg10) hLtIn5)[outBase + k]? = some wOut
      rw [Array.getElem?_set_ne hLtIn5 (by rw [hAddrInCur]; exact hDisj), hd5, hd4, hd3, hd2, hd1]
      exact hwOut)
  have ha4 : code[s8.pc]? = some (.add reg9 reg5 reg3) := by
    rw [hpc8, hpc7, hpc6]; exact hPl 8 _ rfl
  obtain ⟨s9, hs9, hpc9, hr9_9, ho9, hd9⟩ := step_add_at (input := input) ha4
    (by rw [hpc8, hpc7, hpc6]; exact Nat.lt_trans (by decide) hSz)
  have h5_8 : (reg s8 reg5).val = outBase := by
    rw [ho8 reg5 (by intro h; cases h), ho7 reg5 (by intro h; cases h), h5_6]
  have h3_8 : (reg s8 reg3).val = k + 1 := by
    rw [ho8 reg3 (by intro h; cases h), ho7 reg3 (by intro h; cases h)]
    change (reg s5 reg3).val = _
    rw [ho5 reg3 (by intro h; cases h), h3_4]
  have hAddrOutCur : (reg s9 reg9).val = outBase + (k + 1) := by
    rw [hr9_9, add_no_wrap _ _ (by rw [h5_8, h3_8]; exact Nat.lt_of_lt_of_le hOutFit hw), h5_8, h3_8]
  have hLtOut9 : (reg s9 reg9).val < s9.data.size := by
    rw [s9.data_size, hAddrOutCur]; exact hOutFit
  have hst2 : code[s9.pc]? = some (.storeData reg9 reg10) := by
    rw [hpc9, hpc8, hpc7, hpc6]; exact hPl 9 _ rfl
  obtain ⟨hs10, hpc10, _⟩ := step_storeData_at (input := input) hst2 hLtOut9
    (by rw [hpc9, hpc8, hpc7, hpc6]; exact Nat.lt_trans (by decide) hSz)
  let s10 : State DomL :=
    { s9 with
      data := s9.data.set (reg s9 reg9).val (reg s9 reg10) hLtOut9
      pc := s9.pc + 1
      data_size := by simp only [Array.size_set, s9.data_size] }
  have hpc10 : s10.pc = 47 + 10 := by dsimp only [s10]; rw [hpc9, hpc8, hpc7, hpc6]
  have hMov : code[s10.pc]? = some (.mov reg3 reg8) := by rw [hpc10]; exact hPl 10 _ rfl
  obtain ⟨s11, hs11, hpc11, hr3_11, ho11, hd11⟩ := step_mov_at (input := input) hMov
    (by rw [hpc10]; exact Nat.lt_trans (by decide) hSz)
  have hJmp : code[s11.pc]? = some (.goto 47) := by rw [hpc11, hpc10]; exact hPl 11 _ rfl
  obtain ⟨s12, hs12, hpc12, hreg12, hd12⟩ := step_goto_at (input := input) hJmp (Nat.lt_trans (by decide) hSz)
  have hr12 : ∀ r : Fin 15, reg s12 r = reg s11 r := reg_of_regs_eq hreg12
  have hr10_5 : reg s5 reg10 = wIn := by
    rw [ho5 reg10 (by intro h; cases h), hr10_4]
  have hr10_9 : reg s9 reg10 = wOut := by
    rw [ho9 reg10 (by intro h; cases h), hr10_8]
  refine ⟨s12, wIn, wOut,
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (steps_1_of_step hs12))))))))))),
    hpc12, ?_, hwInV, hwOutV, ?_, ?_⟩
  · rw [hr12, hr3_11]; change (reg s9 reg8).val = k
    rw [ho9 reg8 (by intro h; cases h), ho8 reg8 (by intro h; cases h),
      ho7 reg8 (by intro h; cases h), h8_6]
  · intro r hr3 hr8 hr9 hr10
    rw [hr12, ho11 r hr3]; change reg s9 r = _
    rw [ho9 r hr9, ho8 r hr10, ho7 r hr9]; change reg s5 r = _
    rw [ho5 r hr9, ho4 r hr10, ho3 r hr9, ho2 r hr8, hr1]
  · intro j
    rw [hd12, hd11]
    change (s9.data.set (reg s9 reg9).val (reg s9 reg10) hLtOut9)[j]? = _
    by_cases hA : j = outBase + (k + 1)
    · subst hA; rw [ite_eq_left rfl, ← hAddrOutCur, ← hr10_9]; simp [hLtOut9]
    · rw [ite_eq_right hA, Array.getElem?_set_ne hLtOut9 (by rw [hAddrOutCur]; exact fun hh => hA hh.symm),
        hd9, hd8, hd7]
      change (s5.data.set (reg s5 reg9).val (reg s5 reg10) hLtIn5)[j]? = _
      by_cases hB : j = isb + (k + 1)
      · subst hB; rw [ite_eq_left rfl, ← hAddrInCur, ← hr10_5]; simp [hLtIn5]
      · rw [ite_eq_right hB, Array.getElem?_set_ne hLtIn5 (by rw [hAddrInCur]; exact fun hh => hB hh.symm),
          hd5, hd4, hd3, hd2, hd1]

private theorem csrScatterLoop2_spec {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hPl : Placed code 47 csrScatterLoop2Instrs) (hSz : 61 < code.size)
    (k : Nat) (hkLe : k ≤ H.vertexCount)
    (st : State DomL) (hpc : st.pc = 47)
    (h0 : (reg st reg0).val = 0) (h1 : (reg st reg1).val = 1)
    (hMeta : (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next)
    (hK : (reg st reg3).val = k)
    (hInS : (reg st reg4).val = inStartArrBase H.vertexCount r.out.tables.next)
    (hOutS : (reg st reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount)
    (hInLow : ∀ j < k, (st.data[inStartArrBase H.vertexCount r.out.tables.next + j]?).map Fin.val =
      some (prefixIn H (j + 1)))
    (hInHigh : ∀ j, k < j → j ≤ H.vertexCount →
      (st.data[inStartArrBase H.vertexCount r.out.tables.next + j]?).map Fin.val = some (prefixIn H j))
    (hOutLow : ∀ j < k, (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j]?).map Fin.val =
      some (prefixOut H (j + 1)))
    (hOutHigh : ∀ j, k < j → j ≤ H.vertexCount →
      (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j]?).map Fin.val =
        some (prefixOut H j)) :
    ∃ steps : Nat, ∃ t : State DomL,
      steps ≤ 12 * k + 3 ∧
      Steps code input steps st t ∧ t.pc = 61 ∧
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
  have hInEndLt : inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount < workCap := by omega
  have hOutEndLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + H.vertexCount < workCap := by omega
  induction k generalizing st with
  | zero =>
    have hCmp : code[st.pc]? = some (.branchLt reg0 reg3 48 59) := by rw [hpc]; exact hPl 0 _ rfl
    have hFalse : ¬ ((reg st reg0).val < (reg st reg3).val) := by rw [h0, hK]; exact Nat.lt_irrefl 0
    obtain ⟨s1, hs1, hpc1, hreg1, hd1⟩ := step_branchLt_at (input := input) hCmp
      (by rw [ite_eq_right hFalse]; exact Nat.lt_trans (by decide) hSz)
    rw [ite_eq_right hFalse] at hpc1
    have hr1 : ∀ r : Fin 15, reg s1 r = reg st r := reg_of_regs_eq hreg1
    have h4_1 : (reg s1 reg4).val = inStartArrBase H.vertexCount r.out.tables.next := by rw [hr1, hInS]
    have h0_1 : (reg s1 reg0).val = 0 := by rw [hr1, h0]
    have hLtIn1 : (reg s1 reg4).val < s1.data.size := by
      rw [s1.data_size, h4_1]; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hInEndLt
    have hst1 : code[s1.pc]? = some (.storeData reg4 reg0) := by rw [hpc1]; exact hPl 12 _ rfl
    obtain ⟨hs2, hpc2, _⟩ := step_storeData_at (input := input) hst1 hLtIn1
      (by rw [hpc1]; exact Nat.lt_trans (by decide) hSz)
    let s2 : State DomL :=
      { s1 with
        data := s1.data.set (reg s1 reg4).val (reg s1 reg0) hLtIn1
        pc := s1.pc + 1
        data_size := by simp only [Array.size_set, s1.data_size] }
    have hpc2 : s2.pc = 47 + 13 := by dsimp only [s2]; rw [hpc1]
    have h5_2 : (reg s2 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
      change (reg s1 reg5).val = _; rw [hr1, hOutS]
    have hLtOut2 : (reg s2 reg5).val < s2.data.size := by
      rw [s2.data_size, h5_2]; exact Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hOutEndLt
    have hst2 : code[s2.pc]? = some (.storeData reg5 reg0) := by rw [hpc2]; exact hPl 13 _ rfl
    obtain ⟨hs3, hpc3, _⟩ := step_storeData_at (input := input) hst2 hLtOut2
      (by rw [hpc2]; exact hSz)
    let s3 : State DomL :=
      { s2 with
        data := s2.data.set (reg s2 reg5).val (reg s2 reg0) hLtOut2
        pc := s2.pc + 1
        data_size := by simp only [Array.size_set, s2.data_size] }
    have hpc3 : s3.pc = 61 := by dsimp only [s3]; rw [hpc2]
    refine ⟨3, s3, by decide, Steps.cons hs1 (Steps.cons hs2 (steps_1_of_step hs3)), hpc3,
      by change (reg s2 reg0).val = 0; change (reg s1 reg0).val = 0; exact h0_1,
      by change (reg s2 reg1).val = 1; change (reg s1 reg1).val = 1; rw [hr1, h1],
      by change (reg s2 rMeta).val = _; change (reg s1 rMeta).val = _; rw [hr1, hMeta],
      fun i hiLe => ?_, fun i hiLe => ?_, fun j hj => ?_⟩
    · have hDisj : inStartArrBase H.vertexCount r.out.tables.next + i ≠
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by omega
      change (s2.data.set (reg s2 reg5).val (reg s2 reg0) hLtOut2)[inStartArrBase H.vertexCount r.out.tables.next + i]?.map Fin.val = _
      rw [Array.getElem?_set_ne hLtOut2 (by rw [h5_2]; exact hDisj.symm)]
      by_cases hi0 : i = 0
      · subst hi0
        have hSet0 : (s1.data.set (reg s1 reg4).val (reg s1 reg0) hLtIn1)[inStartArrBase H.vertexCount r.out.tables.next + 0]? =
            some (reg s1 reg0) := by
          rw [Nat.add_zero, ← h4_1]; simp [hLtIn1]
        change (s1.data.set (reg s1 reg4).val (reg s1 reg0) hLtIn1)[inStartArrBase H.vertexCount r.out.tables.next + 0]?.map Fin.val = _
        rw [hSet0, Option.map_some, Option.some.injEq, h0_1]; rfl
      · rw [Array.getElem?_set_ne hLtIn1 (by rw [h4_1]; exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hi0))), hd1]
        exact hInHigh i (Nat.pos_of_ne_zero hi0) hiLe
    · change (s2.data.set (reg s2 reg5).val (reg s2 reg0) hLtOut2)[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?.map Fin.val = _
      by_cases hi0 : i = 0
      · subst hi0
        have hSet0 : (s2.data.set (reg s2 reg5).val (reg s2 reg0) hLtOut2)[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + 0]? =
            some (reg s2 reg0) := by
          rw [Nat.add_zero, ← h5_2]; simp [hLtOut2]
        rw [hSet0, Option.map_some, Option.some.injEq]
        change (reg s1 reg0).val = prefixOut H 0
        rw [h0_1]; rfl
      · have hDisjOut : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i ≠
            inStartArrBase H.vertexCount r.out.tables.next := by
          exact Nat.ne_of_gt (Nat.lt_of_le_of_lt
            (Nat.le_trans (Nat.le_add_right _ H.vertexCount) (Nat.le_trans hGapInTemp (Nat.le_add_right _ H.vertexCount)))
            (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hi0)))
        rw [Array.getElem?_set_ne hLtOut2 (by rw [h5_2]; exact Nat.ne_of_lt (Nat.lt_add_of_pos_right (Nat.pos_of_ne_zero hi0))),
          Array.getElem?_set_ne hLtIn1 (by rw [h4_1]; exact hDisjOut.symm),
          hd1]
        exact hOutHigh i (Nat.pos_of_ne_zero hi0) hiLe
    · change (s2.data.set (reg s2 reg5).val (reg s2 reg0) hLtOut2)[j]? = st.data[j]?
      have hNe5 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
        rcases hj with h | ⟨_, h⟩ | h
        · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h
            (Nat.le_trans (Nat.le_add_right _ H.vertexCount) (Nat.le_trans hGapInTemp (Nat.le_add_right _ H.vertexCount))))
        · exact Nat.ne_of_lt h
        · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega) h)
      have hNe4 : j ≠ inStartArrBase H.vertexCount r.out.tables.next := by
        rcases hj with h | ⟨h, _⟩ | h
        · exact Nat.ne_of_lt h
        · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos H.vertexCount)) h)
        · exact Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.le_add_right _ H.vertexCount) hGapInTemp)
            (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega)) h))
      rw [Array.getElem?_set_ne hLtOut2 (by rw [h5_2]; exact hNe5.symm),
        Array.getElem?_set_ne hLtIn1 (by rw [h4_1]; exact hNe4.symm), hd1]
  | succ k ih =>
    have hInFitK : inStartArrBase H.vertexCount r.out.tables.next + (k + 1) < workCap :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left hkLe _) hInEndLt
    have hOutFitK : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) < workCap :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_left hkLe _) hOutEndLt
    have hDisjK : inStartArrBase H.vertexCount r.out.tables.next + (k + 1) ≠
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + k := by
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_of_le_of_lt hkLe (Nat.lt_succ_self _)) _)
        (by
          rw [← hB3, ← hB2, ← hB1]
          exact Nat.le_trans (Nat.le_add_right _ _)
            (Nat.le_trans (Nat.le_add_right _ _)
              (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))))
    obtain ⟨s12, wIn, wOut, hStep12, hpc12, hK12, hwInV, hwOutV, hKeep12, hData12⟩ :=
      csrScatterLoop2_step12 hPl hSz hInFitK hOutFitK hDisjK st hpc h0 h1 hK hInS hOutS
        (hInLow k (Nat.lt_succ_self k)) (hOutLow k (Nat.lt_succ_self k))
    obtain ⟨kRest, t, hkRest, hStepsRest, hpcT, h0T, h1T, hMetaT, hInRes, hOutRes, hFrT⟩ :=
      ih (Nat.le_trans (Nat.le_succ k) hkLe) s12 hpc12
        (by rw [hKeep12 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hKeep12 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hKeep12 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
        hK12
        (by rw [hKeep12 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hInS])
        (by rw [hKeep12 reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hOutS])
        (fun j hjk => by
          rw [hData12 (inStartArrBase H.vertexCount r.out.tables.next + j)]
          have hn1 : inStartArrBase H.vertexCount r.out.tables.next + j ≠
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) :=
            Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_of_lt hjk) hkLe) _)
              (Nat.le_trans hGapInTemp (Nat.le_trans (Nat.le_add_right _ H.vertexCount) (Nat.le_add_right _ (k + 1)))))
          have hn2 : inStartArrBase H.vertexCount r.out.tables.next + j ≠
              inStartArrBase H.vertexCount r.out.tables.next + (k + 1) :=
            Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_succ_of_lt hjk) _)
          rw [ite_eq_right hn1, ite_eq_right hn2]
          exact hInLow j (Nat.lt_succ_of_lt hjk))
        (fun j hkj hjn => by
          rw [hData12 (inStartArrBase H.vertexCount r.out.tables.next + j)]
          have hn1 : inStartArrBase H.vertexCount r.out.tables.next + j ≠
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) :=
            Nat.ne_of_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_left hjn _)
              (Nat.lt_of_le_of_lt (Nat.le_trans hGapInTemp (Nat.le_add_right _ H.vertexCount)) (Nat.lt_add_of_pos_right (Nat.succ_pos _))))
          rw [ite_eq_right hn1]
          by_cases hjEq : j = k + 1
          · subst hjEq; rw [ite_eq_left rfl, Option.map_some, hwInV]
          · rw [ite_eq_right (fun h => hjEq (Nat.add_left_cancel h))]
            exact hInHigh j (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hkj) (Ne.symm hjEq)) hjn)
        (fun j hjk => by
          rw [hData12 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j)]
          have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j ≠
              tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) :=
            Nat.ne_of_lt (Nat.add_lt_add_left (Nat.lt_succ_of_lt hjk) _)
          have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j ≠
              inStartArrBase H.vertexCount r.out.tables.next + (k + 1) :=
            Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.add_le_add_left hkLe _) hGapInTemp)
              (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (by decide : 0 < 3) large)) (Nat.le_add_right _ j)))
          rw [ite_eq_right hn1, ite_eq_right hn2]
          exact hOutLow j (Nat.lt_succ_of_lt hjk))
        (fun j hkj hjn => by
          rw [hData12 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j)]
          by_cases hjEq : j = k + 1
          · subst hjEq; rw [ite_eq_left rfl, Option.map_some, hwOutV]
          · have hn1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j ≠
                tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) :=
              fun h => hjEq (Nat.add_left_cancel h)
            have hn2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + j ≠
                inStartArrBase H.vertexCount r.out.tables.next + (k + 1) :=
              Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.add_le_add_left hkLe _) hGapInTemp)
                (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.lt_of_lt_of_le (by decide : 0 < 3) large)) (Nat.le_add_right _ j)))
            rw [ite_eq_right hn1, ite_eq_right hn2]
            exact hOutHigh j (Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hkj) (Ne.symm hjEq)) hjn)
    refine ⟨12 + kRest, t, Nat.le_trans (Nat.add_le_add_left hkRest 12) (by omega),
      hStep12.append hStepsRest, hpcT, h0T, h1T, hMetaT, hInRes, hOutRes, fun j hj => ?_⟩
    rw [hFrT j hj, hData12 j]
    have hNe1 : j ≠ tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) := by
      rcases hj with h | ⟨_, h⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h
          (Nat.le_trans (Nat.le_add_right _ H.vertexCount) (Nat.le_trans hGapInTemp (Nat.le_trans (Nat.le_add_right _ H.vertexCount) (Nat.le_add_right _ (k + 1))))))
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
      · have hLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + (k + 1) <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) := by
          rw [Nat.add_assoc]
          exact Nat.add_lt_add_left (Nat.lt_succ_of_le (Nat.le_trans (Nat.add_le_add_left hkLe _) (by rw [Nat.two_mul]; exact Nat.le_refl _))) _
        exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt h)
    have hNe2 : j ≠ inStartArrBase H.vertexCount r.out.tables.next + (k + 1) := by
      rcases hj with h | ⟨h, _⟩ | h
      · exact Nat.ne_of_lt (Nat.lt_of_lt_of_le h (Nat.le_add_right _ _))
      · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_succ_of_le hkLe) _) h)
      · exact Nat.ne_of_gt (Nat.lt_of_le_of_lt (Nat.le_trans (Nat.add_le_add_left hkLe _) hGapInTemp)
          (Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (Nat.succ_pos _)) h))
    rw [ite_eq_right hNe1, ite_eq_right hNe2]

private theorem csrScatter_step_bound0 {n m k2 : Nat}
    (hk2 : k2 ≤ 12 * n + 3) :
    21 + k2 + 1 ≤ 12 * n + 19 * m + 35 := by omega

private theorem csrScatter_step_bound1 {n m k1 k2 : Nat}
    (hk1 : k1 ≤ 19 * (m - 0) + 1) (hk2 : k2 ≤ 12 * n + 3) :
    (28 + k1) + k2 + 1 ≤ 12 * n + 19 * m + 35 := by omega

private theorem csrScatter_prefix20 {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hPlSetup : Placed code 0 (csrScatterSetupInstrs (bits := bits) h100))
    (hSz : 20 < code.size)
    (hTempAddLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 < 2 ^ bits)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal) :
    ∃ s10 : State DomL,
      Steps code input 20 (Phase.initial s0) s10 ∧
      s10.pc = 20 ∧
      s10.data = s0.data ∧
      (reg s10 reg0).val = 0 ∧
      (reg s10 reg1).val = 1 ∧
      (reg s10 reg2).val = H.arcCount ∧
      (reg s10 reg3).val = H.vertexCount ∧
      (reg s10 reg4).val = inStartArrBase H.vertexCount r.out.tables.next ∧
      (reg s10 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ∧
      (reg s10 reg6).val = inArcIdArrBase H.vertexCount r.out.tables.next ∧
      (reg s10 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ∧
      (reg s10 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlM := Placed_append_left (by unfold csrScatterSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold csrScatterSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPlN := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
  have hPlInS := Placed_append_left hPlS2
  have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
  have hPlTemp := Placed_append_left hPlS3
  have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
  have hPlAdds := Placed_append_left hPlS4
  have hPlS5 := Placed_append_right hPlS4
  rw [show ([Instr.add reg7 reg5 reg3, Instr.add reg7 reg7 reg3, Instr.add reg7 reg7 reg3,
    Instr.add reg7 reg7 reg1, Instr.add reg5 reg5 reg3] : List (Instr bits 15)).length = 5 by rfl] at hPlS5
  have hPlInArc := Placed_append_left hPlS5
  have hMeta48 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ 2 ^ bits := by
    change tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ 2 ^ bits
    exact Nat.le_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _)
      (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hTempAddLt))
  have hFitM : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxM < 2 ^ bits := by
    dsimp only [mIdxM]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hFitN : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxN < 2 ^ bits := by
    dsimp only [mIdxN]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hFitInS : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxInStartBase < 2 ^ bits := by
    dsimp only [mIdxInStartBase]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hFitTemp : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxTempBase < 2 ^ bits := by
    dsimp only [mIdxTempBase]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hFitInArc : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxInArcIdBase < 2 ^ bits := by
    dsimp only [mIdxInArcIdBase]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hAdd1 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount < 2 ^ bits := by omega
  have hAdd2 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + H.vertexCount < 2 ^ bits := by omega
  have hAdd3 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + H.vertexCount < 2 ^ bits := by omega
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlM (Nat.lt_trans (by decide) hSz) rfl hMeta.rMeta_eq hFitM hMeta.meta_m
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlN (Nat.lt_trans (by decide) hSz) hpc1 hMeta1 hFitN
    (by rw [hd1]; exact hMeta.meta_n)
  have hMeta2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho2 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta1
  obtain ⟨s3, hs3, hpc3, hd3, h4_3, ho3⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlInS (Nat.lt_trans (by decide) hSz) hpc2 hMeta2 hFitInS
    (by rw [hd2, hd1]; exact hMeta.meta_inStartBase)
  have hMeta3 : (reg s3 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho3 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta2
  obtain ⟨s4, hs4, hpc4, hd4, h5_4, ho4⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlTemp (Nat.lt_trans (by decide) hSz) hpc3 hMeta3 hFitTemp
    (by rw [hd3, hd2, hd1]; exact hMeta.meta_tempBase)
  have hMeta4 : (reg s4 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho4 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta3
  have h0_4 : (reg s4 reg0).val = 0 := by
    rw [ho4 reg0 (by intro h; cases h) (by intro h; cases h), ho3 reg0 (by intro h; cases h) (by intro h; cases h),
      ho2 reg0 (by intro h; cases h) (by intro h; cases h), ho1 reg0 (by intro h; cases h) (by intro h; cases h),
      reg_initial, hMeta.r0_zero]
  have h1_4 : (reg s4 reg1).val = 1 := by
    rw [ho4 reg1 (by intro h; cases h) (by intro h; cases h), ho3 reg1 (by intro h; cases h) (by intro h; cases h),
      ho2 reg1 (by intro h; cases h) (by intro h; cases h), ho1 reg1 (by intro h; cases h) (by intro h; cases h),
      reg_initial, hMeta.r1_one]
  have h2_4 : (reg s4 reg2).val = H.arcCount := by
    rw [ho4 reg2 (by intro h; cases h) (by intro h; cases h), ho3 reg2 (by intro h; cases h) (by intro h; cases h),
      ho2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h3_4 : (reg s4 reg3).val = H.vertexCount := by
    rw [ho4 reg3 (by intro h; cases h) (by intro h; cases h), ho3 reg3 (by intro h; cases h) (by intro h; cases h), h3_2]
  have h4_4 : (reg s4 reg4).val = inStartArrBase H.vertexCount r.out.tables.next := by
    rw [ho4 reg4 (by intro h; cases h) (by intro h; cases h), h4_3]
  have ha1 : code[s4.pc]? = some (.add reg7 reg5 reg3) := by rw [hpc4]; exact hPlAdds 0 _ rfl
  obtain ⟨s5, hs5, hpc5, h7_5, ho5, hd5⟩ := step_add_at (input := input) ha1 (by rw [hpc4]; exact Nat.lt_trans (by decide) hSz)
  have hpc5' : s5.pc = 13 := by rw [hpc5, hpc4]
  have h7Val5 : (reg s5 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [h7_5, add_no_wrap _ _ (by rw [h5_4, h3_4]; exact hAdd1), h5_4, h3_4]
  have ha2 : code[s5.pc]? = some (.add reg7 reg7 reg3) := by rw [hpc5']; exact hPlAdds 1 _ rfl
  obtain ⟨s6, hs6, hpc6, h7_6, ho6, hd6⟩ := step_add_at (input := input) ha2 (by rw [hpc5']; exact Nat.lt_trans (by decide) hSz)
  have hpc6' : s6.pc = 14 := by rw [hpc6, hpc5']
  have h3_5 : (reg s5 reg3).val = H.vertexCount := by rw [ho5 reg3 (by intro h; cases h), h3_4]
  have h7Val6 : (reg s6 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount := by
    rw [h7_6, add_no_wrap _ _ (by rw [h7Val5, h3_5]; exact hAdd2), h7Val5, h3_5, Nat.add_assoc, Nat.two_mul]
  have ha3 : code[s6.pc]? = some (.add reg7 reg7 reg3) := by rw [hpc6']; exact hPlAdds 2 _ rfl
  obtain ⟨s7, hs7, hpc7, h7_7, ho7, hd7⟩ := step_add_at (input := input) ha3 (by rw [hpc6']; exact Nat.lt_trans (by decide) hSz)
  have hpc7' : s7.pc = 15 := by rw [hpc7, hpc6']
  have h3_6 : (reg s6 reg3).val = H.vertexCount := by rw [ho6 reg3 (by intro h; cases h), h3_5]
  have h7Val7 : (reg s7 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount := by
    rw [h7_7, add_no_wrap _ _ (by rw [h7Val6, h3_6]; exact hAdd3), h7Val6, h3_6, Nat.add_assoc, ← Nat.succ_mul 2]
  have ha4 : code[s7.pc]? = some (.add reg7 reg7 reg1) := by rw [hpc7']; exact hPlAdds 3 _ rfl
  obtain ⟨s8, hs8, hpc8, h7_8, ho8, hd8⟩ := step_add_at (input := input) ha4 (by rw [hpc7']; exact Nat.lt_trans (by decide) hSz)
  have hpc8' : s8.pc = 16 := by rw [hpc8, hpc7']
  have h1_7 : (reg s7 reg1).val = 1 := by
    rw [ho7 reg1 (by intro h; cases h), ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h), h1_4]
  have h7Val8 : (reg s8 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 := by
    rw [h7_8, add_no_wrap _ _ (by rw [h7Val7, h1_7]; exact hTempAddLt), h7Val7, h1_7]
  have ha5 : code[s8.pc]? = some (.add reg5 reg5 reg3) := by rw [hpc8']; exact hPlAdds 4 _ rfl
  obtain ⟨s9, hs9, hpc9, h5_9, ho9, hd9⟩ := step_add_at (input := input) ha5 (by rw [hpc8']; exact Nat.lt_trans (by decide) hSz)
  have hpc9' : s9.pc = 0 + 3 + 3 + 3 + 3 + 5 := by rw [hpc9, hpc8']
  have h5_8 : (reg s8 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho8 reg5 (by intro h; cases h), ho7 reg5 (by intro h; cases h), ho6 reg5 (by intro h; cases h),
      ho5 reg5 (by intro h; cases h), h5_4]
  have h3_8 : (reg s8 reg3).val = H.vertexCount := by rw [ho8 reg3 (by intro h; cases h), ho7 reg3 (by intro h; cases h), h3_6]
  have hOutS9 : (reg s9 reg5).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [h5_9, add_no_wrap _ _ (by rw [h5_8, h3_8]; exact hAdd1), h5_8, h3_8]
  have hMeta9 : (reg s9 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h),
      ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h), hMeta4]
  have hd9' : s9.data = s0.data := by rw [hd9, hd8, hd7, hd6, hd5, hd4, hd3, hd2, hd1, data_initial]
  obtain ⟨s10, hs10, hpc10, hd10, h6_10, ho10⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlInArc hSz hpc9' hMeta9 hFitInArc
    (by rw [hd9']; exact hMeta.meta_inArcIdBase)
  have hKeep10 : ∀ rf : Fin 15, rf ≠ reg5 → rf ≠ reg6 → rf ≠ reg7 → rf ≠ reg11 → reg s10 rf = reg s4 rf := by
    intro rf hr5 hr6 hr7 hr11
    rw [ho10 rf hr6 hr11, ho9 rf hr5, ho8 rf hr7, ho7 rf hr7, ho6 rf hr7, ho5 rf hr7]
  refine ⟨s10,
    hs1.append (hs2.append (hs3.append (hs4.append (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7
      (Steps.cons hs8 (Steps.cons hs9 hs10)))))))),
    hpc10, by rw [hd10, hd9'],
    by rw [hKeep10 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_4],
    by rw [hKeep10 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_4],
    by rw [hKeep10 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2_4],
    by rw [hKeep10 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3_4],
    by rw [hKeep10 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4_4],
    by rw [ho10 reg5 (by intro h; cases h) (by intro h; cases h), hOutS9],
    h6_10,
    by rw [ho10 reg7 (by intro h; cases h) (by intro h; cases h), ho9 reg7 (by intro h; cases h), h7Val8],
    by rw [ho10 rMeta (by intro h; cases h) (by intro h; cases h), hMeta9]⟩

private theorem csrScatter_pos_setup8 {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hPlSetup : Placed code 0 (csrScatterSetupInstrs (bits := bits) h100))
    (hSz : 28 < code.size)
    (hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ 2 ^ bits)
    (hmPos : 0 < H.arcCount)
    (s0 s10 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hpc10 : s10.pc = 20)
    (hd10 : s10.data = s0.data)
    (h0_10 : (reg s10 reg0).val = 0)
    (h2_10 : (reg s10 reg2).val = H.arcCount)
    (hMeta10 : (reg s10 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next) :
    ∃ s14 : State DomL,
      Steps code input 8 s10 s14 ∧
      s14.pc = 28 ∧
      s14.data = s0.data ∧
      (reg s14 reg8).val = 4 + H.vertexCount + 4 * r.out.tables.next ∧
      (reg s14 reg9).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount ∧
      (reg s14 reg10).val = 0 ∧
      (∀ rf : Fin 15, rf ≠ reg8 → rf ≠ reg9 → rf ≠ reg10 → rf ≠ reg11 → reg s14 rf = reg s10 rf) := by
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlS1 := Placed_append_right (by unfold csrScatterSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
  have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
  have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
  have hPlS5 := Placed_append_right hPlS4
  rw [show ([Instr.add reg7 reg5 reg3, Instr.add reg7 reg7 reg3, Instr.add reg7 reg7 reg3,
    Instr.add reg7 reg7 reg1, Instr.add reg5 reg5 reg3] : List (Instr bits 15)).length = 5 by rfl] at hPlS5
  have hPlS6 := Placed_append_right hPlS5; rw [hLml] at hPlS6
  have hPlBr := Placed_append_left hPlS6
  have hPlS7 := Placed_append_right hPlS6
  rw [show ([Instr.branchLt reg0 reg2 21 47] : List (Instr bits 15)).length = 1 by rfl] at hPlS7
  have hPlQSrc := Placed_append_left hPlS7
  have hPlS8 := Placed_append_right hPlS7; rw [hLml] at hPlS8
  have hPlQHead := Placed_append_left hPlS8
  have hPlMov := Placed_append_right hPlS8; rw [hLml] at hPlMov
  have hMeta48 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ 2 ^ bits := hTempFit
  have hFitQSrc : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxQSrcInBase < 2 ^ bits := by
    dsimp only [mIdxQSrcInBase]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hFitQHead : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxQHeadInBase < 2 ^ bits := by
    dsimp only [mIdxQHeadInBase]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (by decide) _) hMeta48
  have hBr : code[s10.pc]? = some (.branchLt reg0 reg2 21 47) := by rw [hpc10]; exact hPlBr 0 _ rfl
  have hTrue : (reg s10 reg0).val < (reg s10 reg2).val := by rw [h0_10, h2_10]; exact hmPos
  obtain ⟨s11, hs11, hpc11, hreg11, hd11⟩ := step_branchLt_at (input := input) hBr
    (by rw [ite_eq_left hTrue]; exact Nat.lt_trans (by decide) hSz)
  rw [ite_eq_left hTrue] at hpc11
  have hr11 : ∀ rf : Fin 15, reg s11 rf = reg s10 rf := reg_of_regs_eq hreg11
  have hMeta11 : (reg s11 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by rw [hr11, hMeta10]
  have hd11' : s11.data = s0.data := by rw [hd11, hd10]
  obtain ⟨s12, hs12, hpc12, hd12, h8_12, ho12⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlQSrc (Nat.lt_trans (by decide) hSz) hpc11 hMeta11 hFitQSrc
    (by rw [hd11']; exact hMeta.meta_qSrcIn hmPos)
  have hMeta12 : (reg s12 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho12 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta11
  obtain ⟨s13, hs13, hpc13, hd13, h9_13, ho13⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlQHead (Nat.lt_trans (by decide) hSz) hpc12 hMeta12 hFitQHead
    (by rw [hd12, hd11']; exact hMeta.meta_qHeadIn hmPos)
  have hMov : code[s13.pc]? = some (.mov reg10 reg0) := by rw [hpc13]; exact hPlMov 0 _ rfl
  obtain ⟨s14, hs14, hpc14, h10_14, ho14, hd14⟩ := step_mov_at (input := input) hMov
    (by rw [hpc13]; exact hSz)
  refine ⟨s14,
    (steps_1_of_step hs11).append (hs12.append (hs13.append (steps_1_of_step hs14))),
    by rw [hpc14, hpc13],
    by rw [hd14, hd13, hd12, hd11'],
    by rw [ho14 reg8 (by intro h; cases h), ho13 reg8 (by intro h; cases h) (by intro h; cases h), h8_12],
    by rw [ho14 reg9 (by intro h; cases h), h9_13],
    by rw [h10_14, ho13 reg0 (by intro h; cases h) (by intro h; cases h),
      ho12 reg0 (by intro h; cases h) (by intro h; cases h), hr11, h0_10],
    fun rf hr8 hr9 hr10 hr11' => by rw [ho14 rf hr10, ho13 rf hr9 hr11', ho12 rf hr8 hr11', hr11]⟩

private theorem run_csrScatter_aux {code : Program DomL} {input : Input DomL}
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
    (hInPref : ∀ i ≤ H.vertexCount,
      (s0.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i))
    (hOutPref : ∀ i ≤ H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i))
    (hCodeSize : code.size = 62)
    (hPlFull : Placed code 0 (csrScatterInstrs (bits := bits) h100))
    (hHaltAt : ∀ t : State DomL, t.pc = 61 → step code input t = some (.halted t)) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 12 * H.vertexCount + 19 * H.arcCount + 35 ∧
      run code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ i ≤ H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)) ∧
      (∀ i ≤ H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (prefixOut H i)) ∧
      (∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val)]?).map Fin.val =
          some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) ∧
      (∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
        (t.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
          some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))) ∧
      (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
          (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + H.arcCount ≤ j) →
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
  have hTempAddLt : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 < 2 ^ bits := by omega
  have hMetaFrame1 : ∀ i < 22,
      inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) ≤
        metaArrBase H.vertexCount H.arcCount r.out.tables.next + i ∧
      metaArrBase H.vertexCount H.arcCount r.out.tables.next + i <
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    intro i hi22
    refine ⟨?_, ?_⟩
    · rw [← hB2, ← hB1]
      exact Nat.le_trans (Nat.le_add_right _ H.arcCount) (Nat.le_add_right _ i)
    · rw [← hB3]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hi22 _)
        (Nat.le_trans (Nat.add_le_add_left (by decide) _) (Nat.le_add_right _ _))
  have hMetaFrame2 : ∀ i < 22,
      inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount ≤
        metaArrBase H.vertexCount H.arcCount r.out.tables.next + i ∧
      metaArrBase H.vertexCount H.arcCount r.out.tables.next + i <
        tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    intro i hi22
    refine ⟨?_, ?_⟩
    · rw [← hB2]; exact Nat.le_add_right _ i
    · rw [← hB3]
      exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_trans hi22 (by decide)) _) (Nat.le_add_right _ _)
  have hInArcToTemp : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [hB2, ← hB3]
    exact Nat.le_trans (Nat.le_add_right _ 48) (Nat.le_add_right _ H.vertexCount)
  have h2to3 : tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + H.arcCount := by omega
  have h2toOut : tempArrBase H.vertexCount H.arcCount r.out.tables.next + (2 * H.vertexCount + 1) ≤
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 := by omega
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold csrScatterInstrs at hPlFull; exact hPlFull)
  have hPlLoops := Placed_append_right (by unfold csrScatterInstrs at hPlFull; exact hPlFull)
  rw [show (csrScatterSetupInstrs (bits := bits) h100).length = 28 by
    simp [csrScatterSetupInstrs, metaLoadInstrs]] at hPlLoops
  have hPlLoop1 := Placed_append_left hPlLoops
  have hPlLoop2 := Placed_append_right hPlLoops
  rw [show (csrScatterLoop1Instrs (bits := bits)).length = 19 by rfl] at hPlLoop2
  have hPlBr : code[20]? = some (.branchLt reg0 reg2 21 47) := by
    have hPlS1 := Placed_append_right (by unfold csrScatterSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
    have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
    have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
    have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
    have hPlS5 := Placed_append_right hPlS4
    rw [show ([Instr.add reg7 reg5 reg3, Instr.add reg7 reg7 reg3, Instr.add reg7 reg7 reg3,
      Instr.add reg7 reg7 reg1, Instr.add reg5 reg5 reg3] : List (Instr bits 15)).length = 5 by rfl] at hPlS5
    have hPlS6 := Placed_append_right hPlS5; rw [hLml] at hPlS6
    exact (Placed_append_left hPlS6) 0 _ rfl
  obtain ⟨s10, hPrefix20, hpc10, hd10', h0_10, h1_10, h2_10, h3_10, h4_10, h5_10, h6_10, h7_10, hMeta10⟩ :=
    csrScatter_prefix20 h100 hPlSetup (by rw [hCodeSize]; decide) hTempAddLt s0 hMeta
  by_cases hmZero : H.arcCount = 0
  · have hBr : code[s10.pc]? = some (.branchLt reg0 reg2 21 47) := by rw [hpc10]; exact hPlBr
    have hFalse : ¬ ((reg s10 reg0).val < (reg s10 reg2).val) := by rw [h0_10, h2_10, hmZero]; exact Nat.lt_irrefl _
    obtain ⟨s11, hs11, hpc11, hreg11, hd11⟩ := step_branchLt_at (input := input) hBr
      (by rw [ite_eq_right hFalse, hCodeSize]; decide)
    rw [ite_eq_right hFalse] at hpc11
    have hr11 : ∀ rf : Fin 15, reg s11 rf = reg s10 rf := reg_of_regs_eq hreg11
    have hd11' : s11.data = s0.data := by rw [hd11, hd10']
    have hPrefIn0 : ∀ x, prefixIn H x = 0 := by
      intro x; induction x with
      | zero => rfl
      | succ x ihx =>
        have hdz : degIn H x = 0 := by unfold degIn; rw [hmZero]; rfl
        change prefixIn H x + degIn H x = 0; rw [ihx, hdz]
    have hPrefOut0 : ∀ x, prefixOut H x = 0 := by
      intro x; induction x with
      | zero => rfl
      | succ x ihx =>
        have hdz : degOut H x = 0 := by unfold degOut; rw [hmZero]; rfl
        change prefixOut H x + degOut H x = 0; rw [ihx, hdz]
    obtain ⟨k2, t, hk2, hSteps2, hpcT, h0T, h1T, hMetaT, hInRes, hOutRes, hFr2⟩ :=
      csrScatterLoop2_spec (H := H) (r := r) hWork hPlLoop2 (by rw [hCodeSize]; decide)
        H.vertexCount (Nat.le_refl _) s11 hpc11
        (by rw [hr11, h0_10]) (by rw [hr11, h1_10]) (by rw [hr11, hMeta10])
        (by rw [hr11, h3_10]) (by rw [hr11, h4_10]) (by rw [hr11, h5_10])
        (fun j hj => by
          rw [hd11', hPrefIn0 (j + 1)]
          have hEq := hInPref j (Nat.le_of_lt hj)
          rw [hPrefIn0 j] at hEq
          exact hEq)
        (fun _ hnj hLt => False.elim (Nat.not_lt.mpr hLt hnj))
        (fun j hj => by
          rw [hd11', hPrefOut0 (j + 1)]
          have hEq := hOutPref j (Nat.le_of_lt hj)
          rw [hPrefOut0 j] at hEq
          exact hEq)
        (fun _ hnj hLt => False.elim (Nat.not_lt.mpr hLt hnj))
    have hAllSteps : Steps code input (21 + k2) (Phase.initial s0) t :=
      (hPrefix20.append (steps_1_of_step hs11)).append hSteps2
    have hDegOut0 : ∀ u, degOut H u = 0 := fun u => by unfold degOut; rw [hmZero]; rfl
    have hDegIn0 : ∀ v, degIn H v = 0 := fun v => by unfold degIn; rw [hmZero]; rfl
    refine ⟨21 + k2 + 1, t, csrScatter_step_bound0 hk2, hAllSteps.halts (hHaltAt t hpcT),
      ?_, hInRes, hOutRes,
      fun u _ j => False.elim (Nat.not_lt_zero j.val (hDegOut0 u ▸ j.isLt)),
      fun v _ j => False.elim (Nat.not_lt_zero j.val (hDegIn0 v ▸ j.isLt)),
      fun j hj => ?_⟩
    · apply hMeta.preserve hMetaT h0T h1T
      intro i hi22
      rw [hFr2 (metaArrBase H.vertexCount H.arcCount r.out.tables.next + i)
        (Or.inr (Or.inl (hMetaFrame1 i hi22))), hd11']
    · rw [hFr2 j (by
        rcases hj with h | ⟨h1, h2⟩ | ⟨h1, _⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Nat.le_trans (hB1 ▸ Nat.le_add_right _ _) h1, h2⟩)
        · exact Or.inr (Or.inr (by rw [← Nat.add_assoc]; exact h1))
        · exact Or.inr (Or.inr (Nat.le_trans h2to3 h))), hd11']
  · have hmPos : 0 < H.arcCount := Nat.pos_of_ne_zero hmZero
    obtain ⟨s14, hSetup8, hpc14, hd14', h8_14, h9_14, h10_14, hKeep14⟩ :=
      csrScatter_pos_setup8 h100 hPlSetup (by rw [hCodeSize]; decide) hTempFit hmPos s0 s10 hMeta
        hpc10 hd10' h0_10 h2_10 hMeta10
    obtain ⟨k1, s15, hk1, hSteps1, hpc15, h0_15, h1_15, hMeta15, hN15, hInS15, hOutS15,
      hOut15, hOutN15, hIn15, hInN15, hOutSl15, hInSl15, hFr15⟩ :=
      csrScatterLoop1_spec hIn hWork hPlLoop1 (by rw [hCodeSize]; decide) 0 (Nat.zero_le _) s14 hpc14
        (by rw [hKeep14 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_10])
        (by rw [hKeep14 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_10])
        (by rw [hKeep14 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta10])
        (by rw [hKeep14 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2_10])
        (by rw [hKeep14 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3_10])
        (by rw [hKeep14 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4_10])
        (by rw [hKeep14 reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h5_10])
        (by rw [hKeep14 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6_10])
        (by rw [hKeep14 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7_10])
        h8_14 h9_14 h10_14
        (fun u hu => by
          change (s14.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + u]?).map Fin.val = some (prefixOut H u)
          rw [hd14']; exact hOutPref u (Nat.le_of_lt hu))
        (by
          change (s14.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount]?).map Fin.val = some H.arcCount
          have hTot := hOutPref H.vertexCount (Nat.le_refl _)
          rw [Nat.add_assoc, ← Nat.two_mul, prefixOut_vertexCount H] at hTot
          rw [hd14']; exact hTot)
        (fun v hv => by
          change (s14.data[inStartArrBase H.vertexCount r.out.tables.next + v]?).map Fin.val = some (prefixIn H v)
          rw [hd14']; exact hInPref v (Nat.le_of_lt hv))
        (by
          change (s14.data[inStartArrBase H.vertexCount r.out.tables.next + H.vertexCount]?).map Fin.val = some H.arcCount
          rw [hd14', ← prefixIn_vertexCount H]; exact hInPref H.vertexCount (Nat.le_refl _))
        (fun u hu j => False.elim (Nat.not_lt_zero _ j.isLt))
        (fun v hv j => False.elim (Nat.not_lt_zero _ j.isLt))
    obtain ⟨k2, t, hk2, hSteps2, hpcT, h0T, h1T, hMetaT, hInRes, hOutRes, hFr2⟩ :=
      csrScatterLoop2_spec (H := H) (r := r) hWork hPlLoop2 (by rw [hCodeSize]; decide)
        H.vertexCount (Nat.le_refl _) s15 hpc15
        h0_15 h1_15 hMeta15 hN15 hInS15 hOutS15
        hIn15 (fun _ hnj hLt => False.elim (Nat.not_lt.mpr hLt hnj))
        hOut15 (fun _ hnj hLt => False.elim (Nat.not_lt.mpr hLt hnj))
    have hSetup14 : Steps code input 28 (Phase.initial s0) s14 :=
      hPrefix20.append hSetup8
    refine ⟨(28 + k1) + k2 + 1, t, csrScatter_step_bound1 hk1 hk2,
      ((hSetup14.append hSteps1).append hSteps2).halts (hHaltAt t hpcT), ?_,
      hInRes, hOutRes, fun u hu j => ?_, fun v hv j => ?_, fun j hj => ?_⟩
    · apply hMeta.preserve hMetaT h0T h1T
      intro i hi22
      rw [hFr2 (metaArrBase H.vertexCount H.arcCount r.out.tables.next + i)
          (Or.inr (Or.inl (hMetaFrame1 i hi22))),
        hFr15 (metaArrBase H.vertexCount H.arcCount r.out.tables.next + i)
          (Or.inr (Or.inl (hMetaFrame2 i hi22))),
        hd14']
    · rw [hFr2 (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val))
        (Or.inr (Or.inr (Nat.le_trans h2toOut (Nat.le_add_right _ _))))]
      exact hOutSl15 u hu j
    · have hSumLt : prefixIn H v + j.val < H.arcCount :=
        Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt _) ((prefixIn_vertexCount H) ▸ (prefixIn_mono H hv))
      rw [hFr2 (inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val))
        (Or.inr (Or.inl ⟨hB1 ▸ Nat.le_add_right _ _,
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left hSumLt _) hInArcToTemp⟩))]
      exact hInSl15 v hv j
    · rw [hFr2 j (by
        rcases hj with h | ⟨h1, h2⟩ | ⟨h1, _⟩ | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨Nat.le_trans (hB1 ▸ Nat.le_add_right _ _) h1, h2⟩)
        · exact Or.inr (Or.inr (by rw [← Nat.add_assoc]; exact h1))
        · exact Or.inr (Or.inr (Nat.le_trans h2to3 h)))]
      rw [hFr15 j hj, hd14']

theorem run_csrScatter {input : Input DomL}
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
    (hInPref : ∀ i ≤ H.vertexCount,
      (s0.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i))
    (hOutPref : ∀ i ≤ H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i)) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 12 * H.vertexCount + 19 * H.arcCount + 35 ∧
      run (csrScatterPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ i ≤ H.vertexCount,
        (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)) ∧
      (∀ i ≤ H.vertexCount,
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (prefixOut H i)) ∧
      (∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + (prefixOut H u + j.val)]?).map Fin.val =
          some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) ∧
      (∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
        (t.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
          some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))) ∧
      (∀ j, (j < inStartArrBase H.vertexCount r.out.tables.next ∨
          (inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount) ∨
          (tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 + H.arcCount ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  have hCodeLen : (csrScatterInstrs (bits := bits) h100).length = 61 := by
    simp [csrScatterInstrs, csrScatterSetupInstrs, csrScatterLoop1Instrs, csrScatterLoop2Instrs, metaLoadInstrs]
  exact run_csrScatter_aux h100 hIn hWork s0 hMeta hInPref hOutPref
    (by dsimp [csrScatterPhase]; rw [codeSize_mkHaltPhase, hCodeLen])
    (Placed_mkHaltPhase _ _)
    (fun t hpc => haltAt_mkHaltPhase (hi := hi) (hw := hw) (csrScatterInstrs (bits := bits) h100) _
      (by rw [hpc, hCodeLen]) (input := input))

end CsrScatterPhase


end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
