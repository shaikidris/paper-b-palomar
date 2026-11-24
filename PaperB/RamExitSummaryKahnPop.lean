module

public import PaperB.RamExitSummaryKahnInner

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 2000000

/-!
Queue pop and the two order-column writes in the word-RAM Kahn traversal.
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

section KahnLoopPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw


theorem kahn_order_end_le_temp (n m N : Nat) :
    orderArrBase n N + n ≤ tempArrBase n m N := by
  rw [show tempArrBase n m N = metaArrBase n m N + 48 from rfl, metaArrBase_eq]
  unfold orderArrBase
  omega

theorem kahn_rank_end_le_temp (n m N : Nat) :
    topoRankArrBase n N + n ≤ tempArrBase n m N := by
  rw [show tempArrBase n m N = metaArrBase n m N + 48 from rfl, metaArrBase_eq]
  unfold topoRankArrBase orderArrBase
  omega

/-- Pop a queue entry, write its two order columns and load its arc bounds. -/
theorem kahn_pop_prefix {code : Program DomL} {input : Input DomL} (H : LabelledQuotient)
    (N : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hTempFit : tempArrBase H.vertexCount H.arcCount N +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap)
    (hPlOuter : Placed code 20 (kahnLoopOuterInstrs (bits := bits) h100))
    (hSz : 51 < code.size)
    (st : State DomL) (k qLen u : Nat) (hkLtQ : k < qLen)
    (hqLenLe : qLen ≤ H.vertexCount) (huLt : u < H.vertexCount)
    (hpc : st.pc = 20) (h1 : (reg st reg1).val = 1)
    (hMeta : (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount N)
    (h2 : (reg st reg2).val = k) (h3 : (reg st reg3).val = qLen)
    (h4 : (reg st reg4).val = orderArrBase H.vertexCount N)
    (h7 : (reg st reg7).val = tempArrBase H.vertexCount H.arcCount N + H.vertexCount)
    (h9 : (reg st reg9).val = tempArrBase H.vertexCount H.arcCount N + 2 * H.vertexCount + 1)
    (hMetaTR : (st.data[metaArrBase H.vertexCount H.arcCount N + mIdxTopoRankBase]?).map Fin.val =
      some (topoRankArrBase H.vertexCount N))
    (hQAt : (st.data[tempArrBase H.vertexCount H.arcCount N + 2 * H.vertexCount + 1 + k]?).map Fin.val =
      some u)
    (hOutPref : ∀ i ≤ H.vertexCount,
      (st.data[tempArrBase H.vertexCount H.arcCount N + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i)) :
    ∃ s : State DomL, Steps code input 15 st s ∧ s.pc = 35 ∧
      (reg s reg2).val = k + 1 ∧
      (reg s reg11).val = prefixOut H u ∧ (reg s reg12).val = prefixOut H u + degOut H u ∧
      (∀ j : Fin 15, j ≠ reg2 → j ≠ reg11 → j ≠ reg12 → j ≠ reg13 → reg s j = reg st j) ∧
      (s.data[orderArrBase H.vertexCount N + k]?).map Fin.val = some u ∧
      (s.data[topoRankArrBase H.vertexCount N + u]?).map Fin.val = some k ∧
      (∀ a, orderArrBase H.vertexCount N + k ≠ a → topoRankArrBase H.vertexCount N + u ≠ a →
        s.data[a]? = st.data[a]?) := by
  have hOrdBound := kahn_order_end_le_temp H.vertexCount H.arcCount N
  have hTRBound := kahn_rank_end_le_temp H.vertexCount H.arcCount N
  obtain ⟨s1, hs1, hpc1, hrt1, hd1⟩ := step_branchLt_at (input := input)
    (by rw [hpc]; exact hPlOuter 0 _ rfl) (by split <;> omega)
  rw [ite_eq_left (by rw [h2, h3]; exact hkLtQ)] at hpc1
  have hr1 := reg_of_regs_eq hrt1
  have ha1 : code[s1.pc]? = some (.add reg11 reg9 reg2) := by rw [hpc1]; exact hPlOuter 1 _ rfl
  have hFitQ : (reg s1 reg9).val + (reg s1 reg2).val < 2 ^ bits := by
    rw [hr1, hr1, h9, h2]; omega
  obtain ⟨s2, hs2, hpc2, h11_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by omega)
  have hQAddr : (reg s2 reg11).val =
      tempArrBase H.vertexCount H.arcCount N + 2 * H.vertexCount + 1 + k := by
    rw [h11_2, add_no_wrap _ _ hFitQ, hr1, hr1, h9, h2]
  obtain ⟨wU, hwU, hwUV⟩ := Option.map_eq_some_iff.mp hQAt
  have hMemU : s2.data[(reg s2 reg11).val]? = some wU := by rw [hQAddr, hd2, hd1]; exact hwU
  have hl1 : code[s2.pc]? = some (.loadData reg11 reg11) := by rw [hpc2, hpc1]; exact hPlOuter 2 _ rfl
  obtain ⟨s3, hs3, hpc3, h11_3, ho3, hd3⟩ := step_loadData_at (input := input) hl1 (by omega) hMemU
  have hUVal : (reg s3 reg11).val = u := by rw [h11_3, hwUV]
  have h4_3 : (reg s3 reg4).val = orderArrBase H.vertexCount N := by
    rw [ho3 reg4 (by intro h; cases h), ho2 reg4 (by intro h; cases h), hr1, h4]
  have h2_3 : (reg s3 reg2).val = k := by
    rw [ho3 reg2 (by intro h; cases h), ho2 reg2 (by intro h; cases h), hr1, h2]
  have ha2 : code[s3.pc]? = some (.add reg12 reg4 reg2) := by rw [hpc3, hpc2, hpc1]; exact hPlOuter 3 _ rfl
  have hFitOrd : (reg s3 reg4).val + (reg s3 reg2).val < 2 ^ bits := by
    rw [h4_3, h2_3]; omega
  obtain ⟨s4, hs4, hpc4, h12_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by omega)
  have hOrdAddr : (reg s4 reg12).val = orderArrBase H.vertexCount N + k := by
    rw [h12_4, add_no_wrap _ _ hFitOrd, h4_3, h2_3]
  have hLtOrd4 : (reg s4 reg12).val < s4.data.size := lt_data_size (by rw [hOrdAddr]; omega)
  have hst1 : code[s4.pc]? = some (.storeData reg12 reg11) := by
    rw [hpc4, hpc3, hpc2, hpc1]; exact hPlOuter 4 _ rfl
  obtain ⟨s5, hs5, hpc5, hreg5, hd5⟩ := step_storeData_opaque (input := input) hst1 hLtOrd4 (by omega)
  have hr5 := reg_of_regs_eq hreg5
  have hd4' : s4.data = st.data := by rw [hd4, hd3, hd2, hd1]
  have hLtOrd4St : (reg s4 reg12).val < st.data.size := by rw [← hd4']; exact hLtOrd4
  have hs5Data : s5.data = st.data.set (reg s4 reg12).val (reg s4 reg11) hLtOrd4St := by
    rw [hd5]; exact array_set_eq_of_data_eq hd4' hLtOrd4 hLtOrd4St
  have hPres5 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s5 r = reg st r := fun r hr11 hr12 => by
    rw [hr5, ho4 r hr12, ho3 r hr11, ho2 r hr11, hr1]
  have h11_5 : (reg s5 reg11).val = u := by
    rw [hr5, ho4 reg11 (by intro h; cases h), hUVal]
  have hM_5 : (reg s5 rMeta).val = metaArrBase H.vertexCount H.arcCount N := by
    rw [hPres5 rMeta (by intro h; cases h) (by intro h; cases h), hMeta]
  have hPlTRTail := Placed_append_right (by unfold kahnLoopOuterInstrs at hPlOuter; exact hPlOuter)
  rw [show ([Instr.branchLt reg2 reg3 21 51, Instr.add reg11 reg9 reg2,
    Instr.loadData reg11 reg11, Instr.add reg12 reg4 reg2,
    Instr.storeData reg12 reg11] : List (Instr bits 15)).length = 5 by rfl] at hPlTRTail
  have hPlMetaTR : Placed code 25
      (metaLoadInstrs (bits := bits) reg12 reg13 mIdxTopoRankBase (by dsimp only [mIdxTopoRankBase]; omega)) :=
    Placed_append_left hPlTRTail
  have hPlPostTR := Placed_append_right hPlTRTail
  rw [show (metaLoadInstrs (bits := bits) reg12 reg13 mIdxTopoRankBase (by dsimp only [mIdxTopoRankBase]; omega)).length = 3 by rfl] at hPlPostTR
  have hNeMetaOrd : metaArrBase H.vertexCount H.arcCount N + mIdxTopoRankBase ≠
      (reg s4 reg12).val := by
    rw [hOrdAddr]; unfold metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase
      trigHeadArrBase topoRankArrBase
    omega
  have hMemTR5 : (s5.data[metaArrBase H.vertexCount H.arcCount N + mIdxTopoRankBase]?).map Fin.val =
      some (topoRankArrBase H.vertexCount N) := by
    rw [hs5Data, Array.getElem?_set_ne hLtOrd4St hNeMetaOrd.symm]
    exact hMetaTR
  obtain ⟨s6, hs6, hpc6, hd6, h12_6, ho6⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlMetaTR (by omega) (by rw [hpc5, hpc4, hpc3, hpc2, hpc1]) hM_5 (by
      unfold tempArrBase at hTempFit
      dsimp only [mIdxTopoRankBase]
      omega) hMemTR5
  have h11_6 : (reg s6 reg11).val = u := by rw [ho6 reg11 (by intro h; cases h) (by intro h; cases h), h11_5]
  have hFitTR : (reg s6 reg12).val + (reg s6 reg11).val < 2 ^ bits := by rw [h12_6, h11_6]; omega
  have ha3 : code[s6.pc]? = some (.add reg12 reg12 reg11) := by rw [hpc6]; exact hPlPostTR 0 _ rfl
  obtain ⟨s7, hs7, hpc7, h12_7, ho7, hd7⟩ := step_add_at (input := input) ha3 (by omega)
  have hTRAddr : (reg s7 reg12).val = topoRankArrBase H.vertexCount N + u := by
    rw [h12_7, add_no_wrap _ _ hFitTR, h12_6, h11_6]
  have hLtTR7 : (reg s7 reg12).val < s7.data.size := lt_data_size (by rw [hTRAddr]; omega)
  have hst2 : code[s7.pc]? = some (.storeData reg12 reg2) := by
    rw [hpc7, hpc6]; exact hPlPostTR 1 _ rfl
  obtain ⟨s8, hs8, hpc8, hreg8, hd8⟩ := step_storeData_opaque (input := input) hst2 hLtTR7 (by omega)
  have hr8 := reg_of_regs_eq hreg8
  have hPres8 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → r ≠ reg13 → reg s8 r = reg st r :=
    fun r hr11 hr12 hr13 => by rw [hr8, ho7 r hr12, ho6 r hr12 hr13, hPres5 r hr11 hr12]
  have h7_8 : (reg s8 reg7).val =
      tempArrBase H.vertexCount H.arcCount N + H.vertexCount := by
    rw [hPres8 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7]
  have h11_8 : (reg s8 reg11).val = u := by
    rw [hr8, ho7 reg11 (by intro h; cases h), h11_6]
  have hFitOS1 : (reg s8 reg7).val + (reg s8 reg11).val < 2 ^ bits := by
    rw [h7_8, h11_8]; omega
  have ha4 : code[s8.pc]? = some (.add reg12 reg7 reg11) := by
    rw [hpc8, hpc7, hpc6]; exact hPlPostTR 2 _ rfl
  obtain ⟨s9, hs9, hpc9, h12_9, ho9, hd9⟩ := step_add_at (input := input) ha4 (by omega)
  have hOSAddr : (reg s9 reg12).val =
      tempArrBase H.vertexCount H.arcCount N + H.vertexCount + u := by
    rw [h12_9, add_no_wrap _ _ hFitOS1, h7_8, h11_8]
  have hd7' : s7.data = s5.data := by rw [hd7, hd6]
  have hLtTR7S5 : (reg s7 reg12).val < s5.data.size := by rw [← hd7']; exact hLtTR7
  have hs9Data : s9.data = s5.data.set (reg s7 reg12).val (reg s7 reg2) hLtTR7S5 := by
    rw [hd9, hd8]; exact array_set_eq_of_data_eq hd7' hLtTR7 hLtTR7S5
  have hNeOS1 : tempArrBase H.vertexCount H.arcCount N + H.vertexCount + u ≠
      (reg s7 reg12).val := by rw [hTRAddr]; omega
  have hNeOS2 : tempArrBase H.vertexCount H.arcCount N + H.vertexCount + u ≠
      (reg s4 reg12).val := by rw [hOrdAddr]; omega
  have hMemP0 : (s9.data[tempArrBase H.vertexCount H.arcCount N + H.vertexCount + u]?).map Fin.val =
      some (prefixOut H u) := by
    rw [hs9Data, Array.getElem?_set_ne hLtTR7S5 hNeOS1.symm, hs5Data,
      Array.getElem?_set_ne hLtOrd4St hNeOS2.symm]
    exact hOutPref u (Nat.le_of_lt huLt)
  obtain ⟨wP0, hwP0, hwP0V⟩ := Option.map_eq_some_iff.mp hMemP0
  have hl2 : code[s9.pc]? = some (.loadData reg11 reg12) := by
    rw [hpc9, hpc8, hpc7, hpc6]; exact hPlPostTR 3 _ rfl
  obtain ⟨s10, hs10, hpc10, h11_10, ho10, hd10⟩ := step_loadData_at (input := input) hl2 (by omega)
    (by rw [hOSAddr]; exact hwP0)
  have hP0Val : (reg s10 reg11).val = prefixOut H u := by rw [h11_10, hwP0V]
  have h12_10 : (reg s10 reg12).val =
      tempArrBase H.vertexCount H.arcCount N + H.vertexCount + u := by
    rw [ho10 reg12 (by intro h; cases h), hOSAddr]
  have h1_10 : (reg s10 reg1).val = 1 := by
    rw [ho10 reg1 (by intro h; cases h), ho9 reg1 (by intro h; cases h),
      hPres8 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1]
  have hFitOS2 : (reg s10 reg12).val + (reg s10 reg1).val < 2 ^ bits := by
    rw [h12_10, h1_10]; omega
  have ha5 : code[s10.pc]? = some (.add reg12 reg12 reg1) := by
    rw [hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPlPostTR 4 _ rfl
  obtain ⟨s11, hs11, hpc11, h12_11, ho11, hd11⟩ := step_add_at (input := input) ha5 (by omega)
  have hOSAddr1 : (reg s11 reg12).val =
      tempArrBase H.vertexCount H.arcCount N + H.vertexCount + (u + 1) := by
    rw [h12_11, add_no_wrap _ _ hFitOS2, h12_10, h1_10]; omega
  have hNeOS1b : tempArrBase H.vertexCount H.arcCount N + H.vertexCount + (u + 1) ≠
      (reg s7 reg12).val := by rw [hTRAddr]; omega
  have hNeOS2b : tempArrBase H.vertexCount H.arcCount N + H.vertexCount + (u + 1) ≠
      (reg s4 reg12).val := by rw [hOrdAddr]; omega
  have hMemP1 : (s11.data[tempArrBase H.vertexCount H.arcCount N + H.vertexCount + (u + 1)]?).map Fin.val =
      some (prefixOut H (u + 1)) := by
    rw [hd11, hd10, hs9Data, Array.getElem?_set_ne hLtTR7S5 hNeOS1b.symm, hs5Data,
      Array.getElem?_set_ne hLtOrd4St hNeOS2b.symm]
    exact hOutPref (u + 1) huLt
  obtain ⟨wP1, hwP1, hwP1V⟩ := Option.map_eq_some_iff.mp hMemP1
  have hl3 : code[s11.pc]? = some (.loadData reg12 reg12) := by
    rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPlPostTR 5 _ rfl
  obtain ⟨s12, hs12, hpc12, h12_12, ho12, hd12⟩ := step_loadData_at (input := input) hl3 (by omega)
    (by rw [hOSAddr1]; exact hwP1)
  have hP1Val : (reg s12 reg12).val = prefixOut H u + degOut H u := by
    rw [h12_12, hwP1V]; rfl
  have h2_12 : (reg s12 reg2).val = k := by
    rw [ho12 reg2 (by intro h; cases h), ho11 reg2 (by intro h; cases h), ho10 reg2 (by intro h; cases h),
      ho9 reg2 (by intro h; cases h), hPres8 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2]
  have h1_12 : (reg s12 reg1).val = 1 := by
    rw [ho12 reg1 (by intro h; cases h), ho11 reg1 (by intro h; cases h), h1_10]
  have hFitK : (reg s12 reg2).val + (reg s12 reg1).val < 2 ^ bits := by rw [h2_12, h1_12]; omega
  have ha6 : code[s12.pc]? = some (.add reg2 reg2 reg1) := by
    rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]; exact hPlPostTR 6 _ rfl
  obtain ⟨s13, hs13, hpc13, h2_13, ho13, hd13⟩ := step_add_at (input := input) ha6 (by omega)
  have hPres13 : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg11 → r ≠ reg12 → r ≠ reg13 → reg s13 r = reg st r :=
    fun r hr2 hr11 hr12 hr13 => by
      rw [ho13 r hr2, ho12 r hr12, ho11 r hr12, ho10 r hr11, ho9 r hr12, hPres8 r hr11 hr12 hr13]
  have hData13Eq : s13.data = s9.data := by rw [hd13, hd12, hd11, hd10]
  have hStep15 : Steps code input 15 st s13 := by
    have h5 : Steps code input 5 st s5 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5))))
    have h8 : Steps code input 8 st s6 := h5.append hs6
    exact h8.append (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
      (Steps.cons hs11 (Steps.cons hs12 (steps_1_of_step hs13)))))))
  have hS13At : ∀ a,
      orderArrBase H.vertexCount N + k ≠ a →
      topoRankArrBase H.vertexCount N + u ≠ a →
      s13.data[a]? = st.data[a]? := fun a haOrd haTR => by
    rw [hData13Eq, hs9Data, Array.getElem?_set_ne hLtTR7S5 (by rw [hTRAddr]; exact haTR),
      hs5Data, Array.getElem?_set_ne hLtOrd4St (by rw [hOrdAddr]; exact haOrd)]
  have hOrdBeforeRank : orderArrBase H.vertexCount N + k < topoRankArrBase H.vertexCount N + u :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hkLtQ hqLenLe) _)
      (show orderArrBase H.vertexCount N + H.vertexCount ≤ topoRankArrBase H.vertexCount N + u
        from Nat.le_add_right _ _)
  refine ⟨s13, hStep15, ?_, ?_, ?_, ?_, hPres13, ?_, ?_, hS13At⟩
  · rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6]
  · rw [h2_13, add_no_wrap _ _ hFitK, h2_12, h1_12]
  · rw [ho13 reg11 (by intro h; cases h), ho12 reg11 (by intro h; cases h),
      ho11 reg11 (by intro h; cases h), hP0Val]
  · rw [ho13 reg12 (by intro h; cases h), hP1Val]
  · rw [hData13Eq, hs9Data,
      Array.getElem?_set_ne hLtTR7S5 (by
        rw [hTRAddr]; exact Nat.ne_of_gt hOrdBeforeRank),
      hs5Data, ← hOrdAddr, Array.getElem?_set_self, Option.map_some,
      ho4 reg11 (by intro h; cases h), hUVal]
  · rw [hData13Eq, hs9Data, ← hTRAddr, Array.getElem?_set_self, Option.map_some,
      ho7 reg2 (by intro h; cases h), ho6 reg2 (by intro h; cases h) (by intro h; cases h),
      hPres5 reg2 (by intro h; cases h) (by intro h; cases h), h2]

end KahnLoopPhase
end Stage2CsrKahn
end PaperB.RamProgram.ExitSummaryBuild
