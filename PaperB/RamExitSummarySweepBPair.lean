module

public import PaperB.RamExitSummarySweepBParentHeader

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

def step4B_decodePairInstrs (src : Fin 15) (off0 off1 : Nat)
    (h0 : off0 < 2 ^ bits) (h1 : off1 < 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg7 mIdxBackFstInBase (Nat.lt_of_lt_of_le (by decide) h100) ++
  [.add reg6 reg6 src, .loadInput reg6 reg6, .sub reg6 reg6 reg1] ++
  metaStoreInstrs reg6 reg7 off0 h0 ++
  metaLoadInstrs reg6 reg7 mIdxBackSndInBase (Nat.lt_of_lt_of_le (by decide) h100) ++
  [.add reg6 reg6 src, .loadInput reg6 reg6] ++
  metaStoreInstrs reg6 reg7 off1 h1

theorem step4B_decodePair_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (src : Fin 15) (off0 off1 : Nat)
    (hSrc6 : src ≠ reg6) (hSrc7 : src ≠ reg7)
    (hOff0 : off0 < 64) (hOff1 : off1 < 64) (hNeOff : off0 ≠ off1)
    (hNeBase : mIdxBackSndInBase ≠ off0)
    (hPl : Placed code basePc (step4B_decodePairInstrs src off0 off1 (by omega) (by omega) h100))
    (hSz : basePc + 17 < code.size)
    (n N metaBase slot a b : Nat)
    (hBoundMeta : metaBase + 64 ≤ workCap)
    (hFitFst : 4 + n + slot < 2 ^ bits) (hFitSnd : 4 + n + N + slot < 2 ^ bits)
    (st : State DomL) (hpc14 : st.pc = basePc)
    (hMeta : (reg st rMeta).val = metaBase)
    (hOne : (reg st reg1).val = 1)
    (hSource : (reg st src).val = slot)
    (hBaseFst : (st.data[metaBase + mIdxBackFstInBase]?).map Fin.val = some (4 + n))
    (hBaseSnd : (st.data[metaBase + mIdxBackSndInBase]?).map Fin.val = some (4 + n + N))
    (hBackFst : (input.words[4 + n + slot]?).map Fin.val = some (1 + a))
    (hBackSnd : (input.words[4 + n + N + slot]?).map Fin.val = some b) :
    ∃ t, Steps code input 17 st t ∧ t.pc = basePc + 17 ∧
      (t.data[metaBase + off0]?).map Fin.val = some a ∧
      (t.data[metaBase + off1]?).map Fin.val = some b ∧
      (∀ j, j ≠ metaBase + off0 → j ≠ metaBase + off1 → t.data[j]? = st.data[j]?) ∧
      (∀ rr, rr ≠ reg6 → rr ≠ reg7 → reg t rr = reg st rr) := by
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hOffsetFit (off : Nat) (hoff : off < 64) : metaBase + off < 2 ^ bits := by omega
  have hPlBF1 : Placed code (basePc) (metaLoadInstrs (bits := bits) reg6 reg7 mIdxBackFstInBase (by dsimp only [mIdxBackFstInBase]; omega)) :=
    Placed_window hPl 0 rfl
  obtain ⟨s15, hs15, hpc15, hd15, h6_15, hPres15⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlBF1 (by omega) hpc14 hMeta (hOffsetFit mIdxBackFstInBase (by decide))
    hBaseFst
  change (reg s15 reg6).val = 4 + n at h6_15
  have h2_15 : (reg s15 src).val = slot := by rw [hPres15 src hSrc6 hSrc7, hSource]
  have haA27 : code[s15.pc]? = some (.add reg6 reg6 src) := by rw [hpc15]; exact hPl 3 _ rfl
  obtain ⟨s16, hs16Raw, hpc16, h6_16, ho16, hd16⟩ := step_add_at (input := input) haA27 (by omega)
  have hs16 := steps_1_of_step hs16Raw
  have h6Val16 : (reg s16 reg6).val = 4 + n + slot := by rw [h6_16, add_no_wrap _ _ (by rw [h6_15, h2_15]; omega), h6_15, h2_15]
  obtain ⟨wbfW, hwbfW, hwbfWV⟩ := Option.map_eq_some_iff.mp hBackFst
  have haL28 : code[s16.pc]? = some (.loadInput reg6 reg6) := by rw [hpc16, hpc15]; exact hPl 4 _ rfl
  obtain ⟨s17, hs17Raw, hpc17, h6_17, ho17, hd17⟩ := step_loadInput_at (input := input) haL28 (by omega)
    (by rw [h6Val16]; exact hwbfW)
  have hs17 := steps_1_of_step hs17Raw
  have h1_17 : (reg s17 reg1).val = 1 := by
    rw [ho17 reg1 (by intro h; cases h), ho16 reg1 (by intro h; cases h),
      hPres15 reg1 (by intro h; cases h) (by intro h; cases h), hOne]
  have h6Val17 : (reg s17 reg6).val = 1 + a := by rw [h6_17, hwbfWV]
  have haS29 : code[s17.pc]? = some (.sub reg6 reg6 reg1) := by rw [hpc17, hpc16, hpc15]; exact hPl 5 _ rfl
  obtain ⟨s18, hs18Raw, hpc18, h6_18, ho18, hd18⟩ := step_sub_at (input := input) haS29 (by omega)
  have hs18 := steps_1_of_step hs18Raw
  have haVal18 : (reg s18 reg6).val = a := by
    rw [h6_18, sub_exact (by rw [h6Val17, h1_17]; omega), h6Val17, h1_17]; omega
  have hM_18 : (reg s18 rMeta).val = metaBase := by
    rw [ho18 rMeta (by intro h; cases h), ho17 rMeta (by intro h; cases h),
      ho16 rMeta (by intro h; cases h), hPres15 rMeta (by intro h; cases h) (by intro h; cases h), hMeta]
  have hPlS50 : Placed code (basePc + 6) (metaStoreInstrs (bits := bits) reg6 reg7 off0 (by omega)) :=
    Placed_window hPl 6 rfl
  obtain ⟨s19, hs19, hpc19, hAt19, hFr19, hPres19⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS50 (by omega) (by rw [hpc18, hpc17, hpc16, hpc15]) hM_18 (by omega)
    (lt_data_size (by omega))
  have hM_19 : (reg s19 rMeta).val = metaBase := by rw [hPres19 rMeta (by intro h; cases h), hM_18]
  have h2_19 : (reg s19 src).val = slot := by
    rw [hPres19 src hSrc7, ho18 src hSrc6,
      ho17 src hSrc6, ho16 src hSrc6, h2_15]
  have hPlBS1 : Placed code (basePc + 9) (metaLoadInstrs (bits := bits) reg6 reg7 mIdxBackSndInBase (by dsimp only [mIdxBackSndInBase]; omega)) :=
    Placed_window hPl 9 rfl
  obtain ⟨s20, hs20, hpc20, hd20, h6_20, hPres20⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlBS1 (by omega) hpc19 hM_19 (hOffsetFit mIdxBackSndInBase (by decide))
    (by rw [hFr19 (metaBase + mIdxBackSndInBase) (fun he => hNeBase (Nat.add_left_cancel he)),
      hd18, hd17, hd16, hd15]; exact hBaseSnd)
  change (reg s20 reg6).val = 4 + n + N at h6_20
  have h2_20 : (reg s20 src).val = slot := by rw [hPres20 src hSrc6 hSrc7, h2_19]
  have haA36 : code[s20.pc]? = some (.add reg6 reg6 src) := by rw [hpc20]; exact hPl 12 _ rfl
  obtain ⟨s21, hs21Raw, hpc21, h6_21, ho21, hd21⟩ := step_add_at (input := input) haA36 (by omega)
  have hs21 := steps_1_of_step hs21Raw
  have h6Val21 : (reg s21 reg6).val = 4 + n + N + slot := by rw [h6_21, add_no_wrap _ _ (by rw [h6_20, h2_20]; omega), h6_20, h2_20]
  obtain ⟨wbsW, hwbsW, hwbsWV⟩ := Option.map_eq_some_iff.mp hBackSnd
  have haL37 : code[s21.pc]? = some (.loadInput reg6 reg6) := by rw [hpc21, hpc20]; exact hPl 13 _ rfl
  obtain ⟨s22, hs22Raw, hpc22, h6_22, ho22, hd22⟩ := step_loadInput_at (input := input) haL37 (by omega)
    (by rw [h6Val21]; exact hwbsW)
  have hs22 := steps_1_of_step hs22Raw
  have hbVal22 : (reg s22 reg6).val = b := by rw [h6_22, hwbsWV]
  have hM_22 : (reg s22 rMeta).val = metaBase := by
    rw [ho22 rMeta (by intro h; cases h), ho21 rMeta (by intro h; cases h),
      hPres20 rMeta (by intro h; cases h) (by intro h; cases h), hM_19]
  have hPlS51 : Placed code (basePc + 14) (metaStoreInstrs (bits := bits) reg6 reg7 off1 (by omega)) :=
    Placed_window hPl 14 rfl
  obtain ⟨s23, hs23, hpc23, hAt23, hFr23, hPres23⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS51 (by omega) (by rw [hpc22, hpc21, hpc20]) hM_22 (by omega)
    (by exact lt_data_size (by omega))
  have hs : Steps code input 17 st s23 :=
    (((hs15.append hs16).append (hs17.append hs18)).append hs19).append
      ((hs20.append (hs21.append hs22)).append hs23)
  have hb0 : (s23.data[metaBase + off0]?).map Fin.val = some a := by
    rw [hFr23 _ (fun he => hNeOff (Nat.add_left_cancel he)), hd22, hd21, hd20, hAt19, Option.map_some, haVal18]
  have hb1 : (s23.data[metaBase + off1]?).map Fin.val = some b := by
    rw [hAt23, Option.map_some, hbVal22]
  refine ⟨s23, hs, hpc23, hb0, hb1, ?_, ?_⟩
  · intro j h0 h1
    rw [hFr23 j h1, hd22, hd21, hd20, hFr19 j h0, hd18, hd17, hd16, hd15]
  · intro rr h6 h7
    rw [hPres23 rr h7, ho22 rr h6, ho21 rr h6, hPres20 rr h6 h7,
      hPres19 rr h7, ho18 rr h6, ho17 rr h6, ho16 rr h6, hPres15 rr h6 h7]

end PaperB.RamProgram.ExitSummaryBuild
