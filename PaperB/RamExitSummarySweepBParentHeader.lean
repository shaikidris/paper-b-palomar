module

public import PaperB.RamExitSummarySweepBROM
public import PaperB.RamExitSummarySweepAROM

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

theorem step4B_parentHeader_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hRecord : Placed code (basePc + 0) (step4BOneNode_record h100))
    (hSz : basePc + 24 < code.size)
    (n m N nGlobal w pN jN : Nat) (hwLt : w < N)
    (st : State DomL) (hpc : st.pc = basePc)
    (hMeta : MetaReady st n m N nGlobal)
    (hBoundMeta : metaArrBase n m N + 64 ≤ workCap)
    (hCur : (st.data[metaArrBase n m N + mIdxCCursor]?).map Fin.val = some w)
    (hParW : (st.data[storedBase N + 18 * w]?).map Fin.val = some pN)
    (hJumpW : (st.data[storedBase N + 18 * w + 1]?).map Fin.val = some jN) :
    let metaBase := metaArrBase n m N
    ∃ t, Steps code input 24 st t ∧ t.pc = basePc + 24 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaBase ∧
      (reg t reg2).val = w ∧ (reg t reg5).val = pN ∧
      (t.data[metaBase + 48]?).map Fin.val = some pN ∧
      (t.data[metaBase + 49]?).map Fin.val = some jN ∧
      (t.data[metaBase + 55]?).map Fin.val = some (storedBase N + 18 * w) ∧
      (∀ j, j ≠ metaBase + 48 → j ≠ metaBase + 49 → j ≠ metaBase + 55 →
        t.data[j]? = st.data[j]?) := by
  intro metaBase
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  change metaBase + 64 ≤ workCap at hBoundMeta
  have hRM := hMeta.rMeta_eq
  have hOffsetLt (off : Nat) (hOff : off < 64) : metaBase + off < workCap := by omega
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (hOffsetLt off hOff) hw
  have hPlC : Placed code basePc (metaLoadInstrs (bits := bits) reg2 reg4 mIdxCCursor (by dsimp only [mIdxCCursor]; omega)) :=
    Placed_window hRecord 0 rfl
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, hPres1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlC (by omega) hpc hRM (hOffsetFit mIdxCCursor (by decide)) hCur
  have hPlMul : Placed code (basePc + 3)
      [.add reg5 reg2 reg2, .add reg4 reg5 reg5, .add reg4 reg4 reg4,
       .add reg4 reg4 reg4, .add reg4 reg4 reg5] :=
    Placed_window hRecord 3 rfl
  obtain ⟨s6, hs6, hpc6, hd6, h4_6, hPres6⟩ :=
    steps_add_mul18 (input := input) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
      hPlMul (by omega) s1 hpc1 (by rw [h2_1]; omega)
  have h4Val6 : (reg s6 reg4).val = 18 * w := by rw [h4_6, h2_1]
  have hM_6 : (reg s6 rMeta).val = metaBase := by
    rw [hPres6 rMeta (by intro h; cases h) (by intro h; cases h), hPres1 rMeta (by intro h; cases h) (by intro h; cases h), hRM]
  have hd6' : s6.data = st.data := hd6.trans hd1
  have hPlSB : Placed code (basePc + 8) (metaLoadInstrs (bits := bits) reg5 reg6 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega)) :=
    Placed_window hRecord 8 rfl
  obtain ⟨s7, hs7, hpc7, hd7, h5_7, hPres7⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSB (by omega) (by rw [hpc6])
    hM_6 (hOffsetFit mIdxStoredBase (by decide)) (by rw [hd6']; exact hMeta.meta_storedBase)
  have h4_7 : (reg s7 reg4).val = 18 * w := by rw [hPres7 reg4 (by intro h; cases h) (by intro h; cases h), h4Val6]
  have haABW : code[s7.pc]? = some (.add reg4 reg5 reg4) := by rw [hpc7]; exact hRecord 11 _ rfl
  obtain ⟨s8, hs8Raw, hpc8, h4_8, ho8, hd8⟩ := step_add_at (input := input) haABW (by omega)
  have hs8 := steps_1_of_step hs8Raw
  have hBWVal8 : (reg s8 reg4).val = storedBase N + 18 * w := by
    change (reg s7 reg5).val = N at h5_7
    rw [h4_8, add_no_wrap _ _ (by rw [h5_7, h4_7]; omega), h5_7, h4_7]
    rfl
  have hM_8 : (reg s8 rMeta).val = metaBase := by
    rw [ho8 rMeta (by intro h; cases h), hPres7 rMeta (by intro h; cases h) (by intro h; cases h), hM_6]
  have hPlS55 : Placed code (basePc + 12) (metaStoreInstrs (bits := bits) reg4 reg6 55 (by omega)) :=
    Placed_window hRecord 12 rfl
  obtain ⟨s9, hs9, hpc9, hAt9, hFr9, hPres9⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS55 (by omega) (by rw [hpc8, hpc7]) hM_8 (by omega)
    (by rw [hd8, hd7, hd6']; exact lt_data_size (by omega))
  have h4_9 : (reg s9 reg4).val = storedBase N + 18 * w := by rw [hPres9 reg4 (by intro h; cases h), hBWVal8]
  have hM_9 : (reg s9 rMeta).val = metaBase := by rw [hPres9 rMeta (by intro h; cases h), hM_8]
  have h1_9 : (reg s9 reg1).val = 1 := by
    rw [hPres9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h),
      hPres7 reg1 (by intro h; cases h) (by intro h; cases h), hPres6 reg1 (by intro h; cases h) (by intro h; cases h), hPres1 reg1 (by intro h; cases h) (by intro h; cases h), hMeta.r1_one]
  have h2_9 : (reg s9 reg2).val = w := by
    rw [hPres9 reg2 (by intro h; cases h), ho8 reg2 (by intro h; cases h),
      hPres7 reg2 (by intro h; cases h) (by intro h; cases h), hPres6 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  obtain ⟨wp, hwp, hwpV⟩ := Option.map_eq_some_iff.mp hParW
  have haLP : code[s9.pc]? = some (.loadData reg5 reg4) := by rw [hpc9]; exact hRecord 15 _ rfl
  obtain ⟨s10, hs10Raw, hpc10, h5_10, ho10, hd10⟩ := step_loadData_at (input := input) haLP (by omega)
    (by rw [h4_9, hFr9 _ (by unfold storedBase; omega), hd8, hd7, hd6']; exact hwp)
  have hs10 := steps_1_of_step hs10Raw
  have hpVal10 : (reg s10 reg5).val = pN := by rw [h5_10, hwpV]
  have hM_10 : (reg s10 rMeta).val = metaBase := by rw [ho10 rMeta (by intro h; cases h), hM_9]
  have hPlS48 : Placed code (basePc + 16) (metaStoreInstrs (bits := bits) reg5 reg6 48 (by omega)) :=
    Placed_window hRecord 16 rfl
  obtain ⟨s11, hs11, hpc11, hAt11, hFr11, hPres11⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS48 (by omega) (by rw [hpc10, hpc9]) hM_10 (by omega)
    (by rw [hd10]; exact lt_data_size (by omega))
  have h4_11 : (reg s11 reg4).val = storedBase N + 18 * w := by
    rw [hPres11 reg4 (by intro h; cases h), ho10 reg4 (by intro h; cases h), h4_9]
  have h1_11 : (reg s11 reg1).val = 1 := by
    rw [hPres11 reg1 (by intro h; cases h), ho10 reg1 (by intro h; cases h), h1_9]
  have h5_11 : (reg s11 reg5).val = pN := by rw [hPres11 reg5 (by intro h; cases h), hpVal10]
  have haAJ1 : code[s11.pc]? = some (.add reg6 reg4 reg1) := by rw [hpc11]; exact hRecord 19 _ rfl
  obtain ⟨s12, hs12Raw, hpc12, h6_12, ho12, hd12⟩ := step_add_at (input := input) haAJ1 (by omega)
  have hs12 := steps_1_of_step hs12Raw
  have h6Val12 : (reg s12 reg6).val = storedBase N + 18 * w + 1 := by
    rw [h6_12, add_no_wrap _ _ (by rw [h4_11, h1_11]; try dsimp only [storedBase]; omega), h4_11, h1_11]
  obtain ⟨wj, hwj, hwjV⟩ := Option.map_eq_some_iff.mp hJumpW
  have haLJ1 : code[s12.pc]? = some (.loadData reg6 reg6) := by rw [hpc12, hpc11]; exact hRecord 20 _ rfl
  obtain ⟨s13, hs13Raw, hpc13, h6_13, ho13, hd13⟩ := step_loadData_at (input := input) haLJ1 (by omega)
    (by rw [h6Val12, hd12, hFr11 _ (by unfold storedBase; omega), hd10,
        hFr9 _ (by unfold storedBase; omega), hd8, hd7, hd6']; exact hwj)
  have hs13 := steps_1_of_step hs13Raw
  have hjVal13 : (reg s13 reg6).val = jN := by rw [h6_13, hwjV]
  have hM_13 : (reg s13 rMeta).val = metaBase := by
    rw [ho13 rMeta (by intro h; cases h), ho12 rMeta (by intro h; cases h),
      hPres11 rMeta (by intro h; cases h), hM_10]
  have hPlS49 : Placed code (basePc + 21) (metaStoreInstrs (bits := bits) reg6 reg7 49 (by omega)) :=
    Placed_window hRecord 21 rfl
  obtain ⟨s14, hs14, hpc14, hAt14, hFr14, hPres14⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS49 (by omega) (by rw [hpc13, hpc12, hpc11]) hM_13 (by omega)
    (by exact lt_data_size (by omega))
  have hM_14 : (reg s14 rMeta).val = metaBase := by rw [hPres14 rMeta (by intro h; cases h), hM_13]
  have h1_14 : (reg s14 reg1).val = 1 := by
    rw [hPres14 reg1 (by intro h; cases h), ho13 reg1 (by intro h; cases h), ho12 reg1 (by intro h; cases h), h1_11]
  have h2_14 : (reg s14 reg2).val = w := by
    rw [hPres14 reg2 (by intro h; cases h), ho13 reg2 (by intro h; cases h), ho12 reg2 (by intro h; cases h),
      hPres11 reg2 (by intro h; cases h), ho10 reg2 (by intro h; cases h), h2_9]
  have h5_14 : (reg s14 reg5).val = pN := by
    rw [hPres14 reg5 (by intro h; cases h), ho13 reg5 (by intro h; cases h), ho12 reg5 (by intro h; cases h), h5_11]
  have hData14 : ∀ j, j ≠ metaBase + 48 → j ≠ metaBase + 49 → j ≠ metaBase + 55 →
      s14.data[j]? = st.data[j]? := fun j h1 h2 h3 => by
    rw [hFr14 j h2, hd13, hd12, hFr11 j h1, hd10, hFr9 j h3, hd8, hd7, hd6']
  have h0_14 : (reg s14 reg0).val = 0 := by
    rw [hPres14 reg0 (by intro h; cases h), ho13 reg0 (by intro h; cases h),
      ho12 reg0 (by intro h; cases h), hPres11 reg0 (by intro h; cases h),
      ho10 reg0 (by intro h; cases h), hPres9 reg0 (by intro h; cases h),
      ho8 reg0 (by intro h; cases h), hPres7 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres6 reg0 (by intro h; cases h) (by intro h; cases h),
      hPres1 reg0 (by intro h; cases h) (by intro h; cases h), hMeta.r0_zero]
  have h48_14 : (s14.data[metaBase + 48]?).map Fin.val = some pN := by
    rw [hFr14 _ (by omega), hd13, hd12, hAt11, Option.map_some, hpVal10]
  have h49_14 : (s14.data[metaBase + 49]?).map Fin.val = some jN := by
    rw [hAt14, Option.map_some, hjVal13]
  have h55_14 : (s14.data[metaBase + 55]?).map Fin.val = some (storedBase N + 18 * w) := by
    rw [hFr14 _ (by omega), hd13, hd12, hFr11 _ (by omega), hd10, hAt9, Option.map_some, hBWVal8]
  have hSteps14 : Steps code input 24 st s14 :=
    (((hs1.append hs6).append (hs7.append hs8)).append
      ((hs9.append (hs10.append hs11)).append (hs12.append hs13))).append hs14
  exact ⟨s14, hSteps14, hpc14, h0_14, h1_14, hM_14, h2_14, h5_14,
    h48_14, h49_14, h55_14, hData14⟩

end PaperB.RamProgram.ExitSummaryBuild
