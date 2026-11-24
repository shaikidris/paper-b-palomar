module

public import PaperB.RamExitSummarySweepAROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

/-! Install the owner’s endpoints, ancestry interval and depth before the prior-base fold. -/

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

theorem step4A_ownerFields_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits) (hSz : basePc + 520 < code.size)
    (hBack : Placed code (basePc + 9) (step4ASetup_backPointers h100))
    (hInterval : Placed code (basePc + 29) (step4ASetup_interval h100))
    (hAccumulator : Placed code (basePc + 45) (step4ASetup_accumulators h100))
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (y ownerSlot ownerDepth : Nat)
    (hOwnLt : ownerSlot < r.out.tables.next) (Bcut : CutPair H)
    (hBackB : r.out.tables.back[ownerSlot]? = some (some Bcut))
    (s5 : State DomL) (hpc5 : s5.pc = basePc + 9)
    (hMeta : MetaReady s5 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (h2_5 : (reg s5 reg2).val = y) (h3_5 : (reg s5 reg3).val = ownerSlot)
    (hBoundMeta : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 64 ≤ workCap)
    (hDepth : (s5.data[ownerSlot]?).map Fin.val = some ownerDepth) :
    let metaBase := metaArrBase H.vertexCount H.arcCount r.out.tables.next
    ∃ t, Steps code input 40 s5 t ∧ t.pc = basePc + 49 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = metaBase ∧ (reg t reg2).val = y ∧
      (t.data[metaBase + 48]?).map Fin.val = some Bcut.fst.val ∧
      (t.data[metaBase + 49]?).map Fin.val = some Bcut.snd.val ∧
      (t.data[metaBase + 50]?).map Fin.val =
        some (r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) ∧
      (t.data[metaBase + 51]?).map Fin.val =
        some (r.index.reader.stop (Fin.cast (nodeCount_eq_next r.index.ok).symm ⟨ownerSlot, hOwnLt⟩)) ∧
      (t.data[metaBase + 52]?).map Fin.val = some ownerDepth ∧
      (∀ j, j ≠ metaBase + mIdxCurOwner → j ≠ metaBase + 48 → j ≠ metaBase + 49 →
        j ≠ metaBase + 50 → j ≠ metaBase + 51 → j ≠ metaBase + 52 → t.data[j]? = s5.data[j]?) := by
  let n := H.vertexCount
  let N := r.out.tables.next
  let metaBase := metaArrBase n H.arcCount N
  have hBound : metaBase + 64 ≤ workCap := hBoundMeta
  have hMetaEq : metaBase = 20 * N + 10 * n + H.arcCount + 1 := metaArrBase_eq n H.arcCount N
  have hOffsetLt (off : Nat) (hOff : off < 64) : metaBase + off < workCap := by omega
  have hOffsetFit (off : Nat) (hOff : off < 64) : metaBase + off < 2 ^ bits :=
    Nat.lt_of_lt_of_le (hOffsetLt off hOff) hw
  have hOffNe {a b : Nat} (hne : a ≠ b) : metaBase + a ≠ metaBase + b :=
    fun he => hne (Nat.add_left_cancel he)
  have hBelow : ownerSlot < metaBase := by omega
  have hBelowNe (off : Nat) : ownerSlot ≠ metaBase + off :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hBelow (Nat.le_add_right _ _))
  have hInCap := hIn.cap_ge
  have h0_5 := hMeta.r0_zero
  have h1_5 := hMeta.r1_one
  have hM_5 := hMeta.rMeta_eq
  -- Step 9..11: store `mIdxCurOwner`:
  have hPlSO : Placed code (basePc + 9) (metaStoreInstrs (bits := bits) reg3 reg4 mIdxCurOwner (by dsimp only [mIdxCurOwner]; omega)) :=
    Placed_window hBack 0 rfl
  obtain ⟨s6, hs6, hpc6, hAt6, hFr6, hPres6⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlSO (by omega) hpc5 hM_5 (hOffsetFit mIdxCurOwner (by decide))
    (lt_data_size (hOffsetLt mIdxCurOwner (by decide)))
  have hM_6 : (reg s6 rMeta).val = metaBase := by rw [hPres6 rMeta (by intro h; cases h), hM_5]
  have h3_6 : (reg s6 reg3).val = ownerSlot := by rw [hPres6 reg3 (by intro h; cases h), h3_5]
  have h1_6 : (reg s6 reg1).val = 1 := by rw [hPres6 reg1 (by intro h; cases h), h1_5]
  -- Step 12..20: read `Bcut.fst`, store at `48`:
  have hPlBF : Placed code (basePc + 12) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxBackFstInBase (by dsimp only [mIdxBackFstInBase]; omega)) :=
    Placed_window hBack 3 rfl
  obtain ⟨s7, hs7, hpc7, hd7, h4_7, hPres7⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlBF (by omega) hpc6 hM_6 (hOffsetFit mIdxBackFstInBase (by decide))
    (by rw [hFr6 (metaBase + mIdxBackFstInBase) (hOffNe (by decide))]; exact hMeta.meta_backFstIn)
  have h3_7 : (reg s7 reg3).val = ownerSlot := by rw [hPres7 reg3 (by intro h; cases h) (by intro h; cases h), h3_6]
  have haABF : code[s7.pc]? = some (.add reg4 reg4 reg3) := by rw [hpc7]; exact hBack 6 _ rfl
  obtain ⟨s8, hs8Raw, hpc8, h4_8, ho8, hd8⟩ := step_add_at (input := input) haABF (by omega)
  have hs8 := steps_1_of_step hs8Raw
  have h4Val8 : (reg s8 reg4).val = 4 + n + ownerSlot := by
    rw [h4_8, add_no_wrap _ _ (by rw [h4_7, h3_7]; omega), h4_7, h3_7]
  obtain ⟨oB, hoB, hBack1, _⟩ := hIn.back_at ⟨ownerSlot, hOwnLt⟩
  have hoBEq : oB = some Bcut := Option.some.inj (hoB.symm.trans hBackB)
  rw [hoBEq] at hBack1
  obtain ⟨wbf, hwbf, hwbfV⟩ := Option.map_eq_some_iff.mp hBack1
  have haLBF : code[s8.pc]? = some (.loadInput reg4 reg4) := by rw [hpc8, hpc7]; exact hBack 7 _ rfl
  obtain ⟨s9, hs9Raw, hpc9, h4_9, ho9, hd9⟩ := step_loadInput_at (input := input) haLBF (by omega)
    (by rw [h4Val8]; exact hwbf)
  have hs9 := steps_1_of_step hs9Raw
  have h1_9 : (reg s9 reg1).val = 1 := by
    rw [ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h),
      hPres7 reg1 (by intro h; cases h) (by intro h; cases h), h1_6]
  have h4Val9 : (reg s9 reg4).val = 1 + Bcut.fst.val := by rw [h4_9, hwbfV]; simp [encodeBackPair, RetainedProperLoss.backPairFields, OptionalFinPair.encode, Nat.add_comm]
  have haSBF : code[s9.pc]? = some (.sub reg4 reg4 reg1) := by rw [hpc9, hpc8, hpc7]; exact hBack 8 _ rfl
  obtain ⟨s10, hs10Raw, hpc10, h4_10, ho10, hd10⟩ := step_sub_at (input := input) haSBF (by omega)
  have hs10 := steps_1_of_step hs10Raw
  have h4Val10 : (reg s10 reg4).val = Bcut.fst.val := by
    rw [h4_10, sub_exact (by rw [h4Val9, h1_9]; omega), h4Val9, h1_9]; omega
  have hM_10 : (reg s10 rMeta).val = metaBase := by
    rw [ho10 rMeta (by intro h; cases h), ho9 rMeta (by intro h; cases h),
      ho8 rMeta (by intro h; cases h), hPres7 rMeta (by intro h; cases h) (by intro h; cases h), hM_6]
  have hPlS48 : Placed code (basePc + 18) (metaStoreInstrs (bits := bits) reg4 reg5 48 (by omega)) :=
    Placed_window hBack 9 rfl
  obtain ⟨s11, hs11, hpc11, hAt11, hFr11, hPres11⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS48 (by omega) (by rw [hpc10, hpc9, hpc8, hpc7])
    hM_10 (hOffsetFit 48 (by decide)) (by rw [hd10, hd9, hd8, hd7]; exact lt_data_size (by omega))
  -- Step 21..48: store `Bcut.snd`, `ownerEntry`, `ownerStop`, `ownerDepth` into `49..52`:
  have hM_11 : (reg s11 rMeta).val = metaBase := by rw [hPres11 rMeta (by intro h; cases h), hM_10]
  have h3_11 : (reg s11 reg3).val = ownerSlot := by
    rw [hPres11 reg3 (by intro h; cases h), ho10 reg3 (by intro h; cases h),
      ho9 reg3 (by intro h; cases h), ho8 reg3 (by intro h; cases h), h3_7]
  have hPlBS : Placed code (basePc + 21) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxBackSndInBase (by dsimp only [mIdxBackSndInBase]; omega)) :=
    Placed_window hBack 12 rfl
  obtain ⟨s12, hs12, hpc12, hd12, h4_12, hPres12⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlBS (by omega) hpc11 hM_11 (hOffsetFit mIdxBackSndInBase (by decide))
    (by rw [hFr11 _ (by dsimp only [mIdxBackSndInBase]; omega), hd10, hd9, hd8, hd7,
        hFr6 (metaBase + mIdxBackSndInBase) (hOffNe (by decide))]; exact hMeta.meta_backSndIn)
  have h3_12 : (reg s12 reg3).val = ownerSlot := by rw [hPres12 reg3 (by intro h; cases h) (by intro h; cases h), h3_11]
  have haABS : code[s12.pc]? = some (.add reg4 reg4 reg3) := by rw [hpc12]; exact hBack 15 _ rfl
  obtain ⟨s13, hs13Raw, hpc13, h4_13, ho13, hd13⟩ := step_add_at (input := input) haABS (by omega)
  have hs13 := steps_1_of_step hs13Raw
  have h4Val13 : (reg s13 reg4).val = 4 + n + N + ownerSlot := by
    rw [h4_13, add_no_wrap _ _ (by rw [h4_12, h3_12]; omega), h4_12, h3_12]
  obtain ⟨oB2, hoB2, _, hBack2⟩ := hIn.back_at ⟨ownerSlot, hOwnLt⟩
  rw [Option.some.inj (hoB2.symm.trans hBackB)] at hBack2
  obtain ⟨wbs, hwbs, hwbsV⟩ := Option.map_eq_some_iff.mp hBack2
  have haLBS : code[s13.pc]? = some (.loadInput reg4 reg4) := by rw [hpc13, hpc12]; exact hBack 16 _ rfl
  obtain ⟨s14, hs14Raw, hpc14, h4_14, ho14, hd14⟩ := step_loadInput_at (input := input) haLBS (by omega)
    (by rw [h4Val13]; exact hwbs)
  have hs14 := steps_1_of_step hs14Raw
  have h4Val14 : (reg s14 reg4).val = Bcut.snd.val := by rw [h4_14, hwbsV]; rfl
  have hM_14 : (reg s14 rMeta).val = metaBase := by
    rw [ho14 rMeta (by intro h; cases h), ho13 rMeta (by intro h; cases h),
      hPres12 rMeta (by intro h; cases h) (by intro h; cases h), hM_11]
  have hPlS49 : Placed code (basePc + 26) (metaStoreInstrs (bits := bits) reg4 reg5 49 (by omega)) :=
    Placed_window hBack 17 rfl
  obtain ⟨s15, hs15, hpc15, hAt15, hFr15, hPres15⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS49 (by omega) (by rw [hpc14, hpc13, hpc12])
    hM_14 (hOffsetFit 49 (by decide)) (by exact lt_data_size (by omega))
  have hM_15 : (reg s15 rMeta).val = metaBase := by rw [hPres15 rMeta (by intro h; cases h), hM_14]
  have h3_15 : (reg s15 reg3).val = ownerSlot := by
    rw [hPres15 reg3 (by intro h; cases h), ho14 reg3 (by intro h; cases h), ho13 reg3 (by intro h; cases h), h3_12]
  have hPlFE : Placed code (basePc + 29) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxFEntryInBase (by dsimp only [mIdxFEntryInBase]; omega)) :=
    Placed_window hInterval 0 rfl
  obtain ⟨s16, hs16, hpc16, hd16, h4_16, hPres16⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlFE (by omega) hpc15 hM_15 (hOffsetFit mIdxFEntryInBase (by decide))
    (by rw [hFr15 _ (by dsimp only [mIdxFEntryInBase]; omega), hd14, hd13, hd12,
        hFr11 _ (by dsimp only [mIdxFEntryInBase]; omega), hd10, hd9, hd8, hd7,
        hFr6 (metaBase + mIdxFEntryInBase) (hOffNe (by decide))]; exact hMeta.meta_fEntryIn)
  have h3_16 : (reg s16 reg3).val = ownerSlot := by rw [hPres16 reg3 (by intro h; cases h) (by intro h; cases h), h3_15]
  have haAFE : code[s16.pc]? = some (.add reg4 reg4 reg3) := by rw [hpc16]; exact hInterval 3 _ rfl
  obtain ⟨s17, hs17Raw, hpc17, h4_17, ho17, hd17⟩ := step_add_at (input := input) haAFE (by omega)
  have hs17 := steps_1_of_step hs17Raw
  have h4Val17 : (reg s17 reg4).val = 4 + n + 2 * N + ownerSlot := by
    rw [h4_17, add_no_wrap _ _ (by rw [h4_16, h3_16]; omega), h4_16, h3_16]
  obtain ⟨woen, hwoen, hwoenV⟩ := Option.map_eq_some_iff.mp (hIn.fEntry_at ⟨ownerSlot, hOwnLt⟩)
  have haLFE : code[s17.pc]? = some (.loadInput reg4 reg4) := by rw [hpc17, hpc16]; exact hInterval 4 _ rfl
  obtain ⟨s18, hs18Raw, hpc18, h4_18, ho18, hd18⟩ := step_loadInput_at (input := input) haLFE (by omega)
    (by rw [h4Val17]; exact hwoen)
  have hs18 := steps_1_of_step hs18Raw
  have hM_18 : (reg s18 rMeta).val = metaBase := by
    rw [ho18 rMeta (by intro h; cases h), ho17 rMeta (by intro h; cases h),
      hPres16 rMeta (by intro h; cases h) (by intro h; cases h), hM_15]
  have hPlS50 : Placed code (basePc + 34) (metaStoreInstrs (bits := bits) reg4 reg5 50 (by omega)) :=
    Placed_window hInterval 5 rfl
  obtain ⟨s19, hs19, hpc19, hAt19, hFr19, hPres19⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS50 (by omega) (by rw [hpc18, hpc17, hpc16])
    hM_18 (hOffsetFit 50 (by decide)) (by exact lt_data_size (by omega))
  have hM_19 : (reg s19 rMeta).val = metaBase := by rw [hPres19 rMeta (by intro h; cases h), hM_18]
  have h3_19 : (reg s19 reg3).val = ownerSlot := by
    rw [hPres19 reg3 (by intro h; cases h), ho18 reg3 (by intro h; cases h), ho17 reg3 (by intro h; cases h), h3_16]
  have hPlFS : Placed code (basePc + 37) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxFStopInBase (by dsimp only [mIdxFStopInBase]; omega)) :=
    Placed_window hInterval 8 rfl
  obtain ⟨s20, hs20, hpc20, hd20, h4_20, hPres20⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlFS (by omega) hpc19 hM_19 (hOffsetFit mIdxFStopInBase (by decide))
    (by rw [hFr19 _ (by dsimp only [mIdxFStopInBase]; omega), hd18, hd17, hd16,
        hFr15 _ (by dsimp only [mIdxFStopInBase]; omega), hd14, hd13, hd12,
        hFr11 _ (by dsimp only [mIdxFStopInBase]; omega), hd10, hd9, hd8, hd7,
        hFr6 (metaBase + mIdxFStopInBase) (hOffNe (by decide))]; exact hMeta.meta_fStopIn)
  have h3_20 : (reg s20 reg3).val = ownerSlot := by rw [hPres20 reg3 (by intro h; cases h) (by intro h; cases h), h3_19]
  have haAFS : code[s20.pc]? = some (.add reg4 reg4 reg3) := by rw [hpc20]; exact hInterval 11 _ rfl
  obtain ⟨s21, hs21Raw, hpc21, h4_21, ho21, hd21⟩ := step_add_at (input := input) haAFS (by omega)
  have hs21 := steps_1_of_step hs21Raw
  have h4Val21 : (reg s21 reg4).val = 4 + n + 3 * N + ownerSlot := by
    rw [h4_21, add_no_wrap _ _ (by rw [h4_20, h3_20]; omega), h4_20, h3_20]
  obtain ⟨wost, hwost, hwostV⟩ := Option.map_eq_some_iff.mp (hIn.fStop_at ⟨ownerSlot, hOwnLt⟩)
  have haLFS : code[s21.pc]? = some (.loadInput reg4 reg4) := by rw [hpc21, hpc20]; exact hInterval 12 _ rfl
  obtain ⟨s22, hs22Raw, hpc22, h4_22, ho22, hd22⟩ := step_loadInput_at (input := input) haLFS (by omega)
    (by rw [h4Val21]; exact hwost)
  have hs22 := steps_1_of_step hs22Raw
  have hM_22 : (reg s22 rMeta).val = metaBase := by
    rw [ho22 rMeta (by intro h; cases h), ho21 rMeta (by intro h; cases h),
      hPres20 rMeta (by intro h; cases h) (by intro h; cases h), hM_19]
  have hPlS51 : Placed code (basePc + 42) (metaStoreInstrs (bits := bits) reg4 reg5 51 (by omega)) :=
    Placed_window hInterval 13 rfl
  obtain ⟨s23, hs23, hpc23, hAt23, hFr23, hPres23⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS51 (by omega) (by rw [hpc22, hpc21, hpc20])
    hM_22 (hOffsetFit 51 (by decide)) (lt_data_size (hOffsetLt 51 (by decide)))
  have hM_23 : (reg s23 rMeta).val = metaBase := by rw [hPres23 rMeta (by intro h; cases h), hM_22]
  have h3_23 : (reg s23 reg3).val = ownerSlot := by
    rw [hPres23 reg3 (by intro h; cases h), ho22 reg3 (by intro h; cases h), ho21 reg3 (by intro h; cases h), h3_20]
  have hData23 : ∀ j, j ≠ metaBase + mIdxCurOwner → j ≠ metaBase + 48 → j ≠ metaBase + 49 →
      j ≠ metaBase + 50 → j ≠ metaBase + 51 → s23.data[j]? = s5.data[j]? := fun j h0 j1 j2 j3 j4 => by
    rw [hFr23 j j4, hd22, hd21, hd20, hFr19 j j3, hd18, hd17, hd16,
      hFr15 j j2, hd14, hd13, hd12, hFr11 j j1, hd10, hd9, hd8, hd7, hFr6 j h0]
  obtain ⟨wdp, hwdp, hwdpV⟩ := Option.map_eq_some_iff.mp hDepth
  have haLDep : code[s23.pc]? = some (.loadData reg4 reg3) := by rw [hpc23]; exact hAccumulator 0 _ rfl
  obtain ⟨s24, hs24Raw, hpc24, h4_24, ho24, hd24⟩ := step_loadData_at (input := input) haLDep (by omega)
    (by rw [h3_23, hData23 ownerSlot (hBelowNe mIdxCurOwner) (hBelowNe 48) (hBelowNe 49) (hBelowNe 50) (hBelowNe 51)]; exact hwdp)
  have hs24 := steps_1_of_step hs24Raw
  have hM_24 : (reg s24 rMeta).val = metaBase := by rw [ho24 rMeta (by intro h; cases h), hM_23]
  have hPlS52 : Placed code (basePc + 46) (metaStoreInstrs (bits := bits) reg4 reg5 52 (by omega)) :=
    Placed_window hAccumulator 1 rfl
  obtain ⟨s25, hs25, hpc25, hAt25, hFr25, hPres25⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlS52 (by omega) (by rw [hpc24, hpc23])
    hM_24 (hOffsetFit 52 (by decide)) (lt_data_size (hOffsetLt 52 (by decide)))
  -- The owner fields are installed at instruction 49.
  have hM_25 : (reg s25 rMeta).val = metaBase := by rw [hPres25 rMeta (by intro h; cases h), hM_24]
  have h0_25 : (reg s25 reg0).val = 0 := by
    rw [hPres25 reg0 (by intro h; cases h), ho24 reg0 (by intro h; cases h),
      hPres23 reg0 (by intro h; cases h), ho22 reg0 (by intro h; cases h), ho21 reg0 (by intro h; cases h),
      hPres20 reg0 (by intro h; cases h) (by intro h; cases h), hPres19 reg0 (by intro h; cases h),
      ho18 reg0 (by intro h; cases h), ho17 reg0 (by intro h; cases h),
      hPres16 reg0 (by intro h; cases h) (by intro h; cases h), hPres15 reg0 (by intro h; cases h),
      ho14 reg0 (by intro h; cases h), ho13 reg0 (by intro h; cases h),
      hPres12 reg0 (by intro h; cases h) (by intro h; cases h), hPres11 reg0 (by intro h; cases h),
      ho10 reg0 (by intro h; cases h), ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h),
      hPres7 reg0 (by intro h; cases h) (by intro h; cases h), hPres6 reg0 (by intro h; cases h), h0_5]
  have h1_25 : (reg s25 reg1).val = 1 := by
    rw [hPres25 reg1 (by intro h; cases h), ho24 reg1 (by intro h; cases h),
      hPres23 reg1 (by intro h; cases h), ho22 reg1 (by intro h; cases h), ho21 reg1 (by intro h; cases h),
      hPres20 reg1 (by intro h; cases h) (by intro h; cases h), hPres19 reg1 (by intro h; cases h),
      ho18 reg1 (by intro h; cases h), ho17 reg1 (by intro h; cases h),
      hPres16 reg1 (by intro h; cases h) (by intro h; cases h), hPres15 reg1 (by intro h; cases h),
      ho14 reg1 (by intro h; cases h), ho13 reg1 (by intro h; cases h),
      hPres12 reg1 (by intro h; cases h) (by intro h; cases h), hPres11 reg1 (by intro h; cases h),
      ho10 reg1 (by intro h; cases h), ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h),
      hPres7 reg1 (by intro h; cases h) (by intro h; cases h), hPres6 reg1 (by intro h; cases h), h1_5]
  have h2_25 : (reg s25 reg2).val = y := by
    rw [hPres25 reg2 (by intro h; cases h), ho24 reg2 (by intro h; cases h),
      hPres23 reg2 (by intro h; cases h), ho22 reg2 (by intro h; cases h), ho21 reg2 (by intro h; cases h),
      hPres20 reg2 (by intro h; cases h) (by intro h; cases h), hPres19 reg2 (by intro h; cases h),
      ho18 reg2 (by intro h; cases h), ho17 reg2 (by intro h; cases h),
      hPres16 reg2 (by intro h; cases h) (by intro h; cases h), hPres15 reg2 (by intro h; cases h),
      ho14 reg2 (by intro h; cases h), ho13 reg2 (by intro h; cases h),
      hPres12 reg2 (by intro h; cases h) (by intro h; cases h), hPres11 reg2 (by intro h; cases h),
      ho10 reg2 (by intro h; cases h), ho9 reg2 (by intro h; cases h), ho8 reg2 (by intro h; cases h),
      hPres7 reg2 (by intro h; cases h) (by intro h; cases h), hPres6 reg2 (by intro h; cases h), h2_5]
  have hFirst : Steps code input 12 s5 s11 :=
    (hs6.append (hs7.append (hs8.append (hs9.append hs10)))).append hs11
  have hMiddle : Steps code input 24 s11 s23 :=
    (hs12.append (hs13.append (hs14.append hs15))).append
      ((hs16.append (hs17.append (hs18.append hs19))).append
        (hs20.append (hs21.append (hs22.append hs23))))
  have hTrace : Steps code input 40 s5 s25 :=
    hFirst.append (hMiddle.append (hs24.append hs25))
  have hTailFr : ∀ j, j ≠ metaBase + 52 → s25.data[j]? = s23.data[j]? := by
    intro j hj
    rw [hFr25 j hj, hd24]
  refine ⟨s25, hTrace, hpc25, h0_25, h1_25, hM_25, h2_25, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTailFr (metaBase + 48) (hOffNe (by decide)), hFr23 (metaBase + 48) (hOffNe (by decide)), hd22, hd21, hd20, hFr19 (metaBase + 48) (hOffNe (by decide)),
      hd18, hd17, hd16, hFr15 (metaBase + 48) (hOffNe (by decide)), hd14, hd13, hd12, hAt11, Option.map_some, h4Val10]
  · rw [hTailFr (metaBase + 49) (hOffNe (by decide)), hFr23 (metaBase + 49) (hOffNe (by decide)), hd22, hd21, hd20, hFr19 (metaBase + 49) (hOffNe (by decide)),
      hd18, hd17, hd16, hAt15, Option.map_some, h4Val14]
  · rw [hTailFr (metaBase + 50) (hOffNe (by decide)), hFr23 (metaBase + 50) (hOffNe (by decide)), hd22, hd21, hd20,
      hAt19, Option.map_some, h4_18, hwoenV]
  · rw [hTailFr (metaBase + 51) (hOffNe (by decide)), hAt23, Option.map_some, h4_22, hwostV]
  · rw [hAt25, Option.map_some, h4_24, hwdpV]
  · intro j hOwner h48 h49 h50 h51 h52
    rw [hTailFr j h52, hData23 j hOwner h48 h49 h50 h51]

end PaperB.RamProgram.ExitSummaryBuild
