module

public import PaperB.RamExitSummarySweepAROM
public import PaperB.RamExitSummarySweepBTag

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4800000

/-! Serialize both coordinates of a cached parent map. -/

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

private theorem copyWrite1 {code : Program DomL} {input : Input DomL}
    (basePc metaBase : Nat) : ∀ (off addr srcOff : Nat) (hOff : srcOff < 2 ^ bits) (sIn : State DomL) (val : Nat),
    Placed code (basePc + off) (metaLoadInstrs (bits := bits) reg3 reg4 srcOff hOff ++ [.storeData reg2 reg3, .add reg2 reg2 reg1]) →
    sIn.pc = basePc + off → basePc + off + 5 < code.size →
    (reg sIn reg1).val = 1 → (reg sIn rMeta).val = metaBase → (reg sIn reg2).val = addr →
    addr < workCap → addr + 1 < 2 ^ bits → metaBase + srcOff < 2 ^ bits →
    (sIn.data[metaBase + srcOff]?).map Fin.val = some val →
    ∃ sOut : State DomL, Steps code input 5 sIn sOut ∧ sOut.pc = basePc + off + 5 ∧
      (reg sOut reg0).val = (reg sIn reg0).val ∧ (reg sOut reg1).val = 1 ∧ (reg sOut rMeta).val = metaBase ∧
      (reg sOut reg2).val = addr + 1 ∧
      (sOut.data[addr]?).map Fin.val = some val ∧
      (∀ j, j ≠ addr → sOut.data[j]? = sIn.data[j]?) := by
  intro off addr srcOff hOff sIn val hPlS hpcS hSzS h1S hMS h2S hCapA hFitA hFitSrc hVal
  obtain ⟨sa, hsa, hpca, hda, h3a, hPresa⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) (Placed_append_left hPlS) (by omega) hpcS hMS hFitSrc hVal
  have h2a : (reg sa reg2).val = addr := by rw [hPresa reg2 (by intro h; cases h) (by intro h; cases h), h2S]
  have h1a : (reg sa reg1).val = 1 := by rw [hPresa reg1 (by intro h; cases h) (by intro h; cases h), h1S]
  have h0a : (reg sa reg0).val = (reg sIn reg0).val := congrArg Fin.val (hPresa reg0 (by intro h; cases h) (by intro h; cases h))
  have hMa : (reg sa rMeta).val = metaBase := by rw [hPresa rMeta (by intro h; cases h) (by intro h; cases h), hMS]
  have hLtSa : (reg sa reg2).val < sa.data.size := by rw [hda]; exact lt_data_size (by omega)
  have hPlTail := Placed_append_right hPlS
  rw [show (metaLoadInstrs (bits := bits) reg3 reg4 srcOff hOff).length = 3 by rfl] at hPlTail
  obtain ⟨sb, hsbRaw, hpcb, hrb, hdb⟩ := step_storeData_opaque (input := input)
    (by rw [hpca]; exact hPlTail 0 _ rfl) hLtSa (by omega)
  have hsb := steps_1_of_step hsbRaw
  have hrbF := reg_of_regs_eq hrb
  have h2b : (reg sb reg2).val = addr := by rw [hrbF, h2a]
  have h1b : (reg sb reg1).val = 1 := by rw [hrbF, h1a]
  obtain ⟨sc, hscRaw, hpcc, h2c, hoc, hdc⟩ := step_add_at (input := input)
    (by rw [hpcb, hpca]; exact hPlTail 1 _ rfl) (by omega)
  have hsc := steps_1_of_step hscRaw
  refine ⟨sc, (hsa.append hsb).append hsc, by omega,
    by rw [hoc reg0 (by intro h; cases h), hrbF, h0a],
    by rw [hoc reg1 (by intro h; cases h), h1b],
    by rw [hoc rMeta (by intro h; cases h), hrbF, hMa],
    by rw [h2c, add_no_wrap _ _ (by rw [h2b, h1b]; omega), h2b, h1b],
    by rw [hdc, hdb, ← h2a, Array.getElem?_set_self hLtSa, Option.map_some, h3a],
    fun j hj => by rw [hdc, hdb, Array.getElem?_set_ne hLtSa (by rw [h2a]; exact Ne.symm hj), hda]⟩

theorem step4B_writeParent0_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hWriteFirst : Placed code (basePc + 624) (step4BOneNode_writeFirst basePc h100))
    (hWriteSecond : Placed code (basePc + 664) (step4BOneNode_writeSecond basePc h100))
    (hSz : basePc + 703 < code.size)
    (n m N w a b p0 : Nat) (hwLt : w < N) (hNe : a ≠ b)
    (hBoundMeta : metaArrBase n m N + 64 ≤ workCap)
    (c : Interval) (s53 : State DomL) (hpc53 : s53.pc = basePc + 624)
    (h0_53 : (reg s53 reg0).val = 0) (h1_53 : (reg s53 reg1).val = 1)
    (hM_53 : (reg s53 rMeta).val = metaArrBase n m N)
    (h50 : (s53.data[metaArrBase n m N + 50]?).map Fin.val = some a)
    (h51 : (s53.data[metaArrBase n m N + 51]?).map Fin.val = some b)
    (h52 : (s53.data[metaArrBase n m N + 52]?).map Fin.val = some p0)
    (h55 : (s53.data[metaArrBase n m N + 55]?).map Fin.val = some (storedBase N + 18 * w))
    (hC53 : IntervalWordsAt s53.data (metaArrBase n m N + mIdxAcc0) c) :
    let slot := fun (s : Nat) => if s = a then some (0 : Fin 2) else if s = b then some 1 else none
    ∃ k t, k ≤ 39 ∧ Steps code input k s53 t ∧ t.pc = basePc + 666 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaArrBase n m N ∧
      (reg t reg2).val = storedBase N + 18 * w + 6 ∧
      CoordWordsAt t.data (storedBase N + 18 * w + 2) ⟨c, slot p0⟩ ∧
      (∀ j, (j < storedBase N + 18 * w + 2 ∨ storedBase N + 18 * w + 6 ≤ j) →
        t.data[j]? = s53.data[j]?) := by
  intro slot
  let metaBase := metaArrBase n m N
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hAfter (off : Nat) : storedBase N + 18 * w + 10 ≤ metaBase + off := by
    unfold storedBase
    omega
  change metaBase + 64 ≤ workCap at hBoundMeta
  -- Step 624..702: write `parentMap` into `storedBase N + 18 * w + 2 .. +9`!
  have hPl55 : Placed code (basePc + 624) (metaLoadInstrs (bits := bits) reg2 reg4 55 (by omega)) :=
    Placed_window hWriteFirst 0 rfl
  obtain ⟨s54, hs54, hpc54, hd54, h2_54, hPres54⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl55 (by omega) hpc53 hM_53 (by omega)
    h55
  have h0_54 : (reg s54 reg0).val = 0 := by rw [hPres54 reg0 (by intro h; cases h) (by intro h; cases h), h0_53]
  have h1_54 : (reg s54 reg1).val = 1 := by rw [hPres54 reg1 (by intro h; cases h) (by intro h; cases h), h1_53]
  have hM_54 : (reg s54 rMeta).val = metaBase := by rw [hPres54 rMeta (by intro h; cases h) (by intro h; cases h), hM_53]
  have haA627 : code[s54.pc]? = some (.add reg2 reg2 reg1) := by rw [hpc54]; exact hWriteFirst 3 _ rfl
  obtain ⟨s55, hs55Raw, hpc55, h2_55, ho55, hd55⟩ := step_add_at (input := input) haA627 (by omega)
  have hs55 := steps_1_of_step hs55Raw
  have h2Val55 : (reg s55 reg2).val = storedBase N + 18 * w + 1 := by
    rw [h2_55, add_no_wrap _ _ (by rw [h2_54, h1_54]; try dsimp only [storedBase]; omega), h2_54, h1_54]
  have haA628 : code[s55.pc]? = some (.add reg2 reg2 reg1) := by rw [hpc55, hpc54]; exact hWriteFirst 4 _ rfl
  obtain ⟨s56, hs56Raw, hpc56, h2_56, ho56, hd56⟩ := step_add_at (input := input) haA628 (by omega)
  have hs56 := steps_1_of_step hs56Raw
  have h2Val56 : (reg s56 reg2).val = storedBase N + 18 * w + 2 := by
    rw [h2_56, add_no_wrap _ _ (by rw [h2Val55, ho55 reg1 (by intro h; cases h), h1_54]; try dsimp only [storedBase]; omega),
      h2Val55, ho55 reg1 (by intro h; cases h), h1_54]
  have h0_56 : (reg s56 reg0).val = 0 := by rw [ho56 reg0 (by intro h; cases h), ho55 reg0 (by intro h; cases h), h0_54]
  have h1_56 : (reg s56 reg1).val = 1 := by rw [ho56 reg1 (by intro h; cases h), ho55 reg1 (by intro h; cases h), h1_54]
  have hM_56 : (reg s56 rMeta).val = metaBase := by rw [ho56 rMeta (by intro h; cases h), ho55 rMeta (by intro h; cases h), hM_54]
  have hd56' : s56.data = s53.data := by rw [hd56, hd55, hd54]
  have hc0W : (s56.data[metaBase + 30]?).map Fin.val = some (match c with | .empty => 0 | .span _ _ => 1) ∧
      (s56.data[metaBase + 31]?).map Fin.val = some (match c with | .empty => 0 | .span lo _ => lo) ∧
      (s56.data[metaBase + 32]?).map Fin.val = some (match c with | .empty => 0 | .span _ hi => hi) := by
    rw [hd56']
    cases c <;> exact hC53
  obtain ⟨s57, hs57, hpc57, h0_57, h1_57, hM_57, h2_57, hAt57, hFr57⟩ := copyWrite1 (input := input) basePc metaBase 629 (storedBase N + 18 * w + 2) 30 (by omega) s56 _
    (Placed_window hWriteFirst 5 rfl)
    (by rw [hpc56, hpc55, hpc54]) (by omega) h1_56 hM_56 h2Val56 (by unfold storedBase; omega)
    (by unfold storedBase; omega) (by omega) hc0W.1
  obtain ⟨s58, hs58, hpc58, h0_58, h1_58, hM_58, h2_58, hAt58, hFr58⟩ := copyWrite1 (input := input) basePc metaBase 634 (storedBase N + 18 * w + 3) 31 (by omega) s57 _
    (Placed_window hWriteFirst 10 rfl)
    hpc57 (by omega) h1_57 hM_57 h2_57 (by unfold storedBase; omega) (by unfold storedBase; omega) (by omega)
    (by rw [hFr57 _ (by unfold storedBase; omega)]; exact hc0W.2.1)
  obtain ⟨s59, hs59, hpc59, h0_59, h1_59, hM_59, h2_59, hAt59, hFr59⟩ := copyWrite1 (input := input) basePc metaBase 639 (storedBase N + 18 * w + 4) 32 (by omega) s58 _
    (Placed_window hWriteFirst 15 rfl)
    hpc58 (by omega) h1_58 hM_58 h2_58 (by unfold storedBase; omega) (by unfold storedBase; omega) (by omega)
    (by rw [hFr58 _ (by unfold storedBase; omega), hFr57 _ (by unfold storedBase; omega)]; exact hc0W.2.2)
  have haMv644 : code[s59.pc]? = some (.mov reg6 reg2) := by rw [hpc59]; exact hWriteFirst 20 _ rfl
  obtain ⟨s60, hs60Raw, hpc60, h6_60, ho60, hd60⟩ := step_mov_at (input := input) haMv644 (by omega)
  have hs60 := steps_1_of_step hs60Raw
  have hPlTag0 : Placed code (basePc + 645) (step4BSlotTagInstrs (bits := bits) (basePc + 645) 52 (by omega) h100) := by
    exact Placed_window hWriteFirst 21 rfl
  have hFr59_base : ∀ j, j < storedBase N + 18 * w + 2 ∨ storedBase N + 18 * w + 5 ≤ j → s59.data[j]? = s53.data[j]? := fun j hj => by
    rw [hFr59 j (by rcases hj with h | h <;> omega), hFr58 j (by rcases hj with h | h <;> omega),
      hFr57 j (by rcases hj with h | h <;> omega), hd56']
  obtain ⟨kT0, s61, hkT0, hs61, hpc61, hd61, h0_61, h1_61, hM_61, h4_61, hPres61⟩ := run_step4BSlotTag (input := input)
    (basePc + 645) 52 (by omega) h100 hPlTag0 (by omega) hBoundMeta hWorkFit p0 a b
    hNe s60 (by rw [hpc60, hpc59])
    (by rw [ho60 reg0 (by intro h; cases h), h0_59, h0_58, h0_57, h0_56])
    (by rw [ho60 reg1 (by intro h; cases h), h1_59])
    (by rw [ho60 rMeta (by intro h; cases h), hM_59])
    (by rw [hd60, hFr59_base (metaBase + 52) (Or.inr (Nat.le_trans (by omega : storedBase N + 18 * w + 5 ≤ _) (hAfter 52)))]; exact h52)
    (by rw [hd60, hFr59_base (metaBase + 50) (Or.inr (Nat.le_trans (by omega : storedBase N + 18 * w + 5 ≤ _) (hAfter 50)))]; exact h50)
    (by rw [hd60, hFr59_base (metaBase + 51) (Or.inr (Nat.le_trans (by omega : storedBase N + 18 * w + 5 ≤ _) (hAfter 51)))]; exact h51)
  have h6_61 : (reg s61 reg6).val = storedBase N + 18 * w + 5 := by
    rw [hPres61 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6_60, h2_59]
  have hLt61 : (reg s61 reg6).val < s61.data.size := by rw [h6_61]; exact lt_data_size (by unfold storedBase; omega)
  have haSt664 : code[s61.pc]? = some (.storeData reg6 reg4) := by rw [hpc61]; exact hWriteSecond 0 _ rfl
  obtain ⟨s62, hs62Raw, hpc62, hrb62, hdb62⟩ := step_storeData_opaque (input := input) haSt664 hLt61 (by omega)
  have hs62 := steps_1_of_step hs62Raw
  have hrb62F := reg_of_regs_eq hrb62
  have h6_62 : (reg s62 reg6).val = storedBase N + 18 * w + 5 := by rw [hrb62F, h6_61]
  have h1_62 : (reg s62 reg1).val = 1 := by rw [hrb62F, h1_61]
  have haA665 : code[s62.pc]? = some (.add reg2 reg6 reg1) := by rw [hpc62, hpc61]; exact hWriteSecond 1 _ rfl
  obtain ⟨s63, hs63Raw, hpc63, h2_63, ho63, hd63⟩ := step_add_at (input := input) haA665 (by omega)
  have hs63 := steps_1_of_step hs63Raw
  have h2Val63 : (reg s63 reg2).val = storedBase N + 18 * w + 6 := by
    rw [h2_63, add_no_wrap _ _ (by rw [h6_62, h1_62]; try dsimp only [storedBase]; omega), h6_62, h1_62]
  have h0_63 : (reg s63 reg0).val = 0 := by rw [ho63 reg0 (by intro h; cases h), hrb62F, h0_61]
  have h1_63 : (reg s63 reg1).val = 1 := by rw [ho63 reg1 (by intro h; cases h), h1_62]
  have hM_63 : (reg s63 rMeta).val = metaBase := by rw [ho63 rMeta (by intro h; cases h), hrb62F, hM_61]
  have hAtTag0 : (s63.data[storedBase N + 18 * w + 5]?).map Fin.val =
      some (if p0 = a then 1 else if p0 = b then 2 else 0) := by
    rw [hd63, hdb62, ← h6_61, Array.getElem?_set_self hLt61, Option.map_some, h4_61]
  have hFr63 : ∀ j, (j < storedBase N + 18 * w + 2 ∨ storedBase N + 18 * w + 6 ≤ j) →
      s63.data[j]? = s53.data[j]? := fun j hj => by
    rw [hd63, hdb62, Array.getElem?_set_ne hLt61 (by rw [h6_61]; rcases hj with h | h <;> omega), hd61, hd60]
    exact hFr59_base j (by rcases hj with h | h <;> omega)
  have hSteps : Steps code input (3 + 2 + 15 + 1 + kT0 + 2) s53 s63 :=
    ((hs54.append (hs55.append hs56)).append ((hs57.append (hs58.append hs59)).append hs60)).append
      (hs61.append (hs62.append hs63))
  have hf (j : Nat) (hj : j < storedBase N + 18 * w + 5) :
      s63.data[j]? = s59.data[j]? := by
    rw [hd63, hdb62, Array.getElem?_set_ne hLt61 (by rw [h6_61]; omega), hd61, hd60]
  have hOne : CoordWordsAt s63.data (storedBase N + 18 * w + 2) ⟨c, slot p0⟩ := by
    constructor
    · cases c <;> refine ⟨?_, ?_, ?_⟩
      all_goals first
        | rw [hf _ (by omega), hFr59 _ (by omega), hFr58 _ (by omega)]; exact hAt57
        | rw [hf _ (by omega), hFr59 _ (by omega)]; exact hAt58
        | rw [hf _ (by omega)]; exact hAt59
    · change (s63.data[storedBase N + 18 * w + 5]?).map Fin.val = _
      rw [hAtTag0]
      by_cases h : p0 = a
      · simp [slot, h]
      · by_cases h' : p0 = b <;> simp [slot, h, h', Ne.symm hNe]
  exact ⟨_, s63, by omega, hSteps, by rw [hpc63, hpc62, hpc61],
    h0_63, h1_63, hM_63, h2Val63, hOne, hFr63⟩

theorem step4B_writeParent1_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hWriteSecond : Placed code (basePc + 664) (step4BOneNode_writeSecond basePc h100))
    (hSz : basePc + 703 < code.size)
    (n m N w a b p1 : Nat) (hwLt : w < N) (hNe : a ≠ b)
    (hBoundMeta : metaArrBase n m N + 64 ≤ workCap)
    (c : Interval) (s63 : State DomL) (hpc63 : s63.pc = basePc + 666)
    (h0_63 : (reg s63 reg0).val = 0) (h1_63 : (reg s63 reg1).val = 1)
    (hM_63 : (reg s63 rMeta).val = metaArrBase n m N)
    (h50 : (s63.data[metaArrBase n m N + 50]?).map Fin.val = some a)
    (h51 : (s63.data[metaArrBase n m N + 51]?).map Fin.val = some b)
    (h53 : (s63.data[metaArrBase n m N + 53]?).map Fin.val = some p1)
    (h2_63 : (reg s63 reg2).val = storedBase N + 18 * w + 6)
    (hC63 : IntervalWordsAt s63.data (metaArrBase n m N + 33) c) :
    let slot := fun (s : Nat) => if s = a then some (0 : Fin 2) else if s = b then some 1 else none
    ∃ k t, k ≤ 34 ∧ Steps code input k s63 t ∧ t.pc = basePc + 703 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaArrBase n m N ∧
      CoordWordsAt t.data (storedBase N + 18 * w + 6) ⟨c, slot p1⟩ ∧
      (∀ j, (j < storedBase N + 18 * w + 6 ∨ storedBase N + 18 * w + 10 ≤ j) →
        t.data[j]? = s63.data[j]?) := by
  intro slot
  let metaBase := metaArrBase n m N
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  have hWorkFit : workCap ≤ 2 ^ bits := hw
  have hAfter (off : Nat) : storedBase N + 18 * w + 10 ≤ metaBase + off := by
    unfold storedBase
    omega
  change metaBase + 64 ≤ workCap at hBoundMeta
  -- Step 624..702: write `parentMap` into `storedBase N + 18 * w + 2 .. +9`!
  have hc1W : (s63.data[metaBase + 33]?).map Fin.val = some (match c with | .empty => 0 | .span _ _ => 1) ∧
      (s63.data[metaBase + 34]?).map Fin.val = some (match c with | .empty => 0 | .span lo _ => lo) ∧
      (s63.data[metaBase + 35]?).map Fin.val = some (match c with | .empty => 0 | .span _ hi => hi) := by
    cases c <;> exact hC63
  obtain ⟨s64, hs64, hpc64, h0_64, h1_64, hM_64, h2_64, hAt64, hFr64⟩ := copyWrite1 (input := input) basePc metaBase 666 (storedBase N + 18 * w + 6) 33 (by omega) s63 _
    (Placed_window hWriteSecond 2 rfl)
    hpc63 (by omega) h1_63 hM_63 h2_63 (by unfold storedBase; omega)
    (by unfold storedBase; omega) (by omega) hc1W.1
  obtain ⟨s65, hs65, hpc65, h0_65, h1_65, hM_65, h2_65, hAt65, hFr65⟩ := copyWrite1 (input := input) basePc metaBase 671 (storedBase N + 18 * w + 7) 34 (by omega) s64 _
    (Placed_window hWriteSecond 7 rfl)
    hpc64 (by omega) h1_64 hM_64 h2_64 (by unfold storedBase; omega) (by unfold storedBase; omega) (by omega)
    (by rw [hFr64 (metaBase + 34) (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega : storedBase N + 18 * w + 6 < _) (hAfter 34)))]; exact hc1W.2.1)
  obtain ⟨s66, hs66, hpc66, h0_66, h1_66, hM_66, h2_66, hAt66, hFr66⟩ := copyWrite1 (input := input) basePc metaBase 676 (storedBase N + 18 * w + 8) 35 (by omega) s65 _
    (Placed_window hWriteSecond 12 rfl)
    hpc65 (by omega) h1_65 hM_65 h2_65 (by unfold storedBase; omega) (by unfold storedBase; omega) (by omega)
    (by rw [hFr65 (metaBase + 35) (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega : storedBase N + 18 * w + 7 < _) (hAfter 35))), hFr64 (metaBase + 35) (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by omega : storedBase N + 18 * w + 6 < _) (hAfter 35)))]; exact hc1W.2.2)
  have haMv681 : code[s66.pc]? = some (.mov reg6 reg2) := by rw [hpc66]; exact hWriteSecond 17 _ rfl
  obtain ⟨s67, hs67Raw, hpc67, h6_67, ho67, hd67⟩ := step_mov_at (input := input) haMv681 (by omega)
  have hs67 := steps_1_of_step hs67Raw
  have hPlTag1 : Placed code (basePc + 682) (step4BSlotTagInstrs (bits := bits) (basePc + 682) 53 (by omega) h100) := by
    exact Placed_window hWriteSecond 18 rfl
  have hFr66_base : ∀ j, (j < storedBase N + 18 * w + 6 ∨ storedBase N + 18 * w + 9 ≤ j) → s66.data[j]? = s63.data[j]? := fun j hj => by
    rw [hFr66 j (by rcases hj with h | h <;> omega), hFr65 j (by rcases hj with h | h <;> omega),
      hFr64 j (by rcases hj with h | h <;> omega)]
  obtain ⟨kT1, s68, hkT1, hs68, hpc68, hd68, h0_68, h1_68, hM_68, h4_68, hPres68⟩ := run_step4BSlotTag (input := input)
    (basePc + 682) 53 (by omega) h100 hPlTag1 (by omega) hBoundMeta hWorkFit p1 a b
    hNe s67 (by rw [hpc67, hpc66])
    (by rw [ho67 reg0 (by intro h; cases h), h0_66, h0_65, h0_64, h0_63])
    (by rw [ho67 reg1 (by intro h; cases h), h1_66])
    (by rw [ho67 rMeta (by intro h; cases h), hM_66])
    (by rw [hd67, hFr66_base (metaBase + 53) (Or.inr (Nat.le_trans (by omega : storedBase N + 18 * w + 9 ≤ _) (hAfter 53)))]; exact h53)
    (by rw [hd67, hFr66_base (metaBase + 50) (Or.inr (Nat.le_trans (by omega : storedBase N + 18 * w + 9 ≤ _) (hAfter 50)))]; exact h50)
    (by rw [hd67, hFr66_base (metaBase + 51) (Or.inr (Nat.le_trans (by omega : storedBase N + 18 * w + 9 ≤ _) (hAfter 51)))]; exact h51)
  have h6_68 : (reg s68 reg6).val = storedBase N + 18 * w + 9 := by
    rw [hPres68 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6_67, h2_66]
  have hLt68 : (reg s68 reg6).val < s68.data.size := by rw [h6_68]; exact lt_data_size (by unfold storedBase; omega)
  have haSt701 : code[s68.pc]? = some (.storeData reg6 reg4) := by rw [hpc68]; exact hWriteSecond 37 _ rfl
  obtain ⟨s69, hs69Raw, hpc69, hrb69, hdb69⟩ := step_storeData_opaque (input := input) haSt701 hLt68 (by omega)
  have hs69 := steps_1_of_step hs69Raw
  have hrb69F := reg_of_regs_eq hrb69
  have h6_69 : (reg s69 reg6).val = storedBase N + 18 * w + 9 := by rw [hrb69F, h6_68]
  have h1_69 : (reg s69 reg1).val = 1 := by rw [hrb69F, h1_68]
  have haA702 : code[s69.pc]? = some (.add reg6 reg6 reg1) := by rw [hpc69, hpc68]; exact hWriteSecond 38 _ rfl
  obtain ⟨t, htRaw, hpct, h6t, hot, hdt⟩ := step_add_at (input := input) haA702 (by omega)
  have ht := steps_1_of_step htRaw
  have h0T : (reg t reg0).val = 0 := by rw [hot reg0 (by intro h; cases h), hrb69F, h0_68]
  have h1T : (reg t reg1).val = 1 := by rw [hot reg1 (by intro h; cases h), h1_69]
  have hMT : (reg t rMeta).val = metaBase := by rw [hot rMeta (by intro h; cases h), hrb69F, hM_68]
  have hFr : ∀ j, j < storedBase N + 18 * w + 6 ∨ storedBase N + 18 * w + 10 ≤ j →
      t.data[j]? = s63.data[j]? := fun j hj => by
    rw [hdt, hdb69, Array.getElem?_set_ne hLt68 (by rw [h6_68]; rcases hj with h | h <;> omega),
      hd68, hd67, hFr66_base j (by rcases hj with h | h <;> omega)]
  have hf (j : Nat) (hj : j < storedBase N + 18 * w + 9) :
      t.data[j]? = s66.data[j]? := by
    rw [hdt, hdb69, Array.getElem?_set_ne hLt68 (by rw [h6_68]; omega), hd68, hd67]
  have hOne : CoordWordsAt t.data (storedBase N + 18 * w + 6) ⟨c, slot p1⟩ := by
    constructor
    · cases c <;> refine ⟨?_, ?_, ?_⟩
      all_goals first
        | rw [hf _ (by omega), hFr66 _ (by omega), hFr65 _ (by omega)]; exact hAt64
        | rw [hf _ (by omega), hFr66 _ (by omega)]; exact hAt65
        | rw [hf _ (by omega)]; exact hAt66
    · change (t.data[storedBase N + 18 * w + 9]?).map Fin.val = _
      rw [hdt, hdb69, ← h6_68, Array.getElem?_set_self hLt68, Option.map_some, h4_68]
      by_cases h : p1 = a
      · simp [slot, h]
      · by_cases h' : p1 = b <;> simp [slot, h, h', Ne.symm hNe]
  have hSteps : Steps code input (15 + 1 + kT1 + 2) s63 t :=
    ((hs64.append (hs65.append hs66)).append hs67).append (hs68.append (hs69.append ht))
  exact ⟨_, t, by omega, hSteps, by rw [hpct, hpc69, hpc68], h0T, h1T, hMT, hOne, hFr⟩

theorem step4B_writeParent_spec {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hWriteFirst : Placed code (basePc + 624) (step4BOneNode_writeFirst basePc h100))
    (hWriteSecond : Placed code (basePc + 664) (step4BOneNode_writeSecond basePc h100))
    (hSz : basePc + 703 < code.size)
    (n m N w a b p0 p1 : Nat) (hwLt : w < N) (hNe : a ≠ b)
    (hBoundMeta : metaArrBase n m N + 64 ≤ workCap)
    (c : Values) (s53 : State DomL) (hpc53 : s53.pc = basePc + 624)
    (h0_53 : (reg s53 reg0).val = 0) (h1_53 : (reg s53 reg1).val = 1)
    (hM_53 : (reg s53 rMeta).val = metaArrBase n m N)
    (h50 : (s53.data[metaArrBase n m N + 50]?).map Fin.val = some a)
    (h51 : (s53.data[metaArrBase n m N + 51]?).map Fin.val = some b)
    (h52 : (s53.data[metaArrBase n m N + 52]?).map Fin.val = some p0)
    (h53 : (s53.data[metaArrBase n m N + 53]?).map Fin.val = some p1)
    (h55 : (s53.data[metaArrBase n m N + 55]?).map Fin.val = some (storedBase N + 18 * w))
    (hC53 : ValuesWordsAt s53.data (metaArrBase n m N + mIdxAcc0) c) :
    let slot := fun (s : Nat) => if s = a then some (0 : Fin 2) else if s = b then some 1 else none
    ∃ k t, k ≤ 73 ∧ Steps code input k s53 t ∧ t.pc = basePc + 703 ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaArrBase n m N ∧
      MapWordsAt t.data (storedBase N + 18 * w + 2) ⟨⟨c.x0, slot p0⟩, ⟨c.x1, slot p1⟩⟩ ∧
      (∀ j, (j < storedBase N + 18 * w + 2 ∨ storedBase N + 18 * w + 10 ≤ j) →
        t.data[j]? = s53.data[j]?) := by
  intro slot
  let metaBase := metaArrBase n m N
  have hMetaEq : metaBase = 20 * N + 10 * n + m + 1 := metaArrBase_eq n m N
  change metaBase + 64 ≤ workCap at hBoundMeta
  -- Step 624..702: write `parentMap` into `storedBase N + 18 * w + 2 .. +9`!
  obtain ⟨k0, s63, hk0, hs0, hpc63, h0_63, h1_63, hM_63, h2_63, hc0, hf0⟩ :=
    step4B_writeParent0_spec (input := input) basePc h100 hWriteFirst hWriteSecond hSz
      n m N w a b p0 hwLt hNe hBoundMeta c.x0 s53 hpc53 h0_53 h1_53 hM_53 h50 h51 h52 h55 hC53.1
  have hBelow : storedBase N + 18 * w + 6 ≤ metaBase := by unfold storedBase; omega
  have hUpper (k : Nat) : s63.data[metaBase + k]? = s53.data[metaBase + k]? :=
    hf0 _ (Or.inr (Nat.le_trans hBelow (Nat.le_add_right _ _)))
  have hAcc : IntervalWordsAt s63.data (metaBase + 33) c.x1 :=
    intervalWordsAt_frame (fun i _ => by rw [Nat.add_assoc]; exact hUpper (33 + i)) hC53.2
  obtain ⟨k1, t, hk1, hs1, hpcT, h0T, h1T, hMT, hc1, hf1⟩ :=
    step4B_writeParent1_spec (input := input) basePc h100 hWriteSecond hSz
      n m N w a b p1 hwLt hNe hBoundMeta c.x1 s63 hpc63 h0_63 h1_63 hM_63
      (by rw [hUpper 50]; exact h50) (by rw [hUpper 51]; exact h51)
      (by rw [hUpper 53]; exact h53) h2_63 hAcc
  exact ⟨k0 + k1, t, by omega, hs0.append hs1, hpcT, h0T, h1T, hMT,
    ⟨coordWordsAt_frame (fun i hi => hf1 _ (Or.inl (by omega))) hc0, hc1⟩,
    fun j hj => (hf1 j (by rcases hj with h | h <;> omega)).trans
      (hf0 j (by rcases hj with h | h <;> omega))⟩

end PaperB.RamProgram.ExitSummaryBuild
