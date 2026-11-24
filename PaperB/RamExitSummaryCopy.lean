module

public import PaperB.RamExitSummarySlices

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

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

/-! The fixed 22-instruction copy of an encoded pair of intervals. -/

section Defs

variable {bits : Nat}

def copy6Instrs (dst src tmp : Fin 15) : List (Instr bits 15) :=
  [ .loadData tmp src
  , .storeData dst tmp
  , .add src src reg1
  , .add dst dst reg1
  , .loadData tmp src
  , .storeData dst tmp
  , .add src src reg1
  , .add dst dst reg1
  , .loadData tmp src
  , .storeData dst tmp
  , .add src src reg1
  , .add dst dst reg1
  , .loadData tmp src
  , .storeData dst tmp
  , .add src src reg1
  , .add dst dst reg1
  , .loadData tmp src
  , .storeData dst tmp
  , .add src src reg1
  , .add dst dst reg1
  , .loadData tmp src
  , .storeData dst tmp
  ]

theorem copy6Instrs_length (dst src tmp : Fin 15) :
    (copy6Instrs (bits := bits) dst src tmp).length = 22 := rfl

theorem copy6Instrs_nonHalt (dst src tmp : Fin 15) :
    (copy6Instrs (bits := bits) dst src tmp).all sliceNonHalt = true := by
  rfl

end Defs

section Specs

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private theorem set_eq_after_transport {α : Type} {before after : Array α}
    {i : Nat} {value : α} (hBefore : i < before.size) (hAfter : i < after.size)
    (h : before = after) : before.set i value hBefore = after.set i value hAfter := by
  subst after
  rfl

theorem run_copy6 {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (dst src tmp : Fin 15)
    (hNe1 : dst ≠ src) (hNe2 : dst ≠ tmp) (hNe3 : src ≠ tmp)
    (hNe01 : dst ≠ reg1) (hNe02 : src ≠ reg1) (hNe03 : tmp ≠ reg1)
    (hPl : Placed code basePc (copy6Instrs (bits := bits) dst src tmp))
    (hSz : basePc + 22 < code.size)
    (srcBase dstBase : Nat) (xs : Values)
    (hFitS : srcBase + 5 < 2 ^ bits) (hFitD : dstBase + 5 < 2 ^ bits)
    (hDstLt : dstBase + 5 < workCap)
    (hDisj : dstBase + 6 ≤ srcBase ∨ srcBase + 6 ≤ dstBase)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr1 : (reg st reg1).val = 1)
    (hrS : (reg st src).val = srcBase) (hrD : (reg st dst).val = dstBase)
    (hXs : ValuesWordsAt st.data srcBase xs) :
    ∃ t : State DomL, Steps code input 22 st t ∧ t.pc = basePc + 22 ∧
      ValuesWordsAt t.data dstBase xs ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ src → r ≠ tmp → reg t r = reg st r) ∧
      (∀ j, (j < dstBase ∨ dstBase + 6 ≤ j) → t.data[j]? = st.data[j]?) := by
  have intervalRead {a : Nat} {x : Interval} (hx : IntervalWordsAt st.data a x)
      (i : Nat) (hi : i < 3) : ∃ w : Word bits, st.data[a + i]? = some w := by
    cases x <;> simp only [IntervalWordsAt] at hx
    all_goals
      obtain ⟨h0, h1, h2⟩ := hx
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      · obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.mp h0
        exact ⟨w, by simpa using hw⟩
      · obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.mp h1
        exact ⟨w, hw⟩
      · obtain ⟨w, hw, _⟩ := Option.map_eq_some_iff.mp h2
        exact ⟨w, hw⟩
  have hAt : ∀ i < 6, ∃ w : Word bits, st.data[srcBase + i]? = some w := by
    intro i hi
    by_cases h : i < 3
    · exact intervalRead hXs.1 i h
    · have hAddr : srcBase + i = (srcBase + 3) + (i - 3) := by omega
      rw [hAddr]
      exact intervalRead hXs.2 (i - 3) (by omega)
  have hCopyOne : ∀ (idx : Nat) (hIdx : idx < 5) (pc : Nat) (s : State DomL)
      (hPl4 : Placed code pc [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1])
      (hSz4 : pc + 4 < code.size) (hpcS : s.pc = pc)
      (h1S : (reg s reg1).val = 1) (hSS : (reg s src).val = srcBase + idx) (hDS : (reg s dst).val = dstBase + idx)
      (hMemS : ∀ k, (srcBase + idx ≤ k ∧ k < srcBase + 6) → s.data[k]? = st.data[k]?),
      ∃ s' : State DomL, Steps code input 4 s s' ∧ s'.pc = pc + 4 ∧
        (reg s' reg1).val = 1 ∧ (reg s' src).val = srcBase + (idx + 1) ∧ (reg s' dst).val = dstBase + (idx + 1) ∧
        (∀ r : Fin 15, r ≠ dst → r ≠ src → r ≠ tmp → reg s' r = reg s r) ∧
        (s'.data[dstBase + idx]?).map Fin.val = (st.data[srcBase + idx]?).map Fin.val ∧
        (∀ j, j ≠ dstBase + idx → s'.data[j]? = s.data[j]?) := by
    intro idx hIdx pc s hPl4 hSz4 hpcS h1S hSS hDS hMemS
    obtain ⟨w, hw⟩ := hAt idx (by omega)
    have hm : s.data[(reg s src).val]? = some w := by rw [hSS, hMemS _ ⟨by omega, by omega⟩]; exact hw
    obtain ⟨s1, hs1, hpc1, htmp1, ho1, hd1⟩ := step_loadData_at (input := input)
      (by rw [hpcS]; exact hPl4 0 _ rfl) (by omega) hm
    have hD1 : (reg s1 dst).val = dstBase + idx := by rw [ho1 dst hNe2, hDS]
    have hLt1 : (reg s1 dst).val < s1.data.size := lt_data_size (by rw [hD1]; omega)
    obtain ⟨s2, hs2, hpc2, hr2, hd2⟩ := step_storeData_opaque (input := input)
      (by rw [hpc1, hpcS]; exact hPl4 1 _ rfl) hLt1 (by omega)
    have hr2F := reg_of_regs_eq hr2
    have hS2 : (reg s2 src).val = srcBase + idx := by rw [hr2F, ho1 src hNe3, hSS]
    have h1_2 : (reg s2 reg1).val = 1 := by rw [hr2F, ho1 reg1 hNe03.symm, h1S]
    obtain ⟨s3, hs3, hpc3, hS3, ho3, hd3⟩ := step_add_at (input := input)
      (by rw [hpc2, hpc1, hpcS]; exact hPl4 2 _ rfl) (by omega)
    have hD3 : (reg s3 dst).val = dstBase + idx := by rw [ho3 dst hNe1, hr2F, hD1]
    have h1_3 : (reg s3 reg1).val = 1 := by rw [ho3 reg1 hNe02.symm, h1_2]
    obtain ⟨s4, hs4, hpc4, hD4, ho4, hd4⟩ := step_add_at (input := input)
      (by rw [hpc3, hpc2, hpc1, hpcS]; exact hPl4 3 _ rfl) (by omega)
    have hS3V : (reg s3 src).val = srcBase + (idx + 1) := by
      rw [hS3, add_no_wrap _ _ (by rw [hS2, h1_2]; omega), hS2, h1_2]; omega
    have hD4V : (reg s4 dst).val = dstBase + (idx + 1) := by
      rw [hD4, add_no_wrap _ _ (by rw [hD3, h1_3]; omega), hD3, h1_3]; omega
    have hLt1S : (reg s1 dst).val < s.data.size := by rw [← hd1]; exact hLt1
    have hData4 : s4.data = s.data.set (reg s1 dst).val (reg s1 tmp) hLt1S := by
      rw [hd4, hd3, hd2]
      exact set_eq_after_transport hLt1 hLt1S hd1
    refine ⟨s4, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (steps_1_of_step hs4))),
      by omega, by rw [ho4 reg1 hNe01.symm, h1_3],
      by rw [ho4 src hNe1.symm, hS3V], hD4V,
      fun r hrd hrs hrt => by rw [ho4 r hrd, ho3 r hrs, hr2F, ho1 r hrt],
      ?_, fun j hj => by rw [hData4, Array.getElem?_set_ne hLt1S (by rw [hD1]; exact hj.symm)]⟩
    rw [hData4, ← hD1, Array.getElem?_set_self hLt1S, Option.map_some, hw, Option.map_some, htmp1]
  have hPl0 : Placed code basePc [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] := by
    intro i op hi; exact hPl i op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi | 3 => exact hi)
  have hPl4 : Placed code (basePc + 4) [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (4 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi | 3 => exact hi)
  have hPl8 : Placed code (basePc + 8) [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (8 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi | 3 => exact hi)
  have hPl12 : Placed code (basePc + 12) [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (12 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi | 3 => exact hi)
  have hPl16 : Placed code (basePc + 16) [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (16 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi | 3 => exact hi)
  obtain ⟨s1, hs1, hpc1, h1_1, hS1, hD1, hP1, hAt0, hFr1⟩ :=
    hCopyOne 0 (by decide) basePc st hPl0 (by omega) hpc hr1 (by simpa using hrS) (by simpa using hrD) (fun _ _ => rfl)
  obtain ⟨s2, hs2, hpc2, h1_2, hS2, hD2, hP2, hAt1, hFr2⟩ :=
    hCopyOne 1 (by decide) (basePc + 4) s1 hPl4 (by omega) hpc1 h1_1 hS1 hD1
      (fun k hk => by rw [hFr1 k (by rcases hDisj with h | h <;> omega)])
  obtain ⟨s3, hs3, hpc3, h1_3, hS3, hD3, hP3, hAt2, hFr3⟩ :=
    hCopyOne 2 (by decide) (basePc + 8) s2 hPl8 (by omega) hpc2 h1_2 hS2 hD2
      (fun k hk => by rw [hFr2 k (by rcases hDisj with h | h <;> omega), hFr1 k (by rcases hDisj with h | h <;> omega)])
  obtain ⟨s4, hs4, hpc4, h1_4, hS4, hD4, hP4, hAt3, hFr4⟩ :=
    hCopyOne 3 (by decide) (basePc + 12) s3 hPl12 (by omega) hpc3 h1_3 hS3 hD3
      (fun k hk => by rw [hFr3 k (by rcases hDisj with h | h <;> omega), hFr2 k (by rcases hDisj with h | h <;> omega), hFr1 k (by rcases hDisj with h | h <;> omega)])
  obtain ⟨s5, hs5, hpc5, h1_5, hS5, hD5, hP5, hAt4, hFr5⟩ :=
    hCopyOne 4 (by decide) (basePc + 16) s4 hPl16 (by omega) hpc4 h1_4 hS4 hD4
      (fun k hk => by rw [hFr4 k (by rcases hDisj with h | h <;> omega), hFr3 k (by rcases hDisj with h | h <;> omega), hFr2 k (by rcases hDisj with h | h <;> omega), hFr1 k (by rcases hDisj with h | h <;> omega)])
  obtain ⟨w5, hw5⟩ := hAt 5 (by decide)
  have hm5 : s5.data[(reg s5 src).val]? = some w5 := by
    rw [hS5, hFr5 _ (by rcases hDisj with h | h <;> omega), hFr4 _ (by rcases hDisj with h | h <;> omega),
      hFr3 _ (by rcases hDisj with h | h <;> omega), hFr2 _ (by rcases hDisj with h | h <;> omega),
      hFr1 _ (by rcases hDisj with h | h <;> omega)]; exact hw5
  obtain ⟨s6, hs6, hpc6, htmp6, ho6, hd6⟩ := step_loadData_at (input := input)
    (by rw [hpc5]; exact hPl 20 _ rfl) (by omega) hm5
  have hD6 : (reg s6 dst).val = dstBase + 5 := by rw [ho6 dst hNe2, hD5]
  have hLt6 : (reg s6 dst).val < s6.data.size := lt_data_size (by rw [hD6]; omega)
  obtain ⟨t, hst, hpct, hrt, hdt⟩ := step_storeData_opaque (input := input)
    (by rw [hpc6, hpc5]; exact hPl 21 _ rfl) hLt6 (by omega)
  have hrTF := reg_of_regs_eq hrt
  have hAtT : ∀ a, (t.data[a]?).map Fin.val =
      if a = dstBase + 5 then (st.data[srcBase + 5]?).map Fin.val
      else if a = dstBase + 4 then (st.data[srcBase + 4]?).map Fin.val
      else if a = dstBase + 3 then (st.data[srcBase + 3]?).map Fin.val
      else if a = dstBase + 2 then (st.data[srcBase + 2]?).map Fin.val
      else if a = dstBase + 1 then (st.data[srcBase + 1]?).map Fin.val
      else if a = dstBase then (st.data[srcBase]?).map Fin.val
      else (st.data[a]?).map Fin.val := fun a => by
    rw [hdt]
    by_cases ha5 : a = dstBase + 5
    · subst ha5; rw [ite_eq_left rfl, ← hD6, Array.getElem?_set_self hLt6, Option.map_some, htmp6, hw5, Option.map_some]
    · rw [ite_eq_right ha5, Array.getElem?_set_ne hLt6 (by rw [hD6]; exact Ne.symm ha5), hd6]
      by_cases ha4 : a = dstBase + 4
      · subst ha4; rw [ite_eq_left rfl]; exact hAt4
      · rw [ite_eq_right ha4, hFr5 a ha4]
        by_cases ha3 : a = dstBase + 3
        · subst ha3; rw [ite_eq_left rfl]; exact hAt3
        · rw [ite_eq_right ha3, hFr4 a ha3]
          by_cases ha2 : a = dstBase + 2
          · subst ha2; rw [ite_eq_left rfl]; exact hAt2
          · rw [ite_eq_right ha2, hFr3 a ha2]
            by_cases ha1 : a = dstBase + 1
            · subst ha1; rw [ite_eq_left rfl]; exact hAt1
            · rw [ite_eq_right ha1, hFr2 a ha1]
              by_cases ha0 : a = dstBase
              · subst ha0; rw [ite_eq_left rfl]; simpa using hAt0
              · rw [ite_eq_right ha0, hFr1 a ha0]
  have hFrT : ∀ j, (j < dstBase ∨ dstBase + 6 ≤ j) → t.data[j]? = st.data[j]? := fun j hj => by
    rw [hdt, Array.getElem?_set_ne hLt6 (by rw [hD6]; rcases hj with h | h <;> omega), hd6,
      hFr5 j (by rcases hj with h | h <;> omega), hFr4 j (by rcases hj with h | h <;> omega),
      hFr3 j (by rcases hj with h | h <;> omega), hFr2 j (by rcases hj with h | h <;> omega),
      hFr1 j (by rcases hj with h | h <;> omega)]
  have intervalTransfer {a b : Nat} {x : Interval}
      (hEq : ∀ i < 3, (t.data[a + i]?).map Fin.val = (st.data[b + i]?).map Fin.val)
      (hx : IntervalWordsAt st.data b x) : IntervalWordsAt t.data a x := by
    have h0 : (t.data[a]?).map Fin.val = (st.data[b]?).map Fin.val := by
      simpa using hEq 0 (by decide)
    have h1 := hEq 1 (by decide)
    have h2 := hEq 2 (by decide)
    cases x <;> simp only [IntervalWordsAt, h0, h1, h2] <;> exact hx
  have hWords : ValuesWordsAt t.data dstBase xs := by
    refine ⟨intervalTransfer ?_ hXs.1, intervalTransfer ?_ hXs.2⟩
    all_goals
      intro i hi
      rcases (show i = 0 ∨ i = 1 ∨ i = 2 by omega) with rfl | rfl | rfl
      all_goals
        rw [hAtT]
        simp (disch := omega) [Nat.add_assoc]
  have hSteps22 : Steps code input 22 st t :=
    hs1.append (hs2.append (hs3.append (hs4.append
      (hs5.append (Steps.cons hs6 (steps_1_of_step hst))))))
  exact ⟨t, hSteps22, by omega, hWords, fun r hrd hrs hrt => by
    rw [hrTF r, ho6 r hrt, hP5 r hrd hrs hrt, hP4 r hrd hrs hrt, hP3 r hrd hrs hrt,
      hP2 r hrd hrs hrt, hP1 r hrd hrs hrt], hFrT⟩

end Specs

end PaperB.RamProgram.ExitSummaryBuild
