module

public import PaperB.RamExitSummarySweepBROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 450000

/-! Copy a map record through a fixed unrolled sequence of word loads and stores. -/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB PaperB.RamProgram PaperB.RamForestProgram
open PaperB.Machine (Word)
open PaperB.WordOps (add_no_wrap)
open PaperB.ExitMap

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private def copyWordsInstrs (dst src tmp : Fin 15) : Nat → List (Instr bits 15)
  | 0 => [.loadData tmp src, .storeData dst tmp]
  | k + 1 => [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] ++
    copyWordsInstrs dst src tmp k

private theorem copyWord_head {code : Program DomL} {input : Input DomL}
    {pc srcBase dstBase : Nat} {dst src tmp : Fin 15}
    (hDstTmp : dst ≠ tmp)
    (hPlaced : Placed code pc [.loadData tmp src, .storeData dst tmp])
    (hSize : pc + 2 < code.size)
    (s : State DomL) (hs : s.pc = pc)
    (hSrc : (reg s src).val = srcBase) (hDst : (reg s dst).val = dstBase)
    (hDstLt : dstBase < workCap) (w : Word bits) (hAt : s.data[srcBase]? = some w) :
    ∃ t, Steps code input 2 s t ∧ t.pc = pc + 2 ∧ t.data[dstBase]? = some w ∧
      (∀ j, j ≠ dstBase → t.data[j]? = s.data[j]?) ∧
      (∀ r, r ≠ tmp → reg t r = reg s r) := by
  obtain ⟨a, ha, hpcA, hrA, hRegsA, hdA⟩ := step_loadData_at (input := input)
    (by rw [hs]; exact hPlaced 0 _ rfl) (by omega) (by rw [hSrc]; exact hAt)
  have hAddr : (reg a dst).val = dstBase := by rw [hRegsA dst hDstTmp, hDst]
  have hAddrLt : (reg a dst).val < a.data.size := by rw [hAddr]; exact lt_data_size hDstLt
  obtain ⟨t, ht, hpcT, hRegsT, hdT⟩ := step_storeData_opaque (input := input)
    (by rw [hpcA, hs]; exact hPlaced 1 _ rfl) hAddrLt (by omega)
  refine ⟨t, Steps.cons ha (steps_1_of_step ht), by omega, ?_, ?_, ?_⟩
  · rw [hdT, ← hAddr, Array.getElem?_set_self, hrA]
  · intro j hj
    rw [hdT, Array.getElem?_set_ne hAddrLt (by rw [hAddr]; exact hj.symm), hdA]
  · intro r hr
    rw [reg_of_regs_eq hRegsT, hRegsA r hr]

private theorem copyWords_run {code : Program DomL} {input : Input DomL}
    {dst src tmp : Fin 15} (hDS : dst ≠ src) (hDT : dst ≠ tmp) (hST : src ≠ tmp)
    (hD1 : dst ≠ reg1) (hS1 : src ≠ reg1) (hT1 : tmp ≠ reg1) :
    ∀ (k pc srcBase dstBase : Nat),
      Placed code pc (copyWordsInstrs dst src tmp k) →
      pc + (4 * k + 2) < code.size →
      srcBase + k < 2 ^ bits → dstBase + k < workCap →
      (srcBase + k + 1 ≤ dstBase ∨ dstBase + k + 1 ≤ srcBase) →
      ∀ s : State DomL, s.pc = pc →
      (reg s reg1).val = 1 →
      (reg s src).val = srcBase → (reg s dst).val = dstBase →
      (∀ i ≤ k, ∃ w : Word bits, s.data[srcBase + i]? = some w) →
      ∃ t, Steps code input (4 * k + 2) s t ∧ t.pc = pc + (4 * k + 2) ∧
        (∀ i ≤ k, t.data[dstBase + i]? = s.data[srcBase + i]?) ∧
        (∀ j, (j < dstBase ∨ dstBase + k < j) → t.data[j]? = s.data[j]?) ∧
        (∀ r, r ≠ dst → r ≠ src → r ≠ tmp → reg t r = reg s r) := by
  intro k
  induction k with
  | zero =>
    intro pc srcBase dstBase hPl hSz hSF hDF _ s hpc _ hSrc hDst hData
    obtain ⟨w, hwAt⟩ := hData 0 (by decide)
    have hAt : s.data[srcBase]? = some w := by simpa only [Nat.add_zero] using hwAt
    obtain ⟨t, ht, hpcT, hAtT, hFrT, hrT⟩ := copyWord_head (input := input)
      hDT hPl hSz s hpc hSrc hDst (by omega) w hAt
    refine ⟨t, ht, hpcT, ?_, ?_, fun r _ _ hr => hrT r hr⟩
    · intro i hI
      have hi0 : i = 0 := by omega
      simp only [hi0, Nat.add_zero, hAtT, hAt]
    · intro j hj
      exact hFrT j (by omega)
  | succ k ih =>
    intro pc srcBase dstBase hPl hSz hSF hDF hDisj s hpc hOne hSrc hDst hData
    have hPrefix : Placed code pc
        [.loadData tmp src, .storeData dst tmp, .add src src reg1, .add dst dst reg1] :=
      Placed_append_left hPl
    obtain ⟨w, hwAt⟩ := hData 0 (by omega)
    have hAt : s.data[srcBase]? = some w := by simpa only [Nat.add_zero] using hwAt
    have hPlacedCopy : Placed code pc [.loadData tmp src, .storeData dst tmp] := by
      apply Placed_append_left (b := [.add src src reg1, .add dst dst reg1]) hPrefix
    obtain ⟨a, ha, hpcA, hAtA, hFrA, hRegsA⟩ := copyWord_head (input := input)
      hDT hPlacedCopy (by omega) s hpc hSrc hDst (by omega) w hAt
    obtain ⟨b, hb, hpcB, hSrcB, hRegsB, hdB⟩ := step_add_at (input := input)
      (by rw [hpcA]; exact hPrefix 2 _ rfl) (by omega)
    have hSA : (reg a src).val = srcBase := by rw [hRegsA src hST, hSrc]
    have hOneA : (reg a reg1).val = 1 := by rw [hRegsA reg1 hT1.symm, hOne]
    have hSB : (reg b src).val = srcBase + 1 := by
      rw [hSrcB, add_no_wrap _ _ (by rw [hSA, hOneA]; omega), hSA, hOneA]
    obtain ⟨c, hc, hpcC, hDstC, hRegsC, hdC⟩ := step_add_at (input := input)
      (by rw [hpcB, hpcA]; exact hPrefix 3 _ rfl) (by omega)
    have hDB : (reg b dst).val = dstBase := by rw [hRegsB dst hDS, hRegsA dst hDT, hDst]
    have hOneB : (reg b reg1).val = 1 := by rw [hRegsB reg1 hS1.symm, hOneA]
    have hDC : (reg c dst).val = dstBase + 1 := by
      rw [hDstC, add_no_wrap _ _ (by rw [hDB, hOneB]; omega), hDB, hOneB]
    have hPlTail : Placed code (pc + 4) (copyWordsInstrs dst src tmp k) :=
      Placed_append_right hPl
    obtain ⟨t, ht, hpcT, hSliceT, hFrT, hRegsT⟩ := ih (pc + 4) (srcBase + 1) (dstBase + 1)
      hPlTail (by omega) (by omega) (by omega) (by omega) c (by omega)
      (by rw [hRegsC reg1 hD1.symm, hOneB]) (by rw [hRegsC src hDS.symm, hSB]) hDC
      (fun i hI => by
        obtain ⟨v, hv⟩ := hData (i + 1) (by omega)
        refine ⟨v, ?_⟩
        rw [hdC, hdB, hFrA _ (by omega)]
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hv)
    have hTrace := ha.append (Steps.cons hb (Steps.cons hc ht))
    refine ⟨t, ?_, by omega, ?_, ?_, ?_⟩
    · have hTraceCount : 2 + (4 * k + 2 + 1 + 1) = 4 * (k + 1) + 2 := by omega
      change Steps code input (2 + (4 * k + 2 + 1 + 1)) s t at hTrace
      rwa [hTraceCount] at hTrace
    · intro i hI
      cases i with
      | zero =>
        rw [Nat.add_zero, Nat.add_zero, hFrT dstBase (Or.inl (by omega)), hdC, hdB, hAtA, hAt]
      | succ i =>
        have hEqD : dstBase + (i + 1) = dstBase + 1 + i := by omega
        have hEqS : srcBase + (i + 1) = srcBase + 1 + i := by omega
        rw [hEqD, hSliceT i (by omega), hdC, hdB, hFrA _ (by omega), ← hEqS]
    · intro j hj
      rw [hFrT j (by omega), hdC, hdB, hFrA j (by omega)]
    · intro r hd hs ht
      rw [hRegsT r hd hs ht, hRegsC r hd, hRegsB r hs, hRegsA r ht]

private theorem intervalWordsAt_copy {mem1 mem2 : Array (Word bits)} {a b : Nat} {x : Interval}
    (h : ∀ i < 3, mem2[b + i]? = mem1[a + i]?)
    (hx : IntervalWordsAt mem1 a x) : IntervalWordsAt mem2 b x := by
  have hZero := h 0 (by decide)
  rw [Nat.add_zero, Nat.add_zero] at hZero
  cases x <;> exact ⟨by rw [hZero]; exact hx.1, by rw [h 1 (by decide)]; exact hx.2.1,
    by rw [h 2 (by decide)]; exact hx.2.2⟩

private theorem coordWordsAt_copy {mem1 mem2 : Array (Word bits)} {a b : Nat} {c : Coord}
    (h : ∀ i < 4, mem2[b + i]? = mem1[a + i]?)
    (hc : CoordWordsAt mem1 a c) : CoordWordsAt mem2 b c :=
  ⟨intervalWordsAt_copy (fun i hi => h i (by omega)) hc.1, by rw [h 3 (by decide)]; exact hc.2⟩

theorem run_copy8 {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (dst src tmp : Fin 15)
    (hDS : dst ≠ src) (hDT : dst ≠ tmp) (hST : src ≠ tmp)
    (hD1 : dst ≠ reg1) (hS1 : src ≠ reg1) (hT1 : tmp ≠ reg1)
    (hPl : Placed code basePc (copy8Instrs (bits := bits) dst src tmp))
    (hSz : basePc + 30 < code.size)
    (srcBase dstBase : Nat) (m : Map)
    (hFitS : srcBase + 7 < 2 ^ bits) (_hFitD : dstBase + 7 < 2 ^ bits)
    (hDstLt : dstBase + 7 < workCap)
    (hDisj : dstBase + 8 ≤ srcBase ∨ srcBase + 8 ≤ dstBase)
    (st : State DomL) (hpc : st.pc = basePc)
    (hr1 : (reg st reg1).val = 1)
    (hrS : (reg st src).val = srcBase) (hrD : (reg st dst).val = dstBase)
    (hM : MapWordsAt st.data srcBase m) :
    ∃ t : State DomL, Steps code input 30 st t ∧ t.pc = basePc + 30 ∧
      MapWordsAt t.data dstBase m ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ src → r ≠ tmp → reg t r = reg st r) ∧
      (∀ j, (j < dstBase ∨ dstBase + 8 ≤ j) → t.data[j]? = st.data[j]?) := by
  have coordRead (addr : Nat) (c : Coord) (hc : CoordWordsAt st.data addr c) :
      ∀ i < 4, ∃ w : Word bits, st.data[addr + i]? = some w := by
    intro i hI
    have hBase := hc.1
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl
    · rw [Nat.add_zero]
      cases h : c.base <;> rw [h] at hBase <;> exact (Option.map_eq_some_iff.mp hBase.1).imp (fun _ hw => hw.1)
    · cases h : c.base <;> rw [h] at hBase <;> exact (Option.map_eq_some_iff.mp hBase.2.1).imp (fun _ hw => hw.1)
    · cases h : c.base <;> rw [h] at hBase <;> exact (Option.map_eq_some_iff.mp hBase.2.2).imp (fun _ hw => hw.1)
    · exact Option.map_eq_some_iff.mp hc.2 |>.imp fun _ hw => hw.1
  have hRead : ∀ i ≤ 7, ∃ w : Word bits, st.data[srcBase + i]? = some w := by
    intro i hi
    by_cases hI : i < 4
    · exact coordRead srcBase m.x0 hM.1 i hI
    · have hAddr : srcBase + i = srcBase + 4 + (i - 4) := by omega
      rw [hAddr]
      exact coordRead (srcBase + 4) m.x1 hM.2 (i - 4) (by omega)
  obtain ⟨t, ht, hpcT, hSlice, hFr, hRegs⟩ :=
    copyWords_run (input := input) hDS hDT hST hD1 hS1 hT1 7 basePc srcBase dstBase
      hPl hSz hFitS hDstLt (by omega) st hpc hr1 hrS hrD hRead
  refine ⟨t, ht, hpcT, ⟨?_, ?_⟩, hRegs, fun j hj => hFr j (by omega)⟩
  · exact coordWordsAt_copy (fun i hi => hSlice i (by omega)) hM.1
  · apply coordWordsAt_copy ?_ hM.2
    intro i hi
    rw [Nat.add_assoc, Nat.add_assoc]
    exact hSlice (4 + i) (by omega)

end PaperB.RamProgram.ExitSummaryBuild
