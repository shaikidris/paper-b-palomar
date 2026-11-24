module

public import PaperB.RamExitSummaryEvalROM

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

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

/-! The eight-instruction, read-only header for a jump-map evaluation. -/

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_eval15Header {code : Program DomL} {input : Input DomL}
    {basePc : Nat} {h100 : 100 ≤ 2 ^ bits}
    (hPl : Placed code basePc (eval15Instrs basePc h100))
    (hSz : basePc + 161 < code.size)
    {st : State DomL} {base u d depth : Nat}
    (hpc : st.pc = basePc) (hM : (reg st rMeta).val = base)
    (hFit : base + mIdxEvalD < 2 ^ bits)
    (hEvalU : (st.data[base + mIdxEvalU]?).map Fin.val = some u)
    (hEvalD : (st.data[base + mIdxEvalD]?).map Fin.val = some d)
    (hDepth : (st.data[u]?).map Fin.val = some depth) :
    ∃ t : State DomL, Steps code input 8 st t ∧
      t.pc = (if d < depth then basePc + 8 else basePc + 161) ∧
      t.data = st.data ∧ (reg t reg2).val = u ∧ (reg t reg4).val = d ∧
      (∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → reg t r = reg st r) := by
  have hPlU : Placed code basePc (metaLoadInstrs (bits := bits) reg2 reg5 mIdxEvalU (by dsimp only [mIdxEvalU]; omega)) := by
    intro i op hi; exact hPl i op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi)
  have hPlD : Placed code (basePc + 4) (metaLoadInstrs (bits := bits) reg4 reg5 mIdxEvalD (by dsimp only [mIdxEvalD]; omega)) := by
    intro i op hi; rw [Nat.add_assoc]; exact hPl (4 + i) op (by match i with | 0 => exact hi | 1 => exact hi | 2 => exact hi)
  have hFitU : base + mIdxEvalU < 2 ^ bits := by
    dsimp only [mIdxEvalU, mIdxEvalD] at hFit ⊢
    omega
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlU (by omega) hpc hM hFitU hEvalU
  obtain ⟨wDepU, hwDepU, hwDepUV⟩ := Option.map_eq_some_iff.mp hDepth
  obtain ⟨s2, hs2, hpc2, h3_2, ho2, hd2⟩ := step_loadData_at (input := input)
    (by rw [hpc1]; exact hPl 3 _ rfl) (by omega) (by rw [h2_1, hd1]; exact hwDepU)
  have hM2 : (reg s2 rMeta).val = base := by
    rw [ho2 rMeta (by intro h; cases h), ho1 rMeta (by intro h; cases h) (by intro h; cases h), hM]
  obtain ⟨s3, hs3, hpc3, hd3, h4_3, ho3⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlD (by omega) (by omega) hM2 hFit
    (by rw [hd2, hd1]; exact hEvalD)
  have hPres3 : ∀ r : Fin 15, r ≠ reg2 → r ≠ reg3 → r ≠ reg4 → r ≠ reg5 → reg s3 r = reg st r :=
    fun r hr2 hr3 hr4 hr5 => by rw [ho3 r hr4 hr5, ho2 r hr3, ho1 r hr2 hr5]
  have h2_3 : (reg s3 reg2).val = u := by
    rw [ho3 reg2 (by intro h; cases h) (by intro h; cases h),
      ho2 reg2 (by intro h; cases h), h2_1]
  have h3_3 : (reg s3 reg3).val = depth := by
    rw [ho3 reg3 (by intro h; cases h) (by intro h; cases h), h3_2, hwDepUV]
  have hd3' : s3.data = st.data := by rw [hd3, hd2, hd1]
  obtain ⟨s4, hs4, hpc4, hr4, hd4⟩ := step_branchLt_at (input := input)
    (by rw [hpc3]; exact hPl 7 _ rfl) (by split <;> omega)
  have hr4F := reg_of_regs_eq hr4
  have hPre8 : Steps code input 8 st s4 :=
    hs1.append (Steps.cons hs2 (hs3.append (steps_1_of_step hs4)))
  refine ⟨s4, hPre8, ?_, hd4.trans hd3', ?_, ?_, ?_⟩
  · rw [hpc4, h4_3, h3_3]
  · rw [hr4F, h2_3]
  · rw [hr4F, h4_3]
  · intro r hr2 hr3 hr4 hr5
    rw [hr4F, hPres3 r hr2 hr3 hr4 hr5]

end PaperB.RamProgram.ExitSummaryBuild
