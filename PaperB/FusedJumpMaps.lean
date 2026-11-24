module

public import PaperB.ActualJumpMaps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.CheckedFold
open JumpForest

/-- Choose from the record already read at the current node. The jump is
taken on equality, just as in `stepToDepth`. -/
@[inline] def selectAtDepth (depth : Nat → Nat) (d : Nat)
    (r : Stored) : Selected :=
  r.select (if d ≤ depth r.jump then Move.jump else Move.parent)

private theorem selectAtDepth_eq_traceSelect
    {F : JumpForest} {read : Store} (ok : StoreOK F read) (u d : Nat) :
    selectAtDepth F.depthOf d (read u) =
      (read u).select (kind (F.stepMoveToDepth u d)) := by
  by_cases h : d ≤ F.depthOf (F.jumpOf u) <;>
    simp [selectAtDepth, JumpForest.stepMoveToDepth, kind, ok.jump_eq u, h]

private theorem traceSelect_dst
    {F : JumpForest} {read : Store} (ok : StoreOK F read) (u d : Nat) :
    ((read u).select (kind (F.stepMoveToDepth u d))).dst =
      F.stepToDepth u d := by
  by_cases h : d ≤ F.depthOf (F.jumpOf u) <;>
    simp [JumpForest.stepMoveToDepth, JumpForest.stepToDepth, kind,
      Stored.select, ok.jump_eq u, ok.parent_eq u, h]

/-- The only changing arguments are `u`, `acc`, and `steps`. The budget is
fixed, so the step counter also serves as the fuel check. Each taken
iteration reads one record, selects one map, and composes once. Neither
halt branch reads the store. -/
def foldFusedAux (depth : Nat → Nat) (read : Store) (d budget : Nat)
    (u : Nat) (acc : Map) (steps : Nat) : Result :=
  if h : steps < budget ∧ d < depth u then
    let r := read u
    let e := selectAtDepth depth d r
    foldFusedAux depth read d budget e.dst (Map.compose acc e.map) (steps + 1)
  else
    ⟨u, acc, steps⟩
termination_by budget - steps
decreasing_by omega

def foldFused (F : JumpForest) (read : Store) (u d : Nat) : Result :=
  foldFusedAux F.depthOf read d (F.depthOf u - d) u Map.identity 0

/-- The fixed-register transition. The packed states in this equation
are proof notation; the executable worker passes the three fields directly. -/
theorem foldFusedAux_registers (depth : Nat → Nat) (read : Store)
    (d budget : Nat) (s : Result) :
    foldFusedAux depth read d budget s.stop s.composed s.steps =
      if s.steps < budget ∧ d < depth s.stop then
        let e := selectAtDepth depth d (read s.stop)
        let next : Result :=
          ⟨e.dst, Map.compose s.composed e.map, s.steps + 1⟩
        foldFusedAux depth read d budget next.stop next.composed next.steps
      else
        s := by
  cases s with
  | mk u acc steps =>
    conv =>
      lhs
      rw [foldFusedAux]
    by_cases h : steps < budget ∧ d < depth u
    · exact Eq.trans (dite_eq_left h) (Eq.symm (ite_eq_left h))
    · exact Eq.trans (dite_eq_right h) (Eq.symm (ite_eq_right h))

/-- The trace occurs only in the specification. `fuel` is the reference
loop's remaining fuel, not an extra runtime register. -/
theorem foldFusedAux_eq_foldAux {F : JumpForest} {read : Store}
    (ok : StoreOK F read) (d budget fuel u : Nat) (acc : Map) (steps : Nat)
    (hf : budget - steps = fuel) :
    foldFusedAux F.depthOf read d budget u acc steps =
      foldAux kind read (F.traceMovesAux fuel u d) u acc steps := by
  induction fuel generalizing u acc steps with
  | zero =>
    have hg : ¬ (steps < budget ∧ d < F.depthOf u) := by omega
    conv =>
      lhs
      rw [foldFusedAux]
    conv =>
      rhs
      rw [JumpForest.traceMovesAux_zero]
    simp only [dite_eq_right hg, foldAux]
  | succ fuel ih =>
    conv =>
      lhs
      rw [foldFusedAux]
    conv =>
      rhs
      rw [JumpForest.traceMovesAux_succ]
    by_cases hl : d < F.depthOf u
    · have hb : steps < budget := by omega
      have hg : steps < budget ∧ d < F.depthOf u := ⟨hb, hl⟩
      have hn : budget - (steps + 1) = fuel := by omega
      simp only [dite_eq_left hg, ite_eq_left hl, foldAux,
        selectAtDepth_eq_traceSelect ok u d, traceSelect_dst ok u d]
      exact ih (F.stepToDepth u d) _ (steps + 1) hn
    · have hg : ¬ (steps < budget ∧ d < F.depthOf u) :=
        fun h => hl h.2
      simp only [dite_eq_right hg, ite_eq_right hl, foldAux]

/-- Equality includes the stopping node, the whole composed map, and the
counter. The executable definition does not call `foldTrace`. -/
theorem foldFused_eq_foldTrace {F : JumpForest} {read : Store}
    (ok : StoreOK F read) (u d : Nat) :
    foldFused F read u d = foldTrace F read u d := by
  unfold foldFused foldTrace fold JumpForest.traceMoves
  exact foldFusedAux_eq_foldAux ok d (F.depthOf u - d)
    (F.depthOf u - d) u Map.identity 0 (Nat.sub_zero _)

theorem foldFused_cost {F : JumpForest} {read : Store}
    (ok : StoreOK F read) (hF : ValidJumpForest F) {u n : Nat}
    (hu : u < F.size) (hInserted : F.numInserted ≤ n) (d : Nat) :
    let L := (F.traceMoves u d).length
    let B := 3 * ceilLog2 (n + 2)
    (foldFused F read u d).steps = L ∧ L ≤ B ∧
      2 * (foldFused F read u d).steps ≤ 2 * B := by
  simpa only [foldFused_eq_foldTrace ok u d] using
    (foldTrace_cost read hF hu hInserted d)

theorem foldFused_steps_le {F : JumpForest} {read : Store}
    (ok : StoreOK F read) (hF : ValidJumpForest F) {u n : Nat}
    (hu : u < F.size) (hInserted : F.numInserted ≤ n) (d : Nat) :
    (foldFused F read u d).steps ≤ 3 * ceilLog2 (n + 2) := by
  obtain ⟨hs, hl, _⟩ := foldFused_cost ok hF hu hInserted d
  exact hs ▸ hl

end PaperB.ExitMap.JumpMapRoute
