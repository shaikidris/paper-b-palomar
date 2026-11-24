module

public import PaperB.ExitScheduledRowMass
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace ListWork

universe u

variable {α : Type u}

def total (xs : List α) (cost : α → Nat) : Nat :=
  (xs.map cost).sum

private theorem total_cons (a : α) (xs : List α) (cost : α → Nat) :
    total (a :: xs) cost = cost a + total xs cost := by
  simp [total]

theorem total_affine_bound (xs : List α) (step items calls : α → Nat)
    (fixed perItem perCall : Nat)
    (h : ∀ a ∈ xs, step a ≤ fixed + perItem * items a + perCall * calls a) :
    total xs step ≤
      fixed * xs.length + perItem * total xs items + perCall * total xs calls := by
  induction xs with
  | nil => simp [total]
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [total_cons, List.length_cons, Nat.mul_succ, Nat.mul_add]
    omega

theorem total_affine_of_caps (xs : List α) (step items calls : α → Nat)
    (fixed perItem perCall itemCap callCap : Nat)
    (h : ∀ a ∈ xs, step a ≤ fixed + perItem * items a + perCall * calls a)
    (hItems : total xs items ≤ itemCap) (hCalls : total xs calls ≤ callCap) :
    total xs step ≤ fixed * xs.length + perItem * itemCap + perCall * callCap := by
  have hTotal := total_affine_bound xs step items calls fixed perItem perCall h
  have hi := Nat.mul_le_mul_left perItem hItems
  have hc := Nat.mul_le_mul_left perCall hCalls
  omega

end ListWork


namespace PaperB.EX24.InputPrepCheckpoint

/-- Aggregate the per-event charges against the actual raw row mass.
Work and fused-call charges refer to the event at the supplied schedule vertex. -/
theorem schedule_exit_charges_le (H : LabelledQuotient)
    {m : Nat} {P : _root_.EX42.ArraySweep.Plan H.vertexCount m}
    (S : _root_.EX42.ArraySweep.Schedule P)
    (work fusedCalls : Fin H.vertexCount → Nat) (fixed perArc perCall : Nat)
    (callBound : ∀ y, fusedCalls y ≤ ((ForestIncomingRaw.prepare H).1.row y).length + 2)
    (charge : ∀ y, work y ≤ fixed +
      perArc * ((ForestIncomingRaw.prepare H).1.row y).length + perCall * fusedCalls y) :
    ListWork.total (List.ofFn S.vertex) work ≤
      (fixed + perCall * 2) * H.vertexCount + (perArc + perCall) * H.arcCount := by
  let arcs y := ((ForestIncomingRaw.prepare H).1.row y).length
  have rows : ListWork.total (List.ofFn S.vertex) arcs ≤ H.arcCount := by
    simpa only [ListWork.total, arcs] using
      Nat.le_of_eq (schedule_raw_row_sum_eq_arcCount H S)
  have h := ListWork.total_affine_of_caps (List.ofFn S.vertex) work arcs arcs
    (fixed + perCall * 2) perArc perCall H.arcCount H.arcCount
    (by
      intro y _
      have hm := Nat.mul_le_mul_left perCall (callBound y)
      rw [Nat.mul_add] at hm
      dsimp only [arcs]
      exact Nat.le_trans (charge y) (by omega))
    rows rows
  simpa only [List.length_ofFn, Nat.add_assoc, ← Nat.add_mul] using h

end PaperB.EX24.InputPrepCheckpoint
