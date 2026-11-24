module

public import PaperB.RamForestProgram
public import PaperB.Jumps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.DepthSeek

open PaperB.RamProgram
open PaperB.Machine (Word)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- Read one field from the three-word jump records by reusing the
destination for address arithmetic. The field base already includes
the header and field offset. -/
def recordField {r : Nat} (dst base node : Fin r) : List (Instr bits r) :=
  [.add dst node node, .add dst dst node, .add dst base dst, .loadData dst dst]

theorem recordField_steps (input : Input L) {c : Program L} {pc : Nat}
    {dst base node : Fin 15} {s : State L}
    (placed : Placed c pc (recordField dst base node)) (atPC : s.pc = pc)
    (continuation : pc + 4 < c.size) (keepBase : base ≠ dst) (keepNode : node ≠ dst)
    (fits : (reg s base).val + 3 * (reg s node).val < workCap) :
    ∃ t, Steps c input 4 s t ∧ t.pc = pc + 4 ∧ t.data = s.data ∧
      s.data[(reg s base).val + 3 * (reg s node).val]? = some (reg t dst) ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  have f0 : c[s.pc]? = some (.add dst node node) := by
    rw [atPC]
    simpa only [Nat.add_zero] using (placed 0 _ rfl)
  obtain ⟨u, su, upc, uW, ur, um⟩ := step_add_at (input := input) f0 (by omega)
  have b0 : (reg s node).val + (reg s node).val < 2 ^ bits := by omega
  have val0 : (reg u dst).val = 2 * (reg s node).val := by
    rw [uW, PaperB.WordOps.add_no_wrap _ _ b0]
    omega
  have f1 : c[u.pc]? = some (.add dst dst node) := by rw [upc, atPC]; exact placed 1 _ rfl
  obtain ⟨v, uv, vpc, vW, vr, vm⟩ := step_add_at (input := input) f1 (by omega)
  have b1 : (reg u dst).val + (reg u node).val < 2 ^ bits := by
    rw [val0, ur _ keepNode]; omega
  have val1 : (reg v dst).val = 3 * (reg s node).val := by
    rw [vW, PaperB.WordOps.add_no_wrap _ _ b1, val0, ur _ keepNode]
    omega
  have f2 : c[v.pc]? = some (.add dst base dst) := by
    rw [vpc, upc, atPC, Nat.add_assoc]; exact placed 2 _ rfl
  obtain ⟨w, vw, wpc, wW, wr, wm⟩ := step_add_at (input := input) f2 (by omega)
  have sameBase : reg v base = reg s base := (vr _ keepBase).trans (ur _ keepBase)
  have b2 : (reg v base).val + (reg v dst).val < 2 ^ bits := by
    rw [sameBase, val1]; omega
  have address : (reg w dst).val = (reg s base).val + 3 * (reg s node).val := by
    rw [wW, PaperB.WordOps.add_no_wrap _ _ b2, sameBase, val1]
  have f3 : c[w.pc]? = some (.loadData dst dst) := by
    rw [wpc, vpc, upc, atPC, Nat.add_assoc, Nat.add_assoc]
    exact placed 3 _ rfl
  have dataEq : w.data = s.data := wm.trans (vm.trans um)
  have inBounds : (reg s base).val + 3 * (reg s node).val < s.data.size := by
    rw [s.data_size]
    exact fits
  let value := s.data[(reg s base).val + 3 * (reg s node).val]'inBounds
  have load : w.data[(reg w dst).val]? = some value := by
    rw [address, dataEq]
    exact getElem?_pos s.data ((reg s base).val + 3 * (reg s node).val) inBounds
  obtain ⟨t, wt, tpc, tValue, tr, tm⟩ := step_loadData_at (input := input) f3 load (by omega)
  refine ⟨t, .cons su (.cons uv (.cons vw (.cons wt (.zero t)))), by omega, tm.trans dataEq,
    ?_, fun r ne => (tr r ne).trans ((wr r ne).trans ((vr r ne).trans (ur r ne)))⟩
  rw [tValue]
  exact getElem?_pos s.data ((reg s base).val + 3 * (reg s node).val) inBounds

end PaperB.RamForestProgram.DepthSeek
