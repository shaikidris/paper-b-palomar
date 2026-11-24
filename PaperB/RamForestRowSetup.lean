module

public import PaperB.RamForestProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram

open PaperB.RamProgram
open PaperB.WordOps (add_no_wrap sub_val)
open PaperB.Machine (Word)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private theorem subExact (a b : Word bits) (le : b.val ≤ a.val) :
    (PaperB.WordOps.sub a b).val = a.val - b.val := by
  have ha := a.isLt
  have fit : a.val - b.val < 2 ^ bits := by omega
  rw [sub_val, show 2 ^ bits + a.val - b.val = (a.val - b.val) + 2 ^ bits by omega,
    Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt fit]

/-- Read the two offsets for the current node. The six instructions leave
the child row's length and absolute start in the child-loop registers. -/
theorem prepareRow_steps (input : Input L) (s : State L)
    (pc : s.pc = 8) {lo stop : Word bits}
    (readStart : s.data[(reg s offsetBase).val + (reg s cmd).val]? = some lo)
    (readStop : s.data[(reg s offsetBase).val + (reg s cmd).val + 1]? = some stop)
    (offsetFits : (reg s offsetBase).val + (reg s cmd).val + 1 < workCap)
    (ordered : lo.val ≤ stop.val)
    (childFits : (reg s childrenBase).val + lo.val < 2 ^ bits)
    (one : (reg s registers.one).val = 1) :
    ∃ t, Steps (program hi hw) input 6 s t ∧ t.pc = 14 ∧
      (reg t registers.remain).val = stop.val - lo.val ∧
      (reg t registers.childBase).val = (reg s childrenBase).val + lo.val ∧
      t.data = s.data ∧
      (∀ r : Fin 15, r ≠ registers.tmp → r ≠ registers.value →
        r ≠ registers.remain → r ≠ registers.childBase → reg t r = reg s r) := by
  let code := program hi hw
  have cap : code.size = 32 := program_size (hi := hi) (hw := hw)
  let ix := (reg s offsetBase).val + (reg s cmd).val
  have nextFit : ix + 1 < 2 ^ bits := Nat.lt_of_lt_of_le offsetFits hw
  have ixFits : ix < 2 ^ bits := by omega
  have p := row_setup_placed (hi := hi) (hw := hw)
  have h₀ : code[s.pc]? = some (.add registers.tmp offsetBase cmd) := by
    rw [pc]
    exact p 0 _ rfl
  obtain ⟨a, sa, pa, aWord, ar, aData⟩ := step_add_at (input := input) h₀ (by omega)
  have aIx : (reg a registers.tmp).val = ix := by
    rw [aWord, add_no_wrap _ _ ixFits]
  have h₁ : code[a.pc]? = some (.loadData registers.value registers.tmp) := by
    rw [show a.pc = 9 by omega]
    exact p 1 _ rfl
  have aLoad : a.data[(reg a registers.tmp).val]? = some lo := by
    rw [aData, aIx]
    exact readStart
  obtain ⟨b, ab, pb, bLo, br, bData⟩ := step_loadData_at (input := input) h₁ aLoad (by omega)
  have bIx : (reg b registers.tmp).val = ix := by
    rw [br registers.tmp (by exact (by decide : registers.tmp ≠ registers.value)), aIx]
  have bUnit : (reg b registers.one).val = 1 := by
    rw [br registers.one (by exact (by decide : registers.one ≠ registers.value)), ar registers.one (by exact (by decide : registers.one ≠ registers.tmp)), one]
  have h₂ : code[b.pc]? = some (.add registers.tmp registers.tmp registers.one) := by
    rw [show b.pc = 10 by omega]
    exact p 2 _ rfl
  obtain ⟨c, bc, pc', cWord, cr, cData⟩ := step_add_at (input := input) h₂ (by omega)
  have cIx : (reg c registers.tmp).val = ix + 1 := by
    have fit : (reg b registers.tmp).val + (reg b registers.one).val < 2 ^ bits := by
      rwa [bIx, bUnit]
    rw [cWord, add_no_wrap _ _ fit, bIx, bUnit]
  have h₃ : code[c.pc]? = some (.loadData registers.remain registers.tmp) := by
    rw [show c.pc = 11 by omega]
    exact p 3 _ rfl
  have cLoad : c.data[(reg c registers.tmp).val]? = some stop := by
    rw [cData, bData, aData, cIx]
    exact readStop
  obtain ⟨d, cd, pd, dStop, dr, dData⟩ := step_loadData_at (input := input) h₃ cLoad (by omega)
  have dLo : reg d registers.value = lo := by
    rw [dr registers.value (by exact (by decide : registers.value ≠ registers.remain)), cr registers.value (by exact (by decide : registers.value ≠ registers.tmp)), bLo]
  have h₄ : code[d.pc]? = some (.sub registers.remain registers.remain registers.value) := by
    rw [show d.pc = 12 by omega]
    exact p 4 _ rfl
  obtain ⟨e, de, pe, eWord, er, eData⟩ := step_sub_at (input := input) h₄ (by omega)
  have eLen : (reg e registers.remain).val = stop.val - lo.val := by
    rw [eWord, dStop, dLo, subExact _ _ ordered]
  have eLo : reg e registers.value = lo := by rw [er registers.value (by exact (by decide : registers.value ≠ registers.remain)), dLo]
  have eChild : reg e childrenBase = reg s childrenBase := by
    rw [er childrenBase (by exact (by decide : childrenBase ≠ registers.remain)), dr childrenBase (by exact (by decide : childrenBase ≠ registers.remain)), cr childrenBase (by exact (by decide : childrenBase ≠ registers.tmp)), br childrenBase (by exact (by decide : childrenBase ≠ registers.value)), ar childrenBase (by exact (by decide : childrenBase ≠ registers.tmp))]
  have h₅ : code[e.pc]? = some (.add registers.childBase childrenBase registers.value) := by
    rw [show e.pc = 13 by omega]
    exact p 5 _ rfl
  obtain ⟨t, et, pt, tChild, tr, tData⟩ := step_add_at (input := input) h₅ (by omega)
  have tBase : (reg t registers.childBase).val = (reg s childrenBase).val + lo.val := by
    rw [tChild, eChild, eLo, add_no_wrap _ _ childFits]
  refine ⟨t, .cons sa (.cons ab (.cons bc (.cons cd (.cons de (.cons et (.zero t)))))),
    by omega, ?_, tBase, tData.trans (eData.trans (dData.trans (cData.trans (bData.trans aData)))), ?_⟩
  · rw [tr registers.remain (by exact (by decide : registers.remain ≠ registers.childBase)), eLen]
  · intro r tmp value remain child
    rw [tr r child, er r remain, dr r remain, cr r tmp, br r value, ar r tmp]

end PaperB.RamForestProgram
