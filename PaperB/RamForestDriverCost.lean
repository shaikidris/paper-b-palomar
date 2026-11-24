module

public import PaperB.RamProgram
public import PaperB.ForestLayout

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamForestDriverCost

def guardBlock {bits : Nat} {L : PaperB.RamProgram.Layout bits}
    (zero ptr : Fin L.registerCount) (bodyPC haltPC : Nat) :
    List (PaperB.RamProgram.Instr bits L.registerCount) :=
  [.branchLt zero ptr bodyPC haltPC]

private theorem fetch_lt {bits : Nat} {L : PaperB.RamProgram.Layout bits}
    {code : PaperB.RamProgram.Program L} {pc : Nat}
    (hf : ∃ op, code[pc]? = some op) : pc < code.size := by
  obtain ⟨op, hop⟩ := hf
  by_cases h : pc < code.size
  · exact h
  · simp [getElem?_neg code pc h] at hop

theorem guard_step {bits N : Nat} {L : PaperB.RamProgram.Layout bits}
    {code : PaperB.RamProgram.Program L} {input : PaperB.RamProgram.Input L}
    {entry bodyPC haltPC : Nat} {zero ptr : Fin L.registerCount}
    {ref : PaperB.ForestLayout.State N} {s : PaperB.RamProgram.State L}
    (placed : PaperB.RamProgram.Placed code entry
      (guardBlock (L := L) zero ptr bodyPC haltPC))
    (bodyFetch : ∃ op, code[bodyPC]? = some op)
    (haltFetch : ∃ op, code[haltPC]? = some op)
    (hpc : s.pc = entry)
    (hzero : (PaperB.RamProgram.reg s zero).val = 0)
    (hptr : (PaperB.RamProgram.reg s ptr).val = ref.stack.length) :
    let dst := match ref.stack with
      | [] => haltPC
      | _ :: _ => bodyPC
    let t := { s with pc := dst }
    PaperB.RamProgram.step code input s = some (.next t) ∧
      t.pc = dst ∧ t.data = s.data ∧ t.regs = s.regs := by
  let dst := match ref.stack with
    | [] => haltPC
    | _ :: _ => bodyPC
  have hb :
      (guardBlock (L := L) zero ptr bodyPC haltPC)[0]? =
        some (.branchLt zero ptr bodyPC haltPC) := by
    rfl
  have hf : code[s.pc]? = some (.branchLt zero ptr bodyPC haltPC) := by
    rw [hpc]
    simpa only [Nat.add_zero] using
      (@placed 0 (PaperB.RamProgram.Instr.branchLt zero ptr bodyPC haltPC) hb)
  have hd :
      (if PaperB.WordOps.ltb (PaperB.RamProgram.reg s zero) (PaperB.RamProgram.reg s ptr)
        then bodyPC else haltPC) = dst := by
    cases hs : ref.stack with
    | nil =>
      have hn :
          ¬ (PaperB.WordOps.ltb (PaperB.RamProgram.reg s zero)
            (PaperB.RamProgram.reg s ptr) = true) := by
        intro ht
        have hlt := (PaperB.WordOps.ltb_eq_true
          (PaperB.RamProgram.reg s zero) (PaperB.RamProgram.reg s ptr)).mp ht
        rw [hzero, hptr, hs] at hlt
        exact (Nat.lt_irrefl 0) hlt
      rw [show dst = haltPC by simp only [dst, hs]]
      first
      | exact ite_eq_right hn
      | exact ite_eq_right_iff.mpr (fun h => (hn h).elim)
      | exact if_neg hn
    | cons cmd tail =>
      have ht :
          PaperB.WordOps.ltb (PaperB.RamProgram.reg s zero)
            (PaperB.RamProgram.reg s ptr) = true := by
        apply (PaperB.WordOps.ltb_eq_true
          (PaperB.RamProgram.reg s zero) (PaperB.RamProgram.reg s ptr)).mpr
        rw [hzero, hptr, hs]
        exact Nat.zero_lt_succ tail.length
      rw [show dst = bodyPC by simp only [dst, hs]]
      first
      | exact ite_eq_left ht
      | exact ite_eq_left_iff.mpr (fun h => (h ht).elim)
      | exact if_pos ht
  have htgt :
      (if PaperB.WordOps.ltb (PaperB.RamProgram.reg s zero) (PaperB.RamProgram.reg s ptr)
        then bodyPC else haltPC) < code.size := by
    rw [hd]
    cases hs : ref.stack with
    | nil => simpa only [dst, hs] using (fetch_lt (code := code) haltFetch)
    | cons cmd tail =>
      simpa only [dst, hs] using (fetch_lt (code := code) bodyFetch)
  have hstep := PaperB.RamProgram.step_branchLt_at
    (code := code) (input := input) (s := s)
    (x := zero) (y := ptr) (yesPC := bodyPC) (noPC := haltPC) hf htgt
  exact ⟨by simpa only [hd] using hstep, rfl, rfl, rfl⟩

def bodyCost {N : Nat} (enterBase exitBase childUnit : Nat)
    (g : PaperB.ForestLayout.ChildLists N) : PaperB.ForestLayout.Command N → Nat
  | .enter v => enterBase + childUnit * (g.get v).length
  | .exit _ => exitBase

def traversalWork {N : Nat} (g : PaperB.ForestLayout.ChildLists N)
    (enterBase exitBase childUnit : Nat) :
    Nat → PaperB.ForestLayout.State N → Nat
  | 0, _ => 0
  | fuel + 1, ref =>
    match ref.stack with
    | [] => 0
    | cmd :: tail =>
      (1 + bodyCost enterBase exitBase childUnit g cmd) +
        traversalWork g enterBase exitBase childUnit fuel
          (PaperB.ForestLayout.advance g ref cmd tail)

def potential {N : Nat} (enterBase exitBase childUnit : Nat)
    (ref : PaperB.ForestLayout.State N) : Nat :=
  (enterBase + 1) * ref.enters + (exitBase + 1) * ref.exits +
    childUnit * ref.childrenQueued

theorem potential_advance {N : Nat} (g : PaperB.ForestLayout.ChildLists N)
    (enterBase exitBase childUnit : Nat) (ref : PaperB.ForestLayout.State N)
    (cmd : PaperB.ForestLayout.Command N) (tail : List (PaperB.ForestLayout.Command N)) :
    (1 + bodyCost enterBase exitBase childUnit g cmd) +
        potential enterBase exitBase childUnit ref =
      potential enterBase exitBase childUnit
        (PaperB.ForestLayout.advance g ref cmd tail) := by
  cases cmd with
  | enter v =>
    obtain ⟨_, _, _, he, hx, hq⟩ := PaperB.ForestLayout.advance_enter_spec g ref v tail
    simp only [potential, bodyCost, he, hx, hq, Nat.mul_add, Nat.mul_one] <;> ac_rfl
  | exit v =>
    obtain ⟨_, _, _, he, hx, hq⟩ := PaperB.ForestLayout.advance_exit_spec g ref v tail
    simp only [potential, bodyCost, he, hx, hq, Nat.mul_add, Nat.mul_one] <;> ac_rfl

theorem traversalWork_accounting {N : Nat} (g : PaperB.ForestLayout.ChildLists N)
    (enterBase exitBase childUnit fuel : Nat) (ref : PaperB.ForestLayout.State N) :
    traversalWork g enterBase exitBase childUnit fuel ref +
        potential enterBase exitBase childUnit ref =
      potential enterBase exitBase childUnit (PaperB.ForestLayout.run g fuel ref) := by
  induction fuel generalizing ref with
  | zero =>
    simp [traversalWork, PaperB.ForestLayout.run]
  | succ fuel ih =>
    cases hs : ref.stack with
    | nil =>
      simp [traversalWork, PaperB.ForestLayout.run, hs]
    | cons cmd tail =>
      simp only [traversalWork, PaperB.ForestLayout.run, hs]
      rw [Nat.add_comm (1 + bodyCost enterBase exitBase childUnit g cmd),
        Nat.add_assoc, potential_advance g enterBase exitBase childUnit ref cmd tail]
      exact ih (PaperB.ForestLayout.advance g ref cmd tail)

end PaperB.RamForestDriverCost
