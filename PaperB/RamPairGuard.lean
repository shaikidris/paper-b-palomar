module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/- Append after the supplied RAM definitions, in the same enclosing namespace.
   This fragment checks r1 (first failed ID) against r3 (target ID).
   It assumes reachability is checked elsewhere. A zero failed ID therefore
   passes this check whenever the target is positive.

   Every path executes two control instructions, one write to r0, and halt.
   The comparison law is explicit because the definition of ltb was omitted;
   if ltb is defined by decide on .val, supply `fun _ _ => rfl`. -/

namespace PaperB.RamProgram.PairGuard

open PaperB.Machine (Word)
open PaperB.WordOps (ltb)

variable {bits : Nat} {L : Layout bits}

def r (h16 : L.registerCount = 16) (i : Fin 16) : Fin L.registerCount :=
  ⟨i.val, by rw [h16]; exact i.isLt⟩

def rom (h16 : L.registerCount = 16) (zero one : Word bits) : Program L :=
  #[.branchLt (r h16 1) (r h16 3) 2 1,
    .branchLt (r h16 3) (r h16 1) 3 5,
    .goto 3,
    .imm (r h16 0) one,
    .halt,
    .imm (r h16 0) zero,
    .halt]

private def jump (s : State L) (p : Nat) : State L :=
  { s with pc := p }

private def put (s : State L) (d : Fin L.registerCount) (w : Word bits) :
    State L :=
  let hd : d.val < s.regs.size := by
    simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem regPut (s : State L) (d j : Fin L.registerCount)
    (w : Word bits) :
    reg (put s d w) j = if j = d then w else reg s j := by
  have hd : d.val < s.regs.size := by
    simpa only [s.regs_size] using d.isLt
  have hj : j.val < s.regs.size := by
    simpa only [s.regs_size] using j.isLt
  change
    (s.regs.set d.val w hd)[j.val]'(by simpa only [Array.size_set] using hj) =
      if j = d then w else s.regs[j.val]'hj
  by_cases he : j = d
  · subst j
    simp [Array.getElem_set]
  · have hv : j.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, hv, Ne.symm hv]

private theorem immAt {code : Program L} {input : Input L} {s : State L}
    {d : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (put s d w)) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (put s d w)) else none) = _
  rw [if_pos hn]

private theorem branchTo {code : Program L} {input : Input L} {s : State L}
    {a b : Fin L.registerCount} {yes no dest : Nat}
    (hf : code[s.pc]? = some (.branchLt a b yes no))
    (hc : (if ltb (reg s a) (reg s b) then yes else no) = dest)
    (hd : dest < code.size) :
    step code input s = some (.next (jump s dest)) := by
  have hb : (if ltb (reg s a) (reg s b) then yes else no) < code.size := by
    rw [hc]
    exact hd
  simpa only [hc, jump] using step_branchLt_at (input := input) hf hb

private theorem fourBudget {code : Program L} {input : Input L}
    {s u v t : State L}
    (h0 : step code input s = some (.next u))
    (h1 : step code input u = some (.next v))
    (h2 : step code input v = some (.next t))
    (h3 : step code input t = some (.halted t)) (fuel : Nat) :
    run code input fuel s = if 4 ≤ fuel then some ⟨t, 4⟩ else none := by
  match fuel with
  | 0 => simp [run]
  | 1 => simp [run, h0]
  | 2 => simp [run, h0, h1]
  | 3 => simp [run, h0, h1, h2]
  | n + 4 =>
    have hn : 4 ≤ n + 4 := Nat.add_le_add_right (Nat.zero_le n) 4
    rw [if_pos hn]
    change run code input n.succ.succ.succ.succ s = _
    simp [run, h0, h1, h2, h3]

/-- Equal IDs reject; unequal IDs continue. Only r0 and the PC change. -/
theorem run_spec
    (h16 : L.registerCount = 16) (zero one : Word bits)
    (hz : zero.val = 0) (ho : one.val = 1)
    (cmp : ∀ a b : Word bits, ltb a b = decide (a.val < b.val))
    (input : Input L) (s : State L) (entry : s.pc = 0) :
    let eqID := (reg s (r h16 1)).val = (reg s (r h16 3)).val
    ∃ t : State L,
      (∀ fuel : Nat,
        run (rom h16 zero one) input fuel s =
          if 4 ≤ fuel then some ⟨t, 4⟩ else none) ∧
      t.pc = (if eqID then 6 else 4) ∧
      (reg t (r h16 0)).val = (if eqID then 0 else 1) ∧
      (∀ j : Fin L.registerCount, j ≠ r h16 0 → reg t j = reg s j) ∧
      t.data = s.data := by
  let code := rom h16 zero one
  let f := (reg s (r h16 1)).val
  let x := (reg s (r h16 3)).val
  let p : Nat := if f = x then 5 else 3
  let w := if f = x then zero else one
  let v := jump s p
  let t := put v (r h16 0) w

  have b0 : code[s.pc]? = some (.branchLt (r h16 1) (r h16 3) 2 1) := by
    rw [entry] <;> rfl
  have b1 : code[(jump s 1).pc]? =
      some (.branchLt (r h16 3) (r h16 1) 3 5) := rfl
  have b2 : code[(jump s 2).pc]? = some (.goto 3) := rfl
  have at1 : 1 < code.size := by change 1 < 7; decide
  have at2 : 2 < code.size := by change 2 < 7; decide
  have at3 : 3 < code.size := by change 3 < 7; decide
  have at5 : 5 < code.size := by change 5 < 7; decide
  have c0 : ltb (reg s (r h16 1)) (reg s (r h16 3)) =
      decide (f < x) := cmp _ _
  have c1 : ltb (reg (jump s 1) (r h16 3)) (reg (jump s 1) (r h16 1)) =
      decide (x < f) := cmp _ _

  have guardHead : ∃ u : State L,
      step code input s = some (.next u) ∧
      step code input u = some (.next v) := by
    by_cases hfx : f < x
    · have hne : f ≠ x := fun he => by
        rw [he] at hfx
        exact Nat.lt_irrefl _ hfx
      refine ⟨jump s 2, branchTo b0 (by simp [c0, hfx]) at2, ?_⟩
      simpa only [v, p, if_neg hne, jump] using
        (step_goto_at (input := input) b2 at3)
    · refine ⟨jump s 1, branchTo b0 (by simp [c0, hfx]) at1, ?_⟩
      by_cases hxf : x < f
      · have hne : f ≠ x := fun he => by
          rw [he] at hxf
          exact Nat.lt_irrefl _ hxf
        have hb := branchTo (input := input) b1 (by simp [c1, hxf]) at3
        simpa only [v, p, if_neg hne, jump] using hb
      · have he : f = x :=
          Nat.le_antisymm (Nat.le_of_not_gt hxf) (Nat.le_of_not_gt hfx)
        have hb := branchTo (input := input) b1 (by simp [c1, hxf]) at5
        simpa only [v, p, if_pos he, jump] using hb

  have tail :
      code[v.pc]? = some (.imm (r h16 0) w) ∧
      v.pc + 1 < code.size ∧ code[t.pc]? = some .halt := by
    change code[p]? = some (.imm (r h16 0) w) ∧
      p + 1 < code.size ∧ code[p + 1]? = some .halt
    by_cases he : f = x
    · rw [show p = 5 from if_pos he, show w = zero from if_pos he]
      exact ⟨rfl, by change 6 < 7; decide, rfl⟩
    · rw [show p = 3 from if_neg he, show w = one from if_neg he]
      exact ⟨rfl, by change 4 < 7; decide, rfl⟩

  obtain ⟨u, h0, h1⟩ := guardHead
  obtain ⟨hf, hn, hh⟩ := tail
  have h2 : step code input v = some (.next t) := immAt hf hn
  have h3 : step code input t = some (.halted t) := step_halt_at hh
  refine ⟨t, fourBudget h0 h1 h2 h3, ?_, ?_, ?_, rfl⟩
  · change p + 1 = (if f = x then 6 else 4)
    by_cases he : f = x <;> simp [p, he]
  · change (reg t (r h16 0)).val = (if f = x then 0 else 1)
    have hr : reg t (r h16 0) = w :=
      (regPut v (r h16 0) (r h16 0) w).trans (if_pos rfl)
    rw [hr]
    by_cases he : f = x <;> simp [w, he, hz, ho]
  · intro j hj
    exact (regPut v (r h16 0) j w).trans (if_neg hj)

end PaperB.RamProgram.PairGuard
