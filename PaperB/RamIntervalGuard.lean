module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram.IntervalGuard

open PaperB.Machine (Word)
open PaperB.WordOps (ltb)

variable {bits : Nat} {L : Layout bits}

def r (h16 : L.registerCount = 16) (i : Fin 16) : Fin L.registerCount :=
  ⟨i.val, by rw [h16]; exact i.isLt⟩

def romFor (h16 : L.registerCount = 16) (loReg hiReg xReg : Fin 16)
    (zero one : Word bits) : Program L :=
  #[.branchLt (r h16 xReg) (r h16 loReg) 4 1,
    .branchLt (r h16 xReg) (r h16 hiReg) 2 4,
    .imm (r h16 0) one, .halt,
    .imm (r h16 0) zero, .halt]

def rom (h16 : L.registerCount = 16) (zero one : Word bits) : Program L :=
  romFor h16 1 2 3 zero one

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
    simp
  · have hv : j.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, Ne.symm hv]

private theorem immAt {code : Program L} {input : Input L} {s : State L}
    {d : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (put s d w)) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (put s d w)) else none) = _
  rw [ite_eq_left hn]

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

private theorem threeBudget {code : Program L} {input : Input L}
    {s v t : State L}
    (h0 : step code input s = some (.next v))
    (h1 : step code input v = some (.next t))
    (h2 : step code input t = some (.halted t)) (fuel : Nat) :
    run code input fuel s = if 3 ≤ fuel then some ⟨t, 3⟩ else none := by
  match fuel with
  | 0 => simp [run]
  | 1 => simp [run, h0]
  | 2 => simp [run, h0, h1]
  | n + 3 =>
    rw [ite_eq_left (Nat.add_le_add_right (Nat.zero_le n) 3)]
    change run code input n.succ.succ.succ s = _
    simp [run, h0, h1, h2]

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
    rw [ite_eq_left (Nat.add_le_add_right (Nat.zero_le n) 4)]
    change run code input n.succ.succ.succ.succ s = _
    simp [run, h0, h1, h2, h3]

/-- Below `lo` takes three instructions; every other path takes four. -/
theorem run_spec_for
    (h16 : L.registerCount = 16) (loReg hiReg xReg : Fin 16)
    (zero one : Word bits)
    (hz : zero.val = 0) (ho : one.val = 1)
    (input : Input L) (s : State L) (entry : s.pc = 0) :
    let lo := (reg s (r h16 loReg)).val
    let hi := (reg s (r h16 hiReg)).val
    let x := (reg s (r h16 xReg)).val
    let ok := lo ≤ x ∧ x < hi
    let n : Nat := if x < lo then 3 else 4
    ∃ t : State L,
      (∀ fuel : Nat, run (romFor h16 loReg hiReg xReg zero one) input fuel s =
        if n ≤ fuel then some ⟨t, n⟩ else none) ∧
      t.pc = (if ok then 3 else 5) ∧
      (reg t (r h16 0)).val = (if ok then 1 else 0) ∧
      (∀ j : Fin L.registerCount, j ≠ r h16 0 → reg t j = reg s j) ∧
      t.data = s.data := by
  let code := romFor h16 loReg hiReg xReg zero one
  let lo := (reg s (r h16 loReg)).val
  let hi := (reg s (r h16 hiReg)).val
  let x := (reg s (r h16 xReg)).val
  let ok := lo ≤ x ∧ x < hi
  let n : Nat := if x < lo then 3 else 4
  let p : Nat := if ok then 2 else 4
  let w := if ok then one else zero
  let v := jump s p
  let t := put v (r h16 0) w

  have b0 : code[s.pc]? = some (.branchLt (r h16 xReg) (r h16 loReg) 4 1) := by
    rw [entry] <;> rfl
  have b1 : code[(jump s 1).pc]? =
      some (.branchLt (r h16 xReg) (r h16 hiReg) 2 4) := rfl
  have c0 : ltb (reg s (r h16 xReg)) (reg s (r h16 loReg)) =
      decide (x < lo) := rfl
  have c1 : ltb (reg (jump s 1) (r h16 xReg)) (reg (jump s 1) (r h16 hiReg)) =
      decide (x < hi) := rfl

  have tail : p < code.size ∧ code[v.pc]? = some (.imm (r h16 0) w) ∧
      v.pc + 1 < code.size ∧ code[t.pc]? = some .halt := by
    change p < code.size ∧ code[p]? = some (.imm (r h16 0) w) ∧
      p + 1 < code.size ∧ code[p + 1]? = some .halt
    by_cases h : ok
    · rw [show p = 2 from ite_eq_left h, show w = one from ite_eq_left h]
      exact ⟨by change 2 < 6; decide, rfl, by change 3 < 6; decide, rfl⟩
    · rw [show p = 4 from ite_eq_right h, show w = zero from ite_eq_right h]
      exact ⟨by change 4 < 6; decide, rfl, by change 5 < 6; decide, rfl⟩
  obtain ⟨hp, hf, hn, hh⟩ := tail
  have h2 : step code input v = some (.next t) := immAt hf hn
  have h3 : step code input t = some (.halted t) := step_halt_at hh

  refine ⟨t, ?_, ?_, ?_, ?_, rfl⟩
  · intro fuel
    change run code input fuel s = if n ≤ fuel then some ⟨t, n⟩ else none
    by_cases h : x < lo
    · have hbad : ¬ ok := fun hg => (Nat.not_lt_of_ge hg.1) h
      have h0 : step code input s = some (.next v) :=
        branchTo b0 (by simp [c0, h, p, hbad]) hp
      simpa only [n, ite_eq_left h] using threeBudget h0 h2 h3 fuel
    · have hlo : lo ≤ x := Nat.le_of_not_gt h
      have h0 : step code input s = some (.next (jump s 1)) :=
        branchTo b0 (by simp [c0, h]) (by change 1 < 6; decide)
      have h1 : step code input (jump s 1) = some (.next v) :=
        branchTo b1 (by
          by_cases hhi : x < hi <;> simp [c1, p, ok, hlo, hhi]) hp
      simpa only [n, ite_eq_right h] using fourBudget h0 h1 h2 h3 fuel
  · change p + 1 = (if ok then 3 else 5)
    by_cases h : ok <;> simp [p, h]
  · change (reg t (r h16 0)).val = (if ok then 1 else 0)
    have hr : reg t (r h16 0) = w :=
      (regPut v (r h16 0) (r h16 0) w).trans (ite_eq_left rfl)
    rw [hr]
    by_cases h : ok
    · simpa only [w, ite_eq_left h] using ho
    · simpa only [w, ite_eq_right h] using hz
  · intro j hj
    exact (regPut v (r h16 0) j w).trans (ite_eq_right hj)

/-- Below `lo` takes three instructions; every other path takes four. -/
theorem run_spec
    (h16 : L.registerCount = 16) (zero one : Word bits)
    (hz : zero.val = 0) (ho : one.val = 1)
    (input : Input L) (s : State L) (entry : s.pc = 0) :
    let lo := (reg s (r h16 1)).val
    let hi := (reg s (r h16 2)).val
    let x := (reg s (r h16 3)).val
    let ok := lo ≤ x ∧ x < hi
    let n : Nat := if x < lo then 3 else 4
    ∃ t : State L,
      (∀ fuel : Nat, run (rom h16 zero one) input fuel s =
        if n ≤ fuel then some ⟨t, n⟩ else none) ∧
      t.pc = (if ok then 3 else 5) ∧
      (reg t (r h16 0)).val = (if ok then 1 else 0) ∧
      (∀ j : Fin L.registerCount, j ≠ r h16 0 → reg t j = reg s j) ∧
      t.data = s.data :=
  run_spec_for h16 1 2 3 zero one hz ho input s entry

/-- Exact guard run from the post-loader state `s`, with operands in r5/r6/r7. -/
theorem run_spec_567
    (h16 : L.registerCount = 16) (zero one : Word bits)
    (hz : zero.val = 0) (ho : one.val = 1)
    (input : Input L) (s : State L) (entry : s.pc = 0) :
    let lo := (reg s (r h16 5)).val
    let hi := (reg s (r h16 6)).val
    let x := (reg s (r h16 7)).val
    let ok := lo ≤ x ∧ x < hi
    let n : Nat := if x < lo then 3 else 4
    ∃ t : State L,
      (∀ fuel : Nat, run (romFor h16 5 6 7 zero one) input fuel s =
        if n ≤ fuel then some ⟨t, n⟩ else none) ∧
      t.pc = (if ok then 3 else 5) ∧
      (reg t (r h16 0)).val = (if ok then 1 else 0) ∧
      (∀ j : Fin L.registerCount, j ≠ r h16 0 → reg t j = reg s j) ∧
      t.data = s.data :=
  run_spec_for h16 5 6 7 zero one hz ho input s entry

end PaperB.RamProgram.IntervalGuard
