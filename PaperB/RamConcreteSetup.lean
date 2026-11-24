module

public import PaperB.RamThreeCalls

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine (Word)
open PaperB.WordOps (zero sub ltb)

def setupOne (bits : Nat) (hone : 1 < 2 ^ bits) : Word bits :=
  ⟨1, hone⟩

/-- At PC 4, unsigned `x < 1` is exactly the saved `x = 0` case. -/
def firstSetup (bits : Nat) (hone : 1 < 2 ^ bits) :
    Vector (Instr bits 16) 8 :=
  #v[.imm 0 (zero bits),
     .mov 1 8,
     .mov 2 7,
     .imm 6 (setupOne bits hone),
     .branchLt 11 6 20 5,
     .mov 3 11,
     .sub 3 3 6,
     .goto 8]

def secondSetup (bits : Nat) (hone : 1 < 2 ^ bits) :
    Vector (Instr bits 16) 8 :=
  #v[.mov 13 0,
     .imm 0 (zero bits),
     .mov 1 8,
     .mov 2 7,
     .mov 3 11,
     .imm 6 (setupOne bits hone),
     .imm 4 (zero bits),
     .imm 5 (zero bits)]

def thirdSetup (bits : Nat) (hone : 1 < 2 ^ bits) :
    Vector (Instr bits 16) 8 :=
  #v[.mov 14 0,
     .add 2 9 13,
     .sub 1 14 13,
     .mov 3 12,
     .imm 0 (zero bits),
     .imm 6 (setupOne bits hone),
     .imm 4 (zero bits),
     .imm 5 (zero bits)]

def concreteSetup (bits : Nat) (hone : 1 < 2 ^ bits) : Setup bits :=
  #v[firstSetup bits hone, secondSetup bits hone, thirdSetup bits hone]

def setupReg {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (r : Fin 16) : Word bits :=
  s.regs[r.val]'(by simpa only [s.regs_size] using r.isLt)

/-- The exact state change of a setup register write, including the PC. -/
def setupWriteNext {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (r : Fin 16) (w : Word bits) :
    State (layout bits cap hcap) :=
  { s with
    regs := s.regs.set r.val w (by simpa only [s.regs_size] using r.isLt)
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

section
variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
variable {s : State (layout bits cap hcap)}
variable {code : Program (layout bits cap hcap)}
variable {input : Input (layout bits cap hcap)}

private theorem setupReg_write_same (r : Fin 16) (w : Word bits) :
    setupReg (setupWriteNext s r w) r = w := by
  simp [setupReg, setupWriteNext, Array.getElem_set]

private theorem setupReg_write_ne {r q : Fin 16} (hne : r.val ≠ q.val)
    (w : Word bits) :
    setupReg (setupWriteNext s r w) q = setupReg s q := by
  simp [setupReg, setupWriteNext, Array.getElem_set, hne, Ne.symm hne]

private theorem setup_imm_at {d : Fin 16} {w : Word bits}
    (hf : code[s.pc]? = some (.imm d w)) (ht : s.pc + 1 < code.size) :
    step code input s = some (.next (setupWriteNext s d w)) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d w)) else none) = _
  rw [if_pos ht]

private theorem setup_mov_at {d a : Fin 16}
    (hf : code[s.pc]? = some (.mov d a)) (ht : s.pc + 1 < code.size) :
    step code input s = some (.next (setupWriteNext s d (setupReg s a))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d (setupReg s a))) else none) = _
  rw [if_pos ht]

private theorem setup_sub_at {d a b : Fin 16}
    (hf : code[s.pc]? = some (.sub d a b)) (ht : s.pc + 1 < code.size) :
    step code input s =
      some (.next (setupWriteNext s d (sub (setupReg s a) (setupReg s b)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d (sub (setupReg s a) (setupReg s b))))
      else none) = _
  rw [if_pos ht]

end

/-- On the nonzero branch, the word subtraction computes the natural predecessor. -/
theorem setup_sub_one_val {bits : Nat} (hone : 1 < 2 ^ bits)
    (x : Word bits) (hx : x.val ≠ 0) :
    (sub x (setupOne bits hone)).val = x.val - 1 := by
  have hxlt := x.isLt
  have hlt : x.val - 1 < 2 ^ bits := by omega
  have he : 2 ^ bits + x.val - 1 = (x.val - 1) + 2 ^ bits := by omega
  change (2 ^ bits + x.val - 1) % (2 ^ bits) = x.val - 1
  rw [he, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt]

/-- Exactly five steps to PC 20 when saved `x` is zero, leaving r3 untouched;
otherwise exactly eight steps to PC 8 with r3 set to `x - 1`.
The state expressions specify all register writes and leave data unchanged. -/
theorem run_first_setup {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (hone : 1 < 2 ^ bits) (input : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 0) :
    let code := program hcap (concreteSetup bits hone)
    let one := setupOne bits hone
    let x := setupReg s 11
    let s1 := setupWriteNext s 0 (zero bits)
    let s2 := setupWriteNext s1 1 (setupReg s 8)
    let s3 := setupWriteNext s2 2 (setupReg s 7)
    let s4 := setupWriteNext s3 6 one
    let s5 := { s4 with pc := 5 }
    let s6 := setupWriteNext s5 3 x
    let s7 := setupWriteNext s6 3 (sub x one)
    if x.val = 0 then
      Steps code input 5 s { s4 with pc := 20 }
    else
      Steps code input 8 s { s7 with pc := 8 } := by
  intro code one x s1 s2 s3 s4 s5 s6 s7
  have hsize : code.size = 61 := program_size hcap (concreteSetup bits hone)
  have hp1 : s1.pc = 1 := by
    change s.pc + 1 = 1
    rw [hpc]
  have hp2 : s2.pc = 2 := by
    change s1.pc + 1 = 2
    rw [hp1]
  have hp3 : s3.pc = 3 := by
    change s2.pc + 1 = 3
    rw [hp2]
  have hp4 : s4.pc = 4 := by
    change s3.pc + 1 = 4
    rw [hp3]
  have hp5 : s5.pc = 5 := rfl
  have hp6 : s6.pc = 6 := rfl
  have hp7 : s7.pc = 7 := rfl

  have f0 : code[s.pc]? = some (.imm 0 (zero bits)) := by
    rw [hpc] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (0 : Fin 8)
  have f1 : code[s1.pc]? = some (.mov 1 8) := by
    rw [hp1] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (1 : Fin 8)
  have f2 : code[s2.pc]? = some (.mov 2 7) := by
    rw [hp2] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (2 : Fin 8)
  have f3 : code[s3.pc]? = some (.imm 6 one) := by
    rw [hp3] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (3 : Fin 8)
  have f4 : code[s4.pc]? = some (.branchLt 11 6 20 5) := by
    rw [hp4] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (4 : Fin 8)

  have hr8 : setupReg s1 8 = setupReg s 8 := by
    simp (disch := decide) only [s1, setupReg_write_ne]
  have hr7 : setupReg s2 7 = setupReg s 7 := by
    simp (disch := decide) only [s2, s1, setupReg_write_ne]
  have hx4 : setupReg s4 11 = x := by
    simp (disch := decide) only [s4, s3, s2, s1, x, setupReg_write_ne]
  have ho4 : setupReg s4 6 = one := by
    simp only [s4, setupReg_write_same]

  have e0 : step code input s = some (.next s1) :=
    setup_imm_at (s := s) (input := input) f0 (by rw [hpc, hsize] <;> decide)
  have e1 : step code input s1 = some (.next s2) := by
    simpa only [hr8] using
      (setup_mov_at (s := s1) (input := input) f1 (by rw [hp1, hsize] <;> decide))
  have e2 : step code input s2 = some (.next s3) := by
    simpa only [hr7] using
      (setup_mov_at (s := s2) (input := input) f2 (by rw [hp2, hsize] <;> decide))
  have e3 : step code input s3 = some (.next s4) :=
    setup_imm_at (s := s3) (input := input) f3 (by rw [hp3, hsize] <;> decide)

  have hcmp : ltb (setupReg s4 11) (setupReg s4 6) = decide (x.val = 0) := by
    rw [hx4, ho4]
    change decide (x.val < 1) = decide (x.val = 0)
    by_cases hz : x.val = 0
    · have hl : x.val < 1 := by omega
      simp [hz, hl]
    · have hl : ¬ x.val < 1 := by omega
      simp [hz, hl]
  have hb :
      (if ltb (setupReg s4 11) (setupReg s4 6) then 20 else 5) < code.size := by
    rw [hsize]
    split <;> decide
  have e4 :
      step code input s4 =
        some (.next { s4 with
          pc := if ltb (setupReg s4 11) (setupReg s4 6) then 20 else 5 }) :=
    step_branchLt_at (s := s4) (input := input) f4 hb

  by_cases hz : x.val = 0
  · rw [if_pos hz]
    have ez : step code input s4 = some (.next { s4 with pc := 20 }) := by
      simpa [hcmp, hz] using e4
    exact Steps.cons e0
      (Steps.cons e1 (Steps.cons e2 (Steps.cons e3 (Steps.cons ez (Steps.zero _)))))
  · rw [if_neg hz]
    have en : step code input s4 = some (.next s5) := by
      simpa [hcmp, hz, s5] using e4
    have f5 : code[s5.pc]? = some (.mov 3 11) := by
      rw [hp5] <;>
        exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (5 : Fin 8)
    have f6 : code[s6.pc]? = some (.sub 3 3 6) := by
      rw [hp6] <;>
        exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (6 : Fin 8)
    have f7 : code[s7.pc]? = some (.goto 8) := by
      rw [hp7] <;>
        exact fetch_setup_at hcap (concreteSetup bits hone) (0 : Fin 3) (7 : Fin 8)
    have hx5 : setupReg s5 11 = x := hx4
    have ho5 : setupReg s5 6 = one := ho4
    have hx6 : setupReg s6 3 = x := by
      simp only [s6, setupReg_write_same]
    have ho6 : setupReg s6 6 = one := by
      simp (disch := decide) only [s6, setupReg_write_ne, ho5]
    have e5 : step code input s5 = some (.next s6) := by
      simpa only [hx5] using
        (setup_mov_at (s := s5) (input := input) f5 (by rw [hp5, hsize] <;> decide))
    have e6 : step code input s6 = some (.next s7) := by
      simpa only [hx6, ho6] using
        (setup_sub_at (s := s6) (input := input) f6 (by rw [hp6, hsize] <;> decide))
    have e7 : step code input s7 = some (.next { s7 with pc := 8 }) :=
      step_goto_at (s := s7) (input := input) f7 (by rw [hsize] <;> decide)
    exact Steps.cons e0
      (Steps.cons e1 (Steps.cons e2 (Steps.cons e3 (Steps.cons en
        (Steps.cons e5 (Steps.cons e6 (Steps.cons e7 (Steps.zero _))))))))

-- Checkpoint: an `.add` at the current PC performs one setup write.
private theorem setup_add_at {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    {s : State (layout bits cap hcap)}
    {code : Program (layout bits cap hcap)}
    {input : Input (layout bits cap hcap)} {d a b : Fin 16}
    (hf : code[s.pc]? = some (.add d a b)) (ht : s.pc + 1 < code.size) :
    step code input s =
      some (.next (setupWriteNext s d
        (PaperB.WordOps.add (setupReg s a) (setupReg s b)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
      some (Transition.next (setupWriteNext s d
        (PaperB.WordOps.add (setupReg s a) (setupReg s b))))
      else none) = _
  rw [if_pos ht]

-- Keep the entry PC fixed in the total state transformers. In each trace,
-- the eighth write already falls through to that PC; no jump is executed.
private def setupJumpState {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (pc : Nat) :
    State (layout bits cap hcap) :=
  { s with pc := pc }

private theorem setupJumpState_self {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) :
    setupJumpState s s.pc = s := by
  cases s
  rfl

private theorem setupReg_jump {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (pc : Nat) (r : Fin 16) :
    setupReg (setupJumpState s pc) r = setupReg s r :=
  rfl

private theorem setupReg_write_cases {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : State (layout bits cap hcap)) (d r : Fin 16) (w : Word bits) :
    setupReg (setupWriteNext s d w) r =
      if r = d then w else setupReg s r := by
  by_cases h : r = d
  · subst r
    simpa using
      (setupReg_write_same (s := s) d w)
  · have hne : d.val ≠ r.val := by
      intro e
      exact h (Fin.ext e.symm)
    simpa only [if_neg h] using (setupReg_write_ne (s := s) hne w)

/-- The second worker's entry state, with the first result saved in r13
and scratch registers r4 and r5 cleared. -/
def secondSetupState {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap)) :
    State (layout bits cap hcap) :=
  let s1 := setupWriteNext s 13 (setupReg s 0)
  let s2 := setupWriteNext s1 0 (zero bits)
  let s3 := setupWriteNext s2 1 (setupReg s 8)
  let s4 := setupWriteNext s3 2 (setupReg s 7)
  let s5 := setupWriteNext s4 3 (setupReg s 11)
  let s6 := setupWriteNext s5 6 (setupOne bits hone)
  let s7 := setupWriteNext s6 4 (zero bits)
  let s8 := setupWriteNext s7 5 (zero bits)
  setupJumpState s8 28

/-- The third worker's entry state, with the second result saved in r14
and scratch registers r4 and r5 cleared.
The writes compute the shifted base and interval length in word arithmetic. -/
def thirdSetupState {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap)) :
    State (layout bits cap hcap) :=
  let lower := setupReg s 13
  let upper := setupReg s 0
  let secondBase := setupReg s 9
  let s1 := setupWriteNext s 14 upper
  let s2 := setupWriteNext s1 2 (PaperB.WordOps.add secondBase lower)
  let s3 := setupWriteNext s2 1 (sub upper lower)
  let s4 := setupWriteNext s3 3 (setupReg s 12)
  let s5 := setupWriteNext s4 0 (zero bits)
  let s6 := setupWriteNext s5 6 (setupOne bits hone)
  let s7 := setupWriteNext s6 4 (zero bits)
  let s8 := setupWriteNext s7 5 (zero bits)
  setupJumpState s8 48

/-- Exactly eight setup steps from PC 20, falling through to the second
worker at PC 28 after clearing r4 and r5. -/
theorem run_second_setup {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (hone : 1 < 2 ^ bits) (input : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 20) :
    Steps (program hcap (concreteSetup bits hone)) input 8 s
      (secondSetupState hone s) := by
  let code := program hcap (concreteSetup bits hone)
  let s1 := setupWriteNext s 13 (setupReg s 0)
  let s2 := setupWriteNext s1 0 (zero bits)
  let s3 := setupWriteNext s2 1 (setupReg s 8)
  let s4 := setupWriteNext s3 2 (setupReg s 7)
  let s5 := setupWriteNext s4 3 (setupReg s 11)
  let s6 := setupWriteNext s5 6 (setupOne bits hone)
  let s7 := setupWriteNext s6 4 (zero bits)
  let s8 := setupWriteNext s7 5 (zero bits)
  change Steps code input 8 s (setupJumpState s8 28)
  have hsize : code.size = 61 := program_size hcap (concreteSetup bits hone)
  have hp1 : s1.pc = 21 := by change s.pc + 1 = 21; rw [hpc]
  have hp2 : s2.pc = 22 := by change s1.pc + 1 = 22; rw [hp1]
  have hp3 : s3.pc = 23 := by change s2.pc + 1 = 23; rw [hp2]
  have hp4 : s4.pc = 24 := by change s3.pc + 1 = 24; rw [hp3]
  have hp5 : s5.pc = 25 := by change s4.pc + 1 = 25; rw [hp4]
  have hp6 : s6.pc = 26 := by change s5.pc + 1 = 26; rw [hp5]
  have hp7 : s7.pc = 27 := by change s6.pc + 1 = 27; rw [hp6]
  have hp8 : s8.pc = 28 := by change s7.pc + 1 = 28; rw [hp7]
  have hentry : setupJumpState s8 28 = s8 := by
    simpa only [hp8] using (setupJumpState_self s8)

  have f0 : code[s.pc]? = some (.mov 13 0) := by
    rw [hpc] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (0 : Fin 8)
  have f1 : code[s1.pc]? = some (.imm 0 (zero bits)) := by
    rw [hp1] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (1 : Fin 8)
  have f2 : code[s2.pc]? = some (.mov 1 8) := by
    rw [hp2] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (2 : Fin 8)
  have f3 : code[s3.pc]? = some (.mov 2 7) := by
    rw [hp3] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (3 : Fin 8)
  have f4 : code[s4.pc]? = some (.mov 3 11) := by
    rw [hp4] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (4 : Fin 8)
  have f5 : code[s5.pc]? = some (.imm 6 (setupOne bits hone)) := by
    rw [hp5] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (5 : Fin 8)
  have f6 : code[s6.pc]? = some (.imm 4 (zero bits)) := by
    rw [hp6] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (6 : Fin 8)
  have f7 : code[s7.pc]? = some (.imm 5 (zero bits)) := by
    rw [hp7] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (1 : Fin 3) (7 : Fin 8)

  have hr8 : setupReg s2 8 = setupReg s 8 := by
    simp (disch := decide) only [s2, s1, setupReg_write_ne]
  have hr7 : setupReg s3 7 = setupReg s 7 := by
    simp (disch := decide) only [s3, s2, s1, setupReg_write_ne]
  have hr11 : setupReg s4 11 = setupReg s 11 := by
    simp (disch := decide) only [s4, s3, s2, s1, setupReg_write_ne]

  have e0 : step code input s = some (.next s1) :=
    setup_mov_at (s := s) (input := input) f0 (by rw [hpc, hsize] <;> decide)
  have e1 : step code input s1 = some (.next s2) :=
    setup_imm_at (s := s1) (input := input) f1 (by rw [hp1, hsize] <;> decide)
  have e2 : step code input s2 = some (.next s3) := by
    simpa only [hr8] using
      (setup_mov_at (s := s2) (input := input) f2 (by rw [hp2, hsize] <;> decide))
  have e3 : step code input s3 = some (.next s4) := by
    simpa only [hr7] using
      (setup_mov_at (s := s3) (input := input) f3 (by rw [hp3, hsize] <;> decide))
  have e4 : step code input s4 = some (.next s5) := by
    simpa only [hr11] using
      (setup_mov_at (s := s4) (input := input) f4 (by rw [hp4, hsize] <;> decide))
  have e5 : step code input s5 = some (.next s6) :=
    setup_imm_at (s := s5) (input := input) f5 (by rw [hp5, hsize] <;> decide)
  have e6 : step code input s6 = some (.next s7) :=
    setup_imm_at (s := s6) (input := input) f6 (by rw [hp6, hsize] <;> decide)
  have e7 : step code input s7 = some (.next s8) :=
    setup_imm_at (s := s7) (input := input) f7 (by rw [hp7, hsize] <;> decide)
  rw [hentry]
  exact Steps.cons e0
    (Steps.cons e1 (Steps.cons e2 (Steps.cons e3 (Steps.cons e4
      (Steps.cons e5 (Steps.cons e6 (Steps.cons e7 (Steps.zero _))))))))

/-- Exactly eight setup steps from PC 40, falling through to the third
worker at PC 48 after clearing r4 and r5. -/
theorem run_third_setup {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (hone : 1 < 2 ^ bits) (input : Input (layout bits cap hcap))
    (s : State (layout bits cap hcap)) (hpc : s.pc = 40) :
    Steps (program hcap (concreteSetup bits hone)) input 8 s
      (thirdSetupState hone s) := by
  let code := program hcap (concreteSetup bits hone)
  let lower := setupReg s 13
  let upper := setupReg s 0
  let secondBase := setupReg s 9
  let s1 := setupWriteNext s 14 upper
  let s2 := setupWriteNext s1 2 (PaperB.WordOps.add secondBase lower)
  let s3 := setupWriteNext s2 1 (sub upper lower)
  let s4 := setupWriteNext s3 3 (setupReg s 12)
  let s5 := setupWriteNext s4 0 (zero bits)
  let s6 := setupWriteNext s5 6 (setupOne bits hone)
  let s7 := setupWriteNext s6 4 (zero bits)
  let s8 := setupWriteNext s7 5 (zero bits)
  change Steps code input 8 s (setupJumpState s8 48)
  have hsize : code.size = 61 := program_size hcap (concreteSetup bits hone)
  have hp1 : s1.pc = 41 := by change s.pc + 1 = 41; rw [hpc]
  have hp2 : s2.pc = 42 := by change s1.pc + 1 = 42; rw [hp1]
  have hp3 : s3.pc = 43 := by change s2.pc + 1 = 43; rw [hp2]
  have hp4 : s4.pc = 44 := by change s3.pc + 1 = 44; rw [hp3]
  have hp5 : s5.pc = 45 := by change s4.pc + 1 = 45; rw [hp4]
  have hp6 : s6.pc = 46 := by change s5.pc + 1 = 46; rw [hp5]
  have hp7 : s7.pc = 47 := by change s6.pc + 1 = 47; rw [hp6]
  have hp8 : s8.pc = 48 := by change s7.pc + 1 = 48; rw [hp7]
  have hentry : setupJumpState s8 48 = s8 := by
    simpa only [hp8] using (setupJumpState_self s8)

  have f0 : code[s.pc]? = some (.mov 14 0) := by
    rw [hpc] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (0 : Fin 8)
  have f1 : code[s1.pc]? = some (.add 2 9 13) := by
    rw [hp1] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (1 : Fin 8)
  have f2 : code[s2.pc]? = some (.sub 1 14 13) := by
    rw [hp2] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (2 : Fin 8)
  have f3 : code[s3.pc]? = some (.mov 3 12) := by
    rw [hp3] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (3 : Fin 8)
  have f4 : code[s4.pc]? = some (.imm 0 (zero bits)) := by
    rw [hp4] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (4 : Fin 8)
  have f5 : code[s5.pc]? = some (.imm 6 (setupOne bits hone)) := by
    rw [hp5] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (5 : Fin 8)
  have f6 : code[s6.pc]? = some (.imm 4 (zero bits)) := by
    rw [hp6] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (6 : Fin 8)
  have f7 : code[s7.pc]? = some (.imm 5 (zero bits)) := by
    rw [hp7] <;>
      exact fetch_setup_at hcap (concreteSetup bits hone) (2 : Fin 3) (7 : Fin 8)

  have hr9 : setupReg s1 9 = secondBase := by
    simp (disch := decide) only [s1, secondBase, setupReg_write_ne]
  have hlo1 : setupReg s1 13 = lower := by
    simp (disch := decide) only [s1, lower, setupReg_write_ne]
  have hup2 : setupReg s2 14 = upper := by
    simp (disch := decide) only [s2, s1, setupReg_write_ne, setupReg_write_same]
  have hlo2 : setupReg s2 13 = lower := by
    simp (disch := decide) only [s2, setupReg_write_ne, hlo1]
  have hr12 : setupReg s3 12 = setupReg s 12 := by
    simp (disch := decide) only [s3, s2, s1, setupReg_write_ne]

  have e0 : step code input s = some (.next s1) :=
    setup_mov_at (s := s) (input := input) f0 (by rw [hpc, hsize] <;> decide)
  have e1 : step code input s1 = some (.next s2) := by
    simpa only [hr9, hlo1] using
      (setup_add_at (s := s1) (input := input) f1 (by rw [hp1, hsize] <;> decide))
  have e2 : step code input s2 = some (.next s3) := by
    simpa only [hup2, hlo2] using
      (setup_sub_at (s := s2) (input := input) f2 (by rw [hp2, hsize] <;> decide))
  have e3 : step code input s3 = some (.next s4) := by
    simpa only [hr12] using
      (setup_mov_at (s := s3) (input := input) f3 (by rw [hp3, hsize] <;> decide))
  have e4 : step code input s4 = some (.next s5) :=
    setup_imm_at (s := s4) (input := input) f4 (by rw [hp4, hsize] <;> decide)
  have e5 : step code input s5 = some (.next s6) :=
    setup_imm_at (s := s5) (input := input) f5 (by rw [hp5, hsize] <;> decide)
  have e6 : step code input s6 = some (.next s7) :=
    setup_imm_at (s := s6) (input := input) f6 (by rw [hp6, hsize] <;> decide)
  have e7 : step code input s7 = some (.next s8) :=
    setup_imm_at (s := s7) (input := input) f7 (by rw [hp7, hsize] <;> decide)
  rw [hentry]
  exact Steps.cons e0
    (Steps.cons e1 (Steps.cons e2 (Steps.cons e3 (Steps.cons e4
      (Steps.cons e5 (Steps.cons e6 (Steps.cons e7 (Steps.zero _))))))))

/-- Every register at the second worker's entry, including the saved result
and the two cleared scratch registers. -/
theorem secondSetupState_regs {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap)) (r : Fin 16) :
    setupReg (secondSetupState hone s) r =
      if r = 5 then zero bits
      else if r = 4 then zero bits
      else if r = 6 then setupOne bits hone
      else if r = 3 then setupReg s 11
      else if r = 2 then setupReg s 7
      else if r = 1 then setupReg s 8
      else if r = 0 then zero bits
      else if r = 13 then setupReg s 0
      else setupReg s r := by
  simp only [secondSetupState, setupReg_jump, setupReg_write_cases]

/-- Every register at the third worker's entry. In particular, r4 and r5
are zero, r13 is unchanged, and r14 holds the second worker's result. -/
theorem thirdSetupState_regs {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap)) (r : Fin 16) :
    setupReg (thirdSetupState hone s) r =
      if r = 5 then zero bits
      else if r = 4 then zero bits
      else if r = 6 then setupOne bits hone
      else if r = 0 then zero bits
      else if r = 3 then setupReg s 12
      else if r = 1 then sub (setupReg s 0) (setupReg s 13)
      else if r = 2 then PaperB.WordOps.add (setupReg s 9) (setupReg s 13)
      else if r = 14 then setupReg s 0
      else setupReg s r := by
  simp only [thirdSetupState, setupReg_jump, setupReg_write_cases]

/-- The second worker starts with both scratch registers zero. -/
theorem secondSetupState_scratch {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap)) :
    setupReg (secondSetupState hone s) 4 = zero bits ∧
    setupReg (secondSetupState hone s) 5 = zero bits := by
  constructor <;>
    simp (disch := decide) only [secondSetupState_regs, if_pos, if_neg]

/-- The third worker starts with both scratch registers zero. -/
theorem thirdSetupState_scratch {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap)) :
    setupReg (thirdSetupState hone s) 4 = zero bits ∧
    setupReg (thirdSetupState hone s) 5 = zero bits := by
  constructor <;>
    simp (disch := decide) only [thirdSetupState_regs, if_pos, if_neg]

private theorem setup_add_val_of_lt {bits : Nat} (x y : Word bits)
    (h : x.val + y.val < 2 ^ bits) :
    (PaperB.WordOps.add x y).val = x.val + y.val := by
  change (x.val + y.val) % (2 ^ bits) = x.val + y.val
  exact Nat.mod_eq_of_lt h

private theorem setup_sub_val_of_le {bits : Nat} (x y : Word bits)
    (h : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  have hx := x.isLt
  have hlt : x.val - y.val < 2 ^ bits := by omega
  have he : 2 ^ bits + x.val - y.val = (x.val - y.val) + 2 ^ bits := by omega
  change (2 ^ bits + x.val - y.val) % (2 ^ bits) = x.val - y.val
  rw [he, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt]

/-- With no wrap, the third worker receives base `secondBase + lower` in r2
and length `upper - lower` in r1. The setup trace itself needs neither bound. -/
theorem thirdSetupState_worker_values {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : State (layout bits cap hcap))
    (hbase : (setupReg s 9).val + (setupReg s 13).val < 2 ^ bits)
    (horder : (setupReg s 13).val ≤ (setupReg s 0).val) :
    (setupReg (thirdSetupState hone s) 2).val =
        (setupReg s 9).val + (setupReg s 13).val ∧
    (setupReg (thirdSetupState hone s) 1).val =
        (setupReg s 0).val - (setupReg s 13).val := by
  constructor
  · simpa (disch := decide) only [thirdSetupState_regs, if_pos, if_neg] using
      (setup_add_val_of_lt (setupReg s 9) (setupReg s 13) hbase)
  · simpa (disch := decide) only [thirdSetupState_regs, if_pos, if_neg] using
      (setup_sub_val_of_le (setupReg s 0) (setupReg s 13) horder)

end PaperB.RamProgram.ThreeCalls
