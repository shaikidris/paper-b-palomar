module

public import PaperB.RamSetupAgreement

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram.ThreeCalls

open PaperB.Machine PaperB.WordOps PaperB.PairLookup
open PaperB.RamPairSliceBinding (toPredecessor)

private def firstSetupPrefix {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap)) :
    RamProgram.State (layout bits cap hcap) :=
  let s1 := setupWriteNext s 0 (zero bits)
  let s2 := setupWriteNext s1 1 (setupReg s 8)
  let s3 := setupWriteNext s2 2 (setupReg s 7)
  setupWriteNext s3 6 (setupOne bits hone)

private def firstSetupJump {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : RamProgram.State (layout bits cap hcap)) (pc : Nat) :
    RamProgram.State (layout bits cap hcap) :=
  { s with pc := pc }

/-- The exact endpoint of the installed first setup, on either branch. -/
def firstSetupState {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap)) :
    RamProgram.State (layout bits cap hcap) :=
  let s4 := firstSetupPrefix hone s
  let x := setupReg s 11
  if x.val = 0 then firstSetupJump s4 20
  else
    let s5 := firstSetupJump s4 5
    let s6 := setupWriteNext s5 3 x
    let s7 := setupWriteNext s6 3 (sub x (setupOne bits hone))
    firstSetupJump s7 8

private theorem firstSetupReg_jump {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : RamProgram.State (layout bits cap hcap)) (pc : Nat) (r : Fin 16) :
    setupReg (firstSetupJump s pc) r = setupReg s r := rfl

private theorem firstSetupReg_write {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (s : RamProgram.State (layout bits cap hcap))
    (d r : Fin 16) (w : Word bits) :
    setupReg (setupWriteNext s d w) r =
      if r = d then w else setupReg s r := by
  by_cases he : r = d
  · subst r
    simp [setupReg, setupWriteNext, Array.getElem_set]
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp [setupReg, setupWriteNext, Array.getElem_set, he, hv, Ne.symm hv]

theorem firstSetupState_steps {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (hone : 1 < 2 ^ bits) (input : RamProgram.Input (layout bits cap hcap))
    (s : RamProgram.State (layout bits cap hcap)) (hpc : s.pc = 0) :
    Steps (program hcap (concreteSetup bits hone)) input
      (if (setupReg s 11).val = 0 then 5 else 8) s (firstSetupState hone s) := by
  by_cases hx : (setupReg s 11).val = 0
  · simpa only [firstSetupState, firstSetupPrefix, firstSetupJump, if_pos hx] using
      (run_first_setup hcap hone input s hpc)
  · simpa only [firstSetupState, firstSetupPrefix, firstSetupJump, if_neg hx] using
      (run_first_setup hcap hone input s hpc)

theorem firstSetupState_pc {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap)) :
    (firstSetupState hone s).pc = if (setupReg s 11).val = 0 then 20 else 8 := by
  by_cases hx : (setupReg s 11).val = 0
  · simp only [firstSetupState, if_pos hx] <;> rfl
  · simp only [firstSetupState, if_neg hx] <;> rfl

/-- Both branches preserve the entire data array. -/
theorem firstSetupState_data {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap)) :
    (firstSetupState hone s).data = s.data := by
  by_cases hx : (setupReg s 11).val = 0
  · simp only [firstSetupState, if_pos hx] <;> rfl
  · simp only [firstSetupState, if_neg hx] <;> rfl

theorem firstSetupState_regs {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap))
    (r : Fin 16) :
    setupReg (firstSetupState hone s) r =
      if r = 3 then
        if (setupReg s 11).val = 0 then setupReg s r
        else sub (setupReg s 11) (setupOne bits hone)
      else if r = 6 then setupOne bits hone
      else if r = 2 then setupReg s 7
      else if r = 1 then setupReg s 8
      else if r = 0 then zero bits
      else setupReg s r := by
  by_cases hx : (setupReg s 11).val = 0
  · by_cases hr : r = 3
    · subst r
      simp (disch := decide) only [firstSetupState, firstSetupPrefix,
        firstSetupReg_jump, firstSetupReg_write, if_pos hx, if_pos, if_neg]
    · simp only [firstSetupState, firstSetupPrefix, firstSetupReg_jump,
        firstSetupReg_write, if_pos hx, if_neg hr]
  · by_cases hr : r = 3
    · simp only [firstSetupState, firstSetupPrefix, firstSetupReg_jump,
        firstSetupReg_write, if_neg hx, if_pos hr]
    · simp only [firstSetupState, firstSetupPrefix, firstSetupReg_jump,
        firstSetupReg_write, if_neg hx, if_neg hr]

/-- Registers 7 through 15 retain their caller values on both branches. -/
theorem firstSetupState_caller_regs {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap))
    (r : Fin 16) (hr : 7 ≤ r.val) :
    setupReg (firstSetupState hone s) r = setupReg s r := by
  have hne (q : Fin 16) (hq : q.val < 7) : r ≠ q := by
    intro he
    have hv : r.val = q.val := congrArg Fin.val he
    omega
  simp only [firstSetupState_regs,
    if_neg (hne 3 (by decide)), if_neg (hne 6 (by decide)),
    if_neg (hne 2 (by decide)), if_neg (hne 1 (by decide)),
    if_neg (hne 0 (by decide))]

/-- The first setup does not clear scratch; it retains the caller's zeros. -/
theorem firstSetupState_scratch {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap))
    (h4 : setupReg s 4 = zero bits) (h5 : setupReg s 5 = zero bits) :
    setupReg (firstSetupState hone s) 4 = zero bits ∧
    setupReg (firstSetupState hone s) 5 = zero bits := by
  constructor
  · simpa (disch := decide) only [firstSetupState_regs, if_pos, if_neg] using h4
  · simpa (disch := decide) only [firstSetupState_regs, if_pos, if_neg] using h5

/-- The natural predecessor of the saved key, represented as a word. -/
def firstSetupKey {bits : Nat} (x : Word bits) : Word bits :=
  ⟨x.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le x.val 1) x.isLt⟩

theorem firstSetupState_key {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap))
    (hx : (setupReg s 11).val ≠ 0) :
    setupReg (firstSetupState hone s) 3 = firstSetupKey (setupReg s 11) := by
  rw [firstSetupState_regs, if_pos (rfl : (3 : Fin 16) = 3), if_neg hx]
  exact Fin.ext (setup_sub_one_val hone (setupReg s 11) hx)

theorem firstSetupState_init_agreement
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    (p : ColumnReduction.Slice (bits := bits) i.words)
    (hone : 1 < 2 ^ bits) (s : RamProgram.State (layout bits cap hcap))
    (hx : (setupReg s 11).val ≠ 0)
    (hbase : setupReg s 7 = p.base)
    (hlen : (setupReg s 8).val = p.len)
    (h4 : setupReg s 4 = zero bits) (h5 : setupReg s 5 = zero bits) :
    ArenaAgreement (bank hcap) (firstSetupState hone s)
      (relocateStatePC (entryPC 0)
        (Predecessor.init (toPredecessor (input := i) p)
          (firstSetupKey (setupReg s 11))))
      (firstSetupState hone s) := by
  obtain ⟨ht4, ht5⟩ := firstSetupState_scratch hone s h4 h5
  refine predecessor_init_agreement hcap (i := i) p
    (firstSetupKey (setupReg s 11)) hone 0 (firstSetupState hone s)
    ?_ ?_ ?_ ?_ (firstSetupState_key hone s hx) ht4 ht5 ?_
  · rw [firstSetupState_pc, if_neg hx] <;> rfl
  · simp (disch := decide) only [firstSetupState_regs, if_pos, if_neg]
  · simpa (disch := decide) only [firstSetupState_regs, if_pos, if_neg] using hlen
  · simpa (disch := decide) only [firstSetupState_regs, if_pos, if_neg] using hbase
  · simp (disch := decide) only [firstSetupState_regs, if_pos, if_neg]

/-- The zero branch skips the worker and reaches PC 20 with result zero. -/
theorem run_first_setup_zero_entry {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    (hone : 1 < 2 ^ bits) (input : RamProgram.Input (layout bits cap hcap))
    (s : RamProgram.State (layout bits cap hcap)) (hpc : s.pc = 0)
    (hx : (setupReg s 11).val = 0) :
    Steps (program hcap (concreteSetup bits hone)) input 5 s
        (firstSetupState hone s) ∧
      (firstSetupState hone s).pc = 20 ∧
      setupReg (firstSetupState hone s) 0 = zero bits := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [if_pos hx] using (firstSetupState_steps hcap hone input s hpc)
  · simp only [firstSetupState_pc, if_pos hx]
  · simp (disch := decide) only [firstSetupState_regs, if_pos, if_neg]

/-- The nonzero branch reaches PC 8 in agreement with scalar initialization
on the natural predecessor of the saved key. -/
theorem run_first_setup_nonzero_entry
    {bits cap : Nat} (hcap : cap ≤ 2 ^ bits)
    {i : RamProgram.Input (Predecessor.layout bits cap hcap)}
    (p : ColumnReduction.Slice (bits := bits) i.words)
    (hone : 1 < 2 ^ bits) (input : RamProgram.Input (layout bits cap hcap))
    (s : RamProgram.State (layout bits cap hcap)) (hpc : s.pc = 0)
    (hx : (setupReg s 11).val ≠ 0)
    (hbase : setupReg s 7 = p.base)
    (hlen : (setupReg s 8).val = p.len)
    (h4 : setupReg s 4 = zero bits) (h5 : setupReg s 5 = zero bits) :
    Steps (program hcap (concreteSetup bits hone)) input 8 s
        (firstSetupState hone s) ∧
      (firstSetupState hone s).pc = 8 ∧
      ArenaAgreement (bank hcap) (firstSetupState hone s)
        (relocateStatePC (entryPC 0)
          (Predecessor.init (toPredecessor (input := i) p)
            (firstSetupKey (setupReg s 11))))
        (firstSetupState hone s) := by
  refine ⟨?_, ?_, firstSetupState_init_agreement hcap (i := i) p
    hone s hx hbase hlen h4 h5⟩
  · simpa only [if_neg hx] using (firstSetupState_steps hcap hone input s hpc)
  · simp only [firstSetupState_pc, if_neg hx]

end PaperB.RamProgram.ThreeCalls
