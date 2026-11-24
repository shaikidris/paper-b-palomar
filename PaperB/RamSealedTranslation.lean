module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Append at top level in the same file as `reg`, `put`, `reg_put`,
-- `add_at`, and `add_value`, after those lemmas and `Steps.halts`.
namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add)


section
variable {bits : Nat} {L : Layout bits} {code : Program L} {input : Input L} {s : State L}
private def put (s : State L) (d : Fin L.registerCount) (w : Word bits) :
    State L :=
  let hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  { s with
    regs := s.regs.set d.val w hd
    pc := s.pc + 1
    regs_size := by simp only [Array.size_set, s.regs_size] }

private theorem reg_put (s : State L) (d r : Fin L.registerCount)
    (w : Word bits) :
    reg (put s d w) r = if r = d then w else reg s r := by
  have hd : d.val < s.regs.size := by simpa only [s.regs_size] using d.isLt
  have hr : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
  change (s.regs.set d.val w hd)[r.val]'(by simpa only [Array.size_set] using hr) =
    if r = d then w else s.regs[r.val]'hr
  by_cases he : r = d
  · subst r
    simp [Array.getElem_set]
  · have hv : r.val ≠ d.val := fun h => he (Fin.ext h)
    simp [Array.getElem_set, he, hv, Ne.symm hv]

private theorem add_at {d x y : Fin L.registerCount}
    (hf : code[s.pc]? = some (.add d x y)) (hn : s.pc + 1 < code.size) :
    step code input s = some (.next (put s d (add (reg s x) (reg s y)))) := by
  unfold step
  rw [hf]
  change (if s.pc + 1 < code.size then
    some (Transition.next (put s d (add (reg s x) (reg s y)))) else none) = _
  rw [if_pos hn]

private theorem add_value {a b : Word bits} (h : a.val + b.val < 2 ^ bits) :
    (add a b).val = a.val + b.val := by
  change (a.val + b.val) % (2 ^ bits) = a.val + b.val
  exact Nat.mod_eq_of_lt h


end


abbrev sealedTranslationLayout (bits inputCap : Nat)
    (fits : inputCap ≤ 2 ^ bits) : Layout bits :=
  ⟨16, inputCap, 0, fits, Nat.zero_le _⟩

def sealedTranslation {bits inputCap : Nat} (fits : inputCap ≤ 2 ^ bits) :
    Program (sealedTranslationLayout bits inputCap fits) :=
  #[.loadInput 4 0, .add 4 4 3, .loadInput 5 4, .halt]

private theorem sealedTranslation_load
    {bits : Nat} {L : Layout bits} {code : Program L} {input : Input L}
    {s : State L} {d a : Fin L.registerCount} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput d a))
    (hn : s.pc + 1 < code.size)
    (hw : input.words[(reg s a).val]? = some w) :
    step code input s = some (.next (put s d w)) := by
  unfold step
  rw [hf]
  change Option.bind (input.words[(reg s a).val]?) (fun v =>
    if s.pc + 1 < code.size then some (Transition.next (put s d v)) else none) = _
  rw [hw]
  change (if s.pc + 1 < code.size then
    some (Transition.next (put s d w)) else none) = _
  rw [if_pos hn]

theorem sealedTranslation_correct {bits inputCap : Nat}
    (fits : inputCap ≤ 2 ^ bits)
    (input : Input (sealedTranslationLayout bits inputCap fits))
    (s : State (sealedTranslationLayout bits inputCap fits))
    (header mapBase target : Word bits)
    (hpc : s.pc = 0)
    (h0 : s.regs[0]'(by rw [s.regs_size]; change 0 < 16; decide) = header)
    (h3 : s.regs[3]'(by rw [s.regs_size]; change 3 < 16; decide) = target)
    (hheader : input.words[header.val]? = some mapBase)
    (hmap : mapBase.val + target.val < inputCap) :
    ∃ t : State (sealedTranslationLayout bits inputCap fits),
      run (sealedTranslation fits) input 4 s = some ⟨t, 4⟩ ∧
      (t.regs[4]'(by rw [t.regs_size]; change 4 < 16; decide)).val =
        mapBase.val + target.val ∧
      t.regs[5]'(by rw [t.regs_size]; change 5 < 16; decide) =
        input.words[mapBase.val + target.val]'(by rw [input.size_eq]; exact hmap) := by
  let code := sealedTranslation fits
  let addr := add mapBase target
  have haddr : addr.val = mapBase.val + target.val :=
    add_value (a := mapBase) (b := target) (Nat.lt_of_lt_of_le hmap fits)
  have hi : mapBase.val + target.val < input.words.size := by
    rw [input.size_eq]
    exact hmap
  let w := input.words[mapBase.val + target.val]'hi
  let s1 := put s 4 mapBase
  let s2 := put s1 4 addr
  let s3 := put s2 5 w

  have hp1 : s1.pc = 1 := by
    change s.pc + 1 = 1
    rw [hpc] <;> rfl
  have hp2 : s2.pc = 2 := by
    change s1.pc + 1 = 2
    rw [hp1] <;> rfl
  have hp3 : s3.pc = 3 := by
    change s2.pc + 1 = 3
    rw [hp2] <;> rfl

  have hf0 : code[s.pc]? = some (.loadInput 4 0) := by rw [hpc] <;> rfl
  have hf1 : code[s1.pc]? = some (.add 4 4 3) := by rw [hp1] <;> rfl
  have hf2 : code[s2.pc]? = some (.loadInput 5 4) := by rw [hp2] <;> rfl
  have hf3 : code[s3.pc]? = some .halt := by rw [hp3] <;> rfl
  have hn0 : s.pc + 1 < code.size := by rw [hpc]; change 1 < 4; decide
  have hn1 : s1.pc + 1 < code.size := by rw [hp1]; change 2 < 4; decide
  have hn2 : s2.pc + 1 < code.size := by rw [hp2]; change 3 < 4; decide

  have hr0 : reg s 0 = header := h0
  have hr3 : reg s 3 = target := h3
  have hs0 : step code input s = some (.next s1) :=
    sealedTranslation_load (input := input) (w := mapBase) hf0 hn0
      (by simpa only [hr0] using hheader)

  have hr14 : reg s1 4 = mapBase := by
    change reg (put s 4 mapBase) 4 = mapBase
    rw [reg_put, if_pos rfl]
  have hr13 : reg s1 3 = target := by
    have h34 : (3 : Fin 16) ≠ 4 := by decide
    change reg (put s 4 mapBase) 3 = target
    rw [reg_put, if_neg h34, hr3]
  have hs1 : step code input s1 = some (.next s2) := by
    simpa only [hr14, hr13] using (add_at (input := input) hf1 hn1)

  have hr24 : reg s2 4 = addr := by
    change reg (put s1 4 addr) 4 = addr
    rw [reg_put, if_pos rfl]
  have hs2 : step code input s2 = some (.next s3) :=
    sealedTranslation_load (input := input) (w := w) hf2 hn2 (by
      rw [hr24, haddr]
      exact getElem?_pos input.words (mapBase.val + target.val) hi)

  have hh : step code input s3 = some (.halted s3) := by
    unfold step
    rw [hf3] <;> rfl
  have hprefix : Steps code input 3 s s3 :=
    Steps.cons hs0 (Steps.cons hs1 (Steps.cons hs2 (Steps.zero s3)))

  refine ⟨s3, hprefix.halts hh, ?_, ?_⟩
  · have h45 : (4 : Fin 16) ≠ 5 := by decide
    change (reg (put s2 5 w) 4).val = mapBase.val + target.val
    rw [reg_put, if_neg h45, hr24, haddr]
  · change reg (put s2 5 w) 5 = w
    rw [reg_put, if_pos rfl]

end PaperB.RamProgram
