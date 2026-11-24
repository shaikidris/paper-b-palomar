module

public import PaperB.RamEqualityTail

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamEqualityTailTransfer

open PaperB.RamProgram PaperB.RamProgram.ThreeCalls PaperB.RamProgram.ThreeCalls.EqualityTail

private theorem optionBindMatch {α β : Type _}
    (o : Option α) (f : α → Option β) :
    (o >>= f) = (match o with
      | none => none
      | some a => f a) := by
  cases o <;> rfl

private theorem widenChoice {α : Type _} {m n q : Nat}
    (hmn : m ≤ n) {a b : α}
    (h : (if q < m then some a else none) = some b) :
    (if q < n then some a else none) = some b := by
  by_cases hq : q < m
  · rw [if_pos (Nat.lt_of_lt_of_le hq hmn)]
    simpa only [if_pos hq] using h
  · rw [if_neg hq] at h
    cases h

-- Work with abstract arrays here: only the fetch and the successor check
-- in the ISA depend on which program is supplied.
private theorem widenNext {bits : Nat} {L : Layout bits}
    {old new : Program L} {input : Input L} {s u : State L}
    (hf : new[s.pc]? = old[s.pc]?)
    (hsize : old.size ≤ new.size)
    (h : step old input s = some (.next u)) :
    step new input s = some (.next u) := by
  cases hfetch : old[s.pc]? with
  | none =>
    simp only [step, hfetch, optionBindMatch] at h <;> cases h
  | some instr =>
    cases instr <;>
      (simp only [step, hfetch, optionBindMatch] at h <;>
        simp only [step, hf, hfetch, optionBindMatch])
    case loadInput =>
      split at h
      · cases h
      · exact widenChoice hsize h
    case loadData =>
      split at h
      · cases h
      · exact widenChoice hsize h
    case storeData =>
      split at h
      · rename_i hi
        simp only [dif_pos hi]
        exact widenChoice hsize h
      · cases h
    case branchLt =>
      split at h
      · rename_i hlt
        simp only [if_pos hlt]
        exact widenChoice hsize h
      · rename_i hge
        simp only [if_neg hge]
        exact widenChoice hsize h
    all_goals first | exact widenChoice hsize h | cases h

variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
    {hb : 1 < 2 ^ bits} {setup : Setup bits}
    {input : Input (layout bits cap hcap)}
    {s u t : State (layout bits cap hcap)}

private theorem oldFetchHalt :
    (program hcap setup)[60]? = some .halt := by
  simp only [program, getElem?_def, Array.size_ofFn,
    show 60 < 61 by decide, dif_pos, Array.getElem_ofFn] <;> rfl

private theorem oldNextSource
    (h : step (program hcap setup) input s = some (.next u)) :
    s.pc < 60 := by
  by_cases hp : s.pc < 60
  · exact hp
  · rcases Nat.eq_or_lt_of_le (Nat.le_of_not_gt hp) with heq | hgt
    · have hf : (program hcap setup)[s.pc]? = some .halt := by
        rw [← heq]
        exact oldFetchHalt
      simp only [step, hf, optionBindMatch] at h <;> cases h
    · have hoob : ¬ s.pc < (program hcap setup).size := by
        rw [program_size]
        exact Nat.not_lt_of_ge (Nat.succ_le_of_lt hgt)
      have hf : (program hcap setup)[s.pc]? = none := by
        simp only [getElem?_def, dif_neg hoob]
      simp only [step, hf, optionBindMatch] at h <;> cases h

/-- Every non-halting step of the old program has the same successor in
the checked program. -/
theorem step_checkedProgram
    (h : step (program hcap setup) input s = some (.next u)) :
    step (checkedProgram hcap hb setup) input s = some (.next u) := by
  have hsize : (program hcap setup).size ≤
      (checkedProgram hcap hb setup).size := by
    rw [ThreeCalls.program_size hcap setup, checkedProgram_size hcap hb setup]
    decide
  exact widenNext (fetch_prefix hcap hb setup (oldNextSource h)) hsize h

/-- The checked program preserves every old non-halting prefix, with the
same endpoints and instruction count. -/
theorem steps_checkedProgram {n : Nat}
    (h : Steps (program hcap setup) input n s t) :
    Steps (checkedProgram hcap hb setup) input n s t := by
  induction h with
  | zero s => exact Steps.zero s
  | cons hs _ ih => exact Steps.cons (step_checkedProgram hs) ih

end PaperB.RamEqualityTailTransfer
