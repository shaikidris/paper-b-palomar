module

public import PaperB.RamLexPairCuts
public import PaperB.RamSearchCorrect

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamPairSliceBinding

open PaperB.Machine PaperB.RamProgram
open PaperB.PairLookup

variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
variable {input : RamProgram.Input (Predecessor.layout bits cap hcap)}

/-- Reinterpret the slice metadata over the same input array. -/
abbrev toPredecessor
    (p : ColumnReduction.Slice (bits := bits) input.words) :
    Predecessor.Slice (bits := bits) (cap := cap) (hcap := hcap) input where
  base := p.base
  len := p.len
  fits := p.fits
  within := by
    calc
      p.base.val + p.len ≤ input.words.size := p.within
      _ = cap := input.size_eq

@[simp] theorem toPredecessor_get
    (p : ColumnReduction.Slice (bits := bits) input.words)
    (i : Nat) (hi : i < p.len) :
    (toPredecessor (input := input) p).get i hi = p.get i hi :=
  rfl

theorem toPredecessor_sorted_iff
    (p : ColumnReduction.Slice (bits := bits) input.words) :
    (toPredecessor (input := input) p).Sorted ↔ p.Sorted := by
  constructor
  · intro hs i j hi hj hij
    exact hs i j hi hj (Nat.le_of_lt hij)
  · intro hs i j hi hj hij
    by_cases e : i = j
    · subst j
      exact Nat.le_refl _
    · exact hs i j hi hj (by omega)

theorem toPredecessor_answer_iff
    (p : ColumnReduction.Slice (bits := bits) input.words)
    (key : Machine.Word bits) (k : Nat) :
    Predecessor.Answer (toPredecessor (input := input) p) key k ↔
      ColumnReduction.Answer p key k := by
  unfold Predecessor.Answer ColumnReduction.Answer
  rfl

/-- Execute the existing worker on the physical slice, with no writable arena. -/
theorem worker_correct_on_column
    (p : ColumnReduction.Slice (bits := bits) input.words)
    (key : Machine.Word bits) (sorted : p.Sorted) :
    let budget := 11 * (Nat.log2 (p.len + 1) + 1)
    ∃ r, run (Predecessor.worker hcap) input budget
          (Predecessor.init (toPredecessor (input := input) p) key) = some r ∧
      ColumnReduction.Answer p key (Predecessor.lower r.finalState) ∧
      r.finalState.data = #[] ∧
      r.executed ≤ budget := by
  have hs := (toPredecessor_sorted_iff (input := input) p).2 sorted
  obtain ⟨r, hrun, hanswer, hdata, hsteps⟩ :=
    Predecessor.worker_correct (toPredecessor (input := input) p) key hs
  exact ⟨r, hrun, (toPredecessor_answer_iff (input := input) p key _).1 hanswer,
    hdata, hsteps⟩

end PaperB.RamPairSliceBinding
