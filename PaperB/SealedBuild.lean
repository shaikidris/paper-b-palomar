module

public import PaperB.RamProgram

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.SealedBuild

open PaperB.Machine (Word)
open PaperB.RamProgram (Layout Input State Program Result run run_executed_le)

variable {bits : Nat} {L : Layout bits}

theorem copyPrefix_size (cfg : SealLayout L) (s : State L) :
    (copyPrefix cfg s).size = cfg.k := by
  simp [copyPrefix]

theorem copyPrefix_fits (cfg : SealLayout L) (s : State L) :
    (copyPrefix cfg s).size ≤ 2 ^ bits :=
  Nat.le_trans (Nat.le_of_eq (copyPrefix_size cfg s)) (Nat.le_trans cfg.k_le_workCap L.workFits)

theorem copyPrefix_getElem (cfg : SealLayout L) (s : State L) (i : Fin cfg.k) :
    (copyPrefix cfg s)[i.val]'(by simpa only [copyPrefix_size] using i.isLt) =
      s.data[i.val]'(by
        rw [s.data_size]
        exact Nat.lt_of_lt_of_le i.isLt cfg.k_le_workCap) := by
  simp only [copyPrefix, Array.getElem_ofFn]

/-- Counts model word slots and operations, not Lean runtime overhead.
Code, control bookkeeping, and this telemetry are not charged.
Only `sealedWords` is retained as the built artifact. -/
structure Observation (bits : Nat) where
  sealedWords : Array (Word bits)
  steps : Nat
  operations : Nat
  peakConstructionWords : Nat
  retainedWords : Nat

private def finish (cfg : SealLayout L) (words : Array (Word bits))
    (r : Result L) : Observation bits :=
  let sealedWords := copyPrefix cfg r.finalState
  { sealedWords := sealedWords
    steps := r.executed
    operations := r.executed + L.registerCount + L.workCap + sealedWords.size
    peakConstructionWords :=
      words.size + L.registerCount + L.workCap + sealedWords.size
    retainedWords := sealedWords.size }

/-- Run fixed bytecode on the already serialized input, sealing only on halt. -/
def build (cfg : SealLayout L) (code : Program L) (words : Array (Word bits))
    (words_size : words.size = L.inputCap) (fuel : Nat) :
    Option (Observation bits) :=
  match run code ⟨words, words_size⟩ fuel (initialState L) with
  | none => none
  | some r => some (finish cfg words r)

theorem build_spec {cfg : SealLayout L} {code : Program L}
    {words : Array (Word bits)} {words_size : words.size = L.inputCap}
    {fuel : Nat} {o : Observation bits}
    (h : build cfg code words words_size fuel = some o) :
    ∃ r : Result L,
      run code ⟨words, words_size⟩ fuel (initialState L) = some r ∧
      o.sealedWords = copyPrefix cfg r.finalState ∧
      o.sealedWords.size = cfg.k ∧
      o.sealedWords.size ≤ 2 ^ bits ∧
      o.steps = r.executed ∧
      r.executed ≤ fuel ∧
      o.operations = o.steps + L.registerCount + L.workCap + cfg.k ∧
      o.peakConstructionWords =
        words.size + L.registerCount + L.workCap + cfg.k ∧
      o.retainedWords = o.sealedWords.size := by
  cases hr : run code ⟨words, words_size⟩ fuel (initialState L) with
  | none => simp [build, hr] at h
  | some r =>
    have ho : finish cfg words r = o := by
      simpa [build, hr] using h
    subst o
    refine ⟨r, ?_, rfl, copyPrefix_size cfg r.finalState,
      copyPrefix_fits cfg r.finalState, rfl, run_executed_le hr, ?_, ?_, rfl⟩
    · first | exact hr | rfl
    · simp [finish, copyPrefix_size]
    · simp [finish, copyPrefix_size]

end PaperB.SealedBuild
