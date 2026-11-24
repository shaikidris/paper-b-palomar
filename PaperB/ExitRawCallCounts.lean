module

public import PaperB.ExitRawIncoming
public import PaperB.ExitPackedRuntime -- Only needed for the installer block below.

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.BuiltExit.RawIncoming

open PaperB.ExitMap PaperB.LabelledQuotient PaperB.ExitSummary

variable {A V T : Type}

structure CountedRun where
  values : Values
  fusedCalls : Nat
  labelledOccurrenceVisits : Nat

section
variable [DecidableEq V]
variable (endpoint : Fin 2 → V) (rank : T → Nat)
variable (readArc : A → V × T) (knownLoss : V → Bool) (fused : V → Values)

/-- The filter predicate for the exact count, not an extra test in `runCounted`. -/
def fusedEligible (a : A) : Bool :=
  let s := (readArc a).1
  let b₀ := decide (s = endpoint 0)
  let b₁ := decide (s = endpoint 1)
  match b₀ || b₁ with
  | true => false
  | false => knownLoss s

/-- The branches of `arcValue`, with a count of one only at the fused call. -/
@[inline] def arcValueCounted (a : A) : Values × Nat :=
  let row := readArc a
  let s := row.1
  let tail := row.2
  let b₀ := decide (s = endpoint 0)
  let b₁ := decide (s = endpoint 1)
  match b₀ || b₁ with
  | true =>
    let point := singleton (rank tail)
    (tab (fun j => if (if j = 0 then b₀ else b₁) then point else .empty), 0)
  | false =>
    match knownLoss s with
    | true => (fused s, 1)
    | false => (zero, 0)

private theorem arcValueCounted_eq (a : A) :
    arcValueCounted endpoint rank readArc knownLoss fused a =
      (arcValue endpoint rank readArc knownLoss fused a,
        if fusedEligible endpoint readArc knownLoss a then 1 else 0) := by
  cases he : ((decide ((readArc a).1 = endpoint 0) : Bool) ||
      decide ((readArc a).1 = endpoint 1)) with
  | false =>
    cases hl : knownLoss (readArc a).1 <;>
      simp only [arcValueCounted, arcValue, fusedEligible, he, hl] <;> rfl
  | true =>
    simp only [arcValueCounted, arcValue, fusedEligible, he] <;> rfl

@[inline] private def countedStep (acc : CountedRun) (a : A) : CountedRun :=
  let out := arcValueCounted endpoint rank readArc knownLoss fused a
  ⟨vjoin acc.values out.1, acc.fusedCalls + out.2,
    acc.labelledOccurrenceVisits + 1⟩

/-- A single fold over the stored list, charging one visit per occurrence. -/
def runCounted (incoming : List A) : CountedRun :=
  incoming.foldl (countedStep endpoint rank readArc knownLoss fused) ⟨zero, 0, 0⟩

private theorem foldl_counted (xs : List A) (acc : CountedRun) :
    xs.foldl (countedStep endpoint rank readArc knownLoss fused) acc =
      { values := xs.foldl
          (fun v a => vjoin v (arcValue endpoint rank readArc knownLoss fused a))
          acc.values
        fusedCalls := acc.fusedCalls +
          (xs.filter (fusedEligible endpoint readArc knownLoss)).length
        labelledOccurrenceVisits := acc.labelledOccurrenceVisits + xs.length } := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    simp only [List.foldl_cons, ih]
    cases h : fusedEligible endpoint readArc knownLoss a <;>
      simp [countedStep, arcValueCounted_eq, List.filter_cons, h,
        Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The values are those of the actual `run`. The filter is on the original
list, so repeated qualifying occurrences each contribute one call. -/
theorem runCounted_spec (incoming : List A) :
    runCounted endpoint rank readArc knownLoss fused incoming =
      { values := run endpoint rank readArc knownLoss fused incoming
        fusedCalls := (incoming.filter (fusedEligible endpoint readArc knownLoss)).length
        labelledOccurrenceVisits := incoming.length } := by
  simpa [runCounted, run] using
    (foldl_counted endpoint rank readArc knownLoss fused incoming ⟨zero, 0, 0⟩)

theorem runCounted_fusedCalls_le (incoming : List A) :
    (runCounted endpoint rank readArc knownLoss fused incoming).fusedCalls ≤
        (incoming.filter (fusedEligible endpoint readArc knownLoss)).length ∧
    (runCounted endpoint rank readArc knownLoss fused incoming).fusedCalls ≤
        incoming.length := by
  rw [runCounted_spec]
  constructor
  · exact Nat.le_refl _
  · apply List.length_filter_le

end

end PaperB.BuiltExit.RawIncoming

namespace PaperB.BuiltExit.PackedRuntime.ExactCount

/-- Installer-only count: use the existing missing-lane guards. -/
def install_count {H n bits} (r : Input H n bits) (driver parent : Fin n) : Nat :=
  Input.installFreshCalls r driver parent

theorem install_count_le_two {H n bits}
    (r : Input H n bits) (driver parent : Fin n) :
    install_count r driver parent ≤ 2 := by
  simp only [install_count, Input.installFreshCalls]
  split <;> split <;> decide

end PaperB.BuiltExit.PackedRuntime.ExactCount
