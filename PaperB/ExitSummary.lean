module

-- PaperB/ExitSummary.lean
-- Toolchain: leanprover/lean4:v4.35.0-rc3
public import Std
public import PaperB.ExitMap

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitSummary

open PaperB.ExitMap

def singleton (rank : Nat) : Interval := .span rank rank

/-- Fold the original tail ranks into their min-max interval. -/
def summary (ranks : List Nat) : Interval :=
  ranks.foldr (fun rank acc => Interval.join (singleton rank) acc) .empty

@[simp] theorem summary_nil : summary [] = .empty := rfl

@[simp] theorem summary_cons (rank : Nat) (ranks : List Nat) :
    summary (rank :: ranks) = Interval.join (singleton rank) (summary ranks) :=
  rfl

theorem summary_append (xs ys : List Nat) :
    summary (xs ++ ys) = Interval.join (summary xs) (summary ys) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, summary_cons, ih, Interval.join_assoc]

/-- Test containment in `[tin, tout)`. An empty summary always passes. -/
def endpointsInside (tin tout : Nat) : Interval → Bool
  | .empty => true
  | .span lo hi => decide (tin ≤ lo ∧ hi < tout)

@[simp] theorem endpointsInside_span_iff (tin tout lo hi : Nat) :
    endpointsInside tin tout (.span lo hi) = true ↔ tin ≤ lo ∧ hi < tout := by
  simp [endpointsInside]

private theorem endpointsInside_join_iff (tin tout : Nat) (a b : Interval) :
    endpointsInside tin tout (Interval.join a b) = true ↔
      endpointsInside tin tout a = true ∧ endpointsInside tin tout b = true := by
  cases a with
  | empty => simp [endpointsInside]
  | span lo hi =>
    cases b with
    | empty => simp [endpointsInside]
    | span lo' hi' =>
      simp only [Interval.join, endpointsInside_span_iff, Nat.min_def, Nat.max_def]
      split <;> split <;>
        (constructor
         · rintro ⟨hl, hh⟩
           exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
         · rintro ⟨⟨hl, hh⟩, ⟨hl', hh'⟩⟩
           exact ⟨by omega, by omega⟩)

theorem endpointsInside_summary_iff (tin tout : Nat) (ranks : List Nat) :
    endpointsInside tin tout (summary ranks) = true ↔
      ∀ rank ∈ ranks, tin ≤ rank ∧ rank < tout := by
  induction ranks with
  | nil =>
    -- There are no tail ranks to check.
    simp [endpointsInside]
  | cons x xs ih =>
    simp only [summary_cons, endpointsInside_join_iff, singleton,
      endpointsInside_span_iff, ih]
    constructor
    · rintro ⟨hx, hxs⟩ rank hrank
      rcases List.mem_cons.mp hrank with h | h
      · subst rank
        exact hx
      · exact hxs rank h
    · intro h
      exact ⟨h x (List.mem_cons.mpr (Or.inl rfl)),
        fun rank hrank => h rank (List.mem_cons.mpr (Or.inr hrank))⟩

end PaperB.ExitSummary
