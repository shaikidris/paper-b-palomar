module

public import PaperB.ForestHead
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace ShortCircuitSpace

universe u
variable {A : Type u}

def scan (test : A → Bool) : List A → Bool × Nat
  | [] => (true, 0)
  | a :: rest =>
    if test a = true then
      let r := scan test rest
      (r.1, r.2 + 1)
    else
      (false, 1)

inductive At (test : A → Bool) (xs : List A) : List A → Nat → Prop where
  | start : At test xs xs 0
  | advance {a : A} {rest : List A} {frames : Nat} :
      At test xs (a :: rest) frames → test a = true →
      At test xs rest (frames + 1)

theorem at_length {test : A → Bool} {xs rest : List A} {frames : Nat}
    (h : At test xs rest frames) : frames + rest.length = xs.length := by
  induction h <;> simp_all only [List.length_cons, Nat.zero_add] <;> omega

theorem scan_visits_le (test : A → Bool) (xs : List A) :
    (scan test xs).2 ≤ xs.length := by
  induction xs with
  | nil => simp [scan]
  | cons a rest ih =>
    cases h : test a <;> simp [scan, h, List.length_cons] <;> omega

theorem at_visits_le {test : A → Bool} {xs rest : List A} {frames : Nat}
    (h : At test xs rest frames) : frames + (scan test rest).2 ≤ xs.length := by
  calc
    frames + (scan test rest).2 ≤ frames + rest.length :=
      Nat.add_le_add_left (scan_visits_le test rest) frames
    _ = xs.length := at_length h

theorem scan_value (test : A → Bool) (xs : List A) :
    (scan test xs).1 = List.all xs test := by
  induction xs with
  | nil => simp [scan, List.all]
  | cons a rest ih =>
    cases h : test a <;> simp [scan, List.all, h, ih]

end ShortCircuitSpace

namespace PaperB.ForestHead

variable {α : Type}

private theorem scan_tests_eq (test : α → Bool × Nat) (xs : List α) :
    (scan test xs).tests = (ShortCircuitSpace.scan (fun x => (test x).1) xs).2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : (test x).1 = true <;>
      simp [scan, ShortCircuitSpace.scan, h, ih]

/-- A reached recursive scan can charge each suspended frame and every
remaining test to distinct entries of the original predecessor row. -/
theorem scan_prefix_frames_tests (test : α → Bool × Nat) {xs todo : List α}
    {frames : Nat} (atCursor : ShortCircuitSpace.At (fun x => (test x).1) xs todo frames) :
    frames + todo.length = xs.length ∧
      frames + (scan test todo).tests ≤ xs.length := by
  refine ⟨ShortCircuitSpace.at_length atCursor, ?_⟩
  rw [scan_tests_eq]
  exact ShortCircuitSpace.at_visits_le atCursor

end PaperB.ForestHead
