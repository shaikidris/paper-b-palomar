module

public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Exit-map algebra
File: `PaperB/ExitMap.lean`
Toolchain: `leanprover/lean4:v4.35.0-rc3`
-/

namespace PaperB.ExitMap

inductive Interval where
  | empty
  | span (lo hi : Nat)

namespace Interval

def join : Interval → Interval → Interval
  | .empty, b => b
  | a, .empty => a
  | .span lo hi, .span lo' hi' => .span (min lo lo') (max hi hi')

@[simp] theorem empty_join (a : Interval) : join .empty a = a := by
  cases a <;> rfl

@[simp] theorem join_empty (a : Interval) : join a .empty = a := by
  cases a <;> rfl

theorem join_assoc (a b c : Interval) :
    join (join a b) c = join a (join b c) := by
  cases a <;> cases b <;> cases c <;>
    simp [join, Nat.min_assoc, Nat.max_assoc]

theorem join_comm (a b : Interval) : join a b = join b a := by
  cases a <;> cases b <;> simp [join, Nat.min_comm, Nat.max_comm]

end Interval

universe u v

structure Two (α : Type u) where
  x0 : α
  x1 : α

namespace Two

variable {α : Type u} {β : Type v}

def get (xs : Two α) (i : Fin 2) : α :=
  if i = 0 then xs.x0 else xs.x1

def map (f : α → β) (xs : Two α) : Two β :=
  ⟨f xs.x0, f xs.x1⟩

@[simp] theorem get_zero (xs : Two α) : get xs 0 = xs.x0 := by
  simp [get]

@[simp] theorem get_one (xs : Two α) : get xs 1 = xs.x1 := by
  have h : (1 : Fin 2) ≠ 0 := by decide
  simp [get, h]

@[simp] theorem get_map (f : α → β) (xs : Two α) (i : Fin 2) :
    get (map f xs) i = f (get xs i) := by
  by_cases h : i = 0 <;> simp [get, map, h]

end Two

abbrev Values := Two Interval

structure Coord where
  base : Interval
  slot : Option (Fin 2)

abbrev Map := Two Coord

namespace Coord

def eval (c : Coord) (xs : Values) : Interval :=
  match c.slot with
  | none => c.base
  | some i => Interval.join c.base (Two.get xs i)

/-- Substitute the selected inner coordinate, if the outer coordinate copies one. -/
def compose (inner : Map) (outer : Coord) : Coord :=
  match outer.slot with
  | none => outer
  | some i =>
    let c := Two.get inner i
    ⟨Interval.join outer.base c.base, c.slot⟩

theorem eval_compose (inner : Map) (outer : Coord) (xs : Values) :
    eval (compose inner outer) xs =
      eval outer (Two.map (fun c => eval c xs) inner) := by
  cases outer with
  | mk base slot =>
    cases slot with
    | none => rfl
    | some i =>
      cases h : Two.get inner i with
      | mk innerBase innerSlot =>
        cases innerSlot <;> simp [compose, eval, h, Interval.join_assoc]

end Coord

namespace Map

def eval (m : Map) (xs : Values) : Values :=
  Two.map (fun c => Coord.eval c xs) m

/-- Traversal order: evaluate `inner` first, then `outer`. -/
def compose (inner outer : Map) : Map :=
  Two.map (Coord.compose inner) outer

theorem eval_compose_get (inner outer : Map) (xs : Values) (i : Fin 2) :
    Two.get (eval (compose inner outer) xs) i =
      Two.get (eval outer (eval inner xs)) i := by
  simp [eval, compose, Coord.eval_compose]

def identity : Map :=
  ⟨⟨.empty, some 0⟩, ⟨.empty, some 1⟩⟩

@[simp] theorem eval_identity (xs : Values) : eval identity xs = xs := by
  cases xs <;> simp [eval, identity, Two.map, Coord.eval]

end Map

end PaperB.ExitMap
