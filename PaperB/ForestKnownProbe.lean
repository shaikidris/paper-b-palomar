module

public import PaperB.ForestSlimIndex
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace CountedProbe

universe u v w z

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type z}

def read (a : Array α) (i : Nat) : Option α × Nat :=
  (a[i]?, 1)

def mapC (f : α → β) (x : α × Nat) : β × Nat :=
  (f x.1, x.2)

def bindC (x : α × Nat) (f : α → β × Nat) : β × Nat :=
  let y := f x.1
  (y.1, x.2 + y.2)

def readD (a : Array α) (i : Nat) (fallback : α) : α × Nat :=
  mapC (fun x => x.getD fallback) (read a i)

end CountedProbe

namespace PaperB.RetainedProperLoss.Columns

open PaperB.LabelledQuotient

variable {H : LabelledQuotient}

/-- Read the actual four cells used by the known-node membership test. -/
def knownProbed (s : Columns H) (a i : Nat) : Bool × Nat :=
  CountedProbe.bindC (CountedProbe.readD s.labels i 0) fun label =>
    CountedProbe.bindC (CountedProbe.readD s.entry label 0) fun entry =>
      CountedProbe.bindC (CountedProbe.readD s.entry a 0) fun lo =>
        CountedProbe.mapC (fun hi => decide (lo ≤ entry) && decide (entry < hi))
          (CountedProbe.readD s.stop a 0)

theorem knownProbed_exact (s : Columns H) (a i : Nat) :
    s.knownProbed a i = (s.known a i, 4) :=
  rfl

theorem knownProbed_eq_knownCounted (s : Columns H) (a i : Nat) :
    s.knownProbed a i = s.knownCounted a i :=
  rfl

end PaperB.RetainedProperLoss.Columns
