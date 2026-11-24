module

public import PaperB.ExitRawCallCounts
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace OptionalWork

universe u v w

def select {α : Type u} {β : Type v}
    (choice : Option α) (fallback : β) (f : α → β) : β :=
  match choice with
  | none => fallback
  | some x => f x

theorem project {α : Type u} {β : Type v} {γ : Type w}
    (choice : Option α) (fallback : β) (f : α → β) (g : β → γ) :
    g (select choice fallback f) =
      select choice (g fallback) (fun x => g (f x)) := by
  cases choice <;> rfl

theorem measure_le {α : Type u} {β : Type v}
    (choice : Option α) (fallback : β) (f : α → β)
    (cost : β → Nat) (cap : Nat)
    (hFallback : cost fallback ≤ cap)
    (hSome : ∀ (x : α), choice = some x → cost (f x) ≤ cap) :
    cost (select choice fallback f) ≤ cap := by
  cases choice with
  | none => exact hFallback
  | some x => exact hSome x rfl

end OptionalWork

namespace PaperB.BuiltExit.PackedRuntime.ExactCount

open PaperB.LabelledQuotient PaperB.ExitMap PaperB.ExitSummary
open PaperB.StaticHeadSweep (Slots)

variable {H : LabelledQuotient} {n bits : Nat}

def countedBase (r : Input H n bits) (bases : Slots H.vertexCount (Option Values))
    (y : Fin H.vertexCount) : RawIncoming.CountedRun :=
  OptionalWork.select (r.owners.read y) ⟨zero, 0, 0⟩ fun cut =>
    RawIncoming.runCounted (r.orientation.read cut).endpoint r.entryRank.read
      r.arcFields (r.knownLoss cut) (r.fused bases cut) (ForestIncomingRaw.row H r.rows y)

theorem countedBase_value (r : Input H n bits) (bases : Slots H.vertexCount (Option Values))
    (y : Fin H.vertexCount) :
    (countedBase r bases y).values = r.base bases y := by
  unfold countedBase Input.base
  rw [OptionalWork.project (g := RawIncoming.CountedRun.values)]
  cases h : r.owners.read y with
  | none => rfl
  | some cut =>
    simp only [OptionalWork.select, RawIncoming.runCounted_spec, Input.rowRun]

theorem countedBase_calls_le (r : Input H n bits) (bases : Slots H.vertexCount (Option Values))
    (y : Fin H.vertexCount) :
    (countedBase r bases y).fusedCalls ≤ (ForestIncomingRaw.row H r.rows y).length := by
  unfold countedBase
  apply OptionalWork.measure_le
  · exact Nat.zero_le _
  · intro cut _
    exact (RawIncoming.runCounted_fusedCalls_le _ _ _ _ _ _).2

theorem countedBase_visits_le (r : Input H n bits) (bases : Slots H.vertexCount (Option Values))
    (y : Fin H.vertexCount) :
    (countedBase r bases y).labelledOccurrenceVisits ≤
      (ForestIncomingRaw.row H r.rows y).length := by
  unfold countedBase
  apply OptionalWork.measure_le
  · exact Nat.zero_le _
  · intro cut _
    rw [RawIncoming.runCounted_spec]
    exact Nat.le_refl _

end PaperB.BuiltExit.PackedRuntime.ExactCount
