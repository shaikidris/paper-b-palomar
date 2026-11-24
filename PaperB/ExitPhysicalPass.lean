module

public import PaperB.ExitPhysicalOneSlot

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitPhysicalPass

open PaperB.Machine (Word)
open PaperB.ExitMap PaperB.ExitMap.Retention PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking PaperB.ExitStoredWrite PaperB.ExitPhysicalOneSlot

structure Ready {bits : Nat} (tags : TagsFit bits) (slots : Nat)
    (j : Job) (occ : Nat → Prop) (old : Store) : Prop where
  bound : j.slot < slots
  fresh : ¬ occ j.slot
  deps : j.Dependencies occ old
  fit : (storedCodec tags).valid (buildOneSlot old j.parent j.jump j.edge)

/-- A chronological schedule with logical initial and final states. -/
def Schedule {bits : Nat} (tags : TagsFit bits) (slots : Nat) :
    List Job → (Nat → Prop) → Store → (Nat → Prop) → Store → Prop
  | [], occ, old, dst, out => occ = dst ∧ old = out
  | j :: js, occ, old, dst, out =>
      Ready tags slots j occ old ∧
        Schedule tags slots js (j.occupy occ) (j.overlay old) dst out

variable {bits words slots : Nat}
variable (tags : TagsFit bits) (base : Word bits)
variable (layout : Layout base words slots)

/-- Hide all logical state in an erased argument to the runtime loop. -/
def RunReady (jobs : List Job) (bank : WriteResult bits words) : Prop :=
  ∃ (occ : Nat → Prop) (old : Store) (dst : Nat → Prop) (out : Store),
    OccupiedExact tags base layout bank occ old ∧
      Schedule tags slots jobs occ old dst out

theorem ready_of_schedule (jobs : List Job) (bank : WriteResult bits words)
    {occ dst : Nat → Prop} {old out : Store}
    (hex : OccupiedExact tags base layout bank occ old)
    (hs : Schedule tags slots jobs occ old dst out) :
    RunReady tags base layout jobs bank :=
  ⟨occ, old, dst, out, hex, hs⟩

private theorem headReady (bank : WriteResult bits words) (j : Job) (js : List Job)
    (h : RunReady tags base layout (j :: js) bank) :
    j.slot < slots ∧ (storedCodec tags).valid (buildFromBank tags base layout bank j) := by
  rcases h with ⟨occ, old, dst, out, hex, hs⟩
  change Ready tags slots j occ old ∧
    Schedule tags slots js (j.occupy occ) (j.overlay old) dst out at hs
  exact ⟨hs.1.bound, buildFromBank_fit tags base layout bank j hex hs.1.deps hs.1.fit⟩

private theorem tailReady (bank : WriteResult bits words) (j : Job) (js : List Job)
    (h : RunReady tags base layout (j :: js) bank) :
    RunReady tags base layout js
      (step tags base layout bank j (headReady tags base layout bank j js h).1
        (headReady tags base layout bank j js h).2) := by
  have r := headReady tags base layout bank j js h
  rcases h with ⟨occ, old, dst, out, hex, hs⟩
  change Ready tags slots j occ old ∧
    Schedule tags slots js (j.occupy occ) (j.overlay old) dst out at hs
  exact ⟨j.occupy occ, j.overlay old, dst, out,
    step_exact tags base layout bank j r.1 r.2 hex hs.1.fresh hs.1.deps, hs.2⟩

/-- One step per job, passing only the updated bank to the tail call. -/
def run : (jobs : List Job) → (bank : WriteResult bits words) →
    RunReady tags base layout jobs bank → WriteResult bits words
  | [], bank, _ => bank
  | j :: js, bank, h =>
      let r := headReady tags base layout bank j js h
      let next := step tags base layout bank j r.1 r.2
      run js next (tailReady tags base layout bank j js h)
termination_by structural jobs => jobs

theorem run_exact (jobs : List Job) {dst : Nat → Prop} {out : Store} :
    ∀ (bank : WriteResult bits words) (occ : Nat → Prop) (old : Store)
      (h : RunReady tags base layout jobs bank),
      OccupiedExact tags base layout bank occ old →
      Schedule tags slots jobs occ old dst out →
      OccupiedExact tags base layout (run tags base layout jobs bank h) dst out := by
  induction jobs with
  | nil =>
      intro bank occ old h hex hs
      change occ = dst ∧ old = out at hs
      rcases hs with ⟨rfl, rfl⟩
      simpa only [run] using hex
  | cons j js ih =>
      intro bank occ old h hex hs
      change Ready tags slots j occ old ∧
        Schedule tags slots js (j.occupy occ) (j.overlay old) dst out at hs
      let r := headReady tags base layout bank j js h
      let next := step tags base layout bank j r.1 r.2
      have hn : OccupiedExact tags base layout next (j.occupy occ) (j.overlay old) :=
        step_exact tags base layout bank j r.1 r.2 hex hs.1.fresh hs.1.deps
      rw [run]
      exact ih next (j.occupy occ) (j.overlay old)
        (tailReady tags base layout bank j js h) hn hs.2

theorem run_writes (jobs : List Job) :
    ∀ (bank : WriteResult bits words) (h : RunReady tags base layout jobs bank),
      (run tags base layout jobs bank h).writes = bank.writes + 18 * jobs.length := by
  induction jobs with
  | nil =>
      intro bank h
      simp [run]
  | cons j js ih =>
      intro bank h
      let r := headReady tags base layout bank j js h
      let next := step tags base layout bank j r.1 r.2
      have hs : next.writes = bank.writes + 18 :=
        step_writes tags base layout bank j r.1 r.2
      calc
        (run tags base layout (j :: js) bank h).writes =
            next.writes + 18 * js.length := by
          rw [run]
          exact ih next (tailReady tags base layout bank j js h)
        _ = bank.writes + 18 * (j :: js).length := by
          rw [hs, List.length_cons]
          omega

end PaperB.ExitPhysicalPass
