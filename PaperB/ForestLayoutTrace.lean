module

public import PaperB.ForestLayout

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout

open PaperB.ForestIntervalQuery

set_option maxHeartbeats 1000000

variable {N : Nat}

deriving instance DecidableEq for Command

/-- The vertices whose entry clocks have ticked in this event sequence. -/
def eventVertices : List (Command N) → List (Fin N)
  | [] => []
  | .enter v :: cs => v :: eventVertices cs
  | .exit _ :: cs => eventVertices cs

@[simp] theorem eventVertices_append (p q : List (Command N)) :
    eventVertices (p ++ q) = eventVertices p ++ eventVertices q := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    cases c <;> simp [eventVertices, ih]

/-- The last write to `key`, or `old` if there is no such write.
The clock is read before the current event ticks it. -/
def eventStamp (key : Command N) : List (Command N) → Nat → Nat → Nat
  | [], _, old => old
  | c :: cs, t, old =>
    eventStamp key cs (t + (eventVertices [c]).length)
      (if c = key then t else old)

theorem eventStamp_append (key : Command N) (p q : List (Command N))
    (t old : Nat) :
    eventStamp key (p ++ q) t old =
      eventStamp key q (t + (eventVertices p).length)
        (eventStamp key p t old) := by
  induction p generalizing t old with
  | nil => simp [eventStamp, eventVertices]
  | cons c p ih =>
    cases c <;>
      simp [eventStamp, eventVertices, ih, Nat.add_assoc, Nat.add_comm]

theorem eventStamp_of_not_mem (key : Command N) (cs : List (Command N))
    (t old : Nat) (h : key ∉ cs) :
    eventStamp key cs t old = old := by
  induction cs generalizing t old with
  | nil => rfl
  | cons c cs ih =>
    have hne : c ≠ key := by
      intro he
      apply h
      simp [he]
    rw [eventStamp, ite_eq_right hne]
    apply ih
    intro hm
    exact h (by simp [hm])

/-- A split at the last occurrence gives the actual write timestamp. -/
theorem eventStamp_last (key : Command N) (p q : List (Command N))
    (t old : Nat) (hq : key ∉ q) :
    eventStamp key (p ++ (key :: q)) t old =
      t + (eventVertices p).length := by
  rw [eventStamp_append]
  simp only [eventStamp]
  exact eventStamp_of_not_mem key q _ _ hq

private def readCell (xs : Array Nat) (i : Nat) : Nat :=
  xs[i]?.getD 0

private theorem readCell_eq (xs : Array Nat) (i : Nat) (hi : i < xs.size) :
    readCell xs i = xs[i] := by
  simp [readCell, getElem?_pos, hi]

private theorem readCell_set (xs : Array Nat) (i j value : Nat)
    (hi : i < xs.size) (hj : j < xs.size) :
    readCell (xs.set i value hi) j =
      if i = j then value else readCell xs j := by
  have hj' : j < (xs.set i value hi).size := by simpa using hj
  rw [readCell_eq _ _ hj', readCell_eq _ _ hj]
  by_cases h : i = j
  · subst j
    first
    | (simp <;> done)
    | simp [Array.getElem_set]
  · first
    | (simp [h] <;> done)
    | simp [Array.getElem_set, h]

def State.recorded (s : State N) : Command N → Nat
  | .enter a => readCell s.entries a.val
  | .exit a => readCell s.ends a.val

private theorem advance_recorded_trace (g : ChildLists N) (s : State N)
    (cmd : Command N) (rest : List (Command N)) (key : Command N) :
    (advance g s cmd rest).recorded key =
      if cmd = key then s.enters else s.recorded key := by
  cases cmd with
  | enter v =>
    obtain ⟨_, hin, hout, _, _, _⟩ := advance_enter_spec g s v rest
    cases key with
    | enter a =>
      simp only [State.recorded, hin]
      rw [readCell_set _ _ _ _ _ (by rw [s.entries_size]; exact a.isLt)]
      by_cases h : v = a
      · subst a
        simp
      · have hv : v.val ≠ a.val := fun e => h (Fin.ext e)
        simp [h, hv]
    | exit a =>
      simp [State.recorded, hout]
  | exit v =>
    obtain ⟨_, hin, hout, _, _, _⟩ := advance_exit_spec g s v rest
    cases key with
    | enter a =>
      simp [State.recorded, hin]
    | exit a =>
      simp only [State.recorded, hout]
      rw [readCell_set _ _ _ _ _ (by rw [s.ends_size]; exact a.isLt)]
      by_cases h : v = a
      · subst a
        simp
      · have hv : v.val ≠ a.val := fun e => h (Fin.ext e)
        simp [h, hv]

private theorem advance_enters_trace (g : ChildLists N) (s : State N)
    (cmd : Command N) (rest : List (Command N)) :
    (advance g s cmd rest).enters =
      s.enters + (eventVertices [cmd]).length := by
  cases cmd with
  | enter v =>
    obtain ⟨_, _, _, h, _, _⟩ := advance_enter_spec g s v rest
    simpa [eventVertices] using h
  | exit v =>
    obtain ⟨_, _, _, h, _, _⟩ := advance_exit_spec g s v rest
    simpa [eventVertices] using h

/-- Interpret pending commands as a full event suffix. An enter expands
to its whole subtree; an already-pending exit is just one event. -/
def stackEvents (trace : Fin N → List (Command N))
    (stack : List (Command N)) : List (Command N) :=
  stack.flatMap (fun
    | .enter v => trace v
    | .exit v => [.exit v])

private theorem stackEvents_children (trace : Fin N → List (Command N))
    (kids : List (Fin N)) (rest : List (Command N)) :
    stackEvents trace (kids.map Command.enter ++ rest) =
      kids.flatMap trace ++ stackEvents trace rest := by
  induction kids with
  | nil => rfl
  | cons v vs ih =>
    change trace v ++ stackEvents trace (vs.map Command.enter ++ rest) =
      (trace v ++ vs.flatMap trace) ++ stackEvents trace rest
    rw [ih, List.append_assoc]

theorem stackEvents_advance (g : ChildLists N)
    (trace : Fin N → List (Command N))
    (htrace : ∀ v, trace v =
      .enter v :: ((g.get v).flatMap trace ++ [.exit v]))
    (s : State N) (cmd : Command N) (rest : List (Command N)) :
    stackEvents trace (cmd :: rest) =
      cmd :: stackEvents trace (advance g s cmd rest).stack := by
  cases cmd with
  | enter v =>
    change trace v ++ stackEvents trace rest = _
    rw [(advance_enter_spec g s v rest).1, stackEvents_children, htrace v]
    simp [stackEvents, List.append_assoc]
  | exit v =>
    rw [(advance_exit_spec g s v rest).1]
    rfl

/-- Instrumentation only: the actual popped commands, in pop order. -/
def commandLog (g : ChildLists N) : Nat → State N → List (Command N)
  | 0, _ => []
  | fuel + 1, s =>
    match s.stack with
    | [] => []
    | c :: cs => c :: commandLog g fuel (advance g s c cs)

/-- The step invariant lifts to the entire run: sufficient fuel consumes
exactly the event suffix, and every array cell agrees with its last write
in that suffix (or retains its old value). -/
theorem run_event_trace (g : ChildLists N)
    (trace : Fin N → List (Command N))
    (htrace : ∀ v, trace v =
      .enter v :: ((g.get v).flatMap trace ++ [.exit v]))
    (fuel : Nat) (s : State N)
    (hfuel : (stackEvents trace s.stack).length ≤ fuel) :
    commandLog g fuel s = stackEvents trace s.stack ∧
    (run g fuel s).stack = [] ∧
    (run g fuel s).enters = s.enters + (eventVertices (stackEvents trace s.stack)).length ∧
    ∀ key, (run g fuel s).recorded key =
      eventStamp key (stackEvents trace s.stack) s.enters (s.recorded key) := by
  induction fuel generalizing s with
  | zero =>
    cases hs : s.stack with
    | nil =>
      simp [commandLog, run, hs, stackEvents, eventVertices, eventStamp]
    | cons c cs =>
      have hb : (stackEvents trace (c :: cs)).length ≤ 0 := by
        simpa only [hs] using hfuel
      rw [stackEvents_advance g trace htrace s c cs, List.length_cons] at hb
      omega
  | succ fuel ih =>
    cases hs : s.stack with
    | nil =>
      simp [commandLog, run, hs, stackEvents, eventVertices, eventStamp]
    | cons c cs =>
      have hstep : stackEvents trace s.stack =
          c :: stackEvents trace (advance g s c cs).stack := by
        simpa only [hs] using stackEvents_advance g trace htrace s c cs
      have hnext : (stackEvents trace (advance g s c cs).stack).length ≤ fuel := by
        rw [hstep, List.length_cons] at hfuel
        exact Nat.le_of_succ_le_succ hfuel
      obtain ⟨hlog, hempty, hen, hread⟩ := ih (advance g s c cs) hnext
      have hlogStep : commandLog g (fuel + 1) s =
          c :: commandLog g fuel (advance g s c cs) := by
        simp only [commandLog, hs]
      have hrunStep : run g (fuel + 1) s = run g fuel (advance g s c cs) := by
        simp only [run, hs]
      rw [hs] at hstep
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hlogStep, hlog, hstep]
      · have hstackStep : (run g (fuel + 1) s).stack =
            (run g fuel (advance g s c cs)).stack :=
          congrArg (fun t : State N => t.stack) hrunStep
        exact hstackStep.trans hempty
      · have hentersStep : (run g (fuel + 1) s).enters =
            (run g fuel (advance g s c cs)).enters :=
          congrArg (fun t : State N => t.enters) hrunStep
        rw [hentersStep, hen, advance_enters_trace g s c cs, hstep]
        change
          (s.enters + (eventVertices [c]).length) +
              (eventVertices (stackEvents trace (advance g s c cs).stack)).length =
            s.enters +
              (eventVertices ([c] ++ stackEvents trace (advance g s c cs).stack)).length
        rw [eventVertices_append, List.length_append, Nat.add_assoc]
      · intro key
        have hrecordedStep : (run g (fuel + 1) s).recorded key =
            (run g fuel (advance g s c cs)).recorded key :=
          congrArg (fun t : State N => t.recorded key) hrunStep
        rw [hrecordedStep, hread key, hstep, advance_enters_trace g s c cs,
          advance_recorded_trace g s c cs key] <;> rfl

section FunctionalTrace

private theorem flatMap_congr_mem {α β : Type} (xs : List α)
    (f g : α → List β) (h : ∀ x ∈ xs, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := h x (by simp)
    have hxs := ih (fun y hy => h y (by simp [hy]))
    simp only [List.flatMap_cons, hx, hxs]

end FunctionalTrace

end PaperB.ForestLayout
