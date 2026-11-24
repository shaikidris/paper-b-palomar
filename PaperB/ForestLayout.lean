module

public import PaperB.ForestIntervalQuery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout

variable {N V : Nat}

/-- One ordered child list per node, including the synthetic root. -/
structure ChildLists (N : Nat) where
  rows : Array (List (Fin N))
  rows_size : rows.size = N

@[inline] def ChildLists.get (g : ChildLists N) (v : Fin N) : List (Fin N) :=
  g.rows[v.val]'(by rw [g.rows_size]; exact v.isLt)

inductive Command (N : Nat) where
  | enter (v : Fin N)
  | exit (v : Fin N)

structure State (N : Nat) where
  stack : List (Command N)
  entries : Array Nat
  ends : Array Nat
  entries_size : entries.size = N
  ends_size : ends.size = N
  enters : Nat
  exits : Nat
  childrenQueued : Nat

def State.processed (s : State N) : Nat := s.enters + s.exits

def initial (root : Fin N) : State N :=
  ⟨[.enter root], Array.replicate N 0, Array.replicate N 0,
    by simp, by simp, 0, 0, 0⟩

/-- Allocate the two zero-filled banks independently in the compiled DFS. -/
def initialIndependent (root : Fin N) : State N :=
  ⟨[.enter root], Array.replicate N 0, Array.ofFn (fun _ : Fin N => 0),
    by simp, by simp, 0, 0, 0⟩

@[csimp] theorem initial_csimp : @initial = @initialIndependent := by
  funext n root
  have same : Array.replicate n (0 : Nat) = Array.ofFn (fun _ : Fin n => 0) := by
    apply Array.ext
    · simp
    · intro i h₁ h₂
      simp
  unfold initial initialIndependent
  congr

/-- Prepend the child commands in order and count them in the same fold. -/
def pushChildren (kids : List (Fin N)) (tail : List (Command N)) :
    List (Command N) × Nat :=
  kids.foldr (fun v p => (.enter v :: p.1, p.2 + 1)) (tail, 0)

theorem pushChildren_spec (kids : List (Fin N)) (tail : List (Command N)) :
    pushChildren kids tail = (kids.map Command.enter ++ tail, kids.length) := by
  induction kids with
  | nil => rfl
  | cons v vs ih =>
    change
      (Command.enter v :: (pushChildren vs tail).1, (pushChildren vs tail).2 + 1) =
        ((Command.enter v :: vs.map Command.enter) ++ tail, vs.length + 1)
    simp [ih]

/-- Execute a popped command. `enters` is also the next entry timestamp. -/
def advance (g : ChildLists N) (s : State N) (cmd : Command N)
    (rest : List (Command N)) : State N :=
  match s with
  | ⟨_, tin, tout, hTin, hTout, en, ex, queued⟩ =>
    match cmd with
    | .enter v =>
      let p := pushChildren (g.get v) (.exit v :: rest)
      ⟨p.1, tin.set v.val en (by rw [hTin]; exact v.isLt), tout,
        by simp [hTin], hTout, en + 1, ex, queued + p.2⟩
    | .exit v =>
      ⟨rest, tin, tout.set v.val en (by rw [hTout]; exact v.isLt),
        hTin, by simp [hTout], en, ex + 1, queued⟩

theorem advance_enter_spec (g : ChildLists N) (s : State N) (v : Fin N)
    (rest : List (Command N)) :
    let t := advance g s (.enter v) rest
    t.stack = (g.get v).map Command.enter ++ (.exit v :: rest) ∧
    t.entries = s.entries.set v.val s.enters
      (by rw [s.entries_size]; exact v.isLt) ∧
    t.ends = s.ends ∧
    t.enters = s.enters + 1 ∧ t.exits = s.exits ∧
    t.childrenQueued = s.childrenQueued + (g.get v).length := by
  cases s
  simp [advance, pushChildren_spec]

theorem advance_exit_spec (g : ChildLists N) (s : State N) (v : Fin N)
    (rest : List (Command N)) :
    let t := advance g s (.exit v) rest
    t.stack = rest ∧ t.entries = s.entries ∧
    t.ends = s.ends.set v.val s.enters
      (by rw [s.ends_size]; exact v.isLt) ∧
    t.enters = s.enters ∧ t.exits = s.exits + 1 ∧
    t.childrenQueued = s.childrenQueued := by
  cases s
  simp [advance]

theorem advance_processed (g : ChildLists N) (s : State N) (cmd : Command N)
    (rest : List (Command N)) :
    (advance g s cmd rest).processed = s.processed + 1 := by
  cases s with
  | mk stack tin tout hTin hTout en ex queued =>
    cases cmd with
    | enter v => exact Nat.add_right_comm en 1 ex
    | exit v => exact (Nat.add_assoc en ex 1).symm

/-- Stop on an empty stack or exhausted fuel, retaining any pending commands. -/
def run (g : ChildLists N) : Nat → State N → State N
  | 0, s => s
  | fuel + 1, s =>
    match s.stack with
    | [] => s
    | cmd :: rest => run g fuel (advance g s cmd rest)

theorem run_processed_le (g : ChildLists N) (fuel : Nat) (s : State N) :
    (run g fuel s).processed ≤ s.processed + fuel := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    cases hs : s.stack with
    | nil =>
      simp only [run, hs]
      exact Nat.le_add_right _ _
    | cons cmd rest =>
      simp only [run, hs]
      calc
        _ ≤ (advance g s cmd rest).processed + fuel := ih _
        _ = s.processed + (fuel + 1) := by
          rw [advance_processed, Nat.add_assoc, Nat.add_comm 1 fuel]

/-- The fuel-bounded traversal state; no completion or interval property is assumed. -/
def layout (g : ChildLists N) (root : Fin N) (fuel : Nat) : State N :=
  run g fuel (initial root)

theorem layout_sizes (g : ChildLists N) (root : Fin N) (fuel : Nat) :
    (layout g root fuel).entries.size = N ∧
    (layout g root fuel).ends.size = N :=
  ⟨(layout g root fuel).entries_size, (layout g root fuel).ends_size⟩

theorem layout_processed_le (g : ChildLists N) (root : Fin N) (fuel : Nat) :
    (layout g root fuel).enters + (layout g root fuel).exits ≤ fuel := by
  simpa [layout, initial, State.processed] using
    (run_processed_le g fuel (initial root))

/-- Package the arrays and labels; this asserts sizes, not DFS correctness. -/
def State.toTables (s : State N) (labels : Array (Fin N))
    (h : labels.size = V) : PaperB.ForestIntervalQuery.Tables N V :=
  ⟨s.entries, s.ends, labels, s.entries_size, s.ends_size, h⟩

end PaperB.ForestLayout
