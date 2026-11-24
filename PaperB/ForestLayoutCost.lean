module

public import PaperB.ForestLayout

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout

variable {N : Nat}

def commandPotential (weight : Fin N → Nat) : Command N → Nat
  | .enter v => weight v
  | .exit _ => 1

def stackPotential (weight : Fin N → Nat) (stack : List (Command N)) : Nat :=
  (stack.map (commandPotential weight)).sum

@[simp] theorem stackPotential_nil (weight : Fin N → Nat) :
    stackPotential weight [] = 0 := rfl

@[simp] theorem stackPotential_cons (weight : Fin N → Nat) (cmd : Command N)
    (rest : List (Command N)) :
    stackPotential weight (cmd :: rest) =
      commandPotential weight cmd + stackPotential weight rest := by
  simp only [stackPotential, List.map_cons, List.sum_cons]

theorem stackPotential_map_enter_append (weight : Fin N → Nat)
    (kids : List (Fin N)) (rest : List (Command N)) :
    stackPotential weight (kids.map Command.enter ++ rest) =
      (kids.map weight).sum + stackPotential weight rest := by
  induction kids with
  | nil => simp
  | cons v vs ih =>
    simp [commandPotential, List.sum_cons, ih, Nat.add_assoc]

theorem weight_ge_two (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (v : Fin N) : 2 ≤ weight v := by
  rw [hweight v]
  exact Nat.le_add_right _ _

theorem commandPotential_ge_one (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (cmd : Command N) : 1 ≤ commandPotential weight cmd := by
  cases cmd with
  | enter v =>
    exact Nat.le_trans (show 1 ≤ 2 by decide) (weight_ge_two g weight hweight v)
  | exit v => exact Nat.le_refl 1

theorem length_le_stackPotential (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (stack : List (Command N)) :
    stack.length ≤ stackPotential weight stack := by
  induction stack with
  | nil => simp
  | cons cmd rest ih =>
    simpa only [List.length_cons, stackPotential_cons, Nat.add_comm 1 rest.length]
      using Nat.add_le_add (commandPotential_ge_one g weight hweight cmd) ih

theorem stackPotential_eq_zero_iff (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (stack : List (Command N)) :
    stackPotential weight stack = 0 ↔ stack = [] := by
  constructor
  · intro hp
    have hlen : stack.length ≤ 0 := hp ▸ length_le_stackPotential g weight hweight stack
    cases stack with
    | nil => rfl
    | cons cmd rest => simp at hlen
  · intro hs
    simp [hs]

/-- Popping the head and executing it removes exactly one unit of potential. -/
theorem advance_stackPotential (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (s : State N) (cmd : Command N) (rest : List (Command N)) :
    stackPotential weight (cmd :: rest) =
      stackPotential weight (advance g s cmd rest).stack + 1 := by
  cases cmd with
  | enter v =>
    have ht : (advance g s (.enter v) rest).stack =
        (g.get v).map Command.enter ++ (.exit v :: rest) := by
      cases s
      simp [advance, pushChildren_spec]
    rw [ht, stackPotential_map_enter_append]
    simp only [stackPotential_cons, commandPotential, hweight v]
    calc
      2 + ((g.get v).map weight).sum + stackPotential weight rest =
          (1 + 1) + ((g.get v).map weight).sum + stackPotential weight rest := rfl
      _ = ((g.get v).map weight).sum + (1 + stackPotential weight rest) + 1 := by
        ac_rfl
  | exit v =>
    simpa only [stackPotential_cons, commandPotential, (advance_exit_spec g s v rest).1]
      using Nat.add_comm 1 (stackPotential weight rest)

theorem run_exact_of_ge (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (fuel : Nat) (s : State N) (hfuel : stackPotential weight s.stack ≤ fuel) :
    (run g fuel s).stack = [] ∧
      (run g fuel s).processed = s.processed + stackPotential weight s.stack := by
  induction fuel generalizing s with
  | zero =>
    have hp : stackPotential weight s.stack = 0 :=
      Nat.le_antisymm hfuel (Nat.zero_le _)
    have hs : s.stack = [] :=
      (stackPotential_eq_zero_iff g weight hweight s.stack).mp hp
    simp [run, hs]
  | succ fuel ih =>
    cases hs : s.stack with
    | nil => simp [run, hs]
    | cons cmd rest =>
      have hstep := advance_stackPotential g weight hweight s cmd rest
      have hnext : stackPotential weight (advance g s cmd rest).stack ≤ fuel := by
        apply Nat.le_of_succ_le_succ
        change stackPotential weight (advance g s cmd rest).stack + 1 ≤ fuel + 1
        rw [← hstep]
        simpa only [hs] using hfuel
      obtain ⟨hempty, hprocessed⟩ := ih (advance g s cmd rest) hnext
      simp only [run, hs]
      refine ⟨hempty, ?_⟩
      calc
        _ = (advance g s cmd rest).processed +
              stackPotential weight (advance g s cmd rest).stack := hprocessed
        _ = s.processed + stackPotential weight (cmd :: rest) := by
          rw [advance_processed, hstep, Nat.add_right_comm s.processed 1 _, Nat.add_assoc]

theorem layout_exact_of_ge (g : ChildLists N) (weight : Fin N → Nat)
    (hweight : ∀ v, weight v = 2 + ((g.get v).map weight).sum)
    (root : Fin N) (fuel : Nat) (hfuel : weight root ≤ fuel) :
    (layout g root fuel).stack = [] ∧ (layout g root fuel).processed = weight root := by
  have hinit : stackPotential weight (initial root).stack ≤ fuel := by
    simpa [initial, commandPotential] using hfuel
  simpa [layout, initial, State.processed, commandPotential] using
    run_exact_of_ge g weight hweight fuel (initial root) hinit

end PaperB.ForestLayout
