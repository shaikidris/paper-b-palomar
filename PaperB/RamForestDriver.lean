module

public import PaperB.RamForestDriverCost

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamForestDriver

theorem run_driver
    {bits} {N} {L : PaperB.RamProgram.Layout bits}
    (code : PaperB.RamProgram.Program L) (input : PaperB.RamProgram.Input L)
    (g : PaperB.ForestLayout.ChildLists N)
    (enterBase exitBase childUnit : Nat) (bodyPC haltPC)
    (Rel : PaperB.ForestLayout.State N → PaperB.RamProgram.State L → Prop)
    (emptyGuard : ∀ ref s, Rel ref s → ref.stack = [] →
      PaperB.RamProgram.step code input s = some (.next {s with pc := haltPC}))
    (activeGuard : ∀ ref s cmd tail, Rel ref s → ref.stack = cmd :: tail →
      PaperB.RamProgram.step code input s = some (.next {s with pc := bodyPC}))
    (body : ∀ ref s cmd tail, Rel ref s → ref.stack = cmd :: tail →
      ∃ t, PaperB.RamProgram.Steps code input
          (PaperB.RamForestDriverCost.bodyCost enterBase exitBase childUnit g cmd)
          {s with pc := bodyPC} t ∧
        Rel (PaperB.ForestLayout.advance g ref cmd tail) t)
    (haltInstr : code[haltPC]? = some .halt)
    (fuel : Nat) (ref : PaperB.ForestLayout.State N) (s : PaperB.RamProgram.State L)
    (initial : Rel ref s)
    (complete : (PaperB.ForestLayout.run g fuel ref).stack = []) :
    let w := PaperB.RamForestDriverCost.traversalWork g enterBase exitBase childUnit fuel ref
    ∃ (u : PaperB.RamProgram.State L) (states : List (PaperB.RamProgram.State L)),
      Rel (PaperB.ForestLayout.run g fuel ref) u ∧
      PaperB.RamProgram.run code input (w + 2) s =
        some ⟨{u with pc := haltPC}, w + 2⟩ ∧
      PaperB.RamProgram.SuccessfulTrace code input s states
        ⟨{u with pc := haltPC}, w + 2⟩ ∧
      PaperB.RamProgram.tracePeakWords input states = PaperB.RamProgram.footprint L := by
  have simulate : ∀ (k : Nat) (r : PaperB.ForestLayout.State N)
      (q : PaperB.RamProgram.State L), Rel r q →
      ∃ u : PaperB.RamProgram.State L,
        PaperB.RamProgram.Steps code input
          (PaperB.RamForestDriverCost.traversalWork g enterBase exitBase childUnit k r) q u ∧
        Rel (PaperB.ForestLayout.run g k r) u := by
    intro k
    induction k with
    | zero =>
        intro r q hRel
        exact ⟨q, PaperB.RamProgram.Steps.zero q, hRel⟩
    | succ k ih =>
        intro r q hRel
        cases hStack : r.stack with
        | nil =>
            have hZero : PaperB.RamProgram.Steps code input 0 q q :=
              PaperB.RamProgram.Steps.zero q
            apply Exists.intro q
            constructor
            · simpa only [PaperB.RamForestDriverCost.traversalWork, hStack] using hZero
            · simpa only [PaperB.ForestLayout.run, hStack] using hRel
        | cons cmd tail =>
            obtain ⟨t, bodySteps, hNext⟩ := body r q cmd tail hRel hStack
            obtain ⟨u, suffixSteps, hFinal⟩ :=
              ih (PaperB.ForestLayout.advance g r cmd tail) t hNext
            have hWork :
                PaperB.RamForestDriverCost.traversalWork g enterBase exitBase childUnit
                    (Nat.succ k) r =
                  (1 + PaperB.RamForestDriverCost.bodyCost enterBase exitBase childUnit g cmd) +
                    PaperB.RamForestDriverCost.traversalWork g enterBase exitBase childUnit k
                      (PaperB.ForestLayout.advance g r cmd tail) := by
              simp only [PaperB.RamForestDriverCost.traversalWork, hStack]
            apply Exists.intro u
            constructor
            · rw [hWork, Nat.add_assoc, Nat.add_comm 1]
              exact PaperB.RamProgram.Steps.cons
                (activeGuard r q cmd tail hRel hStack)
                (bodySteps.append suffixSteps)
            · simpa only [PaperB.ForestLayout.run, hStack] using hFinal

  obtain ⟨u, workSteps, hFinal⟩ := simulate fuel ref s initial
  let w := PaperB.RamForestDriverCost.traversalWork g enterBase exitBase childUnit fuel ref
  let finalState : PaperB.RamProgram.State L := {u with pc := haltPC}
  have hGuard : PaperB.RamProgram.step code input u = some (.next finalState) :=
    emptyGuard (PaperB.ForestLayout.run g fuel ref) u hFinal complete
  have guardSteps : PaperB.RamProgram.Steps code input 1 u finalState :=
    PaperB.RamProgram.Steps.cons hGuard (PaperB.RamProgram.Steps.zero finalState)
  have toHalt : PaperB.RamProgram.Steps code input (w + 1) s finalState :=
    workSteps.append guardSteps
  have hHalt :
      PaperB.RamProgram.step code input finalState = some (.halted finalState) := by
    apply PaperB.RamProgram.step_halt_at
    exact haltInstr
  have hRun : PaperB.RamProgram.run code input (w + 2) s =
      some ⟨finalState, w + 2⟩ :=
    toHalt.halts hHalt
  obtain ⟨states, hTrace⟩ :
      ∃ states, PaperB.RamProgram.SuccessfulTrace code input s states
        ⟨finalState, w + 2⟩ := by
    apply PaperB.RamProgram.run_has_successfulTrace
    exact hRun
  exact ⟨u, states, hFinal, hRun, hTrace, hTrace.peak_eq⟩

end PaperB.RamForestDriver
