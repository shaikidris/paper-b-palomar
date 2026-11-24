module

public import PaperB.RamSearchCorrect

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram

theorem SuccessfulTrace.toSteps {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s : State L}
    {states : List (State L)} {r : Result L}
    (h : SuccessfulTrace code input s states r) :
    ∃ (n : Nat) (prehalt : State L),
      Steps code input n s prehalt ∧
      step code input prehalt = some (.halted r.finalState) ∧
      r.executed = n + 1 := by
  induction h with
  | halted hs =>
    exact ⟨0, _, Steps.zero _, hs, rfl⟩
  | next hs _ ih =>
    obtain ⟨n, prehalt, hsteps, hhalt, hcount⟩ := ih
    exact ⟨n + 1, prehalt, Steps.cons hs hsteps, hhalt,
      congrArg (fun k : Nat => k + 1) hcount⟩

theorem run_has_steps_then_halt {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {fuel : Nat}
    {s : State L} {r : Result L}
    (h : run code input fuel s = some r) :
    ∃ (n : Nat) (prehalt : State L),
      Steps code input n s prehalt ∧
      step code input prehalt = some (.halted r.finalState) ∧
      r.executed = n + 1 := by
  obtain ⟨states, htrace⟩ := run_has_successfulTrace h
  exact SuccessfulTrace.toSteps htrace

end PaperB.RamProgram
