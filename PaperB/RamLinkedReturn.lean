module

public import PaperB.RamWorkerReturn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram

/-- Relocate the nonhalting trace, then take the linked return jump in place of
the local halt. The final state changes only in its PC. -/
theorem linked_return_of_trace {bits : Nat} {L : Layout bits}
    {code linked : Program L} {input : Input L}
    {s u t : State L} {base ret n : Nat}
    (placedExcept : ∀ i op, i ≠ t.pc → code[i]? = some op →
      linked[base + i]? = some (relocateInstr base op))
    (slot : linked[base + t.pc]? = some (.goto ret))
    (target : ret < linked.size)
    (trace : Steps code input n s u)
    (halt : step code input u = some (.halted t)) :
    Steps linked input (n + 1) (relocateStatePC base s) { t with pc := ret } := by
  obtain ⟨haltFetch, ht⟩ := halted_fetch_and_state halt
  subst t
  have inBounds : base + u.pc < linked.size := by
    by_cases hb : base + u.pc < linked.size
    · exact hb
    · simp [getElem?_neg, hb] at slot
  let shadow := linked.set (base + u.pc) Instr.halt inBounds
  have sizeEq : shadow.size = linked.size := by
    simp [shadow, Array.size_set]
  have shadowHalt : shadow[base + u.pc]? = some Instr.halt := by
    have hb : base + u.pc < shadow.size := by
      simpa only [sizeEq] using inBounds
    rw [getElem?_pos shadow _ hb] <;> simp [shadow, Array.getElem_set]
  have other (i : Nat) (hi : i ≠ base + u.pc) :
      linked[i]? = shadow[i]? := by
    by_cases hb : i < linked.size
    · have hs : i < shadow.size := by simpa only [sizeEq] using hb
      rw [getElem?_pos linked i hb, getElem?_pos shadow i hs] <;>
        simp [shadow, Array.getElem_set, hi, Ne.symm hi]
    · have hs : ¬ i < shadow.size := by simpa only [sizeEq] using hb
      rw [getElem?_neg linked i hb, getElem?_neg shadow i hs]
  have placed : RelocatedSlice code shadow base := by
    intro i op hf
    by_cases hi : i = u.pc
    · subst i
      have hop : Instr.halt = op := Option.some.inj (haltFetch.symm.trans hf)
      subst op
      exact shadowHalt
    · rw [← other (base + i) (by omega)]
      exact placedExcept i op hi hf
  have transferNext {a b : State L}
      (h : step shadow input a = some (.next b)) :
      step linked input a = some (.next b) := by
    first
    | exact step_next_of_halt_slot_patch shadowHalt sizeEq other h
    | have hne : a.pc ≠ base + u.pc := by
        intro he
        have hf : shadow[a.pc]? = some Instr.halt := by
          simpa only [he] using shadowHalt
        simp [step, hf] at h
      have hf := other a.pc hne
      simpa only [step, hf, advance, sizeEq] using h
  have transfer {k : Nat} {a b : State L}
      (h : Steps shadow input k a b) : Steps linked input k a b := by
    induction h with
    | zero a => exact Steps.zero a
    | cons head tail ih => exact Steps.cons (transferNext head) ih
  have fetch : linked[(relocateStatePC base u).pc]? = some (.goto ret) := by
    simpa only [relocateStatePC] using slot
  have jump : step linked input (relocateStatePC base u) =
      some (.next { u with pc := ret }) := step_goto_at fetch target
  exact (transfer (trace.relocate placed)).append (Steps.cons jump (Steps.zero _))

/-- A successful local run reaches the linked continuation in exactly
`r.executed` steps, with the data and register arrays of `r.finalState`. -/
theorem linked_return_of_run {bits : Nat} {L : Layout bits}
    {code linked : Program L} {input : Input L} {s : State L} {r : Result L}
    {fuel base ret : Nat}
    (hRun : run code input fuel s = some r)
    (placedExcept : ∀ i op, i ≠ r.finalState.pc → code[i]? = some op →
      linked[base + i]? = some (relocateInstr base op))
    (slot : linked[base + r.finalState.pc]? = some (.goto ret))
    (target : ret < linked.size) :
    Steps linked input r.executed (relocateStatePC base s)
      { r.finalState with pc := ret } := by
  obtain ⟨n, prehalt, trace, halt, count⟩ := run_has_steps_then_halt hRun
  rw [count]
  exact linked_return_of_trace placedExcept slot target trace halt

end PaperB.RamProgram
