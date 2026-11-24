module

public import PaperB.RamWorkerHaltPC

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram

variable {bits cap : Nat} {hcap : cap ≤ 2 ^ bits}
variable {input : Input (Predecessor.layout bits cap hcap)}
variable {s t : State (Predecessor.layout bits cap hcap)}

private theorem workerFetchBound {i : Nat} {op : Instr bits 7}
    (hf : (Predecessor.worker hcap)[i]? = some op) : i < 12 := by
  by_cases hi : i < 12
  · exact hi
  · have ho : ¬ i < (Predecessor.worker hcap).size := by
      rwa [Predecessor.worker_size (hcap := hcap)]
    simp [getElem?_neg, ho] at hf

variable {linked : Program (Predecessor.layout bits cap hcap)} {base ret : Nat}

theorem worker_return_of_trace {n : Nat}
    {u : State (Predecessor.layout bits cap hcap)}
    (placedPrefix : ∀ i op, i < 11 → (Predecessor.worker hcap)[i]? = some op →
      linked[base + i]? = some (relocateInstr base op))
    (slot : linked[base + 11]? = some (.goto ret)) (target : ret < linked.size)
    (trace : Steps (Predecessor.worker hcap) input n s u)
    (halt : step (Predecessor.worker hcap) input u = some (.halted t)) :
    Steps linked input (n + 1) (relocateStatePC base s) { t with pc := ret } ∧
      t.data = s.data := by
  obtain ⟨hpc, rfl⟩ := worker_halt_pc halt
  have inBounds : base + 11 < linked.size := by
    by_cases hb : base + 11 < linked.size
    · exact hb
    · simp [getElem?_neg, hb] at slot
  let shadow := linked.set (base + 11) Instr.halt inBounds
  have sizeEq : shadow.size = linked.size := by simp [shadow, Array.size_set]
  have shadowHalt : shadow[base + 11]? = some Instr.halt := by
    have hb : base + 11 < shadow.size := by simpa only [sizeEq] using inBounds
    rw [getElem?_pos shadow _ hb] <;> simp [shadow, Array.getElem_set]
  have other (i : Nat) (hi : i ≠ base + 11) : linked[i]? = shadow[i]? := by
    by_cases hb : i < linked.size
    · have hs : i < shadow.size := by simpa only [sizeEq] using hb
      rw [getElem?_pos linked i hb, getElem?_pos shadow i hs] <;>
        simp [shadow, Array.getElem_set, hi, Ne.symm hi]
    · have hs : ¬ i < shadow.size := by simpa only [sizeEq] using hb
      rw [getElem?_neg linked i hb, getElem?_neg shadow i hs]
  have placed : RelocatedSlice (Predecessor.worker hcap) shadow base := by
    intro i op hf
    by_cases hi : i = 11
    · subst i
      have actual : (Predecessor.worker hcap)[11]? = some Instr.halt := rfl
      have he := Option.some.inj (actual.symm.trans hf)
      subst op
      exact shadowHalt
    · have hb := workerFetchBound hf
      rw [← other (base + i) (by omega)]
      exact placedPrefix i op (by omega) hf
  have transfer {k : Nat} {a b : State (Predecessor.layout bits cap hcap)}
      (h : Steps shadow input k a b) : Steps linked input k a b := by
    induction h with
    | zero a => exact Steps.zero a
    | cons head tail ih =>
      exact Steps.cons (step_next_of_halt_slot_patch shadowHalt sizeEq other head) ih
  have fetch : linked[(relocateStatePC base t).pc]? = some (.goto ret) := by
    simpa only [relocateStatePC, hpc] using slot
  have jump : step linked input (relocateStatePC base t) =
      some (.next { t with pc := ret }) := step_goto_at fetch target
  refine ⟨(transfer (trace.relocate placed)).append (Steps.cons jump (Steps.zero _)), ?_⟩
  exact (Array.eq_empty_of_size_eq_zero t.data_size).trans
    (Array.eq_empty_of_size_eq_zero s.data_size).symm

private abbrev WorkerRunOK (fuel n : Nat)
    (input : Input (Predecessor.layout bits cap hcap))
    (s t : State (Predecessor.layout bits cap hcap)) : Prop := by
  first
  | exact run (Predecessor.worker hcap) input fuel s = some ⟨t, n⟩
  | exact run (Predecessor.worker hcap) input s fuel = some ⟨t, n⟩
  | exact run fuel (Predecessor.worker hcap) input s = some ⟨t, n⟩
  | exact run (Predecessor.worker hcap) input fuel s = some ⟨n, t⟩
  | exact run (Predecessor.worker hcap) input s fuel = some ⟨n, t⟩
  | exact run fuel (Predecessor.worker hcap) input s = some ⟨n, t⟩

/-- The return jump replaces the counted halt; only the final PC changes. -/
theorem worker_linked_return {fuel n : Nat}
    (placedPrefix : ∀ i op, i < 11 → (Predecessor.worker hcap)[i]? = some op →
      linked[base + i]? = some (relocateInstr base op))
    (slot : linked[base + 11]? = some (.goto ret)) (target : ret < linked.size)
    (ok : WorkerRunOK fuel n input s t) :
    Steps linked input n (relocateStatePC base s) { t with pc := ret } ∧
      t.data = s.data := by
  have finish {k : Nat} {u : State (Predecessor.layout bits cap hcap)}
      (hs : Steps (Predecessor.worker hcap) input k s u)
      (hh : step (Predecessor.worker hcap) input u = some (.halted t))
      (hn : k + 1 = n) :
      Steps linked input n (relocateStatePC base s) { t with pc := ret } ∧
        t.data = s.data :=
    hn ▸ worker_return_of_trace placedPrefix slot target hs hh
  obtain ⟨k, u, hsteps, hhalt, hcount⟩ := run_has_steps_then_halt ok
  exact finish hsteps hhalt hcount.symm

end PaperB.RamProgram
