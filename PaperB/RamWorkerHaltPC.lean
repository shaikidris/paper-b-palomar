module

public import PaperB.RamTracePreHalt
public import PaperB.RamPredecessorWorker

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram

variable {bits : Nat} {L : Layout bits}

theorem halted_fetch_and_state {code : Program L} {input : Input L} {s t : State L}
    (h : step code input s = some (.halted t)) :
    code[s.pc]? = some Instr.halt ∧ t = s := by
  have rejectNext (pc : Nat) (u : State L)
      (he : (if pc < code.size then some (Transition.next u) else none) =
        some (.halted t)) : False := by
    by_cases hb : pc < code.size
    · rw [if_pos hb] at he
      cases he
    · rw [if_neg hb] at he
      cases he
  cases hf : code[s.pc]? with
  | none => simp [step, hf, Option.bind_eq_bind, Option.bind] at h
  | some op =>
    cases op <;> simp only [step, hf, Option.bind_eq_bind, Option.bind] at h
    case halt =>
      cases h
      exact ⟨rfl, rfl⟩
    all_goals
      try unfold Option.bind at h
      first
      | change (if _ < code.size then some (Transition.next (L := L) _) else none) =
          some (.halted t) at h
      | split at h
    all_goals
      first
      | change (if _ < code.size then some (Transition.next (L := L) _) else none) =
          some (.halted t) at h
        exact False.elim (rejectNext _ _ h)
      | split at h <;> cases h
      | cases h

private theorem worker_halt_slot {cap : Nat} {hcap : cap ≤ 2 ^ bits} {pc : Nat}
    (hf : (Predecessor.worker hcap)[pc]? = some Instr.halt) : pc = 11 := by
  have hb : pc < 12 := by
    by_cases hi : pc < 12
    · exact hi
    · have ho : ¬ pc < (Predecessor.worker hcap).size := by
        rw [Predecessor.worker_size (hcap := hcap)]
        exact hi
      simp [getElem?_neg, ho] at hf
  let isHalt : Option (Instr bits 7) → Bool
    | some .halt => true
    | _ => false
  have scan (i : Nat) (hi : i < 12) :
      isHalt ((Predecessor.worker hcap)[i]?) = decide (i = 11) := by
    have hs : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
        i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  exact of_decide_eq_true (by simpa only [hf, isHalt] using (scan pc hb).symm)

theorem worker_halt_pc {cap : Nat} {hcap : cap ≤ 2 ^ bits}
    {input : Input (Predecessor.layout bits cap hcap)}
    {s t : State (Predecessor.layout bits cap hcap)}
    (h : step (Predecessor.worker hcap) input s = some (.halted t)) :
    s.pc = 11 ∧ t = s := by
  obtain ⟨hf, ht⟩ := halted_fetch_and_state h
  exact ⟨worker_halt_slot hf, ht⟩

/-- Replacing a halt slot without resizing preserves every original `.next` step. -/
theorem step_next_of_halt_slot_patch {p q : Program L} {slot : Nat}
    (hh : p[slot]? = some Instr.halt) (hs : p.size = q.size)
    (hp : ∀ i : Nat, i ≠ slot → q[i]? = p[i]?)
    {input : Input L} {s t : State L}
    (h : step p input s = some (.next t)) : step q input s = some (.next t) := by
  have hn : s.pc ≠ slot := by
    intro he
    have hf : p[s.pc]? = some Instr.halt := by simpa only [he] using hh
    simp [step, hf, Option.bind_eq_bind, Option.bind] at h
  have heq : step p input s = step q input s := by
    unfold step
    rw [hp s.pc hn]
    cases p[s.pc]? with
    | none => rfl
    | some op =>
      cases op <;> simp only [Option.bind_eq_bind, Option.bind]
      all_goals
        first
        | change (if _ < p.size then some (Transition.next (L := L) _) else none) =
            (if _ < q.size then some (Transition.next (L := L) _) else none)
          rw [hs]
        | refine congrArg (Option.bind (_ : Option (PaperB.Machine.Word bits))) ?_
          funext w
        | split <;> try simp only [dif_pos, dif_neg, *]
      all_goals
        change (if _ < p.size then some (Transition.next (L := L) _) else none) =
          (if _ < q.size then some (Transition.next (L := L) _) else none)
        rw [hs]
  exact heq.symm.trans h

end PaperB.RamProgram
