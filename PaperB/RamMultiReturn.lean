module

public import PaperB.RamWorkerReturn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RamProgram

/-- A `.next` step transfers when the current fetch and program size agree.
This proof does not need access to the private `advance` or `writeReg`. -/
private theorem step_next_if_fetch_size_for_link
    {bits : Nat} {L : Layout bits} {p q : Program L}
    {input : Input L} {s t : State L}
    (hs : p.size = q.size)
    (hf : q[s.pc]? = p[s.pc]?)
    (h : step p input s = some (.next t)) :
    step q input s = some (.next t) := by
  have heq : step p input s = step q input s := by
    unfold step
    rw [hf]
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

/-- Relocate the nonhalting trace, then execute the return jump at the
actual local halt PC. Only the final PC changes. -/
theorem linked_return_of_trace_multi
    {bits : Nat} {L : Layout bits}
    {code linked : Program L} {input : Input L}
    {s u t : State L} {base n : Nat} {ret : Nat → Nat}
    (placedNonhalt : ∀ i op, code[i]? = some op → op ≠ Instr.halt →
      linked[base + i]? = some (relocateInstr base op))
    (placedHalts : ∀ i, code[i]? = some Instr.halt →
      linked[base + i]? = some (.goto (ret i)) ∧ ret i < linked.size)
    (trace : Steps code input n s u)
    (halt : step code input u = some (.halted t)) :
    Steps linked input (n + 1) (relocateStatePC base s)
      { t with pc := ret t.pc } := by
  classical
  obtain ⟨haltFetch, ht⟩ := halted_fetch_and_state halt
  subst t

  have localInBounds (i : Nat) (op : Instr bits L.registerCount)
      (hf : code[i]? = some op) : base + i < linked.size := by
    have hex : ∃ linkedOp : Instr bits L.registerCount,
        linked[base + i]? = some linkedOp := by
      by_cases hh : op = Instr.halt
      · subst op
        exact ⟨.goto (ret i), (placedHalts i hf).1⟩
      · exact ⟨relocateInstr base op, placedNonhalt i op hf hh⟩
    obtain ⟨_, hfetch⟩ := hex
    by_cases hb : base + i < linked.size
    · exact hb
    · simp [getElem?_neg, hb] at hfetch

  let sourceAt (j : Nat) : Option (Instr bits L.registerCount) :=
    if base ≤ j then code[j - base]? else none

  have sourceIndex (j : Nat) (op : Instr bits L.registerCount)
      (hf : sourceAt j = some op) :
      base + (j - base) = j ∧ code[j - base]? = some op := by
    by_cases hb : base ≤ j
    · exact ⟨by omega, by simpa only [sourceAt, if_pos hb] using hf⟩
    · simp [sourceAt, hb] at hf

  -- Proof-only program: override every local cell and keep the rest of `linked`.
  let shadow : Program L :=
    Array.ofFn fun j : Fin linked.size =>
      match sourceAt j.val with
      | some op => relocateInstr base op
      | none => linked[j.val]'(j.isLt)

  have sizeEq : shadow.size = linked.size := by
    simp [shadow, Array.size_ofFn]

  have shadowFetch (j : Nat) :
      shadow[j]? =
        (match sourceAt j with
        | some op => some (relocateInstr base op)
        | none => linked[j]?) := by
    by_cases hj : j < linked.size
    · have hs : j < shadow.size := by simpa only [sizeEq] using hj
      rw [getElem?_pos shadow j hs, getElem?_pos linked j hj]
      cases hsrc : sourceAt j <;> simp [shadow, Array.getElem_ofFn, hsrc]
    · have hs : ¬ j < shadow.size := by simpa only [sizeEq] using hj
      rw [getElem?_neg shadow j hs, getElem?_neg linked j hj]
      cases hsrc : sourceAt j with
      | none => rfl
      | some op =>
        obtain ⟨he, hf⟩ := sourceIndex j op hsrc
        have hb := localInBounds (j - base) op hf
        rw [he] at hb
        exact (hj hb).elim

  have placed : RelocatedSlice code shadow base := by
    intro i op hf
    have hle : base ≤ base + i := by omega
    have hsub : base + i - base = i := by omega
    have hsrc : sourceAt (base + i) = some op := by
      simpa only [sourceAt, if_pos hle, hsub] using hf
    simpa only [hsrc] using (shadowFetch (base + i))

  have sameFetchOfNext {a b : State L}
      (h : step shadow input a = some (.next b)) :
      linked[a.pc]? = shadow[a.pc]? := by
    rw [shadowFetch]
    cases hf : sourceAt a.pc with
    | none => rfl
    | some op =>
      have hnonhalt : op ≠ Instr.halt := by
        intro he
        subst op
        have hh : shadow[a.pc]? = some Instr.halt := by
          simpa only [hf, relocateInstr] using (shadowFetch a.pc)
        simp [step, hh, Option.bind_eq_bind, Option.bind] at h
      obtain ⟨he, hlocal⟩ := sourceIndex a.pc op hf
      simpa only [he] using
        (placedNonhalt (a.pc - base) op hlocal hnonhalt)

  have transfer {k : Nat} {a b : State L}
      (h : Steps shadow input k a b) : Steps linked input k a b := by
    induction h with
    | zero a => exact Steps.zero a
    | cons head tail ih =>
      exact Steps.cons
        (step_next_if_fetch_size_for_link sizeEq (sameFetchOfNext head) head) ih

  obtain ⟨slot, target⟩ := placedHalts u.pc haltFetch
  have fetch : linked[(relocateStatePC base u).pc]? =
      some (.goto (ret u.pc)) := by
    simpa only [relocateStatePC] using slot
  have jump : step linked input (relocateStatePC base u) =
      some (.next { u with pc := ret u.pc }) :=
    step_goto_at fetch target
  exact (transfer (trace.relocate placed)).append
    (Steps.cons jump (Steps.zero _))

/-- A verified local run reaches the continuation for its actual halt PC
in exactly `r.executed` linked steps, with its registers and data unchanged. -/
theorem linked_return_of_run_multi
    {bits : Nat} {L : Layout bits}
    {code linked : Program L} {input : Input L} {s : State L} {r : Result L}
    {fuel base : Nat} {ret : Nat → Nat}
    (hRun : run code input fuel s = some r)
    (placedNonhalt : ∀ i op, code[i]? = some op → op ≠ Instr.halt →
      linked[base + i]? = some (relocateInstr base op))
    (placedHalts : ∀ i, code[i]? = some Instr.halt →
      linked[base + i]? = some (.goto (ret i)) ∧ ret i < linked.size) :
    Steps linked input r.executed (relocateStatePC base s)
      { r.finalState with pc := ret r.finalState.pc } := by
  obtain ⟨n, prehalt, trace, halt, count⟩ := run_has_steps_then_halt hRun
  rw [count]
  exact linked_return_of_trace_multi placedNonhalt placedHalts trace halt

end PaperB.RamProgram
