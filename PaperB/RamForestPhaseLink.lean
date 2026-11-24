module

public import PaperB.RamAppendLink

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamProgram.FixedROM

variable {bits : Nat} {L : Layout bits}

/-- A pipeline component with a unique halt instruction. The linker
replaces it with a jump into the succeeding code. -/
structure Phase (L : Layout bits) where
  code : Program L
  haltPC : Nat
  haltFits : haltPC < code.size
  haltAt : code[haltPC]? = some .halt
  uniqueHalt : ∀ i, code[i]? = some .halt → i = haltPC

/-- Boolean recognition of an instruction that can precede the unique halt. -/
def nonHalt (op : Instr bits L.registerCount) : Bool :=
  match op with
  | .halt => false
  | _ => true

def Phase.ofLast (code : Program L) (last : Nat) (size : code.size = last + 1)
    (halted : code[last]? = some .halt)
    (noEarly : (code.toList.take last).all (@nonHalt bits L) = true) : Phase L where
  code := code
  haltPC := last
  haltFits := by omega
  haltAt := halted
  uniqueHalt := by
    intro i got
    have bound : i < code.size := by
      by_cases h : i < code.size
      · exact h
      · have gone : code[i]? = none := getElem?_neg code i h
        rw [gone] at got
        cases got
    by_cases early : i < last
    · have cell : (code.toList.take last)[i]? = some .halt := by
        rw [List.getElem?_take_of_lt early, Array.getElem?_toList, got]
      have impossible : @nonHalt bits L .halt = true :=
        List.all_eq_true.mp noEarly _ (List.mem_of_getElem? cell)
      cases impossible
    · omega

def Phase.link (first second : Phase L) : Phase L where
  code := join first.code second.code first.haltPC first.haltFits
  haltPC := first.code.size + second.haltPC
  haltFits := by
    rw [join, Array.size_append, Array.size_set, Array.size_map]
    exact Nat.add_lt_add_left second.haltFits _
  haltAt := relocated_right first.code second.code first.haltFits _ .halt second.haltAt
  uniqueHalt := by
    intro i got
    by_cases left : i < first.code.size
    · by_cases old : i = first.haltPC
      · rw [old, (fetch_halt first.code second.code first.haltFits).1] at got
        cases got
      · unfold join at got
        rw [Array.getElem?_append_left (by rw [Array.size_set]; exact left),
          Array.getElem?_set_ne first.haltFits (Ne.symm old)] at got
        exact (old (first.uniqueHalt i got)).elim
    · unfold join at got
      rw [Array.getElem?_append_right (by rw [Array.size_set]; omega),
        Array.size_set, Array.getElem?_map] at got
      cases h : second.code[i - first.code.size]? with
      | none => simp [h] at got
      | some op =>
        rw [h, Option.map_some] at got
        have prev : op = .halt := by cases op <;> cases got <;> rfl
        subst op
        have position := second.uniqueHalt _ h
        omega

/-- Each local run starts at PC 0. Linking preserves registers and memory
without restarting or allocating at a phase boundary. -/
def Phase.initial {L : Layout bits} (s : State L) : State L := {s with pc := 0}

@[simp] theorem Phase.initial_data (s : State L) : (Phase.initial s).data = s.data := rfl

def pipeline : List (Phase L) → Program L
  | [] => #[.halt]
  | p :: ps => join p.code (pipeline ps) p.haltPC p.haltFits

theorem pipeline_nonempty (phases : List (Phase L)) : 0 < (pipeline phases).size := by
  cases phases with
  | nil => exact (show 0 < 1 by decide)
  | cons p ps =>
    unfold pipeline join
    rw [Array.size_append, Array.size_set, Array.size_map]
    have room := p.haltFits
    omega

inductive PhasesRun (input : Input L) :
    List (Phase L) → State L → State L → Nat → Prop
  | nil {s : State L} :
      PhasesRun input [] s (Phase.initial s) 1
  | cons {p : Phase L} {ps : List (Phase L)} {s t u : State L} {a b : Nat} :
      run p.code input a (Phase.initial s) = some ⟨t, a⟩ →
      PhasesRun input ps t u b →
      PhasesRun input (p :: ps) s u (a + b)

/-- Link a returning phase to an already verified executable suffix.
The suffix may have more than one halt. All registers and arena cells
are carried across the jump, and both local instruction counts are exact. -/
theorem run_linked_pair (p : Phase L) (right : Program L) (nonempty : 0 < right.size)
    {input : Input L} {start middle u : State L} {a b : Nat}
    (first : run p.code input a (Phase.initial start) = some ⟨middle, a⟩)
    (second : run right input b (Phase.initial middle) = some ⟨u, b⟩) :
    let code := join p.code right p.haltPC p.haltFits
    ∃ v states, v.regs = u.regs ∧ v.data = u.data ∧
      run code input (a + b) (Phase.initial start) = some ⟨v, a + b⟩ ∧
      SuccessfulTrace code input (Phase.initial start) states ⟨v, a + b⟩ ∧
      tracePeakWords input states = footprint L := by
  let code := join p.code right p.haltPC p.haltFits
  have jmp : Steps code input a (Phase.initial start)
      {middle with pc := p.code.size} := by
    have src : relocateStatePC 0 (Phase.initial start) = Phase.initial start := rfl
    have link := linked_return_of_run_multi (linked := code) (base := 0)
      (ret := fun _ => p.code.size) first
      (fun i op h nonhalt => by
        have neq : i ≠ p.haltPC := fun e => nonhalt
          (Option.some.inj (h.symm.trans (e.symm ▸ p.haltAt)))
        have same : relocateInstr 0 op = op := by cases op <;> simp only [relocateInstr, Nat.zero_add]
        simpa only [code, Nat.zero_add, same] using fetch_left p.code right p.haltFits neq h)
      (fun i h => by
        rw [p.uniqueHalt i h, Nat.zero_add]
        have patched := fetch_halt p.code right p.haltFits
        exact ⟨patched.1, patched.2 nonempty⟩)
    rw [src] at link
    exact link
  obtain ⟨k, last, route, halt, cost⟩ := run_has_steps_then_halt second
  have placed : RelocatedSlice right code p.code.size :=
    relocated_right p.code right p.haltFits
  have after := route.relocate placed
  have sameEntry : relocateStatePC p.code.size (Phase.initial middle) =
      {middle with pc := p.code.size} := by
    simp only [relocateStatePC, Phase.initial, Nat.add_zero]
  rw [sameEntry] at after
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input (relocateStatePC p.code.size last) =
      some (.halted (relocateStatePC p.code.size u)) := by
    change u = last at sameHalt
    rw [sameHalt]
    exact step_halt_at (s := relocateStatePC p.code.size last) (placed last.pc .halt atHalt)
  have execution := (jmp.append after).halts terminal
  change b = k + 1 at cost
  rw [Nat.add_assoc, ← cost] at execution
  obtain ⟨states, checked⟩ := run_has_successfulTrace execution
  exact ⟨relocateStatePC p.code.size u, states, rfl, rfl, execution, checked, checked.peak_eq⟩

/-- Link the exact sum of local work. Since all phases use the same
layout, the peak charges the one physical arena at every step. -/
theorem run_pipeline {input : Input L} {phases : List (Phase L)}
    {s t : State L} {work : Nat} (trace : PhasesRun input phases s t work) :
    ∃ u states, u.regs = t.regs ∧ u.data = t.data ∧
      run (pipeline phases) input work (Phase.initial s) = some ⟨u, work⟩ ∧
      SuccessfulTrace (pipeline phases) input (Phase.initial s) states ⟨u, work⟩ ∧
      tracePeakWords input states = footprint L := by
  induction trace with
  | @nil start =>
    have stop : step (pipeline ([] : List (Phase L))) input (Phase.initial start) =
        some (.halted (Phase.initial start)) := step_halt_at rfl
    have exec := (Steps.zero (Phase.initial start)).halts stop
    obtain ⟨states, ht⟩ := run_has_successfulTrace exec
    exact ⟨_, states, rfl, rfl, exec, ht, ht.peak_eq⟩
  | @cons p ps start middle final a b first rest ih =>
    obtain ⟨u, _, regs, data, second, _, _⟩ := ih
    obtain ⟨t, trace, sameRegs, sameData, exec, checked, peak⟩ :=
      run_linked_pair p (pipeline ps) (pipeline_nonempty ps) first second
    exact ⟨t, trace, sameRegs.trans regs, sameData.trans data, exec, checked, peak⟩

end PaperB.RamProgram.FixedROM
