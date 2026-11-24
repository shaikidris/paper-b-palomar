module

-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
public import Std
public import PaperB.WordOps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add sub band ltb)

variable {bits : Nat} {L : Layout bits}

theorem run_executed_le {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {r : Result L}
    (h : run code input fuel s = some r) : r.executed ≤ fuel := by
  induction fuel generalizing s r with
  | zero => simp [run] at h
  | succ n ih =>
    cases hs : step code input s with
    | none => simp [run, hs] at h
    | some out =>
      cases out with
      | halted t =>
        have hr : (⟨t, 1⟩ : Result L) = r := by simpa [run, hs] using h
        subst r
        exact Nat.succ_le_succ (Nat.zero_le n)
      | next t =>
        cases ht : run code input n t with
        | none => simp [run, hs, ht] at h
        | some q =>
          have hr : { q with executed := q.executed + 1 } = r := by
            simpa [run, hs, ht] using h
          subst r
          exact Nat.succ_le_succ (ih (s := t) (r := q) ht)

-- The input array is the same parameter throughout the run.
theorem run_preserves_lengths {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {r : Result L}
    (_ : run code input fuel s = some r) :
    r.finalState.data.size = s.data.size ∧ r.finalState.regs.size = s.regs.size :=
  ⟨r.finalState.data_size.trans s.data_size.symm,
   r.finalState.regs_size.trans s.regs_size.symm⟩

theorem storageWords_eq (input : Input L) (s : State L) :
    storageWords input s = footprint L := by
  simp only [storageWords, footprint, input.size_eq, s.data_size, s.regs_size]

structure Observation {bits : Nat} (L : Layout bits) where
  result : Result L
  initialWords : Nat
  finalWords : Nat

def observe (code : Program L) (input : Input L) (fuel : Nat) (s : State L) :
    Option (Observation L) :=
  match run code input fuel s with
  | none => none
  | some r => some ⟨r, storageWords input s, storageWords input r.finalState⟩

theorem observe_footprint {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {o : Observation L}
    (h : observe code input fuel s = some o) :
    o.initialWords = footprint L ∧ o.finalWords = footprint L := by
  cases hr : run code input fuel s with
  | none => simp [observe, hr] at h
  | some r =>
    have ho : (⟨r, storageWords input s, storageWords input r.finalState⟩ :
        Observation L) = o := by simpa [observe, hr] using h
    subst o
    exact ⟨storageWords_eq input s, storageWords_eq input r.finalState⟩

/-- Extra fuel does not change a successful execution. -/
theorem run_stable_of_le {code : Program L} {input : Input L}
    {fuel more : Nat} {s : State L} {r : Result L}
    (hle : fuel ≤ more) (h : run code input fuel s = some r) :
    run code input more s = some r := by
  induction fuel generalizing more s r with
  | zero => simp [run] at h
  | succ n ih =>
    cases more with
    | zero => simp at hle
    | succ m =>
      cases hs : step code input s with
      | none => simp [run, hs] at h
      | some out =>
        cases out with
        | halted t => simpa [run, hs] using h
        | next t =>
          cases ht : run code input n t with
          | none => simp [run, hs, ht] at h
          | some q =>
            have hm : run code input m t = some q :=
              ih (more := m) (s := t) (r := q) (Nat.le_of_succ_le_succ hle) ht
            simpa [run, hs, ht, hm] using h

/-- The whole result, including the instruction count, is independent of fuel
whenever both runs succeed. -/
theorem run_success_unique {code : Program L} {input : Input L}
    {fuel₁ fuel₂ : Nat} {s : State L} {r₁ r₂ : Result L}
    (h₁ : run code input fuel₁ s = some r₁)
    (h₂ : run code input fuel₂ s = some r₂) : r₁ = r₂ := by
  rcases Nat.le_total fuel₁ fuel₂ with hle | hle
  · exact Option.some.inj ((run_stable_of_le hle h₁).symm.trans h₂)
  · exact Option.some.inj (h₁.symm.trans (run_stable_of_le hle h₂))

/-- A successful trace records the initial state and one successor per
instruction, including the state returned by halt. -/
inductive SuccessfulTrace (code : Program L) (input : Input L) :
    State L → List (State L) → Result L → Prop where
  | halted {s t : State L} (hs : step code input s = some (.halted t)) :
      SuccessfulTrace code input s [s, t] ⟨t, 1⟩
  | next {s t : State L} {states : List (State L)} {r : Result L}
      (hs : step code input s = some (.next t))
      (tail : SuccessfulTrace code input t states r) :
      SuccessfulTrace code input s (s :: states)
        { r with executed := r.executed + 1 }

theorem SuccessfulTrace.unique {code : Program L} {input : Input L}
    {s : State L} {states states' : List (State L)} {r r' : Result L}
    (h : SuccessfulTrace code input s states r)
    (h' : SuccessfulTrace code input s states' r') :
    states = states' ∧ r = r' := by
  induction h generalizing states' r' with
  | halted hs =>
    cases h' with
    | halted hs' =>
      have he := Transition.halted.inj (Option.some.inj (hs.symm.trans hs'))
      cases he
      exact ⟨rfl, rfl⟩
    | next hs' ht' =>
      have he := Option.some.inj (hs.symm.trans hs')
      cases he
  | next hs ht ih =>
    cases h' with
    | halted hs' =>
      have he := Option.some.inj (hs.symm.trans hs')
      cases he
    | next hs' ht' =>
      have he := Transition.next.inj (Option.some.inj (hs.symm.trans hs'))
      cases he
      obtain ⟨hl, hr⟩ := @ih _ _ ht'
      cases hl
      cases hr
      exact ⟨rfl, rfl⟩

theorem run_has_successfulTrace {code : Program L} {input : Input L}
    {fuel : Nat} {s : State L} {r : Result L}
    (h : run code input fuel s = some r) :
    ∃ states : List (State L), SuccessfulTrace code input s states r := by
  induction fuel generalizing s r with
  | zero => simp [run] at h
  | succ n ih =>
    cases hs : step code input s with
    | none => simp [run, hs] at h
    | some out =>
      cases out with
      | halted t =>
        have hr : (⟨t, 1⟩ : Result L) = r := by simpa [run, hs] using h
        subst r
        exact ⟨[s, t], SuccessfulTrace.halted hs⟩
      | next t =>
        cases ht : run code input n t with
        | none => simp [run, hs, ht] at h
        | some q =>
          have hr : { q with executed := q.executed + 1 } = r := by
            simpa [run, hs, ht] using h
          subst r
          obtain ⟨states, htail⟩ := ih (s := t) (r := q) ht
          exact ⟨s :: states, SuccessfulTrace.next hs htail⟩

theorem SuccessfulTrace.storage_eq {code : Program L} {input : Input L}
    {s t : State L} {states : List (State L)} {r : Result L}
    (_ : SuccessfulTrace code input s states r) (_ : t ∈ states) :
    storageWords input t = footprint L :=
  storageWords_eq input t

/-- Peak modeled word slots; excludes code, PC, and metadata charges. -/
def tracePeakWords (input : Input L) : List (State L) → Nat
  | [] => 0
  | s :: states => max (storageWords input s) (tracePeakWords input states)

theorem SuccessfulTrace.peak_eq {code : Program L} {input : Input L}
    {s : State L} {states : List (State L)} {r : Result L}
    (h : SuccessfulTrace code input s states r) :
    tracePeakWords input states = footprint L := by
  induction h with
  | halted hs =>
    simp [tracePeakWords, storageWords_eq, Nat.max_eq_left]
  | next hs ht ih =>
    simp [tracePeakWords, storageWords_eq, ih]

end PaperB.RamProgram

-- Append to PaperB/RamProgram.lean after its namespace closes.
-- This extension uses the existing private register helpers and the actual
-- step/run semantics. It adds no instructions and changes no resource charges.

namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add ltb)

variable {bits : Nat} {L : Layout bits}

/-- Exactly `n` non-halting instructions in one fixed program and input. -/
inductive Steps (code : Program L) (input : Input L) :
    Nat → State L → State L → Prop where
  | zero (s : State L) : Steps code input 0 s s
  | cons {n : Nat} {s u t : State L}
      (head : step code input s = some (.next u))
      (tail : Steps code input n u t) :
      Steps code input (Nat.succ n) s t

theorem Steps.append {code : Program L} {input : Input L}
    {m n : Nat} {s u t : State L} (h : Steps code input m s u) :
    Steps code input n u t → Steps code input (m + n) s t := by
  induction h with
  | zero s =>
    intro hn
    simpa only [Nat.zero_add] using hn
  | cons hs ht ih =>
    intro hn
    simpa only [Nat.succ_add] using Steps.cons hs (ih hn)

/-- Prefixing a successful run preserves its final state and adds exactly
the number of non-halting instructions in the prefix. -/
theorem Steps.thenRun {code : Program L} {input : Input L}
    {n fuel : Nat} {s t : State L} {r : Result L}
    (h : Steps code input n s t) :
    run code input fuel t = some r →
    run code input (n + fuel) s =
      some ⟨r.finalState, n + r.executed⟩ := by
  induction h with
  | zero s =>
    intro hr
    cases r
    simpa only [Nat.zero_add] using hr
  | cons hs ht ih =>
    intro hr
    simp only [Nat.succ_add, run, hs, ih hr]

theorem Steps.halts {code : Program L} {input : Input L}
    {n : Nat} {s t v : State L} (h : Steps code input n s t)
    (hh : step code input t = some (.halted v)) :
    run code input (n + 1) s = some ⟨v, n + 1⟩ :=
  h.thenRun (fuel := 1) (r := ⟨v, 1⟩) (by simp [run, hh])

/-- The witnessed instruction count is also the minimum successful fuel. -/
theorem Steps.halt_run_iff {code : Program L} {input : Input L}
    {n fuel : Nat} {s t v : State L} {r : Result L}
    (h : Steps code input n s t)
    (hh : step code input t = some (.halted v)) :
    run code input fuel s = some r ↔
      n + 1 ≤ fuel ∧ r = ⟨v, n + 1⟩ := by
  have he := h.halts hh
  constructor
  · intro hr
    have eq := run_success_unique hr he
    have hle := run_executed_le hr
    rw [eq] at hle
    exact ⟨hle, eq⟩
  · rintro ⟨hle, rfl⟩
    exact run_stable_of_le hle he

/-- Contracts operate on complete machine states. In particular, a
postcondition can require the PC expected by the next block. -/
def BlockSpec (code : Program L) (input : Input L) (n : Nat)
    (pre post : State L → Prop) : Prop :=
  ∀ s, pre s → ∃ t, Steps code input n s t ∧ post t

theorem BlockSpec.seq {code : Program L} {input : Input L}
    {m n : Nat} {P Q R : State L → Prop}
    (hp : BlockSpec code input m P Q)
    (hq : BlockSpec code input n Q R) :
    BlockSpec code input (m + n) P R := by
  intro s hs
  obtain ⟨u, hsu, hu⟩ := hp s hs
  obtain ⟨t, hut, ht⟩ := hq u hu
  exact ⟨t, hsu.append hut, ht⟩

def iterationCost (cost : Nat → Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => iterationCost cost i + cost i

/-- Each body trace includes all emitted control-flow instructions on its
path, including the taken guard and back-edge when present. -/
theorem loop_steps {code : Program L} {input : Input L}
    (count : Nat) (cost : Nat → Nat) (inv : Nat → State L → Prop)
    (body : ∀ i, i < count →
      BlockSpec code input (cost i) (inv i) (inv (i + 1))) :
    BlockSpec code input (iterationCost cost count) (inv 0) (inv count) := by
  intro s hs
  have reach : ∀ i, i ≤ count →
      ∃ t, Steps code input (iterationCost cost i) s t ∧ inv i t := by
    intro i
    induction i with
    | zero =>
      intro _
      exact ⟨s, Steps.zero s, hs⟩
    | succ i ih =>
      intro hi
      obtain ⟨u, hsu, hu⟩ := ih (by omega)
      obtain ⟨t, hut, ht⟩ := body i (by omega) u hu
      exact ⟨t, hsu.append hut, ht⟩
  exact reach count (Nat.le_refl count)

/-- The exit block includes any final guard and epilogue up to, but not
including, halt. Halt is charged separately, once. -/
theorem loop_run {code : Program L} {input : Input L} {s : State L}
    (count exitCost : Nat) (cost : Nat → Nat)
    (inv : Nat → State L → Prop) (post : State L → Prop)
    (initial : inv 0 s)
    (body : ∀ i, i < count →
      BlockSpec code input (cost i) (inv i) (inv (i + 1)))
    (exit : BlockSpec code input exitCost (inv count)
      (fun u => ∃ v, step code input u = some (.halted v) ∧ post v)) :
    ∃ v, post v ∧
      run code input (iterationCost cost count + exitCost + 1) s =
        some ⟨v, iterationCost cost count + exitCost + 1⟩ := by
  have hloop := loop_steps count cost inv body
  obtain ⟨u, hsu, hu⟩ := hloop s initial
  obtain ⟨t, hut, v, hh, hv⟩ := exit u hu
  exact ⟨v, hv, (hsu.append hut).halts hh⟩

/-- A block's local instruction offsets agree with the linked program. This
does not run the block as a standalone program: every successor is checked
against the full program by `step`. -/
def Placed (code : Program L) (entry : Nat)
    (block : List (Instr bits L.registerCount)) : Prop :=
  ∀ (i : Nat) (op : Instr bits L.registerCount),
    block[i]? = some op → code[entry + i]? = some op

private theorem fetch_shift {α : Type} (pre xs : List α) (i : Nat) :
    (pre ++ xs)[pre.length + i]? = xs[i]? := by
  induction pre with
  | nil => simp
  | cons x pre ih =>
    have he : (x :: pre).length + i = (pre.length + i) + 1 := by
      simp only [List.length_cons]
      omega
    rw [he]
    simpa using ih

private theorem fetch_append_left {α : Type} (xs ys : List α)
    {i : Nat} {x : α} (h : xs[i]? = some x) :
    (xs ++ ys)[i]? = some x := by
  induction xs generalizing i with
  | nil => simp at h
  | cons y xs ih =>
    cases i with
    | zero => simpa using h
    | succ i =>
      have h' : xs[i]? = some x := by simpa using h
      simpa using ih (i := i) h'

theorem placed_link
    (pre block suffix : List (Instr bits L.registerCount)) :
    Placed (L := L) (pre ++ (block ++ suffix)).toArray pre.length block := by
  intro i op hi
  have h := (fetch_shift pre (block ++ suffix) i).trans
    (fetch_append_left block suffix hi)
  simpa using h

private theorem fetch_in_bounds {code : Program L} {pc : Nat}
    {op : Instr bits L.registerCount} (h : code[pc]? = some op) :
    pc < code.size := by
  by_cases hp : pc < code.size
  · exact hp
  · simp [getElem?_def, hp] at h

/-- Public register observation, with no change to the state representation. -/
abbrev reg (s : State L) (r : Fin L.registerCount) : Word bits :=
  readReg s r

private theorem reg_write_same (s : State L) (r : Fin L.registerCount)
    (w : Word bits) : reg (writeReg s r w) r = w := by
  simp [reg, readReg, writeReg, Array.getElem_set]

private theorem reg_write_other (s : State L)
    (dst r : Fin L.registerCount) (w : Word bits) (h : r ≠ dst) :
    reg (writeReg s dst w) r = reg s r := by
  have hv : r.val ≠ dst.val := fun he => h (Fin.ext he)
  simp [reg, readReg, writeReg, Array.getElem_set, hv, Ne.symm hv]

theorem step_halt_at {code : Program L} {input : Input L} {s : State L}
    (hf : code[s.pc]? = some .halt) :
    step code input s = some (.halted s) := by
  simp [step, hf]

theorem step_goto_at {code : Program L} {input : Input L} {s : State L}
    {target : Nat} (hf : code[s.pc]? = some (.goto target))
    (ht : target < code.size) :
    step code input s = some (.next { s with pc := target }) := by
  simp [step, hf, advance, ht]

theorem step_branchLt_at {code : Program L} {input : Input L}
    {s : State L} {x y : Fin L.registerCount} {yesPC noPC : Nat}
    (hf : code[s.pc]? = some (.branchLt x y yesPC noPC))
    (ht : (if ltb (reg s x) (reg s y) then yesPC else noPC) < code.size) :
    step code input s =
      some (.next { s with
        pc := if ltb (reg s x) (reg s y) then yesPC else noPC }) := by
  change (if ltb (readReg s x) (readReg s y) then yesPC else noPC) <
    code.size at ht
  simp [step, hf, advance, reg, ht]

/-- Shift the original source value, allowing `dst` and `src` to alias. -/
theorem step_shr1_at {code : Program L} {input : Input L} {s : State L}
    {dst src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.shr1 dst src))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧
      t.pc = s.pc + 1 ∧ (reg t dst).val = (reg s src).val / 2 ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  let w := shr1Word (readReg s src)
  let t : State L := { (writeReg s dst w) with pc := s.pc + 1 }
  have hs : step code input s = some (.next t) := by
    simp [step, hf, advance, hnext, t, w]
  refine ⟨t, hs, rfl, ?_, ?_, rfl⟩
  · change (reg t dst).val = w.val
    have hreg : reg t dst = w := reg_write_same s dst w
    exact congrArg Fin.val hreg
  · intro r hr
    exact reg_write_other s dst r w hr

/-- The shift contributes exactly one non-halting instruction to a trace. -/
theorem shr1_steps {code : Program L} {input : Input L} {s : State L}
    {dst src : Fin L.registerCount}
    (hf : code[s.pc]? = some (.shr1 dst src))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, Steps code input 1 s t ∧
      t.pc = s.pc + 1 ∧ (reg t dst).val = (reg s src).val / 2 ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  obtain ⟨t, ht, hpost⟩ :=
    step_shr1_at (code := code) (input := input) (s := s) hf hnext
  exact ⟨t, Steps.cons ht (Steps.zero t), hpost⟩

/-- Read input at `base + index`. The destination also holds the temporary
address, so no extra register is needed and either source may alias `dst`. -/
def indexedInputRead {w r : Nat} (dst base index : Fin r) :
    List (Instr w r) :=
  [.add dst base index, .loadInput dst dst]

/-- Write work data at `base + index`. Only `src` must survive the address
calculation; `tmp` may alias either address operand. -/
def indexedDataWrite {w r : Nat} (tmp base index src : Fin r) :
    List (Instr w r) :=
  [.add tmp base index, .storeData tmp src]

/-- The unsigned bound is on the mathematical sum of the original register
values. Since `inputCap ≤ 2^bits`, it rules out both wrap and invalid access.
The continuation at `entry + 2` must be fetchable. -/
theorem indexedInputRead_steps {code : Program L} {input : Input L}
    {s : State L} {entry : Nat} {dst base index : Fin L.registerCount}
    (placed : Placed code entry (indexedInputRead dst base index))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hbound : (reg s base).val + (reg s index).val < L.inputCap) :
    ∃ t, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      some (reg t dst) =
        input.words[(reg s base).val + (reg s index).val]? ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  have hf₀ : code[entry]? = some (.add dst base index) :=
    placed 0 (.add dst base index) (by simp [indexedInputRead])
  have hf₁ : code[entry + 1]? = some (.loadInput dst dst) :=
    placed 1 (.loadInput dst dst) (by simp [indexedInputRead])
  have hmid := fetch_in_bounds hf₁
  let a := (reg s base).val + (reg s index).val
  let w := add (reg s base) (reg s index)
  have hw : w.val = a :=
    PaperB.WordOps.add_no_wrap _ _ (Nat.lt_of_lt_of_le hbound L.inputFits)
  have ha : a < input.words.size := by
    simpa only [a, input.size_eq] using hbound
  let v := input.words[a]'ha
  have hv : input.words[a]? = some v := by
    simp [getElem?_def, ha, v]
  let u : State L := { (writeReg s dst w) with pc := entry + 1 }
  let t : State L := { (writeReg u dst v) with pc := entry + 2 }
  have huPC : u.pc = entry + 1 := rfl
  have huReg : readReg u dst = w := reg_write_same s dst w
  have huAddr : (readReg u dst).val = a := (congrArg Fin.val huReg).trans hw
  have hs₀ : step code input s = some (.next u) := by
    simp [step, hpc, hf₀, advance, hmid, u, w, reg]
  have hs₁ : step code input u = some (.next t) := by
    simp [step, huPC, hf₁, huAddr, hv, advance, hexit, t]
  refine ⟨t, Steps.cons hs₀ (Steps.cons hs₁ (Steps.zero t)), rfl,
    ?_, ?_, rfl⟩
  · have htReg : reg t dst = v := reg_write_same u dst v
    exact (congrArg some htReg).trans hv.symm
  · intro r hr
    exact (reg_write_other u dst r v hr).trans
      (reg_write_other s dst r w hr)

/-- The array update is at the exact unsigned sum, not at a wrapped
address. The postcondition gives the full updated array and all register
effects, so it can be used directly in a kernel invariant. -/
theorem indexedDataWrite_steps {code : Program L} {input : Input L}
    {s : State L} {entry : Nat} {tmp base index src : Fin L.registerCount}
    (placed : Placed code entry (indexedDataWrite tmp base index src))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hsrc : src ≠ tmp)
    (hbound : (reg s base).val + (reg s index).val < L.workCap) :
    ∃ t, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      t.data = s.data.set ((reg s base).val + (reg s index).val)
        (reg s src) (by simpa only [s.data_size] using hbound) ∧
      reg t tmp = add (reg s base) (reg s index) ∧
      (∀ r : Fin L.registerCount, r ≠ tmp → reg t r = reg s r) := by
  have hf₀ : code[entry]? = some (.add tmp base index) :=
    placed 0 (.add tmp base index) (by simp [indexedDataWrite])
  have hf₁ : code[entry + 1]? = some (.storeData tmp src) :=
    placed 1 (.storeData tmp src) (by simp [indexedDataWrite])
  have hmid := fetch_in_bounds hf₁
  let a := (reg s base).val + (reg s index).val
  let w := add (reg s base) (reg s index)
  have hw : w.val = a :=
    PaperB.WordOps.add_no_wrap _ _ (Nat.lt_of_lt_of_le hbound L.workFits)
  have ha : a < s.data.size := by
    simpa only [a, s.data_size] using hbound
  let u : State L := { (writeReg s tmp w) with pc := entry + 1 }
  let t : State L :=
    { u with
      data := s.data.set a (reg s src) ha
      pc := entry + 2
      data_size := by simp only [Array.size_set, s.data_size] }
  have huPC : u.pc = entry + 1 := rfl
  have huReg : readReg u tmp = w := reg_write_same s tmp w
  have huAddr : (readReg u tmp).val = a := (congrArg Fin.val huReg).trans hw
  have huSrc : readReg u src = readReg s src :=
    reg_write_other s tmp src w hsrc
  have huBound : a < u.data.size := ha
  have hs₀ : step code input s = some (.next u) := by
    simp [step, hpc, hf₀, advance, hmid, u, w, reg]
  have hs₁ : step code input u = some (.next t) := by
    simp [step, huPC, hf₁, huAddr, huSrc, huBound, advance, hexit, t, reg]
    exact ⟨hexit, rfl⟩
  refine ⟨t, Steps.cons hs₀ (Steps.cons hs₁ (Steps.zero t)), rfl, rfl,
    reg_write_same s tmp w, ?_⟩
  intro r hr
  exact reg_write_other s tmp r w hr

end PaperB.RamProgram

namespace PaperB.RamProgram

open PaperB.Machine (Word)
open PaperB.WordOps (add sub band ltb)

variable {bits : Nat} {L : Layout bits}

/-- Three instructions; the instruction at `entry + 3` is not part of the block. -/
def ramMidpoint (dst lo hi : Fin L.registerCount) :
    List (Instr bits L.registerCount) :=
  [.sub dst hi lo, .shr1 dst dst, .add dst lo dst]

private theorem ramMid_word_lt (w : Word bits) : w.val < 2 ^ bits :=
  w.isLt

private theorem ramMid_sub_exact (x y : Word bits) (h : y.val ≤ x.val) :
    (sub x y).val = x.val - y.val := by
  have hb : x.val - y.val < 2 ^ bits :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ramMid_word_lt x)
  change (2 ^ bits + x.val - y.val) % (2 ^ bits) = x.val - y.val
  rw [Nat.add_sub_assoc h, Nat.add_mod]
  simp only [Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt hb]

private theorem ramMid_sub_at {code : Program L} {input : Input L}
    {s : State L} {dst lo hi : Fin L.registerCount}
    (hf : code[s.pc]? = some (.sub dst hi lo))
    (hn : s.pc + 1 < code.size)
    (hle : (reg s lo).val ≤ (reg s hi).val) :
    ∃ t, step code input s = some (.next t) ∧
      t.pc = s.pc + 1 ∧
      (reg t dst).val = (reg s hi).val - (reg s lo).val ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  let w := sub (reg s hi) (reg s lo)
  let t : State L := { (writeReg s dst w) with pc := s.pc + 1 }
  have hs : step code input s = some (.next t) := by
    calc
      step code input s = advance code (writeReg s dst w) (s.pc + 1) := by
        simp [step, hf, w, reg]
      _ = some (.next t) := by simp [advance, hn, t]
  refine ⟨t, hs, rfl, ?_, ?_, rfl⟩
  · have hd : reg t dst = w := reg_write_same s dst w
    exact (congrArg Fin.val hd).trans (ramMid_sub_exact (reg s hi) (reg s lo) hle)
  · intro r h
    exact reg_write_other s dst r w h

theorem ramMidpoint_steps {code : Program L} {input : Input L}
    {s : State L} {entry : Nat} {dst lo hi : Fin L.registerCount}
    (placed : Placed code entry (ramMidpoint dst lo hi))
    (hpc : s.pc = entry) (hexit : entry + 3 < code.size)
    (hAlias : dst ≠ lo) (hle : (reg s lo).val ≤ (reg s hi).val) :
    ∃ t, Steps code input 3 s t ∧ t.pc = entry + 3 ∧
      (reg t dst).val = (reg s lo).val + ((reg s hi).val - (reg s lo).val) / 2 ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  have hf₀ : code[s.pc]? = some (.sub dst hi lo) := by
    rw [hpc]
    exact placed 0 _ (by simp [ramMidpoint])
  obtain ⟨a, ha, hapc, haval, hakeep, hadata⟩ :=
    ramMid_sub_at (input := input) hf₀ (by omega) hle
  have haentry : a.pc = entry + 1 := by omega
  have hf₁ : code[a.pc]? = some (.shr1 dst dst) := by
    rw [haentry]
    exact placed 1 _ (by simp [ramMidpoint])
  obtain ⟨b, hb, hbpc, hbval, hbkeep, hbdata⟩ :=
    step_shr1_at (input := input) hf₁ (by omega)
  have hbentry : b.pc = entry + 2 := by omega
  have hbLo : reg b lo = reg s lo :=
    (hbkeep lo (Ne.symm hAlias)).trans (hakeep lo (Ne.symm hAlias))
  have hbHalf :
      (reg b dst).val = ((reg s hi).val - (reg s lo).val) / 2 := by
    rw [hbval, haval]
  have hsum : (reg b lo).val + (reg b dst).val < 2 ^ bits := by
    rw [hbLo, hbHalf]
    have hh := ramMid_word_lt (reg s hi)
    omega
  have hf₂ : code[b.pc]? = some (.add dst lo dst) := by
    rw [hbentry]
    exact placed 2 _ (by simp [ramMidpoint])
  have hn : b.pc + 1 < code.size := by omega
  let w := add (reg b lo) (reg b dst)
  let t : State L := { (writeReg b dst w) with pc := b.pc + 1 }
  have ht : step code input b = some (.next t) := by
    calc
      step code input b = advance code (writeReg b dst w) (b.pc + 1) := by
        simp [step, hf₂, w, reg]
      _ = some (.next t) := by simp [advance, hn, t]
  refine ⟨t, Steps.cons ha (Steps.cons hb (Steps.cons ht (Steps.zero t))),
    ?_, ?_, ?_, ?_⟩
  · change b.pc + 1 = entry + 3
    omega
  · have hd : reg t dst = w := reg_write_same b dst w
    calc
      (reg t dst).val = w.val := congrArg Fin.val hd
      _ = (reg b lo).val + (reg b dst).val :=
        PaperB.WordOps.add_no_wrap (reg b lo) (reg b dst) hsum
      _ = _ := by rw [hbLo, hbHalf]
  · intro r h
    exact (reg_write_other b dst r w h).trans ((hbkeep r h).trans (hakeep r h))
  · exact (show t.data = b.data from rfl).trans (hbdata.trans hadata)

end PaperB.RamProgram

namespace PaperB.RamProgram
open PaperB.Machine (Word)
open PaperB.WordOps (add sub band ltb)
section FixedCodePlacement

variable {bits : Nat} {L : Layout bits}

/-- Relocate absolute targets at assembly time. All other instructions
are copied verbatim. -/
def relocateInstr {bits registerCount : Nat} (base : Nat) :
    Instr bits registerCount → Instr bits registerCount
  | .goto target => .goto (base + target)
  | .branchLt lhs rhs ltPC gePC =>
      .branchLt lhs rhs (base + ltPC) (base + gePC)
  | op => op

/-- Translate the PC without changing the registers or work data. -/
def relocateStatePC (base : Nat) (s : State L) : State L :=
  { s with pc := base + s.pc }

/-- Every instruction of `localCode` is present at its relocated address
in the already assembled `linkedCode`. -/
def RelocatedSlice (localCode linkedCode : Program L) (base : Nat) : Prop :=
  ∀ (i : Nat) (op : Instr bits L.registerCount),
    localCode[i]? = some op →
      linkedCode[base + i]? = some (relocateInstr base op)

private theorem advance_relocated_next
    {localCode linkedCode : Program L} {base p : Nat} {u t : State L}
    (placed : RelocatedSlice (L := L) localCode linkedCode base)
    (h : advance localCode u p = some (.next t)) :
    advance linkedCode (relocateStatePC base u) (base + p) =
      some (.next (relocateStatePC base t)) := by
  by_cases hp : p < localCode.size
  · have hf : localCode[p]? = some (localCode[p]'hp) :=
      getElem?_pos localCode p hp
    have hg := placed p (localCode[p]'hp) hf
    have hq : base + p < linkedCode.size := by
      by_cases hq : base + p < linkedCode.size
      · exact hq
      · rw [getElem?_neg linkedCode (base + p) hq] at hg
        cases hg
    rw [advance, if_pos hp] at h
    have ht : { u with pc := p } = t :=
      Transition.next.inj (Option.some.inj h)
    subst t
    rw [advance, if_pos hq] <;> rfl
  · rw [advance, if_neg hp] at h
    cases h

/-- A successful non-halting local instruction takes exactly one step
in the linked code, with the same register and data effects. -/
theorem step_relocated_next
    {localCode linkedCode : Program L} {input : Input L} {base : Nat}
    {s t : State L}
    (placed : RelocatedSlice (L := L) localCode linkedCode base)
    (h : step localCode input s = some (.next t)) :
    step linkedCode input (relocateStatePC base s) =
      some (.next (relocateStatePC base t)) := by
  have fallthrough (u : State L)
      (hu : advance localCode u (s.pc + 1) = some (.next t)) :
      advance linkedCode (relocateStatePC base u)
          ((relocateStatePC base s).pc + 1) =
        some (.next (relocateStatePC base t)) := by
    have hpc : (relocateStatePC base s).pc + 1 = base + (s.pc + 1) :=
      Nat.add_assoc base s.pc 1
    rw [hpc]
    exact advance_relocated_next (u := u) (p := s.pc + 1) placed hu
  have load (dst : Fin L.registerCount) (value : Option (Word bits))
      (hv : value.bind (fun w =>
        advance localCode (writeReg s dst w) (s.pc + 1)) = some (.next t)) :
      value.bind (fun w =>
        advance linkedCode (relocateStatePC base (writeReg s dst w))
          ((relocateStatePC base s).pc + 1)) =
        some (.next (relocateStatePC base t)) := by
    cases value with
    | none =>
      change (none : Option (Transition L)) = some (.next t) at hv
      cases hv
    | some w =>
      exact fallthrough (writeReg s dst w) hv
  cases hf : localCode[s.pc]? with
  | none =>
    unfold step at h
    rw [hf] at h
    change (none : Option (Transition L)) = some (.next t) at h
    cases h
  | some op =>
    have hg : linkedCode[(relocateStatePC base s).pc]? =
        some (relocateInstr base op) :=
      placed s.pc op hf
    unfold step at h ⊢
    rw [hf] at h
    rw [hg]
    cases op with
    | imm dst w =>
      exact fallthrough (writeReg s dst w) h
    | mov dst src =>
      exact fallthrough (writeReg s dst (readReg s src)) h
    | add dst x y =>
      exact fallthrough (writeReg s dst (add (readReg s x) (readReg s y))) h
    | sub dst x y =>
      exact fallthrough (writeReg s dst (sub (readReg s x) (readReg s y))) h
    | band dst x y =>
      exact fallthrough (writeReg s dst (band (readReg s x) (readReg s y))) h
    | loadInput dst addr =>
      exact load dst (input.words[(readReg s addr).val]?) h
    | loadData dst addr =>
      exact load dst (s.data[(readReg s addr).val]?) h
    | storeData addr src =>
      let i := (readReg s addr).val
      let update (hi : i < s.data.size) : State L :=
        { s with
          data := s.data.set i (readReg s src) hi
          data_size := by simp only [Array.size_set, s.data_size] }
      change
        (if hi : i < s.data.size then
          advance localCode (update hi) (s.pc + 1)
        else none) = some (.next t) at h
      change
        (if hi : i < s.data.size then
          advance linkedCode (relocateStatePC base (update hi))
            ((relocateStatePC base s).pc + 1)
        else none) = some (.next (relocateStatePC base t))
      by_cases hi : i < s.data.size
      · rw [dif_pos hi] at h ⊢
        exact fallthrough (update hi) h
      · rw [dif_neg hi] at h
        cases h
    | branchLt x y ltPC gePC =>
      change advance localCode s
        (if ltb (readReg s x) (readReg s y) then ltPC else gePC) =
          some (.next t) at h
      change advance linkedCode (relocateStatePC base s)
        (if ltb (readReg s x) (readReg s y) then base + ltPC else base + gePC) =
          some (.next (relocateStatePC base t))
      by_cases hb : ltb (readReg s x) (readReg s y)
      · rw [if_pos hb] at h ⊢
        exact advance_relocated_next (u := s) (p := ltPC) placed h
      · rw [if_neg hb] at h ⊢
        exact advance_relocated_next (u := s) (p := gePC) placed h
    | goto target =>
      exact advance_relocated_next (u := s) (p := target) placed h
    | halt =>
      change some (Transition.halted s) = some (Transition.next t) at h
      cases h
    | shr1 dst src =>
      exact fallthrough (writeReg s dst (shr1Word (readReg s src))) h

/-- A placed slice reproduces a successful local non-halting execution
with exactly the same instruction count. Execution uses only the fixed
linked program; relocation is not a machine step. -/
theorem Steps.relocate
    {localCode linkedCode : Program L} {input : Input L} {base n : Nat}
    {s t : State L}
    (h : Steps localCode input n s t)
    (placed : RelocatedSlice (L := L) localCode linkedCode base) :
    Steps linkedCode input n (relocateStatePC base s) (relocateStatePC base t) := by
  induction h with
  | zero u =>
    exact Steps.zero (relocateStatePC base u)
  | cons head tail ih =>
    exact Steps.cons (step_relocated_next placed head) ih

end FixedCodePlacement

end PaperB.RamProgram

namespace PaperB.RamProgram
open PaperB.Machine (Word)
open PaperB.WordOps (add sub band)

variable {bits : Nat} {L A : Layout bits}

abbrev ArenaMap (L A : Layout bits) := Fin L.registerCount → Fin A.registerCount

def embedInstr (ρ : ArenaMap L A) :
    Instr bits L.registerCount → Instr bits A.registerCount
  | .imm d w => .imm (ρ d) w
  | .mov d r => .mov (ρ d) (ρ r)
  | .add d x y => .add (ρ d) (ρ x) (ρ y)
  | .sub d x y => .sub (ρ d) (ρ x) (ρ y)
  | .band d x y => .band (ρ d) (ρ x) (ρ y)
  | .loadInput d a => .loadInput (ρ d) (ρ a)
  | .loadData d a => .loadData (ρ d) (ρ a)
  | .storeData a r => .storeData (ρ a) (ρ r)
  | .branchLt x y yes no => .branchLt (ρ x) (ρ y) yes no
  | .goto p => .goto p
  | .halt => .halt
  | .shr1 d r => .shr1 (ρ d) (ρ r)

structure ArenaAgreement (ρ : ArenaMap L A) (base : State A)
    (s : State L) (t : State A) : Prop where
  pc_eq : s.pc = t.pc
  data_eq : s.data = t.data
  reg_eq : ∀ r, reg s r = reg t (ρ r)
  frame : ∀ r, (∀ q, ρ q ≠ r) → reg t r = reg base r

def ArenaOutcome (ρ : ArenaMap L A) (base : State A) :
    Option (Transition L) → Option (Transition A) → Prop
  | none, none => True
  | some (.next s), some (.next t) => ArenaAgreement ρ base s t
  | some (.halted s), some (.halted t) => ArenaAgreement ρ base s t
  | _, _ => False

private theorem arenaAdvance {ρ : ArenaMap L A} {base t : State A} {s : State L}
    {code : Program L} {wide : Program A} (hlen : code.size = wide.size)
    (h : ArenaAgreement ρ base s t) {p q : Nat} (e : p = q) :
    ArenaOutcome ρ base (advance code s p) (advance wide t q) := by
  subst q
  by_cases hp : p < code.size
  · have hq : p < wide.size := by simpa only [← hlen] using hp
    simpa only [advance, if_pos hp, if_pos hq, ArenaOutcome] using
      (show ArenaAgreement ρ base { s with pc := p } { t with pc := p } from
        ⟨rfl, h.data_eq, h.reg_eq, h.frame⟩)
  · have hq : ¬ p < wide.size := by simpa only [← hlen] using hp
    simp [advance, hp, hq, ArenaOutcome]

private theorem arenaWrite {ρ : ArenaMap L A} {base t : State A} {s : State L}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b) (h : ArenaAgreement ρ base s t)
    (d : Fin L.registerCount) (w : Word bits) :
    ArenaAgreement ρ base (writeReg s d w) (writeReg t (ρ d) w) := by
  refine ⟨h.pc_eq, h.data_eq, ?_, ?_⟩
  · intro r
    by_cases e : r = d
    · subst r
      simp only [reg_write_same]
    · rw [reg_write_other s d r w e,
          reg_write_other t (ρ d) (ρ r) w (fun k => e (hinj k))]
      exact h.reg_eq r
  · intro r hr
    exact (reg_write_other t (ρ d) r w (Ne.symm (hr d))).trans (h.frame r hr)

/-- Refine one fetched instruction, preserving rejection, halt, and the arena frame. -/
theorem step_embedInstrWithStore {ρ : ArenaMap L A} {base t : State A} {s : State L}
    {code : Program L} {wide : Program A} {i : Input L} {j : Input A}
    {op : Instr bits L.registerCount}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hlen : code.size = wide.size) (hi : i.words = j.words)
    (h : ArenaAgreement ρ base s t)
    (hf : code[s.pc]? = some op) (hg : wide[t.pc]? = some (embedInstr ρ op))
    :
    ArenaOutcome ρ base (step code i s) (step wide j t) := by
  have hn : s.pc + 1 = t.pc + 1 := congrArg (fun p => p + 1) h.pc_eq
  have put (d : Fin L.registerCount) (w v : Word bits) (e : w = v) :
      ArenaOutcome ρ base (advance code (writeReg s d w) (s.pc + 1))
        (advance wide (writeReg t (ρ d) v) (t.pc + 1)) := by
    subst v
    exact arenaAdvance hlen (arenaWrite hinj h d w) hn
  have load (d : Fin L.registerCount) (v u : Option (Word bits)) (e : v = u) :
      ArenaOutcome ρ base
        (v.bind fun w => advance code (writeReg s d w) (s.pc + 1))
        (u.bind fun w => advance wide (writeReg t (ρ d) w) (t.pc + 1)) := by
    subst u
    cases v with
    | none => exact True.intro
    | some w => exact put d w w rfl
  cases op
  all_goals simp only [step, hf, hg, embedInstr]
  case imm d w => exact put d w w rfl
  case mov d r => exact put d (reg s r) (reg t (ρ r)) (h.reg_eq r)
  case add d x y =>
    refine put d (add (reg s x) (reg s y))
      (add (reg t (ρ x)) (reg t (ρ y))) ?_
    rw [h.reg_eq x, h.reg_eq y]
  case sub d x y =>
    refine put d (sub (reg s x) (reg s y))
      (sub (reg t (ρ x)) (reg t (ρ y))) ?_
    rw [h.reg_eq x, h.reg_eq y]
  case band d x y =>
    refine put d (band (reg s x) (reg s y))
      (band (reg t (ρ x)) (reg t (ρ y))) ?_
    rw [h.reg_eq x, h.reg_eq y]
  case shr1 d r =>
    refine put d (shr1Word (reg s r)) (shr1Word (reg t (ρ r))) ?_
    rw [h.reg_eq r]
  case loadInput d a =>
    refine load d (i.words[(reg s a).val]?) (j.words[(reg t (ρ a)).val]?) ?_
    calc
      i.words[(reg s a).val]? = j.words[(reg s a).val]? :=
        congrArg (fun ws : Array (Word bits) => ws[(reg s a).val]?) hi
      _ = j.words[(reg t (ρ a)).val]? := by rw [h.reg_eq a]
  case loadData d a =>
    refine load d (s.data[(reg s a).val]?) (t.data[(reg t (ρ a)).val]?) ?_
    calc
      s.data[(reg s a).val]? = t.data[(reg s a).val]? :=
        congrArg (fun ws : Array (Word bits) => ws[(reg s a).val]?) h.data_eq
      _ = t.data[(reg t (ρ a)).val]? := by rw [h.reg_eq a]
  case storeData a r =>
    simp only [Option.bind_eq_bind, Option.bind]
    have addr : (readReg s a).val = (readReg t (ρ a)).val := congrArg Fin.val (h.reg_eq a)
    have same : (readReg s a).val < s.data.size ↔
        (readReg t (ρ a)).val < t.data.size := by rw [addr, h.data_eq]
    by_cases fits : (readReg s a).val < s.data.size
    · rw [dite_eq_left fits, dite_eq_left (same.mp fits)]
      apply arenaAdvance hlen _ hn
      exact ⟨h.pc_eq, by simp only [h.data_eq, h.reg_eq r, addr], h.reg_eq, h.frame⟩
    · rw [dite_eq_right fits, dite_eq_right (fun other => fits (same.mpr other))]
      exact True.intro
  case branchLt x y yes no =>
    change ArenaOutcome ρ base
      (advance code s (if PaperB.WordOps.ltb (reg s x) (reg s y) then yes else no))
      (advance wide t
        (if PaperB.WordOps.ltb (reg t (ρ x)) (reg t (ρ y)) then yes else no))
    rw [h.reg_eq x, h.reg_eq y]
    exact arenaAdvance hlen h rfl
  case goto p =>
    exact arenaAdvance (code := code) (wide := wide) hlen h (rfl : p = p)
  case halt => exact h

/-- Refine one fetched non-store instruction, preserving rejection, halt, and the arena frame. -/
theorem step_embedInstr {ρ : ArenaMap L A} {base t : State A} {s : State L}
    {code : Program L} {wide : Program A} {i : Input L} {j : Input A}
    {op : Instr bits L.registerCount}
    (hinj : ∀ {a b}, ρ a = ρ b → a = b)
    (hlen : code.size = wide.size) (hi : i.words = j.words)
    (h : ArenaAgreement ρ base s t)
    (hf : code[s.pc]? = some op) (hg : wide[t.pc]? = some (embedInstr ρ op))
    (_hNoStore : ∀ a r : Fin L.registerCount, op ≠ Instr.storeData a r) :
    ArenaOutcome ρ base (step code i s) (step wide j t) :=
  step_embedInstrWithStore hinj hlen hi h hf hg

end PaperB.RamProgram

namespace PaperB.RamProgram

open PaperB.WordOps (add)
variable {bits : Nat} {L : Layout bits}

def indexedDataRead {w r : Nat} (dst base index : Fin r) : List (Instr w r) :=
  [.add dst base index, .loadData dst dst]

/-- Advance one instruction and expose all effects of a register addition. -/
theorem step_add_at {code : Program L} {input : Input L} {s : State L}
    {dst lhs rhs : Fin L.registerCount}
    (hf : code[s.pc]? = some (.add dst lhs rhs))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t dst = add (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  let w := add (reg s lhs) (reg s rhs)
  let t := { (writeReg s dst w) with pc := s.pc + 1 }
  refine ⟨t, ?_, rfl, reg_write_same _ _ _, ?_, rfl⟩
  · simp [step, hf, advance, hnext, t, w, reg]
  · intro r h
    exact reg_write_other _ _ _ _ h

/-- Fetch a word from mutable data without changing the data arena. -/
theorem indexedDataRead_steps {code : Program L} {input : Input L}
    {s : State L} {entry : Nat} {dst base index : Fin L.registerCount}
    (placed : Placed code entry (indexedDataRead dst base index))
    (hpc : s.pc = entry) (hexit : entry + 2 < code.size)
    (hbound : (reg s base).val + (reg s index).val < L.workCap) :
    ∃ t, Steps code input 2 s t ∧ t.pc = entry + 2 ∧
      some (reg t dst) =
        s.data[(reg s base).val + (reg s index).val]? ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  have hf₀ : code[entry]? = some (.add dst base index) :=
    placed 0 (.add dst base index) (by simp [indexedDataRead])
  have hf₁ : code[entry + 1]? = some (.loadData dst dst) :=
    placed 1 (.loadData dst dst) (by simp [indexedDataRead])
  have hmid := fetch_in_bounds hf₁
  let a := (reg s base).val + (reg s index).val
  let w := add (reg s base) (reg s index)
  have hw : w.val = a :=
    PaperB.WordOps.add_no_wrap _ _ (Nat.lt_of_lt_of_le hbound L.workFits)
  have ha : a < s.data.size := by
    simpa only [a, s.data_size] using hbound
  let v := s.data[a]'ha
  have hv : s.data[a]? = some v := by
    simp [ha, v]
  let u : State L := { (writeReg s dst w) with pc := entry + 1 }
  let t : State L := { (writeReg u dst v) with pc := entry + 2 }
  have huPC : u.pc = entry + 1 := rfl
  have huReg : readReg u dst = w := reg_write_same s dst w
  have huAddr : (readReg u dst).val = a := (congrArg Fin.val huReg).trans hw
  have hs₀ : step code input s = some (.next u) := by
    simp [step, hpc, hf₀, advance, hmid, u, w, reg]
  have hs₁ : step code input u = some (.next t) := by
    simp [step, huPC, hf₁, huAddr, show u.data = s.data from rfl, hv, advance, hexit, t]
  refine ⟨t, Steps.cons hs₀ (Steps.cons hs₁ (Steps.zero t)), rfl,
    ?_, ?_, rfl⟩
  · have htReg : reg t dst = v := reg_write_same u dst v
    exact (congrArg some htReg).trans hv.symm
  · intro r hr
    exact (reg_write_other u dst r v hr).trans
      (reg_write_other s dst r w hr)

end PaperB.RamProgram

namespace PaperB.RamProgram

variable {bits : Nat} {L : Layout bits}

/-- Advance one instruction and expose all effects of subtraction. -/
theorem step_sub_at {code : Program L} {input : Input L} {s : State L}
    {dst lhs rhs : Fin L.registerCount}
    (hf : code[s.pc]? = some (.sub dst lhs rhs))
    (hnext : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧
      reg t dst = PaperB.WordOps.sub (reg s lhs) (reg s rhs) ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧
      t.data = s.data := by
  let w := PaperB.WordOps.sub (reg s lhs) (reg s rhs)
  let t := { (writeReg s dst w) with pc := s.pc + 1 }
  refine ⟨t, ?_, rfl, reg_write_same _ _ _, ?_, rfl⟩
  · simp [step, hf, advance, hnext, t, w, reg]
  · intro r h
    exact reg_write_other _ _ _ _ h

end PaperB.RamProgram

namespace PaperB.RamProgram

variable {bits : Nat} {L : Layout bits}

/-- Read an addressed work word into a register, preserving the arena. -/
theorem step_loadData_at {code : Program L} {input : Input L} {s : State L}
    {dst addr : Fin L.registerCount} {w : PaperB.Machine.Word bits}
    (hf : code[s.pc]? = some (.loadData dst addr))
    (hread : s.data[(reg s addr).val]? = some w)
    (hnext : s.pc + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧ reg t dst = w ∧
      (∀ r : Fin L.registerCount, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  let t := { (writeReg s dst w) with pc := s.pc + 1 }
  refine ⟨t, ?_, rfl, reg_write_same _ _ _, ?_, rfl⟩
  · change s.data[(readReg s addr).val]? = some w at hread
    simp [step, hf, hread, advance, hnext, t]
  · intro r h
    exact reg_write_other _ _ _ _ h

end PaperB.RamProgram
