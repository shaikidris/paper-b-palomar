module

public import PaperB.RamProgram
public import PaperB.ForestCompactPeak

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestStack

open PaperB.Machine (Word)
open PaperB.RamProgram

variable {bits : Nat} {L : Layout bits}
variable {code : Program L} {input : Input L}

/-- Top-first stack view. The last occupied address contains the head. -/
def StackAt (data : Array (Word bits)) (base : Nat) : List (Word bits) → Prop
  | [] => True
  | w :: ws => data[base + ws.length]? = some w ∧ StackAt data base ws

private theorem preserve {data data' : Array (Word bits)} {base : Nat}
    {ws : List (Word bits)} (old : StackAt data base ws)
    (frame : ∀ i < ws.length, data'[base + i]? = data[base + i]?) :
    StackAt data' base ws := by
  induction ws with
  | nil => exact True.intro
  | cons w ws ih =>
    obtain ⟨head, tail⟩ := old
    refine ⟨(frame _ (by simp)).trans head, ih tail ?_⟩
    intro i hi
    exact frame i (by simp; omega)

private def writeIncrement {w r : Nat}
    (base index value next one tmp : Fin r) : List (Instr w r) :=
  indexedDataWrite tmp base index value ++ [.add next next one]

private theorem writeIncrement_steps
    {entry : Nat} {base index value next one tmp : Fin L.registerCount}
    {s : State L}
    (placed : Placed code entry (writeIncrement base index value next one tmp))
    (pc : s.pc = entry) (cont : entry + 3 < code.size)
    (unitVal : (reg s one).val = 1)
    (fits : (reg s base).val + (reg s index).val < L.workCap)
    (nextFits : (reg s next).val + 1 < 2 ^ bits)
    (valueStable : value ≠ tmp) (nextStable : next ≠ tmp) (unitStable : one ≠ tmp) :
    ∃ t, Steps code input 3 s t ∧ t.pc = entry + 3 ∧
      (reg t next).val = (reg s next).val + 1 ∧
      t.data = s.data.set ((reg s base).val + (reg s index).val)
        (reg s value) (by rw [s.data_size]; exact fits) ∧
      (∀ r, r ≠ next → r ≠ tmp → reg t r = reg s r) := by
  have put : Placed code entry (indexedDataWrite tmp base index value) := by
    intro k op hk
    apply placed k op
    cases k with
    | zero => exact hk
    | succ k =>
      cases k with
      | zero => exact hk
      | succ k => simp [indexedDataWrite] at hk
  obtain ⟨u, su, upc, uMem, _, uReg⟩ :=
    indexedDataWrite_steps (input := input) put pc (by omega) valueStable fits
  have fetch : code[u.pc]? = some (.add next next one) := by
    rw [upc]
    exact placed 2 _ rfl
  obtain ⟨t, ut, tpc, tNext, tReg, tMem⟩ :=
    step_add_at (input := input) fetch (by omega)
  have hfit : (reg u next).val + (reg u one).val < 2 ^ bits := by
    rwa [uReg next nextStable, uReg one unitStable, unitVal]
  refine ⟨t, su.append (.cons ut (.zero t)), by omega, ?_, tMem.trans uMem, ?_⟩
  · rw [tNext, PaperB.WordOps.add_no_wrap _ _ hfit,
      uReg next nextStable, uReg one unitStable, unitVal]
  · intro r a b
    exact (tReg r a).trans (uReg r b)

/-- Two instructions store the command, then advance the stack cursor. -/
def pushCode {w r : Nat} (ptr base value one tmp : Fin r) : List (Instr w r) :=
  writeIncrement base ptr value ptr one tmp

/-- One decrement followed by the two instructions that read the top.
Popping preserves the arena, including cells outside the stack. -/
def popCode {w r : Nat} (ptr base value one : Fin r) : List (Instr w r) :=
  .sub ptr ptr one :: indexedDataRead value base ptr

theorem push_steps {entry : Nat} {ptr base value one tmp : Fin L.registerCount}
    {s : State L} {ws : List (Word bits)}
    (placed : Placed code entry (pushCode ptr base value one tmp))
    (pc : s.pc = entry) (cont : entry + 3 < code.size)
    (hptr : (reg s ptr).val = ws.length) (hunit : (reg s one).val = 1)
    (fits : (reg s base).val + ws.length < L.workCap)
    (nextFits : ws.length + 1 < 2 ^ bits)
    (srcStable : value ≠ tmp) (ptrStable : ptr ≠ tmp) (unitStable : one ≠ tmp)
    (stack : StackAt s.data (reg s base).val ws) :
    ∃ t, Steps code input 3 s t ∧ t.pc = entry + 3 ∧
      (reg t ptr).val = ws.length + 1 ∧
      StackAt t.data (reg s base).val (reg s value :: ws) ∧
      (∀ r, r ≠ ptr → r ≠ tmp → reg t r = reg s r) ∧
      (∀ i, i ≠ (reg s base).val + ws.length → t.data[i]? = s.data[i]?) := by
  let a := (reg s base).val + ws.length
  have ha : a < s.data.size := by rw [s.data_size]; exact fits
  have bound : (reg s base).val + (reg s ptr).val < L.workCap := by rwa [hptr]
  obtain ⟨t, ht, tpc, tPtr, tMem, unchanged⟩ :=
    writeIncrement_steps (input := input) placed pc cont hunit bound
      (by rwa [hptr]) srcStable ptrStable unitStable
  have addr : t.data = s.data.set a (reg s value) ha := by
    simpa only [a, hptr] using tMem
  have f : ∀ i, i ≠ a → t.data[i]? = s.data[i]? := by
    intro i different
    rw [addr]
    exact Array.getElem?_set_ne ha (Ne.symm different)
  refine ⟨t, ht, tpc, hptr ▸ tPtr, ?_, unchanged, f⟩
  refine ⟨?_, preserve stack ?_⟩
  · rw [addr]
    exact Array.getElem?_set_self ha
  · intro i before
    exact f _ (by dsimp only [a]; omega)

private theorem sub_exact (a b : Word bits) (h : b.val ≤ a.val) :
    (PaperB.WordOps.sub a b).val = a.val - b.val := by
  have ha := a.isLt
  have hlt : a.val - b.val < 2 ^ bits := by omega
  rw [PaperB.WordOps.sub_val,
    show 2 ^ bits + a.val - b.val = (a.val - b.val) + 2 ^ bits by omega,
    Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hlt]

theorem pop_steps {entry : Nat} {ptr base value one : Fin L.registerCount}
    {s : State L} {head : Word bits} {rest : List (Word bits)}
    (placed : Placed code entry (popCode ptr base value one))
    (pc : s.pc = entry) (cont : entry + 3 < code.size)
    (hptr : (reg s ptr).val = rest.length + 1) (hunit : (reg s one).val = 1)
    (fits : (reg s base).val + rest.length < L.workCap)
    (baseStable : base ≠ ptr) (ptrStable : ptr ≠ value)
    (stack : StackAt s.data (reg s base).val (head :: rest)) :
    ∃ t, Steps code input 3 s t ∧ t.pc = entry + 3 ∧
      (reg t ptr).val = rest.length ∧ reg t value = head ∧
      t.data = s.data ∧ StackAt t.data (reg s base).val rest ∧
      (∀ r, r ≠ ptr → r ≠ value → reg t r = reg s r) := by
  have hf : code[s.pc]? = some (.sub ptr ptr one) := by
    rw [pc, ← Nat.add_zero entry]
    exact placed 0 _ rfl
  obtain ⟨u, su, upc, new, uReg, uMem⟩ :=
    step_sub_at (input := input) hf (by omega)
  have uPtr : (reg u ptr).val = rest.length := by
    rw [new, sub_exact _ _ (by rw [hptr, hunit]; omega), hptr, hunit]
    omega
  have read : Placed code (entry + 1) (indexedDataRead value base ptr) := by
    intro k op hk
    have h : (popCode ptr base value one)[1 + k]? = some op := by
      rw [Nat.add_comm 1 k]
      exact hk
    rw [Nat.add_assoc]
    exact placed (1 + k) op h
  have ubound : (reg u base).val + (reg u ptr).val < L.workCap := by
    rwa [uReg base baseStable, uPtr]
  obtain ⟨t, ut, tpc, hRead, unchanged, tMem⟩ :=
    indexedDataRead_steps (input := input) read (by omega) (by omega) ubound
  rw [uMem, uReg base baseStable, uPtr, stack.1] at hRead
  have hd := tMem.trans uMem
  refine ⟨t, Steps.append (.cons su (.zero u)) ut, by omega, ?_,
    Option.some.inj hRead, hd, hd.symm ▸ stack.2, ?_⟩
  · rwa [unchanged ptr ptrStable]
  · intro r h₁ h₂
    exact (unchanged r h₂).trans (uReg r h₁)

/-- Starting a node stores the current timestamp then increments it.
Ending a node uses just the same indexed write, with the stop-column base. -/
def enterCode {w r : Nat} (stamp one base node tmp : Fin r) : List (Instr w r) :=
  writeIncrement base node stamp stamp one tmp

theorem enter_steps {entry : Nat} {stamp one base node tmp : Fin L.registerCount}
    {s : State L}
    (placed : Placed code entry (enterCode stamp one base node tmp))
    (pc : s.pc = entry) (cont : entry + 3 < code.size)
    (unitVal : (reg s one).val = 1)
    (fits : (reg s base).val + (reg s node).val < L.workCap)
    (nextFits : (reg s stamp).val + 1 < 2 ^ bits)
    (stampStable : stamp ≠ tmp) (unitStable : one ≠ tmp) :
    ∃ t, Steps code input 3 s t ∧ t.pc = entry + 3 ∧
      (reg t stamp).val = (reg s stamp).val + 1 ∧
      t.data = s.data.set ((reg s base).val + (reg s node).val)
        (reg s stamp) (by rw [s.data_size]; exact fits) ∧
      (∀ r, r ≠ stamp → r ≠ tmp → reg t r = reg s r) := by
  exact writeIncrement_steps placed pc cont unitVal fits nextFits stampStable
    stampStable unitStable

open PaperB.ForestLayout (Command)

/-- An enter command uses the lower vertex range; an exit command uses the
upper one. A single unsigned comparison selects the command branch. -/
def commandWord {n : Nat} (fits : 2 * n ≤ 2 ^ bits) : Command n → Word bits
  | .enter v => ⟨v.val, by have hv := v.isLt; omega⟩
  | .exit v => ⟨n + v.val, by have hv := v.isLt; omega⟩

theorem commandWord_enter_lt {n : Nat} (fits : 2*n ≤ 2 ^ bits) (v : Fin n) :
    (commandWord fits (.enter v)).val < n := v.isLt

theorem commandWord_exit_ge {n : Nat} (fits : 2*n ≤ 2 ^ bits) (v : Fin n) :
    n ≤ (commandWord fits (.exit v)).val := Nat.le_add_right _ _

theorem commandWord_exit_node {n : Nat} (fits : 2*n ≤ 2 ^ bits) (v : Fin n) :
    (commandWord fits (.exit v)).val - n = v.val := by
  change n + v.val - n = v.val
  omega


namespace Finish

open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.ForestLayout.LiveCells
open PaperB.ForestPreparedBuild

theorem stack_word_fits {vertices occupied : Nat}
    (capacity : occupied ≤ vertices + 1) :
    2 * occupied < 2 ^ OracleContract.wordBits 5 vertices 0 :=
  OracleContract.linear_payload_fits 5 vertices 0 2 _ (by decide)
    (Nat.mul_le_mul_left 2 (by simpa only [Nat.add_zero] using capacity))

/-- Two words per node suffice for the pending-command stack at each
completed step and during each reversed child-row push. Command tags
fit in the same word as the vertex ID. -/
theorem stackFits {n mass k : Nat} {g : ChildLists n} {root : Fin n}
    (prefixLive : PrefixLive g root mass k)
    (fit : 2 * n ≤ 2 ^ bits) :
    let s := layout g root k
    (s.stack.map (commandWord fit)).length ≤ 2 * n ∧
    ∀ v rest, s.stack = .enter v :: rest →
      ∀ ahead written, g.get v = ahead ++ written →
        ((pushChildren written (.exit v :: rest)).1.map (commandWord fit)).length
          ≤ 2 * n := by
  refine ⟨by simpa only [List.length_map] using prefixLive.pending, ?_⟩
  intro v rest h ahead written split
  simpa only [List.length_map] using (prefixLive.enterFold v rest h ahead written split).1

/-- The complete DFS pops and pushes exactly two commands per node.
The root push is included. At three instructions per linked stack
operation, the stack portion of the finish has a budget of 12 per node. -/
theorem exact_stackOperations {n : Nat} {root : Fin n} {parent : Fin n → Fin n}
    {depth : Fin n → Nat} (hTree : ValidDepthTree root parent depth) :
    let g := (groupedChildLists root parent).1
    let s := layout g root (2 * n)
    let pushes := 1 + s.enters + s.childrenQueued
    let pops := s.processed
    pushes = 2 * n ∧ pops = 2 * n ∧ 3 * pushes + 3 * pops = 12 * n := by
  intro g s pushes pops
  have hg : g = bucketChildLists root parent := groupedChildLists_eq_bucketChildLists _ _
  have hDone : s.stack = [] ∧ s.processed = 2 * n := by
    change (layout g root (2 * n)).stack = [] ∧
      (layout g root (2 * n)).processed = 2 * n
    rw [hg]
    exact layout_bucketChildren_exact hTree
  have bal : s.exits + s.stack.length = 1 + s.childrenQueued :=
    exit_pending_run g (2 * n) (initial root) rfl
  rw [hDone.1, List.length_nil] at bal
  have p := hDone.2
  change s.enters + s.exits = 2 * n at p
  change 1 + s.enters + s.childrenQueued = 2 * n ∧
    s.processed = 2 * n ∧ 3 * (1 + s.enters + s.childrenQueued) + 3 * s.processed = 12 * n
  omega

end Finish
end PaperB.RamForestStack
