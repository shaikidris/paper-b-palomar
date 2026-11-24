module

public import PaperB.RamForestStack

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamPushChildRow

open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.RamForestStack
open PaperB.WordOps (ltb)

variable {bits : Nat} {L : Layout bits}
variable {code : Program L} {input : Input L}

structure Registers (r : Nat) where
  atIndex : Fin 8 → Fin r
  injective : ∀ ⦃a b⦄, atIndex a = atIndex b → a = b

namespace Registers

variable {r : Nat} (R : Registers r)

abbrev ptr := R.atIndex 0
abbrev stackBase := R.atIndex 1
abbrev remain := R.atIndex 2
abbrev childBase := R.atIndex 3
abbrev value := R.atIndex 4
abbrev one := R.atIndex 5
abbrev tmp := R.atIndex 6
abbrev zero := R.atIndex 7

theorem distinct {a b : Fin 8} (h : a ≠ b) : R.atIndex a ≠ R.atIndex b :=
  fun e => h (R.injective e)

end Registers

/-- Read children in reverse order and push one command at a time.
Each successful loop iteration has one guard, one decrement, two load
instructions, three push instructions and a back-edge. -/
def codeBlock {w r : Nat} (R : Registers r) (entry : Nat) : List (Instr w r) :=
  [.branchLt R.zero R.remain (entry + 1) (entry + 8),
    .sub R.remain R.remain R.one] ++
    indexedDataRead R.value R.childBase R.remain ++
    pushCode R.ptr R.stackBase R.value R.one R.tmp ++ [.goto entry]

structure Placement (bits cap : Nat) where
  source : Nat
  stack : Nat
  row : List (Word bits)
  old : List (Word bits)
  src_fits : source + row.length ≤ cap
  stack_fits : stack + (row.length + old.length) ≤ cap
  separated : source + row.length ≤ stack ∨
    stack + (row.length + old.length) ≤ source
  ptr_fits : row.length + old.length < 2 ^ bits

/-- The suffix already read from the right end is atop the old stack in
its original row order. The row itself stays intact at every iteration. -/
structure Cursor (R : Registers L.registerCount) (place : Placement bits L.workCap)
    (entry k : Nat) (initial s : State L) : Prop where
  pc : s.pc = entry
  remaining : (reg s R.remain).val = place.row.length - k
  ptr : (reg s R.ptr).val = (place.row.drop (place.row.length - k) ++ place.old).length
  source : (reg s R.childBase).val = place.source
  base : (reg s R.stackBase).val = place.stack
  one : (reg s R.one).val = 1
  zero : (reg s R.zero).val = 0
  row : ∀ j < place.row.length, s.data[place.source + j]? = place.row[j]?
  stack : StackAt s.data place.stack (place.row.drop (place.row.length - k) ++ place.old)
  frame : ∀ j, j < place.stack + place.old.length ∨
      place.stack + (place.row.length + place.old.length) ≤ j →
    s.data[j]? = initial.data[j]?
  regs : ∀ r, r ≠ R.ptr → r ≠ R.remain → r ≠ R.value → r ≠ R.tmp →
    reg s r = reg initial r

private theorem subOne (u v : Word bits) (hu : 1 ≤ u.val) (hv : v.val = 1) :
    (PaperB.WordOps.sub u v).val = u.val - 1 := by
  have hlt : u.val - 1 < 2 ^ bits := by have := u.isLt; omega
  rw [PaperB.WordOps.sub_val, hv,
    show 2 ^ bits + u.val - 1 = (u.val - 1) + 2 ^ bits by omega, Nat.add_mod]
  simp only [Nat.mod_self, Nat.add_zero, Nat.mod_eq_of_lt hlt]

private theorem placed_read (R : Registers L.registerCount) {entry : Nat}
    (placed : Placed code entry (codeBlock R entry)) :
    Placed code (entry + 2) (indexedDataRead R.value R.childBase R.remain) := by
  intro i op hi
  cases i with
  | zero =>
    have eq : Instr.add R.value R.childBase R.remain = op := Option.some.inj hi
    subst op
    exact placed 2 _ rfl
  | succ i =>
    cases i with
    | zero =>
      have eq : Instr.loadData R.value R.value = op := Option.some.inj hi
      subst op
      exact placed 3 _ rfl
    | succ i => simp [indexedDataRead] at hi

private theorem placed_push (R : Registers L.registerCount) {entry : Nat}
    (placed : Placed code entry (codeBlock R entry)) :
    Placed code (entry + 4) (pushCode R.ptr R.stackBase R.value R.one R.tmp) := by
  intro i op hi
  let prefixCode : List (Instr bits L.registerCount) :=
    [.branchLt R.zero R.remain (entry + 1) (entry + 8),
      .sub R.remain R.remain R.one] ++ indexedDataRead R.value R.childBase R.remain
  let push := pushCode (w := bits) R.ptr R.stackBase R.value R.one R.tmp
  have hlen : prefixCode.length = 4 := rfl
  have hidx : i < push.length := (List.getElem?_eq_some_iff.mp hi).choose
  have h : (codeBlock (w := bits) R entry)[4 + i]? = some op := by
    rw [show codeBlock (w := bits) R entry = prefixCode ++ (push ++ [.goto entry]) by
      simp only [codeBlock, prefixCode, push, List.append_assoc]]
    rw [List.getElem?_append_right (by omega : prefixCode.length ≤ 4 + i), hlen]
    rw [show 4 + i - 4 = i by omega, List.getElem?_append_left hidx]
    exact hi
  rw [Nat.add_assoc]
  exact placed (4 + i) op h

private theorem iteration (R : Registers L.registerCount) (p : Placement bits L.workCap)
    {entry k : Nat} {initial : State L} (placed : Placed code entry (codeBlock R entry))
    (head : entry < code.size) (exit : entry + 8 < code.size)
    (hk : k < p.row.length) :
    BlockSpec code input 8 (Cursor R p entry k initial) (Cursor R p entry (k + 1) initial) := by
  intro s hs
  let i := p.row.length - (k + 1)
  let old := p.row.drop (p.row.length - k) ++ p.old
  have hi : i < p.row.length := by dsimp [i]; omega
  have iNext : i + 1 = p.row.length - k := by dsimp [i]; omega
  have oldLen : old.length = k + p.old.length := by
    simp only [old, List.length_append, List.length_drop]
    omega
  have dropEq : p.row.drop (p.row.length - (k + 1)) ++ p.old =
      p.row[i]'hi :: old := by
    change p.row.drop i ++ p.old = _
    rw [List.drop_eq_getElem_cons hi, iNext]
    rfl
  have take :
      ltb (reg s R.zero) (reg s R.remain) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hs.zero, hs.remaining]; omega)
  let a := {s with pc := entry + 1}
  have ha : step code input s = some (.next a) := by
    have f : code[s.pc]? = some (.branchLt R.zero R.remain (entry + 1) (entry + 8)) := by
      rw [hs.pc, ← Nat.add_zero entry]
      exact placed 0 _ rfl
    simpa [take, a] using
      step_branchLt_at (input := input) f (by simp [take]; omega)
  have fSub : code[a.pc]? = some (.sub R.remain R.remain R.one) :=
    placed 1 _ rfl
  obtain ⟨b, ab, bPc, bRem, bReg, bData⟩ :=
    step_sub_at (input := input) fSub (by change entry + 2 < code.size; omega)
  have bSame {r : Fin L.registerCount} (h : r ≠ R.remain) : reg b r = reg s r :=
    bReg r h
  have bRemaining : (reg b R.remain).val = i := by
    rw [bRem, subOne _ _ (by change 1 ≤ (reg s R.remain).val; rw [hs.remaining]; omega)
      (by exact hs.one)]
    change (reg s R.remain).val - 1 = i
    rw [hs.remaining]
    dsimp [i]
    omega
  have bBound : (reg b R.childBase).val + (reg b R.remain).val < L.workCap := by
    rw [bSame (R.distinct (by decide)), bRemaining, hs.source]
    have := p.src_fits
    omega
  obtain ⟨c, bc, cPc, cLoad, cReg, cData⟩ :=
    indexedDataRead_steps (input := input) (placed_read R placed)
      (by exact bPc) (by omega) bBound
  have bMem : b.data = s.data := bData
  have cMem : c.data = s.data := cData.trans bMem
  have cSame {r : Fin L.registerCount} (u : r ≠ R.value) (v : r ≠ R.remain) :
      reg c r = reg s r := (cReg r u).trans (bSame v)
  have payload : reg c R.value = p.row[i]'hi := by
    rw [bSame (R.distinct (by decide)), bRemaining, bMem, hs.source, hs.row i hi,
      getElem?_pos p.row i hi] at cLoad
    exact Option.some.inj cLoad
  have pStack : StackAt c.data (reg c R.stackBase).val old := by
    rw [cSame (R.distinct (by decide)) (R.distinct (by decide)), hs.base, cMem]
    exact hs.stack
  have cPtr : (reg c R.ptr).val = old.length :=
    (congrArg Fin.val (cSame (R.distinct (by decide)) (R.distinct (by decide)))).trans hs.ptr
  have cBase : (reg c R.stackBase).val = p.stack :=
    (congrArg Fin.val (cSame (R.distinct (by decide)) (R.distinct (by decide)))).trans hs.base
  have cUnit : (reg c R.one).val = 1 :=
    (congrArg Fin.val (cSame (R.distinct (by decide)) (R.distinct (by decide)))).trans hs.one
  have pushBound : (reg c R.stackBase).val + old.length < L.workCap := by
    rw [cBase, oldLen]
    have := p.stack_fits
    omega
  have pushWord : old.length + 1 < 2 ^ bits := by
    rw [oldLen]
    have := p.ptr_fits
    omega
  obtain ⟨d, cd, dPc, dPtr, dStack, dStable, dFrame⟩ :=
    push_steps (input := input) (placed_push R placed) (by omega) (by omega)
      cPtr cUnit pushBound pushWord (R.distinct (by decide)) (R.distinct (by decide))
      (R.distinct (by decide)) pStack
  let e := { d with pc := entry }
  have de : step code input d = some (.next e) :=
    step_goto_at (by rw [show d.pc = entry + 7 by omega]; exact placed 7 _ rfl) head
  have stable {r : Fin L.registerCount} (hp : r ≠ R.ptr) (ht : r ≠ R.tmp)
      (hv : r ≠ R.value) (hr : r ≠ R.remain) :
      reg e r = reg s r := (dStable r hp ht).trans (cSame hv hr)
  refine ⟨e, ?_, ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have sab : Steps code input 2 s b := .cons ha (.cons ab (.zero b))
    have sde : Steps code input 1 d e := .cons de (.zero e)
    exact sab.append (bc.append (cd.append sde))
  · change (reg d R.remain).val = i
    rw [dStable _ (R.distinct (by decide)) (R.distinct (by decide)),
      cReg _ (R.distinct (by decide)), bRemaining]
  · change (reg d R.ptr).val = _
    rw [dPtr, dropEq, List.length_cons]
  · rw [stable (R.distinct (by decide)) (R.distinct (by decide))
      (R.distinct (by decide)) (R.distinct (by decide)), hs.source]
  · rw [stable (R.distinct (by decide)) (R.distinct (by decide))
      (R.distinct (by decide)) (R.distinct (by decide)), hs.base]
  · rw [stable (R.distinct (by decide)) (R.distinct (by decide))
      (R.distinct (by decide)) (R.distinct (by decide)), hs.one]
  · rw [stable (R.distinct (by decide)) (R.distinct (by decide))
      (R.distinct (by decide)) (R.distinct (by decide)), hs.zero]
  · intro j hj
    change d.data[p.source + j]? = _
    rw [dFrame, cMem, hs.row j hj]
    rw [cBase, oldLen]
    rcases p.separated with h | h <;> omega
  · change StackAt d.data p.stack _
    rw [dropEq, ← payload, ← cBase]
    exact dStack
  · intro j separate
    change d.data[j]? = _
    rw [dFrame, cMem, hs.frame j separate]
    rw [cBase, oldLen]
    rcases separate with h | h <;> omega
  · intro r a b c d
    exact (stable a d c b).trans (hs.regs r a b c d)

private theorem iterations (n : Nat) : iterationCost (fun _ => 8) n = 8 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterationCost, ih, Nat.mul_succ]

/-- A child list is pushed in exactly eight instructions per child plus the
exit guard. Control passes to the following instruction, with the child
row intact and its original order preserved at the top of the stack. -/
theorem push_row_steps (R : Registers L.registerCount) (p : Placement bits L.workCap)
    {entry : Nat} (placed : Placed code entry (codeBlock R entry))
    (exit : entry + 8 < code.size) {s : State L} (start : Cursor R p entry 0 s s) :
    ∃ t, Steps code input (8 * p.row.length + 1) s t ∧
      t.pc = entry + 8 ∧
      (reg t R.ptr).val = (p.row ++ p.old).length ∧
      (reg t R.remain).val = 0 ∧ StackAt t.data p.stack (p.row ++ p.old) ∧
      (∀ j < p.row.length, t.data[p.source + j]? = p.row[j]?) ∧
      (∀ j, j < p.stack + p.old.length ∨ p.stack + (p.row.length + p.old.length) ≤ j →
        t.data[j]? = s.data[j]?) ∧
      (∀ r, r ≠ R.ptr → r ≠ R.remain → r ≠ R.value → r ≠ R.tmp →
        reg t r = reg s r) := by
  obtain ⟨u, reach, done⟩ :=
    loop_steps (code := code) (input := input) p.row.length (fun _ => 8)
      (fun k => Cursor R p entry k s) (fun _ h => iteration R p placed (by omega) exit h) s start
  have no : ltb (reg u R.zero) (reg u R.remain) = false := by
    cases v : ltb (reg u R.zero) (reg u R.remain)
    · rfl
    · have bad := (PaperB.WordOps.ltb_eq_true _ _).mp v
      rw [done.zero, done.remaining, Nat.sub_self] at bad
      omega
  let t := { u with pc := entry + 8 }
  have hs : step code input u = some (.next t) := by
    have f : code[u.pc]? = some (.branchLt R.zero R.remain (entry + 1) (entry + 8)) := by
      rw [done.pc, ← Nat.add_zero entry]
      exact placed 0 _ rfl
    simpa [no, t] using step_branchLt_at (input := input) f (by simpa [no] using exit)
  rw [iterations] at reach
  refine ⟨t, reach.append (.cons hs (.zero t)), rfl, ?_, ?_, ?_,
    done.row, done.frame, done.regs⟩
  · change (reg u R.ptr).val = _
    simpa only [Nat.sub_self, List.drop_zero] using done.ptr
  · change (reg u R.remain).val = _
    simpa only [Nat.sub_self] using done.remaining
  · simpa only [t, Nat.sub_self, List.drop_zero] using done.stack


open PaperB.ForestLayout (Command pushChildren pushChildren_spec)

/-- Bind the checked row transfer to the exact children ordering used by the
compact interval traversal. The exit command is already the old stack head. -/
theorem encode_children_stack {n : Nat} (hfit : 2 * n ≤ 2 ^ bits)
    (children : List (Fin n)) (v : Fin n) (tail : List (Command n)) :
    ((pushChildren children (.exit v :: tail)).1.map (commandWord hfit)) =
      children.map (fun u => commandWord hfit (.enter u)) ++
        ((Command.exit v :: tail).map (commandWord hfit)) := by
  simp only [pushChildren_spec, List.map_append, List.map_map, Function.comp_def]

end PaperB.RamPushChildRow
