module

public import PaperB.RamForestRowSetup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram

open PaperB.RamProgram
open PaperB.RamForestStack (StackAt commandWord commandWord_enter_lt commandWord_exit_ge)
open PaperB.Machine (Word)
open PaperB.ForestLayout (Command)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

def commandPC {n : Nat} : Command n → Nat
  | .enter _ => 5
  | .exit _ => 27

/-- Pop the next command and dispatch on its unsigned tag. The popped
word remains available in the command register. -/
theorem openCommand_steps (input : Input L) (s : State L) {n : Nat}
    (wordFits : 2 * n ≤ 2 ^ bits) (head : Command n) (tail : List (Command n))
    (pc : s.pc = 1) (one : (reg s registers.one).val = 1)
    (countEq : (reg s count).val = n)
    (ptr : (reg s registers.ptr).val = tail.length + 1)
    (fits : (reg s registers.stackBase).val + tail.length < workCap)
    (stack : StackAt s.data (reg s registers.stackBase).val
      (commandWord wordFits head :: tail.map (commandWord wordFits))) :
    ∃ t, Steps (program hi hw) input 4 s t ∧
      t.pc = commandPC head ∧
      reg t cmd = commandWord wordFits head ∧
      (reg t registers.ptr).val = tail.length ∧ t.data = s.data ∧
      StackAt t.data (reg s registers.stackBase).val (tail.map (commandWord wordFits)) ∧
      (∀ r : Fin 15, r ≠ registers.ptr → r ≠ cmd → reg t r = reg s r) := by
  have cap := program_size (hi := hi) (hw := hw)
  have hp : (reg s registers.ptr).val = (tail.map (commandWord wordFits)).length + 1 := by
    simpa only [List.length_map] using ptr
  have hf : (reg s registers.stackBase).val + (tail.map (commandWord wordFits)).length <
      workCap := by simpa only [List.length_map] using fits
  obtain ⟨u, su, upc, uPtr, uWord, uData, uStack, uRegs⟩ :=
    PaperB.RamForestStack.pop_steps (input := input) (pop_placed (hi := hi) (hw := hw))
      pc (by omega) hp one hf
      (by exact (by decide : registers.stackBase ≠ registers.ptr))
      (by exact (by decide : registers.ptr ≠ cmd)) stack
  obtain ⟨t, ut, tRegs, tData, tpc⟩ :=
    PaperB.RamForestDispatch.dispatch_steps (input := input)
      (dispatch_placed (hi := hi) (hw := hw)) upc (by omega) (by omega)
  have finalPC : t.pc = commandPC head := by
    rw [tpc, uWord, uRegs count (show count ≠ registers.ptr by decide) (show count ≠ cmd by decide), countEq]
    cases head with
    | enter v => exact ite_eq_left (commandWord_enter_lt wordFits v)
    | exit v => exact ite_eq_right (Nat.not_lt_of_ge (commandWord_exit_ge wordFits v))
  refine ⟨t, su.append ut, finalPC, (tRegs cmd).trans uWord, ?_,
    tData.trans uData, tData.symm ▸ uStack, ?_⟩
  · rw [tRegs registers.ptr, uPtr, List.length_map]
  · intro r a b
    exact (tRegs r).trans (uRegs r a b)

/-- Decode and store the closing timestamp, then return to the guard. -/
theorem closeNode_steps (input : Input L) (s : State L)
    {node : Nat} (pc : s.pc = 27)
    (commandTag : (reg s cmd).val = (reg s count).val + node)
    (fits : (reg s toutBase).val + node < workCap) :
    ∃ t, Steps (program hi hw) input 4 s t ∧ t.pc = 0 ∧
      t.data = s.data.set ((reg s toutBase).val + node) (reg s clk)
        (by rw [s.data_size]; exact fits) ∧
      (∀ r : Fin 15, r ≠ cmd → r ≠ registers.tmp → reg t r = reg s r) := by
  have cap := program_size (hi := hi) (hw := hw)
  obtain ⟨u, tr, upc, _, uData, uReg⟩ :=
    PaperB.RamForestDispatch.exit_steps (input := input) pc
      (exit_placed (hi := hi) (hw := hw)) (by omega) commandTag fits
      (by exact (by decide : toutBase ≠ cmd)) (by exact (by decide : clk ≠ cmd))
      (by exact (by decide : clk ≠ registers.tmp))
      (by exact (by decide : cmd ≠ registers.tmp))
  let t := {u with pc := 0}
  have f : (program hi hw)[u.pc]? = some (.goto 0) := by
    rw [upc]
    exact exit_back_fetch
  have back : step (program hi hw) input u = some (.next t) := step_goto_at f (by omega)
  exact ⟨t, tr.append (.cons back (.zero t)), rfl, uData, uReg⟩


/-- The child rows and pending commands occupy disjoint slices. The
post-visit stack begins with the children, then the node's closing tag. -/
structure EnterInput {ell : Layout bits} (row : List (Word bits)) where
  stackAddr : Nat
  rowAddr : Nat
  stop : Word bits
  start : Word bits
  tail : List (Word bits)
  closing : Word bits
  stop_eq : stop.val = start.val + row.length
  spaceRow : rowAddr + row.length ≤ ell.workCap
  spaceStack : stackAddr + (row.length + (closing :: tail).length) ≤ ell.workCap
  pointerFits : row.length + (closing :: tail).length < 2 ^ bits
  stackBeforeRow : stackAddr + (row.length + (closing :: tail).length) ≤ rowAddr

theorem stackFrame {orig next : Array (Word bits)} {base : Nat}
    {ws : List (Word bits)} (h : StackAt orig base ws)
    (same : ∀ i < ws.length, next[base + i]? = orig[base + i]?) :
    StackAt next base ws := by
  induction ws with
  | nil => exact True.intro
  | cons head tail ih =>
    refine ⟨(same _ (by simp)).trans h.1, ih h.2 ?_⟩
    intro j hj
    exact same j (by simp; omega)

/-- The opening path stores the entry timestamp, stages the CSR row, pushes
the closing command and all children, and takes the back edge. -/
theorem startNode_steps (input : Input L) (s : State L)
    (row : List (Word bits)) (a : EnterInput (ell := L) row)
    (pc : s.pc = 5) (one : (reg s registers.one).val = 1)
    (zero : (reg s registers.zero).val = 0)
    (ptr : (reg s registers.ptr).val = a.tail.length)
    (base : (reg s registers.stackBase).val = a.stackAddr)
    (stack : StackAt s.data a.stackAddr a.tail)
    (tag : a.closing.val = (reg s count).val + (reg s cmd).val)
    (src : a.rowAddr = (reg s childrenBase).val + a.start.val)
    (rowRead : ∀ j < row.length, s.data[a.rowAddr + j]? = row[j]?)
    (startRead : s.data[(reg s offsetBase).val + (reg s cmd).val]? = some a.start)
    (stopRead : s.data[(reg s offsetBase).val + (reg s cmd).val + 1]? = some a.stop)
    (headerFits : (reg s offsetBase).val + (reg s cmd).val + 1 < workCap)
    (rowWordFits : a.rowAddr < 2 ^ bits)
    (timeFits : (reg s tinBase).val + (reg s cmd).val < workCap)
    (clockFits : (reg s clk).val + 1 < 2 ^ bits)
    (writeAfterStack : a.stackAddr + (row.length + (a.closing :: a.tail).length) ≤
      (reg s tinBase).val + (reg s cmd).val)
    (writeBeforeRow : (reg s tinBase).val + (reg s cmd).val < a.rowAddr)
    (writeBeforeHeaders : (reg s tinBase).val + (reg s cmd).val <
      (reg s offsetBase).val + (reg s cmd).val) :
    ∃ t, Steps (program hi hw) input (15 + 8 * row.length) s t ∧ t.pc = 0 ∧
      (reg t clk).val = (reg s clk).val + 1 ∧
      (reg t registers.ptr).val = (row ++ (a.closing :: a.tail)).length ∧
      StackAt t.data a.stackAddr (row ++ (a.closing :: a.tail)) ∧
      t.data[(reg s tinBase).val + (reg s cmd).val]? = some (reg s clk) ∧
      (∀ j, j ≠ (reg s tinBase).val + (reg s cmd).val →
        (j < a.stackAddr + a.tail.length ∨
          a.stackAddr + (row.length + (a.closing :: a.tail).length) ≤ j) →
        t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ clk → r ≠ registers.ptr → r ≠ registers.remain →
        r ≠ registers.childBase → r ≠ registers.value → r ≠ registers.tmp →
        reg t r = reg s r) := by
  have cap := program_size (hi := hi) (hw := hw)
  let stampAddr := (reg s tinBase).val + (reg s cmd).val
  have stampFits : stampAddr < s.data.size := by rw [s.data_size]; exact timeFits
  obtain ⟨b, sb, bpc, bClock, bData, bRegs⟩ :=
    PaperB.RamForestStack.enter_steps (input := input) (enter_placed (hi := hi) (hw := hw))
      pc (by omega) one timeFits clockFits
      (by exact (by decide : clk ≠ registers.tmp))
      (by exact (by decide : registers.one ≠ registers.tmp))
  have bFrame : ∀ j, j ≠ stampAddr → b.data[j]? = s.data[j]? := by
    intro j other
    rw [bData]
    exact Array.getElem?_set_ne stampFits (Ne.symm other)
  have bReadStart : b.data[(reg b offsetBase).val + (reg b cmd).val]? = some a.start := by
    rw [bRegs offsetBase (show offsetBase ≠ clk by decide) (show offsetBase ≠ registers.tmp by decide), bRegs cmd (show cmd ≠ clk by decide) (show cmd ≠ registers.tmp by decide),
      bFrame _ (by omega)]
    exact startRead
  have bReadStop : b.data[(reg b offsetBase).val + (reg b cmd).val + 1]? = some a.stop := by
    rw [bRegs offsetBase (show offsetBase ≠ clk by decide) (show offsetBase ≠ registers.tmp by decide), bRegs cmd (show cmd ≠ clk by decide) (show cmd ≠ registers.tmp by decide),
      bFrame _ (by omega)]
    exact stopRead
  have bFits : (reg b offsetBase).val + (reg b cmd).val + 1 < workCap := by
    rwa [bRegs offsetBase (show offsetBase ≠ clk by decide) (show offsetBase ≠ registers.tmp by decide), bRegs cmd (show cmd ≠ clk by decide) (show cmd ≠ registers.tmp by decide)]
  have bRowFit : (reg b childrenBase).val + a.start.val < 2 ^ bits := by
    rwa [bRegs childrenBase (show childrenBase ≠ clk by decide) (show childrenBase ≠ registers.tmp by decide), ← src]
  have bOne : (reg b registers.one).val = 1 := by
    rwa [bRegs registers.one (show registers.one ≠ clk by decide) (show registers.one ≠ registers.tmp by decide)]
  have ordered : a.start.val ≤ a.stop.val := by rw [a.stop_eq]; omega
  obtain ⟨c, bc, cpc, cLength, cBase, cData, cRegs⟩ :=
    prepareRow_steps input b bpc bReadStart bReadStop bFits ordered bRowFit bOne
  have cFrame {r : Fin 15} (rClk : r ≠ clk) (rTmp : r ≠ registers.tmp)
      (rVal : r ≠ registers.value) (rLen : r ≠ registers.remain)
      (rBase : r ≠ registers.childBase) : reg c r = reg s r :=
    (cRegs r rTmp rVal rLen rBase).trans (bRegs r rClk rTmp)
  have hf : (program hi hw)[c.pc]? = some (.add registers.value count cmd) := by
    rw [cpc]
    exact tag_fetch
  obtain ⟨d, cd, dpc, dTag, dRegs, dData⟩ :=
    step_add_at (input := input) hf (by omega)
  have dTagExact : reg d registers.value = a.closing := by
    have cnt := cFrame (r := count) (by decide) (by decide) (by decide) (by decide) (by decide)
    have nd := cFrame (r := cmd) (by decide) (by decide) (by decide) (by decide) (by decide)
    have fit : (reg c count).val + (reg c cmd).val < 2 ^ bits := by
      rw [cnt, nd, ← tag]
      exact a.closing.isLt
    apply Fin.ext
    rw [dTag, PaperB.WordOps.add_no_wrap _ _ fit, cnt, nd, ← tag]
  have dFrame {r : Fin 15} (rClk : r ≠ clk) (rTmp : r ≠ registers.tmp)
      (rVal : r ≠ registers.value) (rLen : r ≠ registers.remain)
      (rBase : r ≠ registers.childBase) : reg d r = reg s r :=
    (dRegs r rVal).trans (cFrame rClk rTmp rVal rLen rBase)
  have dMem : d.data = b.data := dData.trans cData
  have dPtr : (reg d registers.ptr).val = a.tail.length := by
    rw [dFrame (r := registers.ptr) (by decide) (by decide) (by decide) (by decide) (by decide), ptr]
  have dBase : (reg d registers.stackBase).val = a.stackAddr := by
    rw [dFrame (r := registers.stackBase) (by decide) (by decide) (by decide) (by decide) (by decide), base]
  have dOne : (reg d registers.one).val = 1 := by
    rw [dFrame (r := registers.one) (by decide) (by decide) (by decide) (by decide) (by decide), one]
  have dStack : StackAt d.data (reg d registers.stackBase).val a.tail := by
    rw [dMem, dBase]
    apply stackFrame stack
    intro i ile
    apply bFrame
    simp only [List.length_cons] at writeAfterStack
    omega
  have eSafe : (reg d registers.stackBase).val + a.tail.length < workCap := by
    rw [dBase]
    have bound := a.spaceStack
    simp only [List.length_cons] at bound
    omega
  have ptrSafe : a.tail.length + 1 < 2 ^ bits := by
    have bound := a.pointerFits
    simp only [List.length_cons] at bound
    omega
  obtain ⟨e, de, epc, ePtr, eStack, eRegs, eData⟩ :=
    PaperB.RamForestStack.push_steps (input := input) (push_placed (hi := hi) (hw := hw))
      (by omega) (by omega) dPtr dOne eSafe ptrSafe
      (by exact (by decide : registers.value ≠ registers.tmp))
      (by exact (by decide : registers.ptr ≠ registers.tmp))
      (by exact (by decide : registers.one ≠ registers.tmp)) dStack
  let p : PaperB.RamPushChildRow.Placement bits workCap :=
    ⟨a.rowAddr, a.stackAddr, row, a.closing :: a.tail, a.spaceRow, a.spaceStack,
      Or.inr a.stackBeforeRow, a.pointerFits⟩
  have rInit : PaperB.RamPushChildRow.Cursor registers p 18 0 e e := by
    refine ⟨epc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (reg e registers.remain).val = row.length - 0
      rw [eRegs registers.remain (show registers.remain ≠ registers.ptr by decide) (show registers.remain ≠ registers.tmp by decide), dRegs registers.remain (show registers.remain ≠ registers.value by decide),
        cLength, a.stop_eq]
      omega
    · simpa [p] using ePtr
    · change (reg e registers.childBase).val = a.rowAddr
      rw [eRegs registers.childBase (show registers.childBase ≠ registers.ptr by decide) (show registers.childBase ≠ registers.tmp by decide), dRegs registers.childBase (show registers.childBase ≠ registers.value by decide),
        cBase, bRegs childrenBase (show childrenBase ≠ clk by decide) (show childrenBase ≠ registers.tmp by decide), src]
    · change (reg e registers.stackBase).val = a.stackAddr
      rw [eRegs registers.stackBase (show registers.stackBase ≠ registers.ptr by decide) (show registers.stackBase ≠ registers.tmp by decide), dBase]
    · rw [eRegs registers.one (show registers.one ≠ registers.ptr by decide) (show registers.one ≠ registers.tmp by decide), dOne]
    · rw [eRegs registers.zero (show registers.zero ≠ registers.ptr by decide) (show registers.zero ≠ registers.tmp by decide),
        dFrame (r := registers.zero) (by decide) (by decide) (by decide) (by decide) (by decide), zero]
    · intro j hj
      change e.data[a.rowAddr + j]? = row[j]?
      have safe := a.stackBeforeRow
      simp only [List.length_cons] at safe
      rw [eData _ (by rw [dBase]; omega), dMem, bFrame _ (by omega)]
      exact rowRead j hj
    · simpa [p, dBase, dTagExact] using eStack
    · intro _ _; rfl
    · intro _ _ _ _ _; rfl
  obtain ⟨f, ef, fpc, fPtr, _, fStack, _, fFrame, fRegs⟩ :=
    PaperB.RamPushChildRow.push_row_steps (input := input) registers p
      (row_placed (hi := hi) (hw := hw)) (by omega) rInit
  let t := { f with pc := 0 }
  have fFetch : (program hi hw)[f.pc]? = some (.goto 0) := by
    rw [show f.pc = 26 by omega]
    exact enter_back_fetch
  have ft : step (program hi hw) input f = some (.next t) := step_goto_at fFetch (by omega)
  have gStep : Steps (program hi hw) input 1 f t := .cons ft (.zero t)
  have tagStep : Steps (program hi hw) input 1 c d := .cons cd (.zero d)
  have hTrace := sb.append (bc.append (tagStep.append (de.append (ef.append gStep))))
  have arithmetic : 3 + (6 + (1 + (3 + (8 * row.length + 1 + 1)))) =
      15 + 8 * row.length := by omega
  refine ⟨t, ?_, rfl, ?_, fPtr, fStack, ?_, ?_, ?_⟩
  · change Steps (program hi hw) input (3 + (6 + (1 + (3 + (8 * row.length + 1 + 1))))) s t
      at hTrace
    rwa [arithmetic] at hTrace
  · change (reg f clk).val = _
    rw [fRegs clk (show clk ≠ registers.ptr by decide) (show clk ≠ registers.remain by decide) (show clk ≠ registers.value by decide) (show clk ≠ registers.tmp by decide),
      eRegs clk (show clk ≠ registers.ptr by decide) (show clk ≠ registers.tmp by decide), dRegs clk (show clk ≠ registers.value by decide),
      cRegs clk (show clk ≠ registers.tmp by decide) (show clk ≠ registers.value by decide) (show clk ≠ registers.remain by decide) (show clk ≠ registers.childBase by decide), bClock]
  · change f.data[stampAddr]? = _
    have hf' : p.stack + (p.row.length + p.old.length) ≤ stampAddr := writeAfterStack
    have eDistinct : stampAddr ≠ (reg d registers.stackBase).val + a.tail.length := by
      rw [dBase]
      simp only [List.length_cons, stampAddr] at writeAfterStack ⊢
      omega
    rw [fFrame _ (Or.inr hf'), eData _ eDistinct, dMem, bData]
    exact Array.getElem?_set_self stampFits
  · intro j different outside
    change f.data[j]? = _
    have fOutside : j < p.stack + p.old.length ∨ p.stack + (p.row.length + p.old.length) ≤ j := by
      rcases outside with small | large
      · left
        simp only [p, List.length_cons]
        omega
      · exact Or.inr large
    have eOutside : j ≠ (reg d registers.stackBase).val + a.tail.length := by
      rw [dBase]
      simp only [List.length_cons] at outside
      rcases outside with h | h <;> omega
    rw [fFrame _ fOutside, eData _ eOutside, dMem, bFrame _ different]
  · intro r clk' ptr' remain child value tmp
    exact (fRegs r ptr' remain value tmp).trans
      ((eRegs r ptr' tmp).trans (dFrame clk' tmp value remain child))

end PaperB.RamForestProgram
