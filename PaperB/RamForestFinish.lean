module

public import PaperB.RamForestCommand
public import PaperB.RamForestDriver

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram
open PaperB.RamForestStack (StackAt commandWord)
open PaperB.Machine (Word)
open PaperB.ForestLayout (ChildLists Command advance advance_enter_spec advance_exit_spec)
open PaperB.ForestLayout.LiveCells (PrefixLive)
open PaperB.LabelledQuotient (ValidDepthTree)

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw
local notation "Ref" => PaperB.ForestLayout.State n

/-- Arena from left to right: stack, entry times, stop times, CSR offsets
and CSR children. All five banks are reserved through the traversal. -/
structure Arena (bits cap n : Nat) where
  base : Nat
  children : Nat
  room : base + 5 * n + 1 + children ≤ cap
  wordFits : base + 5 * n + 1 + children < 2 ^ bits

namespace Arena
variable (a : Arena bits workCap n)

def tin : Nat := a.base + 2 * n
def tout : Nat := a.base + 3 * n
def offsets : Nat := a.base + 4 * n
def payload : Nat := a.base + 5 * n + 1

theorem tags (a : Arena bits workCap n) : 2 * n ≤ 2 ^ bits := by have := a.wordFits; omega

end Arena

private def fixedRegs : List (Fin 15) :=
  [registers.zero, registers.one, registers.stackBase, count, tinBase, toutBase,
    offsetBase, childrenBase]

private theorem fixed_ne {r : Fin 15} (fixed : r ∈ fixedRegs) :
    r ≠ registers.ptr ∧ r ≠ cmd ∧ r ≠ clk ∧ r ≠ registers.tmp ∧
      r ≠ registers.value ∧ r ≠ registers.remain ∧ r ≠ registers.childBase :=
  (by decide : ∀ r : Fin 15, r ∈ fixedRegs →
    r ≠ registers.ptr ∧ r ≠ cmd ∧ r ≠ clk ∧ r ≠ registers.tmp ∧
      r ≠ registers.value ∧ r ≠ registers.remain ∧ r ≠ registers.childBase) r fixed

structure Control (a : Arena bits workCap n) (s : State L) : Prop where
  count_eq : (reg s count).val = n
  one : (reg s registers.one).val = 1
  zero : (reg s registers.zero).val = 0
  stackBase_eq : (reg s registers.stackBase).val = a.base
  tin_eq : (reg s tinBase).val = a.tin
  tout_eq : (reg s toutBase).val = a.tout
  offset_eq : (reg s offsetBase).val = a.offsets
  child_eq : (reg s childrenBase).val = a.payload

private theorem Control.transfer {a : Arena bits workCap n} {s t : State L}
    (h : Control a s) (frame : ∀ r ∈ fixedRegs, reg t r = reg s r) : Control a t :=
  ⟨(congrArg Fin.val (frame count (by decide +revert))).trans h.count_eq,
    (congrArg Fin.val (frame registers.one (by decide +revert))).trans h.one,
    (congrArg Fin.val (frame registers.zero (by decide +revert))).trans h.zero,
    (congrArg Fin.val (frame registers.stackBase (by decide +revert))).trans h.stackBase_eq,
    (congrArg Fin.val (frame tinBase (by decide +revert))).trans h.tin_eq,
    (congrArg Fin.val (frame toutBase (by decide +revert))).trans h.tout_eq,
    (congrArg Fin.val (frame offsetBase (by decide +revert))).trans h.offset_eq,
    (congrArg Fin.val (frame childrenBase (by decide +revert))).trans h.child_eq⟩

def childrenOf (a : Arena bits workCap n) (g : ChildLists n) (v : Fin n) :
    List (Word bits) :=
  (g.get v).map (fun u => commandWord a.tags (.enter u))

/-- Prepared CSR view, including the extra terminal offset. -/
def ChildImage (a : Arena bits workCap n) (g : ChildLists n)
    (data : Array (Word bits)) : Prop :=
  ∀ v : Fin n, ∃ (lo stop : Word bits),
    data[a.offsets + v.val]? = some lo ∧
    data[a.offsets + v.val + 1]? = some stop ∧
    stop.val = lo.val + (childrenOf a g v).length ∧
    stop.val ≤ a.children ∧
    (∀ j < (childrenOf a g v).length,
      data[a.payload + lo.val + j]? = (childrenOf a g v)[j]?)

private theorem ChildImage.transfer {a : Arena bits workCap n} {g : ChildLists n}
    {s t : Array (Word bits)} (old : ChildImage a g s)
    (frame : ∀ j, a.offsets ≤ j → t[j]? = s[j]?) : ChildImage a g t := by
  intro v
  obtain ⟨lo, stop, loRead, stopRead, degree, fits, words⟩ := old v
  refine ⟨lo, stop, ?_, ?_, degree, fits, ?_⟩
  · rw [frame _ (by omega)]; exact loRead
  · rw [frame _ (by omega)]; exact stopRead
  · intro j hj
    have h : a.offsets ≤ a.payload + lo.val + j := by unfold Arena.offsets Arena.payload; omega
    rw [frame _ h]; exact words j hj

def ColumnAt (base : Nat) (col : Array Nat) (data : Array (Word bits)) : Prop :=
  ∀ i : Fin n, (data[base + i.val]?).map Fin.val = col[i.val]?

private theorem ColumnAt.transfer {base : Nat} {col : Array Nat}
    {s t : Array (Word bits)}
    (h : ColumnAt (n := n) base col s)
    (frame : ∀ i : Fin n, t[base + i.val]? = s[base + i.val]?) :
    ColumnAt (n := n) base col t := by
  intro i
  rw [frame i]
  exact h i

private theorem ColumnAt.put {base : Nat} {col : Array Nat} {s t : Array (Word bits)}
    {node : Fin n} {w : Word bits} (fits : node.val < col.size)
    (old : ColumnAt (n := n) base col s)
    (write : t[base + node.val]? = some w)
    (frame : ∀ i : Fin n, i ≠ node → t[base + i.val]? = s[base + i.val]?) :
    ColumnAt (n := n) base (col.set node.val w.val fits) t := by
  intro i
  by_cases eq : i = node
  · subst i
    rw [write, Array.getElem?_set_self fits]
    rfl
  · rw [frame i eq, old i]
    exact (Array.getElem?_set_ne fits (fun e => eq (Fin.ext e.symm))).symm

/-- Relation at the machine guard. The reference stack is represented
top-first by the occupied prefix of the command bank. -/
structure AtGuard (a : Arena bits workCap n) (g : ChildLists n) (ref : Ref)
    (s : State L) : Prop where
  pc : s.pc = 0
  regs : Control a s
  ptr : (reg s registers.ptr).val = ref.stack.length
  clk_eq : (reg s clk).val = ref.enters
  stack : StackAt s.data a.base (ref.stack.map (commandWord a.tags))
  childRows : ChildImage a g s.data
  entries : ColumnAt (n := n) a.tin ref.entries s.data
  ends : ColumnAt (n := n) a.tout ref.ends s.data

private theorem openGuard {a : Arena bits workCap n} {g : ChildLists n}
    (input : Input L) {ref : Ref} {s : State L}
    (atGuard : AtGuard a g ref s) (head : Command n) (tail : List (Command n))
    (nonempty : ref.stack = head :: tail) (sizeBound : ref.stack.length ≤ 2 * n) :
    ∃ u, Steps (program hi hw) input 4 {s with pc := 1} u ∧ u.pc = commandPC head ∧
      reg u cmd = commandWord a.tags head ∧ (reg u registers.ptr).val = tail.length ∧
      u.data = s.data ∧ StackAt u.data a.base (tail.map (commandWord a.tags)) ∧
      Control a u ∧ (reg u clk).val = ref.enters := by
  have room := a.room
  let entry := { s with pc := 1 }
  have openPtr : (reg entry registers.ptr).val = tail.length + 1 := by
    change (reg s registers.ptr).val = _
    rw [atGuard.ptr, nonempty, List.length_cons]
  have openFits : (reg entry registers.stackBase).val + tail.length < workCap := by
    change (reg s registers.stackBase).val + tail.length < workCap
    rw [atGuard.regs.stackBase_eq]
    rw [nonempty, List.length_cons] at sizeBound
    omega
  have openStack : StackAt entry.data (reg entry registers.stackBase).val
      (commandWord a.tags head :: tail.map (commandWord a.tags)) := by
    change StackAt s.data (reg s registers.stackBase).val _
    rw [atGuard.regs.stackBase_eq]
    simpa only [nonempty, List.map_cons] using atGuard.stack
  obtain ⟨u, su, upc, uCmd, uPtr, uData, uStack, uRegs⟩ :=
    openCommand_steps input entry a.tags head tail rfl atGuard.regs.one
      atGuard.regs.count_eq openPtr openFits openStack
  have uc : Control a u := atGuard.regs.transfer (fun r hr =>
    let h := fixed_ne hr
    uRegs r h.1 h.2.1)
  have uClock : (reg u clk).val = ref.enters := by
    have eq := uRegs clk (by decide +revert) (by decide +revert)
    exact (congrArg Fin.val eq).trans atGuard.clk_eq
  refine ⟨u, su, upc, uCmd, uPtr, uData, ?_, uc, uClock⟩
  change StackAt u.data (reg s registers.stackBase).val _ at uStack
  simpa only [atGuard.regs.stackBase_eq] using uStack

private theorem after_exit {a : Arena bits workCap n} {g : ChildLists n}
    (input : Input L) {ref : Ref} {s : State L}
    (atGuard : AtGuard a g ref s) (v : Fin n) (tail : List (Command n))
    (nonempty : ref.stack = .exit v :: tail) (sizeBound : ref.stack.length ≤ 2 * n) :
    ∃ t, Steps (program hi hw) input 8 {s with pc := 1} t ∧
      AtGuard a g (advance g ref (.exit v) tail) t ∧
      (∀ j < a.base, t.data[j]? = s.data[j]?) := by
  have room := a.room
  obtain ⟨u, su, upc, uCmd, uPtr, uData, uStack, uc, uClock⟩ :=
    openGuard input atGuard (.exit v) tail nonempty sizeBound
  have tag : (reg u cmd).val = (reg u count).val + v.val := by
    rw [uCmd, uc.count_eq]
    rfl
  have fits : (reg u toutBase).val + v.val < workCap := by
    rw [uc.tout_eq]
    unfold Arena.tout
    have := v.isLt
    omega
  obtain ⟨t, ut, tpc, tMem, tRegs⟩ := closeNode_steps input u upc tag fits
  have whereWrite : t.data = u.data.set (a.tout + v.val) (reg u clk)
      (by rw [u.data_size]; rw [← uc.tout_eq]; exact fits) := by
    simpa only [uc.tout_eq] using tMem
  have untouched : ∀ j, j ≠ a.tout + v.val → t.data[j]? = u.data[j]? := by
    intro j hj
    rw [whereWrite]
    exact Array.getElem?_set_ne _ hj.symm
  have tc := uc.transfer (fun r hr =>
    let h := fixed_ne hr
    tRegs r h.2.1 h.2.2.2.1)
  obtain ⟨nextStack, nextTin, nextTout, nextClock, _, _⟩ := advance_exit_spec g ref v tail
  refine ⟨t, su.append ut, ⟨tpc, tc, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have h := tRegs registers.ptr (by decide +revert) (by decide +revert)
    rw [h, uPtr, nextStack]
  · have h := tRegs clk (by decide +revert) (by decide +revert)
    rw [h, uClock, nextClock]
  · rw [nextStack]
    apply stackFrame uStack
    intro i ilt
    apply untouched
    simp only [List.length_map] at ilt
    rw [nonempty, List.length_cons] at sizeBound
    unfold Arena.tout
    omega
  · apply ChildImage.transfer (s := u.data)
      (by simpa only [uData] using atGuard.childRows)
    intro j bound
    apply untouched
    unfold Arena.offsets Arena.tout at *
    have := v.isLt
    omega
  · rw [nextTin]
    apply ColumnAt.transfer (s := u.data) (by simpa only [uData] using atGuard.entries)
    intro i
    apply untouched
    unfold Arena.tin Arena.tout
    have := i.isLt
    omega
  · rw [nextTout, ← uClock]
    apply ColumnAt.put (s := u.data)
      (old := by simpa only [uData] using atGuard.ends)
    · rw [whereWrite]
      exact Array.getElem?_set_self _
    · intro i different
      apply untouched
      intro e
      apply different
      exact Fin.ext (Nat.add_left_cancel e)

  · intro j hj
    rw [untouched _ (by unfold Arena.tout; omega), uData]

private theorem after_enter {a : Arena bits workCap n} {g : ChildLists n}
    (input : Input L) {ref : Ref} {s : State L}
    (atGuard : AtGuard a g ref s) (v : Fin n) (tail : List (Command n))
    (nonempty : ref.stack = .enter v :: tail) (sizeBound : ref.stack.length ≤ 2 * n)
    (nextBound : (advance g ref (.enter v) tail).stack.length ≤ 2 * n)
    (clockBound : ref.enters < 2 * n) :
    ∃ t, Steps (program hi hw) input (19 + 8 * (g.get v).length) {s with pc := 1} t ∧
      AtGuard a g (advance g ref (.enter v) tail) t ∧
      (∀ j < a.base, t.data[j]? = s.data[j]?) := by
  have room := a.room
  have width := a.wordFits
  have vertex := v.isLt
  obtain ⟨u, su, upc, uCmd, uPtr, uData, uStack, uc, uClock⟩ :=
    openGuard input atGuard (.enter v) tail nonempty sizeBound
  have node : (reg u cmd).val = v.val := by rw [uCmd]; rfl
  obtain ⟨lo, stop, loRead, stopRead, degree, mass, words⟩ := atGuard.childRows v
  let row := childrenOf a g v
  let closing := commandWord a.tags (.exit v)
  let pending := tail.map (commandWord a.tags)
  obtain ⟨nextStack, nextTin, nextTout, nextClock, _, _⟩ := advance_enter_spec g ref v tail
  have stacked : row.length + (closing :: pending).length ≤ 2 * n := by
    rw [nextStack, List.length_append, List.length_map, List.length_cons] at nextBound
    simpa only [row, childrenOf, pending, List.length_map, List.length_cons] using nextBound
  change stop.val = lo.val + row.length at degree
  have rowRoom : lo.val + row.length ≤ a.children := by omega
  let prepared : EnterInput (ell := L) row :=
    { stackAddr := a.base, rowAddr := a.payload + lo.val, stop := stop, start := lo,
      tail := pending, closing := closing, stop_eq := degree,
      spaceRow := by change a.payload + lo.val + row.length ≤ workCap; unfold Arena.payload; omega,
      spaceStack := by change a.base + (row.length + (closing :: pending).length) ≤ workCap; omega, pointerFits := by omega,
      stackBeforeRow := by unfold Arena.payload; omega }
  have ptr : (reg u registers.ptr).val = pending.length := by
    simpa only [pending, List.length_map] using uPtr
  have tag : closing.val = (reg u count).val + (reg u cmd).val := by
    rw [uc.count_eq, node]; rfl
  have src : prepared.rowAddr = (reg u childrenBase).val + prepared.start.val := by
    rw [uc.child_eq]
  have getRow : ∀ j < row.length, u.data[prepared.rowAddr + j]? = row[j]? := by
    intro j hj
    rw [uData]
    exact words j hj
  have startRead : u.data[(reg u offsetBase).val + (reg u cmd).val]? = some prepared.start := by
    rw [uc.offset_eq, node, uData]
    exact loRead
  have stopRead' : u.data[(reg u offsetBase).val + (reg u cmd).val + 1]? = some prepared.stop := by
    rw [uc.offset_eq, node, uData]
    exact stopRead
  have headerFits : (reg u offsetBase).val + (reg u cmd).val + 1 < workCap := by
    rw [uc.offset_eq, node]
    unfold Arena.offsets
    omega
  have rowWordFits : prepared.rowAddr < 2 ^ bits := by
    change a.payload + lo.val < 2 ^ bits
    unfold Arena.payload
    omega
  have timeFits : (reg u tinBase).val + (reg u cmd).val < workCap := by
    rw [uc.tin_eq, node]
    unfold Arena.tin
    omega
  have clockFits : (reg u clk).val + 1 < 2 ^ bits := by omega
  have afterStack : prepared.stackAddr + (row.length +
      (prepared.closing :: prepared.tail).length) ≤ (reg u tinBase).val + (reg u cmd).val := by
    rw [uc.tin_eq, node]
    change a.base + (row.length + (closing :: pending).length) ≤ a.tin + v.val
    unfold Arena.tin
    omega
  have beforeRow : (reg u tinBase).val + (reg u cmd).val < prepared.rowAddr := by
    rw [uc.tin_eq, node]
    change a.tin + v.val < a.payload + lo.val
    unfold Arena.tin Arena.payload
    omega
  have beforeHeader : (reg u tinBase).val + (reg u cmd).val <
      (reg u offsetBase).val + (reg u cmd).val := by
    rw [uc.tin_eq, uc.offset_eq, node]
    unfold Arena.tin Arena.offsets
    omega
  obtain ⟨t, ut, tpc, tClock, tPtr, tStack, tWrite, tFrame, tRegs⟩ :=
    startNode_steps input u row prepared upc uc.one uc.zero ptr uc.stackBase_eq uStack tag src
      getRow startRead stopRead' headerFits rowWordFits timeFits clockFits
      afterStack beforeRow beforeHeader
  have tc := uc.transfer (fun r hr =>
    let h := fixed_ne hr
    tRegs r h.2.2.1 h.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2 h.2.2.2.2.1 h.2.2.2.1)
  have encodedOrder : ((advance g ref (.enter v) tail).stack.map (commandWord a.tags)) =
      row ++ (closing :: pending) :=
    nextStack ▸ (by simp only [row, childrenOf, closing, pending, List.map_append,
      List.map_map, List.map_cons, Function.comp_def])
  have stampAddress : (reg u tinBase).val + (reg u cmd).val = a.tin + v.val := by
    rw [uc.tin_eq, node]
  have tPrefix := su.append ut
  have work : row.length = (g.get v).length := by simp [row, childrenOf]
  change Steps (program hi hw) input (4 + (15 + 8 * row.length)) {s with pc := 1} t at tPrefix
  rw [work, show 4 + (15 + 8 * (g.get v).length) = 19 + 8 * (g.get v).length by omega] at tPrefix
  refine ⟨t, tPrefix, ⟨tpc, tc, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · change (reg t registers.ptr).val = (row ++ (closing :: pending)).length at tPtr
    rw [← List.length_map (f := commandWord a.tags), encodedOrder]
    exact tPtr
  · rw [tClock, uClock, nextClock]
  · rw [encodedOrder]
    exact tStack
  · apply ChildImage.transfer (s := u.data)
      (by simpa only [uData] using atGuard.childRows)
    intro j bound
    apply tFrame
    · rw [stampAddress]
      unfold Arena.tin Arena.offsets at *
      omega
    · right
      change a.base + (row.length + (closing :: pending).length) ≤ j
      unfold Arena.offsets at bound
      omega
  · rw [nextTin, ← uClock]
    apply ColumnAt.put (s := u.data)
      (old := by simpa only [uData] using atGuard.entries)
    · simpa only [stampAddress] using tWrite
    · intro i diff
      apply tFrame
      · rw [stampAddress]
        intro eq
        exact diff (Fin.ext (Nat.add_left_cancel eq))
      · right
        change a.base + (row.length + (closing :: pending).length) ≤ a.tin + i.val
        unfold Arena.tin
        omega
  · rw [nextTout]
    apply ColumnAt.transfer (s := u.data)
      (by simpa only [uData] using atGuard.ends)
    intro i
    apply tFrame
    · rw [stampAddress]
      unfold Arena.tin Arena.tout
      omega
    · right
      change a.base + (row.length + (closing :: pending).length) ≤ a.tout + i.val
      unfold Arena.tout
      omega

  · intro j hj
    rw [tFrame j, uData]
    · rw [stampAddress]
      unfold Arena.tin
      omega
    · left
      change j < a.base + pending.length
      omega

open PaperB.ForestLayout (bucketChildLists exit_pending_run)
open PaperB.RamForestDriverCost (bodyCost potential traversalWork traversalWork_accounting)

private def Reached (g : ChildLists n) (root : Fin n) (ref : Ref) : Prop :=
  ∃ k ≤ 2 * n, ref = PaperB.ForestLayout.layout g root k

private theorem runGuard (input : Input L) {a : Arena bits workCap n}
    {g : ChildLists n} {ref : Ref} {s : State L} (ready : AtGuard a g ref s) :
    step (program hi hw) input s = some (.next
      {s with pc := match ref.stack with | [] => 31 | _ :: _ => 1}) :=
  (PaperB.RamForestDriverCost.guard_step guard_placed
    ⟨_, @pop_placed bits inputCap workCap hi hw 0 _ rfl⟩
    ⟨_, halt_fetch⟩ ready.pc ready.regs.zero ready.ptr).1

/-- The linked program executes from a prepared CSR arena. The bound
includes every instruction through the final guard and halt. The output
columns are in the same arena and the run allocates no extra banks. -/
theorem run_prepared_tree (input : Input L) {a : Arena bits workCap n}
    {g : ChildLists n} {root : Fin n} {parent : Fin n → Fin n} {depth : Fin n → Nat}
    (tree : ValidDepthTree root parent depth) (rows : g = bucketChildLists root parent)
    (mass : a.children ≤ n) (s : State L)
    (ready : AtGuard a g (PaperB.ForestLayout.initial root) s) :
    let final := PaperB.ForestLayout.layout g root (2 * n)
    ∃ (u : State L) (trace : List (State L)) (work : Nat),
      AtGuard a g final u ∧ work ≤ 40 * n + 2 ∧
      run (program hi hw) input work s = some ⟨{u with pc := 31}, work⟩ ∧
      SuccessfulTrace (program hi hw) input s trace ⟨{u with pc := 31}, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      (∀ j < a.base, u.data[j]? = s.data[j]?) := by
  let final := PaperB.ForestLayout.layout g root (2 * n)
  have complete : final.stack = [] ∧ final.processed = 2 * n := by
    dsimp only [final]
    rw [rows]
    exact PaperB.ForestLayout.layout_bucketChildren_exact tree
  let rel (ref : Ref) (u : State L) := AtGuard a g ref u ∧ Reached g root ref ∧
    (∀ j < a.base, u.data[j]? = s.data[j]?)
  have body (ref : Ref) (u : State L) (c : Command n) (tail : List (Command n))
      (r : rel ref u) (active : ref.stack = c :: tail) :
      ∃ t, Steps (program hi hw) input (bodyCost 19 8 8 g c) {u with pc := 1} t ∧
        rel (advance g ref c tail) t := by
    obtain ⟨ready, reached, original⟩ := r
    obtain ⟨k, bound, eq⟩ := reached
    have more : k < 2 * n := by
      by_cases h : k < 2 * n
      · exact h
      · have last : k = 2 * n := by omega
        rw [eq, last, complete.1] at active
        cases active
    have prefixLive := PaperB.ForestLayout.LiveCells.validTree_prefix tree g rows _ mass k bound
    have successor := PaperB.ForestLayout.LiveCells.validTree_prefix tree g rows _ mass
      (k + 1) (by omega)
    have eqNext : advance g ref c tail = PaperB.ForestLayout.layout g root (k + 1) := by
      unfold PaperB.ForestLayout.layout
      rw [PaperB.ForestLayout.LiveCells.run_fuel_add]
      change advance g ref c tail = PaperB.ForestLayout.run g 1 (PaperB.ForestLayout.layout g root k)
      rw [← eq]
      simp only [PaperB.ForestLayout.run, active]
    have nextReached : Reached g root (advance g ref c tail) :=
      ⟨k + 1, by omega, eqNext⟩
    have pending : ref.stack.length ≤ 2 * n := by rw [eq]; exact prefixLive.pending
    cases c with
    | exit v =>
      obtain ⟨t, steps, inv, frame⟩ := after_exit input ready v tail active pending
      exact ⟨t, steps, inv, nextReached, fun j hj => (frame j hj).trans (original j hj)⟩
    | enter v =>
      have clock : ref.enters < 2 * n := by
        have processed : ref.enters + ref.exits = k := by rw [eq]; exact prefixLive.processed
        omega
      obtain ⟨t, steps, inv, frame⟩ := after_enter input ready v tail active pending
        (by rw [eqNext]; exact successor.pending) clock
      exact ⟨t, steps, inv, nextReached, fun j hj => (frame j hj).trans (original j hj)⟩
  obtain ⟨u, trace, inv, execution, success, peak⟩ :=
    PaperB.RamForestDriver.run_driver (program hi hw) input g 19 8 8 1 31 rel
      (fun _ _ r empty => by simpa only [empty] using runGuard input r.1)
      (fun _ _ _ _ r active => by simpa only [active] using runGuard input r.1)
      body halt_fetch (2 * n) (PaperB.ForestLayout.initial root) s
      ⟨ready, ⟨0, Nat.zero_le _, rfl⟩, fun _ _ => rfl⟩ complete.1
  let steps := traversalWork g 19 8 8 (2 * n) (PaperB.ForestLayout.initial root)
  have comp := traversalWork_accounting g 19 8 8 (2 * n) (PaperB.ForestLayout.initial root)
  change steps + 0 = 20 * final.enters + 9 * final.exits + 8 * final.childrenQueued at comp
  have balance : final.exits + final.stack.length = 1 + final.childrenQueued :=
    exit_pending_run g (2 * n) (PaperB.ForestLayout.initial root) rfl
  rw [complete.1, List.length_nil] at balance
  have countEq : final.enters + final.exits = 2 * n := complete.2
  exact ⟨u, trace, steps + 2, inv.1, by omega, execution, success, peak, inv.2.2⟩

end PaperB.RamForestProgram.Finish
