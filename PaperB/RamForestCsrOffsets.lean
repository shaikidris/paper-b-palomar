module

public import PaperB.RamForestFinish

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram
open PaperB.WordOps (ltb)
open PaperB.Machine (Word)

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- Prefix totals of the row degrees. The natural index includes the
terminal word at index `n`. -/
def rowPrefix (degree : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => rowPrefix degree k + degree k

theorem rowPrefix_mono (degree : Nat → Nat) {i j : Nat} (h : i ≤ j) :
    rowPrefix degree i ≤ rowPrefix degree j := by
  induction j with
  | zero =>
    have eq : i = 0 := by omega
    rw [eq]
    exact Nat.le_refl _
  | succ j ih =>
    by_cases e : i = j + 1
    · rw [e]
      exact Nat.le_refl _
    · have before := ih (by omega)
      simp only [rowPrefix]
      omega

private def getDegree : List (Instr bits 15) :=
  indexedDataRead registers.value tinBase registers.ptr

private def putOffset : List (Instr bits 15) :=
  indexedDataWrite registers.tmp offsetBase registers.ptr clk

/-- Eight instructions per row, one final guard, two instructions for
the terminal offset, and the halt. -/
def offsetProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  let branch : Instr bits 15 := .branchLt registers.ptr count 1 8
  let back : List (Instr bits 15) :=
    [.add clk clk registers.value, .add registers.ptr registers.ptr registers.one, .goto 0]
  ([branch] ++ getDegree ++ putOffset ++ back ++ putOffset ++ [Instr.halt]).toArray

structure OffsetInput (a : Arena bits workCap n) (degree : Nat → Nat)
    (s : State L) : Prop where
  pc : s.pc = 0
  cursor : (reg s registers.ptr).val = 0
  acc : (reg s clk).val = 0
  regs : Control a s
  degrees : ∀ j < n, (s.data[a.tin + j]?).map Fin.val = some (degree j)
  sum : rowPrefix degree n ≤ a.children

private structure OffsetLoop (a : Arena bits workCap n) (degree : Nat → Nat)
    (origin : State L) (i : Nat) (s : State L) : Prop where
  pc : s.pc = 0
  cursor : (reg s registers.ptr).val = i
  acc : (reg s clk).val = rowPrefix degree i
  regs : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ clk → r ≠ registers.value →
    r ≠ registers.tmp → reg s r = reg origin r
  written : ∀ j < i, (s.data[a.offsets + j]?).map Fin.val = some (rowPrefix degree j)
  frame : ∀ j, (j < a.offsets ∨ a.offsets + i ≤ j) → s.data[j]? = origin.data[j]?

private theorem readPlaced : Placed (offsetProgram hi hw) 1 (getDegree (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [getDegree, indexedDataRead] at h

private theorem putPlaced :
    Placed (offsetProgram hi hw) 3 (putOffset (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [putOffset, indexedDataWrite] at h

private theorem lastPlaced :
    Placed (offsetProgram hi hw) 8 (putOffset (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [putOffset, indexedDataWrite] at h

private theorem offset_iteration (input : Input L) {a : Arena bits workCap n}
    {degree : Nat → Nat} {orig : State L} (initial : OffsetInput a degree orig)
    {i : Nat} (below : i < n) :
    BlockSpec (offsetProgram hi hw) input 8 (OffsetLoop a degree orig i)
      (OffsetLoop a degree orig (i + 1)) := by
  intro s h
  have width := a.wordFits
  have room := a.room
  have hcount := (congrArg Fin.val (h.regs count (by decide +revert) (by decide +revert)
    (by decide +revert) (by decide +revert))).trans initial.regs.count_eq
  have tins := (congrArg Fin.val (h.regs tinBase (by decide +revert) (by decide +revert)
    (by decide +revert) (by decide +revert))).trans initial.regs.tin_eq
  have offsets := (congrArg Fin.val (h.regs offsetBase (by decide +revert) (by decide +revert)
    (by decide +revert) (by decide +revert))).trans initial.regs.offset_eq
  have cmp : ltb (reg s registers.ptr) (reg s count) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [h.cursor, hcount]; exact below)
  let u : State L := {s with pc := 1}
  have guard : (offsetProgram hi hw)[s.pc]? = some (.branchLt registers.ptr count 1 8) := by
    rw [h.pc]; rfl
  have su : step (offsetProgram hi hw) input s = some (.next u) := by
    simpa only [u, cmp, ite_true] using
      step_branchLt_at (input := input) guard (by rw [cmp]; exact (show 1 < 11 by decide))
  have loadBound : (reg u tinBase).val + (reg u registers.ptr).val < workCap := by
    change (reg s tinBase).val + (reg s registers.ptr).val < workCap
    rw [tins, h.cursor]
    unfold Arena.tin
    omega
  obtain ⟨v, uv, vpc, read, vregs, vmem⟩ := indexedDataRead_steps
    (input := input) (s := u) readPlaced rfl (show 3 < 11 by decide) loadBound
  have vVal : (reg v registers.value).val = degree i := by
    change some (reg v registers.value) =
      s.data[(reg s tinBase).val + (reg s registers.ptr).val]? at read
    rw [tins, h.cursor, h.frame _ (Or.inl (by unfold Arena.tin Arena.offsets; omega))] at read
    have val := congrArg (Option.map Fin.val) read
    rw [initial.degrees i below] at val
    exact Option.some.inj val
  have storeBound : (reg v offsetBase).val + (reg v registers.ptr).val < workCap := by
    rw [vregs offsetBase (show offsetBase ≠ registers.value by decide),
      vregs registers.ptr (show registers.ptr ≠ registers.value by decide)]
    change (reg s offsetBase).val + (reg s registers.ptr).val < workCap
    rw [offsets, h.cursor]
    unfold Arena.offsets
    omega
  obtain ⟨w, vw, wpc, wmem, _, wregs⟩ := indexedDataWrite_steps (input := input)
    (s := v) putPlaced vpc (show 5 < 11 by decide) (show clk ≠ registers.tmp by decide)
    storeBound
  have common (r : Fin 15) (tmp : r ≠ registers.tmp) (value : r ≠ registers.value) :
      reg w r = reg s r := (wregs r tmp).trans (vregs r value)
  have wValue : (reg w registers.value).val = degree i :=
    (congrArg Fin.val (wregs _ (show registers.value ≠ registers.tmp by decide))).trans vVal
  have wAcc : (reg w clk).val = rowPrefix degree i :=
    (congrArg Fin.val (common clk (by decide +revert) (by decide +revert))).trans h.acc
  have nextTotal := Nat.le_trans (rowPrefix_mono degree (show i + 1 ≤ n by omega)) initial.sum
  have addSafe : (reg w clk).val + (reg w registers.value).val < 2 ^ bits := by
    rw [wAcc, wValue]
    change rowPrefix degree (i + 1) < 2 ^ bits
    omega
  have accFetch : (offsetProgram hi hw)[w.pc]? = some (.add clk clk registers.value) := by
    rw [wpc]; rfl
  obtain ⟨x, wx, xpc, xval, xregs, xmem⟩ := step_add_at (input := input) accFetch
    (by rw [wpc]; exact (show 6 < 11 by decide))
  have ptrFetch : (offsetProgram hi hw)[x.pc]? =
      some (.add registers.ptr registers.ptr registers.one) := by
    rw [xpc, wpc]; rfl
  obtain ⟨y, xy, ypc, yval, yregs, ymem⟩ := step_add_at (input := input) ptrFetch
    (by rw [xpc, wpc]; exact (show 7 < 11 by decide))
  have xPtr : (reg x registers.ptr).val = i :=
    (congrArg Fin.val ((xregs _ (show registers.ptr ≠ clk by decide)).trans
      (common _ (show registers.ptr ≠ registers.tmp by decide)
        (show registers.ptr ≠ registers.value by decide)))).trans h.cursor
  have xOne : (reg x registers.one).val = 1 :=
    (congrArg Fin.val ((xregs _ (show registers.one ≠ clk by decide)).trans
      ((common _ (show registers.one ≠ registers.tmp by decide)
        (show registers.one ≠ registers.value by decide)).trans
        (h.regs _ (show registers.one ≠ registers.ptr by decide)
          (show registers.one ≠ clk by decide) (show registers.one ≠ registers.value by decide)
          (show registers.one ≠ registers.tmp by decide))))).trans initial.regs.one
  have incFits : (reg x registers.ptr).val + (reg x registers.one).val < 2 ^ bits := by
    rw [xPtr, xOne]; omega
  have back : (offsetProgram hi hw)[y.pc]? = some (.goto 0) := by
    rw [ypc, xpc, wpc]; rfl
  let t : State L := {y with pc := 0}
  have yt : step (offsetProgram hi hw) input y = some (.next t) :=
    step_goto_at back (show 0 < 11 by decide)
  have address : (reg v offsetBase).val + (reg v registers.ptr).val = a.offsets + i := by
    rw [vregs offsetBase (show offsetBase ≠ registers.value by decide),
      vregs registers.ptr (show registers.ptr ≠ registers.value by decide)]
    change (reg s offsetBase).val + (reg s registers.ptr).val = _
    rw [offsets, h.cursor]
  have oldAcc : (reg v clk).val = rowPrefix degree i := by
    have eq := vregs clk (show clk ≠ registers.value by decide)
    change reg v clk = reg s clk at eq
    rw [eq, h.acc]
  have mem : t.data = s.data.set (a.offsets + i) (reg v clk)
      (by rw [s.data_size]; change a.offsets + i < workCap; unfold Arena.offsets; omega) := by
    change y.data = _
    rw [ymem, xmem]
    simpa only [address, vmem] using wmem
  have unchanged (j : Nat) (ne : j ≠ a.offsets + i) : t.data[j]? = s.data[j]? := by
    rw [mem]
    exact Array.getElem?_set_ne _ ne.symm
  refine ⟨t, (Steps.cons su uv).append
    (vw.append (.cons wx (.cons xy (.cons yt (.zero t))))), rfl, ?_, ?_, ?_, ?_, ?_⟩
  · change (reg y registers.ptr).val = _
    rw [yval, PaperB.WordOps.add_no_wrap _ _ incFits, xPtr, xOne]
  · change (reg y clk).val = _
    rw [yregs clk (show clk ≠ registers.ptr by decide), xval,
      PaperB.WordOps.add_no_wrap _ _ addSafe, wAcc, wValue]
    rfl
  · intro r hp hc hv ht
    exact (yregs r hp).trans ((xregs r hc).trans ((common r ht hv).trans (h.regs r hp hc hv ht)))
  · intro j hj
    by_cases here : j = i
    · subst j
      rw [mem, Array.getElem?_set_self, Option.map_some, oldAcc]
    · rw [unchanged _ (by omega), h.written j (by omega)]
  · intro j hj
    rw [unchanged _ (by omega), h.frame j (by omega)]

private theorem eight_iterations (k : Nat) : iterationCost (fun _ => 8) k = 8 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterationCost, ih, Nat.mul_succ]

/-- From the physical degree bank, write offsets 0 through n inclusive.
The input, scratch arena and registers all remain charged through the run. -/
theorem run_csr_offsets_with_frame (input : Input L) {a : Arena bits workCap n}
    {degree : Nat → Nat} (s : State L) (ready : OffsetInput a degree s) :
    ∃ t trace,
      run (offsetProgram hi hw) input (8 * n + 4) s = some ⟨t, 8 * n + 4⟩ ∧
      (∀ j ≤ n, (t.data[a.offsets + j]?).map Fin.val = some (rowPrefix degree j)) ∧
      (∀ j, (j < a.offsets ∨ a.offsets + n + 1 ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (offsetProgram hi hw) input s trace ⟨t, 8 * n + 4⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      (∀ r : Fin 15, r ≠ registers.ptr → r ≠ clk → r ≠ registers.value →
        r ≠ registers.tmp → reg t r = reg s r) ∧
      (reg t registers.ptr).val = n := by
  have start : OffsetLoop a degree s 0 s :=
    ⟨ready.pc, ready.cursor, ready.acc, fun _ _ _ _ _ => rfl,
      fun _ h => False.elim (Nat.not_lt_zero _ h), fun _ _ => rfl⟩
  obtain ⟨v, iter, h⟩ := loop_steps (code := offsetProgram hi hw) (input := input)
    n (fun _ => 8) (OffsetLoop a degree s)
    (fun _ hi => offset_iteration input ready hi) s start
  rw [eight_iterations] at iter
  have countEq : (reg v count).val = n :=
    (congrArg Fin.val (h.regs count (by decide +revert) (by decide +revert)
      (by decide +revert) (by decide +revert))).trans ready.regs.count_eq
  have compare : ltb (reg v registers.ptr) (reg v count) = false := by
    cases hx : ltb (reg v registers.ptr) (reg v count) with
    | false => rfl
    | true =>
      have lt := (PaperB.WordOps.ltb_eq_true _ _).mp hx
      rw [h.cursor, countEq] at lt
      exact False.elim (Nat.lt_irrefl _ lt)
  have guard : (offsetProgram hi hw)[v.pc]? = some (.branchLt registers.ptr count 1 8) := by
    rw [h.pc]; rfl
  let w : State L := {v with pc := 8}
  have jump : step (offsetProgram hi hw) input v = some (.next w) := by
    simpa only [w, compare, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) guard (by rw [compare]; exact (show 8 < 11 by decide))
  have offsetEq : (reg v offsetBase).val = a.offsets :=
    (congrArg Fin.val (h.regs offsetBase (by decide +revert) (by decide +revert)
      (by decide +revert) (by decide +revert))).trans ready.regs.offset_eq
  have room := a.room
  have address : (reg w offsetBase).val + (reg w registers.ptr).val = a.offsets + n := by
    change (reg v offsetBase).val + (reg v registers.ptr).val = _
    rw [offsetEq, h.cursor]
  have fit : a.offsets + n < workCap := by unfold Arena.offsets; omega
  have bound : (reg w offsetBase).val + (reg w registers.ptr).val < workCap := by
    rw [address]; exact fit
  obtain ⟨t, wt, tpc, tmem, _, tRegs⟩ := indexedDataWrite_steps (input := input) (s := w)
    lastPlaced rfl (show 10 < 11 by decide) (show clk ≠ registers.tmp by decide) bound
  have written : t.data = v.data.set (a.offsets + n) (reg v clk)
      (by rw [v.data_size]; exact fit) := by
    have sameAcc : reg w clk = reg v clk := rfl
    have sameData : w.data = v.data := rfl
    simpa only [address, sameAcc, sameData] using tmem
  have untouched (j : Nat) (ne : j ≠ a.offsets + n) : t.data[j]? = v.data[j]? := by
    rw [written]
    exact Array.getElem?_set_ne _ ne.symm
  have halt : step (offsetProgram hi hw) input t = some (.halted t) :=
    step_halt_at (by rw [tpc]; rfl)
  have successful := (iter.append (.cons jump wt)).halts halt
  obtain ⟨trace, replay⟩ := run_has_successfulTrace successful
  refine ⟨t, trace, successful, ?_, ?_, replay, replay.peak_eq, ?_, ?_⟩
  · intro j hj
    by_cases last : j = n
    · subst j; rw [written, Array.getElem?_set_self, Option.map_some, h.acc]
    · rw [untouched _ (by omega), h.written j (by omega)]
  · intro j hj
    rw [untouched _ (by omega), h.frame j (by omega)]
  · intro r hp hc hv ht
    exact (tRegs r ht).trans (h.regs r hp hc hv ht)
  · rw [tRegs registers.ptr (show registers.ptr ≠ registers.tmp by decide)]
    exact h.cursor

/-- Prefix-scan functional correctness and fixed-arena work and space. -/
theorem run_csr_offsets (input : Input L) {a : Arena bits workCap n}
    {degree : Nat → Nat} (s : State L) (ready : OffsetInput a degree s) :
    ∃ t trace,
      run (offsetProgram hi hw) input (8 * n + 4) s = some ⟨t, 8 * n + 4⟩ ∧
      (∀ j ≤ n, (t.data[a.offsets + j]?).map Fin.val = some (rowPrefix degree j)) ∧
      (∀ j, (j < a.offsets ∨ a.offsets + n + 1 ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (offsetProgram hi hw) input s trace ⟨t, 8 * n + 4⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨t, trace, run, offsets, frame, checked, peak, _, _⟩ :=
    run_csr_offsets_with_frame input s ready
  exact ⟨t, trace, run, offsets, frame, checked, peak⟩

private theorem some_word_at {value : Nat} {cell : Option (Word bits)}
    (h : cell.map Fin.val = some value) : ∃ w, cell = some w ∧ w.val = value := by
  cases cell with
  | none => cases h
  | some w => exact ⟨w, rfl, Option.some.inj h⟩

/-- The offset and payload producers meet the DFS input contract at these
precise addresses. Both ends of each row come from the same prefix table. -/
theorem childImage_of_offsets {a : Arena bits workCap n}
    {g : PaperB.ForestLayout.ChildLists n} (degree : Nat → Nat)
    (data : Array (Word bits))
    (degrees : ∀ v : Fin n, degree v.val = (g.get v).length)
    (mass : rowPrefix degree n ≤ a.children)
    (offsets : ∀ j ≤ n, (data[a.offsets + j]?).map Fin.val = some (rowPrefix degree j))
    (payload : ∀ (v : Fin n) j, j < (childrenOf a g v).length →
      data[a.payload + rowPrefix degree v.val + j]? = (childrenOf a g v)[j]?) :
    ChildImage a g data := by
  intro v
  have isLt := v.isLt
  obtain ⟨lo, loRead, loVal⟩ := some_word_at (offsets v.val (by omega))
  obtain ⟨stop, stopRead, stopVal⟩ := some_word_at (offsets (v.val + 1) (by omega))
  have bound := rowPrefix_mono degree (show v.val + 1 ≤ n by omega)
  refine ⟨lo, stop, loRead, ?_, ?_, ?_, ?_⟩
  · rw [Nat.add_assoc]
    exact stopRead
  · rw [loVal, stopVal, rowPrefix, degrees v]
    simp only [childrenOf, List.length_map]
  · rw [stopVal]
    exact Nat.le_trans bound mass
  · intro j hj
    rw [loVal]
    exact payload v j hj

end PaperB.RamForestProgram.Finish
