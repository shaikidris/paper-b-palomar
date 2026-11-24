module

public import PaperB.RamForestParentScan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram
open PaperB.RamForestStack (commandWord)
open PaperB.Machine (Word)
open PaperB.ForestLayout (bucketChildLists)

variable {bits n inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- Number of cells still to fill at the front of parent `p`'s row. -/
def vacant (root : Fin n) (parent : Fin n → Fin n) (i : Nat) (p : Fin n) : Nat :=
  parentDegree root parent p.val - (visitedRows root parent i p).length

def rowStart (root : Fin n) (parent : Fin n → Fin n) (p : Fin n) : Nat :=
  rowPrefix (parentDegree root parent) p.val

def OffsetAt (a : Arena bits workCap n) (root : Fin n) (parent : Fin n → Fin n)
    (data : Array (Word bits)) : Prop :=
  ∀ i ≤ n, (data[a.offsets + i]?).map Fin.val = some (rowPrefix (parentDegree root parent) i)

private def seenWords (a : Arena bits workCap n) (root : Fin n)
    (parent : Fin n → Fin n) (i : Nat) (p : Fin n) : List (Word bits) :=
  (visitedRows root parent i p).map (fun v => commandWord a.tags (.enter v))

structure ScatterState (a : Arena bits workCap n) (root : Fin n)
    (parent : Fin n → Fin n) (original : Array (Word bits)) (i : Nat)
    (data : Array (Word bits)) : Prop where
  parents : ParentAt a parent data
  offsets : OffsetAt a root parent data
  counters : ∀ p : Fin n, (data[a.tin + p.val]?).map Fin.val = some (vacant root parent i p)
  suffix : ∀ (p : Fin n) j, j < (seenWords a root parent i p).length →
    data[a.payload + rowStart root parent p + vacant root parent i p + j]? =
      (seenWords a root parent i p)[j]?
  priorOutput : ∀ j < a.base, data[j]? = original[j]?

theorem vacant_step (root : Fin n) (parent : Fin n → Fin n) (u : Fin n)
    (other : u ≠ root) :
    vacant root parent u.val (parent u) = vacant root parent (u.val + 1) (parent u) + 1 := by
  have full : (visitedRows root parent (u.val + 1) (parent u)).length ≤
      parentDegree root parent (parent u).val := by
    simpa only [visitedRows_full, parentDegree_at] using
      (visitedRows_length_mono root parent (parent u) (show u.val + 1 ≤ n from u.isLt) (Nat.le_refl n))
  have next : visitedRows root parent (u.val + 1) (parent u) =
      u :: visitedRows root parent u.val (parent u) := by
    rw [visitedRows_succ]
    exact ite_eq_left ⟨other, rfl⟩
  rw [next, List.length_cons] at full
  simp only [vacant, next, List.length_cons]
  omega

private theorem vacancy_le (root : Fin n) (parent : Fin n → Fin n) (i : Nat)
    (p : Fin n) :
    vacant root parent i p ≤ parentDegree root parent p.val :=
  Nat.sub_le _ _

private theorem total_row (root : Fin n) (parent : Fin n → Fin n) (i : Nat)
    (bound : i ≤ n) (p : Fin n) :
    vacant root parent i p + (visitedRows root parent i p).length =
      parentDegree root parent p.val := by
  have known := visitedRows_length_mono root parent p bound (Nat.le_refl n)
  rw [visitedRows_full] at known
  unfold vacant
  rw [parentDegree_at]
  omega

private theorem end_le (root : Fin n) (parent : Fin n → Fin n) (p : Fin n) :
    rowStart root parent p + parentDegree root parent p.val ≤ rowPrefix (parentDegree root parent) n :=
  rowPrefix_mono _ p.isLt

private theorem rows_separate (root : Fin n) (parent : Fin n → Fin n)
    (p q : Fin n) (other : p ≠ q) :
    rowStart root parent p + parentDegree root parent p.val ≤ rowStart root parent q ∨
      rowStart root parent q + parentDegree root parent q.val ≤ rowStart root parent p := by
  by_cases order : p.val < q.val
  · exact Or.inl (rowPrefix_mono _ order)
  · have distinct : p.val ≠ q.val := fun e => other (Fin.ext e)
    exact Or.inr (rowPrefix_mono _ (show q.val < p.val by omega))

private theorem scatter_skip {a : Arena bits workCap n} {root : Fin n}
    {parent : Fin n → Fin n} {original data : Array (Word bits)}
    (h : ScatterState a root parent original root.val data) :
    ScatterState a root parent original (root.val + 1) data := by
  have same (p : Fin n) : visitedRows root parent (root.val + 1) p =
      visitedRows root parent root.val p := by rw [visitedRows_succ]; simp
  refine ⟨h.parents, h.offsets, ?_, ?_, h.priorOutput⟩
  · intro p
    simpa only [vacant, same] using h.counters p
  · intro p j hj
    simp only [seenWords, same] at hj
    simpa only [vacant, seenWords, same] using h.suffix p j hj

private theorem scatter_put {a : Arena bits workCap n} {root : Fin n}
    {parent : Fin n → Fin n} {original data next : Array (Word bits)}
    (u : Fin n) (other : u ≠ root)
    (h : ScatterState a root parent original u.val data)
    (counter : (next[a.tin + (parent u).val]?).map Fin.val =
      some (vacant root parent (u.val + 1) (parent u)))
    (write : next[a.payload + rowStart root parent (parent u) +
      vacant root parent (u.val + 1) (parent u)]? = some (commandWord a.tags (.enter u)))
    (keep : ∀ j, j ≠ a.tin + (parent u).val →
      j ≠ a.payload + rowStart root parent (parent u) + vacant root parent (u.val + 1) (parent u) →
      next[j]? = data[j]?) :
    ScatterState a root parent original (u.val + 1) next := by
  let p := parent u
  let qStart := rowStart root parent p
  let qFree := vacant root parent (u.val + 1) p
  have room := (parent u).isLt
  have oldFree : vacant root parent u.val p = qFree + 1 := vacant_step root parent u other
  have headRoom : qFree < parentDegree root parent p.val := by
    have upper := vacancy_le root parent u.val p
    omega
  have visitSame (q : Fin n) (distinct : q ≠ p) :
      visitedRows root parent (u.val + 1) q = visitedRows root parent u.val q := by
    rw [visitedRows_succ]
    exact ite_eq_right (fun h => distinct h.2)
  have visitNew : visitedRows root parent (u.val + 1) p =
      u :: visitedRows root parent u.val p := by
    rw [visitedRows_succ]
    exact ite_eq_left ⟨other, rfl⟩
  have notDegree {i : Nat} (h : a.offsets ≤ i) : i ≠ a.tin + p.val := by
    unfold Arena.offsets Arena.tin at *
    omega
  have offsetsBefore : a.offsets + n < a.payload := by
    unfold Arena.offsets Arena.payload
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q
    have nq := q.isLt
    rw [keep _ (by unfold Arena.tin; omega) (by unfold Arena.payload; omega)]
    exact h.parents q
  · intro j hj
    rw [keep _ (notDegree (by omega)) (by omega)]
    exact h.offsets j hj
  · intro q
    by_cases e : q = p
    · subst q; exact counter
    · rw [keep _ (fun eq => e (Fin.ext (Nat.add_left_cancel eq)))
        (by unfold Arena.tin Arena.payload; have := q.isLt; omega)]
      simpa only [vacant, visitSame q e] using h.counters q
  · intro q j hj
    by_cases e : q = p
    · subst q
      have extended : seenWords a root parent (u.val + 1) p =
          commandWord a.tags (.enter u) :: seenWords a root parent u.val p := by
        rw [seenWords, visitNew, List.map_cons]
        rfl
      rw [extended] at hj ⊢
      cases j with
      | zero =>
        simpa only [Nat.add_zero, List.getElem?_cons_zero] using write
      | succ j =>
        simp only [List.length_cons, List.getElem?_cons_succ] at hj ⊢
        have addr : a.payload + qStart + qFree + (j + 1) =
            a.payload + qStart + vacant root parent u.val p + j := by omega
        change next[a.payload + qStart + qFree + (j + 1)]? = _
        rw [addr, keep _ (by unfold Arena.tin Arena.payload; omega) (by
          change a.payload + qStart + vacant root parent u.val p + j ≠
            a.payload + qStart + qFree
          omega)]
        exact h.suffix p j (by omega)
    · have freeSame : vacant root parent (u.val + 1) q = vacant root parent u.val q := by
        simp only [vacant, visitSame q e]
      have wordsSame : seenWords a root parent (u.val + 1) q =
          seenWords a root parent u.val q := by simp only [seenWords, visitSame q e]
      rw [wordsSame] at hj
      rw [freeSame, wordsSame]
      have length : (seenWords a root parent u.val q).length =
          (visitedRows root parent u.val q).length := List.length_map _
      have qBound := total_row root parent u.val (Nat.le_of_lt u.isLt) q
      have disjoint := rows_separate root parent q p e
      rw [keep _ (by unfold Arena.tin Arena.payload; omega)
        (by
          change a.payload + rowStart root parent q + vacant root parent u.val q + j ≠
            a.payload + qStart + qFree
          rcases disjoint with left | right <;> dsimp only [qStart] <;> omega)]
      exact h.suffix q j hj
  · intro j hj
    exact (keep j (by unfold Arena.tin; omega) (by unfold Arena.payload; omega)).trans
      (h.priorOutput j hj)

/-- The executed scatter loop may reuse the degree bank as cursors. Its
last state has every row written, including rows with no children. -/
theorem scatter_childImage {a : Arena bits workCap n} {root : Fin n}
    {parent : Fin n → Fin n} {original data : Array (Word bits)}
    (h : ScatterState a root parent original n data)
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) :
    ChildImage a (bucketChildLists root parent) data := by
  refine childImage_of_offsets _ data (parentDegree_at root parent) mass h.offsets ?_
  intro v j hj
  have full : seenWords a root parent n v = childrenOf a (bucketChildLists root parent) v := by
    simp only [seenWords, visitedRows_full, childrenOf]
  have empty : vacant root parent n v = 0 := by
    simp only [vacant, parentDegree_at, visitedRows_full, Nat.sub_self]
  have read := h.suffix v j (by rwa [full])
  simpa only [full, empty, Nat.add_zero, rowStart] using read

/-- Place one nonroot vertex. The remaining count is decreased before
adding its row offset, so successive writes run from right to left. -/
def scatterBody : List (Instr bits 15) :=
  indexedDataRead registers.remain registers.stackBase registers.ptr ++
  indexedDataRead registers.value tinBase registers.remain ++
  [.sub registers.value registers.value registers.one] ++
  indexedDataWrite registers.tmp tinBase registers.remain registers.value ++
  indexedDataRead clk offsetBase registers.remain ++
  [.add clk clk registers.value] ++
  indexedDataWrite registers.tmp childrenBase clk registers.ptr

private theorem placePair {code : Program L} {entry : Nat} {first last : Instr bits 15}
    (h₀ : code[entry]? = some first) (h₁ : code[entry + 1]? = some last) :
    Placed code entry [first, last] := by
  intro i op h
  cases i with
  | zero =>
    rw [Nat.add_zero]
    exact h₀.trans h
  | succ i =>
    cases i with
    | zero => exact h₁.trans h
    | succ i => simp at h

private theorem keepCursor {a : Arena bits workCap n} {root : Fin n} {i : Nat}
    {s t : State L} (d : Fin 15) (temporary : d ∈ parentScratch)
    (h : ParentCursor a root i s) (frame : ∀ r : Fin 15, r ≠ d → reg t r = reg s r) :
    ParentCursor a root i t :=
  h.unchanged (fun r hr => frame r (fun eq => hr (eq ▸ temporary)))

private theorem scatter_body (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n} {original : Array (Word bits)}
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) :
    ParentBodySpec input scatterBody a root (ScatterState a root parent original) := by
  intro u nonroot s pc cursor old
  let code : Program L := parentScanCode (scatterBody (bits := bits))
  have placed : Placed code 4 (scatterBody (bits := bits)) := parentBody_placed _
  have size : code.size = 19 := parentScan_size scatterBody
  have room := a.room
  have width := a.wordFits
  have ul := u.isLt
  have pl := (parent u).isLt
  let start := rowStart root parent (parent u)
  let left := vacant root parent (u.val + 1) (parent u)
  have free : vacant root parent u.val (parent u) = left + 1 :=
    vacant_step root parent u nonroot
  have rowRoom : start + left < a.children := by
    have len := vacancy_le root parent u.val (parent u)
    have endpoint := end_le root parent (parent u)
    change start + parentDegree root parent (parent u).val ≤ _ at endpoint
    omega
  have read0 : Placed code 4 (indexedDataRead registers.remain registers.stackBase registers.ptr) :=
    placePair (placed 0 _ rfl) (placed 1 _ rfl)
  have bound0 : (reg s registers.stackBase).val + (reg s registers.ptr).val < workCap := by
    rw [cursor.ctrl.stackBase_eq, cursor.ptrVal]; omega
  obtain ⟨v, sv, vpc, pvRead, vr, vm⟩ :=
    indexedDataRead_steps (input := input) (s := s) read0 pc (by omega) bound0
  have pVal : (reg v registers.remain).val = (parent u).val := by
    rw [cursor.ctrl.stackBase_eq, cursor.ptrVal] at pvRead
    have vv := congrArg (Option.map Fin.val) pvRead
    rw [old.parents u] at vv
    exact Option.some.inj vv
  have vc := keepCursor registers.remain (by decide +revert) cursor vr
  have read1 : Placed code 6 (indexedDataRead registers.value tinBase registers.remain) :=
    placePair (placed 2 _ rfl) (placed 3 _ rfl)
  have bound1 : (reg v tinBase).val + (reg v registers.remain).val < workCap := by
    rw [vc.ctrl.tin_eq, pVal]; unfold Arena.tin; omega
  obtain ⟨w, vw, wpc, wRead, wr, wm⟩ :=
    indexedDataRead_steps (input := input) read1 vpc (by omega) bound1
  have wc := keepCursor registers.value (by decide +revert) vc wr
  have wValue : (reg w registers.value).val = left + 1 := by
    rw [vc.ctrl.tin_eq, pVal, vm] at wRead
    have vv := congrArg (Option.map Fin.val) wRead
    rw [old.counters (parent u), free] at vv
    exact Option.some.inj vv
  have dec : code[w.pc]? = some (.sub registers.value registers.value registers.one) := by
    rw [wpc]; exact placed 4 _ rfl
  obtain ⟨x, wx, xpc, xValue, xr, xm⟩ := step_sub_at (input := input) dec (by omega)
  have xc := keepCursor registers.value (by decide +revert) wc xr
  have xLeft : (reg x registers.value).val = left := by
    rw [xValue, PaperB.WordOps.sub_val, wValue, wc.ctrl.one]
    rw [show 2 ^ bits + (left + 1) - 1 = 2 ^ bits + left by omega,
      Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have xParent : (reg x registers.remain).val = (parent u).val := by
    rw [xr _ (show registers.remain ≠ registers.value by decide),
      wr _ (show registers.remain ≠ registers.value by decide), pVal]
  have put0 : Placed code 9 (indexedDataWrite registers.tmp tinBase registers.remain registers.value) :=
    placePair (placed 5 _ rfl) (placed 6 _ rfl)
  have bound2 : (reg x tinBase).val + (reg x registers.remain).val < workCap := by
    rw [xc.ctrl.tin_eq, xParent]; unfold Arena.tin; omega
  obtain ⟨y, xy, ypc, yMem, _, yr⟩ := indexedDataWrite_steps (input := input)
    (s := x) put0 (by omega) (by omega) (show registers.value ≠ registers.tmp by decide) bound2
  have yc := keepCursor registers.tmp (by decide +revert) xc yr
  have yParent : (reg y registers.remain).val = (parent u).val := by
    rw [yr _ (show registers.remain ≠ registers.tmp by decide), xParent]
  have degreeWrite : y.data = s.data.set (a.tin + (parent u).val) (reg x registers.value)
      (by rw [s.data_size]; change a.tin + (parent u).val < workCap
          unfold Arena.tin; omega) := by
    simpa only [xc.ctrl.tin_eq, xParent, xm, wm, vm] using yMem
  have degreeFrame (j : Nat) (hne : j ≠ a.tin + (parent u).val) :
      y.data[j]? = s.data[j]? := by
    rw [degreeWrite]
    exact Array.getElem?_set_ne _ hne.symm
  have read2 : Placed code 11 (indexedDataRead clk offsetBase registers.remain) :=
    placePair (placed 7 _ rfl) (placed 8 _ rfl)
  have bound3 : (reg y offsetBase).val + (reg y registers.remain).val < workCap := by
    rw [yc.ctrl.offset_eq, yParent]; unfold Arena.offsets; omega
  obtain ⟨z, yz, zpc, zRead, zr, zm⟩ := indexedDataRead_steps (input := input)
    (s := y) read2 ypc (by omega) bound3
  have zc := keepCursor clk (by decide +revert) yc zr
  have zOffset : (reg z clk).val = start := by
    rw [yc.ctrl.offset_eq, yParent, degreeFrame _ (by unfold Arena.tin Arena.offsets; omega)] at zRead
    have vv := congrArg (Option.map Fin.val) zRead
    rw [old.offsets (parent u).val (by omega)] at vv
    exact Option.some.inj vv
  have zLeft : (reg z registers.value).val = left := by
    rw [zr _ (show registers.value ≠ clk by decide),
      yr _ (show registers.value ≠ registers.tmp by decide), xLeft]
  have add : code[z.pc]? = some (.add clk clk registers.value) := by
    rw [zpc]; exact placed 9 _ rfl
  obtain ⟨b, zb, bpc, bVal, br, bm⟩ := step_add_at (input := input) add (by omega)
  have bc := keepCursor clk (by decide +revert) zc br
  have sumFits : (reg z clk).val + (reg z registers.value).val < 2 ^ bits := by
    rw [zOffset, zLeft]; omega
  have index : (reg b clk).val = start + left := by
    rw [bVal, PaperB.WordOps.add_no_wrap _ _ sumFits, zOffset, zLeft]
  have put1 : Placed code 14 (indexedDataWrite registers.tmp childrenBase clk registers.ptr) :=
    placePair (placed 10 _ rfl) (placed 11 _ rfl)
  have bound4 : (reg b childrenBase).val + (reg b clk).val < workCap := by
    rw [bc.ctrl.child_eq, index]; unfold Arena.payload; omega
  obtain ⟨t, bt, tpc, tm, _, tr⟩ := indexedDataWrite_steps (input := input)
    (s := b) put1 (by omega) (by omega) (show registers.ptr ≠ registers.tmp by decide) bound4
  have tc := keepCursor registers.tmp (by decide +revert) bc tr
  have coded : reg b registers.ptr = commandWord a.tags (.enter u) := by
    apply Fin.ext
    exact bc.ptrVal
  have payloadWrite : t.data = y.data.set (a.payload + start + left)
      (commandWord a.tags (.enter u))
      (by rw [y.data_size]; change a.payload + start + left < workCap
          unfold Arena.payload; omega) := by
    simpa only [bc.ctrl.child_eq, index, coded, bm, zm, Nat.add_assoc] using tm
  have payloadFrame (j : Nat) (hne : j ≠ a.payload + start + left) : t.data[j]? = y.data[j]? := by
    rw [payloadWrite]
    exact Array.getElem?_set_ne _ hne.symm
  refine ⟨t, sv.append (vw.append (.cons wx (xy.append (yz.append (.cons zb bt))))),
    tpc, tc, scatter_put u nonroot old ?_ ?_ ?_⟩
  · have separate : a.tin + (parent u).val ≠ a.payload + start + left := by
      unfold Arena.tin Arena.payload
      omega
    rw [payloadFrame _ separate, degreeWrite, Array.getElem?_set_self, Option.map_some, xLeft]
  · change t.data[a.payload + start + left]? = _
    rw [payloadWrite, Array.getElem?_set_self]
  · intro j h₀ h₁
    exact (payloadFrame j h₁).trans (degreeFrame j h₀)

/-- Runs scatter on the parent words, exact offsets and degree counters.
The cursor bank may be overwritten. The parent, offset and earlier output
banks survive, and the resulting rows have precisely the DFS order. -/
theorem run_parent_scatter (input : Input L) {a : Arena bits workCap n}
    (root : Fin n) (parent : Fin n → Fin n) (s : State L)
    (pc : s.pc = 0) (cursor : ParentCursor a root 0 s)
    (par : ParentAt a parent s.data) (offsets : OffsetAt a root parent s.data)
    (counters : ∀ p : Fin n, (s.data[a.tin + p.val]?).map Fin.val =
      some (parentDegree root parent p.val))
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) :
    ∃ t trace work, work ≤ 17 * n + 2 ∧
      run (parentScanCode (scatterBody (bits := bits))) input work s = some ⟨t, work⟩ ∧
      ParentCursor a root n t ∧ ChildImage a (bucketChildLists root parent) t.data ∧
      (∀ j < a.base, t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (parentScanCode (scatterBody (bits := bits))) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have start : ScatterState a root parent s.data 0 s.data := by
    refine ⟨par, offsets, ?_, ?_, fun _ _ => rfl⟩
    · simpa only [vacant, visitedRows_zero, List.length_nil, Nat.sub_zero] using counters
    · intro q j tooLarge
      simp [seenWords] at tooLarge
  obtain ⟨t, trace, work, bound, execute, endRegs, final, success, peak⟩ :=
    run_parent_scan input scatterBody (scatter_body input mass)
      (fun _ c => scatter_skip c) s pc cursor start
  exact ⟨t, trace, work, bound, execute, endRegs, scatter_childImage final mass, final.priorOutput,
    success, peak⟩

end PaperB.RamForestProgram.Finish
