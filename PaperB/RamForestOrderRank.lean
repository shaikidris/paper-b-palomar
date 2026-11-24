module

public import PaperB.RamForestProgram
public import PaperB.ForestOrderRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.OrderRank

open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.WordOps (ltb)
open PaperB.LabelledQuotient
open PaperB.ForestHead (Vertex)

variable {bits inputCap workCap n : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def readOrder : List (Instr bits 15) :=
  indexedInputRead registers.value offsetBase registers.ptr

private def putRank : List (Instr bits 15) :=
  indexedDataWrite registers.tmp childrenBase registers.value registers.ptr

/-- Seven instructions per vertex. Read its identifier from the order
bank and scatter the current cursor to its inverse-rank slot. -/
def code (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  let guard : Instr bits 15 := .branchLt registers.ptr count 1 7
  let tail : List (Instr bits 15) :=
    [.add registers.ptr registers.ptr registers.one, .goto 0, .halt]
  ([guard] ++ (readOrder ++ (putRank ++ tail))).toArray

/-- The order begins at an input address; output is a dense work bank.
The two banks are in different machine address spaces. -/
structure Banks (bits inputCap workCap n : Nat) where
  order : Nat
  ranks : Nat
  orderFits : order + n ≤ inputCap
  ranksFit : ranks + n ≤ workCap
  cursorFits : n < 2 ^ bits

def InputOrder (input : Input L) (b : Banks bits inputCap workCap n)
    (order : Fin n → Fin n) : Prop :=
  ∀ i : Fin n, (input.words[b.order + i.val]?).map Fin.val = some (order i).val

structure Parameters (b : Banks bits inputCap workCap n) (s : State L) : Prop where
  countVal : (reg s count).val = n
  unitVal : (reg s registers.one).val = 1
  orderBase : (reg s offsetBase).val = b.order
  rankBase : (reg s childrenBase).val = b.ranks

private theorem Parameters.keep {b : Banks bits inputCap workCap n} {s t : State L}
    (h : Parameters b s) (same : ∀ r : Fin 15, r ≠ registers.value → r ≠ registers.tmp →
      r ≠ registers.ptr → reg t r = reg s r) : Parameters b t :=
  ⟨(congrArg Fin.val (same count (by decide +revert) (by decide +revert) (by decide +revert))).trans h.countVal,
    (congrArg Fin.val (same registers.one (by decide +revert) (by decide +revert) (by decide +revert))).trans h.unitVal,
    (congrArg Fin.val (same offsetBase (by decide +revert) (by decide +revert) (by decide +revert))).trans h.orderBase,
    (congrArg Fin.val (same childrenBase (by decide +revert) (by decide +revert) (by decide +revert))).trans h.rankBase⟩

private structure Scatter (b : Banks bits inputCap workCap n) (order : Fin n → Fin n)
    (original : Array (Word bits)) (cursor : Nat) (s : State L) : Prop where
  pc : s.pc = 0
  parameters : Parameters b s
  ptr : (reg s registers.ptr).val = cursor
  ranked : ∀ i : Fin n, i.val < cursor →
    (s.data[b.ranks + (order i).val]?).map Fin.val = some i.val
  frame : ∀ j, (j < b.ranks ∨ b.ranks + n ≤ j) → s.data[j]? = original[j]?

private theorem readPlaced :
    Placed (code hi hw) 1 (readOrder (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [readOrder, indexedInputRead] at h

private theorem putPlaced :
    Placed (code hi hw) 3 (putRank (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [putRank, indexedDataWrite] at h

private theorem iteration (input : Input L) {b : Banks bits inputCap workCap n}
    {order : Fin n → Fin n} {orig : Array (Word bits)}
    (words : InputOrder input b order)
    (injective : ∀ {i j}, order i = order j → i = j)
    (k : Nat) (below : k < n) :
    BlockSpec (code hi hw) input 7 (Scatter b order orig k) (Scatter b order orig (k + 1)) := by
  intro s inv
  let i : Fin n := ⟨k, below⟩
  have iVal : i.val = k := rfl
  have iOrderLt : (order i).val < n := (order i).isLt
  let x : State L := {s with pc := 1}
  have test : ltb (reg s registers.ptr) (reg s count) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr
      (by rw [inv.ptr, inv.parameters.countVal]; exact below)
  have guard : (code hi hw)[s.pc]? = some (.branchLt registers.ptr count 1 7) := by
    rw [inv.pc]; rfl
  have sx : step (code hi hw) input s = some (.next x) := by
    simpa only [x, test, ite_true] using
      step_branchLt_at (input := input) guard (by rw [test]; exact (show 1 < 8 by decide))
  have inputFits := b.orderFits
  have workFits := b.ranksFit
  have counterFits := b.cursorFits
  have readBound : (reg x offsetBase).val + (reg x registers.ptr).val < inputCap := by
    change (reg s offsetBase).val + (reg s registers.ptr).val < inputCap
    rw [inv.parameters.orderBase, inv.ptr]
    omega
  obtain ⟨y, xy, ypc, yWord, yr, ym⟩ := indexedInputRead_steps
    (input := input) (s := x) readPlaced rfl (show 3 < 8 by decide) readBound
  have yValue : (reg y registers.value).val = (order i).val := by
    change some (reg y registers.value) = input.words[(reg s offsetBase).val +
      (reg s registers.ptr).val]? at yWord
    rw [inv.parameters.orderBase, inv.ptr, ← iVal] at yWord
    have h := congrArg (Option.map Fin.val) yWord
    rw [words i] at h
    exact Option.some.inj h
  have yBase : (reg y childrenBase).val = b.ranks :=
    (congrArg Fin.val (yr _ (show childrenBase ≠ registers.value by decide))).trans
      inv.parameters.rankBase
  have storeBound : (reg y childrenBase).val + (reg y registers.value).val < workCap := by
    rw [yBase, yValue]
    omega
  obtain ⟨z, yz, zpc, zMem, _, zr⟩ := indexedDataWrite_steps (input := input)
    (s := y) putPlaced ypc (show 5 < 8 by decide) (show registers.ptr ≠ registers.tmp by decide)
    storeBound
  have yPtr : (reg y registers.ptr).val = k :=
    (congrArg Fin.val (yr registers.ptr (show registers.ptr ≠ registers.value by decide))).trans inv.ptr
  have keep (r : Fin 15) (notTmp : r ≠ registers.tmp) (notValue : r ≠ registers.value) :
      reg z r = reg s r := (zr r notTmp).trans (yr r notValue)
  have incFetch : (code hi hw)[z.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [zpc]; rfl
  obtain ⟨v, zv, vpc, vPtr, vr, vm⟩ := step_add_at (input := input) incFetch
    (by rw [zpc]; exact (show 6 < 8 by decide))
  have vGuard : (code hi hw)[v.pc]? = some (.goto 0) := by rw [vpc, zpc]; rfl
  let t : State L := {v with pc := 0}
  have vt : step (code hi hw) input v = some (.next t) := step_goto_at vGuard (show 0 < 8 by decide)
  have zPtr : (reg z registers.ptr).val = k :=
    (congrArg Fin.val (keep _ (by decide +revert) (by decide +revert))).trans inv.ptr
  have zOne : (reg z registers.one).val = 1 :=
    (congrArg Fin.val (keep _ (by decide +revert) (by decide +revert))).trans inv.parameters.unitVal
  have sumFit : (reg z registers.ptr).val + (reg z registers.one).val < 2 ^ bits := by
    rw [zPtr, zOne]
    omega
  have next : (reg t registers.ptr).val = k + 1 := by
    change (reg v registers.ptr).val = _
    rw [vPtr, PaperB.WordOps.add_no_wrap _ _ sumFit, zPtr, zOne]
  have memory : t.data = s.data.set (b.ranks + (order i).val) (reg y registers.ptr)
      (by rw [s.data_size]; change b.ranks + (order i).val < workCap; omega) := by
    change v.data = _
    rw [vm]
    have same : y.data = s.data := ym
    simpa only [same, yBase, yValue] using zMem
  have frame (j : Nat) (neq : j ≠ b.ranks + (order i).val) : t.data[j]? = s.data[j]? := by
    rw [memory]
    exact Array.getElem?_set_ne _ neq.symm
  refine ⟨t, (Steps.cons sx xy).append (yz.append (.cons zv (.cons vt (.zero _)))),
    ⟨rfl, inv.parameters.keep (fun r hv ht hp => (vr r hp).trans (keep r ht hv)),
      next, ?_, ?_⟩⟩
  · intro j hj
    by_cases same : j = i
    · subst j
      rw [memory, Array.getElem?_set_self, Option.map_some, yPtr]
    · have first : j.val ≠ k := fun eq => same (Fin.ext eq)
      have elsewhere : b.ranks + (order j).val ≠ b.ranks + (order i).val :=
        fun eq => same (injective (Fin.ext (Nat.add_left_cancel eq)))
      rw [frame _ elsewhere]
      exact inv.ranked j (by omega)
  · intro j outside
    exact (frame j (by omega)).trans (inv.frame j outside)

private theorem sevenIterations (n : Nat) : iterationCost (fun _ => 7) n = 7 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterationCost, ih, Nat.mul_succ]

/-- Actual word-RAM inverse of a supplied packed permutation. All
initial rank cells may be arbitrary. Both whole arenas are charged. -/
theorem run_rank_scatter (input : Input L) (b : Banks bits inputCap workCap n)
    (order : Fin n → Fin n) (reading : InputOrder input b order)
    (injective : ∀ {i j}, order i = order j → i = j)
    (s : State L) (pc : s.pc = 0) (params : Parameters b s)
    (zero : (reg s registers.ptr).val = 0) :
    ∃ t trace,
      run (code hi hw) input (7 * n + 2) s = some ⟨t, 7 * n + 2⟩ ∧
      (∀ i : Fin n, (t.data[b.ranks + (order i).val]?).map Fin.val = some i.val) ∧
      (∀ j, (j < b.ranks ∨ b.ranks + n ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (code hi hw) input s trace ⟨t, 7 * n + 2⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have start : Scatter b order s.data 0 s :=
    ⟨pc, params, zero, fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩
  obtain ⟨u, traverse, inv⟩ := loop_steps (code := code hi hw) (input := input)
    n (fun _ => 7) (Scatter b order s.data)
    (iteration input reading injective) s start
  rw [sevenIterations] at traverse
  have no : ltb (reg u registers.ptr) (reg u count) = false := by
    cases e : ltb (reg u registers.ptr) (reg u count) with
    | false => rfl
    | true =>
      have lt := (PaperB.WordOps.ltb_eq_true _ _).mp e
      rw [inv.ptr, inv.parameters.countVal] at lt
      omega
  have guard : (code hi hw)[u.pc]? = some (.branchLt registers.ptr count 1 7) := by rw [inv.pc]; rfl
  let t : State L := {u with pc := 7}
  have ut : step (code hi hw) input u = some (.next t) := by
    simpa only [no, Bool.false_eq_true, ite_false, t] using
      step_branchLt_at (input := input) guard (by rw [no]; exact (show 7 < 8 by decide))
  have execute := (traverse.append (.cons ut (.zero t))).halts (step_halt_at rfl)
  obtain ⟨trace, checked⟩ := run_has_successfulTrace execute
  exact ⟨t, trace, execute, fun i => inv.ranked i i.isLt, inv.frame, checked, checked.peak_eq⟩

open PaperB.ForestPreparedBuild (IsTopologicalOrder orderRanks orderRanks_at orderRanks_rankArc)
open PaperB.KahnDecreasing (readRank)
open _root_.EX24.PreparedSweep (orderedVertexAt)

/-- Identify the physical bank with the exact rank table consumed by the
ordered quotient sweep. The supplied order is read, never recomputed. -/
theorem run_order_ranks (input : Input L) {H : LabelledQuotient}
    (b : Banks bits inputCap workCap H.vertexCount)
    (order : Array (Vertex H)) (size : order.size = H.vertexCount)
    (unique : order.toList.Nodup)
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt order size i = v)
    (topo : IsTopologicalOrder order size)
    (reading : InputOrder input b (orderedVertexAt order size))
    (s : State L) (pc : s.pc = 0) (params : Parameters b s)
    (zero : (reg s registers.ptr).val = 0) :
    let rank := readRank (orderRanks order unique)
    ∃ t trace,
      run (code hi hw) input (7 * H.vertexCount + 2) s =
        some ⟨t, 7 * H.vertexCount + 2⟩ ∧
      (∀ v : Vertex H, (t.data[b.ranks + v.val]?).map Fin.val = some (rank v)) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) ∧
      (∀ j, (j < b.ranks ∨ b.ranks + H.vertexCount ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (code hi hw) input s trace ⟨t, 7 * H.vertexCount + 2⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let rank := readRank (orderRanks order unique)
  have exactAt (i : Fin H.vertexCount) :
      rank (orderedVertexAt order size i) = i.val := orderRanks_at order size unique i
  have injective : ∀ {i j}, orderedVertexAt order size i = orderedVertexAt order size j → i = j := by
    intro i j eq
    apply Fin.ext
    rw [← exactAt i, ← exactAt j, eq]
  obtain ⟨t, states, exec, written, frame, trace, peak⟩ :=
    run_rank_scatter input b (orderedVertexAt order size) reading injective s pc params zero
  refine ⟨t, states, exec, ?_, orderRanks_rankArc order size unique covers topo,
    frame, trace, peak⟩
  intro v
  obtain ⟨i, eq⟩ := covers v
  change (t.data[b.ranks + v.val]?).map Fin.val = some (rank v)
  rw [← eq, exactAt i]
  exact written i

end PaperB.RamForestProgram.OrderRank
