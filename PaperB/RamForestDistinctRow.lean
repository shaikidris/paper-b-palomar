module

public import PaperB.RamForestArcDecode

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.ArcDecode

open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.WordOps (ltb)

variable {bits inputCap workCap vertices arcs length : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

structure DistinctBanks (bits inputCap workCap vertices arcs length : Nat) where
  read : Banks bits inputCap workCap vertices arcs length
  output : Nat
  epoch : Nat
  rowsBeforeStamps : read.tokens + length ≤ read.stamps
  stampsBeforeOutput : read.stamps + vertices ≤ output
  outputFits : output + length ≤ workCap

structure DistinctParams (b : DistinctBanks bits inputCap workCap vertices arcs length)
    (s : State L) : Prop where
  reader : ReadParams b.read s
  total : (reg s count).val = length
  outputBase : (reg s childrenBase).val = b.output
  epochVal : (reg s toutBase).val = b.epoch
  unit : (reg s registers.one).val = 1

private theorem DistinctParams.keep {b : DistinctBanks bits inputCap workCap vertices arcs length}
    {s t : State L} (p : DistinctParams b s)
    (keep : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
      r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk → reg t r = reg s r) :
    DistinctParams b t := by
  have val (r : Fin 15) (p₀ : r ≠ registers.ptr) (p₁ : r ≠ registers.remain)
      (p₂ : r ≠ registers.value) (p₃ : r ≠ registers.childBase) (p₄ : r ≠ registers.tmp)
      (p₅ : r ≠ clk) : (reg t r).val = (reg s r).val := congrArg Fin.val (keep r p₀ p₁ p₂ p₃ p₄ p₅)
  exact ⟨⟨(val registers.stackBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.sourceBase,
      (val offsetBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.tokensBase,
      (val tinBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.stampsBase,
      (val cmd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.shift⟩,
    (val count (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.total,
    (val childrenBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.outputBase,
    (val toutBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.epochVal,
    (val registers.one (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.unit⟩

private def storeStamp : List (Instr bits 15) :=
  indexedDataWrite registers.tmp tinBase registers.value toutBase

private def appendSrc : List (Instr bits 15) :=
  indexedDataWrite registers.tmp childrenBase clk registers.value

/-- Test the epoch marker once per occurrence and emit one word per
distinct source. The original incoming row is read in place. -/
def distinctProgram (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  let first : Instr bits 15 := .branchLt registers.ptr count 1 16
  let test : Instr bits 15 := .branchLt registers.childBase toutBase 9 14
  let last : List (Instr bits 15) :=
    [.add clk clk registers.one, .add registers.ptr registers.ptr registers.one, .goto 0, .halt]
  ([first] ++ (readBlock ++ ([test] ++ (storeStamp ++ (appendSrc ++ last))))).toArray

private theorem readerPlaced :
    Placed (distinctProgram hi hw) 1 (readBlock (bits := bits)) := by
  exact @placed_link bits L [.branchLt registers.ptr count 1 16] readBlock
    ([Instr.branchLt registers.childBase toutBase 9 14] ++ (storeStamp ++
      (appendSrc ++ [.add clk clk registers.one, .add registers.ptr registers.ptr registers.one, .goto 0, .halt])))

private theorem markPlaced : Placed (distinctProgram hi hw) 9 (storeStamp (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [storeStamp, indexedDataWrite] at h

private theorem outPlaced : Placed (distinctProgram hi hw) 11 (appendSrc (bits := bits)) := by
  intro i op h
  cases i with
  | zero => exact h
  | succ i =>
    cases i with
    | zero => exact h
    | succ i => simp [appendSrc, indexedDataWrite] at h

private structure Selected (b : DistinctBanks bits inputCap workCap vertices arcs length)
    (source : Fin arcs → Fin vertices) (row : Fin length → Fin arcs)
    (orig : Array (Word bits)) (i : Nat) (xs : List (Fin vertices)) (data : Array (Word bits)) : Prop where
  tokens : TokensAt (vertices := vertices) data b.read.tokens row
  nodup : xs.Nodup
  count_le : xs.length ≤ i
  membership : ∀ v, v ∈ xs ↔ ∃ j : Fin length, j.val < i ∧ source (row j) = v
  markers : ∀ v : Fin vertices, ∃ w : Word bits,
    data[b.read.stamps + v.val]? = some w ∧ w.val ≤ b.epoch ∧
      (w.val = b.epoch ↔ v ∈ xs)
  output : ∀ j : Fin xs.length,
    (data[b.output + j.val]?).map Fin.val = some (xs[j.val]'j.isLt).val
  frame : ∀ j, (j < b.read.stamps ∨ b.output + length ≤ j) → data[j]? = orig[j]?

private def atCursor (b : DistinctBanks bits inputCap workCap vertices arcs length)
    (source : Fin arcs → Fin vertices) (row : Fin length → Fin arcs)
    (orig : Array (Word bits)) (i : Nat) (s : State L) : Prop :=
  s.pc = 0 ∧ DistinctParams b s ∧ (reg s registers.ptr).val = i ∧
  ∃ xs, (reg s clk).val = xs.length ∧ Selected b source row orig i xs s.data

private theorem prefixMembership {source : Fin arcs → Fin vertices} {row : Fin length → Fin arcs}
    (i : Fin length) (v : Fin vertices) :
    (∃ j : Fin length, j.val < i.val + 1 ∧ source (row j) = v) ↔
      (∃ j : Fin length, j.val < i.val ∧ source (row j) = v) ∨ source (row i) = v := by
  constructor
  · rintro ⟨j, lt, eq⟩
    by_cases same : j = i
    · exact Or.inr (same ▸ eq)
    · have ne : j.val ≠ i.val := fun h => same (Fin.ext h)
      exact Or.inl ⟨j, by omega, eq⟩
  · rintro (⟨j, lt, eq⟩ | eq)
    · exact ⟨j, by omega, eq⟩
    · exact ⟨i, by omega, eq⟩

private theorem selected_skip {b : DistinctBanks bits inputCap workCap vertices arcs length}
    {source : Fin arcs → Fin vertices} {row : Fin length → Fin arcs}
    {orig data : Array (Word bits)} {xs : List (Fin vertices)} (i : Fin length)
    (old : Selected b source row orig i.val xs data) (seen : source (row i) ∈ xs) :
    Selected b source row orig (i.val + 1) xs data := by
  refine ⟨old.tokens, old.nodup, by have := old.count_le; omega, ?_, old.markers, old.output, old.frame⟩
  intro v
  rw [prefixMembership, ← old.membership]
  exact ⟨Or.inl, fun p => p.elim id (fun eq => eq ▸ seen)⟩

private theorem selected_add {b : DistinctBanks bits inputCap workCap vertices arcs length}
    {source : Fin arcs → Fin vertices} {row : Fin length → Fin arcs}
    {orig data next : Array (Word bits)} {xs : List (Fin vertices)} (i : Fin length)
    (old : Selected b source row orig i.val xs data) (fresh : source (row i) ∉ xs)
    (tag : Word bits) (tagVal : tag.val = b.epoch)
    (stamped : next[b.read.stamps + (source (row i)).val]? = some tag)
    (wrote : (next[b.output + xs.length]?).map Fin.val = some (source (row i)).val)
    (keep : ∀ j, j ≠ b.read.stamps + (source (row i)).val → j ≠ b.output + xs.length →
      next[j]? = data[j]?) :
    Selected b source row orig (i.val + 1) (xs ++ [source (row i)]) next := by
  let v := source (row i)
  have vFit := v.isLt
  have split := b.stampsBeforeOutput
  have before := b.rowsBeforeStamps
  have len := old.count_le
  have limit := i.isLt
  have nodup : (xs ++ [v]).Nodup := by
    rw [List.nodup_append]
    exact ⟨old.nodup, by simp, fun a ha b hb eq => by
      simp only [List.mem_singleton] at hb
      rw [hb] at eq
      apply fresh
      change v ∈ xs
      rwa [← eq]⟩
  refine ⟨?_, nodup, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have jt := j.isLt
    rw [keep _ (by omega) (by omega)]
    exact old.tokens j
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · intro q
    rw [List.mem_append, List.mem_singleton, prefixMembership, ← old.membership]
    constructor
    · exact fun h => h.elim Or.inl (fun eq => Or.inr eq.symm)
    · exact fun h => h.elim Or.inl (fun eq => Or.inr eq.symm)
  · intro q
    by_cases eq : q = v
    · subst q
      exact ⟨tag, stamped, by omega, by simp [tagVal, v]⟩
    · obtain ⟨value, present, bound, changeAt⟩ := old.markers q
      have qFit := q.isLt
      have notCell : b.read.stamps + q.val ≠ b.read.stamps + v.val :=
        fun eq' => eq (Fin.ext (Nat.add_left_cancel eq'))
      refine ⟨value, (keep _ notCell (by omega)).trans present, bound, ?_⟩
      have other : q ≠ source (row i) := eq
      simpa only [List.mem_append, List.mem_singleton, other, or_false] using changeAt
  · intro j
    have ji := j.isLt
    simp only [List.length_append, List.length_cons, List.length_nil] at ji
    by_cases prior : j.val < xs.length
    · rw [List.getElem_append_left prior, keep _ (by omega) (by omega)]
      exact old.output ⟨j.val, prior⟩
    · have jlast : j.val = xs.length := by omega
      have read : (xs ++ [v])[j.val]'j.isLt = v := by
        simp only [List.getElem_append_right (show xs.length ≤ j.val by omega),
          show j.val - xs.length = 0 by omega, List.getElem_cons_zero]
      rw [read, jlast]
      exact wrote
  · intro j outside
    exact (keep j (by omega) (by omega)).trans (old.frame j outside)

private theorem insertAt9 (input : Input L)
    {b : DistinctBanks bits inputCap workCap vertices arcs length}
    {source : Fin arcs → Fin vertices} {row : Fin length → Fin arcs}
    {orig : Array (Word bits)} {xs : List (Fin vertices)} (i : Fin length)
    (s : State L) (pc : s.pc = 9) (params : DistinctParams b s)
    (idx : (reg s registers.ptr).val = i.val) (cursor : (reg s clk).val = xs.length)
    (tail : (reg s registers.value).val = (source (row i)).val)
    (old : Selected b source row orig i.val xs s.data)
    (fresh : source (row i) ∉ xs) :
    ∃ t, Steps (distinctProgram hi hw) input 5 s t ∧ t.pc = 14 ∧
      DistinctParams b t ∧ (reg t registers.ptr).val = i.val ∧
      (reg t clk).val = (xs ++ [source (row i)]).length ∧
      Selected b source row orig (i.val + 1) (xs ++ [source (row i)]) t.data := by
  let k := source (row i)
  have kt := k.isLt
  have width := old.count_le
  have lt := i.isLt
  have before := b.stampsBeforeOutput
  have outputFits := b.outputFits
  have stampFit : (reg s tinBase).val + (reg s registers.value).val < workCap := by
    rw [params.reader.stampsBase, tail]
    change b.read.stamps + k.val < workCap
    omega
  obtain ⟨u, su, upc, um, _, ur⟩ := indexedDataWrite_steps (input := input) (s := s)
    markPlaced pc (show 11 < 17 by decide) (show toutBase ≠ registers.tmp by decide) stampFit
  have uParams := params.keep (fun r _ _ _ _ ht _ => ur r ht)
  have uCount : (reg u clk).val = xs.length :=
    (congrArg Fin.val (ur _ (show clk ≠ registers.tmp by decide))).trans cursor
  have uTail : (reg u registers.value).val = k.val :=
    (congrArg Fin.val (ur _ (show registers.value ≠ registers.tmp by decide))).trans tail
  have outFit : (reg u childrenBase).val + (reg u clk).val < workCap := by
    rw [uParams.outputBase, uCount]; omega
  obtain ⟨v, uv, vpc, vm, _, vr⟩ := indexedDataWrite_steps (input := input) (s := u)
    outPlaced upc (show 13 < 17 by decide) (show registers.value ≠ registers.tmp by decide) outFit
  have vCount : (reg v clk).val = xs.length :=
    (congrArg Fin.val (vr _ (show clk ≠ registers.tmp by decide))).trans uCount
  have vParams := uParams.keep (fun r _ _ _ _ ht _ => vr r ht)
  have incFetch : (distinctProgram hi hw)[v.pc]? = some (.add clk clk registers.one) := by
    rw [vpc]; rfl
  obtain ⟨t, vt, tpc, tval, tr, tm⟩ := step_add_at (input := input) incFetch
    (by rw [vpc]; exact (show 14 < 17 by decide))
  have lengthFit := (reg v count).isLt
  rw [vParams.total] at lengthFit
  have addFit : (reg v clk).val + (reg v registers.one).val < 2 ^ bits := by
    rw [vCount, vParams.unit]; omega
  have installed : u.data = s.data.set (b.read.stamps + k.val) (reg s toutBase)
      (by rw [s.data_size]; change b.read.stamps + k.val < workCap; omega) := by
    simpa only [params.reader.stampsBase, tail, k] using um
  have appended : t.data = u.data.set (b.output + xs.length) (reg u registers.value)
      (by rw [u.data_size]; change b.output + xs.length < workCap; omega) := by
    rw [tm]
    simpa only [uParams.outputBase, uCount] using vm
  have keepStamp (j : Nat) (h : j ≠ b.read.stamps + k.val) : u.data[j]? = s.data[j]? := by
    rw [installed]; exact Array.getElem?_set_ne _ h.symm
  have keepOut (j : Nat) (h : j ≠ b.output + xs.length) : t.data[j]? = u.data[j]? := by
    rw [appended]; exact Array.getElem?_set_ne _ h.symm
  have stamp : t.data[b.read.stamps + k.val]? = some (reg s toutBase) := by
    rw [keepOut _ (by omega), installed, Array.getElem?_set_self]
  have out : (t.data[b.output + xs.length]?).map Fin.val = some k.val := by
    rw [appended, Array.getElem?_set_self, Option.map_some, uTail]
  refine ⟨t, su.append (uv.append (.cons vt (.zero t))), by omega,
    vParams.keep (fun r _ _ _ _ _ hc => tr r hc), ?_, ?_,
    selected_add i old fresh (reg s toutBase) params.epochVal stamp out
      (fun j a c => (keepOut j c).trans (keepStamp j a))⟩
  · rw [tr _ (show registers.ptr ≠ clk by decide),
      vr _ (show registers.ptr ≠ registers.tmp by decide),
      ur _ (show registers.ptr ≠ registers.tmp by decide), idx]
  · rw [tval, PaperB.WordOps.add_no_wrap _ _ addFit, vCount, vParams.unit]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]

private theorem distinct_step (input : Input L)
    {b : DistinctBanks bits inputCap workCap vertices arcs length}
    {source : Fin arcs → Fin vertices} {row : Fin length → Fin arcs}
    {orig : Array (Word bits)} (raw : SourcesAt input b.read.inputSource source)
    (i : Nat) (lt : i < length) (s : State L) (ready : atCursor b source row orig i s) :
    ∃ t cost, cost ≤ 16 ∧ Steps (distinctProgram hi hw) input cost s t ∧
      atCursor b source row orig (i + 1) t := by
  obtain ⟨pc, params, idx, xs, outLen, old⟩ := ready
  let j : Fin length := ⟨i, lt⟩
  let k := source (row j)
  let u : State L := {s with pc := 1}
  have guard : (distinctProgram hi hw)[s.pc]? = some (.branchLt registers.ptr count 1 16) := by
    rw [pc]; rfl
  have go : ltb (reg s registers.ptr) (reg s count) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [idx, params.total]; exact lt)
  have su : step (distinctProgram hi hw) input s = some (.next u) := by
    simpa only [u, go, ite_true] using
      step_branchLt_at (input := input) guard (by rw [go]; exact (show 1 < 17 by decide))
  have up : DistinctParams b u := params.keep (fun _ _ _ _ _ _ _ => rfl)
  obtain ⟨v, uv, vpc, vm, _, tail, mark, vr⟩ := readBlock_steps
    input source row raw readerPlaced (show 8 < 17 by decide) u rfl up.reader old.tokens j idx
  have vp := params.keep (fun r _ nr nv nc _ _ => vr r nr nv nc)
  have vIdx : (reg v registers.ptr).val = i :=
    (congrArg Fin.val (vr _ (show registers.ptr ≠ registers.remain by decide)
      (show registers.ptr ≠ registers.value by decide)
      (show registers.ptr ≠ registers.childBase by decide))).trans idx
  have vLen : (reg v clk).val = xs.length :=
    (congrArg Fin.val (vr _ (show clk ≠ registers.remain by decide)
      (show clk ≠ registers.value by decide) (show clk ≠ registers.childBase by decide))).trans outLen
  have vData : v.data = s.data := vm
  obtain ⟨w, read, atMost, present⟩ := old.markers k
  have markEq : reg v registers.childBase = w := Option.some.inj (mark.symm.trans read)
  have tested : (distinctProgram hi hw)[v.pc]? =
      some (.branchLt registers.childBase toutBase 9 14) := by rw [vpc]; rfl
  have selected : ∃ (y : State L) (w : Nat) (out : List (Fin vertices)),
      w ≤ 6 ∧ Steps (distinctProgram hi hw) input w v y ∧ y.pc = 14 ∧
      DistinctParams b y ∧ (reg y registers.ptr).val = i ∧
      (reg y clk).val = out.length ∧ Selected b source row orig (i + 1) out y.data := by
    by_cases seen : k ∈ xs
    · have markSame : (reg v registers.childBase).val = (reg v toutBase).val := by
        rw [markEq, vp.epochVal]; exact present.mpr seen
      have no : ltb (reg v registers.childBase) (reg v toutBase) = false := by
        cases h : ltb (reg v registers.childBase) (reg v toutBase) with
        | false => rfl
        | true =>
          have bad := (PaperB.WordOps.ltb_eq_true _ _).mp h
          rw [markSame] at bad
          exact (Nat.lt_irrefl _ bad).elim
      let y : State L := {v with pc := 14}
      have vy : step (distinctProgram hi hw) input v = some (.next y) := by
        simpa only [y, no, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) tested (by rw [no]; exact (show 14 < 17 by decide))
      refine ⟨y, 1, xs, by decide, .cons vy (.zero y), rfl,
        vp.keep (fun _ _ _ _ _ _ _ => rfl), vIdx, vLen, ?_⟩
      change Selected b source row orig (i + 1) xs v.data
      rw [vData]
      exact selected_skip j old seen
    · have yes : ltb (reg v registers.childBase) (reg v toutBase) = true := by
        apply (PaperB.WordOps.ltb_eq_true _ _).mpr
        rw [markEq, vp.epochVal]
        have neq : w.val ≠ b.epoch := fun e => seen (present.mp e)
        omega
      let y : State L := {v with pc := 9}
      have vy : step (distinctProgram hi hw) input v = some (.next y) := by
        simpa only [y, yes, ite_true] using
          step_branchLt_at (input := input) tested (by rw [yes]; exact (show 9 < 17 by decide))
      have start : Selected b source row orig i xs y.data := by
        change Selected b source row orig i xs v.data
        rwa [vData]
      obtain ⟨z, yz, zpc, zp, zi, len, correct⟩ := insertAt9 input j y rfl
        (vp.keep (fun _ _ _ _ _ _ _ => rfl)) vIdx vLen tail start seen
      exact ⟨z, 6, _, by decide, .cons vy yz, zpc, zp, zi, len, correct⟩
  obtain ⟨y, work, out, bound, vy, ypc, yp, yidx, ylen, after⟩ := selected
  have bump : (distinctProgram hi hw)[y.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [ypc]; rfl
  obtain ⟨z, yz, zpc, zVal, zr, zm⟩ := step_add_at (input := input) bump
    (by rw [ypc]; exact (show 15 < 17 by decide))
  have jmp : (distinctProgram hi hw)[z.pc]? = some (.goto 0) := by rw [zpc, ypc]; rfl
  let t : State L := {z with pc := 0}
  have zt : step (distinctProgram hi hw) input z = some (.next t) :=
    step_goto_at jmp (show 0 < 17 by decide)
  have lengthFit := (reg y count).isLt
  rw [yp.total] at lengthFit
  have safe : (reg y registers.ptr).val + (reg y registers.one).val < 2 ^ bits := by
    rw [yidx, yp.unit]; omega
  have next : (reg t registers.ptr).val = i + 1 := by
    change (reg z registers.ptr).val = _
    rw [zVal, PaperB.WordOps.add_no_wrap _ _ safe, yidx, yp.unit]
  have ok : Selected b source row orig (i + 1) out t.data := by
    change Selected b source row orig (i + 1) out z.data
    rwa [zm]
  exact ⟨t, 8 + (work + 2), by omega,
    (Steps.cons su uv).append (vy.append (.cons yz (.cons zt (.zero t)))),
    rfl, yp.keep (fun r hp _ _ _ _ _ => zr r hp), next, out,
    (congrArg Fin.val (zr _ (show clk ≠ registers.ptr by decide))).trans ylen, ok⟩

/-- From any physical incoming row and an older epoch table, emit the
first occurrence of each distinct predecessor. In particular the
budget is linear in raw occurrences, including all duplicates. -/
theorem run_distinct_row (input : Input L)
    (b : DistinctBanks bits inputCap workCap vertices arcs length)
    (source : Fin arcs → Fin vertices) (row : Fin length → Fin arcs)
    (raw : SourcesAt input b.read.inputSource source) (s : State L)
    (pc : s.pc = 0) (params : DistinctParams b s)
    (cursor : (reg s registers.ptr).val = 0) (empty : (reg s clk).val = 0)
    (tokens : TokensAt (vertices := vertices) s.data b.read.tokens row)
    (older : ∀ v : Fin vertices, ∃ w : Word bits, s.data[b.read.stamps + v.val]? = some w ∧
      w.val < b.epoch) :
    ∃ (t : State L) (trace : List (State L)) (work : Nat) (out : List (Fin vertices)),
      work ≤ 16 * length + 2 ∧
      run (distinctProgram hi hw) input work s = some ⟨t, work⟩ ∧
      (reg t clk).val = out.length ∧ out.Nodup ∧ out.length ≤ length ∧
      (∀ v, v ∈ out ↔ ∃ j : Fin length, source (row j) = v) ∧
      (∀ j : Fin out.length, (t.data[b.output + j.val]?).map Fin.val = some (out[j.val]'j.isLt).val) ∧
      (∀ j, (j < b.read.stamps ∨ b.output + length ≤ j) → t.data[j]? = s.data[j]?) ∧
      SuccessfulTrace (distinctProgram hi hw) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have start : atCursor b source row s.data 0 s := by
    refine ⟨pc, params, cursor, [], empty, tokens, List.nodup_nil, Nat.le_refl _, ?_, ?_, ?_, fun _ _ => rfl⟩
    · intro v; constructor
      · simp
      · rintro ⟨j, bound, _⟩
        exact (Nat.not_lt_zero _ bound).elim
    · intro v
      obtain ⟨w, read, bound⟩ := older v
      exact ⟨w, read, Nat.le_of_lt bound, by simp [Nat.ne_of_lt bound]⟩
    · intro j
      exact j.elim0
  have traverse : ∀ k, k ≤ length → ∃ t work, work ≤ 16 * k ∧
      Steps (distinctProgram hi hw) input work s t ∧ atCursor b source row s.data k t := by
    intro k bound
    induction k with
    | zero => exact ⟨s, 0, Nat.le_refl _, .zero s, start⟩
    | succ k ih =>
      obtain ⟨v, w, wBound, steps, inv⟩ := ih (by omega)
      obtain ⟨t, kWork, kBound, next, h⟩ := distinct_step input raw k (by omega) v inv
      exact ⟨t, w + kWork, by omega, steps.append next, h⟩
  obtain ⟨v, w, bound, steps, inv⟩ := traverse length (Nat.le_refl _)
  obtain ⟨vpc, vp, vind, out, vlen, state⟩ := inv
  have no : ltb (reg v registers.ptr) (reg v count) = false := by
    cases h : ltb (reg v registers.ptr) (reg v count) with
    | false => rfl
    | true =>
      have wrong := (PaperB.WordOps.ltb_eq_true _ _).mp h
      rw [vind, vp.total] at wrong
      exact (Nat.lt_irrefl _ wrong).elim
  let t : State L := {v with pc := 16}
  have guard : (distinctProgram hi hw)[v.pc]? = some (.branchLt registers.ptr count 1 16) := by
    rw [vpc]; rfl
  have vt : step (distinctProgram hi hw) input v = some (.next t) := by
    simpa only [t, no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) guard (by rw [no]; exact (show 16 < 17 by decide))
  have run := (steps.append (.cons vt (.zero _))).halts (step_halt_at rfl)
  obtain ⟨trace, success⟩ := run_has_successfulTrace run
  refine ⟨t, trace, w + 2, out, by omega, run, vlen, state.nodup, state.count_le, ?_,
    state.output, state.frame, success, success.peak_eq⟩
  intro u
  constructor
  · intro once
    obtain ⟨j, _, head⟩ := (state.membership u).mp once
    exact ⟨j, head⟩
  · rintro ⟨j, head⟩
    exact (state.membership u).mpr ⟨j, j.isLt, head⟩

section Quotient

open PaperB (LabelledQuotient)
open PaperB.RamForestProgram.ArcParents (rawOccurrence rawHead rawRow_source_iff rowNodes arcNode)

/-- An output row has the exact predecessor support used by the forest
sweep. Its occurrence decoder is the one from the physical CSR image. -/
theorem distinct_source_support (H : LabelledQuotient) (v : Fin H.vertexCount)
    (row : Fin (rowNodes (rawHead H) v).length → Fin H.arcCount)
    (positions : ∀ i : Fin (rowNodes (rawHead H) v).length,
      (rowNodes (rawHead H) v)[i.val]'i.isLt = arcNode H.vertexCount (row i))
    (out : List (Fin H.vertexCount))
    (observed : ∀ u, u ∈ out ↔ ∃ i, (rawOccurrence H (row i)).1 = u) :
    ∀ u, u ∈ out ↔ H.HasQuotientArc u v := by
  intro u
  rw [observed u, ← rawRow_source_iff H u v]
  constructor
  · rintro ⟨i, source⟩
    have h : (rowNodes (rawHead H) v)[i.val]'i.isLt ∈ rowNodes (rawHead H) v :=
      List.getElem_mem i.isLt
    rw [positions i] at h
    exact ⟨row i, h, source⟩
  · rintro ⟨e, here, source⟩
    obtain ⟨j, bound, atj⟩ := List.mem_iff_getElem.mp here
    let i : Fin (rowNodes (rawHead H) v).length := ⟨j, bound⟩
    have eq : arcNode H.vertexCount (row i) = arcNode H.vertexCount e :=
      (positions i).symm.trans atj
    have same : row i = e := by
      apply Fin.ext
      have addr := congrArg Fin.val eq
      change H.vertexCount + 1 + (row i).val = H.vertexCount + 1 + e.val at addr
      omega
    exact ⟨i, same.symm ▸ source⟩

end Quotient

end PaperB.RamForestProgram.ArcDecode
