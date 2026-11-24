module

public import PaperB.RamProgram
public import PaperB.PackedSectionSeal
public import PaperB.ForestOrderRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

universe u

namespace SliceCopy

structure Prefix {α : Type u} (orig current : Array α)
    (src dst i : Nat) : Prop where
  sameSize : current.size = orig.size
  copied : ∀ j : Nat, j < i → current[dst + j]? = orig[src + j]?
  untouched : ∀ k : Nat, (k < dst ∨ dst + i ≤ k) →
    current[k]? = orig[k]?

theorem Prefix.zero {α : Type u} (orig : Array α) (src dst : Nat) :
    Prefix orig orig src dst 0 where
  sameSize := rfl
  copied := by
    intro j hj
    omega
  untouched := by
    intro k hk
    rfl

theorem Prefix.advance {α : Type u} {orig current : Array α}
    {src dst i : Nat} {v : α}
    (p : Prefix orig current src dst i)
    (hwrite : dst + i < current.size)
    (hread : orig[src + i]? = some v) :
    Prefix orig (current.set (dst + i) v hwrite) src dst (i + 1) := by
  have hsize : (current.set (dst + i) v hwrite).size = current.size := by
    simp only [Array.size_set]
  have hupdated : (current.set (dst + i) v hwrite)[dst + i]? = some v := by
    have hbound : dst + i < (current.set (dst + i) v hwrite).size := by
      simpa only [hsize] using hwrite
    rw [getElem?_pos (current.set (dst + i) v hwrite) (dst + i) hbound] <;> simp
  have hunchanged (k : Nat) (hne : dst + i ≠ k) :
      (current.set (dst + i) v hwrite)[k]? = current[k]? := by
    by_cases hk : k < current.size
    · have hk' : k < (current.set (dst + i) v hwrite).size := by
        simpa only [hsize] using hk
      rw [getElem?_pos (current.set (dst + i) v hwrite) k hk', getElem?_pos current k hk] <;>
        simp [Array.getElem_set, hne]
    · have hk' : ¬ k < (current.set (dst + i) v hwrite).size := by
        simpa only [hsize] using hk
      rw [getElem?_neg (current.set (dst + i) v hwrite) k hk', getElem?_neg current k hk]
  refine ⟨hsize.trans p.sameSize, ?_, ?_⟩
  · intro j hj
    by_cases heq : j = i
    · subst j
      exact hupdated.trans hread.symm
    · have hj' : j < i := by omega
      exact (hunchanged (dst + j) (by omega)).trans (p.copied j hj')
  · intro k hk
    rcases hk with hleft | hright
    · exact (hunchanged k (by omega)).trans (p.untouched k (Or.inl hleft))
    · have hold : dst + i ≤ k := by omega
      exact (hunchanged k (by omega)).trans (p.untouched k (Or.inr hold))

theorem source_outside {src dst count i : Nat}
    (hdisjoint : dst + count ≤ src ∨ src + count ≤ dst)
    (hi : i < count) :
    src + i < dst ∨ dst + i ≤ src + i := by
  rcases hdisjoint with h | h
  · exact Or.inr (by omega)
  · exact Or.inl (by omega)

end SliceCopy

namespace PaperB.RamSliceCopy

open PaperB.Machine (Word)
open PaperB.WordOps (add ltb)
open PaperB.RamProgram

def layout (bits inputCap workCap : Nat) (hi : inputCap ≤ 2 ^ bits)
    (hw : workCap ≤ 2 ^ bits) : Layout bits :=
  ⟨7, inputCap, workCap, hi, hw⟩

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}

private abbrev cursor : Fin 7 := 0
private abbrev limit : Fin 7 := 1
private abbrev source : Fin 7 := 2
private abbrev target : Fin 7 := 3
private abbrev unit : Fin 7 := 4
private abbrev value : Fin 7 := 5
private abbrev address : Fin 7 := 6

/-- The loop reads and writes the same work arena. The enclosing program
supplies the start offsets, limit, zero cursor and unit increment. -/
def codeBlock (entry : Nat) : List (Instr bits 7) :=
  [.branchLt cursor limit (entry + 1) (entry + 7),
   .add value source cursor, .loadData value value,
   .add address target cursor, .storeData address value,
   .add cursor cursor unit, .goto entry]

structure Transfer (bits workCap : Nat) where
  src : Nat
  dst : Nat
  count : Nat
  src_end : src + count ≤ workCap
  dst_end : dst + count ≤ workCap
  disjoint : dst + count ≤ src ∨ src + count ≤ dst
  count_fits : count < 2 ^ bits

structure Invariant
    (x : Transfer bits workCap) (orig : Array (Word bits)) (entry i : Nat)
    (s : State (layout bits inputCap workCap hi hw)) : Prop where
  loopPC : s.pc = entry
  cursor_val : (reg s cursor).val = i
  limit_val : (reg s limit).val = x.count
  source_val : (reg s source).val = x.src
  target_val : (reg s target).val = x.dst
  unit_val : (reg s unit).val = 1
  copiedPrefix : SliceCopy.Prefix orig s.data x.src x.dst i

variable {code : Program (layout bits inputCap workCap hi hw)}
variable {input : Input (layout bits inputCap workCap hi hw)}

private theorem iteration {x : Transfer bits workCap} {orig : Array (Word bits)}
    {entry i : Nat} (placed : Placed code entry (codeBlock entry))
    (exit_fits : entry + 7 < code.size) (below : i < x.count) :
    BlockSpec code input 7 (Invariant x orig entry i) (Invariant x orig entry (i + 1)) := by
  intro s hs
  have cmp : ltb (reg s cursor) (reg s limit) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [hs.cursor_val, hs.limit_val]; exact below)
  let a := { s with pc := entry + 1 }
  have ha : step code input s = some (.next a) := by
    have hf : code[s.pc]? = some (.branchLt cursor limit (entry + 1) (entry + 7)) := by
      rw [hs.loopPC, ← Nat.add_zero entry]
      exact placed 0 _ rfl
    simpa [cmp, a] using
      (step_branchLt_at (input := input) hf (by simp [cmp]; omega))
  have pa : Placed code (entry + 1) (indexedDataRead value source cursor) := by
    intro k op hk
    cases k with
    | zero =>
      have eq : Instr.add value source cursor = op := Option.some.inj hk
      subst op
      exact placed 1 _ rfl
    | succ k =>
      cases k with
      | zero =>
        have eq : Instr.loadData value value = op := Option.some.inj hk
        subst op
        exact placed 2 _ rfl
      | succ k => simp [indexedDataRead] at hk
  have srcBound : x.src + i < workCap := by have := x.src_end; omega
  have dstBound : x.dst + i < workCap := by have := x.dst_end; omega
  have loadBound : (reg a source).val + (reg a cursor).val < workCap := by
    change (reg s source).val + (reg s cursor).val < workCap
    rwa [hs.source_val, hs.cursor_val]
  obtain ⟨b, hab, pb, hb, regsB, dataB⟩ :=
    indexedDataRead_steps (input := input) (s := a) pa rfl (by omega) loadBound
  have savedRead : orig[x.src + i]? = some (reg b value) := by
    have remain := hs.copiedPrefix.untouched (x.src + i)
      (SliceCopy.source_outside x.disjoint below)
    have hRead : some (reg b value) = s.data[x.src+i]? := by
      change some (reg b value) =
        s.data[(reg s source).val + (reg s cursor).val]? at hb
      rwa [hs.source_val, hs.cursor_val] at hb
    exact remain.symm.trans hRead.symm
  have pw : Placed code (entry + 3) (indexedDataWrite address target cursor value) := by
    intro k op hk
    cases k with
    | zero =>
      have eq : Instr.add address target cursor = op := Option.some.inj hk
      subst op
      exact placed 3 _ rfl
    | succ k =>
      cases k with
      | zero =>
        have eq : Instr.storeData address value = op := Option.some.inj hk
        subst op
        exact placed 4 _ rfl
      | succ k => simp [indexedDataWrite] at hk
  have bSame {r : Fin 7} (h : r ≠ value) : reg b r = reg s r :=
    regsB r h
  have bIdx : (reg b cursor).val = i := by rw [bSame (by decide), hs.cursor_val]
  have bDst : (reg b target).val = x.dst := by rw [bSame (by decide), hs.target_val]
  have toWrite : (reg b target).val + (reg b cursor).val < workCap := by
    rwa [bDst, bIdx]
  obtain ⟨c, hbc, pc, dataC, _, regsC⟩ :=
    indexedDataWrite_steps (input := input) (s := b) pw (by omega) (by omega)
      (show value ≠ address by decide) toWrite
  have cSame {r : Fin 7} (h : r ≠ address) (g : r ≠ value) : reg c r = reg s r :=
    (regsC r h).trans (bSame g)
  have prefixC : SliceCopy.Prefix orig c.data x.src x.dst (i + 1) := by
    have writeBound : x.dst + i < s.data.size := by
      rw [s.data_size]; exact dstBound
    have advanced := hs.copiedPrefix.advance writeBound savedRead
    have update : c.data = s.data.set (x.dst + i) (reg b value) writeBound := by
      simpa only [bDst, bIdx, dataB, a] using dataC
    rw [update]
    exact advanced
  have inc : code[c.pc]? = some (.add cursor cursor unit) := by
    rw [show c.pc = entry + 5 by omega]
    exact placed 5 _ rfl
  obtain ⟨d, hcd, pd, incReg, regsD, dataD⟩ :=
    step_add_at (input := input) inc (by omega)
  have idxD : (reg d cursor).val = i + 1 := by
    have idxC := congrArg Fin.val (cSame (r := cursor) (by decide) (by decide))
    have unitC := congrArg Fin.val (cSame (r := unit) (by decide) (by decide))
    rw [hs.cursor_val] at idxC
    rw [hs.unit_val] at unitC
    have hFit : (reg c cursor).val + (reg c unit).val < 2 ^ bits := by
      rw [idxC, unitC]
      have bound := x.count_fits
      omega
    rw [incReg, PaperB.WordOps.add_no_wrap _ _ hFit, idxC, unitC]
  let e := { d with pc := entry }
  have he : step code input d = some (.next e) := by
    have hf : code[d.pc]? = some (.goto entry) := by
      rw [show d.pc = entry + 6 by omega]
      exact placed 6 _ rfl
    exact step_goto_at hf (by omega)
  have same {r : Fin 7} (h : r ≠ cursor) (g : r ≠ address) (j : r ≠ value) :
      reg e r = reg s r := (regsD r h).trans (cSame g j)
  refine ⟨e, ?_, ⟨rfl, idxD, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have h₁ : Steps code input 1 s a := .cons ha (.zero a)
    have h₂ : Steps code input 1 c d := .cons hcd (.zero d)
    have h₃ : Steps code input 1 d e := .cons he (.zero e)
    exact h₁.append (hab.append (hbc.append (h₂.append h₃)))
  · rw [same (by decide) (by decide) (by decide), hs.limit_val]
  · rw [same (by decide) (by decide) (by decide), hs.source_val]
  · rw [same (by decide) (by decide) (by decide), hs.target_val]
  · rw [same (by decide) (by decide) (by decide), hs.unit_val]
  · change SliceCopy.Prefix orig d.data x.src x.dst (i + 1)
    rwa [dataD]

private theorem sevenIterations (n : Nat) :
    iterationCost (fun _ => 7) n = 7 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [iterationCost, ih, Nat.mul_succ]

/-- The copy takes exactly seven instructions per word and one exit
guard, including the zero-length case. All other data stays intact. -/
theorem copy_steps_with_target {x : Transfer bits workCap} {s : State (layout bits inputCap workCap hi hw)}
    {entry : Nat} (placed : Placed code entry (codeBlock entry))
    (exit_fits : entry + 7 < code.size)
    (initial : Invariant x s.data entry 0 s) :
    ∃ t, Steps code input (7 * x.count + 1) s t ∧ t.pc = entry + 7 ∧
      SliceCopy.Prefix s.data t.data x.src x.dst x.count ∧ (reg t target).val = x.dst := by
  have loop := loop_steps (code := code) (input := input)
    x.count (fun _ => 7) (Invariant x s.data entry)
    (fun _ below => iteration placed exit_fits below)
  obtain ⟨t, run, done⟩ := loop s initial
  have no : ltb (reg t cursor) (reg t limit) = false := by
    cases e : ltb (reg t cursor) (reg t limit) with
    | false => rfl
    | true =>
      have h := (PaperB.WordOps.ltb_eq_true _ _).mp e
      rw [done.cursor_val, done.limit_val] at h
      omega
  let u := { t with pc := entry + 7 }
  have stepOut : step code input t = some (.next u) := by
    have hf : code[t.pc]? = some (.branchLt cursor limit (entry + 1) (entry + 7)) := by
      rw [done.loopPC, ← Nat.add_zero entry]
      exact placed 0 _ rfl
    simpa [no, u] using
      step_branchLt_at (input := input) hf (by simpa [no] using exit_fits)
  rw [sevenIterations] at run
  exact ⟨u, run.append (.cons stepOut (.zero u)), rfl, done.copiedPrefix, done.target_val⟩

theorem copy_steps {x : Transfer bits workCap} {s : State (layout bits inputCap workCap hi hw)}
    {entry : Nat} (placed : Placed code entry (codeBlock entry))
    (exit_fits : entry + 7 < code.size)
    (initial : Invariant x s.data entry 0 s) :
    ∃ t, Steps code input (7 * x.count + 1) s t ∧ t.pc = entry + 7 ∧
      SliceCopy.Prefix s.data t.data x.src x.dst x.count := by
  obtain ⟨t, steps, pc, copied, _⟩ := copy_steps_with_target placed exit_fits initial
  exact ⟨t, steps, pc, copied⟩

def standalone (bits inputCap workCap : Nat) (hi : inputCap ≤ 2 ^ bits)
    (hw : workCap ≤ 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  (codeBlock 0 ++ [Instr.halt]).toArray

/-- The actual machine trace includes the final halt. Its peak includes
the whole arena (both banks), all seven registers and read-only input. -/
theorem standalone_exact_with_target (input : Input (layout bits inputCap workCap hi hw))
    (x : Transfer bits workCap) (s : State (layout bits inputCap workCap hi hw))
    (initial : Invariant x s.data 0 0 s) :
    ∃ t states,
      run (standalone bits inputCap workCap hi hw) input (7 * x.count + 2) s =
        some ⟨t, 7 * x.count + 2⟩ ∧
      SliceCopy.Prefix s.data t.data x.src x.dst x.count ∧
      SuccessfulTrace (standalone bits inputCap workCap hi hw) input s states
        ⟨t, 7 * x.count + 2⟩ ∧
      tracePeakWords input states = inputCap + workCap + 7 ∧ (reg t (3 : Fin 7)).val = x.dst := by
  let code := standalone bits inputCap workCap hi hw
  have placed : Placed code 0 (codeBlock 0) :=
    placed_link (L := layout bits inputCap workCap hi hw) [] (codeBlock 0) [Instr.halt]
  have hSize : code.size = 8 := rfl
  obtain ⟨t, hr, hp, hData, hTarget⟩ := copy_steps_with_target (input := input) placed (by omega) initial
  have stop : step code input t = some (.halted t) := by
    apply step_halt_at
    rw [hp]
    rfl
  have runEq : run code input (7 * x.count + 2) s = some ⟨t, 7 * x.count + 2⟩ :=
    hr.halts stop
  obtain ⟨states, ht⟩ := run_has_successfulTrace runEq
  exact ⟨t, states, runEq, hData, ht, ht.peak_eq, hTarget⟩

theorem standalone_exact (input : Input (layout bits inputCap workCap hi hw))
    (x : Transfer bits workCap) (s : State (layout bits inputCap workCap hi hw))
    (initial : Invariant x s.data 0 0 s) :
    ∃ t states,
      run (standalone bits inputCap workCap hi hw) input (7 * x.count + 2) s =
        some ⟨t, 7 * x.count + 2⟩ ∧
      SliceCopy.Prefix s.data t.data x.src x.dst x.count ∧
      SuccessfulTrace (standalone bits inputCap workCap hi hw) input s states
        ⟨t, 7 * x.count + 2⟩ ∧
      tracePeakWords input states = inputCap + workCap + 7 := by
  obtain ⟨t, states, exec, copied, trace, peak, _⟩ := standalone_exact_with_target input x s initial
  exact ⟨t, states, exec, copied, trace, peak⟩

end PaperB.RamSliceCopy

namespace PaperB.RetainedProperLoss

open PaperB.RamProgram
open PaperB.PairLookup.ColumnReduction.EX52Seal
open PaperB.RamSliceCopy (Transfer Invariant layout standalone standalone_exact)

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}

/-- The six columns returned by the existing compact constructor, in the
order used by the seal contract. -/
def WordColumns.sealBanks (w : WordColumns bits) : List (Bank bits) :=
  [w.dictionary, w.back.tagAndFirst, w.back.second, w.labels, w.entry, w.stop]

theorem WordColumns.sealBanks_cells (w : WordColumns bits) :
    cells w.sealBanks = w.wordCount := by
  simp only [WordColumns.sealBanks, cells, WordColumns.wordCount, Nat.add_zero]
  omega

/-- The last transfer of the serialized payload. The phase starts after the
six encoded columns have been staged at `x.src`. The logical array used
to specify their concatenation is only a proof argument. -/
theorem WordColumns.seal_payload_run (w : WordColumns bits)
    (x : Transfer bits workCap) (size : x.count = w.wordCount)
    (fit : cells w.sealBanks < 2 ^ bits)
    (input : Input (layout bits inputCap workCap hi hw))
    (s : State (layout bits inputCap workCap hi hw))
    (initial : Invariant x s.data 0 0 s)
    (staged : ∀ j < x.count,
      s.data[x.src + j]? = (serialize w.sealBanks fit).data[j]?) :
    ∃ t states,
      run (standalone bits inputCap workCap hi hw) input (7 * w.wordCount + 2) s =
        some ⟨t, 7 * w.wordCount + 2⟩ ∧
      (∀ q (hq : q < w.sealBanks.length) i (h : i < (w.sealBanks[q]'hq).size),
        t.data[x.dst + (offset w.sealBanks q + i)]? =
          some ((w.sealBanks[q]'hq)[i]'h)) ∧
      tracePeakWords input states = inputCap + workCap + 7 ∧
      SuccessfulTrace (standalone bits inputCap workCap hi hw) input s states
        ⟨t, 7 * w.wordCount + 2⟩ := by
  obtain ⟨t, states, hr, copied, trace, peak⟩ := standalone_exact input x s initial
  refine ⟨t, states, ?_, ?_, peak, ?_⟩
  · simpa only [size] using hr
  · intro q hq i h
    have hb := block_end w.sealBanks q hq
    rw [w.sealBanks_cells, ← size] at hb
    let j := offset w.sealBanks q + i
    have hj : j < x.count := by dsimp only [j]; omega
    have pos := seal_start w.sealBanks fit q (Nat.le_of_lt hq)
    have hs : j < (serialize w.sealBanks fit).data.size := by
      rw [seal_data_size, w.sealBanks_cells, ← size]
      exact hj
    have rd : (serialize w.sealBanks fit).data[j]'hs = (w.sealBanks[q]'hq)[i]'h := by
      have e := seal_read w.sealBanks fit q hq i h
      simp only [Packed.read, pos] at e
      exact e
    rw [copied.copied j hj, staged j hj, getElem?_pos (serialize w.sealBanks fit).data j hs, rd]
  · simpa only [size] using trace

end PaperB.RetainedProperLoss

namespace PaperB.ForestPreparedBuild

open PaperB.LabelledQuotient PaperB.RetainedProperLoss
open PaperB.ForestHead _root_.EX24.PreparedSweep

/-- The exact payload-copy instruction count is linear on the output
of the compact builder. The payload staging is a preceding phase. -/
theorem buildWordsFromOrder_seal_budget
    {H : LabelledQuotient} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {unique : data.toList.Nodup}
    {covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v}
    {topo : IsTopologicalOrder data size_data} {flat : H.IsFlat}
    {w : WordColumns (OracleContract.wordBits 5 H.vertexCount 0)}
    (h : buildWordsFromOrder data size_data unique covers topo flat = some w) :
    7 * w.wordCount + 2 ≤ 135 * H.vertexCount ∧
      2 * w.wordCount + 7 ≤ 45 * H.vertexCount := by
  have npos : 1 ≤ H.vertexCount := Nat.zero_lt_of_lt H.root.isLt
  have wide := buildWordsFromOrder_retained data size_data unique covers topo flat
  rw [h] at wide
  change w.wordCount ≤ 19 * H.vertexCount at wide
  omega

end PaperB.ForestPreparedBuild
