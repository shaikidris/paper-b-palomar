module

public import PaperB.RamForestKahn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.RawBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.ArcParents
open PaperB.RamForestProgram.ArcDecode
open PaperB.ForestHead (Vertex TestSpec)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open _root_.EX24.PreparedSweep (orderedVertexAt)

/-! ### Stage 1B helpers: `loadData`, `distinctProgram` mid-frame + stamp bound, and row-length mass -/

section Stage1BHelpers

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw
local notation "L15" => layout bits inputCap workCap hi hw

theorem step_loadData15 {code : Program L15} {input : Input L15} {s : State L15}
    {dst addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadData dst addr))
    (hread : s.data[(reg s addr).val]? = some w)
    (hnext : s.pc + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = s.pc + 1 ∧ reg t dst = w ∧
      (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data :=
  step_loadData_at hf hread hnext

private theorem distinctParams_keep {vertices arcs length : Nat}
    {b : DistinctBanks bits inputCap workCap vertices arcs length}
    {s t : State L} (p : DistinctParams b s)
    (keep : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
      r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk → reg t r = reg s r) :
    DistinctParams b t := by
  have val (r : Fin 15) (p₀ : r ≠ registers.ptr) (p₁ : r ≠ registers.remain)
      (p₂ : r ≠ registers.value) (p₃ : r ≠ registers.childBase) (p₄ : r ≠ registers.tmp)
      (p₅ : r ≠ clk) : (reg t r).val = (reg s r).val :=
    congrArg Fin.val (keep r p₀ p₁ p₂ p₃ p₄ p₅)
  exact ⟨⟨(val registers.stackBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.sourceBase,
      (val offsetBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.tokensBase,
      (val tinBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.stampsBase,
      (val cmd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.reader.shift⟩,
    (val count (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.total,
    (val childrenBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.outputBase,
    (val toutBase (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.epochVal,
    (val registers.one (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans p.unit⟩

private theorem distinctProgram_readerPlaced :
    Placed (distinctProgram (bits := bits) hi hw) 1 (readBlock (bits := bits)) := by
  intro i op h
  rcases i with _ | _ | _ | _ | _ | _ | _ | _
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · cases h; rfl
  · simp [readBlock, indexedDataRead, indexedInputRead] at h

private theorem distinctProgram_size :
    (distinctProgram (bits := bits) hi hw).size = 17 := rfl

private theorem distinctProgram_at_0 :
    (distinctProgram (bits := bits) hi hw)[0]? = some (.branchLt registers.ptr count 1 16) := rfl

private theorem distinctProgram_at_8 :
    (distinctProgram (bits := bits) hi hw)[8]? = some (.branchLt registers.childBase toutBase 9 14) := rfl

private theorem distinctProgram_markPlaced :
    Placed (distinctProgram (bits := bits) hi hw) 9
      (indexedDataWrite registers.tmp tinBase registers.value toutBase) := by
  intro i op h
  rcases i with _ | _ | _
  · cases h; rfl
  · cases h; rfl
  · simp [indexedDataWrite] at h

private theorem distinctProgram_outPlaced :
    Placed (distinctProgram (bits := bits) hi hw) 11
      (indexedDataWrite registers.tmp childrenBase clk registers.value) := by
  intro i op h
  rcases i with _ | _ | _
  · cases h; rfl
  · cases h; rfl
  · simp [indexedDataWrite] at h

private theorem distinctProgram_at_13 :
    (distinctProgram (bits := bits) hi hw)[13]? = some (.add clk clk registers.one) := rfl

private theorem distinctProgram_at_14 :
    (distinctProgram (bits := bits) hi hw)[14]? = some (.add registers.ptr registers.ptr registers.one) := rfl

private theorem distinctProgram_at_15 :
    (distinctProgram (bits := bits) hi hw)[15]? = some (.goto 0) := rfl

private theorem distinctProgram_at_16 :
    (distinctProgram (bits := bits) hi hw)[16]? = some .halt := rfl

private theorem distinctProgram_noEarlyHalt :
    ((distinctProgram (bits := bits) hi hw).toList.take 16).all (@nonHalt bits L) = true := rfl

private theorem distinctProgram_uniqueHalt (i : Nat)
    (h : (distinctProgram (bits := bits) hi hw)[i]? = some .halt) : i = 16 := by
  by_cases hi16 : i < 16
  · have cell : ((distinctProgram (bits := bits) hi hw).toList.take 16)[i]? = some .halt := by
      rw [List.getElem?_take_of_lt hi16, Array.getElem?_toList, h]
    have bad : @nonHalt bits L .halt = true :=
      List.all_eq_true.mp (distinctProgram_noEarlyHalt (hi := hi) (hw := hw)) _
        (List.mem_of_getElem? cell)
    cases bad
  · by_cases hlt : i < 17
    · omega
    · have gone : (distinctProgram (bits := bits) hi hw)[i]? = none :=
        getElem?_neg _ i (by rw [distinctProgram_size]; omega)
      rw [gone] at h
      cases h

private structure MidInv {vertices arcs length : Nat}
    (b : DistinctBanks bits inputCap workCap vertices arcs length)
    (row : Fin length → Fin arcs) (orig : Array (Word bits))
    (k : Nat) (s s0 : State L) : Prop where
  pc0 : s.pc = 0
  params : DistinctParams b s
  ptrVal : (reg s registers.ptr).val = k
  clkLe : (reg s clk).val ≤ k
  tokens : TokensAt (vertices := vertices) s.data b.read.tokens row
  stamps : ∀ v : Fin vertices, ∃ w : Word bits,
    s.data[b.read.stamps + v.val]? = some w ∧ w.val ≤ b.epoch
  midFrame : ∀ j,
    (j < b.read.stamps ∨ b.read.stamps + vertices ≤ j) →
    (j < b.output ∨ b.output + length ≤ j) →
    s.data[j]? = orig[j]?
  regs : ∀ r : Fin 15,
    r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
    r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk →
    reg s r = reg s0 r

private theorem distinctProgram_mid_step {vertices arcs length : Nat}
    (input : Input L) (b : DistinctBanks bits inputCap workCap vertices arcs length)
    (source : Fin arcs → Fin vertices) (row : Fin length → Fin arcs)
    (raw : SourcesAt input b.read.inputSource source) (s0 : State L)
    (k : Nat) (hk : k < length) (s : State L)
    (inv : MidInv b row s0.data k s s0) :
    ∃ t cost, cost ≤ 16 ∧ Steps (distinctProgram hi hw) input cost s t ∧
      MidInv b row s0.data (k + 1) t s0 := by
  let code := distinctProgram (bits := bits) hi hw
  have hSize : code.size = 17 := distinctProgram_size
  have hlt : ltb (reg s registers.ptr) (reg s count) = true :=
    branchLt_true (by rw [inv.ptrVal, inv.params.total]; exact hk)
  let u : State L := { s with pc := 1 }
  have su : step code input s = some (.next u) := by
    have h0 : code[s.pc]? = some (.branchLt registers.ptr count 1 16) := by
      rw [inv.pc0]; exact distinctProgram_at_0
    simpa only [u, hlt, ite_true] using
      step_branchLt_at (input := input) h0 (by rw [hlt, hSize]; decide)
  have uParams : DistinctParams b u := distinctParams_keep inv.params (fun _ _ _ _ _ _ _ => rfl)
  let idx : Fin length := ⟨k, hk⟩
  obtain ⟨v, uv, vpc, vm, _, tail, _, vr⟩ := readBlock_steps input source row raw
    distinctProgram_readerPlaced (by rw [hSize]; decide) u rfl uParams.reader inv.tokens idx inv.ptrVal
  have vParams : DistinctParams b v := distinctParams_keep uParams
    (fun r _ nr nv nc _ _ => vr r nr nv nc)
  have vPtr : (reg v registers.ptr).val = k :=
    (congrArg Fin.val (vr _ (by decide) (by decide) (by decide))).trans inv.ptrVal
  have vClk : (reg v clk).val ≤ k := by
    rw [vr _ (by decide) (by decide) (by decide)]
    exact inv.clkLe
  have vTokens : TokensAt (vertices := vertices) v.data b.read.tokens row := by
    change TokensAt (vertices := vertices) v.data b.read.tokens row
    rw [vm]; exact inv.tokens
  have vStamps : ∀ wv : Fin vertices, ∃ w : Word bits,
      v.data[b.read.stamps + wv.val]? = some w ∧ w.val ≤ b.epoch := by
    intro wv; rw [vm]; exact inv.stamps wv
  have vMidFrame : ∀ j, (j < b.read.stamps ∨ b.read.stamps + vertices ≤ j) →
      (j < b.output ∨ b.output + length ≤ j) → v.data[j]? = s0.data[j]? := by
    intro j hj1 hj2; rw [vm]; exact inv.midFrame j hj1 hj2
  have vRegs : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
      r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk → reg v r = reg s0 r := by
    intro r hp hr hv hc ht hk0
    exact (vr r hr hv hc).trans (inv.regs r hp hr hv hc ht hk0)
  have h8 : code[v.pc]? = some (.branchLt registers.childBase toutBase 9 14) := by
    rw [vpc]; exact distinctProgram_at_8
  have hBody : ∃ (y : State L) (w : Nat), w ≤ 6 ∧ Steps code input w v y ∧ y.pc = 14 ∧
      DistinctParams b y ∧ (reg y registers.ptr).val = k ∧ (reg y clk).val ≤ k + 1 ∧
      TokensAt (vertices := vertices) y.data b.read.tokens row ∧
      (∀ wv : Fin vertices, ∃ w : Word bits,
        y.data[b.read.stamps + wv.val]? = some w ∧ w.val ≤ b.epoch) ∧
      (∀ j, (j < b.read.stamps ∨ b.read.stamps + vertices ≤ j) →
        (j < b.output ∨ b.output + length ≤ j) → y.data[j]? = s0.data[j]?) ∧
      (∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
        r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk → reg y r = reg s0 r) := by
    by_cases hcb : (reg v registers.childBase).val < (reg v toutBase).val
    · have yes : ltb (reg v registers.childBase) (reg v toutBase) = true := branchLt_true hcb
      let y0 : State L := { v with pc := 9 }
      have vy0 : step code input v = some (.next y0) := by
        simpa only [y0, yes, ite_true] using step_branchLt_at (input := input) h8
          (by rw [yes, hSize]; decide)
      have y0St : (reg y0 tinBase).val = b.read.stamps := vParams.reader.stampsBase
      have y0Val : (reg y0 registers.value).val = (source (row idx)).val := tail
      have y0Clk : (reg y0 clk).val = (reg v clk).val := rfl
      have fitStamp : (reg y0 tinBase).val + (reg y0 registers.value).val < workCap := by
        have hltV := (source (row idx)).isLt
        have hstFit := b.read.stampsFit
        rw [y0St, y0Val]; omega
      obtain ⟨y1, y01, p1, w1, _, d1⟩ := indexedDataWrite15 (code := code) (input := input)
        (s := y0) distinctProgram_markPlaced rfl (by rw [hSize]; decide) (by decide) fitStamp
      have y1Out : (reg y1 childrenBase).val = b.output := by
        rw [d1 _ (by decide)]; exact vParams.outputBase
      have y1Clk : (reg y1 clk).val = (reg v clk).val := by
        rw [d1 _ (by decide)]; exact y0Clk
      have fitOut : (reg y1 childrenBase).val + (reg y1 clk).val < workCap := by
        have houtFit := b.outputFits
        rw [y1Out, y1Clk]; omega
      obtain ⟨y2, y12, p2, w2, _, d2⟩ := indexedDataWrite15 (code := code) (input := input)
        (s := y1) distinctProgram_outPlaced p1 (by rw [hSize]; decide) (by decide) fitOut
      have h13 : code[y2.pc]? = some (.add clk clk registers.one) := by
        rw [p2]; exact distinctProgram_at_13
      obtain ⟨y3, y23, p3, c3, r3, d3⟩ := step_add15 (code := code) (input := input) (s := y2) h13
        (by rw [p2, hSize]; decide)
      have y2Params : DistinctParams b y2 :=
        distinctParams_keep vParams (fun r _ _ _ _ ht _ =>
          (d2 r ht).trans (d1 r ht))
      have y3Params : DistinctParams b y3 :=
        distinctParams_keep y2Params (fun r _ _ _ _ _ hk0 => r3 r hk0)
      have y3Ptr : (reg y3 registers.ptr).val = k := by
        rw [r3 _ (by decide), d2 _ (by decide), d1 _ (by decide)]; exact vPtr
      have y2Clk : (reg y2 clk).val = (reg v clk).val := by
        rw [d2 _ (by decide)]; exact y1Clk
      have y2One : (reg y2 registers.one).val = 1 := y2Params.unit
      have cFit : (reg y2 clk).val + (reg y2 registers.one).val < 2 ^ bits := by
        have hlen := (reg v count).isLt
        rw [vParams.total] at hlen
        rw [y2Clk, y2One]; omega
      have y3Clk : (reg y3 clk).val ≤ k + 1 := by
        rw [c3, add_no_wrap _ _ cFit, y2Clk, y2One]; omega
      have keep12 (j : Nat) (hj1 : j ≠ b.read.stamps + (source (row idx)).val)
          (hj2 : j ≠ b.output + (reg v clk).val) : y3.data[j]? = v.data[j]? := by
        rw [d3, w2, Array.getElem?_set_ne _ (by rw [y1Out, y1Clk]; exact hj2.symm),
          w1, Array.getElem?_set_ne _ (by rw [y0St, y0Val]; exact hj1.symm)]
      have y3Tokens : TokensAt (vertices := vertices) y3.data b.read.tokens row := by
        intro q
        have hrb := b.rowsBeforeStamps
        have hso := b.stampsBeforeOutput
        have hq := q.isLt
        rw [keep12 _ (by omega) (by omega)]
        exact vTokens q
      have y3Stamps : ∀ wv : Fin vertices, ∃ w : Word bits,
          y3.data[b.read.stamps + wv.val]? = some w ∧ w.val ≤ b.epoch := by
        intro wv
        by_cases hweq : wv = source (row idx)
        · subst wv
          have hmem : y1.data[b.read.stamps + (source (row idx)).val]? = some (reg y0 toutBase) := by
            rw [w1, ← y0St, ← y0Val, Array.getElem?_set_self]
          have hjneq : b.read.stamps + (source (row idx)).val ≠ b.output + (reg v clk).val := by
            have hso := b.stampsBeforeOutput
            have hvlt := (source (row idx)).isLt
            omega
          have hmem3 : y3.data[b.read.stamps + (source (row idx)).val]? = some (reg y0 toutBase) := by
            rw [d3, w2, Array.getElem?_set_ne _ (by rw [y1Out, y1Clk]; exact hjneq.symm), hmem]
          refine ⟨reg y0 toutBase, hmem3, ?_⟩
          change (reg v toutBase).val ≤ b.epoch
          rw [vParams.epochVal]
          exact Nat.le_refl _
        · have hj1 : b.read.stamps + wv.val ≠ b.read.stamps + (source (row idx)).val := by
            intro heq; apply hweq; apply Fin.ext; omega
          have hj2 : b.read.stamps + wv.val ≠ b.output + (reg v clk).val := by
            have hso := b.stampsBeforeOutput
            have hvlt := wv.isLt
            omega
          rw [keep12 _ hj1 hj2]
          exact vStamps wv
      have y3MidFrame : ∀ j, (j < b.read.stamps ∨ b.read.stamps + vertices ≤ j) →
          (j < b.output ∨ b.output + length ≤ j) → y3.data[j]? = s0.data[j]? := by
        intro j hj1 hj2
        have hvlt := (source (row idx)).isLt
        rw [keep12 _ (by omega) (by omega)]
        exact vMidFrame j hj1 hj2
      have y3Regs : ∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
          r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk → reg y3 r = reg s0 r := by
        intro r hp hr hv hc ht hk0
        rw [r3 r hk0, d2 r ht, d1 r ht]
        exact vRegs r hp hr hv hc ht hk0
      exact ⟨y3, 6, Nat.le_refl _, .cons vy0 (y01.append (y12.append (.cons y23 (.zero y3)))),
        by rw [p3, p2], y3Params, y3Ptr, y3Clk, y3Tokens, y3Stamps, y3MidFrame, y3Regs⟩
    · have no : ltb (reg v registers.childBase) (reg v toutBase) = false :=
        branchLt_false (by omega)
      let y : State L := { v with pc := 14 }
      have vy : step code input v = some (.next y) := by
        simpa only [y, no, Bool.false_eq_true, ite_false] using
          step_branchLt_at (input := input) h8 (by rw [no, hSize]; decide)
      exact ⟨y, 1, by decide, .cons vy (.zero y), rfl,
        distinctParams_keep vParams (fun _ _ _ _ _ _ _ => rfl), vPtr,
        by change (reg v clk).val ≤ k + 1; omega,
        vTokens, vStamps, vMidFrame, vRegs⟩
  obtain ⟨y, w, hw6, vy, ypc, yParams, yPtr, yClk, yTokens, yStamps, yMidFrame, yRegs⟩ := hBody
  have h14 : code[y.pc]? = some (.add registers.ptr registers.ptr registers.one) := by
    rw [ypc]; exact distinctProgram_at_14
  obtain ⟨z, yz, zpc, zPtr, zr, zm⟩ := step_add15 (code := code) (input := input) h14
    (by rw [ypc, hSize]; decide)
  have h15 : code[z.pc]? = some (.goto 0) := by
    rw [zpc, ypc]; exact distinctProgram_at_15
  let t : State L := { z with pc := 0 }
  have zt : step code input z = some (.next t) :=
    step_goto_at h15 (by rw [hSize]; decide)
  have lenFit := (reg y count).isLt
  rw [yParams.total] at lenFit
  have ptrFit : (reg y registers.ptr).val + (reg y registers.one).val < 2 ^ bits := by
    rw [yPtr, yParams.unit]; omega
  have hSteps : Steps code input (1 + (7 + (w + 1 + 1))) s t := by
    have hRaw := Steps.cons su (uv.append (vy.append (.cons yz (.cons zt (.zero t)))))
    change Steps code input (7 + (w + 2) + 1) s t at hRaw
    rwa [show 1 + (7 + (w + 1 + 1)) = 7 + (w + 2) + 1 by omega]
  refine ⟨t, 1 + (7 + (w + 1 + 1)), by omega, hSteps, ?_⟩
  refine ⟨rfl, distinctParams_keep yParams (fun r hp _ _ _ _ _ => zr r hp), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (reg z registers.ptr).val = k + 1
    rw [zPtr, add_no_wrap _ _ ptrFit, yPtr, yParams.unit]
  · change (reg z clk).val ≤ k + 1
    rw [zr _ (by decide)]; exact yClk
  · change TokensAt (vertices := vertices) z.data b.read.tokens row
    rw [zm]; exact yTokens
  · intro v; change ∃ w, z.data[b.read.stamps + v.val]? = some w ∧ w.val ≤ b.epoch
    rw [zm]; exact yStamps v
  · intro j hj1 hj2; change z.data[j]? = s0.data[j]?
    rw [zm]; exact yMidFrame j hj1 hj2
  · intro r hp hr hv hc ht hk0
    exact (zr r hp).trans (yRegs r hp hr hv hc ht hk0)

/-- Full distinct-row specification extending `run_distinct_row` with stamp upper bounds,
middle-arena framing outside `[stamps, stamps + vertices) ∪ [output, output + length)`,
and preserved control/base registers. -/
theorem run_distinct_row_full {vertices arcs length : Nat} (input : Input L)
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
      (∀ v : Fin vertices, ∃ w : Word bits, t.data[b.read.stamps + v.val]? = some w ∧ w.val ≤ b.epoch) ∧
      (∀ j, (j < b.read.stamps ∨ b.read.stamps + vertices ≤ j) →
        (j < b.output ∨ b.output + length ≤ j) → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ registers.ptr → r ≠ registers.remain → r ≠ registers.value →
        r ≠ registers.childBase → r ≠ registers.tmp → r ≠ clk → reg t r = reg s r) ∧
      SuccessfulTrace (distinctProgram hi hw) input s trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨t, trace, work, out, hwBound, hRun, hClk, hNodup, hLen, hMem, hOut, _, hST, hPeak⟩ :=
    run_distinct_row input b source row raw s pc params cursor empty tokens older
  have hStart : MidInv b row s.data 0 s s :=
    ⟨pc, params, cursor, by omega, tokens,
      fun v => by obtain ⟨w, hmw, hlt⟩ := older v; exact ⟨w, hmw, Nat.le_of_lt hlt⟩,
      fun _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  have hIter : ∀ k, k ≤ length → ∃ q w, w ≤ 16 * k ∧
      Steps (distinctProgram hi hw) input w s q ∧ MidInv b row s.data k q s := by
    intro k hk
    induction k with
    | zero => exact ⟨s, 0, Nat.le_refl 0, .zero s, hStart⟩
    | succ k ih =>
      obtain ⟨q, w, hw, sq, hInv⟩ := ih (by omega)
      obtain ⟨q', w', hw', qq', hInv'⟩ :=
        distinctProgram_mid_step input b source row raw s k (by omega) q hInv
      exact ⟨q', w + w', by omega, sq.append qq', hInv'⟩
  obtain ⟨q, w, _, sq, hInv⟩ := hIter length (Nat.le_refl _)
  have no : ltb (reg q registers.ptr) (reg q count) = false :=
    branchLt_false (by rw [hInv.ptrVal, hInv.params.total]; exact Nat.le_refl _)
  let t' : State L := { q with pc := 16 }
  have qt' : step (distinctProgram hi hw) input q = some (.next t') := by
    have h0 : (distinctProgram (bits := bits) hi hw)[q.pc]? =
        some (.branchLt registers.ptr count 1 16) := by
      rw [hInv.pc0]; exact distinctProgram_at_0
    simpa only [t', no, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) h0 (by rw [no, distinctProgram_size]; decide)
  have hRun' : run (distinctProgram hi hw) input (w + 2) s = some ⟨t', w + 2⟩ :=
    (sq.append (.cons qt' (.zero t'))).halts (step_halt_at distinctProgram_at_16)
  have hResEq : (⟨t, work⟩ : Result L) = ⟨t', w + 2⟩ := run_success_unique hRun hRun'
  have htEq : t = t' := congrArg Result.finalState hResEq
  refine ⟨t, trace, work, out, hwBound, hRun, hClk, hNodup, hLen, hMem, hOut, ?_, ?_, ?_, hST, hPeak⟩
  · rw [htEq]; exact hInv.stamps
  · rw [htEq]; exact hInv.midFrame
  · rw [htEq]; exact hInv.regs

private theorem nodup_subset_length_le {α : Type} [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup → (∀ x, x ∈ xs → x ∈ ys) → xs.length ≤ ys.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, ys, hnd, hsub => by
    have hnd' := List.pairwise_cons.mp hnd
    have hx : x ∈ ys := hsub x (by simp)
    have hlen : xs.length ≤ (ys.erase x).length := by
      apply nodup_subset_length_le xs (ys.erase x) hnd'.2
      intro z hz
      have hne : z ≠ x := fun heq => hnd'.1 z hz heq.symm
      exact List.mem_erase_of_ne hne |>.mpr (hsub z (by simp [hz]))
    have her : (ys.erase x).length = ys.length - 1 := List.length_erase_of_mem hx
    have hpos : 0 < ys.length := List.length_pos_of_mem hx
    simp only [List.length_cons]
    omega

private def sumRowLenAux {vertices arcs : Nat} (heads : Fin arcs → Fin vertices) :
    Nat → Nat
  | 0 => 0
  | k + 1 =>
    if hk : k < vertices then
      sumRowLenAux heads k + (rowNodes heads ⟨k, hk⟩).length
    else sumRowLenAux heads k

private def flatRowNodesAux {vertices arcs : Nat} (heads : Fin arcs → Fin vertices) :
    Nat → List (Fin (vertices + 1 + arcs))
  | 0 => []
  | k + 1 =>
    if hk : k < vertices then
      flatRowNodesAux heads k ++ rowNodes heads ⟨k, hk⟩
    else flatRowNodesAux heads k

private theorem flatRowNodesAux_length {vertices arcs : Nat} (heads : Fin arcs → Fin vertices)
    (k : Nat) : (flatRowNodesAux heads k).length = sumRowLenAux heads k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    by_cases hk : k < vertices
    · simp [flatRowNodesAux, sumRowLenAux, hk, ih]
    · simp [flatRowNodesAux, sumRowLenAux, hk, ih]

private theorem flatRowNodesAux_spec {vertices arcs : Nat} (heads : Fin arcs → Fin vertices)
    (k : Nat) :
    (flatRowNodesAux heads k).Nodup ∧
    ∀ u, u ∈ flatRowNodesAux heads k →
      ∃ e : Fin arcs, u = arcNode vertices e ∧ (heads e).val < k := by
  induction k with
  | zero => exact ⟨List.nodup_nil, fun _ h => by simp [flatRowNodesAux] at h⟩
  | succ k ih =>
    by_cases hk : k < vertices
    · have ⟨ihNd, ihMem⟩ := ih
      have hNdRow := rowNodes_nodup heads ⟨k, hk⟩
      have hDisj : ∀ u, u ∈ flatRowNodesAux heads k → u ∉ rowNodes heads ⟨k, hk⟩ := by
        intro u hu1 hu2
        obtain ⟨e, heu, hlt⟩ := ihMem u hu1
        obtain ⟨e', he'u, hhe'⟩ := rowNodes_are_arcs heads ⟨k, hk⟩ u hu2
        have eqNode : arcNode vertices e = arcNode vertices e' := heu.symm.trans he'u
        have eqe : e = e' := Fin.ext (by
          have hv := congrArg Fin.val eqNode
          change vertices + 1 + e.val = vertices + 1 + e'.val at hv
          omega)
        rw [eqe, hhe'] at hlt
        exact Nat.lt_irrefl k hlt
      refine ⟨?_, ?_⟩
      · simp only [flatRowNodesAux, hk, dite_true, List.nodup_append]
        exact ⟨ihNd, hNdRow, fun a ha b hb heq => hDisj a ha (heq ▸ hb)⟩
      · intro u hu
        simp only [flatRowNodesAux, hk, dite_true, List.mem_append] at hu
        rcases hu with hu | hu
        · obtain ⟨e, heu, hlt⟩ := ihMem u hu
          exact ⟨e, heu, Nat.lt_succ_of_lt hlt⟩
        · obtain ⟨e, heu, hhe⟩ := rowNodes_are_arcs heads ⟨k, hk⟩ u hu
          exact ⟨e, heu, by rw [hhe]; exact Nat.lt_succ_self k⟩
    · simp only [flatRowNodesAux, hk, dite_false]
      exact ⟨ih.1, fun u hu => by
        obtain ⟨e, heu, hlt⟩ := ih.2 u hu
        exact ⟨e, heu, Nat.lt_succ_of_lt hlt⟩⟩

private theorem sumRowLen_le_arcs {vertices arcs : Nat} (heads : Fin arcs → Fin vertices)
    (k : Nat) : sumRowLenAux heads k ≤ arcs := by
  rw [← flatRowNodesAux_length]
  have hSpec := flatRowNodesAux_spec heads k
  have hSub : ∀ u, u ∈ flatRowNodesAux heads k →
      u ∈ (List.finRange arcs).map (arcNode vertices) := by
    intro u hu
    obtain ⟨e, heu, _⟩ := hSpec.2 u hu
    rw [heu, List.mem_map]
    exact ⟨e, List.mem_finRange e, rfl⟩
  have hLen := nodup_subset_length_le (flatRowNodesAux heads k)
    ((List.finRange arcs).map (arcNode vertices)) hSpec.1 hSub
  simpa only [List.length_map, List.length_finRange] using hLen

end Stage1BHelpers

/-! ### Stage 1B Phases: Incoming CSR + Stamp Zeroing + All-Row Distinct Predecessor Schedule -/

section Stage1BPhases

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

private def initIncomingCsrRegsList (h1 : 1 < 2 ^ bits) (h3 : 3 < 2 ^ bits) : List (Instr bits 15) :=
  [ .imm registers.zero ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.one ⟨1, h1⟩,
    .imm registers.ptr ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.stackBase ⟨0, Nat.two_pow_pos bits⟩,
    .imm cmd ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.childBase ⟨3, h3⟩,
    .loadInput registers.value registers.zero,
    .loadInput registers.remain registers.one,
    .add registers.childBase registers.childBase registers.remain,
    .add clk registers.value registers.one,
    .add count clk registers.remain,
    .add tinBase count count,
    .add toutBase tinBase count,
    .add offsetBase toutBase count,
    .add childrenBase offsetBase count,
    .add childrenBase childrenBase registers.one,
    .halt ]

/-- Initialize registers for `rawIncomingPhase` on `HeadsAt input (3 + m) (rawHead H)`. -/
def initIncomingCsrRegsPhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (initIncomingCsrRegsList (by omega) (by omega)).toArray 16 rfl rfl rfl

theorem run_initIncomingCsrRegs (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State L) :
    let n := H.vertexCount
    let m := H.arcCount
    let K := n + 1 + m
    let a : Arena bits workCap K :=
      ⟨0, n + m, by unfold rawWorkCap at workRoom; omega,
        by have := Nat.lt_of_lt_of_le (show 0 + 5 * K + 1 + (n + m) < rawWorkCap n m by
            unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
           exact this⟩
    ∃ t : State L,
      run (initIncomingCsrRegsPhase (hi := hi) (hw := hw) (by
        exact Nat.le_trans (show 4 ≤ rawWorkCap n m by unfold rawWorkCap; omega)
          (Nat.le_trans workRoom hw))).code input 17 (Phase.initial s) = some ⟨t, 17⟩ ∧
      ParentCursor a (root n m) 0 t ∧
      (reg t clk).val = n + 1 ∧
      (reg t registers.childBase).val = 3 + m ∧
      t.data = s.data := by
  intro n m K a
  have h4 : 4 ≤ 2 ^ bits :=
    Nat.le_trans (show 4 ≤ rawWorkCap n m by unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
  let code := (initIncomingCsrRegsPhase (hi := hi) (hw := hw) h4).code
  have hSize : code.size = 17 := rfl
  have h5K1 : 5 * K + 1 < 2 ^ bits :=
    Nat.lt_of_lt_of_le (show 5 * K + 1 < rawWorkCap n m by unfold rawWorkCap; omega)
      (Nat.le_trans workRoom hw)
  have h3m : 3 + m < 2 ^ bits := by
    have := raw.cap_ge; unfold rawInputCap at this; omega
  have hnWord : ∃ wn, input.words[0]? = some wn ∧ wn.val = n := by
    cases hw0 : input.words[0]? with
    | none => have h := raw.hdr_n; simp [hw0] at h
    | some w => have h := raw.hdr_n; simp [hw0] at h; exact ⟨w, rfl, h⟩
  have hmWord : ∃ wm, input.words[1]? = some wm ∧ wm.val = m := by
    cases hw1 : input.words[1]? with
    | none => have h := raw.hdr_m; simp [hw1] at h
    | some w => have h := raw.hdr_m; simp [hw1] at h; exact ⟨w, rfl, h⟩
  obtain ⟨wn, hwn, hwnV⟩ := hnWord
  obtain ⟨wm, hwm, hwmV⟩ := hmWord
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1z, fr1, d1⟩ := step_imm15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2o, fr2, d2⟩ := step_imm15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3p, fr3, d3⟩ := step_imm15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  obtain ⟨s4, hs34, p4, r4s, fr4, d4⟩ := step_imm15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s5, hs45, p5, r5c, fr5, d5⟩ := step_imm15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s6, hs56, p6, r6cb, fr6, d6⟩ := step_imm15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, p1]; rfl) (by rw [p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hZero6 : (reg s6 registers.zero).val = 0 := by
    rw [fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide),
      fr2 _ (by decide), r1z]
  have hOne6 : (reg s6 registers.one).val = 1 := by
    rw [fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), r2o]
  obtain ⟨s7, hs67, p7, r7n, fr7, d7⟩ := step_loadInput15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p6, p5, p4, p3, p2, p1, hSize, s0]; omega) (by rw [hZero6]; exact hwn)
  have hOne7 : (reg s7 registers.one).val = 1 := by rw [fr7 _ (by decide), hOne6]
  obtain ⟨s8, hs78, p8, r8m, fr8, d8⟩ := step_loadInput15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega) (by rw [hOne7]; exact hwm)
  obtain ⟨s9, hs89, p9, r9cb, fr9, d9⟩ := step_add15 (code := code) (input := input)
    (s := s8) (by rw [p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s10, hs910, p10, r10clk, fr10, d10⟩ := step_add15 (code := code) (input := input)
    (s := s9) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s11, hs1011, p11, r11cnt, fr11, d11⟩ := step_add15 (code := code) (input := input)
    (s := s10) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s12, hs1112, p12, r12tin, fr12, d12⟩ := step_add15 (code := code) (input := input)
    (s := s11) (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s13, hs1213, p13, r13tout, fr13, d13⟩ := step_add15 (code := code) (input := input)
    (s := s12) (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s14, hs1314, p14, r14off, fr14, d14⟩ := step_add15 (code := code) (input := input)
    (s := s13) (by rw [p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s15, hs1415, p15, r15cb, fr15, d15⟩ := step_add15 (code := code) (input := input)
    (s := s14) (by rw [p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s16, hs1516, p16, r16cb, fr16, d16⟩ := step_add15 (code := code) (input := input)
    (s := s15) (by rw [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 16 (Phase.initial s) s16 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67
      (.cons hs78 (.cons hs89 (.cons hs910 (.cons hs1011 (.cons hs1112 (.cons hs1213
        (.cons hs1314 (.cons hs1415 (.cons hs1516 (.zero s16))))))))))))))))
  have halt : step code input s16 = some (.halted s16) :=
    step_halt_at (by rw [p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
  have exec := hSteps.halts halt
  have vZero : (reg s16 registers.zero).val = 0 := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), hZero6]
  have vOne : (reg s16 registers.one).val = 1 := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), hOne7]
  have vPtr : (reg s16 registers.ptr).val = 0 := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), r3p]
  have vStack : (reg s16 registers.stackBase).val = 0 := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide), r4s]
  have vCmd : (reg s16 cmd).val = 0 := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), r5c]
  have vCb8 : (reg s8 registers.childBase).val = 3 := by
    rw [fr8 _ (by decide), fr7 _ (by decide), r6cb]
  have vRem8 : (reg s8 registers.remain).val = m := by rw [r8m, hwmV]
  have vCb9 : (reg s9 registers.childBase).val = 3 + m := by
    rw [r9cb, add_no_wrap _ _ (by rw [vCb8, vRem8]; exact h3m), vCb8, vRem8]
  have vChildBase : (reg s16 registers.childBase).val = 3 + m := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), vCb9]
  have vVal9 : (reg s9 registers.value).val = n := by
    rw [fr9 _ (by decide), fr8 _ (by decide), r7n, hwnV]
  have vOne9 : (reg s9 registers.one).val = 1 := by
    rw [fr9 _ (by decide), fr8 _ (by decide), hOne7]
  have vClk10 : (reg s10 clk).val = n + 1 := by
    rw [r10clk, add_no_wrap _ _ (by rw [vVal9, vOne9]; omega), vVal9, vOne9]
  have vRemain10 : (reg s10 registers.remain).val = m := by
    rw [fr10 _ (by decide), fr9 _ (by decide), vRem8]
  have vCnt11 : (reg s11 count).val = K := by
    rw [r11cnt, add_no_wrap _ _ (by rw [vClk10, vRemain10]; change K < 2 ^ bits; omega),
      vClk10, vRemain10]
  have vTin12 : (reg s12 tinBase).val = 2 * K := by
    rw [r12tin, add_no_wrap _ _ (by rw [vCnt11]; omega), vCnt11]; omega
  have vCnt12 : (reg s12 count).val = K := by rw [fr12 _ (by decide), vCnt11]
  have vTout13 : (reg s13 toutBase).val = 3 * K := by
    rw [r13tout, add_no_wrap _ _ (by rw [vTin12, vCnt12]; omega), vTin12, vCnt12]; omega
  have vCnt13 : (reg s13 count).val = K := by rw [fr13 _ (by decide), vCnt12]
  have vOff14 : (reg s14 offsetBase).val = 4 * K := by
    rw [r14off, add_no_wrap _ _ (by rw [vTout13, vCnt13]; omega), vTout13, vCnt13]; omega
  have vCnt14 : (reg s14 count).val = K := by rw [fr14 _ (by decide), vCnt13]
  have vCb15 : (reg s15 childrenBase).val = 5 * K := by
    rw [r15cb, add_no_wrap _ _ (by rw [vOff14, vCnt14]; omega), vOff14, vCnt14]; omega
  have vOne15 : (reg s15 registers.one).val = 1 := by
    rw [fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide),
      fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), hOne7]
  have vCb16_raw : (reg s16 childrenBase).val = 5 * K + 1 := by
    rw [r16cb, add_no_wrap _ _ (by rw [vCb15, vOne15]; omega), vCb15, vOne15]
  have vCb16 : (reg s16 childrenBase).val = a.payload := by
    simpa only [Arena.payload, a, Nat.zero_add] using vCb16_raw
  have vClk : (reg s16 clk).val = n + 1 := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), fr11 _ (by decide), vClk10]
  have vCnt : (reg s16 count).val = K := by
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      fr12 _ (by decide), vCnt11]
  have vTin : (reg s16 tinBase).val = a.tin := by
    change (reg s16 tinBase).val = 0 + 2 * K
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
      vTin12, Nat.zero_add]
  have vTout : (reg s16 toutBase).val = a.tout := by
    change (reg s16 toutBase).val = 0 + 3 * K
    rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), vTout13, Nat.zero_add]
  have vOff : (reg s16 offsetBase).val = a.offsets := by
    change (reg s16 offsetBase).val = 0 + 4 * K
    rw [fr16 _ (by decide), fr15 _ (by decide), vOff14, Nat.zero_add]
  have vData : s16.data = s.data :=
    d16.trans (d15.trans (d14.trans (d13.trans (d12.trans (d11.trans (d10.trans (d9.trans
      (d8.trans (d7.trans (d6.trans (d5.trans (d4.trans (d3.trans (d2.trans d1))))))))))))))
  refine ⟨s16, exec, ⟨⟨vCnt, vOne, vZero, vStack, vTin, vTout, vOff, vCb16⟩, vCmd, vPtr⟩,
    vClk, vChildBase, vData⟩

private def initStampsSetupList (h1 : 1 < 2 ^ bits) : List (Instr bits 15) :=
  [ .imm registers.zero ⟨0, Nat.two_pow_pos bits⟩,
    .imm registers.one ⟨1, h1⟩,
    .imm registers.ptr ⟨0, Nat.two_pow_pos bits⟩,
    .loadInput count registers.zero,
    .loadInput registers.remain registers.one,
    .add registers.tmp count registers.remain,
    .add registers.tmp registers.tmp registers.one,
    .add tinBase registers.tmp registers.tmp,
    .add registers.value tinBase registers.tmp,
    .add tinBase registers.value registers.value,
    .add tinBase tinBase registers.one,
    .add tinBase tinBase count,
    .halt ]

/-- Set `tinBase := stampsBase n m`, `count := n`, `ptr := 0`, `zero := 0`, `one := 1`. -/
def initStampsSetupPhase (hbits : 2 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (initStampsSetupList (by omega)).toArray 12 rfl rfl rfl

theorem run_initStampsSetup (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State L) :
    ∃ t : State L,
      run (initStampsSetupPhase (hi := hi) (hw := hw) (by
        exact Nat.le_trans (show 2 ≤ rawWorkCap H.vertexCount H.arcCount by unfold rawWorkCap; omega)
          (Nat.le_trans workRoom hw))).code input 13 (Phase.initial s) = some ⟨t, 13⟩ ∧
      ZeroBankParams (stampsBase H.vertexCount H.arcCount) H.vertexCount t ∧
      t.data = s.data := by
  let n := H.vertexCount
  let m := H.arcCount
  have h2 : 2 ≤ 2 ^ bits :=
    Nat.le_trans (show 2 ≤ rawWorkCap n m by unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
  let code := (initStampsSetupPhase (hi := hi) (hw := hw) h2).code
  have hSize : code.size = 13 := rfl
  have hBound : 7 * n + 6 * m + 7 < 2 ^ bits :=
    Nat.lt_of_lt_of_le (show 7 * n + 6 * m + 7 < rawWorkCap n m by unfold rawWorkCap; omega)
      (Nat.le_trans workRoom hw)
  have hnWord : ∃ wn, input.words[0]? = some wn ∧ wn.val = n := by
    cases hw0 : input.words[0]? with
    | none => have h := raw.hdr_n; simp [hw0] at h
    | some w => have h := raw.hdr_n; simp [hw0] at h; exact ⟨w, rfl, h⟩
  have hmWord : ∃ wm, input.words[1]? = some wm ∧ wm.val = m := by
    cases hw1 : input.words[1]? with
    | none => have h := raw.hdr_m; simp [hw1] at h
    | some w => have h := raw.hdr_m; simp [hw1] at h; exact ⟨w, rfl, h⟩
  obtain ⟨wn, hwn, hwnV⟩ := hnWord
  obtain ⟨wm, hwm, hwmV⟩ := hmWord
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1z, fr1, d1⟩ := step_imm15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2o, fr2, d2⟩ := step_imm15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3p, fr3, d3⟩ := step_imm15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  have hZ3 : (reg s3 registers.zero).val = 0 := by rw [fr3 _ (by decide), fr2 _ (by decide), r1z]
  have hO3 : (reg s3 registers.one).val = 1 := by rw [fr3 _ (by decide), r2o]
  obtain ⟨s4, hs34, p4, r4n, fr4, d4⟩ := step_loadInput15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
    (by rw [hZ3]; exact hwn)
  have hO4 : (reg s4 registers.one).val = 1 := by rw [fr4 _ (by decide), hO3]
  obtain ⟨s5, hs45, p5, r5m, fr5, d5⟩ := step_loadInput15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
    (by rw [hO4]; exact hwm)
  obtain ⟨s6, hs56, p6, r6tmp, fr6, d6⟩ := step_add15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, p1]; rfl) (by rw [p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s7, hs67, p7, r7tmp, fr7, d7⟩ := step_add15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, p1]; rfl) (by rw [p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s8, hs78, p8, r8tin, fr8, d8⟩ := step_add15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, p1]; rfl) (by rw [p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s9, hs89, p9, r9val, fr9, d9⟩ := step_add15 (code := code) (input := input)
    (s := s8) (by rw [p8, p7, p6, p5, p4, p3, p2, p1]; rfl) (by rw [p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s10, hs910, p10, r10tin, fr10, d10⟩ := step_add15 (code := code) (input := input)
    (s := s9) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s11, hs1011, p11, r11tin, fr11, d11⟩ := step_add15 (code := code) (input := input)
    (s := s10) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s12, hs1112, p12, r12tin, fr12, d12⟩ := step_add15 (code := code) (input := input)
    (s := s11) (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 12 (Phase.initial s) s12 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67
      (.cons hs78 (.cons hs89 (.cons hs910 (.cons hs1011 (.cons hs1112 (.zero s12))))))))))))
  have halt : step code input s12 = some (.halted s12) :=
    step_halt_at (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
  have exec := hSteps.halts halt
  have vCnt5 : (reg s5 count).val = n := by rw [fr5 _ (by decide), r4n, hwnV]
  have vRem5 : (reg s5 registers.remain).val = m := by rw [r5m, hwmV]
  have vTmp6 : (reg s6 registers.tmp).val = n + m := by
    rw [r6tmp, add_no_wrap _ _ (by rw [vCnt5, vRem5]; omega), vCnt5, vRem5]
  have vOne6 : (reg s6 registers.one).val = 1 := by
    rw [fr6 _ (by decide), fr5 _ (by decide), hO4]
  have vTmp7 : (reg s7 registers.tmp).val = n + m + 1 := by
    rw [r7tmp, add_no_wrap _ _ (by rw [vTmp6, vOne6]; omega), vTmp6, vOne6]
  have vTin8 : (reg s8 tinBase).val = 2 * (n + m + 1) := by
    rw [r8tin, add_no_wrap _ _ (by rw [vTmp7]; omega), vTmp7]; omega
  have vTmp8 : (reg s8 registers.tmp).val = n + m + 1 := by rw [fr8 _ (by decide), vTmp7]
  have vVal9 : (reg s9 registers.value).val = 3 * (n + m + 1) := by
    rw [r9val, add_no_wrap _ _ (by rw [vTin8, vTmp8]; omega), vTin8, vTmp8]; omega
  have vTin10 : (reg s10 tinBase).val = 6 * (n + m + 1) := by
    rw [r10tin, add_no_wrap _ _ (by rw [vVal9]; omega), vVal9]; omega
  have vOne10 : (reg s10 registers.one).val = 1 := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide), vOne6]
  have vTin11 : (reg s11 tinBase).val = indegBase n m := by
    have heq : indegBase n m = 6 * (n + m + 1) + 1 := by unfold indegBase csrArenaWords; omega
    rw [r11tin, add_no_wrap _ _ (by rw [vTin10, vOne10]; omega), vTin10, vOne10, heq]
  have vCnt11 : (reg s11 count).val = n := by
    rw [fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide),
      fr7 _ (by decide), fr6 _ (by decide), vCnt5]
  have vTin12 : (reg s12 tinBase).val = stampsBase n m := by
    have heq : stampsBase n m = indegBase n m + n := rfl
    rw [r12tin, add_no_wrap _ _ (by rw [vTin11, vCnt11]; unfold indegBase csrArenaWords; omega),
      vTin11, vCnt11, heq]
  have vPtr12 : (reg s12 registers.ptr).val = 0 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), r3p]
  have vCnt12 : (reg s12 count).val = n := by rw [fr12 _ (by decide), vCnt11]
  have vZ12 : (reg s12 registers.zero).val = 0 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
      fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), hZ3]
  have vO12 : (reg s12 registers.one).val = 1 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), vOne10]
  have vRoom : stampsBase n m + n ≤ workCap := by
    have : stampsBase n m + n ≤ rawWorkCap n m := by
      unfold stampsBase indegBase csrArenaWords rawWorkCap; omega
    exact Nat.le_trans this workRoom
  have vData : s12.data = s.data :=
    d12.trans (d11.trans (d10.trans (d9.trans (d8.trans (d7.trans (d6.trans
      (d5.trans (d4.trans (d3.trans (d2.trans d1))))))))))
  exact ⟨s12, exec, ⟨vPtr12, vCnt12, vTin12, vZ12, vO12, vRoom⟩, vData⟩

private def scheduleRowsSetupList (h3 : 3 < 2 ^ bits) : List (Instr bits 15) :=
  [ .imm registers.stackBase ⟨3, h3⟩,
    .add cmd count registers.one,
    .mov toutBase registers.one,
    .add childrenBase tinBase count,
    .add childrenBase childrenBase count,
    .add childrenBase childrenBase count,
    .add childrenBase childrenBase count,
    .add childrenBase childrenBase count,
    .halt ]

/-- Set `stackBase := 3`, `cmd := n + 1`, `toutBase := 1`, `childrenBase := predBufBase n m`. -/
def scheduleRowsSetupPhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  Phase.ofLast (scheduleRowsSetupList (by omega)).toArray 8 rfl rfl rfl

theorem run_scheduleRowsSetup (input : Input L) {H : LabelledQuotient}
    (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap) (s : State L)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1)
    (hCount : (reg s count).val = H.vertexCount)
    (hTin : (reg s tinBase).val = stampsBase H.vertexCount H.arcCount) :
    ∃ t : State L,
      run (scheduleRowsSetupPhase (hi := hi) (hw := hw) (by
        exact Nat.le_trans (show 4 ≤ rawWorkCap H.vertexCount H.arcCount by unfold rawWorkCap; omega)
          (Nat.le_trans workRoom hw))).code input 9 (Phase.initial s) = some ⟨t, 9⟩ ∧
      (reg t registers.zero).val = 0 ∧
      (reg t registers.one).val = 1 ∧
      (reg t registers.stackBase).val = 3 ∧
      (reg t cmd).val = H.vertexCount + 1 ∧
      (reg t tinBase).val = stampsBase H.vertexCount H.arcCount ∧
      (reg t toutBase).val = 1 ∧
      (reg t childrenBase).val = predBufBase H.vertexCount H.arcCount ∧
      t.data = s.data := by
  let n := H.vertexCount
  let m := H.arcCount
  have h4 : 4 ≤ 2 ^ bits :=
    Nat.le_trans (show 4 ≤ rawWorkCap n m by unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
  let code := (scheduleRowsSetupPhase (hi := hi) (hw := hw) h4).code
  have hSize : code.size = 9 := rfl
  have hBound : predBufBase n m < 2 ^ bits :=
    Nat.lt_of_lt_of_le (by unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase
                              indegBase csrArenaWords rawWorkCap; omega)
      (Nat.le_trans workRoom hw)
  have s0 : (Phase.initial s).pc = 0 := rfl
  obtain ⟨s1, hs01, p1, r1sb, fr1, d1⟩ := step_imm15 (code := code) (input := input)
    (s := Phase.initial s) rfl (by rw [hSize, s0]; omega)
  obtain ⟨s2, hs12, p2, r2cmd, fr2, d2⟩ := step_add15 (code := code) (input := input)
    (s := s1) (by rw [p1]; rfl) (by rw [p1, hSize, s0]; omega)
  obtain ⟨s3, hs23, p3, r3tout, fr3, d3⟩ := step_mov15 (code := code) (input := input)
    (s := s2) (by rw [p2, p1]; rfl) (by rw [p2, p1, hSize, s0]; omega)
  obtain ⟨s4, hs34, p4, r4cb, fr4, d4⟩ := step_add15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, p1]; rfl) (by rw [p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s5, hs45, p5, r5cb, fr5, d5⟩ := step_add15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, p1]; rfl) (by rw [p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s6, hs56, p6, r6cb, fr6, d6⟩ := step_add15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, p1]; rfl) (by rw [p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s7, hs67, p7, r7cb, fr7, d7⟩ := step_add15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  obtain ⟨s8, hs78, p8, r8cb, fr8, d8⟩ := step_add15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, p1]; rfl)
    (by rw [p7, p6, p5, p4, p3, p2, p1, hSize, s0]; omega)
  have hSteps : Steps code input 8 (Phase.initial s) s8 :=
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67 (.cons hs78 (.zero s8))))))))
  have halt : step code input s8 = some (.halted s8) :=
    step_halt_at (by rw [p8, p7, p6, p5, p4, p3, p2, p1]; rfl)
  have exec := hSteps.halts halt
  have vZ8 : (reg s8 registers.zero).val = 0 := by
    rw [fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hZero
  have vO8 : (reg s8 registers.one).val = 1 := by
    rw [fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hOne
  have vCnt1 : (reg s1 count).val = n := by rw [fr1 _ (by decide)]; exact hCount
  have vOne1 : (reg s1 registers.one).val = 1 := by rw [fr1 _ (by decide)]; exact hOne
  have vTin3 : (reg s3 tinBase).val = stampsBase n m := by
    rw [fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide)]; exact hTin
  have vCnt3 : (reg s3 count).val = n := by rw [fr3 _ (by decide), fr2 _ (by decide), vCnt1]
  have vPred : predBufBase n m = stampsBase n m + 5 * n := by
    unfold predBufBase rowEndBase rowStartBase ranksBase orderBase; omega
  have vCb4 : (reg s4 childrenBase).val = stampsBase n m + n := by
    rw [r4cb, add_no_wrap _ _ (by rw [vTin3, vCnt3]; omega), vTin3, vCnt3]
  have vCnt4 : (reg s4 count).val = n := by rw [fr4 _ (by decide), vCnt3]
  have vCb5 : (reg s5 childrenBase).val = stampsBase n m + 2 * n := by
    rw [r5cb, add_no_wrap _ _ (by rw [vCb4, vCnt4]; omega), vCb4, vCnt4]; omega
  have vCnt5 : (reg s5 count).val = n := by rw [fr5 _ (by decide), vCnt4]
  have vCb6 : (reg s6 childrenBase).val = stampsBase n m + 3 * n := by
    rw [r6cb, add_no_wrap _ _ (by rw [vCb5, vCnt5]; omega), vCb5, vCnt5]; omega
  have vCnt6 : (reg s6 count).val = n := by rw [fr6 _ (by decide), vCnt5]
  have vCb7 : (reg s7 childrenBase).val = stampsBase n m + 4 * n := by
    rw [r7cb, add_no_wrap _ _ (by rw [vCb6, vCnt6]; omega), vCb6, vCnt6]; omega
  have vCnt7 : (reg s7 count).val = n := by rw [fr7 _ (by decide), vCnt6]
  have vCb8 : (reg s8 childrenBase).val = predBufBase n m := by
    rw [r8cb, add_no_wrap _ _ (by rw [vCb7, vCnt7]; omega), vCb7, vCnt7, vPred]; omega
  have vCmd2 : (reg s2 cmd).val = n + 1 := by
    rw [r2cmd, add_no_wrap _ _ (by rw [vCnt1, vOne1]; omega), vCnt1, vOne1]
  have vTout3 : (reg s3 toutBase).val = 1 := by
    rw [r3tout, fr2 _ (by decide), vOne1]
  refine ⟨s8, exec, vZ8, vO8, ?_, ?_, ?_, ?_, vCb8,
    d8.trans (d7.trans (d6.trans (d5.trans (d4.trans (d3.trans (d2.trans d1))))))⟩
  · rw [fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), r1sb]
  · rw [fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), fr3 _ (by decide), vCmd2]
  · rw [fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), vTin3]
  · rw [fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
      fr4 _ (by decide), vTout3]

private def scheduleRowsPre : List (Instr bits 15) :=
  [ .branchLt toutBase cmd 1 49,
    .loadInput registers.tmp registers.one,
    .add registers.ptr cmd registers.tmp,
    .add registers.ptr registers.ptr registers.ptr,
    .add registers.ptr registers.ptr registers.ptr,
    .add registers.value registers.ptr toutBase,
    .loadData offsetBase registers.value,
    .add registers.value registers.value registers.one,
    .loadData count registers.value,
    .sub count count offsetBase,
    .add registers.ptr registers.ptr cmd,
    .add registers.ptr registers.ptr registers.tmp,
    .add registers.ptr registers.ptr registers.one,
    .add offsetBase registers.ptr offsetBase,
    .mov registers.ptr registers.zero,
    .mov clk registers.zero ]

private def scheduleRowsPost : List (Instr bits 15) :=
  [ .sub registers.value toutBase registers.one,
    .sub registers.remain cmd registers.one,
    .add registers.ptr tinBase registers.remain,
    .add registers.ptr registers.ptr registers.remain,
    .add registers.ptr registers.ptr registers.remain,
    .add count registers.ptr registers.remain,
    .add offsetBase count registers.remain,
    .sub registers.childBase childrenBase offsetBase,
    .add registers.tmp registers.ptr registers.value,
    .storeData registers.tmp registers.childBase,
    .add registers.childBase registers.childBase clk,
    .add registers.tmp count registers.value,
    .storeData registers.tmp registers.childBase,
    .add childrenBase childrenBase clk,
    .add toutBase toutBase registers.one,
    .goto 0,
    .halt ]

private def scheduleRowsList (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    List (Instr bits 15) :=
  scheduleRowsPre ++
    ((distinctProgram (bits := bits) hi hw).toList.take 16).map (relocateInstr 16) ++
    [.goto 33] ++ scheduleRowsPost

private theorem scheduleRows_midLen :
    (((distinctProgram (bits := bits) hi hw).toList.take 16).map (relocateInstr 16)).length = 16 := by
  have hSize : (distinctProgram (bits := bits) hi hw).size = 17 := distinctProgram_size
  rw [List.length_map, List.length_take, Array.length_toList, hSize]
  decide

private theorem scheduleRows_preLen :
    (scheduleRowsPre (bits := bits)).length = 16 := rfl

private theorem scheduleRows_postLen :
    (scheduleRowsPost (bits := bits)).length = 17 := rfl

/-- All-row distinct predecessor scheduler (`50` instructions, `.halt` at PC `49`). -/
def scheduleRowsPhase : Phase L :=
  Phase.ofLast (scheduleRowsList (bits := bits) hi hw).toArray 49
    (by
      rw [List.size_toArray, scheduleRowsList, List.length_append, List.length_append,
        List.length_append, scheduleRows_preLen, scheduleRows_midLen, scheduleRows_postLen]
      rfl)
    (by
      rw [← Array.getElem?_toList]
      change (scheduleRowsList (bits := bits) hi hw)[49]? = some .halt
      rw [scheduleRowsList]
      have hL : (scheduleRowsPre (bits := bits) ++
          ((distinctProgram (bits := bits) hi hw).toList.take 16).map (relocateInstr 16) ++
          [Instr.goto 33]).length = 33 := by
        rw [List.length_append, List.length_append, scheduleRows_preLen, scheduleRows_midLen]
        rfl
      rw [List.getElem?_append_right (by omega), hL]
      rfl)
    (by
      have hPre : (scheduleRowsPre (bits := bits)).all (@nonHalt bits L) = true := by
        simp [scheduleRowsPre, nonHalt]
      have hMid : (((distinctProgram (bits := bits) hi hw).toList.take 16).map (relocateInstr 16)).all
          (@nonHalt bits L) = true := by
        rw [List.all_eq_true]
        intro op hop
        obtain ⟨op0, hop0, rfl⟩ := List.mem_map.mp hop
        have hnh : @nonHalt bits L op0 = true :=
          List.all_eq_true.mp (distinctProgram_noEarlyHalt (hi := hi) (hw := hw)) op0 hop0
        cases op0 <;> simp [nonHalt, relocateInstr] at hnh ⊢
      have hPost : ((scheduleRowsPost (bits := bits)).take 16).all (@nonHalt bits L) = true := by
        simp [scheduleRowsPost, nonHalt]
      change ((scheduleRowsList (bits := bits) hi hw).take 49).all (@nonHalt bits L) = true
      have h33 : (scheduleRowsPre (bits := bits) ++
          ((distinctProgram (bits := bits) hi hw).toList.take 16).map (relocateInstr 16) ++
          [Instr.goto 33]).length = 33 := by
        rw [List.length_append, List.length_append, scheduleRows_preLen, scheduleRows_midLen]
        rfl
      rw [scheduleRowsList, List.take_append, List.take_of_length_le (by rw [h33]; omega), h33]
      simp only [List.all_append, hPre, hMid, hPost]
      rfl)

private theorem scheduleRows_size :
    (scheduleRowsPhase (hi := hi) (hw := hw)).code.size = 50 := by
  change (scheduleRowsList (bits := bits) hi hw).toArray.size = 50
  rw [List.size_toArray, scheduleRowsList, List.length_append, List.length_append,
    List.length_append, scheduleRows_preLen, scheduleRows_midLen, scheduleRows_postLen]
  rfl

private theorem scheduleRows_pre_at (k : Nat) (hk : k < 16) :
    (scheduleRowsPhase (hi := hi) (hw := hw)).code[k]? =
      (scheduleRowsPre (bits := bits))[k]? := by
  change (scheduleRowsList (bits := bits) hi hw).toArray[k]? = _
  rw [← Array.getElem?_toList]
  change (scheduleRowsList (bits := bits) hi hw)[k]? = _
  rw [scheduleRowsList, List.append_assoc, List.append_assoc,
    List.getElem?_append_left (by rw [scheduleRows_preLen]; exact hk)]

private theorem scheduleRows_post_at (k : Nat) (hk : k < 17) :
    (scheduleRowsPhase (hi := hi) (hw := hw)).code[33 + k]? =
      (scheduleRowsPost (bits := bits))[k]? := by
  change (scheduleRowsList (bits := bits) hi hw).toArray[33 + k]? = _
  rw [← Array.getElem?_toList]
  change (scheduleRowsList (bits := bits) hi hw)[33 + k]? = _
  rw [scheduleRowsList]
  have hL1 : (scheduleRowsPre (bits := bits) ++
      ((distinctProgram (bits := bits) hi hw).toList.take 16).map (relocateInstr 16) ++
      [Instr.goto 33]).length = 33 := by
    rw [List.length_append, List.length_append, scheduleRows_preLen, scheduleRows_midLen]
    rfl
  rw [List.getElem?_append_right (by omega), hL1, show 33 + k - 33 = k by omega]

private theorem scheduleRows_distinct_placed :
    (∀ i op, (distinctProgram (bits := bits) hi hw)[i]? = some op → op ≠ .halt →
      (scheduleRowsPhase (hi := hi) (hw := hw)).code[16 + i]? = some (relocateInstr 16 op)) ∧
    (∀ i, (distinctProgram (bits := bits) hi hw)[i]? = some .halt →
      (scheduleRowsPhase (hi := hi) (hw := hw)).code[16 + i]? = some (.goto 33) ∧
      33 < (scheduleRowsPhase (hi := hi) (hw := hw)).code.size) := by
  constructor
  · intro i op hiop hne
    have hlt16 : i < 16 := by
      by_cases h16 : i < 16
      · exact h16
      · have hlt17 : i < 17 := by
          by_cases h17 : i < 17
          · exact h17
          · have hg := getElem?_neg (distinctProgram (bits := bits) hi hw) i
              (by rw [distinctProgram_size]; omega)
            rw [hg] at hiop; cases hiop
        have hi16 : i = 16 := by omega
        subst hi16
        rw [distinctProgram_at_16] at hiop
        cases hiop; exact (hne rfl).elim
    change (scheduleRowsList (bits := bits) hi hw).toArray[16 + i]? = some (relocateInstr 16 op)
    rw [← Array.getElem?_toList]
    change (scheduleRowsList (bits := bits) hi hw)[16 + i]? = some (relocateInstr 16 op)
    rw [scheduleRowsList, List.append_assoc, List.append_assoc,
      List.getElem?_append_right (by rw [scheduleRows_preLen]; omega),
      scheduleRows_preLen, show 16 + i - 16 = i by omega,
      List.getElem?_append_left (by rw [scheduleRows_midLen]; exact hlt16),
      List.getElem?_map, List.getElem?_take_of_lt hlt16, Array.getElem?_toList, hiop]
    rfl
  · intro i hiop
    have hi16 : i = 16 := distinctProgram_uniqueHalt i hiop
    subst hi16
    refine ⟨?_, by rw [scheduleRows_size]; decide⟩
    change (scheduleRowsList (bits := bits) hi hw).toArray[16 + 16]? = some (.goto 33)
    rw [← Array.getElem?_toList]
    change (scheduleRowsList (bits := bits) hi hw)[16 + 16]? = some (.goto 33)
    rw [scheduleRowsList, List.append_assoc, List.append_assoc,
      List.getElem?_append_right (by rw [scheduleRows_preLen]; omega),
      scheduleRows_preLen, show 16 + 16 - 16 = 16 by omega,
      List.getElem?_append_right (by rw [scheduleRows_midLen]; omega),
      scheduleRows_midLen]
    rfl

private structure SchedInv {H : LabelledQuotient}
    (aIn : Arena bits workCap (H.vertexCount + 1 + H.arcCount))
    (origData : Array (Word bits))
    (k predCursor : Nat) (hkLe : k ≤ H.vertexCount) (s : State L)
    (rowsPrefix : ∀ j, j < k → List (Vertex H)) : Prop where
  pc0 : s.pc = 0
  rZero : (reg s registers.zero).val = 0
  rOne : (reg s registers.one).val = 1
  rStack : (reg s registers.stackBase).val = 3
  rCmd : (reg s cmd).val = H.vertexCount + 1
  rTin : (reg s tinBase).val = stampsBase H.vertexCount H.arcCount
  rTout : (reg s toutBase).val = k + 1
  rCb : (reg s childrenBase).val = predBufBase H.vertexCount H.arcCount + predCursor
  cursorLe : predCursor ≤ sumRowLenAux (rawHead H) k
  incoming : IncomingAt aIn (rawHead H) s.data
  stamps : ∀ v : Fin H.vertexCount, ∃ w : Word bits,
    s.data[stampsBase H.vertexCount H.arcCount + v.val]? = some w ∧ w.val < k + 1
  rowsDone : ∀ (j : Nat) (hj : j < k),
    let v : Vertex H := ⟨j, Nat.lt_of_lt_of_le hj hkLe⟩
    TestSpec v (rowsPrefix j hj) ∧
    ∃ lo hi : Nat,
      (s.data[rowStartBase H.vertexCount H.arcCount + j]?).map Fin.val = some lo ∧
      (s.data[rowEndBase H.vertexCount H.arcCount + j]?).map Fin.val = some hi ∧
      lo ≤ hi ∧ hi ≤ predCursor ∧
      hi - lo = (rowsPrefix j hj).length ∧
      ∀ idx : Fin (rowsPrefix j hj).length,
        (s.data[predBufBase H.vertexCount H.arcCount + lo + idx.val]?).map Fin.val =
          some ((rowsPrefix j hj)[idx.val]'idx.isLt).val
  orderBank : ∀ j, orderBase H.vertexCount H.arcCount ≤ j →
    j < rowStartBase H.vertexCount H.arcCount → s.data[j]? = origData[j]?

private theorem scheduleRows_pre_block (input : Input L) {n m k predCursor rowLen : Nat}
    (hk : k < n) (hmWord : ∃ wm : Word bits, input.words[1]? = some wm ∧ wm.val = m)
    (hRoom : rawWorkCap n m ≤ workCap)
    (lo stop : Word bits)
    (s : State L) (hpc : s.pc = 0)
    (rZero : (reg s registers.zero).val = 0) (rOne : (reg s registers.one).val = 1)
    (rStack : (reg s registers.stackBase).val = 3) (rCmd : (reg s cmd).val = n + 1)
    (rTin : (reg s tinBase).val = stampsBase n m) (rTout : (reg s toutBase).val = k + 1)
    (rCb : (reg s childrenBase).val = predBufBase n m + predCursor)
    (hLo : s.data[4 * (n + 1 + m) + (k + 1)]? = some lo)
    (hStop : s.data[4 * (n + 1 + m) + (k + 1) + 1]? = some stop)
    (hStopEq : stop.val = lo.val + rowLen) (hStopLe : stop.val ≤ n + m) :
    ∃ s16 : State L,
      Steps (scheduleRowsPhase (hi := hi) (hw := hw)).code input 16 s s16 ∧
      s16.pc = 16 ∧ s16.data = s.data ∧
      (reg s16 registers.zero).val = 0 ∧ (reg s16 registers.one).val = 1 ∧
      (reg s16 registers.stackBase).val = 3 ∧ (reg s16 cmd).val = n + 1 ∧
      (reg s16 tinBase).val = stampsBase n m ∧ (reg s16 toutBase).val = k + 1 ∧
      (reg s16 childrenBase).val = predBufBase n m + predCursor ∧
      (reg s16 offsetBase).val = (5 * (n + 1 + m) + 1) + lo.val ∧
      (reg s16 count).val = rowLen ∧
      (reg s16 registers.ptr).val = 0 ∧ (reg s16 clk).val = 0 := by
  let K := n + 1 + m
  let code := (scheduleRowsPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 50 := scheduleRows_size
  have hBitsBound : 32 * n + 7 * m + 17 ≤ 2 ^ bits := by
    have := Nat.le_trans hRoom hw; unfold rawWorkCap at this; exact this
  obtain ⟨wm, hwm, hwmV⟩ := hmWord
  have h0 : code[s.pc]? = some (.branchLt toutBase cmd 1 49) := by
    rw [hpc]; exact scheduleRows_pre_at 0 (by decide)
  have hlt0 : ltb (reg s toutBase) (reg s cmd) = true :=
    branchLt_true (by rw [rTout, rCmd]; omega)
  let s1 : State L := { s with pc := 1 }
  have hs1pc : s1.pc = 1 := rfl
  have hs01 : step code input s = some (.next s1) := by
    simpa only [s1, hlt0, ite_true] using step_branchLt_at (input := input) h0
      (by rw [hlt0, hSize]; decide)
  have hOne1 : (reg s1 registers.one).val = 1 := rOne
  obtain ⟨s2, hs12, p2, r2tmp, fr2, d2⟩ := step_loadInput15 (code := code) (input := input)
    (s := s1) (by rw [hs1pc]; exact scheduleRows_pre_at 1 (by decide)) (by rw [hs1pc, hSize]; omega)
    (by change (reg s1 registers.one).val = 1 at hOne1; rw [hOne1]; exact hwm)
  obtain ⟨s3, hs23, p3, r3ptr, fr3, d3⟩ := step_add15 (code := code) (input := input)
    (s := s2) (by rw [p2, hs1pc]; exact scheduleRows_pre_at 2 (by decide)) (by rw [p2, hs1pc, hSize]; omega)
  obtain ⟨s4, hs34, p4, r4ptr, fr4, d4⟩ := step_add15 (code := code) (input := input)
    (s := s3) (by rw [p3, p2, hs1pc]; exact scheduleRows_pre_at 3 (by decide)) (by rw [p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s5, hs45, p5, r5ptr, fr5, d5⟩ := step_add15 (code := code) (input := input)
    (s := s4) (by rw [p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 4 (by decide)) (by rw [p4, p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s6, hs56, p6, r6val, fr6, d6⟩ := step_add15 (code := code) (input := input)
    (s := s5) (by rw [p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 5 (by decide)) (by rw [p5, p4, p3, p2, hs1pc, hSize]; omega)
  have vCmd2 : (reg s2 cmd).val = n + 1 := by rw [fr2 _ (by decide)]; exact rCmd
  have vTmp2 : (reg s2 registers.tmp).val = m := by rw [r2tmp, hwmV]
  have vPtr3 : (reg s3 registers.ptr).val = K := by
    rw [r3ptr, add_no_wrap (reg s2 cmd) (reg s2 registers.tmp) (by rw [vCmd2, vTmp2]; omega), vCmd2, vTmp2]
  have vPtr4 : (reg s4 registers.ptr).val = 2 * K := by
    rw [r4ptr, add_no_wrap (reg s3 registers.ptr) (reg s3 registers.ptr)
      (by rw [vPtr3]; dsimp [K]; omega), vPtr3]; omega
  have vPtr5 : (reg s5 registers.ptr).val = 4 * K := by
    rw [r5ptr, add_no_wrap (reg s4 registers.ptr) (reg s4 registers.ptr)
      (by rw [vPtr4]; dsimp [K]; omega), vPtr4]; omega
  have vTout5 : (reg s5 toutBase).val = k + 1 := by
    rw [fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide)]; exact rTout
  have vVal6 : (reg s6 registers.value).val = 4 * K + (k + 1) := by
    rw [r6val, add_no_wrap (reg s5 registers.ptr) (reg s5 toutBase)
      (by rw [vPtr5, vTout5]; dsimp [K]; omega), vPtr5, vTout5]
  have d5eq : s6.data = s.data := d6.trans (d5.trans (d4.trans (d3.trans d2)))
  obtain ⟨s7, hs67, p7, r7off, fr7, d7⟩ := step_loadData15 (code := code) (input := input)
    (s := s6) (by rw [p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 6 (by decide))
    (by rw [d5eq, vVal6]; exact hLo) (by rw [p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  have vOne6 : (reg s6 registers.one).val = 1 := by
    rw [fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide),
      fr2 _ (by decide)]; exact hOne1
  have vVal7 : (reg s7 registers.value).val = 4 * K + (k + 1) := by rw [fr7 _ (by decide), vVal6]
  have vOne7 : (reg s7 registers.one).val = 1 := by rw [fr7 _ (by decide), vOne6]
  obtain ⟨s8, hs78, p8, r8val, fr8, d8⟩ := step_add15 (code := code) (input := input)
    (s := s7) (by rw [p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 7 (by decide))
    (by rw [p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  have vVal8 : (reg s8 registers.value).val = 4 * K + (k + 1) + 1 := by
    rw [r8val, add_no_wrap (reg s7 registers.value) (reg s7 registers.one)
      (by rw [vVal7, vOne7]; dsimp [K]; omega), vVal7, vOne7]
  have d8eq : s8.data = s.data := d8.trans (d7.trans d5eq)
  obtain ⟨s9, hs89, p9, r9cnt, fr9, d9⟩ := step_loadData15 (code := code) (input := input)
    (s := s8) (by rw [p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 8 (by decide))
    (by rw [d8eq, vVal8]; exact hStop) (by rw [p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  have vOff7 : (reg s7 offsetBase).val = lo.val := by rw [r7off]
  have vOff9 : (reg s9 offsetBase).val = lo.val := by rw [fr9 _ (by decide), fr8 _ (by decide), vOff7]
  have vCnt9 : (reg s9 count).val = stop.val := by rw [r9cnt]
  obtain ⟨s10, hs910, p10, r10cnt, fr10, d10⟩ := step_sub15 (code := code) (input := input)
    (s := s9) (by rw [p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 9 (by decide))
    (by rw [p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  have vCnt10 : (reg s10 count).val = rowLen := by
    rw [r10cnt, sub_exact (reg s9 count) (reg s9 offsetBase) (by rw [vCnt9, vOff9, hStopEq]; omega),
      vCnt9, vOff9, hStopEq]; omega
  obtain ⟨s11, hs1011, p11, r11ptr, fr11, d11⟩ := step_add15 (code := code) (input := input)
    (s := s10) (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 10 (by decide))
    (by rw [p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s12, hs1112, p12, r12ptr, fr12, d12⟩ := step_add15 (code := code) (input := input)
    (s := s11) (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 11 (by decide))
    (by rw [p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s13, hs1213, p13, r13ptr, fr13, d13⟩ := step_add15 (code := code) (input := input)
    (s := s12) (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 12 (by decide))
    (by rw [p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s14, hs1314, p14, r14off, fr14, d14⟩ := step_add15 (code := code) (input := input)
    (s := s13) (by rw [p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 13 (by decide))
    (by rw [p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s15, hs1415, p15, r15ptr, fr15, d15⟩ := step_mov15 (code := code) (input := input)
    (s := s14) (by rw [p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 14 (by decide))
    (by rw [p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  obtain ⟨s16, hs1516, p16, r16clk, fr16, d16⟩ := step_mov15 (code := code) (input := input)
    (s := s15) (by rw [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc]; exact scheduleRows_pre_at 15 (by decide))
    (by rw [p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc, hSize]; omega)
  have vPtr10 : (reg s10 registers.ptr).val = 4 * K := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide),
      fr6 _ (by decide), vPtr5]
  have vCmd10 : (reg s10 cmd).val = n + 1 := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide),
      fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), vCmd2]
  have vTmp10 : (reg s10 registers.tmp).val = m := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide),
      fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide), vTmp2]
  have vOne10 : (reg s10 registers.one).val = 1 := by
    rw [fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), vOne7]
  have vPtr11 : (reg s11 registers.ptr).val = 4 * K + n + 1 := by
    rw [r11ptr, add_no_wrap (reg s10 registers.ptr) (reg s10 cmd)
      (by rw [vPtr10, vCmd10]; dsimp [K]; omega), vPtr10, vCmd10]; omega
  have vTmp11 : (reg s11 registers.tmp).val = m := by rw [fr11 _ (by decide), vTmp10]
  have vPtr12 : (reg s12 registers.ptr).val = 5 * K := by
    rw [r12ptr, add_no_wrap (reg s11 registers.ptr) (reg s11 registers.tmp)
      (by rw [vPtr11, vTmp11]; dsimp [K]; omega), vPtr11, vTmp11]; dsimp [K]; omega
  have vOne12 : (reg s12 registers.one).val = 1 := by
    rw [fr12 _ (by decide), fr11 _ (by decide), vOne10]
  have vPtr13 : (reg s13 registers.ptr).val = 5 * K + 1 := by
    rw [r13ptr, add_no_wrap (reg s12 registers.ptr) (reg s12 registers.one)
      (by rw [vPtr12, vOne12]; dsimp [K]; omega), vPtr12, vOne12]
  have vOff13 : (reg s13 offsetBase).val = lo.val := by
    rw [fr13 _ (by decide), fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), vOff9]
  have vOff14 : (reg s14 offsetBase).val = 5 * K + 1 + lo.val := by
    rw [r14off, add_no_wrap (reg s13 registers.ptr) (reg s13 offsetBase)
      (by rw [vPtr13, vOff13]; dsimp [K]; omega), vPtr13, vOff13]
  have vZero14 : (reg s14 registers.zero).val = 0 := by
    rw [fr14 _ (by decide), fr13 _ (by decide), fr12 _ (by decide), fr11 _ (by decide),
      fr10 _ (by decide), fr9 _ (by decide), fr8 _ (by decide), fr7 _ (by decide),
      fr6 _ (by decide), fr5 _ (by decide), fr4 _ (by decide), fr3 _ (by decide),
      fr2 _ (by decide)]; exact rZero
  have vZero15 : (reg s15 registers.zero).val = 0 := by rw [fr15 _ (by decide), vZero14]
  have vPtr15 : (reg s15 registers.ptr).val = 0 := by rw [r15ptr, vZero14]
  refine ⟨s16,
    .cons hs01 (.cons hs12 (.cons hs23 (.cons hs34 (.cons hs45 (.cons hs56 (.cons hs67
      (.cons hs78 (.cons hs89 (.cons hs910 (.cons hs1011 (.cons hs1112 (.cons hs1213
        (.cons hs1314 (.cons hs1415 (.cons hs1516 (.zero s16)))))))))))))))),
    by rw [p16, p15, p14, p13, p12, p11, p10, p9, p8, p7, p6, p5, p4, p3, p2, hs1pc],
    d16.trans (d15.trans (d14.trans (d13.trans (d12.trans (d11.trans (d10.trans (d9.trans d8eq))))))),
    by rw [fr16 _ (by decide), vZero15],
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide), vOne12],
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
        fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
        fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
        fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide)]; exact rStack,
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
        fr12 _ (by decide), fr11 _ (by decide), vCmd10],
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
        fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
        fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
        fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide)]; exact rTin,
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
        fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
        fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide)]; exact vTout5,
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
        fr12 _ (by decide), fr11 _ (by decide), fr10 _ (by decide), fr9 _ (by decide),
        fr8 _ (by decide), fr7 _ (by decide), fr6 _ (by decide), fr5 _ (by decide),
        fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide)]; exact rCb,
    by rw [fr16 _ (by decide), fr15 _ (by decide), vOff14],
    by rw [fr16 _ (by decide), fr15 _ (by decide), fr14 _ (by decide), fr13 _ (by decide),
        fr12 _ (by decide), fr11 _ (by decide), vCnt10],
    by rw [fr16 _ (by decide), vPtr15],
    by rw [r16clk, vZero15]⟩

private theorem scheduleRows_post_block (input : Input L) {n m k predCursor outLen : Nat}
    (hk : k < n) (hOutSum : predCursor + outLen ≤ m) (hRoom : rawWorkCap n m ≤ workCap)
    (s33 : State L) (hs33pc : s33.pc = 33)
    (vZero33 : (reg s33 registers.zero).val = 0) (vOne33 : (reg s33 registers.one).val = 1)
    (vStack33 : (reg s33 registers.stackBase).val = 3) (vCmd33 : (reg s33 cmd).val = n + 1)
    (vTin33 : (reg s33 tinBase).val = stampsBase n m) (vTout33 : (reg s33 toutBase).val = k + 1)
    (vCb33 : (reg s33 childrenBase).val = predBufBase n m + predCursor)
    (vClk33 : (reg s33 clk).val = outLen) :
    ∃ t : State L,
      Steps (scheduleRowsPhase (hi := hi) (hw := hw)).code input 16 s33 t ∧
      t.pc = 0 ∧
      (reg t registers.zero).val = 0 ∧ (reg t registers.one).val = 1 ∧
      (reg t registers.stackBase).val = 3 ∧ (reg t cmd).val = n + 1 ∧
      (reg t tinBase).val = stampsBase n m ∧ (reg t toutBase).val = k + 2 ∧
      (reg t childrenBase).val = predBufBase n m + (predCursor + outLen) ∧
      (t.data[rowStartBase n m + k]?).map Fin.val = some predCursor ∧
      (t.data[rowEndBase n m + k]?).map Fin.val = some (predCursor + outLen) ∧
      (∀ j, j ≠ rowStartBase n m + k → j ≠ rowEndBase n m + k → t.data[j]? = s33.data[j]?) := by
  let code := (scheduleRowsPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 50 := scheduleRows_size
  have hBitsBound : 32 * n + 7 * m + 17 ≤ 2 ^ bits := by
    have := Nat.le_trans hRoom hw; unfold rawWorkCap at this; exact this
  obtain ⟨s34, hs33, p34, r34val, fr34, d34⟩ := step_sub15 (code := code) (input := input)
    (s := s33) (by rw [hs33pc]; exact scheduleRows_post_at 0 (by decide)) (by rw [hs33pc, hSize]; omega)
  obtain ⟨s35, hs34, p35, r35rem, fr35, d35⟩ := step_sub15 (code := code) (input := input)
    (s := s34) (by rw [p34, hs33pc]; exact scheduleRows_post_at 1 (by decide)) (by rw [p34, hs33pc, hSize]; omega)
  obtain ⟨s36, hs35, p36, r36ptr, fr36, d36⟩ := step_add15 (code := code) (input := input)
    (s := s35) (by rw [p35, p34, hs33pc]; exact scheduleRows_post_at 2 (by decide)) (by rw [p35, p34, hs33pc, hSize]; omega)
  obtain ⟨s37, hs36, p37, r37ptr, fr37, d37⟩ := step_add15 (code := code) (input := input)
    (s := s36) (by rw [p36, p35, p34, hs33pc]; exact scheduleRows_post_at 3 (by decide))
    (by rw [p36, p35, p34, hs33pc, hSize]; omega)
  obtain ⟨s38, hs37, p38, r38ptr, fr38, d38⟩ := step_add15 (code := code) (input := input)
    (s := s37) (by rw [p37, p36, p35, p34, hs33pc]; exact scheduleRows_post_at 4 (by decide))
    (by rw [p37, p36, p35, p34, hs33pc, hSize]; omega)
  obtain ⟨s39, hs38, p39, r39cnt, fr39, d39⟩ := step_add15 (code := code) (input := input)
    (s := s38) (by rw [p38, p37, p36, p35, p34, hs33pc]; exact scheduleRows_post_at 5 (by decide))
    (by rw [p38, p37, p36, p35, p34, hs33pc, hSize]; omega)
  obtain ⟨s40, hs39, p40, r40off, fr40, d40⟩ := step_add15 (code := code) (input := input)
    (s := s39) (by rw [p39, p38, p37, p36, p35, p34, hs33pc]; exact scheduleRows_post_at 6 (by decide))
    (by rw [p39, p38, p37, p36, p35, p34, hs33pc, hSize]; omega)
  obtain ⟨s41, hs40, p41, r41cb, fr41, d41⟩ := step_sub15 (code := code) (input := input)
    (s := s40) (by rw [p40, p39, p38, p37, p36, p35, p34, hs33pc]; exact scheduleRows_post_at 7 (by decide))
    (by rw [p40, p39, p38, p37, p36, p35, p34, hs33pc, hSize]; omega)
  have vVal34 : (reg s34 registers.value).val = k := by
    rw [r34val, sub_exact (reg s33 toutBase) (reg s33 registers.one) (by rw [vTout33, vOne33]; omega),
      vTout33, vOne33, Nat.add_sub_cancel]
  have vCmd34 : (reg s34 cmd).val = n + 1 := by rw [fr34 _ (by decide)]; exact vCmd33
  have vOne34 : (reg s34 registers.one).val = 1 := by rw [fr34 _ (by decide)]; exact vOne33
  have vRem35 : (reg s35 registers.remain).val = n := by
    rw [r35rem, sub_exact (reg s34 cmd) (reg s34 registers.one) (by rw [vCmd34, vOne34]; omega),
      vCmd34, vOne34, Nat.add_sub_cancel]
  have vTin35 : (reg s35 tinBase).val = stampsBase n m := by
    rw [fr35 _ (by decide), fr34 _ (by decide)]; exact vTin33
  have hBaseFit : predBufBase n m < 2 ^ bits := by
    unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords
    omega
  have vPtr36 : (reg s36 registers.ptr).val = orderBase n m := by
    have heq : orderBase n m = stampsBase n m + n := rfl
    have hlt : stampsBase n m + n < 2 ^ bits := by
      unfold orderBase predBufBase rowEndBase rowStartBase ranksBase stampsBase indegBase
        csrArenaWords at *; omega
    rw [r36ptr, add_no_wrap (reg s35 tinBase) (reg s35 registers.remain)
      (by rw [vTin35, vRem35]; exact hlt), vTin35, vRem35, heq]
  have vRem36 : (reg s36 registers.remain).val = n := by rw [fr36 _ (by decide), vRem35]
  have vPtr37 : (reg s37 registers.ptr).val = ranksBase n m := by
    have heq : ranksBase n m = orderBase n m + n := rfl
    have hlt : orderBase n m + n < 2 ^ bits := by
      unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase
        csrArenaWords at *; omega
    rw [r37ptr, add_no_wrap (reg s36 registers.ptr) (reg s36 registers.remain)
      (by rw [vPtr36, vRem36]; exact hlt), vPtr36, vRem36, heq]
  have vRem37 : (reg s37 registers.remain).val = n := by rw [fr37 _ (by decide), vRem36]
  have vPtr38 : (reg s38 registers.ptr).val = rowStartBase n m := by
    have heq : rowStartBase n m = ranksBase n m + n := rfl
    have hlt : ranksBase n m + n < 2 ^ bits := by
      unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase
        csrArenaWords at *; omega
    rw [r38ptr, add_no_wrap (reg s37 registers.ptr) (reg s37 registers.remain)
      (by rw [vPtr37, vRem37]; exact hlt), vPtr37, vRem37, heq]
  have vRem38 : (reg s38 registers.remain).val = n := by rw [fr38 _ (by decide), vRem37]
  have vCnt39 : (reg s39 count).val = rowEndBase n m := by
    have heq : rowEndBase n m = rowStartBase n m + n := rfl
    have hlt : rowStartBase n m + n < 2 ^ bits := by
      unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase
        csrArenaWords at *; omega
    rw [r39cnt, add_no_wrap (reg s38 registers.ptr) (reg s38 registers.remain)
      (by rw [vPtr38, vRem38]; exact hlt), vPtr38, vRem38, heq]
  have vRem39 : (reg s39 registers.remain).val = n := by rw [fr39 _ (by decide), vRem38]
  have vOff40 : (reg s40 offsetBase).val = predBufBase n m := by
    have heq : predBufBase n m = rowEndBase n m + n := rfl
    rw [r40off, add_no_wrap (reg s39 count) (reg s39 registers.remain)
      (by rw [vCnt39, vRem39, ← heq]; exact hBaseFit), vCnt39, vRem39, heq]
  have vCb40 : (reg s40 childrenBase).val = predBufBase n m + predCursor := by
    rw [fr40 _ (by decide), fr39 _ (by decide), fr38 _ (by decide), fr37 _ (by decide),
      fr36 _ (by decide), fr35 _ (by decide), fr34 _ (by decide)]; exact vCb33
  have vChild41 : (reg s41 registers.childBase).val = predCursor := by
    rw [r41cb, sub_exact (reg s40 childrenBase) (reg s40 offsetBase) (by rw [vCb40, vOff40]; omega),
      vCb40, vOff40, Nat.add_sub_cancel_left]
  have vPtr41 : (reg s41 registers.ptr).val = rowStartBase n m := by
    rw [fr41 _ (by decide), fr40 _ (by decide), fr39 _ (by decide)]; exact vPtr38
  have vVal41 : (reg s41 registers.value).val = k := by
    rw [fr41 _ (by decide), fr40 _ (by decide), fr39 _ (by decide), fr38 _ (by decide),
      fr37 _ (by decide), fr36 _ (by decide), fr35 _ (by decide)]; exact vVal34
  have vCnt41 : (reg s41 count).val = rowEndBase n m := by
    rw [fr41 _ (by decide), fr40 _ (by decide)]; exact vCnt39
  have vClk41 : (reg s41 clk).val = outLen := by
    rw [fr41 _ (by decide), fr40 _ (by decide), fr39 _ (by decide), fr38 _ (by decide),
      fr37 _ (by decide), fr36 _ (by decide), fr35 _ (by decide), fr34 _ (by decide)]; exact vClk33
  have hWrite1Placed : Placed code 41 (indexedDataWrite registers.tmp registers.ptr registers.value registers.childBase) := by
    intro i op h
    rcases i with _ | _ | _
    · cases h; exact scheduleRows_post_at 8 (by decide)
    · cases h; exact scheduleRows_post_at 9 (by decide)
    · simp [indexedDataWrite] at h
  have hFitStart : (reg s41 registers.ptr).val + (reg s41 registers.value).val < workCap := by
    rw [vPtr41, vVal41]
    have : rowStartBase n m + n ≤ rawWorkCap n m := by
      unfold rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords rawWorkCap; omega
    omega
  obtain ⟨s43, hs41, p43, w43, _, fr43⟩ := indexedDataWrite15 (code := code) (input := input)
    (s := s41) hWrite1Placed
    (by rw [p41, p40, p39, p38, p37, p36, p35, p34, hs33pc])
    (by rw [hSize]; omega) (by decide) hFitStart
  have h43 : code[s43.pc]? = some (.add registers.childBase registers.childBase clk) := by
    rw [p43]; exact scheduleRows_post_at 10 (by decide)
  obtain ⟨s44, hs43, p44, r44cb, fr44, d44⟩ := step_add15 (code := code) (input := input)
    (s := s43) h43 (by rw [p43, hSize]; omega)
  have vChild43 : (reg s43 registers.childBase).val = predCursor := by
    rw [fr43 _ (by decide)]; exact vChild41
  have vClk43 : (reg s43 clk).val = outLen := by rw [fr43 _ (by decide)]; exact vClk41
  have vChild44 : (reg s44 registers.childBase).val = predCursor + outLen := by
    rw [r44cb, add_no_wrap (reg s43 registers.childBase) (reg s43 clk)
      (by rw [vChild43, vClk43]; omega), vChild43, vClk43]
  have vCnt44 : (reg s44 count).val = rowEndBase n m := by
    rw [fr44 _ (by decide), fr43 _ (by decide)]; exact vCnt41
  have vVal44 : (reg s44 registers.value).val = k := by
    rw [fr44 _ (by decide), fr43 _ (by decide)]; exact vVal41
  have hWrite2Placed : Placed code 44 (indexedDataWrite registers.tmp count registers.value registers.childBase) := by
    intro i op h
    rcases i with _ | _ | _
    · cases h; exact scheduleRows_post_at 11 (by decide)
    · cases h; exact scheduleRows_post_at 12 (by decide)
    · simp [indexedDataWrite] at h
  have hFitEnd : (reg s44 count).val + (reg s44 registers.value).val < workCap := by
    rw [vCnt44, vVal44]
    have : rowEndBase n m + n ≤ rawWorkCap n m := by
      unfold rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords rawWorkCap; omega
    omega
  obtain ⟨s46, hs44, p46, w46, _, fr46⟩ := indexedDataWrite15 (code := code) (input := input)
    (s := s44) hWrite2Placed (by rw [p44, p43]) (by rw [hSize]; omega) (by decide) hFitEnd
  have h46 : code[s46.pc]? = some (.add childrenBase childrenBase clk) := by
    rw [p46]; exact scheduleRows_post_at 13 (by decide)
  obtain ⟨s47, hs46, p47, r47cb, fr47, d47⟩ := step_add15 (code := code) (input := input)
    (s := s46) h46 (by rw [p46, hSize]; omega)
  have h47 : code[s47.pc]? = some (.add toutBase toutBase registers.one) := by
    rw [p47, p46]; exact scheduleRows_post_at 14 (by decide)
  obtain ⟨s48, hs47, p48, r48tout, fr48, d48⟩ := step_add15 (code := code) (input := input)
    (s := s47) h47 (by rw [p47, p46, hSize]; omega)
  have h48 : code[s48.pc]? = some (.goto 0) := by
    rw [p48, p47, p46]; exact scheduleRows_post_at 15 (by decide)
  let t : State L := { s48 with pc := 0 }
  have hs48 : step code input s48 = some (.next t) := step_goto_at h48 (by rw [hSize]; decide)
  have hPreserveBase : ∀ r : Fin 15, r = registers.zero ∨ r = registers.one ∨
      r = registers.stackBase ∨ r = cmd ∨ r = tinBase → reg t r = reg s33 r := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;>
    · change reg s48 _ = reg s33 _
      rw [fr48 _ (by decide), fr47 _ (by decide), fr46 _ (by decide), fr44 _ (by decide),
        fr43 _ (by decide), fr41 _ (by decide), fr40 _ (by decide), fr39 _ (by decide),
        fr38 _ (by decide), fr37 _ (by decide), fr36 _ (by decide), fr35 _ (by decide),
        fr34 _ (by decide)]
  have vCb46 : (reg s46 childrenBase).val = predBufBase n m + predCursor := by
    rw [fr46 _ (by decide), fr44 _ (by decide), fr43 _ (by decide), fr41 _ (by decide)]; exact vCb40
  have vClk46 : (reg s46 clk).val = outLen := by
    rw [fr46 _ (by decide), fr44 _ (by decide)]; exact vClk43
  have vCb47 : (reg s47 childrenBase).val = predBufBase n m + (predCursor + outLen) := by
    rw [r47cb, add_no_wrap (reg s46 childrenBase) (reg s46 clk)
      (by rw [vCb46, vClk46]; unfold predBufBase rowEndBase rowStartBase ranksBase orderBase
                              stampsBase indegBase csrArenaWords at *; omega),
      vCb46, vClk46]; omega
  have vTout47 : (reg s47 toutBase).val = k + 1 := by
    rw [fr47 _ (by decide), fr46 _ (by decide), fr44 _ (by decide), fr43 _ (by decide),
      fr41 _ (by decide), fr40 _ (by decide), fr39 _ (by decide), fr38 _ (by decide),
      fr37 _ (by decide), fr36 _ (by decide), fr35 _ (by decide), fr34 _ (by decide)]; exact vTout33
  have vOne47 : (reg s47 registers.one).val = 1 := by
    rw [fr47 _ (by decide), fr46 _ (by decide), fr44 _ (by decide), fr43 _ (by decide),
      fr41 _ (by decide), fr40 _ (by decide), fr39 _ (by decide), fr38 _ (by decide),
      fr37 _ (by decide), fr36 _ (by decide), fr35 _ (by decide), fr34 _ (by decide)]; exact vOne33
  have d41eq : s41.data = s33.data := d41.trans (d40.trans (d39.trans (d38.trans
    (d37.trans (d36.trans (d35.trans d34))))))
  refine ⟨t,
    .cons hs33 (.cons hs34 (.cons hs35 (.cons hs36 (.cons hs37 (.cons hs38 (.cons hs39
      (.cons hs40 (hs41.append (.cons hs43 (hs44.append (.cons hs46 (.cons hs47
        (.cons hs48 (.zero t)))))))))))))),
    rfl,
    by rw [hPreserveBase _ (Or.inl rfl)]; exact vZero33,
    by rw [hPreserveBase _ (Or.inr (Or.inl rfl))]; exact vOne33,
    by rw [hPreserveBase _ (Or.inr (Or.inr (Or.inl rfl)))]; exact vStack33,
    by rw [hPreserveBase _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]; exact vCmd33,
    by rw [hPreserveBase _ (Or.inr (Or.inr (Or.inr (Or.inr rfl))))]; exact vTin33,
    by change (reg s48 toutBase).val = k + 2
       rw [r48tout, add_no_wrap (reg s47 toutBase) (reg s47 registers.one)
         (by rw [vTout47, vOne47]; omega), vTout47, vOne47],
    by change (reg s48 childrenBase).val = predBufBase n m + (predCursor + outLen)
       rw [fr48 _ (by decide), vCb47],
    by have hneq : rowStartBase n m + k ≠ rowEndBase n m + k := by
         unfold rowEndBase rowStartBase; omega
       change (s48.data[rowStartBase n m + k]?).map Fin.val = some predCursor
       rw [d48, d47, w46, Array.getElem?_set_ne _ (by rw [vCnt44, vVal44]; exact hneq.symm),
         d44, w43, ← vPtr41, ← vVal41, Array.getElem?_set_self, Option.map_some, vChild41],
    by change (s48.data[rowEndBase n m + k]?).map Fin.val = some (predCursor + outLen)
       rw [d48, d47, w46, ← vCnt44, ← vVal44, Array.getElem?_set_self, Option.map_some, vChild44],
    by intro j hj1 hj2
       change s48.data[j]? = s33.data[j]?
       rw [d48, d47, w46, Array.getElem?_set_ne _ (by rw [vCnt44, vVal44]; exact hj2.symm),
         d44, w43, Array.getElem?_set_ne _ (by rw [vPtr41, vVal41]; exact hj1.symm), d41eq]⟩

private theorem scheduleRows_step (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (aIn : Arena bits workCap (H.vertexCount + 1 + H.arcCount))
    (haInBase : aIn.base = 0) (haInCh : aIn.children = H.vertexCount + H.arcCount)
    (origData : Array (Word bits))
    (k predCursor : Nat) (hk : k < H.vertexCount) (s : State L)
    (rowsPrefix : ∀ j, j < k → List (Vertex H))
    (inv : SchedInv aIn origData k predCursor (Nat.le_of_lt hk) s rowsPrefix) :
    let y : Vertex H := ⟨k, hk⟩
    ∃ (t : State L) (cost predCursor' : Nat) (out : List (Vertex H)),
      cost ≤ 34 + 16 * (rowNodes (rawHead H) y).length ∧
      Steps (scheduleRowsPhase (hi := hi) (hw := hw)).code input cost s t ∧
      predCursor' = predCursor + out.length ∧
      SchedInv aIn origData (k + 1) predCursor' hk t
        (fun j _ => if hlt : j < k then rowsPrefix j hlt else out) := by
  let n := H.vertexCount
  let m := H.arcCount
  let K := n + 1 + m
  let y : Vertex H := ⟨k, hk⟩
  let code := (scheduleRowsPhase (hi := hi) (hw := hw)).code
  have hWorkRoomNM : rawWorkCap n m ≤ workCap := workRoom
  have hSumLe : sumRowLenAux (rawHead H) k ≤ m := sumRowLen_le_arcs (rawHead H) k
  have hCursorM : predCursor ≤ m := Nat.le_trans inv.cursorLe hSumLe
  have hmWord : ∃ wm : Word bits, input.words[1]? = some wm ∧ wm.val = m := by
    cases hw1 : input.words[1]? with
    | none => have h := raw.hdr_m; simp [hw1] at h
    | some w => have h := raw.hdr_m; simp [hw1] at h; exact ⟨w, rfl, h⟩
  obtain ⟨lo, stop, row, hLo, hStop, hStopEq, hStopLe, hTokens, _, hRowPos⟩ :=
    tokenView_of_incoming inv.incoming y
  have hLo' : s.data[4 * (n + 1 + m) + (k + 1)]? = some lo := by
    simpa only [Arena.offsets, haInBase, Nat.zero_add, headNode] using hLo
  have hStop' : s.data[4 * (n + 1 + m) + (k + 1) + 1]? = some stop := by
    simpa only [Arena.offsets, haInBase, Nat.zero_add, headNode] using hStop
  have hStopLe' : stop.val ≤ n + m := by simpa only [haInCh] using hStopLe
  obtain ⟨s16, hPreSteps, hs16Pc, hs16Data, vZero16, vOne16, vStack16, vCmd16,
      vTin16, vTout16, vCb16, vOff16, vCnt16, vPtr16, vClk16⟩ :=
    scheduleRows_pre_block input hk hmWord hWorkRoomNM lo stop s inv.pc0
      inv.rZero inv.rOne inv.rStack inv.rCmd inv.rTin inv.rTout inv.rCb
      hLo' hStop' hStopEq hStopLe'
  have haOff : aIn.offsets = 4 * K := by change aIn.base + 4 * K = 4 * K; rw [haInBase, Nat.zero_add]
  have haPay : aIn.payload = 5 * K + 1 := by
    change aIn.base + 5 * K + 1 = 5 * K + 1; rw [haInBase, Nat.zero_add]
  have vOff16' : (reg s16 offsetBase).val = aIn.payload + lo.val := by
    rw [vOff16, haPay]
  have hTokFit : aIn.payload + lo.val + (rowNodes (rawHead H) y).length ≤ workCap := by
    have : aIn.payload + lo.val + (rowNodes (rawHead H) y).length ≤ 6 * K := by
      rw [haPay]; dsimp [K]; omega
    have : 6 * K < rawWorkCap n m := by unfold rawWorkCap; dsimp [K]; omega
    omega
  -- Set up DistinctBanks + DistinctParams for distinctProgram
  let b : DistinctBanks bits inputCap workCap n m (rowNodes (rawHead H) y).length :=
    { read :=
        { inputSource := 3
          tokens := aIn.payload + lo.val
          stamps := stampsBase n m
          sourcesFit := by have := raw.cap_ge; unfold rawInputCap at this; omega
          tokensFit := hTokFit
          stampsFit := by
            have : stampsBase n m + n ≤ rawWorkCap n m := by
              unfold stampsBase indegBase csrArenaWords rawWorkCap; omega
            omega }
      output := predBufBase n m + predCursor
      epoch := k + 1
      rowsBeforeStamps := by
          dsimp only
          change aIn.payload + lo.val + (rowNodes (rawHead H) y).length ≤ stampsBase n m
          have : 6 * K ≤ stampsBase n m := by
            unfold stampsBase indegBase csrArenaWords; dsimp [K]; omega
          omega
      stampsBeforeOutput := by
        dsimp only
        change stampsBase n m + n ≤ predBufBase n m + predCursor
        have : stampsBase n m + n ≤ predBufBase n m := by
          unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase; omega
        omega
      outputFits := by
        have : predBufBase n m + predCursor + (rowNodes (rawHead H) y).length ≤
            predBufBase n m + m := by
          have := hSumLe
          have : sumRowLenAux (rawHead H) (k + 1) =
              sumRowLenAux (rawHead H) k + (rowNodes (rawHead H) y).length := by
            simp only [sumRowLenAux]; exact dite_eq_left hk
          have h1 := sumRowLen_le_arcs (rawHead H) (k + 1)
          have h2 := inv.cursorLe
          omega
        have : predBufBase n m + m ≤ rawWorkCap n m := by
          unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase
            indegBase csrArenaWords rawWorkCap; omega
        omega }
  have hParams : DistinctParams b (Phase.initial s16) :=
    ⟨⟨vStack16, vOff16', vTin16, vCmd16⟩, vCnt16, vCb16, vTout16, vOne16⟩
  have hToks : TokensAt (vertices := n) (Phase.initial s16).data b.read.tokens row := by
    change TokensAt (vertices := n) s16.data (aIn.payload + lo.val) row
    rw [hs16Data]
    exact hTokens
  have hOlder : ∀ v : Fin n, ∃ w : Word bits,
      (Phase.initial s16).data[b.read.stamps + v.val]? = some w ∧ w.val < b.epoch := by
    intro v
    change ∃ w : Word bits, s16.data[stampsBase n m + v.val]? = some w ∧ w.val < k + 1
    rw [hs16Data]
    exact inv.stamps v
  obtain ⟨sD, _, workD, out, hWorkD, hRunD, hClkD, hNodupD, hLenD, hMemD, hOutD,
      hStampsD, hMidD, hRegsD, _, _⟩ :=
    run_distinct_row_full input b (fun e => (rawOccurrence H e).1) row raw.sources
      (Phase.initial s16) rfl hParams vPtr16 vClk16 hToks hOlder
  have hLinkedD : Steps code input workD s16 { sD with pc := 33 } := by
    have hReloc : relocateStatePC 16 (Phase.initial s16) = s16 := by
      rw [← hs16Pc]
      simp only [relocateStatePC, Phase.initial, Nat.add_zero]
    have hLink := linked_return_of_run_multi (linked := code) (base := 16) (ret := fun _ => 33)
      hRunD scheduleRows_distinct_placed.1 scheduleRows_distinct_placed.2
    simpa only [hReloc] using hLink
  let s33 : State L := { sD with pc := 33 }
  have vZero33 : (reg s33 registers.zero).val = 0 := by
    change (reg sD registers.zero).val = 0
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vZero16
  have vOne33 : (reg s33 registers.one).val = 1 := by
    change (reg sD registers.one).val = 1
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vOne16
  have vStack33 : (reg s33 registers.stackBase).val = 3 := by
    change (reg sD registers.stackBase).val = 3
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vStack16
  have vCmd33 : (reg s33 cmd).val = n + 1 := by
    change (reg sD cmd).val = n + 1
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vCmd16
  have vTin33 : (reg s33 tinBase).val = stampsBase n m := by
    change (reg sD tinBase).val = stampsBase n m
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vTin16
  have vTout33 : (reg s33 toutBase).val = k + 1 := by
    change (reg sD toutBase).val = k + 1
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vTout16
  have vCb33 : (reg s33 childrenBase).val = predBufBase n m + predCursor := by
    change (reg sD childrenBase).val = predBufBase n m + predCursor
    rw [hRegsD _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact vCb16
  have hLenLe : (rowNodes (rawHead H) y).length ≤ m := by
    have : sumRowLenAux (rawHead H) (k + 1) =
        sumRowLenAux (rawHead H) k + (rowNodes (rawHead H) y).length := by
      simp only [sumRowLenAux]; exact dite_eq_left hk
    have hNext := sumRowLen_le_arcs (rawHead H) (k + 1)
    omega
  have hCurOutSum : predCursor + out.length ≤ m := by
    have : sumRowLenAux (rawHead H) (k + 1) =
        sumRowLenAux (rawHead H) k + (rowNodes (rawHead H) y).length := by
      simp only [sumRowLenAux]; exact dite_eq_left hk
    have hNext := sumRowLen_le_arcs (rawHead H) (k + 1)
    have hCur := inv.cursorLe
    omega
  obtain ⟨t, hPostSteps, htPc, htZero, htOne, htStack, htCmd, htTin, htTout, htCb,
      hWrite1Mem, hWrite2Mem, dPostKeep⟩ :=
    scheduleRows_post_block input hk hCurOutSum hWorkRoomNM s33 rfl
      vZero33 vOne33 vStack33 vCmd33 vTin33 vTout33 vCb33 hClkD
  have dPreKeep (j : Nat) (hj1 : j < stampsBase n m ∨ stampsBase n m + n ≤ j)
      (hj2 : j < predBufBase n m + predCursor ∨ predBufBase n m + predCursor + (rowNodes (rawHead H) y).length ≤ j) :
      sD.data[j]? = s.data[j]? := by
    rw [hMidD j hj1 hj2, Phase.initial_data, hs16Data]
  have hSupport : ∀ u, u ∈ out ↔ H.HasQuotientArc u y :=
    distinct_source_support H y row hRowPos out hMemD
  refine ⟨t, 16 + workD + 16, predCursor + out.length, out,
    by change 16 + workD + 16 ≤ 34 + 16 * (rowNodes (rawHead H) y).length; omega,
    hPreSteps.append (hLinkedD.append hPostSteps), rfl, ?_⟩
  refine ⟨htPc, htZero, htOne, htStack, htCmd, htTin, htTout, htCb, ?_, ?_, ?_, ?_, ?_⟩
  · have hSumNext : sumRowLenAux (rawHead H) (k + 1) =
        sumRowLenAux (rawHead H) k + (rowNodes (rawHead H) y).length := by
      simp only [sumRowLenAux]; exact dite_eq_left hk
    have := inv.cursorLe
    omega
  · intro v
    obtain ⟨lv, stv, hLv, hStv, hLenEq, hLeCh, hCell⟩ := inv.incoming v
    have hVlt := v.isLt
    have h1 : aIn.offsets + (headNode m v).val < stampsBase n m := by
      change aIn.base + 4 * K + (v.val + 1) < stampsBase n m
      rw [haInBase]; unfold stampsBase indegBase csrArenaWords; dsimp [K]; omega
    have h2 : aIn.offsets + (headNode m v).val + 1 < stampsBase n m := by
      change aIn.base + 4 * K + (v.val + 1) + 1 < stampsBase n m
      rw [haInBase]; unfold stampsBase indegBase csrArenaWords; dsimp [K]; omega
    have hKeepOff1 : t.data[aIn.offsets + (headNode m v).val]? = s.data[aIn.offsets + (headNode m v).val]? := by
      have hNeq1 : aIn.offsets + (headNode m v).val ≠ rowStartBase n m + k := by
        unfold rowStartBase ranksBase orderBase stampsBase at *; omega
      have hNeq2 : aIn.offsets + (headNode m v).val ≠ rowEndBase n m + k := by
        unfold rowEndBase rowStartBase ranksBase orderBase stampsBase at *; omega
      have hPre1 : aIn.offsets + (headNode m v).val < predBufBase n m + predCursor := by
        unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase at *; omega
      exact (dPostKeep _ hNeq1 hNeq2).trans (dPreKeep _ (Or.inl h1) (Or.inl hPre1))
    have hKeepOff2 : t.data[aIn.offsets + (headNode m v).val + 1]? = s.data[aIn.offsets + (headNode m v).val + 1]? := by
      have hNeq1 : aIn.offsets + (headNode m v).val + 1 ≠ rowStartBase n m + k := by
        unfold rowStartBase ranksBase orderBase stampsBase at *; omega
      have hNeq2 : aIn.offsets + (headNode m v).val + 1 ≠ rowEndBase n m + k := by
        unfold rowEndBase rowStartBase ranksBase orderBase stampsBase at *; omega
      have hPre2 : aIn.offsets + (headNode m v).val + 1 < predBufBase n m + predCursor := by
        unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase at *; omega
      exact (dPostKeep _ hNeq1 hNeq2).trans (dPreKeep _ (Or.inl h2) (Or.inl hPre2))
    refine ⟨lv, stv, hKeepOff1 ▸ hLv, hKeepOff2 ▸ hStv, hLenEq, hLeCh, ?_⟩
    intro q
    obtain ⟨e, hePos, heHead, heCell⟩ := hCell q
    have hLtSt : aIn.payload + lv.val + q.val < stampsBase n m := by
      have hqLt := q.isLt
      have hPayBd : aIn.payload + stv.val ≤ 6 * K := by rw [haPay]; have := haInCh; dsimp [K]; omega
      rw [haPay] at hPayBd
      unfold stampsBase indegBase csrArenaWords; omega
    have hKeepPay : t.data[aIn.payload + lv.val + q.val]? = s.data[aIn.payload + lv.val + q.val]? := by
      have hNeq1 : aIn.payload + lv.val + q.val ≠ rowStartBase n m + k := by
        unfold rowStartBase ranksBase orderBase stampsBase at *; omega
      have hNeq2 : aIn.payload + lv.val + q.val ≠ rowEndBase n m + k := by
        unfold rowEndBase rowStartBase ranksBase orderBase stampsBase at *; omega
      have hPre3 : aIn.payload + lv.val + q.val < predBufBase n m + predCursor := by
        unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase at *; omega
      exact (dPostKeep _ hNeq1 hNeq2).trans (dPreKeep _ (Or.inl hLtSt) (Or.inl hPre3))
    exact ⟨e, hePos, heHead, hKeepPay ▸ heCell⟩
  · intro v
    obtain ⟨w, hwMem, hwVal⟩ := hStampsD v
    change w.val ≤ k + 1 at hwVal
    have h1 : stampsBase n m + v.val ≠ rowStartBase n m + k := by
      have := v.isLt; unfold rowStartBase ranksBase orderBase stampsBase; omega
    have h2 : stampsBase n m + v.val ≠ rowEndBase n m + k := by
      have := v.isLt; unfold rowEndBase rowStartBase ranksBase orderBase stampsBase; omega
    exact ⟨w, (dPostKeep _ h1 h2) ▸ hwMem, by omega⟩
  · intro j hj
    by_cases hlt : j < k
    · simp only [hlt, dite_true]
      obtain ⟨hSpec, loj, hij, hLs, hRs, hLej, hHij, hDiffj, hCellsj⟩ := inv.rowsDone j hlt
      change (s.data[rowStartBase n m + j]?).map Fin.val = some loj at hLs
      change (s.data[rowEndBase n m + j]?).map Fin.val = some hij at hRs
      refine ⟨hSpec, loj, hij, ?_, ?_, hLej, by omega, hDiffj, ?_⟩
      · have hNeq1 : rowStartBase n m + j ≠ rowStartBase n m + k := by omega
        have hNeq2 : rowStartBase n m + j ≠ rowEndBase n m + k := by
          unfold rowEndBase rowStartBase; omega
        have hSt1 : stampsBase n m + n ≤ rowStartBase n m + j := by
          unfold rowStartBase ranksBase orderBase stampsBase; omega
        have hPre1 : rowStartBase n m + j < predBufBase n m + predCursor := by
          unfold predBufBase rowEndBase rowStartBase; omega
        change (t.data[rowStartBase n m + j]?).map Fin.val = some loj
        rw [dPostKeep _ hNeq1 hNeq2, dPreKeep _ (Or.inr hSt1) (Or.inl hPre1)]
        exact hLs
      · have hNeq1 : rowEndBase n m + j ≠ rowStartBase n m + k := by
          unfold rowEndBase rowStartBase; omega
        have hNeq2 : rowEndBase n m + j ≠ rowEndBase n m + k := by omega
        have hSt2 : stampsBase n m + n ≤ rowEndBase n m + j := by
          unfold rowEndBase rowStartBase ranksBase orderBase stampsBase; omega
        have hPre2 : rowEndBase n m + j < predBufBase n m + predCursor := by
          unfold predBufBase rowEndBase; omega
        change (t.data[rowEndBase n m + j]?).map Fin.val = some hij
        rw [dPostKeep _ hNeq1 hNeq2, dPreKeep _ (Or.inr hSt2) (Or.inl hPre2)]
        exact hRs
      · intro idx
        have hIdxLt : idx.val < (rowsPrefix j hlt).length := by
          simpa only [hlt, dite_true] using idx.isLt
        have hNeq1 : predBufBase n m + loj + idx.val ≠ rowStartBase n m + k := by
          unfold predBufBase rowEndBase rowStartBase; omega
        have hNeq2 : predBufBase n m + loj + idx.val ≠ rowEndBase n m + k := by
          unfold predBufBase rowEndBase; omega
        have hSt3 : stampsBase n m + n ≤ predBufBase n m + loj + idx.val := by
          unfold predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase; omega
        have hPre3 : predBufBase n m + loj + idx.val < predBufBase n m + predCursor := by omega
        change (t.data[predBufBase n m + loj + idx.val]?).map Fin.val = _
        rw [dPostKeep _ hNeq1 hNeq2, dPreKeep _ (Or.inr hSt3) (Or.inl hPre3)]
        exact hCellsj ⟨idx.val, hIdxLt⟩
    · have hjEq : j = k := by omega
      simp only [hjEq, Nat.lt_irrefl, dite_false]
      refine ⟨⟨hNodupD, hSupport⟩, predCursor, predCursor + out.length,
        hWrite1Mem, hWrite2Mem, Nat.le_add_right _ _, Nat.le_refl _, by omega, ?_⟩
      intro idx
      have hIdxLt : idx.val < out.length := by
        simpa only [hjEq, Nat.lt_irrefl, dite_false] using idx.isLt
      have h1 : predBufBase n m + predCursor + idx.val ≠ rowStartBase n m + k := by
        unfold predBufBase rowEndBase rowStartBase; omega
      have h2 : predBufBase n m + predCursor + idx.val ≠ rowEndBase n m + k := by
        unfold predBufBase rowEndBase; omega
      change (t.data[predBufBase n m + predCursor + idx.val]?).map Fin.val = _
      rw [dPostKeep _ h1 h2]
      exact hOutD ⟨idx.val, hIdxLt⟩
  · intro j hjLo hjHi
    change orderBase n m ≤ j at hjLo
    change j < rowStartBase n m at hjHi
    have h1 : j ≠ rowStartBase n m + k := by omega
    have h2 : j ≠ rowEndBase n m + k := by
      unfold rowEndBase rowStartBase at *; omega
    have h3 : stampsBase n m + n ≤ j := by
      change stampsBase n m + n ≤ j at hjLo; exact hjLo
    have h4 : j < predBufBase n m + predCursor := by
      unfold predBufBase rowEndBase rowStartBase at *; omega
    rw [dPostKeep _ h1 h2, dPreKeep _ (Or.inr h3) (Or.inl h4)]
    exact inv.orderBank j hjLo hjHi

theorem run_scheduleRows (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (aIn : Arena bits workCap (H.vertexCount + 1 + H.arcCount))
    (haInBase : aIn.base = 0) (haInCh : aIn.children = H.vertexCount + H.arcCount)
    (s : State L)
    (hZero : (reg s registers.zero).val = 0)
    (hOne : (reg s registers.one).val = 1)
    (hStack : (reg s registers.stackBase).val = 3)
    (hCmd : (reg s cmd).val = H.vertexCount + 1)
    (hTin : (reg s tinBase).val = stampsBase H.vertexCount H.arcCount)
    (hTout : (reg s toutBase).val = 1)
    (hCb : (reg s childrenBase).val = predBufBase H.vertexCount H.arcCount)
    (hInc : IncomingAt aIn (rawHead H) s.data)
    (hStampsZero : ∀ v : Fin H.vertexCount, (s.data[stampsBase H.vertexCount H.arcCount + v.val]?).map Fin.val = some 0) :
    ∃ (t : State L) (work : Nat) (rows : PaperB.ForestDictionary.Rows H),
      work ≤ 34 * H.vertexCount + 16 * H.arcCount + 2 ∧
      run (scheduleRowsPhase (hi := hi) (hw := hw)).code input work (Phase.initial s) = some ⟨t, work⟩ ∧
      (∀ y : Vertex H, ∃ lo hi : Nat,
        (t.data[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
        (t.data[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
        lo ≤ hi ∧ hi ≤ H.arcCount ∧
        hi - lo = (rows.row y).length ∧
        ∀ j : Fin (rows.row y).length,
          (t.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
            some ((rows.row y)[j.val]'j.isLt).val) ∧
      (∀ j, orderBase H.vertexCount H.arcCount ≤ j →
        j < rowStartBase H.vertexCount H.arcCount → t.data[j]? = s.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let code := (scheduleRowsPhase (hi := hi) (hw := hw)).code
  have hSize : code.size = 50 := scheduleRows_size
  have hStampsInit : ∀ v : Fin n, ∃ w : Word bits,
      s.data[stampsBase n m + v.val]? = some w ∧ w.val < 0 + 1 := by
    intro v
    have h := hStampsZero v
    change (s.data[stampsBase n m + v.val]?).map Fin.val = some 0 at h
    cases hs : s.data[stampsBase n m + v.val]? with
    | none => simp only [hs, Option.map_none] at h; cases h
    | some w =>
      simp only [hs, Option.map_some] at h
      exact ⟨w, rfl, by rw [Option.some.inj h]; decide⟩
  have hStart : SchedInv aIn s.data 0 0 (Nat.zero_le n) (Phase.initial s) (fun _ h => (Nat.not_lt_zero _ h).elim) :=
    ⟨rfl, hZero, hOne, hStack, hCmd, hTin, hTout,
      by change (reg s childrenBase).val = predBufBase n m + 0; rw [hCb, Nat.add_zero],
      Nat.zero_le _, hInc, hStampsInit,
      fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ _ => rfl⟩
  have hIter : ∀ k (hk : k ≤ n),
      ∃ (q : State L) (work predCursor : Nat) (rowsPrefix : ∀ j, j < k → List (Vertex H)),
        work ≤ 34 * k + 16 * sumRowLenAux (rawHead H) k ∧
        Steps code input work (Phase.initial s) q ∧
        SchedInv aIn s.data k predCursor hk q rowsPrefix := by
    intro k hk
    induction k with
    | zero => exact ⟨Phase.initial s, 0, 0, fun _ h => (Nat.not_lt_zero _ h).elim, Nat.le_refl _,
        .zero _, hStart⟩
    | succ k ih =>
      obtain ⟨q, w, predCursor, rowsPrefix, hwLe, hsq, hInv⟩ := ih (by omega)
      obtain ⟨q', cost, predCursor', out, hCost, hqq', hPredEq, hInv'⟩ :=
        scheduleRows_step input raw workRoom aIn haInBase haInCh s.data k predCursor hk q rowsPrefix hInv
      have hSumNext : sumRowLenAux (rawHead H) (k + 1) =
          sumRowLenAux (rawHead H) k + (rowNodes (rawHead H) ⟨k, hk⟩).length := by
        simp only [sumRowLenAux]; exact dite_eq_left hk
      exact ⟨q', w + cost, predCursor', _, by rw [hSumNext]; omega, hsq.append hqq', hInv'⟩
  obtain ⟨q, work, predCursor, rowsPrefix, hwLe, hsq, hInv⟩ := hIter n (Nat.le_refl n)
  have h0 : code[q.pc]? = some (.branchLt toutBase cmd 1 49) := by
    rw [hInv.pc0]; exact scheduleRows_pre_at 0 (by decide)
  have hExit : ltb (reg q toutBase) (reg q cmd) = false :=
    branchLt_false (by
      have h1 := hInv.rTout
      have h2 := hInv.rCmd
      dsimp [n] at h1 h2
      rw [h1, h2]
      exact Nat.le_refl _)
  let t : State L := { q with pc := 49 }
  have hqt : step code input q = some (.next t) := by
    simpa only [t, hExit, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) h0 (by rw [hExit, hSize]; decide)
  have h49 : code[49]? = some .halt := by
    rw [show (49 : Nat) = 33 + 16 by rfl]
    exact scheduleRows_post_at 16 (by decide)
  have hRun : run code input (work + 2) (Phase.initial s) = some ⟨t, work + 2⟩ :=
    (hsq.append (.cons hqt (.zero t))).halts (step_halt_at h49)
  have hSumM : sumRowLenAux (rawHead H) n ≤ m := sumRowLen_le_arcs (rawHead H) n
  let rows : PaperB.ForestDictionary.Rows H :=
    { row := fun y => rowsPrefix y.val y.isLt
      spec := fun y => (hInv.rowsDone y.val y.isLt).1 }
  refine ⟨t, work + 2, rows, by omega, hRun, ?_, ?_⟩
  · intro y
    obtain ⟨_, lo, hiV, hLo, hHi, hLe, hLePred, hDiff, hCells⟩ := hInv.rowsDone y.val y.isLt
    have hPredM : predCursor ≤ m := Nat.le_trans hInv.cursorLe hSumM
    exact ⟨lo, hiV, hLo, hHi, hLe, Nat.le_trans hLePred hPredM, hDiff, hCells⟩
  · exact hInv.orderBank

/-- Ordered list of Stage 1B phases. -/
def stage1BPhases (hbits : 4 ≤ 2 ^ bits) : List (Phase L) :=
  [ initIncomingCsrRegsPhase (hi := hi) (hw := hw) hbits,
    rawIncomingPhase (hi := hi) (hw := hw),
    initStampsSetupPhase (hi := hi) (hw := hw) (by omega),
    zeroBankPhase (hi := hi) (hw := hw),
    scheduleRowsSetupPhase (hi := hi) (hw := hw) hbits,
    scheduleRowsPhase (hi := hi) (hw := hw) ]

/-- Linked single ROM phase for Stage 1B. -/
def stage1BPhase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  pipelinePhase (stage1BPhases (hi := hi) (hw := hw) hbits)

theorem stage1BPhase_code (hbits : 4 ≤ 2 ^ bits) :
    (stage1BPhase (hi := hi) (hw := hw) hbits).code =
      pipeline (stage1BPhases (hi := hi) (hw := hw) hbits) :=
  pipelinePhase_code _

/-- Run Stage 1B preserving `[orderBase, rowStartBase)` and producing `rows` + `rows_mem`. -/
theorem run_stage1B (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State L) :
    ∃ (t : State L) (work : Nat) (rows : PaperB.ForestDictionary.Rows H),
      work ≤ 91 * H.vertexCount + 68 * H.arcCount + 125 ∧
      run (stage1BPhase (hi := hi) (hw := hw) (bits_ge_four_of_raw raw)).code
        input work (Phase.initial s) = some ⟨t, work⟩ ∧
      (∀ y : Vertex H, ∃ lo hi : Nat,
        (t.data[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
        (t.data[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
        lo ≤ hi ∧ hi ≤ H.arcCount ∧
        hi - lo = (rows.row y).length ∧
        ∀ j : Fin (rows.row y).length,
          (t.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
            some ((rows.row y)[j.val]'j.isLt).val) ∧
      (∀ j, orderBase H.vertexCount H.arcCount ≤ j →
        j < rowStartBase H.vertexCount H.arcCount → t.data[j]? = s.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let K := n + 1 + m
  have hbits : 4 ≤ 2 ^ bits := bits_ge_four_of_raw raw
  let aIn : Arena bits workCap K :=
    ⟨0, n + m, by unfold rawWorkCap at workRoom; omega,
      by have := Nat.lt_of_lt_of_le (show 0 + 5 * K + 1 + (n + m) < rawWorkCap n m by
          unfold rawWorkCap; omega) (Nat.le_trans workRoom hw)
         exact this⟩
  have haInBase : aIn.base = 0 := rfl
  have haInCh : aIn.children = n + m := rfl
  obtain ⟨s1, hRun1, hCur1, hClk1, hCb1, hData1⟩ :=
    run_initIncomingCsrRegs input raw workRoom s
  have hInFit : (3 + m) + m ≤ inputCap := by have := raw.cap_ge; unfold rawInputCap at this; omega
  have hSpace : K - 1 ≤ aIn.children := by dsimp [aIn, K]; omega
  obtain ⟨s2, _, w2, hw2, hInc2, hFr2, hRun2, _, _⟩ :=
    run_raw_incoming_framed input aIn (rawHead H) (3 + m) hInFit raw.heads hSpace s1 hCur1 hClk1 hCb1
  obtain ⟨s3, hRun3, hZbp3, hData3⟩ := run_initStampsSetup input raw workRoom s2
  have hZbp3Init : ZeroBankParams (stampsBase n m) n (Phase.initial s3) :=
    ⟨hZbp3.ptr, hZbp3.countVal, hZbp3.baseVal, hZbp3.zeroVal, hZbp3.oneVal, hZbp3.room⟩
  obtain ⟨s4, _, hRun4, hZs4, hFr4, hRegs4, _, _⟩ :=
    run_zeroBank input (stampsBase n m) n (Phase.initial s3) rfl hZbp3Init
  have hZ4 : (reg s4 registers.zero).val = 0 := by
    rw [hRegs4 _ (by decide) (by decide)]; exact hZbp3.zeroVal
  have hO4 : (reg s4 registers.one).val = 1 := by
    rw [hRegs4 _ (by decide) (by decide)]; exact hZbp3.oneVal
  have hCnt4 : (reg s4 count).val = n := by
    rw [hRegs4 _ (by decide) (by decide)]; exact hZbp3.countVal
  have hTin4 : (reg s4 tinBase).val = stampsBase n m := by
    rw [hRegs4 _ (by decide) (by decide)]; exact hZbp3.baseVal
  obtain ⟨s5, hRun5, hZ5, hO5, hSb5, hCmd5, hTin5, hTout5, hCb5, hData5⟩ :=
    run_scheduleRowsSetup input workRoom s4 hZ4 hO4 hCnt4 hTin4
  have hInc5 : IncomingAt aIn (rawHead H) s5.data := by
    rw [hData5]
    intro v
    obtain ⟨lv, stv, hLv, hStv, hLenEq, hLeCh, hCell⟩ := hInc2 v
    have hVlt := v.isLt
    have h1 : aIn.offsets + (headNode m v).val < stampsBase n m := by
      change 0 + 4 * K + (v.val + 1) < stampsBase n m
      unfold stampsBase indegBase csrArenaWords; omega
    have h2 : aIn.offsets + (headNode m v).val + 1 < stampsBase n m := by
      change 0 + 4 * K + (v.val + 1) + 1 < stampsBase n m
      unfold stampsBase indegBase csrArenaWords; omega
    refine ⟨lv, stv, (hFr4 _ (Or.inl h1)).trans (by rw [Phase.initial_data, hData3]; exact hLv),
      (hFr4 _ (Or.inl h2)).trans (by rw [Phase.initial_data, hData3]; exact hStv), hLenEq, hLeCh, ?_⟩
    intro q
    obtain ⟨e, hePos, heHead, heCell⟩ := hCell q
    have hqLt := q.isLt
    have h3 : aIn.payload + lv.val + q.val < stampsBase n m := by
      change 0 + 5 * K + 1 + lv.val + q.val < stampsBase n m
      have : lv.val + (rowNodes (rawHead H) v).length ≤ n + m := by rw [← hLenEq]; exact hLeCh
      unfold stampsBase indegBase csrArenaWords; omega
    exact ⟨e, hePos, heHead, by rw [hFr4 _ (Or.inl h3), Phase.initial_data, hData3]; exact heCell⟩
  have hStamps5 : ∀ v : Fin n, (s5.data[stampsBase n m + v.val]?).map Fin.val = some 0 := by
    intro v; rw [hData5]; exact hZs4 v.val v.isLt
  obtain ⟨s6, w6, rows, hw6, hRun6, hRowsMem6, hOrder6⟩ :=
    run_scheduleRows input raw workRoom aIn haInBase haInCh s5 hZ5 hO5 hSb5 hCmd5 hTin5 hTout5
      hCb5 hInc5 hStamps5
  have hPhases : PhasesRun input (stage1BPhases (hi := hi) (hw := hw) hbits) s (Phase.initial s6)
      (17 + (w2 + (13 + (5 * n + 2 + (9 + (w6 + 1)))))) :=
    .cons hRun1 (.cons hRun2 (.cons hRun3 (.cons hRun4
      (.cons hRun5 (.cons hRun6 (.nil (s := s6)))))))
  obtain ⟨u, _, _, huData, hRunU, _, _⟩ := run_pipeline hPhases
  have huData6 : u.data = s6.data := huData.trans rfl
  refine ⟨u, 17 + (w2 + (13 + (5 * n + 2 + (9 + (w6 + 1))))), rows, by omega,
    by rw [stage1BPhase_code]; exact hRunU, ?_, ?_⟩
  · intro y
    obtain ⟨lo, hiV, hLo, hHi, hLe, hLeM, hDiff, hCells⟩ := hRowsMem6 y
    exact ⟨lo, hiV, huData6 ▸ hLo, huData6 ▸ hHi, hLe, hLeM, hDiff,
      fun j => huData6 ▸ hCells j⟩
  · intro j hjLo hjHi
    have hPa : aIn.payload + aIn.children ≤ j := by
      change 0 + 5 * K + 1 + (n + m) ≤ j
      unfold orderBase stampsBase indegBase csrArenaWords at hjLo; omega
    have hSt : stampsBase n m + n ≤ j := by
      unfold orderBase at hjLo; exact hjLo
    rw [huData6, hOrder6 j hjLo hjHi, hData5, hFr4 j (Or.inr hSt), Phase.initial_data,
      hData3, hFr2 j hPa, hData1]

end Stage1BPhases

/-! ### Full Linked Stage 1 Pipeline & `Stage1Output` -/

section Stage1Linked

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- Full Stage 1 word-RAM pipeline (`kahnStagePhase` linked with `stage1BPhase`). -/
def stage1Phase (hbits : 4 ≤ 2 ^ bits) : Phase L :=
  Phase.link (kahnStagePhase (hi := hi) (hw := hw) hbits)
    (stage1BPhase (hi := hi) (hw := hw) hbits)

/-- Full Stage 1 ROM program. -/
def stage1Program (hbits : 4 ≤ 2 ^ bits) : Program L :=
  (stage1Phase (hi := hi) (hw := hw) hbits).code

/-- Constant factor in the linear `O(n_H + m_H)` instruction bound for Stage 1. -/
def stage1WorkFactor : Nat := 275

/-- Full linked Stage 1 execution from raw quotient words and arbitrary initial `s₀`
to `Stage1Output`, in `≤ 275 * (n_H + m_H + 1)` instructions and exact peak footprint
`inputCap + workCap + 15`. -/
theorem run_stage1 (input : Input L) {H : LabelledQuotient}
    (raw : RawQuotientInput input H) (acyc : H.IsAcyclic)
    (workRoom : rawWorkCap H.vertexCount H.arcCount ≤ workCap) (s₀ : State L) :
    ∃ (t : State L) (trace : List (State L)) (work : Nat)
      (order : Array (Vertex H)) (size_order : order.size = H.vertexCount)
      (rank : Vertex H → Nat) (rows : PaperB.ForestDictionary.Rows H),
      work ≤ stage1WorkFactor * (H.vertexCount + H.arcCount + 1) ∧
      run (stage1Program (hi := hi) (hw := hw) (bits_ge_four_of_raw raw))
        input work (Phase.initial s₀) = some ⟨t, work⟩ ∧
      SuccessfulTrace (stage1Program (hi := hi) (hw := hw) (bits_ge_four_of_raw raw))
        input (Phase.initial s₀) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 ∧
      Stage1Output H t order size_order rank rows := by
  have hbits : 4 ≤ 2 ^ bits := bits_ge_four_of_raw raw
  obtain ⟨t1, _, w1, order, size_order, rank, hw1, hRun1, hNodup, hCovers, hTopo,
      hRankAt, hRankInc, hRankArc, hOrderMem1, hRanksMem1, _, _⟩ :=
    run_kahn_stage input raw acyc workRoom s₀
  obtain ⟨t2, w2, rows, hw2, hRun2, hRowsMem2, hPreserve2⟩ :=
    run_stage1B input raw workRoom t1
  have hNonempty : 0 < (stage1BPhase (hi := hi) (hw := hw) hbits).code.size := by
    rw [stage1BPhase_code]
    exact pipeline_nonempty _
  obtain ⟨t, trace, _, hDataEq, hRun, hTrace, hPeak⟩ :=
    run_linked_pair (kahnStagePhase (hi := hi) (hw := hw) hbits)
      (stage1BPhase (hi := hi) (hw := hw) hbits).code hNonempty hRun1
      (by simpa only [stage1BPhase_code] using hRun2)
  have hPeak' : tracePeakWords input trace = inputCap + workCap + 15 := by
    simpa only [footprint] using hPeak
  have hOrderMem : ∀ i : Fin H.vertexCount,
      (t.data[orderBase H.vertexCount H.arcCount + i.val]?).map Fin.val =
        some (orderedVertexAt order size_order i).val := by
    intro i
    have hiLt := i.isLt
    have hLo : orderBase H.vertexCount H.arcCount ≤ orderBase H.vertexCount H.arcCount + i.val := by omega
    have hHi : orderBase H.vertexCount H.arcCount + i.val < rowStartBase H.vertexCount H.arcCount := by
      unfold rowStartBase ranksBase orderBase; omega
    rw [hDataEq, hPreserve2 _ hLo hHi]
    exact hOrderMem1 i
  have hRanksMem : ∀ v : Vertex H,
      (t.data[ranksBase H.vertexCount H.arcCount + v.val]?).map Fin.val = some (rank v) := by
    intro v
    have hvLt := v.isLt
    have hLo : orderBase H.vertexCount H.arcCount ≤ ranksBase H.vertexCount H.arcCount + v.val := by
      unfold ranksBase orderBase; omega
    have hHi : ranksBase H.vertexCount H.arcCount + v.val < rowStartBase H.vertexCount H.arcCount := by
      unfold rowStartBase ranksBase; omega
    rw [hDataEq, hPreserve2 _ hLo hHi]
    exact hRanksMem1 v
  have hRowsMem : ∀ y : Vertex H, ∃ lo hi : Nat,
      (t.data[rowStartBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some lo ∧
      (t.data[rowEndBase H.vertexCount H.arcCount + y.val]?).map Fin.val = some hi ∧
      lo ≤ hi ∧ hi ≤ H.arcCount ∧
      hi - lo = (rows.row y).length ∧
      ∀ j : Fin (rows.row y).length,
        (t.data[predBufBase H.vertexCount H.arcCount + lo + j.val]?).map Fin.val =
          some ((rows.row y)[j.val]'j.isLt).val := by
    intro y
    obtain ⟨lo, hiV, h1, h2, h3, h4, h5, h6⟩ := hRowsMem2 y
    exact ⟨lo, hiV, hDataEq ▸ h1, hDataEq ▸ h2, h3, h4, h5, fun j => hDataEq ▸ h6 j⟩
  refine ⟨t, trace, w1 + w2, order, size_order, rank, rows, by unfold stage1WorkFactor; omega,
    hRun, hTrace, hPeak',
    ⟨hNodup, hCovers, hTopo, hRankAt, hRankInc, hRankArc, hOrderMem, hRanksMem, hRowsMem⟩⟩

end Stage1Linked

private theorem stage1BPhaseEq_link {bits c₁ d₁ c₂ d₂ : Nat}
    {h₁ : c₁ ≤ 2 ^ bits} {k₁ : d₁ ≤ 2 ^ bits}
    {h₂ : c₂ ≤ 2 ^ bits} {k₂ : d₂ ≤ 2 ^ bits}
    {p₁ q₁ : Phase (layout bits c₁ d₁ h₁ k₁)}
    {p₂ q₂ : Phase (layout bits c₂ d₂ h₂ k₂)}
    (hp : p₁.code = p₂.code ∧ p₁.haltPC = p₂.haltPC)
    (hq : q₁.code = q₂.code ∧ q₁.haltPC = q₂.haltPC) :
    (p₁.link q₁).code = (p₂.link q₂).code ∧
    (p₁.link q₁).haltPC = (p₂.link q₂).haltPC := by
  refine ⟨?_, ?_⟩
  · simp only [Phase.link, FixedROM.join, hp.1, hp.2, hq.1]
  · simp only [Phase.link, hp.1, hq.2]

theorem stage1BPhase_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits)
    (hb₁ : 4 ≤ 2 ^ bits) (hb₂ : 4 ≤ 2 ^ bits) :
    (stage1BPhase (bits := bits) (hi := h₁) (hw := k₁) hb₁).code =
      (stage1BPhase (bits := bits) (hi := h₂) (hw := k₂) hb₂).code ∧
    (stage1BPhase (bits := bits) (hi := h₁) (hw := k₁) hb₁).haltPC =
      (stage1BPhase (bits := bits) (hi := h₂) (hw := k₂) hb₂).haltPC := by
  have hEq : hb₁ = hb₂ := Subsingleton.elim hb₁ hb₂
  subst hEq
  unfold stage1BPhase stage1BPhases pipelinePhase
  repeat' (refine stage1BPhaseEq_link ?_ ?_)
  all_goals
    first
    | exact rawIncomingPhase_cap_indep h₁ k₁ h₂ k₂
    | exact ⟨rfl, rfl⟩

end PaperB.RamForestProgram.RawBuild
