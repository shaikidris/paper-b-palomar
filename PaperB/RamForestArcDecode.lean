module

public import PaperB.RamForestIncomingArcs

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.ArcDecode

open PaperB.RamProgram
open PaperB.Machine (Word)
open PaperB.RamForestProgram.ArcParents (arcNode IncomingAt rowNodes)

variable {bits inputCap workCap vertices arcs length : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- The immutable source column still uses the original occurrence
indices. The CSR payload contains these indices shifted by n+1. -/
def SourcesAt (input : Input L) (base : Nat) (source : Fin arcs → Fin vertices) : Prop :=
  ∀ e : Fin arcs, (input.words[base + e.val]?).map Fin.val = some (source e).val

def TokensAt (data : Array (Word bits)) (base : Nat)
    (row : Fin length → Fin arcs) : Prop :=
  ∀ i : Fin length, (data[base + i.val]?).map Fin.val = some (vertices + 1 + (row i).val)

structure Banks (bits inputCap workCap vertices arcs length : Nat) where
  inputSource : Nat
  tokens : Nat
  stamps : Nat
  sourcesFit : inputSource + arcs ≤ inputCap
  tokensFit : tokens + length ≤ workCap
  stampsFit : stamps + vertices ≤ workCap

structure ReadParams (b : Banks bits inputCap workCap vertices arcs length) (s : State L) : Prop where
  sourceBase : (reg s registers.stackBase).val = b.inputSource
  tokensBase : (reg s offsetBase).val = b.tokens
  stampsBase : (reg s tinBase).val = b.stamps
  shift : (reg s cmd).val = vertices + 1

/-- Fetch a token, recover its occurrence index, load its original tail,
and read the tail's mark. These are the first seven instructions of the
distinct-predecessor loop body. -/
def readBlock : List (Instr bits 15) :=
  indexedDataRead registers.remain offsetBase registers.ptr ++
  [Instr.sub registers.remain registers.remain cmd] ++
  indexedInputRead registers.value registers.stackBase registers.remain ++
  indexedDataRead registers.childBase tinBase registers.value

private theorem pairPlaced {c : Program L} {pc : Nat} {op0 op1 : Instr bits 15}
    (p : c[pc]? = some op0) (q : c[pc + 1]? = some op1) :
    Placed c pc [op0, op1] := by
  intro i op h
  cases i with
  | zero => rw [Nat.add_zero]; exact p.trans h
  | succ i =>
    cases i with
    | zero => exact q.trans h
    | succ i => simp at h

/-- Execute the raw-row decoder on the actual mutable and immutable word
arrays, preserving both. The returned token, tail and mark are available
in fixed registers, and lookup does not replace the original arc record. -/
theorem readBlock_steps (input : Input L) {b : Banks bits inputCap workCap vertices arcs length}
    (source : Fin arcs → Fin vertices) (row : Fin length → Fin arcs)
    (raw : SourcesAt input b.inputSource source) {c : Program L} {entry : Nat}
    (placed : Placed c entry (readBlock (bits := bits))) (continuation : entry + 7 < c.size)
    (s : State L) (atEntry : s.pc = entry) (params : ReadParams b s)
    (token : TokensAt (vertices := vertices) s.data b.tokens row)
    (i : Fin length) (ptr : (reg s registers.ptr).val = i.val) :
    ∃ t, Steps c input 7 s t ∧ t.pc = entry + 7 ∧ t.data = s.data ∧
      (reg t registers.remain).val = (row i).val ∧
      (reg t registers.value).val = (source (row i)).val ∧
      s.data[b.stamps + (source (row i)).val]? = some (reg t registers.childBase) ∧
      (∀ r : Fin 15, r ≠ registers.remain → r ≠ registers.value →
        r ≠ registers.childBase → reg t r = reg s r) := by
  have part0 : Placed c entry (indexedDataRead registers.remain offsetBase registers.ptr) := by
    apply pairPlaced
    · simpa only [Nat.add_zero] using (placed 0 _ rfl)
    · exact placed 1 _ rfl
  have tokFit := b.tokensFit
  have iFit := i.isLt
  have fit0 : (reg s offsetBase).val + (reg s registers.ptr).val < workCap := by
    rw [params.tokensBase, ptr]; omega
  obtain ⟨v, sv, vpc, tv, vr, vm⟩ := indexedDataRead_steps (input := input) (s := s)
    part0 atEntry (by omega) fit0
  have tokenWord : (reg v registers.remain).val = vertices + 1 + (row i).val := by
    rw [params.tokensBase, ptr] at tv
    have h := congrArg (Option.map Fin.val) tv
    rw [token i] at h
    exact Option.some.inj h
  have unshift : c[v.pc]? = some (.sub registers.remain registers.remain cmd) := by
    rw [vpc]; exact placed 2 _ rfl
  obtain ⟨w, vw, wpc, wVal, wr, wm⟩ := step_sub_at (input := input) unshift (by omega)
  have vShift : (reg v cmd).val = vertices + 1 :=
    (congrArg Fin.val (vr _ (show cmd ≠ registers.remain by decide))).trans params.shift
  have index : (reg w registers.remain).val = (row i).val := by
    rw [wVal, PaperB.WordOps.sub_val, tokenWord, vShift]
    have fit : vertices + 1 + (row i).val < 2 ^ bits := tokenWord ▸ (reg v registers.remain).isLt
    rw [show 2 ^ bits + (vertices + 1 + (row i).val) - (vertices + 1) =
      2 ^ bits + (row i).val by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have part1 : Placed c (entry + 3) (indexedInputRead registers.value registers.stackBase registers.remain) := by
    exact pairPlaced (placed 3 _ rfl) (by
      rw [show entry + 3 + 1 = entry + 4 by omega]
      exact placed 4 _ rfl)
  have sourceBase : (reg w registers.stackBase).val = b.inputSource :=
    (congrArg Fin.val ((wr _ (show registers.stackBase ≠ registers.remain by decide)).trans
      (vr _ (show registers.stackBase ≠ registers.remain by decide)))).trans params.sourceBase
  have srcFit := b.sourcesFit
  have eFit := (row i).isLt
  have fit1 : (reg w registers.stackBase).val + (reg w registers.remain).val < inputCap := by
    rw [sourceBase, index]; omega
  obtain ⟨x, wx, xpc, xt, xr, xm⟩ := indexedInputRead_steps (input := input) (s := w)
    part1 (by omega) (by omega) fit1
  have tail : (reg x registers.value).val = (source (row i)).val := by
    rw [sourceBase, index] at xt
    have h := congrArg (Option.map Fin.val) xt
    rw [raw (row i)] at h
    exact Option.some.inj h
  have part2 : Placed c (entry + 5) (indexedDataRead registers.childBase tinBase registers.value) := by
    exact pairPlaced (placed 5 _ rfl) (by
      rw [show entry + 5 + 1 = entry + 6 by omega]
      exact placed 6 _ rfl)
  have stampBase : (reg x tinBase).val = b.stamps :=
    (congrArg Fin.val ((xr _ (show tinBase ≠ registers.value by decide)).trans
      ((wr _ (show tinBase ≠ registers.remain by decide)).trans
       (vr _ (show tinBase ≠ registers.remain by decide))))).trans params.stampsBase
  have stampFit := b.stampsFit
  have uFit := (source (row i)).isLt
  have fit2 : (reg x tinBase).val + (reg x registers.value).val < workCap := by
    rw [stampBase, tail]; omega
  obtain ⟨t, xt, tpc, got, tr, tm⟩ := indexedDataRead_steps (input := input) (s := x)
    part2 (by omega) (by omega) fit2
  refine ⟨t, sv.append (.cons vw (wx.append xt)), by omega,
    tm.trans (xm.trans (wm.trans vm)), ?_, ?_, ?_, ?_⟩
  · rw [tr _ (show registers.remain ≠ registers.childBase by decide),
      xr _ (show registers.remain ≠ registers.value by decide), index]
  · rw [tr _ (show registers.value ≠ registers.childBase by decide), tail]
  · rw [stampBase, tail, xm, wm, vm] at got
    exact got.symm
  · intro r nr nv nc
    exact (tr r nc).trans ((xr r nv).trans ((wr r nr).trans (vr r nr)))

/-- The raw incoming producer discharges the decoder's token-word input
for each quotient vertex. The proof never creates a runtime row array. -/
theorem tokenView_of_incoming {a : Finish.Arena bits workCap (vertices + 1 + arcs)}
    {heads : Fin arcs → Fin vertices} {data : Array (Word bits)}
    (image : IncomingAt a heads data) (v : Fin vertices) :
    ∃ lo stop : Word bits, ∃ row : Fin (rowNodes heads v).length → Fin arcs,
      data[a.offsets + (ArcParents.headNode arcs v).val]? = some lo ∧
      data[a.offsets + (ArcParents.headNode arcs v).val + 1]? = some stop ∧
      stop.val = lo.val + (rowNodes heads v).length ∧ stop.val ≤ a.children ∧
      TokensAt (vertices := vertices) data (a.payload + lo.val) row ∧
      (∀ i, heads (row i) = v) ∧
      (∀ i : Fin (rowNodes heads v).length,
        (rowNodes heads v)[i.val]'i.isLt = arcNode vertices (row i)) := by
  classical
  obtain ⟨lo, stop, first, last, width, fit, cells⟩ := image v
  let row := fun i => Classical.choose (cells i)
  refine ⟨lo, stop, row, first, last, width, fit, ?_, ?_, ?_⟩
  · intro i
    exact (Classical.choose_spec (cells i)).2.2
  · intro i
    exact (Classical.choose_spec (cells i)).2.1
  · intro i
    exact (Classical.choose_spec (cells i)).1

end PaperB.RamForestProgram.ArcDecode
