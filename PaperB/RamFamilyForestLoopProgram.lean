module

public import PaperB.RamQuotientEmitter
public import PaperB.RamDataSliceAdapter
public import PaperB.RamForestRawBuild

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.1 Family Forest Loop (`PaperB.RamFamilyForestLoop`):
Fixed 16-register word-RAM program `familyForestLoopProgram` consuming the
`StaticTreeSlice` at `treeBase` and the emitted quotient-arc workspace
`[emitBase .. emitBase + 3*n + 3*m + 3)` produced by `quotientEmitProgram`.

For every quotient owner `d = 0 .. Q - 1`:
1. Stably counting-sorts `S.emittedArcs d` by `srcLocal ∈ 0 .. n_d - 1`, staging
   `[n_d, m_d, 0] ++ sortedSrc ++ sortedHead` into reusable scratch `loopSubInBase`
   and writing retained sorted `(sortedSrc, sortedHead, sortedTailEntry)` back
   into `[qStart[d] .. qStart[d+1])` inside `emitBase` for `RamExitSummaryBuild`.
2. If `n_d < 3`, writes 6 zeros at `ownerForestPtrsBase + 6 * d .. + 6`.
3. If `3 ≤ n_d`, saves loop registers into `loopSubStateBase`, executes the
   relocated lifted 15-register proper-loss forest constructor (`largeBuildProgram`)
   via `inPtrAddr = 0`, `dataPtrAddr = 1` on reusable `loopSubWorkBase`, restores
   registers, scans `N_d = 1 + max_{j < D_d} slots[j]`, copies the serialized
   `WordColumns` payload (`w_d.wordCount` words) into `forestArena`, and records
   the 6 bank pointers `(dictPtr, backFstPtr, backSndPtr, labelsPtr, fEntryPtr, fStopPtr)`
   at `ownerForestPtrsBase + 6 * d .. + 6`.
-/

namespace PaperB.RamFamilyForestLoop

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (zero add sub ltb ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamDagReach
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.RamForestProgram.Sweep
open PaperB.RamForestProgram.ArcDecode
open PaperB.RamForestProgram.ArcParents
open PaperB.RamDataSliceAdapter
open PaperB.RamQuotientEmitter
open PaperB.RetainedProperLoss
open PaperB.ForestSlimIndex
open PaperB.ForestHead (Vertex)
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next)
open PaperB.ForestIncomingRaw (Entry supplied arcHead)
open _root_.EX24.PreparedSweep (orderedConfig)

section Step16Helpers

theorem step16_imm {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k : Nat}
    (hpc : s.pc = k) {dst : Fin 16} {v : Word bits}
    (hAt : code[k]? = some (.imm dst v)) (hFit : k + 1 < code.size) :
    ∃ t, step code input s = some (.next t) ∧ t.pc = k + 1 ∧
      reg t dst = v ∧ (∀ r : Fin 16, r ≠ dst → reg t r = reg s r) ∧ t.data = s.data := by
  obtain ⟨t, ht, hpc', hd, ho, hm⟩ :=
    step_imm16 (code := code) (input := input) (s := s) (by rw [hpc]; exact hAt) (by rw [hpc]; exact hFit)
  exact ⟨t, ht, hpc'.trans (congrArg (· + 1) hpc), hd, ho, hm⟩

theorem wordOption_eq_of_map_val {bits : Nat} {a b : Option (Word bits)}
    (h : a.map Fin.val = b.map Fin.val) : a = b := by
  cases a <;> cases b
  · rfl
  · cases h
  · cases h
  · exact congrArg some (Fin.ext (Option.some.inj h))

end Step16Helpers

section LayoutOffsets

/-- Constant scratch addresses in `data[0..3)` for the relocated 15-register submachine
and loop state save/restore (`< 3 ≤ 3 * n`). -/
def inPtrAddr : Nat := 0
def dataPtrAddr : Nat := 1
def statePtrAddr : Nat := 2

def loopSubInBase (loopBase : Nat) : Nat := loopBase
def loopSubWorkBase (loopBase _n m : Nat) : Nat := loopBase + rawInputCap m
def loopSubStateBase (loopBase n m : Nat) : Nat := loopSubWorkBase loopBase n m + rawWorkCap n m
def loopDegBase (loopBase n m : Nat) : Nat := loopSubStateBase loopBase n m + 16
def loopCursorBase (loopBase n m : Nat) : Nat := loopDegBase loopBase n m + n
def loopSortEntryBase (loopBase n m : Nat) : Nat := loopCursorBase loopBase n m + (n + 1)
def ownerForestPtrsBase (loopBase n m : Nat) : Nat := loopSortEntryBase loopBase n m + m
def forestArenaBase (loopBase n m : Nat) : Nat := ownerForestPtrsBase loopBase n m + 6 * n
def loopWorkWords (n m : Nat) : Nat := 78 * n + 10 * m + 37

theorem forestArenaEnd_eq (loopBase n m : Nat) :
    forestArenaBase loopBase n m + 38 * n = loopBase + loopWorkWords n m := by
  unfold forestArenaBase ownerForestPtrsBase loopSortEntryBase loopCursorBase
    loopDegBase loopSubStateBase loopSubWorkBase loopWorkWords rawInputCap rawWorkCap
  omega

/-- Registers expected at entry to `familyForestLoopProgram`. -/
structure LoopEntryRegs (n m root Q treeBase emitBase loopBase : Nat)
    {bits inputCap workCap : Nat} {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (s : State (layout16 bits inputCap workCap hi hw)) : Prop where
  consts : ConstRegs n m root s
  qVal : (reg s r5).val = Q
  treeBaseVal : (reg s r6).val = treeBase
  emitBaseVal : (reg s r7).val = emitBase
  loopBaseVal : (reg s r8).val = loopBase

end LayoutOffsets

section BankSizesAndLargeBuild

private theorem foldl_max_le {xs : Array Nat} {d bound : Nat}
    (hAll : ∀ i < d, (xs[i]?).getD 0 ≤ bound) :
    ∀ acc ≤ bound,
      (List.range d).foldl (fun a i => max a ((xs[i]?).getD 0)) acc ≤ bound := by
  induction d with
  | zero => intro acc ha; simp [ha]
  | succ d ih =>
    intro acc ha
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hprev := ih (fun i hi => hAll i (Nat.lt_succ_of_lt hi)) acc ha
    exact Nat.max_le.mpr ⟨hprev, hAll d (Nat.lt_succ_self d)⟩

private theorem foldl_max_mem_le {xs : Array Nat} {d i : Nat} (hi : i < d) :
    ∀ acc, (xs[i]?).getD 0 ≤ (List.range d).foldl (fun a j => max a ((xs[j]?).getD 0)) acc := by
  induction d with
  | zero => omega
  | succ d ih =>
    intro acc
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    by_cases he : i = d
    · subst he; exact Nat.le_max_right _ _
    · exact Nat.le_trans (ih (by omega) acc) (Nat.le_max_left _ _)

private theorem lookup_lt_size {dict : Array PaperB.PairLookup.Key}
    (hs : PaperB.PairLookup.StrictSorted dict) {key : PaperB.PairLookup.Key} {i : Nat}
    (h : (PaperB.PairLookup.lookup dict key).1 = some i) : i < dict.size :=
  ((PaperB.PairLookup.lookup_eq_some_iff dict key hs i).mp h).1

private theorem nodeKey?_some_of_ne_root (H : LabelledQuotient) (rank : Vertex H → Nat)
    (z : Fin ((H.buildProperLossForest rank).realNodeCount + 1))
    (hz : z ≠ (H.buildProperLossForest rank).rootNode) :
    ((H.buildProperLossForest rank).nodeKey? z).isSome = true := by
  cases hk : (H.buildProperLossForest rank).nodeKey? z with
  | some _ => rfl
  | none =>
    have hEq := H.buildProperLossForest_nodeKey?_inj rank
      (hk.trans (H.buildProperLossForest_nodeKey?_root rank).symm)
    exact False.elim (hz hEq)

/-- Exact bank sizes of `packWordColumns r hWidth` and exact recovery of
`N_H = w.entry.size = 1 + max_{j < D_H} slots[j]` from the serialized dictionary. -/
theorem packWordColumns_bank_sizes {H : LabelledQuotient} [DecidableEq H.CutPair]
    {p : PaperB.ForestDictionary.Rows H} {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    {bits : Nat} (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits) :
    let w := packWordColumns r hWidth
    let D := ((w.dictionary[0]?).map Fin.val).getD 0
    1 ≤ w.entry.size ∧
    w.dictionary.size = 1 + 3 * D ∧
    w.back.tagAndFirst.size = H.vertexCount + 1 ∧
    w.back.second.size = H.vertexCount + 1 ∧
    w.labels.size = H.vertexCount ∧
    w.stop.size = w.entry.size ∧
    w.entry.size = 1 + (List.range D).foldl
      (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 := by
  intro w D
  let s := ofOrderedReader r
  have hFits := dictionary_fits r hWidth
  have hRep := FlatPairDictionary.serialize_represents s hFits
  obtain ⟨F, up, hG, _, ⟨E⟩⟩ := r.index.ok.2.2
  have hD_eq : D = s.dict.size := FlatPairDictionary.rowCount_serialize s hFits
  have hDictSz : w.dictionary.size = 1 + 3 * D := by
    change (FlatPairDictionary.serialize s hFits).size = _
    rw [FlatPairDictionary.retained_words, hD_eq]
    have hSlotSz : s.slots.size = s.dict.size := hG.slot_size
    omega
  have hBackSz := packBackWords_size s (by omega : H.vertexCount < 2 ^ bits)
  have hBackNode : s.back.size = H.vertexCount + 1 := hG.back_size
  have hBack1 : w.back.tagAndFirst.size = H.vertexCount + 1 := hBackSz.1.trans hBackNode
  have hBack2 : w.back.second.size = H.vertexCount + 1 := hBackSz.2.trans hBackNode
  have hLabSz : w.labels.size = H.vertexCount := by
    change (BoundedScalarArray.pack s.labels _ _).size = H.vertexCount
    rw [BoundedScalarArray.size_pack]
    exact r.index.ok.1
  have hNodeEq : nodeCount (orderedConfig p large) r.out = r.out.tables.next :=
    nodeCount_eq_next r.index.ok
  have hEntrySz : w.entry.size = r.out.tables.next := by
    change (BoundedScalarArray.pack s.entry _ _).size = r.out.tables.next
    rw [BoundedScalarArray.size_pack, ← hNodeEq]
    exact r.index.reader.layout.endpoints.entry.len
  have hStopSz : w.stop.size = w.entry.size := by
    change (BoundedScalarArray.pack s.stop _ _).size = _
    rw [BoundedScalarArray.size_pack, hEntrySz, ← hNodeEq]
    exact r.index.reader.layout.endpoints.stop.len
  have hPosNext : 1 ≤ r.out.tables.next := by
    have hl := E.label_lt H.root True.intro
    rw [hG.size_eq] at hl
    omega
  have hSlotVal : ∀ j < D,
      ((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0 = (s.slots[j]?).getD 0 := by
    intro j hj
    have hjD : j < s.dict.size := hD_eq ▸ hj
    have hjSlot : j < s.slots.size := hG.slot_size ▸ hjD
    have hjSlice : j < (FlatPairDictionary.slotSlice (FlatPairDictionary.serialize s hFits) hRep.valid).len := by
      rw [hRep.slot_len]; exact hjSlot
    have hEq := hRep.slot_eq j hjSlice hjSlot
    have hBase : (FlatPairDictionary.slotSlice (FlatPairDictionary.serialize s hFits) hRep.valid).base.val =
        1 + 2 * D := by
      change FlatPairDictionary.slotBase (FlatPairDictionary.rowCount (FlatPairDictionary.serialize s hFits)) =
        1 + 2 * D
      rw [FlatPairDictionary.rowCount_serialize, ← hD_eq]
      unfold FlatPairDictionary.slotBase FlatPairDictionary.secondBase
      omega
    have hIdxLt : 1 + 2 * D + j < w.dictionary.size := by
      rw [hDictSz]; omega
    have hGetVal :
        ((FlatPairDictionary.slotSlice (FlatPairDictionary.serialize s hFits) hRep.valid).get j hjSlice).val =
          ((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0 := by
      change ((FlatPairDictionary.serialize s hFits)[(FlatPairDictionary.slotSlice
          (FlatPairDictionary.serialize s hFits) hRep.valid).base.val + j]'_).val = _
      have hSerEq : FlatPairDictionary.serialize s hFits = w.dictionary := rfl
      rw [getElem?_pos w.dictionary (1 + 2 * D + j) hIdxLt, Option.map_some, Option.getD_some]
      congr 1
      simp only [hSerEq, hBase]
    exact hGetVal.symm.trans hEq
  have hFoldEq :
      (List.range D).foldl (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 =
      (List.range D).foldl (fun acc j => max acc ((s.slots[j]?).getD 0)) 0 := by
    suffices ∀ xs : List Nat, (∀ j ∈ xs, j < D) → ∀ acc,
        xs.foldl (fun a j => max a (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) acc =
        xs.foldl (fun a j => max a ((s.slots[j]?).getD 0)) acc from
      this (List.range D) (fun j hj => List.mem_range.mp hj) 0
    intro xs
    induction xs with
    | nil => intro _ acc; rfl
    | cons x xs ih =>
      intro hx acc
      simp only [List.foldl_cons]
      rw [hSlotVal x (hx x List.mem_cons_self)]
      exact ih (fun j hj => hx j (List.mem_cons_of_mem x hj)) _
  have hUpper : (List.range D).foldl (fun acc j => max acc ((s.slots[j]?).getD 0)) 0 ≤ r.out.tables.next - 1 := by
    apply foldl_max_le _ 0 (Nat.zero_le _)
    intro j _
    by_cases h0 : r.out.tables.slotAt j = 0
    · change r.out.tables.slotAt j ≤ _
      omega
    · obtain ⟨q, _, hq⟩ := hG.forward j h0
      have hBack := (hG.backward _ q hq).1
      change r.out.tables.slotAt j ≤ r.out.tables.next - 1
      omega
  have hLower : r.out.tables.next - 1 ≤ (List.range D).foldl (fun acc j => max acc ((s.slots[j]?).getD 0)) 0 := by
    by_cases h1 : r.out.tables.next = 1
    · omega
    · have haLt : r.out.tables.next - 1 < F.size := by rw [hG.size_eq]; omega
      let a : Fin F.size := ⟨r.out.tables.next - 1, haLt⟩
      have hneRoot : E.image a ≠ (H.buildProperLossForest rank).rootNode := by
        intro heq
        have h0Lt : 0 < F.size := by rw [hG.size_eq]; omega
        have hRootEq : E.image a = E.image ⟨0, h0Lt⟩ :=
          heq.trans (E.root_eq h0Lt).symm
        have hFinEq := congrArg Fin.val (E.injective hRootEq)
        dsimp [a] at hFinEq
        omega
      have hBackA := E.back_eq a
      cases hK : (H.buildProperLossForest rank).nodeKey? (E.image a) with
      | none =>
        have hS := nodeKey?_some_of_ne_root H rank (E.image a) hneRoot
        rw [hK] at hS
        simp at hS
      | some q =>
        rw [hK] at hBackA
        obtain ⟨_, _, i, hLook, hSlotEq⟩ := hG.backward a.val q hBackA
        have hiDict : i < (orderedConfig p large).dict.size :=
          lookup_lt_size (orderedConfig p large).sorted hLook
        have hiD : i < D := by rw [hD_eq]; exact hiDict
        have hMem := foldl_max_mem_le (xs := s.slots) hiD 0
        change r.out.tables.slotAt i ≤ _ at hMem
        rw [hSlotEq] at hMem
        exact hMem
  refine ⟨by omega, hDictSz, hBack1, hBack2, hLabSz, hStopSz, ?_⟩
  omega

private theorem large_combined_work_bound (n m w1 w2a w2bc w3 : Nat) (hn : 3 ≤ n)
    (h1 : w1 ≤ stage1WorkFactor * (n + m + 1))
    (h2a : w2a ≤ 120 * (n + 1) * OracleContract.L n)
    (h2bc : w2bc ≤ 5200 * ((n + m + 1) * (OracleContract.L n) ^ 2))
    (h3 : w3 ≤ 232 * n + 159) :
    (w1 + (w2a + w2bc)) + w3 ≤ 11662 * ((n + m) * (OracleContract.L n) ^ 2) := by
  have hL : 1 ≤ OracleContract.L n := OracleContract.one_le_L n
  have hL2 : 1 ≤ (OracleContract.L n) ^ 2 := Nat.pow_pos hL
  have hL_le : OracleContract.L n ≤ (OracleContract.L n) ^ 2 := by
    simpa only [Nat.pow_two] using Nat.le_mul_of_pos_right (OracleContract.L n) hL
  let LSq := (OracleContract.L n) ^ 2
  let B := (n + m + 1) * LSq
  have hw1 : w1 ≤ 275 * B :=
    Nat.le_trans h1 (Nat.mul_le_mul_left 275 (Nat.le_mul_of_pos_right _ hL2))
  have hw2a : w2a ≤ 120 * B := by
    calc w2a ≤ 120 * (n + 1) * OracleContract.L n := h2a
      _ ≤ 120 * (n + m + 1) * LSq :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 120 (by omega)) hL_le
      _ = 120 * B := Nat.mul_assoc _ _ _
  have hw2bc : w2bc ≤ 5200 * B := h2bc
  have hw3 : w3 ≤ 232 * B :=
    Nat.le_trans (by omega : w3 ≤ 232 * (n + m + 1))
      (Nat.mul_le_mul_left 232 (Nat.le_mul_of_pos_right _ hL2))
  have hsum : (w1 + (w2a + w2bc)) + w3 ≤ 5827 * B := by omega
  have hnm : n + m + 1 ≤ 2 * (n + m) := by omega
  calc (w1 + (w2a + w2bc)) + w3
      ≤ 5827 * B := hsum
    _ ≤ 5831 * B := by omega
    _ ≤ 5831 * ((2 * (n + m)) * LSq) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hnm)
    _ = 11662 * ((n + m) * LSq) := by
      rw [Nat.mul_assoc 2 (n + m) LSq, ← Nat.mul_assoc 5831 2 ((n + m) * LSq)]

private noncomputable def liftStage2Output' {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {dictRows : PaperB.ForestDictionary.Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult dictRows order size_order rank large}
    {width : 1 + 18 * H.vertexCount < 2 ^ bits}
    {u v : State (layout bits inputCap workCap hi hw)}
    (hRegs : v.regs = u.regs) (hData : v.data = u.data)
    (out : Stage2Output H r width u) :
    Stage2Output H r width v :=
  let hRegEq : ∀ regId : Fin 15, reg v regId = reg u regId := fun regId => by
    cases u; cases v; dsimp at hRegs; subst hRegs; rfl
  { arena := out.arena
    ctrl :=
      { count_eq := (congrArg Fin.val (hRegEq count)).trans out.ctrl.count_eq
        one := (congrArg Fin.val (hRegEq registers.one)).trans out.ctrl.one
        zero := (congrArg Fin.val (hRegEq registers.zero)).trans out.ctrl.zero
        stackBase_eq := (congrArg Fin.val (hRegEq registers.stackBase)).trans out.ctrl.stackBase_eq
        tin_eq := (congrArg Fin.val (hRegEq tinBase)).trans out.ctrl.tin_eq
        tout_eq := (congrArg Fin.val (hRegEq toutBase)).trans out.ctrl.tout_eq
        offset_eq := (congrArg Fin.val (hRegEq offsetBase)).trans out.ctrl.offset_eq
        child_eq := (congrArg Fin.val (hRegEq childrenBase)).trans out.ctrl.child_eq }
    rootVal := (congrArg Fin.val (hRegEq cmd)).trans out.rootVal
    parents := fun a => by rw [hData]; exact out.parents a
    mass := out.mass
    children := out.children
    place := out.place
    src := out.src
    fits := out.fits
    apart := out.apart
    params :=
      { cursor := (congrArg Fin.val (hRegEq registers.ptr)).trans out.params.cursor
        src := (congrArg Fin.val (hRegEq registers.childBase)).trans out.params.src
        unit := (congrArg Fin.val (hRegEq clk)).trans out.params.unit
        count := (congrArg Fin.val (hRegEq registers.remain)).trans out.params.count }
    sourceAt := fun j hj => by rw [hData]; exact out.sourceAt j hj }

/-- Execute `largeBuildProgram` on any flat acyclic quotient `H` with `3 ≤ H.vertexCount`,
producing `w := packWordColumns r hWidth` along with its exact 6 bank sizes and
`w.entry.size = 1 + max_{j < D} slots[j]`. -/
def PackedWordColumnsSpec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (w : WordColumns bits) (t : State (layout bits inputCap workCap hi hw)) : Prop :=
  let D := ((w.dictionary[0]?).map Fin.val).getD 0
  w.wordCount ≤ workCap ∧
  w.wordCount ≤ 1 + 18 * H.vertexCount ∧
  w.wordCount ≤ 19 * H.vertexCount ∧
  1 ≤ w.entry.size ∧
  w.dictionary.size = 1 + 3 * D ∧
  w.back.tagAndFirst.size = H.vertexCount + 1 ∧
  w.back.second.size = H.vertexCount + 1 ∧
  w.labels.size = H.vertexCount ∧
  w.stop.size = w.entry.size ∧
  w.entry.size = 1 + (List.range D).foldl
    (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
  t.data.extract 0 w.wordCount = packedPayload w ∧
  SerializedProperLossIndex H w

theorem run_large_build_packed {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (hlarge : 3 ≤ H.vertexCount) (flat : H.IsFlat) (acyc : H.IsAcyclic)
    (input : Input (layout bits inputCap workCap hi hw))
    (hRaw : RawQuotientInput input H)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s₀ : State (layout bits inputCap workCap hi hw)) :
    let code := largeBuildProgram hi hw h8
    let L := OracleContract.L H.vertexCount
    ∃ (pH : PaperB.ForestDictionary.Rows H) (dataH : Array (Vertex H))
      (sizeH : dataH.size = H.vertexCount) (rankH : Vertex H → Nat)
      (_incH : ∀ i j : Fin H.vertexCount, i.val < j.val →
        rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i) <
          rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH j))
      (_covH : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
        _root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i = v)
      (_rArcH : ∀ u v : Vertex H, H.HasQuotientArc u v → rankH u < rankH v)
      (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
      (t : State (layout bits inputCap workCap hi hw)) (work : Nat),
      let w := packWordColumns ordResH hWidth
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      w.wordCount ≤ workCap ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      w.wordCount ≤ 19 * H.vertexCount ∧
      1 ≤ w.entry.size ∧
      w.dictionary.size = 1 + 3 * D ∧
      w.back.tagAndFirst.size = H.vertexCount + 1 ∧
      w.back.second.size = H.vertexCount + 1 ∧
      w.labels.size = H.vertexCount ∧
      w.stop.size = w.entry.size ∧
      w.entry.size = 1 + (List.range D).foldl
        (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      work ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) ∧
      SerializedProperLossIndex H w ∧
      run code input work (Phase.initial s₀) = some ⟨t, work⟩ := by
  intro code L
  obtain ⟨t1, _, w1, order, size_order, rank, rows, hw1, hRun1, _, _, hSt1⟩ :=
    run_stage1 input hRaw acyc hWork s₀
  have hRun1' :
      run (stage1Phase (hi := hi) (hw := hw) (by omega)).code input w1
        (Phase.initial s₀) = some ⟨t1, w1⟩ := hRun1
  obtain ⟨t2, _, w2a, hw2a, hRun2a, _, _, dso⟩ :=
    run_dict_sort h8 H input hRaw hWork t1 hSt1
  let r : PaperB.OrderedReaderResult rows order size_order rank hlarge :=
    runOrderedReaderFast rows order size_order rank hlarge
      dso.stage1.rank_increasing dso.stage1.covers dso.stage1.rank_arc flat
  obtain ⟨t3, _, w2bc, hw2bc, hRun2bc, _, _, ⟨out3⟩⟩ :=
    run_sweep h8 H input hRaw hWork rows hlarge dso r hWidth
  have hSweepPos : 0 < (sweepPhase hi hw h8).code.size := by
    have := (sweepPhase hi hw h8).haltFits; omega
  obtain ⟨t23, _, hR23, hD23, hRun23, _, _⟩ :=
    run_linked_pair (dictSortPhase hi hw h8) (sweepPhase hi hw h8).code
      hSweepPos hRun2a hRun2bc
  have hDSPos : 0 < ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8)).code.size := by
    have := ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8)).haltFits; omega
  obtain ⟨t123, _, hR123, hD123, hRun123, _, _⟩ :=
    run_linked_pair (stage1Phase (hi := hi) (hw := hw) (by omega))
      ((dictSortPhase hi hw h8).link (sweepPhase hi hw h8)).code
      hDSPos hRun1' hRun23
  have hStage2 : Nonempty (Stage2Output H r hWidth t123) :=
    ⟨liftStage2Output' (hR123.trans hR23) (hD123.trans hD23) out3⟩
  obtain ⟨t4, _, w3, hwCap, hExt, hw3, hwRet, hIdx, hRunAll, _, _⟩ :=
    run_linked_stage2_finish (largeFrontPhase hi hw h8) input r hWidth hRun123 hStage2
  have hWorkBnd := large_combined_work_bound H.vertexCount H.arcCount w1 w2a w2bc w3
    hlarge hw1 hw2a hw2bc hw3
  have hSizes := packWordColumns_bank_sizes r hWidth
  refine ⟨rows, order, size_order, rank, dso.stage1.rank_increasing, dso.stage1.covers,
    dso.stage1.rank_arc, r, t4, (w1 + (w2a + w2bc)) + w3,
    hwCap, hwRet, by omega, hSizes.1, hSizes.2.1, hSizes.2.2.1, hSizes.2.2.2.1,
    hSizes.2.2.2.2.1, hSizes.2.2.2.2.2.1, hSizes.2.2.2.2.2.2, hExt, hWorkBnd, hIdx, hRunAll⟩

theorem run_large_build_exact {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (hlarge : 3 ≤ H.vertexCount) (flat : H.IsFlat) (acyc : H.IsAcyclic)
    (input : Input (layout bits inputCap workCap hi hw))
    (hRaw : RawQuotientInput input H)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hWidth : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s₀ : State (layout bits inputCap workCap hi hw)) :
    let code := largeBuildProgram hi hw h8
    let L := OracleContract.L H.vertexCount
    ∃ (w : WordColumns bits) (t : State (layout bits inputCap workCap hi hw)) (work : Nat),
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      w.wordCount ≤ workCap ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      w.wordCount ≤ 19 * H.vertexCount ∧
      1 ≤ w.entry.size ∧
      w.dictionary.size = 1 + 3 * D ∧
      w.back.tagAndFirst.size = H.vertexCount + 1 ∧
      w.back.second.size = H.vertexCount + 1 ∧
      w.labels.size = H.vertexCount ∧
      w.stop.size = w.entry.size ∧
      w.entry.size = 1 + (List.range D).foldl
        (fun acc j => max acc (((w.dictionary[1 + 2 * D + j]?).map Fin.val).getD 0)) 0 ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      work ≤ 11662 * ((H.vertexCount + H.arcCount) * L ^ 2) ∧
      SerializedProperLossIndex H w ∧
      run code input work (Phase.initial s₀) = some ⟨t, work⟩ := by
  obtain ⟨_, _, _, _, _, _, _, r, t4, work, hRest⟩ :=
    run_large_build_packed h8 H hlarge flat acyc input hRaw hWork hWidth s₀
  exact ⟨packWordColumns r hWidth, t4, work, hRest⟩

end BankSizesAndLargeBuild

section CountingSortModel

/-- Stable counting-sort bucket list of `arcs : List (EmittedArc Q)` grouped by
`srcLocal ∈ 0 .. n_d - 1`. -/
def countingSortedArcs {Q : Nat} (n_d : Nat) (arcs : List (EmittedArc Q)) : List (EmittedArc Q) :=
  (List.finRange n_d).flatMap (fun u => arcs.filter (fun ea => ea.srcLocal == u.val))

/-- Bucket degree of `u` in `arcs`. -/
def bucketDeg {Q : Nat} (arcs : List (EmittedArc Q)) (u : Nat) : Nat :=
  (arcs.filter (fun ea => ea.srcLocal == u)).length

/-- Bucket start offset of `u` in `countingSortedArcs n_d arcs`. -/
def bucketStart {Q : Nat} (arcs : List (EmittedArc Q)) (u : Nat) : Nat :=
  ((List.range u).map (bucketDeg arcs)).sum

theorem bucketStart_zero {Q : Nat} (arcs : List (EmittedArc Q)) :
    bucketStart arcs 0 = 0 := rfl

theorem bucketStart_succ {Q : Nat} (arcs : List (EmittedArc Q)) (u : Nat) :
    bucketStart arcs (u + 1) = bucketStart arcs u + bucketDeg arcs u := by
  unfold bucketStart
  rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

private theorem sum_map_finRange_eq_sum_range {n : Nat} (f : Nat → Nat) :
    ((List.finRange n).map (fun u : Fin n => f u.val)).sum = ((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.finRange_succ_last, List.map_append, List.sum_append, List.map_map]
    simp only [Function.comp_def, Fin.val_castSucc, List.map_singleton, List.sum_singleton, Fin.val_last]
    rw [ih, List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]

theorem sum_bucketDeg_all {Q n_d : Nat} (arcs : List (EmittedArc Q))
    (hBnd : ∀ ea ∈ arcs, ea.srcLocal < n_d) :
    bucketStart arcs n_d = arcs.length := by
  unfold bucketStart
  rw [← sum_map_finRange_eq_sum_range (bucketDeg arcs)]
  induction arcs with
  | nil =>
    clear hBnd
    induction (List.finRange n_d) with
    | nil => rfl
    | cons _ _ ih => simp [bucketDeg]; exact ih
  | cons a xs ih =>
    have ha : a.srcLocal < n_d := hBnd a List.mem_cons_self
    have hxs : ∀ ea ∈ xs, ea.srcLocal < n_d := fun ea h => hBnd ea (List.mem_cons_of_mem a h)
    have ih' := ih hxs
    have hSplit : ∀ u : Fin n_d,
        bucketDeg (a :: xs) u.val = (if a.srcLocal = u.val then 1 else 0) + bucketDeg xs u.val := by
      intro u
      unfold bucketDeg
      by_cases he : a.srcLocal = u.val
      · simp [he, Nat.add_comm]
      · simp [beq_false_of_ne he, he]
    have hMap : ((List.finRange n_d).map (fun u : Fin n_d => bucketDeg (a :: xs) u.val)).sum =
        ((List.finRange n_d).map (fun u : Fin n_d => if a.srcLocal = u.val then 1 else 0)).sum +
        ((List.finRange n_d).map (fun u : Fin n_d => bucketDeg xs u.val)).sum := by
      clear ih ih' ha hxs
      suffices ∀ us : List (Fin n_d),
          (us.map (fun u => bucketDeg (a :: xs) u.val)).sum =
          (us.map (fun u => if a.srcLocal = u.val then 1 else 0)).sum +
          (us.map (fun u => bucketDeg xs u.val)).sum from
        this (List.finRange n_d)
      intro us
      induction us with
      | nil => simp
      | cons u us ihu => simp only [List.map_cons, List.sum_cons, hSplit u, ihu]; omega
    have hOne : ((List.finRange n_d).map (fun u : Fin n_d => if a.srcLocal = u.val then 1 else 0)).sum = 1 := by
      let u0 : Fin n_d := ⟨a.srcLocal, ha⟩
      suffices ∀ us : List (Fin n_d), us.Nodup → u0 ∈ us →
          (us.map (fun u => if a.srcLocal = u.val then 1 else 0)).sum = 1 from
        this (List.finRange n_d) (List.nodup_finRange n_d) (List.mem_finRange u0)
      intro us
      induction us with
      | nil => intro _ hm; simp at hm
      | cons u us ihu =>
        intro hnd hm
        have hnd' := List.nodup_cons.mp hnd
        simp only [List.map_cons, List.sum_cons]
        by_cases he : u0 = u
        · have hZero : (us.map (fun v => if a.srcLocal = v.val then 1 else 0)).sum = 0 := by
            have hna : u0 ∉ us := fun e => hnd'.1 (he ▸ e)
            clear ihu hm hnd hnd' he u
            induction us with
            | nil => rfl
            | cons v vs ihv =>
              have hne' : a.srcLocal ≠ v.val := fun e =>
                hna ((Fin.ext e : u0 = v) ▸ List.mem_cons_self)
              have hna' : u0 ∉ vs := fun e => hna (List.mem_cons_of_mem v e)
              simp only [List.map_cons, List.sum_cons, hne', ↓reduceIte, Nat.zero_add]
              exact ihv hna'
          have hValEq : a.srcLocal = u.val := congrArg Fin.val he
          have hHead : (if a.srcLocal = u.val then 1 else 0) = 1 := ite_eq_left hValEq
          rw [hHead, hZero]
        · have hne : a.srcLocal ≠ u.val := fun e => he (Fin.ext e)
          have hmem : u0 ∈ us := by
            cases List.mem_cons.mp hm with
            | inl e => exact False.elim (he e)
            | inr e => exact e
          simp only [hne, ↓reduceIte, Nat.zero_add]
          exact ihu hnd'.2 hmem
    rw [hMap, hOne, ih']
    simp [Nat.add_comm]

theorem countingSortedArcs_length {Q n_d : Nat} (arcs : List (EmittedArc Q))
    (hBnd : ∀ ea ∈ arcs, ea.srcLocal < n_d) :
    (countingSortedArcs n_d arcs).length = arcs.length := by
  unfold countingSortedArcs
  rw [List.length_flatMap]
  change ((List.finRange n_d).map (fun u : Fin n_d => bucketDeg arcs u.val)).sum = arcs.length
  rw [sum_map_finRange_eq_sum_range (bucketDeg arcs)]
  exact sum_bucketDeg_all arcs hBnd

private theorem flatMap_finRange_getElem {α : Type _} (n : Nat) (f : Fin n → List α)
    (u : Fin n) (k : Nat) (hk : k < (f u).length) :
    let pref := ((List.range u.val).map (fun j => if h : j < n then (f ⟨j, h⟩).length else 0)).sum
    ∃ hLt : pref + k < ((List.finRange n).flatMap f).length,
      ((List.finRange n).flatMap f)[pref + k]'hLt = (f u)[k]'hk := by
  induction n generalizing k with
  | zero => exact Fin.elim0 u
  | succ n ih =>
    intro pref
    by_cases hu : u.val < n
    · let u' : Fin n := ⟨u.val, hu⟩
      have hfu : f u = f ⟨u'.val, Nat.lt_succ_of_lt u'.isLt⟩ := rfl
      have hk' : k < (f ⟨u'.val, Nat.lt_succ_of_lt u'.isLt⟩).length := hfu ▸ hk
      obtain ⟨hLt', hEq'⟩ := ih (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) u' k hk'
      have hPref : pref = ((List.range u'.val).map (fun j =>
          if h : j < n then (f ⟨j, Nat.lt_succ_of_lt h⟩).length else 0)).sum := by
        dsimp only [pref]
        congr 1
        apply List.map_congr_left
        intro j hj
        have hjn : j < n := Nat.lt_trans (List.mem_range.mp hj) hu
        simp [hjn, Nat.lt_succ_of_lt hjn]
      have hSplit : (List.finRange (n + 1)).flatMap f =
          (List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ++
            f ⟨n, Nat.lt_succ_self n⟩ := by
        rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.flatMap_map]
        rfl
      have hLt : pref + k < ((List.finRange (n + 1)).flatMap f).length := by
        rw [hSplit, List.length_append, hPref]
        have : ((List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).length ≥
            ((List.range u'.val).map (fun j =>
              if h : j < n then (f ⟨j, Nat.lt_succ_of_lt h⟩).length else 0)).sum + k + 1 := by
          change _ ≥ _
          exact hLt'
        omega
      refine ⟨hLt, ?_⟩
      simp only [hSplit]
      have hPos' : pref + k <
          ((List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).length := by
        rw [hPref]; exact hLt'
      rw [List.getElem_append_left hPos']
      simpa only [hPref] using hEq'
    · have huEq : u.val = n := by have := u.isLt; omega
      have hSplit : (List.finRange (n + 1)).flatMap f =
          (List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩) ++
            f ⟨n, Nat.lt_succ_self n⟩ := by
        rw [List.finRange_succ_last, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
          List.append_nil, List.flatMap_map]
        rfl
      have hPref : pref =
          ((List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).length := by
        dsimp only [pref]
        rw [huEq, List.length_flatMap, ← sum_map_finRange_eq_sum_range]
        congr 1
        apply List.map_congr_left
        intro j _
        simp [Nat.lt_succ_of_lt j.isLt]
      have huLast : u = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext huEq
      have hkLast : k < (f ⟨n, Nat.lt_succ_self n⟩).length := huLast ▸ hk
      have hLt : pref + k < ((List.finRange (n + 1)).flatMap f).length := by
        rw [hSplit, List.length_append, ← hPref]; omega
      refine ⟨hLt, ?_⟩
      simp only [hSplit]
      rw [List.getElem_append_right (by omega)]
      have hSub : pref + k - ((List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).length = k := by
        omega
      have hCast : ((f ⟨n, Nat.lt_succ_self n⟩)[pref + k -
          ((List.finRange n).flatMap (fun j => f ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩)).length]'(by omega)) =
          (f ⟨n, Nat.lt_succ_self n⟩)[k]'hkLast := by
        congr 1
      rw [hCast]
      subst huLast; rfl

theorem countingSortedArcs_bucket_getElem {Q n_d : Nat} (arcs : List (EmittedArc Q))
    (u : Fin n_d) (k : Nat) (hk : k < bucketDeg arcs u.val) :
    ∃ hLt : bucketStart arcs u.val + k < (countingSortedArcs n_d arcs).length,
      (countingSortedArcs n_d arcs)[bucketStart arcs u.val + k]'hLt =
        (arcs.filter (fun ea => ea.srcLocal == u.val))[k]'hk := by
  let f : Fin n_d → List (EmittedArc Q) := fun v => arcs.filter (fun ea => ea.srcLocal == v.val)
  have h := flatMap_finRange_getElem n_d f u k hk
  have hPref : bucketStart arcs u.val =
      ((List.range u.val).map (fun j =>
        if h : j < n_d then (arcs.filter (fun ea => ea.srcLocal == j)).length else 0)).sum := by
    unfold bucketStart bucketDeg
    congr 1
    apply List.map_congr_left
    intro j hj
    have hjn : j < n_d := Nat.lt_trans (List.mem_range.mp hj) u.isLt
    simp [hjn]
  rw [← hPref] at h
  exact h

private theorem foldCons_supplied (H : LabelledQuotient) :
    (supplied H).reverse =
      (List.finRange H.vertexCount).flatMap
        (fun u : Fin H.vertexCount => (H.outArcs u).map (fun a => (u, a))) := by
  have hFold : ∀ (us : List (Fin H.vertexCount)) (acc : List (Entry H)),
      (us.foldl (fun acc u => (H.outArcs u).foldl (fun es a => (u, a) :: es) acc) acc).reverse =
        acc.reverse ++ us.flatMap (fun u => (H.outArcs u).map (fun a => (u, a))) := by
    intro us
    induction us with
    | nil => intro acc; simp
    | cons u us ih =>
      intro acc
      simp only [List.foldl_cons, ih]
      have hPush : ((H.outArcs u).foldl (fun es a => (u, a) :: es) acc).reverse =
          acc.reverse ++ (H.outArcs u).map (fun a => (u, a)) := by
        have hRev : ∀ (xs : List (QuotientArc H.origVertexCount H.vertexCount)) (acc' : List (Entry H)),
            (xs.foldl (fun es a => (u, a) :: es) acc') =
              xs.reverse.map (fun a => (u, a)) ++ acc' := by
          intro xs
          induction xs with
          | nil => intro _; simp
          | cons x xs ihx =>
            intro acc'
            simp only [List.foldl_cons, ihx, List.reverse_cons, List.map_append,
              List.map_singleton, List.append_assoc, List.singleton_append]
        rw [hRev, List.reverse_append, List.map_reverse, List.reverse_reverse]
      rw [hPush, List.append_assoc, List.flatMap_cons]
  exact hFold (List.finRange H.vertexCount) []

/-- Exact equality between `(supplied (S.ramQuotient d)).reverse` and the
counting-sorted emitted arcs of owner `d`. -/
theorem supplied_reverse_ramQuotient_eq {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    ((supplied (S.ramQuotient d)).reverse).map (fun e => (e.1.val, (arcHead e.2).val)) =
      (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).map
        (fun ea => (ea.srcLocal, ea.headLocal)) := by
  rw [foldCons_supplied (S.ramQuotient d)]
  unfold countingSortedArcs
  rw [List.map_flatMap, List.map_flatMap]
  congr 1
  funext u
  simp only [List.map_map, Function.comp_def]
  have hHeadEq : ∀ a : QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount,
      arcHead a = a.head := fun a => by cases a; rfl
  simp only [hHeadEq]
  change ((S.ramQuotient d).outArcs u).map (fun a => (u.val, a.head.val)) =
    ((S.emittedArcs d).filter (fun ea => ea.srcLocal == u.val)).map (fun ea => (ea.srcLocal, ea.headLocal))
  have hOut : (S.ramQuotient d).outArcs u =
      (S.emittedArcs d).filterMap (fun ea =>
        if ea.srcLocal == u.val then
          if hHead : ea.headLocal < 1 + (S.childSlice d).length then
            if hEnt : ea.tailEntry < dense.length then
              let uD := S.denseOfEntry ⟨ea.tailEntry, hEnt⟩
              some (⟨⟨ea.headLocal, hHead⟩, dense[uD.val]'uD.isLt⟩ :
                QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount)
            else none
          else none
        else none) := by
    simp [LabelledQuotient.outArcs, StaticTreeSlice.ramQuotient]
  rw [hOut]
  have hBnd : ∀ ea ∈ S.emittedArcs d,
      ea.headLocal < 1 + (S.childSlice d).length ∧ ea.tailEntry < dense.length := fun ea hea =>
    ⟨(S.emittedArc_bounds d hea).2.2.1, (S.emittedArc_bounds d hea).2.2.2⟩
  suffices ∀ l : List (EmittedArc dense.length),
      (∀ ea ∈ l, ea.headLocal < 1 + (S.childSlice d).length ∧ ea.tailEntry < dense.length) →
      (l.filterMap (fun ea =>
        if ea.srcLocal == u.val then
          if hHead : ea.headLocal < 1 + (S.childSlice d).length then
            if hEnt : ea.tailEntry < dense.length then
              let uD := S.denseOfEntry ⟨ea.tailEntry, hEnt⟩
              some (⟨⟨ea.headLocal, hHead⟩, dense[uD.val]'uD.isLt⟩ :
                QuotientArc (S.ramQuotient d).origVertexCount (S.ramQuotient d).vertexCount)
            else none
          else none
        else none)).map (fun a => (u.val, a.head.val)) =
      (l.filter (fun ea => ea.srcLocal == u.val)).map (fun ea => (ea.srcLocal, ea.headLocal)) from
    this (S.emittedArcs d) hBnd
  intro l
  induction l with
  | nil => intro _; rfl
  | cons ea xs ih =>
    intro hxs
    have hea := hxs ea List.mem_cons_self
    have hxs' := ih (fun x hx => hxs x (List.mem_cons_of_mem ea hx))
    by_cases hsrc : (ea.srcLocal == u.val) = true
    · have hsrcEq : ea.srcLocal = u.val := beq_iff_eq.mp hsrc
      simp only [List.filterMap_cons, List.filter_cons, hsrc, ↓reduceIte, hea.1, hea.2,
        ↓reduceDIte, List.map_cons, hxs']
      rw [hsrcEq]
    · simp only [List.filterMap_cons, List.filter_cons, hsrc, Bool.false_eq_true, ↓reduceIte, hxs']

theorem ramQuotient_arcCount_eq {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    (S.ramQuotient d).arcCount = (S.emittedArcs d).length := by
  have hLen := congrArg List.length (supplied_reverse_ramQuotient_eq S d)
  rw [List.length_map, List.length_reverse, PaperB.ForestIncomingRaw.length_supplied,
    PaperB.ForestPreparedBuild.arcTotal_eq_arcCount, List.length_map,
    countingSortedArcs_length _ (fun ea hea => (S.emittedArc_bounds d hea).2.1)] at hLen
  exact hLen

/-- Helper: construct `RawQuotientInput` for `S.ramQuotient d` from word memory agreeing
with `countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)` inside `subInput`. -/
theorem rawQuotientInput_of_countingSorted {bits subInCap subWorkCap : Nat}
    {hsi : subInCap ≤ 2 ^ bits} {hsw : subWorkCap ≤ 2 ^ bits}
    {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (subInput : Input (RamForestProgram.layout bits subInCap subWorkCap hsi hsw))
    (hCap : rawInputCap (S.ramQuotient d).arcCount ≤ subInCap)
    (h0 : (subInput.words[0]?).map Fin.val = some (S.ramQuotient d).vertexCount)
    (h1 : (subInput.words[1]?).map Fin.val = some (S.ramQuotient d).arcCount)
    (h2 : (subInput.words[2]?).map Fin.val = some (S.ramQuotient d).root.val)
    (hArcs : ∀ (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(by
        rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp)
      (subInput.words[3 + p]?).map Fin.val = some ea.srcLocal ∧
      (subInput.words[3 + (S.emittedArcs d).length + p]?).map Fin.val = some ea.headLocal) :
    RawQuotientInput subInput (S.ramQuotient d) := by
  have hSup := supplied_reverse_ramQuotient_eq S d
  have hArcEq : (S.ramQuotient d).arcCount = (S.emittedArcs d).length := ramQuotient_arcCount_eq S d
  refine
    { cap_ge := hCap
      hdr_n := h0
      hdr_m := h1
      hdr_root := h2
      sources := fun e => ?_
      heads := fun e => ?_ }
  · have hp : e.val < (S.emittedArcs d).length := hArcEq ▸ e.isLt
    have hSrc := (hArcs e.val hp).1
    have hMapEq : ((supplied (S.ramQuotient d)).reverse.map (fun x => (x.1.val, (arcHead x.2).val)))[e.val]? =
        ((countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).map
          (fun ea => (ea.srcLocal, ea.headLocal)))[e.val]? := by
      rw [hSup]
    have hLenSup : e.val < (supplied (S.ramQuotient d)).reverse.length := by
      rw [List.length_reverse, PaperB.ForestIncomingRaw.length_supplied,
        PaperB.ForestPreparedBuild.arcTotal_eq_arcCount]
      exact e.isLt
    have hLenSort : e.val < (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).length := by
      rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp
    rw [List.getElem?_map, List.getElem?_map, getElem?_pos _ e.val hLenSup,
      getElem?_pos _ e.val hLenSort, Option.map_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hMapEq
    change (subInput.words[3 + e.val]?).map Fin.val = some (rawOccurrence (S.ramQuotient d) e).1.val
    have hRawEq : (rawOccurrence (S.ramQuotient d) e).1.val =
        ((countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[e.val]'hLenSort).srcLocal :=
      hMapEq.1
    rw [hRawEq]
    exact hSrc
  · have hp : e.val < (S.emittedArcs d).length := hArcEq ▸ e.isLt
    have hHead := (hArcs e.val hp).2
    have hMapEq : ((supplied (S.ramQuotient d)).reverse.map (fun x => (x.1.val, (arcHead x.2).val)))[e.val]? =
        ((countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).map
          (fun ea => (ea.srcLocal, ea.headLocal)))[e.val]? := by
      rw [hSup]
    have hLenSup : e.val < (supplied (S.ramQuotient d)).reverse.length := by
      rw [List.length_reverse, PaperB.ForestIncomingRaw.length_supplied,
        PaperB.ForestPreparedBuild.arcTotal_eq_arcCount]
      exact e.isLt
    have hLenSort : e.val < (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d)).length := by
      rw [countingSortedArcs_length _ (fun x hx => (S.emittedArc_bounds d hx).2.1)]; exact hp
    rw [List.getElem?_map, List.getElem?_map, getElem?_pos _ e.val hLenSup,
      getElem?_pos _ e.val hLenSort, Option.map_some, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at hMapEq
    change (subInput.words[3 + (S.ramQuotient d).arcCount + e.val]?).map Fin.val =
      some (rawHead (S.ramQuotient d) e).val
    have hRawEq : (rawHead (S.ramQuotient d) e).val =
        ((countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[e.val]'hLenSort).headLocal :=
      hMapEq.2
    rw [hRawEq]
    exact (congrArg (fun k => (subInput.words[3 + k + e.val]?).map Fin.val) hArcEq).trans hHead

end CountingSortModel

section ProgramCode

open PaperB.RamProgram (Instr)

abbrev r0 : Fin 16 := rZero
abbrev r1 : Fin 16 := rOne
abbrev r2 : Fin 16 := rN
abbrev r3 : Fin 16 := rM
abbrev r4 : Fin 16 := rRoot

def w32 {bits : Nat} (h32 : 32 ≤ 2 ^ bits) (k : Nat) (hk : k < 32 := by decide) : Word bits :=
  ⟨k, Nat.lt_of_lt_of_le hk h32⟩

def offInit : Nat := 0
def offHdr : Nat := 48
def offPrep : Nat := 49
def offZeroDeg : Nat := 72
def offCountDeg : Nat := 84
def offPrefix : Nat := 109
def offScatter : Nat := 127
def offWB : Nat := 187
def offBranch : Nat := 235
def offSmall : Nat := 238
def offLarge : Nat := 260
def offRaw : Nat := 283
def offPost (subLen : Nat) : Nat := 283 + 4 * subLen
def offMax (subLen : Nat) : Nat := 307 + 4 * subLen
def offCopy (subLen : Nat) : Nat := 339 + 4 * subLen
def offRec (subLen : Nat) : Nat := 353 + 4 * subLen
def offHalt (subLen : Nat) : Nat := 395 + 4 * subLen

private def loopInitCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.mov r9 r0,
    .mov r10 r0,
    .storeData r0 r8,
    .add r12 r3 r3,
    .imm r13 (w32 h32 3),
    .add r12 r12 r13,
    .add r11 r8 r12,
    .storeData r1 r11,
    .add r12 r2 r2,
    .add r12 r12 r12,
    .add r12 r12 r12,
    .add r12 r12 r12,
    .add r12 r12 r12,
    .add r11 r11 r12,
    .add r13 r3 r3,
    .add r14 r13 r13,
    .add r14 r14 r13,
    .add r14 r14 r3,
    .add r11 r11 r14,
    .imm r13 (w32 h32 17),
    .add r11 r11 r13,
    .imm r13 (w32 h32 2),
    .storeData r13 r11,
    .imm r12 (w32 h32 16),
    .add r12 r11 r12,
    .imm r13 (w32 h32 11),
    .add r14 r11 r13,
    .storeData r14 r12,
    .add r12 r12 r2,
    .imm r13 (w32 h32 12),
    .add r14 r11 r13,
    .storeData r14 r12,
    .add r12 r12 r2,
    .add r12 r12 r1,
    .imm r13 (w32 h32 13),
    .add r14 r11 r13,
    .storeData r14 r12,
    .add r12 r12 r3,
    .imm r13 (w32 h32 14),
    .add r14 r11 r13,
    .storeData r14 r12,
    .add r13 r2 r2,
    .add r14 r13 r13,
    .add r13 r13 r14,
    .add r12 r12 r13,
    .imm r13 (w32 h32 15),
    .add r14 r11 r13,
    .storeData r14 r12]

private def loopHdrCode (bits subLen : Nat) : Array (Instr bits 16) :=
  #[.branchLt r9 r5 (offHdr + 1) (offHalt subLen)]

private def prepOwnerCode (bits : Nat) : Array (Instr bits 16) :=
  #[.add r11 r5 r5,
    .add r12 r11 r11,
    .add r11 r11 r12,
    .add r11 r11 r5,
    .add r11 r6 r11,
    .add r11 r11 r9,
    .loadData r12 r11,
    .add r11 r11 r1,
    .loadData r13 r11,
    .sub r13 r13 r12,
    .add r11 r13 r1,
    .storeData r8 r11,
    .add r12 r2 r2,
    .add r12 r7 r12,
    .add r12 r12 r9,
    .loadData r13 r12,
    .add r12 r12 r1,
    .loadData r14 r12,
    .sub r14 r14 r13,
    .add r12 r8 r1,
    .storeData r12 r14,
    .add r12 r12 r1,
    .storeData r12 r0]

private def zeroDegCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.loadData r11 r8,
    .imm r12 (w32 h32 2),
    .loadData r15 r12,
    .imm r12 (w32 h32 11),
    .add r12 r15 r12,
    .loadData r15 r12,
    .mov r12 r0,
    .branchLt r12 r11 (offZeroDeg + 8) (offZeroDeg + 12),
    .add r13 r15 r12,
    .storeData r13 r0,
    .add r12 r12 r1,
    .goto (offZeroDeg + 7)]

private def countDegCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r12 (w32 h32 2),
    .loadData r15 r12,
    .imm r12 (w32 h32 11),
    .add r12 r15 r12,
    .loadData r15 r12,
    .add r11 r2 r2,
    .add r11 r11 r2,
    .add r11 r7 r11,
    .add r11 r11 r1,
    .add r12 r2 r2,
    .add r12 r7 r12,
    .add r12 r12 r9,
    .loadData r13 r12,
    .add r12 r12 r1,
    .loadData r14 r12,
    .add r13 r11 r13,
    .add r14 r11 r14,
    .branchLt r13 r14 (offCountDeg + 18) (offCountDeg + 25),
    .loadData r12 r13,
    .add r12 r15 r12,
    .loadData r11 r12,
    .add r11 r11 r1,
    .storeData r12 r11,
    .add r13 r13 r1,
    .goto (offCountDeg + 17)]

private def prefixCursorCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.loadData r11 r8,
    .imm r12 (w32 h32 2),
    .loadData r13 r12,
    .imm r12 (w32 h32 11),
    .add r12 r13 r12,
    .loadData r14 r12,
    .imm r12 (w32 h32 12),
    .add r12 r13 r12,
    .loadData r15 r12,
    .add r11 r14 r11,
    .mov r13 r0,
    .branchLt r14 r11 (offPrefix + 12) (offPrefix + 18),
    .storeData r15 r13,
    .loadData r12 r14,
    .add r13 r13 r12,
    .add r14 r14 r1,
    .add r15 r15 r1,
    .goto (offPrefix + 11)]

private def scatterSortCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.add r12 r2 r2,
    .add r12 r7 r12,
    .add r12 r12 r9,
    .loadData r13 r12,
    .add r12 r2 r2,
    .add r12 r7 r12,
    .add r12 r12 r9,
    .add r12 r12 r1,
    .loadData r14 r12,
    .branchLt r13 r14 (offScatter + 10) (offScatter + 60),
    .add r11 r2 r2,
    .add r11 r11 r2,
    .add r11 r7 r11,
    .add r11 r11 r1,
    .add r11 r11 r13,
    .loadData r11 r11,
    .imm r15 (w32 h32 2),
    .loadData r12 r15,
    .imm r15 (w32 h32 12),
    .add r12 r12 r15,
    .loadData r12 r12,
    .add r12 r12 r11,
    .loadData r14 r12,
    .add r15 r14 r1,
    .storeData r12 r15,
    .imm r12 (w32 h32 3),
    .add r12 r8 r12,
    .add r12 r12 r14,
    .storeData r12 r11,
    .add r12 r2 r2,
    .add r12 r12 r2,
    .add r12 r12 r3,
    .add r12 r7 r12,
    .add r12 r12 r1,
    .add r12 r12 r13,
    .loadData r11 r12,
    .add r15 r8 r1,
    .loadData r12 r15,
    .imm r15 (w32 h32 3),
    .add r15 r8 r15,
    .add r15 r15 r12,
    .add r15 r15 r14,
    .storeData r15 r11,
    .add r12 r2 r2,
    .add r12 r12 r2,
    .add r12 r12 r3,
    .add r12 r12 r3,
    .add r12 r7 r12,
    .add r12 r12 r1,
    .add r12 r12 r13,
    .loadData r11 r12,
    .imm r15 (w32 h32 2),
    .loadData r12 r15,
    .imm r15 (w32 h32 13),
    .add r12 r12 r15,
    .loadData r12 r12,
    .add r12 r12 r14,
    .storeData r12 r11,
    .add r13 r13 r1,
    .goto (offScatter + 4)]

private def writeBackCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.mov r13 r0,
    .add r12 r8 r1,
    .loadData r14 r12,
    .branchLt r13 r14 (offWB + 4) (offWB + 48),
    .add r12 r2 r2,
    .add r12 r7 r12,
    .add r12 r12 r9,
    .loadData r15 r12,
    .add r15 r15 r13,
    .imm r11 (w32 h32 3),
    .add r11 r8 r11,
    .add r11 r11 r13,
    .loadData r11 r11,
    .add r12 r2 r2,
    .add r12 r12 r2,
    .add r12 r7 r12,
    .add r12 r12 r1,
    .add r12 r12 r15,
    .storeData r12 r11,
    .imm r11 (w32 h32 3),
    .add r11 r8 r11,
    .add r11 r11 r14,
    .add r11 r11 r13,
    .loadData r11 r11,
    .add r12 r2 r2,
    .add r12 r12 r2,
    .add r12 r12 r3,
    .add r12 r7 r12,
    .add r12 r12 r1,
    .add r12 r12 r15,
    .storeData r12 r11,
    .imm r12 (w32 h32 2),
    .loadData r11 r12,
    .imm r12 (w32 h32 13),
    .add r11 r11 r12,
    .loadData r11 r11,
    .add r11 r11 r13,
    .loadData r11 r11,
    .add r12 r2 r2,
    .add r12 r12 r2,
    .add r12 r12 r3,
    .add r12 r12 r3,
    .add r12 r7 r12,
    .add r12 r12 r1,
    .add r12 r12 r15,
    .storeData r12 r11,
    .add r13 r13 r1,
    .goto (offWB + 1)]

private def branchOwnerCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.loadData r11 r8,
    .imm r12 (w32 h32 3),
    .branchLt r11 r12 offSmall offLarge]

private def smallBranchCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r12 (w32 h32 2),
    .loadData r11 r12,
    .imm r12 (w32 h32 14),
    .add r11 r11 r12,
    .loadData r11 r11,
    .add r12 r9 r9,
    .add r13 r12 r12,
    .add r12 r12 r13,
    .add r11 r11 r12,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r11 r11 r1,
    .storeData r11 r0,
    .add r9 r9 r1,
    .goto offHdr]

private def saveRegsCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w32 h32 2),
    .loadData r12 r11,
    .storeData r12 r0,
    .add r12 r12 r1,
    .storeData r12 r1,
    .add r12 r12 r1,
    .storeData r12 r2,
    .add r12 r12 r1,
    .storeData r12 r3,
    .add r12 r12 r1,
    .storeData r12 r4,
    .add r12 r12 r1,
    .storeData r12 r5,
    .add r12 r12 r1,
    .storeData r12 r6,
    .add r12 r12 r1,
    .storeData r12 r7,
    .add r12 r12 r1,
    .storeData r12 r8,
    .add r12 r12 r1,
    .storeData r12 r9,
    .add r12 r12 r1,
    .storeData r12 r10]

private def restoreRegsCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r11 (w32 h32 2),
    .loadData r12 r11,
    .imm r13 (w32 h32 1),
    .loadData r0 r12,
    .add r12 r12 r13,
    .loadData r1 r12,
    .add r12 r12 r13,
    .loadData r2 r12,
    .add r12 r12 r13,
    .loadData r3 r12,
    .add r12 r12 r13,
    .loadData r4 r12,
    .add r12 r12 r13,
    .loadData r5 r12,
    .add r12 r12 r13,
    .loadData r6 r12,
    .add r12 r12 r13,
    .loadData r7 r12,
    .add r12 r12 r13,
    .loadData r8 r12,
    .add r12 r12 r13,
    .loadData r9 r12,
    .add r12 r12 r13,
    .loadData r10 r12]

private def maxSlotAndWordCountCode {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    Array (Instr bits 16) :=
  let mBase := offMax subLen
  #[.loadData r11 r1,
    .loadData r12 r11,
    .add r13 r12 r12,
    .add r13 r11 r13,
    .add r13 r13 r1,
    .add r14 r13 r12,
    .mov r15 r0,
    .branchLt r13 r14 (mBase + 8) (mBase + 13),
    .loadData r11 r13,
    .branchLt r15 r11 (mBase + 10) (mBase + 11),
    .mov r15 r11,
    .add r13 r13 r1,
    .goto (mBase + 7),
    .add r15 r15 r1,
    .loadData r11 r1,
    .loadData r12 r11,
    .loadData r13 r8,
    .add r14 r12 r12,
    .add r14 r14 r12,
    .add r14 r14 r1,
    .add r14 r14 r13,
    .add r14 r14 r1,
    .add r14 r14 r13,
    .add r14 r14 r1,
    .add r14 r14 r13,
    .add r14 r14 r15,
    .add r14 r14 r15,
    .imm r11 (w32 h32 2),
    .loadData r12 r11,
    .storeData r12 r15,
    .add r12 r12 r1,
    .storeData r12 r14]

private def arenaCopyCode {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    Array (Instr bits 16) :=
  let cBase := offCopy subLen
  #[.imm r11 (w32 h32 2),
    .loadData r12 r11,
    .imm r13 (w32 h32 15),
    .add r12 r12 r13,
    .loadData r12 r12,
    .add r12 r12 r10,
    .loadData r11 r1,
    .add r15 r11 r14,
    .branchLt r11 r15 (cBase + 9) (cBase + 14),
    .loadData r13 r11,
    .storeData r12 r13,
    .add r11 r11 r1,
    .add r12 r12 r1,
    .goto (cBase + 8)]

private def recordPtrsCode {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  #[.imm r12 (w32 h32 2),
    .loadData r15 r12,
    .imm r12 (w32 h32 14),
    .add r12 r15 r12,
    .loadData r14 r12,
    .add r12 r9 r9,
    .add r13 r12 r12,
    .add r12 r12 r13,
    .add r14 r14 r12,
    .imm r12 (w32 h32 15),
    .add r12 r15 r12,
    .loadData r11 r12,
    .add r11 r11 r10,
    .storeData r14 r11,
    .add r14 r14 r1,
    .loadData r12 r1,
    .loadData r12 r12,
    .add r13 r12 r12,
    .add r13 r13 r12,
    .add r13 r13 r1,
    .add r11 r11 r13,
    .storeData r14 r11,
    .add r14 r14 r1,
    .loadData r12 r8,
    .add r13 r12 r1,
    .add r11 r11 r13,
    .storeData r14 r11,
    .add r14 r14 r1,
    .add r11 r11 r13,
    .storeData r14 r11,
    .add r14 r14 r1,
    .add r11 r11 r12,
    .storeData r14 r11,
    .add r14 r14 r1,
    .loadData r13 r15,
    .add r11 r11 r13,
    .storeData r14 r11,
    .add r15 r15 r1,
    .loadData r12 r15,
    .add r10 r10 r12,
    .add r9 r9 r1,
    .goto offHdr]

private def loopPrefixCode {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    Array (Instr bits 16) :=
  loopInitCode h32 ++ (loopHdrCode bits subLen ++ (prepOwnerCode bits ++ (zeroDegCode h32 ++
    (countDegCode h32 ++ (prefixCursorCode h32 ++ (scatterSortCode h32 ++ (writeBackCode h32 ++
    (branchOwnerCode h32 ++ (smallBranchCode h32 ++ saveRegsCode h32)))))))))

private def loopSuffixCode {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    Array (Instr bits 16) :=
  restoreRegsCode h32 ++ (maxSlotAndWordCountCode subLen h32 ++
    (arenaCopyCode subLen h32 ++ (recordPtrsCode h32 ++ #[.halt])))

private theorem h8Of32 {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : 8 ≤ 2 ^ bits :=
  Nat.le_trans (by decide) h32

private def liftedRawSlice {bits : Nat} (subCode : Array (Instr bits 15))
    (h32 : 32 ≤ 2 ^ bits) : Array (Instr bits 16) :=
  let lifted := liftCode (w32 h32 inPtrAddr) (w32 h32 dataPtrAddr) subCode
  (lifted.extract 0 (4 * subCode.size)).map (relocateInstr offRaw)

/-- Generic family-forest loop parameterized by an arbitrary 15-register worker body `subCode`. -/
def familyForestLoopCode {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  loopPrefixCode subCode.size h32 ++ liftedRawSlice subCode h32 ++ loopSuffixCode subCode.size h32

/-- Complete 16-register fixed word-RAM program for the EX5.1 family-forest loop. -/
def familyForestLoopProgram {bits inputCap workCap subInCap subWorkCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (hsi : subInCap ≤ 2 ^ bits) (hsw : subWorkCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  familyForestLoopCode
    (largeBuildProgram (bits := bits) (inputCap := subInCap) (workCap := subWorkCap)
      hsi hsw (h8Of32 h32))
    h32

private theorem loopPrefixCode_size {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    (loopPrefixCode subLen h32).size = offRaw := by
  have s0 : (loopInitCode h32).size = 48 := by simp [loopInitCode]
  have s1 : (loopHdrCode bits subLen).size = 1 := by simp [loopHdrCode]
  have s2 : (prepOwnerCode bits).size = 23 := by simp [prepOwnerCode]
  have s3 : (zeroDegCode h32).size = 12 := by simp [zeroDegCode]
  have s4 : (countDegCode h32).size = 25 := by simp [countDegCode]
  have s5 : (prefixCursorCode h32).size = 18 := by simp [prefixCursorCode]
  have s6 : (scatterSortCode h32).size = 60 := by simp [scatterSortCode]
  have s7 : (writeBackCode h32).size = 48 := by simp [writeBackCode]
  have s8 : (branchOwnerCode h32).size = 3 := by simp [branchOwnerCode]
  have s9 : (smallBranchCode h32).size = 22 := by simp [smallBranchCode]
  have s10 : (saveRegsCode h32).size = 23 := by simp [saveRegsCode]
  unfold loopPrefixCode offRaw
  simp only [Array.size_append, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10]

private theorem loopSuffixCode_size {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    (loopSuffixCode subLen h32).size = 113 := by
  have s0 : (restoreRegsCode h32).size = 24 := by simp [restoreRegsCode]
  have s1 : (maxSlotAndWordCountCode subLen h32).size = 32 := by simp [maxSlotAndWordCountCode]
  have s2 : (arenaCopyCode subLen h32).size = 14 := by simp [arenaCopyCode]
  have s3 : (recordPtrsCode h32).size = 42 := by simp [recordPtrsCode]
  unfold loopSuffixCode
  simp only [Array.size_append, s0, s1, s2, s3, List.size_toArray, List.length_singleton]

private theorem liftedRawSlice_size {bits : Nat} (subCode : Array (Instr bits 15))
    (h32 : 32 ≤ 2 ^ bits) :
    (liftedRawSlice subCode h32).size = 4 * subCode.size := by
  unfold liftedRawSlice
  rw [Array.size_map, Array.size_extract, liftCode_size]
  omega

theorem familyForestLoopCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32).size = 396 + 4 * subCode.size := by
  unfold familyForestLoopCode
  rw [Array.size_append, Array.size_append, loopPrefixCode_size, liftedRawSlice_size,
    loopSuffixCode_size]
  unfold offRaw
  omega

private theorem code_get_prefix {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {k : Nat} (hk : k < offRaw) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[k]? =
      (loopPrefixCode subCode.size h32)[k]? := by
  unfold familyForestLoopCode
  have h1 : k < (loopPrefixCode subCode.size h32 ++ liftedRawSlice subCode h32).size := by
    rw [Array.size_append, loopPrefixCode_size]; omega
  rw [Array.getElem?_append_left h1, Array.getElem?_append_left (by rw [loopPrefixCode_size]; exact hk)]

private theorem code_get_suffix {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {k : Nat} (_hk : k < 113) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offPost subCode.size + k]? =
      (loopSuffixCode subCode.size h32)[k]? := by
  unfold familyForestLoopCode
  have hPreSz : (loopPrefixCode subCode.size h32 ++ liftedRawSlice subCode h32).size =
      offPost subCode.size := by
    rw [Array.size_append, loopPrefixCode_size, liftedRawSlice_size]
    rfl
  rw [Array.getElem?_append_right (by rw [hPreSz]; omega), hPreSz, Nat.add_sub_cancel_left]

theorem liftedRaw_bodyRelocated {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits) :
    BodyRelocated (bits := bits) (bigL := layout16 bits inputCap workCap hi hw) rfl
      (w32 h32 inPtrAddr) (w32 h32 dataPtrAddr) subCode
      (familyForestLoopCode (hi := hi) (hw := hw) subCode h32) offRaw := by
  intro i hiLt op hop
  have h1 : offRaw + i < (loopPrefixCode subCode.size h32 ++ liftedRawSlice subCode h32).size := by
    rw [Array.size_append, loopPrefixCode_size, liftedRawSlice_size]; omega
  unfold familyForestLoopCode
  rw [Array.getElem?_append_left h1, Array.getElem?_append_right (by rw [loopPrefixCode_size]; omega),
    loopPrefixCode_size, Nat.add_sub_cancel_left]
  unfold liftedRawSlice
  have hCond : i < min (4 * subCode.size)
      (liftCode (w32 h32 inPtrAddr) (w32 h32 dataPtrAddr) subCode).size - 0 := by
    rw [liftCode_size]; omega
  rw [Array.getElem?_map, Array.getElem?_extract, Nat.zero_add, ite_eq_left hCond, hop]
  rfl

private theorem blocks_head {α : Type _} {a b : Array α} {sz i : Nat}
    (ha : a.size = sz) (hi : i < sz) : (a ++ b)[i]? = a[i]? :=
  Array.getElem?_append_left (by omega)

private theorem blocks_tail {α : Type _} {a b : Array α} {sz k : Nat}
    (ha : a.size = sz) (hk : sz ≤ k) : (a ++ b)[k]? = b[k - sz]? := by
  rw [Array.getElem?_append_right (by omega), ha]

private theorem loopInitCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (loopInitCode h32).size = 48 := by simp [loopInitCode]
private theorem loopHdrCode_size (bits subLen : Nat) :
    (loopHdrCode bits subLen).size = 1 := by simp [loopHdrCode]
private theorem prepOwnerCode_size (bits : Nat) :
    (prepOwnerCode bits).size = 23 := by simp [prepOwnerCode]
private theorem zeroDegCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (zeroDegCode h32).size = 12 := by simp [zeroDegCode]
private theorem countDegCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (countDegCode h32).size = 25 := by simp [countDegCode]
private theorem prefixCursorCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (prefixCursorCode h32).size = 18 := by simp [prefixCursorCode]
private theorem scatterSortCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (scatterSortCode h32).size = 60 := by simp [scatterSortCode]
private theorem writeBackCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (writeBackCode h32).size = 48 := by simp [writeBackCode]
private theorem branchOwnerCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (branchOwnerCode h32).size = 3 := by simp [branchOwnerCode]
private theorem smallBranchCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (smallBranchCode h32).size = 22 := by simp [smallBranchCode]
private theorem saveRegsCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (saveRegsCode h32).size = 23 := by simp [saveRegsCode]
private theorem restoreRegsCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (restoreRegsCode h32).size = 24 := by simp [restoreRegsCode]
private theorem maxSlotCode_size {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    (maxSlotAndWordCountCode subLen h32).size = 32 := by simp [maxSlotAndWordCountCode]
private theorem arenaCopyCode_size {bits : Nat} (subLen : Nat) (h32 : 32 ≤ 2 ^ bits) :
    (arenaCopyCode subLen h32).size = 14 := by simp [arenaCopyCode]
private theorem recordPtrsCode_size {bits : Nat} (h32 : 32 ≤ 2 ^ bits) :
    (recordPtrsCode h32).size = 42 := by simp [recordPtrsCode]

theorem at_init {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 48) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offInit + i]? =
      (loopInitCode h32)[i]? := by
  have hi' : offInit + i < offRaw := by unfold offInit offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offInit
  rw [Nat.zero_add]
  exact blocks_head (loopInitCode_size h32) hiLt

theorem at_hdr {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offHdr]? =
      (loopHdrCode bits subCode.size)[0]? := by
  have hi' : offHdr < offRaw := by unfold offHdr offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offHdr
  rw [blocks_tail (loopInitCode_size h32) (by decide)]
  exact blocks_head (loopHdrCode_size bits subCode.size) (by decide)

theorem at_prep {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 23) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offPrep + i]? =
      (prepOwnerCode bits)[i]? := by
  have hi' : offPrep + i < offRaw := by unfold offPrep offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offPrep
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega)]
  have hSub : (49 + i - 48) - 1 = i := by omega
  rw [hSub]
  exact blocks_head (prepOwnerCode_size bits) hiLt

theorem at_zeroDeg {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 12) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offZeroDeg + i]? =
      (zeroDegCode h32)[i]? := by
  have hi' : offZeroDeg + i < offRaw := by unfold offZeroDeg offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offZeroDeg
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega)]
  have hSub : ((72 + i - 48) - 1) - 23 = i := by omega
  rw [hSub]
  exact blocks_head (zeroDegCode_size h32) hiLt

theorem at_countDeg {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 25) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offCountDeg + i]? =
      (countDegCode h32)[i]? := by
  have hi' : offCountDeg + i < offRaw := by unfold offCountDeg offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offCountDeg
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega)]
  have hSub : (((84 + i - 48) - 1) - 23) - 12 = i := by omega
  rw [hSub]
  exact blocks_head (countDegCode_size h32) hiLt

theorem at_prefix {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 18) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offPrefix + i]? =
      (prefixCursorCode h32)[i]? := by
  have hi' : offPrefix + i < offRaw := by unfold offPrefix offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offPrefix
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega),
      blocks_tail (countDegCode_size h32) (by omega)]
  have hSub : ((((109 + i - 48) - 1) - 23) - 12) - 25 = i := by omega
  rw [hSub]
  exact blocks_head (prefixCursorCode_size h32) hiLt

theorem at_scatter {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 60) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offScatter + i]? =
      (scatterSortCode h32)[i]? := by
  have hi' : offScatter + i < offRaw := by unfold offScatter offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offScatter
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega),
      blocks_tail (countDegCode_size h32) (by omega),
      blocks_tail (prefixCursorCode_size h32) (by omega)]
  have hSub : (((((127 + i - 48) - 1) - 23) - 12) - 25) - 18 = i := by omega
  rw [hSub]
  exact blocks_head (scatterSortCode_size h32) hiLt

theorem at_wb {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 48) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offWB + i]? =
      (writeBackCode h32)[i]? := by
  have hi' : offWB + i < offRaw := by unfold offWB offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offWB
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega),
      blocks_tail (countDegCode_size h32) (by omega),
      blocks_tail (prefixCursorCode_size h32) (by omega),
      blocks_tail (scatterSortCode_size h32) (by omega)]
  have hSub : ((((((187 + i - 48) - 1) - 23) - 12) - 25) - 18) - 60 = i := by omega
  rw [hSub]
  exact blocks_head (writeBackCode_size h32) hiLt

theorem at_branch {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 3) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offBranch + i]? =
      (branchOwnerCode h32)[i]? := by
  have hi' : offBranch + i < offRaw := by unfold offBranch offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offBranch
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega),
      blocks_tail (countDegCode_size h32) (by omega),
      blocks_tail (prefixCursorCode_size h32) (by omega),
      blocks_tail (scatterSortCode_size h32) (by omega),
      blocks_tail (writeBackCode_size h32) (by omega)]
  have hSub : (((((((235 + i - 48) - 1) - 23) - 12) - 25) - 18) - 60) - 48 = i := by omega
  rw [hSub]
  exact blocks_head (branchOwnerCode_size h32) hiLt

theorem at_small {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 22) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offSmall + i]? =
      (smallBranchCode h32)[i]? := by
  have hi' : offSmall + i < offRaw := by unfold offSmall offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offSmall
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega),
      blocks_tail (countDegCode_size h32) (by omega),
      blocks_tail (prefixCursorCode_size h32) (by omega),
      blocks_tail (scatterSortCode_size h32) (by omega),
      blocks_tail (writeBackCode_size h32) (by omega),
      blocks_tail (branchOwnerCode_size h32) (by omega)]
  have hSub : ((((((((238 + i - 48) - 1) - 23) - 12) - 25) - 18) - 60) - 48) - 3 = i := by omega
  rw [hSub]
  exact blocks_head (smallBranchCode_size h32) hiLt

theorem at_save {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 23) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offLarge + i]? =
      (saveRegsCode h32)[i]? := by
  have hi' : offLarge + i < offRaw := by unfold offLarge offRaw; omega
  rw [code_get_prefix subCode h32 hi']
  unfold loopPrefixCode offLarge
  rw [blocks_tail (loopInitCode_size h32) (by omega),
      blocks_tail (loopHdrCode_size bits subCode.size) (by omega),
      blocks_tail (prepOwnerCode_size bits) (by omega),
      blocks_tail (zeroDegCode_size h32) (by omega),
      blocks_tail (countDegCode_size h32) (by omega),
      blocks_tail (prefixCursorCode_size h32) (by omega),
      blocks_tail (scatterSortCode_size h32) (by omega),
      blocks_tail (writeBackCode_size h32) (by omega),
      blocks_tail (branchOwnerCode_size h32) (by omega),
      blocks_tail (smallBranchCode_size h32) (by omega)]
  have hSub : (((((((((260 + i - 48) - 1) - 23) - 12) - 25) - 18) - 60) - 48) - 3) - 22 = i := by omega
  rw [hSub]

theorem at_restore {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 24) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offPost subCode.size + i]? =
      (restoreRegsCode h32)[i]? := by
  rw [code_get_suffix subCode h32 (by omega)]
  unfold loopSuffixCode
  exact blocks_head (restoreRegsCode_size h32) hiLt

theorem at_max {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 32) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offMax subCode.size + i]? =
      (maxSlotAndWordCountCode subCode.size h32)[i]? := by
  have hEq : offMax subCode.size + i = offPost subCode.size + (24 + i) := by
    unfold offMax offPost; omega
  rw [hEq, code_get_suffix subCode h32 (by omega)]
  unfold loopSuffixCode
  rw [blocks_tail (restoreRegsCode_size h32) (by omega)]
  have hSub : 24 + i - 24 = i := by omega
  rw [hSub]
  exact blocks_head (maxSlotCode_size subCode.size h32) hiLt

theorem at_copy {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 14) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offCopy subCode.size + i]? =
      (arenaCopyCode subCode.size h32)[i]? := by
  have hEq : offCopy subCode.size + i = offPost subCode.size + (56 + i) := by
    unfold offCopy offPost; omega
  rw [hEq, code_get_suffix subCode h32 (by omega)]
  unfold loopSuffixCode
  rw [blocks_tail (restoreRegsCode_size h32) (by omega),
      blocks_tail (maxSlotCode_size subCode.size h32) (by omega)]
  have hSub : (56 + i - 24) - 32 = i := by omega
  rw [hSub]
  exact blocks_head (arenaCopyCode_size subCode.size h32) hiLt

theorem at_rec {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits)
    {i : Nat} (hiLt : i < 42) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offRec subCode.size + i]? =
      (recordPtrsCode h32)[i]? := by
  have hEq : offRec subCode.size + i = offPost subCode.size + (70 + i) := by
    unfold offRec offPost; omega
  rw [hEq, code_get_suffix subCode h32 (by omega)]
  unfold loopSuffixCode
  rw [blocks_tail (restoreRegsCode_size h32) (by omega),
      blocks_tail (maxSlotCode_size subCode.size h32) (by omega),
      blocks_tail (arenaCopyCode_size subCode.size h32) (by omega)]
  have hSub : ((70 + i - 24) - 32) - 14 = i := by omega
  rw [hSub]
  exact blocks_head (recordPtrsCode_size h32) hiLt

theorem at_halt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[offHalt subCode.size]? = some .halt := by
  have hEq : offHalt subCode.size = offPost subCode.size + 112 := by
    unfold offHalt offPost; omega
  rw [hEq, code_get_suffix subCode h32 (by omega)]
  unfold loopSuffixCode
  rw [blocks_tail (restoreRegsCode_size h32) (by omega),
      blocks_tail (maxSlotCode_size subCode.size h32) (by omega),
      blocks_tail (arenaCopyCode_size subCode.size h32) (by omega),
      blocks_tail (recordPtrsCode_size h32) (by omega)]
  rfl

theorem familyForestLoopCode_last_halt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (subCode : Array (Instr bits 15)) (h32 : 32 ≤ 2 ^ bits) :
    (familyForestLoopCode (hi := hi) (hw := hw) subCode h32)[
      (familyForestLoopCode (hi := hi) (hw := hw) subCode h32).size - 1]? = some .halt := by
  have hEq : (familyForestLoopCode (hi := hi) (hw := hw) subCode h32).size - 1 =
      offHalt subCode.size := by
    rw [familyForestLoopCode_size]
    unfold offHalt
    omega
  rw [hEq]
  exact at_halt subCode h32

theorem familyForestLoopProgram_last_halt {bits inputCap workCap subInCap subWorkCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (hsi : subInCap ≤ 2 ^ bits) (hsw : subWorkCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    (familyForestLoopProgram (hi := hi) (hw := hw) hsi hsw h32)[
      (familyForestLoopProgram (hi := hi) (hw := hw) hsi hsw h32).size - 1]? = some .halt :=
  familyForestLoopCode_last_halt _ h32

end ProgramCode

section SimulationHelpers

open PaperB.WordOps (add_no_wrap)

theorem steps_one {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    {s t : State (layout16 bits inputCap workCap hi hw)}
    (h : step code input s = some (.next t)) :
    Steps code input 1 s t :=
  Steps.cons h (Steps.zero t)

private theorem steps_trans_add {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    {s u t : State (layout16 bits inputCap workCap hi hw)} {k₁ k₂ : Nat}
    (h₁ : Steps code input k₁ s u) (h₂ : Steps code input k₂ u t) :
    Steps code input (k₁ + k₂) s t :=
  h₁.append h₂

theorem loop_steps_budget {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    {α : Type} (inv : α → State (layout16 bits inputCap workCap hi hw) → Prop)
    (meas : α → Nat) (budget : α → Nat)
    (post : α → State (layout16 bits inputCap workCap hi hw) → Prop)
    (stepCase : ∀ a s, inv a s →
      (∃ t k, k ≤ budget a ∧ Steps code input k s t ∧ post a t) ∨
      (∃ a' s' k, meas a' < meas a ∧ k + budget a' ≤ budget a ∧ Steps code input k s s' ∧ inv a' s')) :
    ∀ bound a s, meas a ≤ bound → inv a s →
      ∃ aEnd t k, k ≤ budget a ∧ Steps code input k s t ∧ post aEnd t := by
  intro bound
  induction bound with
  | zero =>
    intro a s hm ha
    rcases stepCase a s ha with ⟨t, k, hk, hst, hpost⟩ | ⟨a', _, _, hlt, _⟩
    · exact ⟨a, t, k, hk, hst, hpost⟩
    · omega
  | succ b ih =>
    intro a s hm ha
    rcases stepCase a s ha with ⟨t, k, hk, hst, hpost⟩ | ⟨a', s', k, hlt, hbud, hst, ha'⟩
    · exact ⟨a, t, k, hk, hst, hpost⟩
    · obtain ⟨aEnd, t, k', hk', hst', hpost'⟩ := ih a' s' (by omega) ha'
      exact ⟨aEnd, t, k + k', by omega, hst.append hst', hpost'⟩

theorem mem_set_same {bits : Nat} (a : Array (Word bits)) {i addr : Nat}
    (hEq : i = addr) (hi : i < a.size) (v : Word bits) :
    (a.set i v hi)[addr]? = some v := by
  subst hEq
  rw [Array.getElem?_set_self]

theorem mem_set_ne {bits : Nat} (a : Array (Word bits)) {i j : Nat}
    (hi : i < a.size) (hne : j ≠ i) (v : Word bits) :
    (a.set i v hi)[j]? = a[j]? :=
  Array.getElem?_set_ne hi hne.symm

theorem mem_word_of_map {bits : Nat} {mem : Array (Word bits)} {addr val : Nat}
    (h : (mem[addr]?).map Fin.val = some val) (hLt : val < 2 ^ bits) :
    mem[addr]? = some ⟨val, hLt⟩ := by
  cases hm : mem[addr]? with
  | none => simp [hm] at h
  | some w =>
    rw [hm, Option.map_some, Option.some.injEq] at h
    exact congrArg some (Fin.ext h)

private theorem word_of_val {bits : Nat} {w : Word bits} {v : Nat}
    (hv : w.val = v) (hvLt : v < 2 ^ bits) : w = ⟨v, hvLt⟩ :=
  Fin.ext hv

theorem step16_branchLt_false {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (code : Program (layout16 bits inputCap workCap hi hw))
    (input : Input (layout16 bits inputCap workCap hi hw))
    {s : State (layout16 bits inputCap workCap hi hw)} {k yesPC noPC : Nat}
    {x y : Fin 16}
    (hpc : s.pc = k) (hAt : code[k]? = some (.branchLt x y yesPC noPC))
    (hNo : noPC < code.size) (hle : (reg s y).val ≤ (reg s x).val) :
    let t : State (layout16 bits inputCap workCap hi hw) :=
      { regs := s.regs, data := s.data, pc := noPC, regs_size := s.regs_size, data_size := s.data_size }
    step code input s = some (.next t) := by
  have hbr := PaperB.RamDagReach.branchLt_false hle
  have hs := step_branchLt_at (code := code) (input := input) (s := s)
    (by rw [hpc]; exact hAt) (by rw [hbr]; exact hNo)
  rw [hbr] at hs
  exact hs

theorem ownerVertexCount_le_Q {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length) :
    1 + (S.childSlice d).length ≤ dense.length := by
  have hNd := S.childSlice_nodup d
  have hNo : d ∉ S.childSlice d := by
    intro hm
    have := ((S.mem_childSlice_iff d d).mp hm).2
    exact S.domParent_ne_self d (Nat.pos_of_ne_zero ((S.mem_childSlice_iff d d).mp hm).1) this
  have hSub : ∀ x ∈ (d :: S.childSlice d), x ∈ List.finRange dense.length := fun x _ =>
    List.mem_finRange x
  have hNdCons : (d :: S.childSlice d).Nodup := List.nodup_cons.mpr ⟨hNo, hNd⟩
  have hLe := hNdCons.length_le_of_subset hSub
  simp only [List.length_cons, List.length_finRange] at hLe
  omega

private theorem qStartFn_mono' {bits : Nat} {origData : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice origData treeBase g r dense) {i j : Nat}
    (hi : i ≤ j) (hj : j ≤ dense.length) :
    qStartFn S i ≤ qStartFn S j := by
  suffices ∀ rem, i + rem ≤ dense.length → qStartFn S i ≤ qStartFn S (i + rem) by
    simpa only [Nat.add_sub_cancel' hi] using this (j - i) (by omega)
  intro rem
  induction rem with
  | zero => intro _; exact Nat.le_refl _
  | succ k ih =>
    intro hle
    have h1 := ih (by omega)
    rw [← Nat.add_assoc, qStartFn_succ S (by omega)]
    omega

end SimulationHelpers

end PaperB.RamFamilyForestLoop
