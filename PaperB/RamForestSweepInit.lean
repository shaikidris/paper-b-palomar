module

public import PaperB.RamForestSweepBase

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.Sweep

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.DepthSeek
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.ForestHead (Vertex TestSpec)
open PaperB.ForestDictionary (Rows packedDictionary packedDictionary_spec dictionary dictionary_spec)
open PaperB.ForestSlimIndex
open PaperB.PairLookup (Key)
open PaperB.RetainedProperLoss (WordColumns packWordColumns BackWords packBackWords encodeBackPair)
open PaperB.EX24.FinalDFS (packedInput nodeCount nodeCount_eq_next packedInput_parent packedInput_root)
open _root_.EX24 (Config Grounded)
open _root_.EX24.PreStep (climb Embedding)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedPairCode orderedConfig orderedRows)
open PaperB.ForestHead (preparedKey)
open PaperB.ForestDictionary (packedDictionary_eq)
open _root_.EX24 (initial initial_grounded)
open _root_.EX24.PreStep (initialUp initial_embedding boundedJumpParent)
open PaperB.Machine

section SweepInitPhase

private def sweepInitP0a {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .imm rZero ⟨0, by omega⟩,
    .imm rOne ⟨1, by omega⟩,
    .imm rTmp ⟨0, by omega⟩,
    .loadInput rVal rTmp,
    .storeData rTmp rVal,
    .imm rTmp ⟨1, by omega⟩,
    .loadInput rRem rTmp,
    .imm rTmp ⟨2, by omega⟩,
    .loadInput rPtr rTmp,
    .imm rTmp ⟨1, by omega⟩,
    .storeData rTmp rPtr,
    .imm rTmp ⟨2, by omega⟩,
    .storeData rTmp rOne,
    .add rStack rVal rOne,
    .add rClk rStack rRem,
    .add rTmp rClk rClk,
    .add rClk rTmp rTmp,
    .add rClk rClk rTmp,
    .add rClk rClk rOne,
    .add rClk rClk rVal,
    .add rClk rClk rVal ]

private theorem sweepInitP0a_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (sweepInitP0a h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def p0bPart1 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  sweepInitStoreScratch h8 slOrder rClk ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slRanks rClk) ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slRowStart rClk) ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slRowEnd rClk) ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slPredBuf rClk) ++
  ([.add rClk rClk rRem, .add rClk rClk rVal, .add rClk rClk rVal, .add rClk rClk rVal,
    .add rClk rClk rVal] ++ sweepInitStoreScratch h8 slDictBase rClk) ++
  ([.loadData rCnt rClk] ++ sweepInitStoreScratch h8 slDictCnt rCnt) ++
  ([.add rTin rClk rOne, .add rTin rTin rCnt] ++ sweepInitStoreScratch h8 slDictSnd rTin) ++
  ([.add rTin rTin rCnt] ++ sweepInitStoreScratch h8 slDictSlots rTin) ++
  ([.add rClk rClk rOne, .add rTmp rVal rVal, .add rTmp rTmp rVal, .add rClk rClk rTmp] ++
    sweepInitStoreScratch h8 slJumpBase rClk)

private def p0bPart2 {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  ([.storeData rClk rZero, .add rTout rClk rOne, .storeData rTout rZero,
    .add rTout rTout rOne, .storeData rTout rZero,
    .add rTout rStack rStack, .add rTout rTout rStack, .add rClk rClk rTout] ++
    sweepInitStoreScratch h8 slBackFst rClk) ++
  ([.mov rTin rClk, .add rClk rClk rStack] ++ sweepInitStoreScratch h8 slBackSnd rClk) ++
  ([.mov rTout rClk, .add rClk rClk rStack] ++ sweepInitStoreScratch h8 slLabels rClk) ++
  ([.mov rOff rClk, .add rClk rClk rVal] ++ sweepInitStoreScratch h8 slParents rClk) ++
  ([.storeData rClk rZero, .add rClk rClk rStack] ++ sweepInitStoreScratch h8 slSource rClk) ++
  sweepInitStoreScratch h8 slIdx rZero ++
  [.mov rPtr rZero]

private def sweepInitP0b {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  p0bPart1 h8 ++ p0bPart2 h8

private theorem sweepInitP0b_eq_parts {bits : Nat} (h8 : 8 ≤ 2 ^ bits) :
    sweepInitP0b h8 = p0bPart1 h8 ++ p0bPart2 h8 := rfl


private theorem p0bPart1_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (p0bPart1 h8).all isNonHaltBool = true := by
  have hsc : ∀ sl src, (sweepInitStoreScratch (bits := bits) h8 sl src).all isNonHaltBool = true := by
    intro sl src
    rw [← all_nonHalt_eq_isNonHaltBool (hi := hi) (hw := hw)]
    exact sweepInitStoreScratch_nonHalt h8 sl src
  unfold p0bPart1
  repeat first
    | apply list_all_append_true
    | (apply list_all_cons_true; rfl)
    | exact List.all_nil
    | exact hsc _ _

private theorem p0bPart2_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (p0bPart2 h8).all isNonHaltBool = true := by
  have hsc : ∀ sl src, (sweepInitStoreScratch (bits := bits) h8 sl src).all isNonHaltBool = true := by
    intro sl src
    rw [← all_nonHalt_eq_isNonHaltBool (hi := hi) (hw := hw)]
    exact sweepInitStoreScratch_nonHalt h8 sl src
  unfold p0bPart2
  repeat first
    | apply list_all_append_true
    | (apply list_all_cons_true; rfl)
    | exact List.all_nil
    | exact hsc _ _

private theorem sweepInitP0b_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (sweepInitP0b h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  rw [all_nonHalt_eq_isNonHaltBool, sweepInitP0b]
  exact list_all_append_true (p0bPart1_nonHalt (hi := hi) (hw := hw) h8)
    (p0bPart2_nonHalt (hi := hi) (hw := hw) h8)

private def sweepInitLoop {bits : Nat} (l1 : Nat) : List (Instr bits 15) :=
  let zeroBack : List (Instr bits 15) :=
    [.branchLt rPtr rStack (l1 + 1) (l1 + 7),
     .add rTmp rTin rPtr,
     .storeData rTmp rZero,
     .add rTmp rTout rPtr,
     .storeData rTmp rZero,
     .add rPtr rPtr rOne,
     .goto l1]
  let l2 := l1 + 7
  let resetPtr : List (Instr bits 15) := [.mov rPtr rZero]
  let l3 := l2 + 1
  let zeroLabels : List (Instr bits 15) :=
    [.branchLt rPtr rVal (l3 + 1) (l3 + 5),
     .add rTmp rOff rPtr,
     .storeData rTmp rZero,
     .add rPtr rPtr rOne,
     .goto l3]
  zeroBack ++ resetPtr ++ zeroLabels

private theorem sweepInitLoop_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (l1 : Nat) :
    (sweepInitLoop (bits := bits) l1).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := rfl

private def sweepInitBody {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  let p0 := sweepInitP0a h8 ++ sweepInitP0b h8
  p0 ++ sweepInitLoop p0.length

private theorem sweepInitBody_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits) :
    (sweepInitBody h8).all (@nonHalt bits (layout bits inputCap workCap hi hw)) = true := by
  simp only [sweepInitBody, List.all_append, sweepInitP0a_nonHalt, sweepInitP0b_nonHalt,
    sweepInitLoop_nonHalt, Bool.and_true]

def sweepInitPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  mkPhase (hi := hi) (hw := hw) (sweepInitBody h8) (sweepInitBody_nonHalt h8)

end SweepInitPhase

section SweepInitExec

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.RamForestProgram.DepthSeek
open PaperB.ForestHead (Vertex preparedKey)
open PaperB.ForestDictionary (Rows packedDictionary packedDictionary_spec)
open _root_.EX24 (Config Grounded initial initial_grounded)
open _root_.EX24.PreStep (Embedding initialUp initial_embedding boundedJumpParent)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedPairCode orderedConfig)


private theorem dictSortOutput_fields_aux {bits : Nat} {H : LabelledQuotient}
    (cols : PaperB.RetainedProperLoss.Columns H)
    (d : Array PaperB.PairLookup.Key)
    (ser : Array (Word bits))
    (hRep : FlatPairDictionary.Represents ser cols)
    (hszSer : ser.size = FlatPairDictionary.packedSize cols)
    (hslots : cols.slots.size = cols.dict.size)
    (hzeros : ∀ i, i < cols.dict.size → (cols.slots[i]?).getD 0 = 0)
    (hDictEq : cols.dict = d)
    (base : Nat) (data : Array (Word bits))
    (hserAt : ∀ j (hj : j < ser.size),
      (data[base + j]?).map Fin.val = some (ser[j]'hj).val) :
    (data[base]?).map Fin.val = some d.size ∧
    (∀ i (hi' : i < d.size),
      (data[base + 1 + i]?).map Fin.val = some (d[i]'hi').1 ∧
      (data[base + 1 + d.size + i]?).map Fin.val = some (d[i]'hi').2 ∧
      (data[base + 1 + 2 * d.size + i]?).map Fin.val = some 0) := by
  have hsz : ser.size = 1 + 3 * d.size := by
    rw [hszSer]
    unfold FlatPairDictionary.packedSize FlatPairDictionary.slotBase FlatPairDictionary.secondBase
    rw [hslots, hDictEq]
    omega
  have arr_fst_eq : ∀ (a b : Array PaperB.PairLookup.Key) i (ha : i < a.size) (hb : i < b.size),
      a = b → (a[i]'ha).1 = (b[i]'hb).1 := fun a b i ha hb h => by subst b; rfl
  have arr_snd_eq : ∀ (a b : Array PaperB.PairLookup.Key) i (ha : i < a.size) (hb : i < b.size),
      a = b → (a[i]'ha).2 = (b[i]'hb).2 := fun a b i ha hb h => by subst b; rfl
  constructor
  · have h0 : 0 < ser.size := by rw [hsz]; omega
    rw [show base = base + 0 by omega, hserAt 0 h0]
    have hcnt : FlatPairDictionary.rowCount ser = (ser[0]'h0).val := by
      unfold FlatPairDictionary.rowCount
      rw [Array.getElem?_eq_getElem h0]
      rfl
    rw [← hcnt, hRep.rows, hDictEq]
  · intro i hi'
    have h1 : 1 + i < ser.size := by rw [hsz]; omega
    have h2 : 1 + d.size + i < ser.size := by rw [hsz]; omega
    have h3 : 1 + 2 * d.size + i < ser.size := by rw [hsz]; omega
    have hci : i < cols.dict.size := by rw [hDictEq]; exact hi'
    have hsi : i < cols.slots.size := by rw [hslots]; exact hci
    have hfirst := hRep.first_eq i (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hci) hci
    have hsec := hRep.second_eq i (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hci) hci
    have hsl := hRep.slot_eq i (by rw [hRep.slot_len]; exact hsi) hsi
    have hfval : (ser[1 + i]'h1).val = (d[i]'hi').1 := by
      have h' : ((FlatPairDictionary.firstSlice ser hRep.valid).get i
          (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hci)).val =
          (ser[1 + i]'h1).val :=
        slice_get_val_eq (FlatPairDictionary.firstSlice ser hRep.valid) i (1 + i)
          (by rw [FlatPairDictionary.firstSlice_len, hRep.rows]; exact hci) h1
          (by change (FlatPairDictionary.firstSlice ser hRep.valid).base.val + i = 1 + i; rfl)
      exact h'.symm.trans (hfirst.trans (arr_fst_eq cols.dict d i hci hi' hDictEq))
    have hsval : (ser[1 + d.size + i]'h2).val = (d[i]'hi').2 := by
      have h' : ((FlatPairDictionary.secondSlice ser hRep.valid).get i
          (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hci)).val =
          (ser[1 + d.size + i]'h2).val :=
        slice_get_val_eq (FlatPairDictionary.secondSlice ser hRep.valid) i (1 + d.size + i)
          (by rw [FlatPairDictionary.secondSlice_len, hRep.rows]; exact hci) h2
          (by rw [secondSlice_base hRep.valid, hRep.rows, hDictEq])
      exact h'.symm.trans (hsec.trans (arr_snd_eq cols.dict d i hci hi' hDictEq))
    have hlval : (ser[1 + 2 * d.size + i]'h3).val = 0 := by
      have h' : ((FlatPairDictionary.slotSlice ser hRep.valid).get i
          (by rw [hRep.slot_len]; exact hsi)).val =
          (ser[1 + 2 * d.size + i]'h3).val :=
        slice_get_val_eq (FlatPairDictionary.slotSlice ser hRep.valid) i (1 + 2 * d.size + i)
          (by rw [hRep.slot_len]; exact hsi) h3
          (by rw [slotSlice_base hRep.valid, hRep.rows, hDictEq])
      exact h'.symm.trans (hsl.trans (hzeros i hci))
    refine ⟨?_, ?_, ?_⟩
    · rw [show base + 1 + i = base + (1 + i) by omega, hserAt (1 + i) h1, hfval]
    · rw [show base + 1 + d.size + i = base + (1 + d.size + i) by omega, hserAt _ h2, hsval]
    · rw [show base + 1 + 2 * d.size + i = base + (1 + 2 * d.size + i) by omega, hserAt _ h3, hlval]

private theorem dictSortOutput_fields {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    {s : State (layout bits inputCap workCap hi hw)}
    {hBound : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ 2 ^ bits}
    (dso : DictSortOutput H s order size_order rank rows hBound)
    (dictRows : Rows H) (large : 3 ≤ H.vertexCount) :
    (s.data[dictBase H.vertexCount H.arcCount]?).map Fin.val =
      some (orderedConfig dictRows large).dict.size ∧
    (∀ i (hi' : i < (orderedConfig dictRows large).dict.size),
      (s.data[dictBase H.vertexCount H.arcCount + 1 + i]?).map Fin.val =
        some ((orderedConfig dictRows large).dict[i]'hi').1 ∧
      (s.data[dictBase H.vertexCount H.arcCount + 1 +
        (orderedConfig dictRows large).dict.size + i]?).map Fin.val =
        some ((orderedConfig dictRows large).dict[i]'hi').2 ∧
      (s.data[dictBase H.vertexCount H.arcCount + 1 +
        2 * (orderedConfig dictRows large).dict.size + i]?).map Fin.val = some 0) := by
  let cols := zeroDictColumns H rows
  let fits := zeroDictFits rows hBound
  exact dictSortOutput_fields_aux cols (orderedConfig dictRows large).dict
    (FlatPairDictionary.serialize cols fits)
    (FlatPairDictionary.serialize_represents cols fits)
    (FlatPairDictionary.serialize_size cols fits)
    (by simp [cols, zeroDictColumns])
    (fun i _ => by
      simp only [cols, zeroDictColumns, Array.getElem?_replicate]
      split <;> rfl)
    (by
      change packedDictionary rows orderedPairCode =
        PaperB.ForestDictionary.dictionary dictRows orderedPairCode
      exact packedDictionary_eq_dictionary H rows dictRows)
    (dictBase H.vertexCount H.arcCount) s.data
    (fun j hj => by rw [dso.dictAt ⟨j, hj⟩, Option.map_some])


private theorem zeroBack_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (l1 backFst backSnd n : Nat) (hBound : backSnd + (n + 1) ≤ workCap)
    (hDisj : backFst + (n + 1) ≤ backSnd) :
    ∀ rem ptr (s : State (layout bits inputCap workCap hi hw)),
      ptr + rem = n + 1 →
      s.pc = l1 →
      (reg s rPtr).val = ptr →
      (reg s rStack).val = n + 1 →
      (reg s rTin).val = backFst →
      (reg s rTout).val = backSnd →
      (reg s rZero).val = 0 →
      (reg s rOne).val = 1 →
      code[l1]? = some (.branchLt rPtr rStack (l1 + 1) (l1 + 7)) →
      code[l1 + 1]? = some (.add rTmp rTin rPtr) →
      code[l1 + 2]? = some (.storeData rTmp rZero) →
      code[l1 + 3]? = some (.add rTmp rTout rPtr) →
      code[l1 + 4]? = some (.storeData rTmp rZero) →
      code[l1 + 5]? = some (.add rPtr rPtr rOne) →
      code[l1 + 6]? = some (.goto l1) →
      l1 + 7 < code.size →
      ∃ t : State (layout bits inputCap workCap hi hw),
        Steps code input (7 * rem + 1) s t ∧
        t.pc = l1 + 7 ∧
        (∀ j, ptr ≤ j → j < n + 1 →
          (t.data[backFst + j]?).map Fin.val = some 0 ∧
          (t.data[backSnd + j]?).map Fin.val = some 0) ∧
        (∀ j, (∀ k, ptr ≤ k → k < n + 1 → j ≠ backFst + k ∧ j ≠ backSnd + k) →
          t.data[j]? = s.data[j]?) ∧
        (∀ r : Fin 15, r ≠ rPtr → r ≠ rTmp → reg t r = reg s r) := by
  intro rem
  induction rem with
  | zero =>
    intro ptr s hsum hpc hrptr hrstk hrtin hrtout hrzero hrone
      f0 _ _ _ _ _ _ hsz
    have heq : ptr = n + 1 := by omega
    obtain ⟨t, st, tpc, k0, dt⟩ :=
      step_branchLt_false (input := input) (by rw [hpc]; exact f0)
        (by rw [hrptr, hrstk, heq]; exact Nat.le_refl _) (by omega)
    refine ⟨t, .cons st (.zero _), tpc, ?_, ?_, fun r _ _ => k0 r⟩
    · intro j hj1 hj2; omega
    · intro j _; rw [dt]
  | succ r ih =>
    intro ptr s hsum hpc hrptr hrstk hrtin hrtout hrzero hrone
      f0 f1 f2 f3 f4 f5 f6 hsz
    have hlt : ptr < n + 1 := by omega
    obtain ⟨s1, st0, pc1, k1, d1⟩ :=
      step_branchLt_true (input := input) (by rw [hpc]; exact f0) (by rw [hrptr, hrstk]; exact hlt) (by omega)
    have hfitF : (reg s1 rTin).val + (reg s1 rPtr).val < workCap := by
      rw [k1 rTin, k1 rPtr, hrtin, hrptr]; omega
    obtain ⟨s2, st1, pc2, d2, k2⟩ :=
      storeAtOffset_steps (input := input) f1 f2 pc1 (by omega)
        (show rZero ≠ rTmp by decide) hfitF
    have hk2' : ∀ regn, regn ≠ rTmp → reg s2 regn = reg s regn :=
      fun regn hn => (k2 regn hn).trans (k1 regn)
    have hfitS : (reg s2 rTout).val + (reg s2 rPtr).val < workCap := by
      rw [hk2' rTout (by decide), hk2' rPtr (by decide), hrtout, hrptr]; omega
    obtain ⟨s3, st2, pc3, d3, k3⟩ :=
      storeAtOffset_steps (input := input) f3 f4 pc2 (by omega)
        (show rZero ≠ rTmp by decide) hfitS
    have hk3' : ∀ regn, regn ≠ rTmp → reg s3 regn = reg s regn :=
      fun regn hn => (k3 regn hn).trans (hk2' regn hn)
    obtain ⟨s4, st5, pc4, r4, k4, d4⟩ :=
      step_add15_at (input := input) (by rw [pc3]; exact f5) (by omega)
    let s5 : State (layout bits inputCap workCap hi hw) := { s4 with pc := l1 }
    have st6 : step code input s4 = some (.next s5) :=
      step_goto_at (input := input) (by rw [pc4, pc3]; exact f6) (by omega)
    have pc5 : s5.pc = l1 := rfl
    have k5 : ∀ regn, reg s5 regn = reg s4 regn := fun _ => rfl
    have d5 : s5.data = s4.data := rfl
    have hr4 : (reg s4 rPtr).val = ptr + 1 := by
      have hp := hk3' rPtr (by decide)
      have ho := hk3' rOne (by decide)
      rw [r4, PaperB.WordOps.add_no_wrap _ _ (by
        rw [hp, ho, hrptr, hrone]; exact Nat.lt_of_lt_of_le (by omega) hw), hp, ho, hrptr, hrone]
    have hk5' : ∀ regn, regn ≠ rPtr → regn ≠ rTmp → reg s5 regn = reg s regn := by
      intro regn hn1 hn2
      rw [k5 regn, k4 regn hn1, hk3' regn hn2]
    have h1 : Steps code input 7 s s5 :=
      .cons st0 (st1.append (st2.append (.cons st5 (.cons st6 (.zero _)))))
    obtain ⟨t, htail, tpc, hback, hfr, kt⟩ :=
      ih (ptr + 1) s5 (by omega) pc5 (by rw [k5 rPtr, hr4])
        (by rw [hk5' rStack (by decide) (by decide), hrstk])
        (by rw [hk5' rTin (by decide) (by decide), hrtin])
        (by rw [hk5' rTout (by decide) (by decide), hrtout])
        (by rw [hk5' rZero (by decide) (by decide), hrzero])
        (by rw [hk5' rOne (by decide) (by decide), hrone])
        f0 f1 f2 f3 f4 f5 f6 hsz
    have hstepTotal : Steps code input (7 * (r + 1) + 1) s t := by
      rw [show 7 * (r + 1) + 1 = 7 + (7 * r + 1) by omega]
      exact h1.append htail
    have ds5 : s5.data = ((s.data.set (backFst + ptr) (reg s rZero)
        (by rw [s.data_size]; change _ < workCap; omega)).set (backSnd + ptr) (reg s rZero)
        (by rw [Array.size_set, s.data_size]; change _ < workCap; omega)) := by
      rw [d5, d4, d3]
      exact array_set_congr
        (a := s2.data)
        (b := s.data.set (backFst + ptr) (reg s rZero)
          (by rw [s.data_size]; change _ < workCap; omega))
        (by rw [s2.data_size]; exact hfitS)
        (by rw [Array.size_set, s.data_size]; change _ < workCap; omega)
        (by
          rw [d2]
          exact array_set_congr (a := s1.data) (b := s.data)
            (by rw [s1.data_size]; exact hfitF)
            (by rw [s.data_size]; change _ < workCap; omega)
            d1 (by rw [k1 rTin, k1 rPtr, hrtin, hrptr]) (k1 rZero))
        (by rw [hk2' rTout (by decide), hk2' rPtr (by decide), hrtout, hrptr])
        (hk2' rZero (by decide))
    have ds5Same : ∀ j, j ≠ backFst + ptr → j ≠ backSnd + ptr → s5.data[j]? = s.data[j]? := by
      intro j hj1 hj2
      rw [ds5, array_set_getElem?_ne _ _ _ _ _ hj2, array_set_getElem?_ne _ _ _ _ _ hj1]
    have ds5F : (s5.data[backFst + ptr]?).map Fin.val = some 0 := by
      have hneFS : backFst + ptr ≠ backSnd + ptr := by omega
      rw [ds5, array_set_getElem?_ne _ _ _ _ _ hneFS, array_set_getElem?_same, Option.map_some, hrzero]
    have ds5S : (s5.data[backSnd + ptr]?).map Fin.val = some 0 := by
      rw [ds5, array_set_getElem?_same, Option.map_some, hrzero]
    refine ⟨t, hstepTotal, tpc, ?_, ?_, fun regn hn1 hn2 => (kt regn hn1 hn2).trans (hk5' regn hn1 hn2)⟩
    · intro j hj1 hj2
      by_cases hjp : j = ptr
      · subst j
        constructor
        · rw [hfr (backFst + ptr) (fun k hk1 hk2 => ⟨by omega, by omega⟩)]
          exact ds5F
        · rw [hfr (backSnd + ptr) (fun k hk1 hk2 => ⟨by omega, by omega⟩)]
          exact ds5S
      · exact hback j (by omega) hj2
    · intro j hj
      rw [hfr j (fun k hk1 hk2 => hj k (by omega) hk2)]
      exact ds5Same j (hj ptr (Nat.le_refl _) hlt).1 (hj ptr (Nat.le_refl _) hlt).2

private theorem zeroLabels_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (l3 labels n : Nat) (hBound : labels + n < workCap) :
    ∀ rem ptr (s : State (layout bits inputCap workCap hi hw)),
      ptr + rem = n →
      s.pc = l3 →
      (reg s rPtr).val = ptr →
      (reg s rVal).val = n →
      (reg s rOff).val = labels →
      (reg s rZero).val = 0 →
      (reg s rOne).val = 1 →
      code[l3]? = some (.branchLt rPtr rVal (l3 + 1) (l3 + 5)) →
      code[l3 + 1]? = some (.add rTmp rOff rPtr) →
      code[l3 + 2]? = some (.storeData rTmp rZero) →
      code[l3 + 3]? = some (.add rPtr rPtr rOne) →
      code[l3 + 4]? = some (.goto l3) →
      l3 + 5 < code.size →
      ∃ t : State (layout bits inputCap workCap hi hw),
        Steps code input (5 * rem + 1) s t ∧
        t.pc = l3 + 5 ∧
        (∀ j, ptr ≤ j → j < n → (t.data[labels + j]?).map Fin.val = some 0) ∧
        (∀ j, (∀ k, ptr ≤ k → k < n → j ≠ labels + k) → t.data[j]? = s.data[j]?) ∧
        (∀ r : Fin 15, r ≠ rPtr → r ≠ rTmp → reg t r = reg s r) := by
  intro rem
  induction rem with
  | zero =>
    intro ptr s hsum hpc hrptr hrval hroff hrzero hrone f0 _ _ _ _ hsz
    have heq : ptr = n := by omega
    obtain ⟨t, st, tpc, k0, dt⟩ :=
      step_branchLt_false (input := input) (by rw [hpc]; exact f0)
        (by rw [hrptr, hrval, heq]; exact Nat.le_refl _) (by omega)
    refine ⟨t, .cons st (.zero _), tpc, fun j hj1 hj2 => by omega, fun j _ => by rw [dt],
      fun r _ _ => k0 r⟩
  | succ r ih =>
    intro ptr s hsum hpc hrptr hrval hroff hrzero hrone f0 f1 f2 f3 f4 hsz
    have hlt : ptr < n := by omega
    obtain ⟨s1, st0, pc1, k1, d1⟩ :=
      step_branchLt_true (input := input) (by rw [hpc]; exact f0) (by rw [hrptr, hrval]; exact hlt) (by omega)
    have hfit : (reg s1 rOff).val + (reg s1 rPtr).val < workCap := by
      rw [k1 rOff, k1 rPtr, hroff, hrptr]; omega
    obtain ⟨s2, st1, pc2, d2, k2⟩ :=
      storeAtOffset_steps (input := input) f1 f2 pc1 (by omega)
        (show rZero ≠ rTmp by decide) hfit
    have hk2' : ∀ regn, regn ≠ rTmp → reg s2 regn = reg s regn :=
      fun regn hn => (k2 regn hn).trans (k1 regn)
    obtain ⟨s3, st3, pc3, r3, k3, d3⟩ :=
      step_add15_at (input := input) (by rw [pc2]; exact f3) (by omega)
    let s4 : State (layout bits inputCap workCap hi hw) := { s3 with pc := l3 }
    have st4 : step code input s3 = some (.next s4) :=
      step_goto_at (input := input) (by rw [pc3, pc2]; exact f4) (by omega)
    have pc4 : s4.pc = l3 := rfl
    have k4 : ∀ regn, reg s4 regn = reg s3 regn := fun _ => rfl
    have d4 : s4.data = s3.data := rfl
    have hr3 : (reg s3 rPtr).val = ptr + 1 := by
      have hp := hk2' rPtr (by decide)
      have ho := hk2' rOne (by decide)
      rw [r3, PaperB.WordOps.add_no_wrap _ _ (by
        rw [hp, ho, hrptr, hrone]; exact Nat.lt_of_lt_of_le (by omega) hw), hp, ho, hrptr, hrone]
    have hk4' : ∀ regn, regn ≠ rPtr → regn ≠ rTmp → reg s4 regn = reg s regn := by
      intro regn hn1 hn2
      rw [k4 regn, k3 regn hn1, hk2' regn hn2]
    have h1 : Steps code input 5 s s4 := .cons st0 (st1.append (.cons st3 (.cons st4 (.zero _))))
    obtain ⟨t, htail, tpc, hlab, hfr, kt⟩ :=
      ih (ptr + 1) s4 (by omega) pc4 (by rw [k4 rPtr, hr3])
        (by rw [hk4' rVal (by decide) (by decide), hrval])
        (by rw [hk4' rOff (by decide) (by decide), hroff])
        (by rw [hk4' rZero (by decide) (by decide), hrzero])
        (by rw [hk4' rOne (by decide) (by decide), hrone])
        f0 f1 f2 f3 f4 hsz
    have hstepTotal : Steps code input (5 * (r + 1) + 1) s t := by
      rw [show 5 * (r + 1) + 1 = 5 + (5 * r + 1) by omega]
      exact h1.append htail
    have ds4 : s4.data = s.data.set (labels + ptr) (reg s rZero)
        (by rw [s.data_size]; change _ < workCap; omega) := by
      rw [d4, d3, d2]
      exact array_set_congr (a := s1.data) (b := s.data)
        (by rw [s1.data_size]; exact hfit)
        (by rw [s.data_size]; change _ < workCap; omega)
        d1 (by rw [k1 rOff, k1 rPtr, hroff, hrptr]) (k1 rZero)
    refine ⟨t, hstepTotal, tpc, ?_, ?_, fun regn hn1 hn2 => (kt regn hn1 hn2).trans (hk4' regn hn1 hn2)⟩
    · intro j hj1 hj2
      by_cases hjp : j = ptr
      · subst j
        rw [hfr (labels + ptr) (fun k hk1 _ => by omega), ds4, array_set_getElem?_same,
            Option.map_some, hrzero]
      · exact hlab j (by omega) hj2
    · intro j hj
      rw [hfr j (fun k hk1 hk2 => hj k (by omega) hk2), ds4,
          array_set_getElem?_ne _ _ _ _ _ (hj ptr (Nat.le_refl _) hlt)]

private theorem add_storeScratch_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {entry : Nat} (dst rhs : Fin 15) (sl : Nat)
    (hd1 : dst ≠ rTmp) (hd2 : dst ≠ rhs) (hr1 : rhs ≠ dst)
    (hsl256 : sl < 256) (hslCap : sl < workCap)
    (hsumFit : (reg s dst).val + (reg s rhs).val < workCap)
    (hpc : s.pc = entry)
    (hpl : Placed code entry ([.add dst dst rhs] ++ sweepInitStoreScratch h8 sl dst))
    (hsz : entry + (1 + (sweepInitStoreScratch (bits := bits) h8 sl dst).length) < code.size)
    (hone : (reg s rOne).val = 1) (hoNe : rOne ≠ dst) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (1 + (sweepInitStoreScratch (bits := bits) h8 sl dst).length) s t ∧
      t.pc = entry + (1 + (sweepInitStoreScratch (bits := bits) h8 sl dst).length) ∧
      (reg t dst).val = (reg s dst).val + (reg s rhs).val ∧
      (t.data[sl]?).map Fin.val = some ((reg s dst).val + (reg s rhs).val) ∧
      (∀ j, j ≠ sl → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ dst → r ≠ rTmp → reg t r = reg s r) := by
  have _ := hd2; have _ := hr1
  have f0 : code[s.pc]? = some (.add dst dst rhs) := by
    rw [hpc]; exact hpl 0 _ rfl
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_add15_at (input := input) f0 (by omega)
  have hdv : (reg s1 dst).val = (reg s dst).val + (reg s rhs).val := by
    rw [r1, PaperB.WordOps.add_no_wrap _ _ (Nat.lt_of_lt_of_le hsumFit hw)]
  have hpl2 : Placed code (entry + 1) (sweepInitStoreScratch h8 sl dst) :=
    placed_append_right hpl
  obtain ⟨s2, st2, pc2, slVal, fr2, k2⟩ :=
    sweepInitStoreScratch_steps h8 sl dst hd1 hsl256 hslCap (by rw [pc1, hpc]) hpl2
      (by omega) (by rw [k1 rOne hoNe, hone])
  have hst : Steps code input (1 + (sweepInitStoreScratch (bits := bits) h8 sl dst).length) s s2 := by
    rw [Nat.add_comm 1 _]; exact .cons st0 st2
  refine ⟨s2, hst, by rw [pc2]; omega, ?_, ?_, ?_, ?_⟩
  · rw [k2 dst hd1, hdv]
  · rw [slVal, hdv]
  · intro j hj; rw [fr2 j hj, d1]
  · intro r hn1 hn2; rw [k2 r hn2, k1 r hn1]

private theorem mov_add_storeScratch_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    {s : State (layout bits inputCap workCap hi hw)}
    {entry : Nat} (sv rhs : Fin 15) (sl : Nat)
    (hsv1 : sv ≠ rTmp) (hsv2 : sv ≠ rClk) (hsv3 : sv ≠ rhs)
    (hr1 : rhs ≠ rClk) (ho1 : rOne ≠ sv) (ho2 : rOne ≠ rClk)
    (hsl256 : sl < 256) (hslCap : sl < workCap)
    (hsumFit : (reg s rClk).val + (reg s rhs).val < workCap)
    (hpc : s.pc = entry)
    (hpl : Placed code entry ([.mov sv rClk, .add rClk rClk rhs] ++ sweepInitStoreScratch h8 sl rClk))
    (hsz : entry + (2 + (sweepInitStoreScratch (bits := bits) h8 sl rClk).length) < code.size)
    (hone : (reg s rOne).val = 1) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (2 + (sweepInitStoreScratch (bits := bits) h8 sl rClk).length) s t ∧
      t.pc = entry + (2 + (sweepInitStoreScratch (bits := bits) h8 sl rClk).length) ∧
      (reg t sv).val = (reg s rClk).val ∧
      (reg t rClk).val = (reg s rClk).val + (reg s rhs).val ∧
      (t.data[sl]?).map Fin.val = some ((reg s rClk).val + (reg s rhs).val) ∧
      (∀ j, j ≠ sl → t.data[j]? = s.data[j]?) ∧
      (∀ r : Fin 15, r ≠ sv → r ≠ rClk → r ≠ rTmp → reg t r = reg s r) := by
  have f0 : code[s.pc]? = some (.mov sv rClk) := by rw [hpc]; exact hpl 0 _ rfl
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ := step_mov_at (input := input) f0 (by omega)
  have hrclk1 : reg s1 rClk = reg s rClk := k1 rClk hsv2.symm
  have hrrhs1 : reg s1 rhs = reg s rhs := k1 rhs hsv3.symm
  have hpl2 : Placed code (entry + 1) ([.add rClk rClk rhs] ++ sweepInitStoreScratch h8 sl rClk) := by
    have h' := hpl
    rw [show ([.mov sv rClk, .add rClk rClk rhs] ++ sweepInitStoreScratch h8 sl rClk) =
        [.mov sv rClk] ++ ([.add rClk rClk rhs] ++ sweepInitStoreScratch h8 sl rClk) by rfl] at h'
    exact placed_append_right h'
  obtain ⟨s2, st2, pc2, rc2, sl2, fr2, k2⟩ :=
    add_storeScratch_steps h8 rClk rhs sl (by decide) hr1.symm hr1 hsl256 hslCap
      (by rw [hrclk1, hrrhs1]; exact hsumFit) (by rw [pc1, hpc]) hpl2 (by omega)
      (by rw [k1 rOne ho1, hone]) ho2
  have hst : Steps code input (2 + (sweepInitStoreScratch (bits := bits) h8 sl rClk).length) s s2 := by
    rw [show 2 + (sweepInitStoreScratch (bits := bits) h8 sl rClk).length =
        (1 + (sweepInitStoreScratch (bits := bits) h8 sl rClk).length).succ by omega]
    exact .cons st0 st2
  refine ⟨s2, hst, by rw [pc2]; omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k2 sv hsv2 hsv1, r1]
  · rw [rc2, hrclk1, hrrhs1]
  · rw [sl2, hrclk1, hrrhs1]
  · intro j hj; rw [fr2 j hj, d1]
  · intro r hn1 hn2 hn3; rw [k2 r hn2 hn3, k1 r hn1]


private theorem sweepInitP0a_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (H : LabelledQuotient) (hRaw : RawQuotientInput input H)
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = 0) (hpl : Placed code 0 (sweepInitP0a h8))
    (hsz : 21 < code.size) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input 21 s t ∧
      t.pc = 21 ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rVal).val = H.vertexCount ∧ (reg t rRem).val = H.arcCount ∧
      (reg t rStack).val = H.vertexCount + 1 ∧
      (reg t rClk).val = orderBase H.vertexCount H.arcCount ∧
      (t.data[slN]?).map Fin.val = some H.vertexCount ∧
      (t.data[slRoot]?).map Fin.val = some H.root.val ∧
      (t.data[slNext]?).map Fin.val = some 1 ∧
      (∀ j, 3 ≤ j → t.data[j]? = s.data[j]?) := by
  have hWork : 32 * H.vertexCount + 7 * H.arcCount + 17 ≤ workCap := hCap
  obtain ⟨w0, hw0, hw0v⟩ := word_mem_eq_of_map_val hRaw.hdr_n
  obtain ⟨w1, hw1, hw1v⟩ := word_mem_eq_of_map_val hRaw.hdr_m
  obtain ⟨w2, hw2, hw2v⟩ := word_mem_eq_of_map_val hRaw.hdr_root
  obtain ⟨s1, st0, pc1, r1, k1, d1⟩ :=
    step_imm_at (input := input) (s := s) (placed_fetch hpl (i := 0) rfl (by rw [hpc])) (by rw [hpc]; omega)
  have hpc1 : s1.pc = 1 := by omega
  obtain ⟨s2, st1, pc2, r2, k2, d2⟩ :=
    step_imm_at (input := input) (s := s1) (placed_fetch hpl (i := 1) rfl hpc1) (by rw [hpc1]; omega)
  have hpc2 : s2.pc = 2 := by omega
  obtain ⟨s3, st2, pc3, r3, k3, d3⟩ :=
    step_imm_at (input := input) (s := s2) (placed_fetch hpl (i := 2) rfl hpc2) (by rw [hpc2]; omega)
  have hpc3 : s3.pc = 3 := by omega
  have hk3_0 : (reg s3 rZero).val = 0 := by
    rw [k3 _ (by decide), k2 _ (by decide), r1]
  have hk3_1 : (reg s3 rOne).val = 1 := by
    rw [k3 _ (by decide), r2]
  have hr3 : (reg s3 rTmp).val = 0 := by rw [r3]
  obtain ⟨s4, st3, pc4, r4, k4, d4⟩ :=
    step_loadInput_at (input := input) (s := s3) (placed_fetch hpl (i := 3) rfl hpc3) (by rw [hpc3]; omega) (by rw [hr3]; exact hw0)
  have hpc4 : s4.pc = 4 := by omega
  have hr4 : (reg s4 rVal).val = H.vertexCount := by rw [r4, hw0v]
  have hr4t : (reg s4 rTmp).val = 0 := by rw [k4 _ (by decide), hr3]
  obtain ⟨s5, st4, pc5, d5, k5⟩ :=
    step_storeData_at (input := input) (s := s4) (placed_fetch hpl (i := 4) rfl hpc4) (by rw [hpc4]; omega) (by rw [hr4t]; omega)
  have hpc5 : s5.pc = 5 := by omega
  obtain ⟨s6, st5, pc6, r6, k6, d6⟩ :=
    step_imm_at (input := input) (s := s5) (placed_fetch hpl (i := 5) rfl hpc5) (by rw [hpc5]; omega)
  have hpc6 : s6.pc = 6 := by omega
  have hr6t : (reg s6 rTmp).val = 1 := by rw [r6]
  obtain ⟨s7, st6, pc7, r7, k7, d7⟩ :=
    step_loadInput_at (input := input) (s := s6) (placed_fetch hpl (i := 6) rfl hpc6) (by rw [hpc6]; omega) (by rw [hr6t]; exact hw1)
  have hpc7 : s7.pc = 7 := by omega
  have hr7 : (reg s7 rRem).val = H.arcCount := by rw [r7, hw1v]
  obtain ⟨s8, st7, pc8, r8, k8, d8⟩ :=
    step_imm_at (input := input) (s := s7) (placed_fetch hpl (i := 7) rfl hpc7) (by rw [hpc7]; omega)
  have hpc8 : s8.pc = 8 := by omega
  have hr8t : (reg s8 rTmp).val = 2 := by rw [r8]
  obtain ⟨s9, st8, pc9, r9, k9, d9⟩ :=
    step_loadInput_at (input := input) (s := s8) (placed_fetch hpl (i := 8) rfl hpc8) (by rw [hpc8]; omega) (by rw [hr8t]; exact hw2)
  have hpc9 : s9.pc = 9 := by omega
  have hr9 : (reg s9 rPtr).val = H.root.val := by rw [r9, hw2v]
  obtain ⟨s10, st9, pc10, r10, k10, d10⟩ :=
    step_imm_at (input := input) (s := s9) (placed_fetch hpl (i := 9) rfl hpc9) (by rw [hpc9]; omega)
  have hpc10 : s10.pc = 10 := by omega
  have hr10t : (reg s10 rTmp).val = 1 := by rw [r10]
  obtain ⟨s11, st10, pc11, d11, k11⟩ :=
    step_storeData_at (input := input) (s := s10) (placed_fetch hpl (i := 10) rfl hpc10) (by rw [hpc10]; omega) (by rw [hr10t]; omega)
  have hpc11 : s11.pc = 11 := by omega
  obtain ⟨s12, st11, pc12, r12, k12, d12⟩ :=
    step_imm_at (input := input) (s := s11) (placed_fetch hpl (i := 11) rfl hpc11) (by rw [hpc11]; omega)
  have hpc12 : s12.pc = 12 := by omega
  have hr12t : (reg s12 rTmp).val = 2 := by rw [r12]
  obtain ⟨s13, st12, pc13, d13, k13⟩ :=
    step_storeData_at (input := input) (s := s12) (placed_fetch hpl (i := 12) rfl hpc12) (by rw [hpc12]; omega) (by rw [hr12t]; omega)
  have hpc13 : s13.pc = 13 := by omega
  have h13_zero : (reg s13 rZero).val = 0 := by
    rw [k13, k12 _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide),
        k7 _ (by decide), k6 _ (by decide), k5, k4 _ (by decide), hk3_0]
  have h13_one : (reg s13 rOne).val = 1 := by
    rw [k13, k12 _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide),
        k7 _ (by decide), k6 _ (by decide), k5, k4 _ (by decide), hk3_1]
  have h13_val : (reg s13 rVal).val = H.vertexCount := by
    rw [k13, k12 _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide),
        k7 _ (by decide), k6 _ (by decide), k5, hr4]
  have h13_rem : (reg s13 rRem).val = H.arcCount := by
    rw [k13, k12 _ (by decide), k11, k10 _ (by decide), k9 _ (by decide), k8 _ (by decide), hr7]
  obtain ⟨s14, st13, pc14, r14, k14, d14⟩ :=
    step_add15_at (input := input) (s := s13) (placed_fetch hpl (i := 13) rfl hpc13) (by rw [hpc13]; omega)
  have hpc14 : s14.pc = 14 := by omega
  have h14_stk : (reg s14 rStack).val = H.vertexCount + 1 := by
    rw [r14, PaperB.WordOps.add_no_wrap _ _ (by rw [h13_val, h13_one]; omega), h13_val, h13_one]
  obtain ⟨s15, st14, pc15, r15, k15, d15⟩ :=
    step_add15_at (input := input) (s := s14) (placed_fetch hpl (i := 14) rfl hpc14) (by rw [hpc14]; omega)
  have hpc15 : s15.pc = 15 := by omega
  have h15_clk : (reg s15 rClk).val = H.vertexCount + 1 + H.arcCount := by
    rw [r15, PaperB.WordOps.add_no_wrap _ _ (by
      rw [h14_stk, k14 rRem (by decide), h13_rem]; omega),
      h14_stk, k14 rRem (by decide), h13_rem]
  obtain ⟨s16, st15, pc16, r16, k16, d16⟩ :=
    step_add15_at (input := input) (s := s15) (placed_fetch hpl (i := 15) rfl hpc15) (by rw [hpc15]; omega)
  have hpc16 : s16.pc = 16 := by omega
  have h16_tmp : (reg s16 rTmp).val = 2 * (H.vertexCount + 1 + H.arcCount) := by
    rw [r16, PaperB.WordOps.add_no_wrap _ _ (by rw [h15_clk]; omega), h15_clk]; omega
  obtain ⟨s17, st16, pc17, r17, k17, d17⟩ :=
    step_add15_at (input := input) (s := s16) (placed_fetch hpl (i := 16) rfl hpc16) (by rw [hpc16]; omega)
  have hpc17 : s17.pc = 17 := by omega
  have h17_clk : (reg s17 rClk).val = 4 * (H.vertexCount + 1 + H.arcCount) := by
    rw [r17, PaperB.WordOps.add_no_wrap _ _ (by rw [h16_tmp]; omega), h16_tmp]; omega
  obtain ⟨s18, st17, pc18, r18, k18, d18⟩ :=
    step_add15_at (input := input) (s := s17) (placed_fetch hpl (i := 17) rfl hpc17) (by rw [hpc17]; omega)
  have hpc18 : s18.pc = 18 := by omega
  have h18_clk : (reg s18 rClk).val = 6 * (H.vertexCount + 1 + H.arcCount) := by
    have ht17 : (reg s17 rTmp).val = 2 * (H.vertexCount + 1 + H.arcCount) := by
      rw [k17 rTmp (by decide), h16_tmp]
    rw [r18, PaperB.WordOps.add_no_wrap _ _ (by rw [h17_clk, ht17]; omega), h17_clk, ht17]; omega
  obtain ⟨s19, st18, pc19, r19, k19, d19⟩ :=
    step_add15_at (input := input) (s := s18) (placed_fetch hpl (i := 18) rfl hpc18) (by rw [hpc18]; omega)
  have hpc19 : s19.pc = 19 := by omega
  have h19_one : (reg s18 rOne).val = 1 := by
    rw [k18 _ (by decide), k17 _ (by decide), k16 _ (by decide), k15 _ (by decide),
        k14 _ (by decide), h13_one]
  have h19_clk : (reg s19 rClk).val = 6 * (H.vertexCount + 1 + H.arcCount) + 1 := by
    rw [r19, PaperB.WordOps.add_no_wrap _ _ (by rw [h18_clk, h19_one]; omega), h18_clk, h19_one]
  obtain ⟨s20, st19, pc20, r20, k20, d20⟩ :=
    step_add15_at (input := input) (s := s19) (placed_fetch hpl (i := 19) rfl hpc19) (by rw [hpc19]; omega)
  have hpc20 : s20.pc = 20 := by omega
  have h19_val : (reg s19 rVal).val = H.vertexCount := by
    rw [k19 _ (by decide), k18 _ (by decide), k17 _ (by decide), k16 _ (by decide),
        k15 _ (by decide), k14 _ (by decide), h13_val]
  have h20_clk : (reg s20 rClk).val = 7 * H.vertexCount + 6 * H.arcCount + 7 := by
    rw [r20, PaperB.WordOps.add_no_wrap _ _ (by rw [h19_clk, h19_val]; omega), h19_clk, h19_val]; omega
  obtain ⟨s21, st20, pc21, r21, k21, d21⟩ :=
    step_add15_at (input := input) (s := s20) (placed_fetch hpl (i := 20) rfl hpc20) (by rw [hpc20]; omega)
  have h20_val : (reg s20 rVal).val = H.vertexCount := by rw [k20 _ (by decide), h19_val]
  have h21_clk : (reg s21 rClk).val = orderBase H.vertexCount H.arcCount := by
    rw [r21, PaperB.WordOps.add_no_wrap _ _ (by rw [h20_clk, h20_val]; omega), h20_clk, h20_val]
    simp only [orderBase, stampsBase, indegBase, csrArenaWords]; omega
  have hsteps : Steps code input 21 s s21 :=
    .cons st0 (.cons st1 (.cons st2 (.cons st3 (.cons st4 (.cons st5 (.cons st6 (.cons st7
      (.cons st8 (.cons st9 (.cons st10 (.cons st11 (.cons st12 (.cons st13 (.cons st14
        (.cons st15 (.cons st16 (.cons st17 (.cons st18 (.cons st19 (.cons st20 (.zero _)))))))))))))))))))))
  have hkeepTail : ∀ r, r ≠ rClk → r ≠ rStack → r ≠ rTmp → reg s21 r = reg s13 r := by
    intro r hn1 hn2 hn3
    rw [k21 r hn1, k20 r hn1, k19 r hn1, k18 r hn1, k17 r hn1, k16 r hn3, k15 r hn1, k14 r hn2]
  have hdt13 : s21.data = s13.data := by
    rw [d21, d20, d19, d18, d17, d16, d15, d14]
  have hdt5 : s13.data[0]? = s5.data[0]? := by
    rw [d13, array_set_getElem?_ne _ _ _ _ _ (by rw [hr12t]; omega), d12, d11,
        array_set_getElem?_ne _ _ _ _ _ (by rw [hr10t]; omega), d10, d9, d8, d7, d6]
  have hdt11 : s13.data[1]? = s11.data[1]? := by
    rw [d13, array_set_getElem?_ne _ _ _ _ _ (by rw [hr12t]; omega), d12, d11]
  have hdt11_root : (s11.data[1]?).map Fin.val = some H.root.val := by
    have hset : s11.data[(reg s10 rTmp).val]? = some (reg s10 rPtr) := by
      rw [d11]; exact Array.getElem?_set_self (by rw [s10.data_size, hr10t]; change 1 < workCap; omega)
    rw [hr10t] at hset
    rw [hset, Option.map_some, k10 rPtr (by decide), hr9]
  have hdt13_next : (s13.data[2]?).map Fin.val = some 1 := by
    have hset : s13.data[(reg s12 rTmp).val]? = some (reg s12 rOne) := by
      rw [d13]; exact Array.getElem?_set_self (by rw [s12.data_size, hr12t]; change 2 < workCap; omega)
    rw [hr12t] at hset
    rw [hset, Option.map_some, k12 rOne (by decide), k11, k10 _ (by decide), k9 _ (by decide),
        k8 _ (by decide), k7 _ (by decide), k6 _ (by decide), k5, k4 _ (by decide), hk3_1]
  have hdt5_n : (s5.data[0]?).map Fin.val = some H.vertexCount := by
    have hset : s5.data[(reg s4 rTmp).val]? = some (reg s4 rVal) := by
      rw [d5]; exact Array.getElem?_set_self (by rw [s4.data_size, hr4t]; change 0 < workCap; omega)
    rw [hr4t] at hset
    rw [hset, Option.map_some, hr4]
  refine ⟨s21, hsteps, by omega, ?_, ?_, ?_, ?_, ?_, h21_clk, ?_, ?_, ?_, ?_⟩
  · rw [hkeepTail rZero (by decide) (by decide) (by decide), h13_zero]
  · rw [hkeepTail rOne (by decide) (by decide) (by decide), h13_one]
  · rw [hkeepTail rVal (by decide) (by decide) (by decide), h13_val]
  · rw [hkeepTail rRem (by decide) (by decide) (by decide), h13_rem]
  · rw [k21 _ (by decide), k20 _ (by decide), k19 _ (by decide), k18 _ (by decide),
        k17 _ (by decide), k16 _ (by decide), k15 _ (by decide), h14_stk]
  · rw [hdt13, hdt5]; exact hdt5_n
  · rw [hdt13, hdt11]; exact hdt11_root
  · rw [hdt13]; exact hdt13_next
  · intro j hj
    rw [hdt13, d13, array_set_getElem?_ne _ _ _ _ _ (by rw [hr12t]; omega), d12, d11,
        array_set_getElem?_ne _ _ _ _ _ (by rw [hr10t]; omega), d10, d9, d8, d7, d6, d5,
        array_set_getElem?_ne _ _ _ _ _ (by rw [hr4t]; omega), d4, d3, d2, d1]

private def p0bPart1a {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  sweepInitStoreScratch h8 slOrder rClk ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slRanks rClk) ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slRowStart rClk) ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slRowEnd rClk) ++
  ([.add rClk rClk rVal] ++ sweepInitStoreScratch h8 slPredBuf rClk)

private def p0bPart1b {bits : Nat} (h8 : 8 ≤ 2 ^ bits) : List (Instr bits 15) :=
  ([.add rClk rClk rRem, .add rClk rClk rVal, .add rClk rClk rVal, .add rClk rClk rVal,
    .add rClk rClk rVal] ++ sweepInitStoreScratch h8 slDictBase rClk) ++
  ([.loadData rCnt rClk] ++ sweepInitStoreScratch h8 slDictCnt rCnt) ++
  ([.add rTin rClk rOne, .add rTin rTin rCnt] ++ sweepInitStoreScratch h8 slDictSnd rTin) ++
  ([.add rTin rTin rCnt] ++ sweepInitStoreScratch h8 slDictSlots rTin) ++
  ([.add rClk rClk rOne, .add rTmp rVal rVal, .add rTmp rTmp rVal, .add rClk rClk rTmp] ++
    sweepInitStoreScratch h8 slJumpBase rClk)

private theorem p0bPart1_eq_ab {bits : Nat} (h8 : 8 ≤ 2 ^ bits) :
    p0bPart1 h8 = p0bPart1a h8 ++ p0bPart1b h8 := by
  simp only [p0bPart1, p0bPart1a, p0bPart1b, List.append_assoc]

private theorem p0bPart1a_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m : Nat) (hWork : rawWorkCap n m ≤ workCap)
    {entry : Nat} (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry) (hpl : Placed code entry (p0bPart1a h8))
    (hsz : entry + (p0bPart1a h8).length < code.size)
    (hrZero : (reg s rZero).val = 0) (hrOne : (reg s rOne).val = 1)
    (hrVal : (reg s rVal).val = n) (hrRem : (reg s rRem).val = m)
    (hrStk : (reg s rStack).val = n + 1)
    (hrClk : (reg s rClk).val = orderBase n m) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (p0bPart1a h8).length s t ∧
      t.pc = entry + (p0bPart1a h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rVal).val = n ∧ (reg t rRem).val = m ∧ (reg t rStack).val = n + 1 ∧
      (reg t rClk).val = predBufBase n m ∧
      (t.data[slOrder]?).map Fin.val = some (orderBase n m) ∧
      (t.data[slRanks]?).map Fin.val = some (ranksBase n m) ∧
      (t.data[slRowStart]?).map Fin.val = some (rowStartBase n m) ∧
      (t.data[slRowEnd]?).map Fin.val = some (rowEndBase n m) ∧
      (t.data[slPredBuf]?).map Fin.val = some (predBufBase n m) ∧
      (∀ j, j < 12 ∨ 17 ≤ j → t.data[j]? = s.data[j]?) := by
  have hWork17 : 32 * n + 7 * m + 17 ≤ workCap := hWork
  have hOrderFit : orderBase n m + n < workCap := by
    simp only [orderBase, stampsBase, indegBase, csrArenaWords]; omega
  let l0 := sweepInitStoreScratch (bits := bits) h8 slOrder rClk
  let l1 := [.add rClk rClk rVal] ++ sweepInitStoreScratch (bits := bits) h8 slRanks rClk
  let l2 := [.add rClk rClk rVal] ++ sweepInitStoreScratch (bits := bits) h8 slRowStart rClk
  let l3 := [.add rClk rClk rVal] ++ sweepInitStoreScratch (bits := bits) h8 slRowEnd rClk
  let l4 := [.add rClk rClk rVal] ++ sweepInitStoreScratch (bits := bits) h8 slPredBuf rClk
  have hp : p0bPart1a h8 = l0 ++ l1 ++ l2 ++ l3 ++ l4 := rfl
  have hpl0123 : Placed code entry (l0 ++ l1 ++ l2 ++ l3) := placed_append_left hpl
  have hpl012 : Placed code entry (l0 ++ l1 ++ l2) := placed_append_left hpl0123
  have hpl01 : Placed code entry (l0 ++ l1) := placed_append_left hpl012
  have hpl0 : Placed code entry l0 := placed_append_left hpl01
  have hpl1 : Placed code (entry + l0.length) l1 := placed_append_right hpl01
  have hpl2 : Placed code (entry + (l0 ++ l1).length) l2 := placed_append_right hpl012
  have hpl3 : Placed code (entry + (l0 ++ l1 ++ l2).length) l3 := placed_append_right hpl0123
  have hpl4 : Placed code (entry + (l0 ++ l1 ++ l2 ++ l3).length) l4 := placed_append_right hpl
  have hszTotal : entry + (l0.length + l1.length + l2.length + l3.length + l4.length) < code.size := by
    simpa [hp, List.length_append, Nat.add_assoc] using hsz
  have hl0 : l0.length = (sweepInitStoreScratch (bits := bits) h8 slOrder rClk).length := rfl
  obtain ⟨s0, st0, pc0, dOrd, fr0, k0⟩ :=
    sweepInitStoreScratch_steps h8 slOrder rClk (by decide) (by decide)
      (scratch_lt_workCap17 hWork (by decide))
      hpc hpl0 (by rw [← hl0]; omega) hrOne
  have hl1 : l1.length = 1 + (sweepInitStoreScratch (bits := bits) h8 slRanks rClk).length := rfl
  obtain ⟨s1, st1, pc1, rc1, dRnk, fr1, k1⟩ :=
    add_storeScratch_steps h8 rClk rVal slRanks (by decide) (by decide) (by decide)
      (by decide) (scratch_lt_workCap17 hWork (by decide))
      (by rw [k0 rClk (by decide), k0 rVal (by decide), hrClk, hrVal]; exact hOrderFit)
      pc0 hpl1 (by rw [hl1] at hszTotal; omega) (by rw [k0 rOne (by decide), hrOne]) (by decide)
  have hrc1 : (reg s1 rClk).val = ranksBase n m :=
    (rc1.trans (by rw [k0 rClk (by decide), k0 rVal (by decide), hrClk, hrVal]; rfl))
  have hl2 : l2.length = 1 + (sweepInitStoreScratch (bits := bits) h8 slRowStart rClk).length := rfl
  have hrVal1 : (reg s1 rVal).val = n := by rw [k1 rVal (by decide) (by decide), k0 rVal (by decide), hrVal]
  have hrOne1 : (reg s1 rOne).val = 1 := by rw [k1 rOne (by decide) (by decide), k0 rOne (by decide), hrOne]
  obtain ⟨s2, st2, pc2, rc2, dRS, fr2, k2⟩ :=
    add_storeScratch_steps h8 rClk rVal slRowStart (by decide) (by decide) (by decide)
      (by decide) (scratch_lt_workCap17 hWork (by decide))
      (by rw [hrc1, hrVal1]; simp only [ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      (by rw [pc1, ← hl0, ← hl1]; simp only [List.length_append, Nat.add_assoc]) hpl2
      (by simp only [List.length_append]; rw [hl2] at hszTotal; omega)
      hrOne1 (by decide)
  have hrc2 : (reg s2 rClk).val = rowStartBase n m :=
    (rc2.trans (by rw [hrc1, hrVal1]; rfl))
  have hl3 : l3.length = 1 + (sweepInitStoreScratch (bits := bits) h8 slRowEnd rClk).length := rfl
  have hrVal2 : (reg s2 rVal).val = n := by rw [k2 rVal (by decide) (by decide), hrVal1]
  have hrOne2 : (reg s2 rOne).val = 1 := by rw [k2 rOne (by decide) (by decide), hrOne1]
  obtain ⟨s3, st3, pc3, rc3, dRE, fr3, k3⟩ :=
    add_storeScratch_steps h8 rClk rVal slRowEnd (by decide) (by decide) (by decide)
      (by decide) (scratch_lt_workCap17 hWork (by decide))
      (by rw [hrc2, hrVal2]; simp only [rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      (by rw [pc2, ← hl2]; simp only [List.length_append, Nat.add_assoc]) hpl3
      (by simp only [List.length_append]; rw [hl3] at hszTotal; omega)
      hrOne2 (by decide)
  have hrc3 : (reg s3 rClk).val = rowEndBase n m :=
    (rc3.trans (by rw [hrc2, hrVal2]; rfl))
  have hl4 : l4.length = 1 + (sweepInitStoreScratch (bits := bits) h8 slPredBuf rClk).length := rfl
  have hrVal3 : (reg s3 rVal).val = n := by rw [k3 rVal (by decide) (by decide), hrVal2]
  have hrOne3 : (reg s3 rOne).val = 1 := by rw [k3 rOne (by decide) (by decide), hrOne2]
  obtain ⟨s4, st4, pc4, rc4, dPB, fr4, k4⟩ :=
    add_storeScratch_steps h8 rClk rVal slPredBuf (by decide) (by decide) (by decide)
      (by decide) (scratch_lt_workCap17 hWork (by decide))
      (by rw [hrc3, hrVal3]; simp only [rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      (by rw [pc3, ← hl3]; simp only [List.length_append, Nat.add_assoc]) hpl4
      (by simp only [List.length_append]; rw [hl4] at hszTotal; omega)
      hrOne3 (by decide)
  have hrc4 : (reg s4 rClk).val = predBufBase n m :=
    (rc4.trans (by rw [hrc3, hrVal3]; rfl))
  have hsteps : Steps code input (p0bPart1a h8).length s s4 := by
    have hl : (p0bPart1a h8).length = l0.length + l1.length + l2.length + l3.length + l4.length := by
      simp only [hp, List.length_append]
    rw [hl]
    exact (((st0.append st1).append st2).append st3).append st4
  refine ⟨s4, hsteps, ?_, ?_, ?_, ?_, ?_, ?_, hrc4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (p0bPart1a h8).length = (l0 ++ l1 ++ l2 ++ l3).length + l4.length := by
      simp only [hp, List.length_append]
    rw [pc4, ← hl4, hl]; simp only [List.length_append]; omega
  · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide),
        k1 _ (by decide) (by decide), k0 _ (by decide), hrZero]
  · rw [k4 _ (by decide) (by decide), hrOne3]
  · rw [k4 _ (by decide) (by decide), hrVal3]
  · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide),
        k1 _ (by decide) (by decide), k0 _ (by decide), hrRem]
  · rw [k4 _ (by decide) (by decide), k3 _ (by decide) (by decide), k2 _ (by decide) (by decide),
        k1 _ (by decide) (by decide), k0 _ (by decide), hrStk]
  · rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), fr1 _ (by decide), dOrd, hrClk]
  · rw [fr4 _ (by decide), fr3 _ (by decide), fr2 _ (by decide), dRnk, ← rc1, hrc1]
  · rw [fr4 _ (by decide), fr3 _ (by decide), dRS, ← rc2, hrc2]
  · rw [fr4 _ (by decide), dRE, ← rc3, hrc3]
  · rw [dPB, ← rc4, hrc4]
  · intro j hj
    have hne : j ≠ slPredBuf ∧ j ≠ slRowEnd ∧ j ≠ slRowStart ∧ j ≠ slRanks ∧ j ≠ slOrder := by
      rcases hj with h | h <;> refine ⟨by change j ≠ 16; omega, by change j ≠ 15; omega,
        by change j ≠ 14; omega, by change j ≠ 13; omega, by change j ≠ 12; omega⟩
    rw [fr4 j hne.1, fr3 j hne.2.1, fr2 j hne.2.2.1, fr1 j hne.2.2.2.1, fr0 j hne.2.2.2.2]

private theorem p0bPart1b_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m dictCnt : Nat) (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap) (hDict : dictCnt ≤ n)
    {entry : Nat} (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry) (hpl : Placed code entry (p0bPart1b h8))
    (hsz : entry + (p0bPart1b h8).length < code.size)
    (hrZero : (reg s rZero).val = 0) (hrOne : (reg s rOne).val = 1)
    (hrVal : (reg s rVal).val = n) (hrRem : (reg s rRem).val = m)
    (hrStk : (reg s rStack).val = n + 1)
    (hrClk : (reg s rClk).val = predBufBase n m)
    (hDictMem : (s.data[dictBase n m]?).map Fin.val = some dictCnt) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (p0bPart1b h8).length s t ∧
      t.pc = entry + (p0bPart1b h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rVal).val = n ∧ (reg t rStack).val = n + 1 ∧
      (reg t rClk).val = jumpBase n m ∧
      (t.data[slDictBase]?).map Fin.val = some (dictBase n m) ∧
      (t.data[slDictCnt]?).map Fin.val = some dictCnt ∧
      (t.data[slDictSnd]?).map Fin.val = some (dictBase n m + 1 + dictCnt) ∧
      (t.data[slDictSlots]?).map Fin.val = some (dictBase n m + 1 + 2 * dictCnt) ∧
      (t.data[slJumpBase]?).map Fin.val = some (jumpBase n m) ∧
      (∀ j, j < 3 ∨ 8 ≤ j → t.data[j]? = s.data[j]?) := by
  have _ := hn
  have hWork17 : 32 * n + 7 * m + 17 ≤ workCap := hWork
  let l5 := [.add rClk rClk rRem, .add rClk rClk rVal, .add rClk rClk rVal, .add rClk rClk rVal,
    .add rClk rClk rVal] ++ sweepInitStoreScratch (bits := bits) h8 slDictBase rClk
  let l6 := [.loadData rCnt rClk] ++ sweepInitStoreScratch (bits := bits) h8 slDictCnt rCnt
  let l7 := [.add rTin rClk rOne, .add rTin rTin rCnt] ++ sweepInitStoreScratch (bits := bits) h8 slDictSnd rTin
  let l8 := [.add rTin rTin rCnt] ++ sweepInitStoreScratch (bits := bits) h8 slDictSlots rTin
  let l9 := [.add rClk rClk rOne, .add rTmp rVal rVal, .add rTmp rTmp rVal, .add rClk rClk rTmp] ++
    sweepInitStoreScratch (bits := bits) h8 slJumpBase rClk
  have hp : p0bPart1b h8 = l5 ++ l6 ++ l7 ++ l8 ++ l9 := rfl
  have hpl5678 : Placed code entry (l5 ++ l6 ++ l7 ++ l8) := placed_append_left hpl
  have hpl567 : Placed code entry (l5 ++ l6 ++ l7) := placed_append_left hpl5678
  have hpl56 : Placed code entry (l5 ++ l6) := placed_append_left hpl567
  have hpl5 : Placed code entry l5 := placed_append_left hpl56
  have hpl6 : Placed code (entry + l5.length) l6 := placed_append_right hpl56
  have hpl7 : Placed code (entry + (l5 ++ l6).length) l7 := placed_append_right hpl567
  have hpl8 : Placed code (entry + (l5 ++ l6 ++ l7).length) l8 := placed_append_right hpl5678
  have hpl9 : Placed code (entry + (l5 ++ l6 ++ l7 ++ l8).length) l9 := placed_append_right hpl
  have hszTotal : entry + (l5.length + l6.length + l7.length + l8.length + l9.length) < code.size := by
    simpa [hp, List.length_append, Nat.add_assoc] using hsz
  have hl5 : l5.length = 5 + (sweepInitStoreScratch (bits := bits) h8 slDictBase rClk).length := rfl
  obtain ⟨s5a, st5a, pc5a, r5a, k5a, d5a⟩ :=
    step_add15_at (input := input) (s := s) (placed_fetch hpl5 (i := 0) rfl hpc)
      (by rw [hpc]; omega)
  have hpc5a : s5a.pc = entry + 1 := by rw [pc5a, hpc]
  obtain ⟨s5b, st5b, pc5b, r5b, k5b, d5b⟩ :=
    step_add15_at (input := input) (s := s5a) (placed_fetch hpl5 (i := 1) rfl hpc5a)
      (by rw [hpc5a]; rw [hl5] at hszTotal; omega)
  have hpc5b : s5b.pc = entry + 2 := by rw [pc5b, hpc5a]
  obtain ⟨s5c, st5c, pc5c, r5c, k5c, d5c⟩ :=
    step_add15_at (input := input) (s := s5b) (placed_fetch hpl5 (i := 2) rfl hpc5b)
      (by rw [hpc5b]; rw [hl5] at hszTotal; omega)
  have hpc5c : s5c.pc = entry + 3 := by rw [pc5c, hpc5b]
  obtain ⟨s5d, st5d, pc5d, r5d, k5d, d5d⟩ :=
    step_add15_at (input := input) (s := s5c) (placed_fetch hpl5 (i := 3) rfl hpc5c)
      (by rw [hpc5c]; rw [hl5] at hszTotal; omega)
  have hpc5d : s5d.pc = entry + 4 := by rw [pc5d, hpc5c]
  obtain ⟨s5e, st5e, pc5e, r5e, k5e, d5e⟩ :=
    step_add15_at (input := input) (s := s5d) (placed_fetch hpl5 (i := 4) rfl hpc5d)
      (by rw [hpc5d]; rw [hl5] at hszTotal; omega)
  have h5e_clk : (reg s5e rClk).val = dictBase n m := by
    have ha : (reg s5a rClk).val = predBufBase n m + m := by
      rw [r5a, PaperB.WordOps.add_no_wrap _ _ (by rw [hrClk, hrRem]; simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), hrClk, hrRem]
    have hb : (reg s5b rClk).val = predBufBase n m + m + n := by
      have hv := (congrArg Fin.val (k5a rVal (by decide))).trans hrVal
      rw [r5b, PaperB.WordOps.add_no_wrap _ _ (by rw [ha, hv]; simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), ha, hv]
    have hc : (reg s5c rClk).val = predBufBase n m + m + 2 * n := by
      have hv := (congrArg Fin.val (k5b rVal (by decide))).trans ((congrArg Fin.val (k5a rVal (by decide))).trans hrVal)
      rw [r5c, PaperB.WordOps.add_no_wrap _ _ (by rw [hb, hv]; simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), hb, hv]; omega
    have hd : (reg s5d rClk).val = predBufBase n m + m + 3 * n := by
      have hv := (congrArg Fin.val (k5c rVal (by decide))).trans ((congrArg Fin.val (k5b rVal (by decide))).trans ((congrArg Fin.val (k5a rVal (by decide))).trans hrVal))
      rw [r5d, PaperB.WordOps.add_no_wrap _ _ (by rw [hc, hv]; simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), hc, hv]; omega
    have hv := (congrArg Fin.val (k5d rVal (by decide))).trans ((congrArg Fin.val (k5c rVal (by decide))).trans ((congrArg Fin.val (k5b rVal (by decide))).trans ((congrArg Fin.val (k5a rVal (by decide))).trans hrVal)))
    rw [r5e, PaperB.WordOps.add_no_wrap _ _ (by rw [hd, hv]; simp only [predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), hd, hv]
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase]; omega
  have hk5e : ∀ r, r ≠ rClk → reg s5e r = reg s r := fun r h =>
    (k5e r h).trans ((k5d r h).trans ((k5c r h).trans ((k5b r h).trans (k5a r h))))
  have hpl5s : Placed code (entry + 5) (sweepInitStoreScratch h8 slDictBase rClk) :=
    placed_append_right (a := [.add rClk rClk rRem, .add rClk rClk rVal, .add rClk rClk rVal,
      .add rClk rClk rVal, .add rClk rClk rVal]) (by exact hpl5)
  obtain ⟨s5, st5s, pc5, dDB, fr5s, k5s⟩ :=
    sweepInitStoreScratch_steps h8 slDictBase rClk (by decide) (by decide)
      (scratch_lt_workCap17 hWork (by decide))
      (by rw [pc5e, hpc5d]) hpl5s (by rw [hl5] at hszTotal; omega)
      (by rw [hk5e rOne (by decide), hrOne])
  have hdt5 : ∀ j, j ≠ slDictBase → s5.data[j]? = s.data[j]? := fun j hj => by
    rw [fr5s j hj, d5e, d5d, d5c, d5b, d5a]
  have hdNe : dictBase n m ≠ slDictBase := by
    change dictBase n m ≠ 3
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
      rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
  have hDictAt5 : (s5.data[dictBase n m]?).map Fin.val = some dictCnt := by
    rw [hdt5 _ hdNe]; exact hDictMem
  have hpc5 : s5.pc = entry + l5.length := by rw [pc5, hl5]; omega
  have h5_clk : (reg s5 rClk).val = dictBase n m := by rw [k5s rClk (by decide), h5e_clk]
  have h5_one : (reg s5 rOne).val = 1 := by rw [k5s rOne (by decide), hk5e rOne (by decide), hrOne]
  have h5_val : (reg s5 rVal).val = n := by rw [k5s rVal (by decide), hk5e rVal (by decide), hrVal]
  have h5_zero : (reg s5 rZero).val = 0 := by rw [k5s rZero (by decide), hk5e rZero (by decide), hrZero]
  have h5_stk : (reg s5 rStack).val = n + 1 := by rw [k5s rStack (by decide), hk5e rStack (by decide), hrStk]
  have hpl6a : s5.data[(reg s5 rClk).val]? = some ⟨dictCnt, by omega⟩ := by
    rw [h5_clk]
    obtain ⟨w, hw1, hw2⟩ := word_mem_eq_of_map_val hDictAt5
    rw [hw1]; exact congrArg some (Fin.ext hw2)
  have hl6 : l6.length = 1 + (sweepInitStoreScratch (bits := bits) h8 slDictCnt rCnt).length := rfl
  obtain ⟨s6a, st6a, pc6a, r6a, k6a, d6a⟩ :=
    step_loadData_at' (input := input) (s := s5) (placed_fetch hpl6 (i := 0) rfl hpc5)
      (by rw [hpc5]; omega)
      (by rw [h5_clk]; simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      hpl6a
  have h6a_cnt : (reg s6a rCnt).val = dictCnt := by rw [r6a]
  have hpl6s : Placed code (entry + l5.length + 1) (sweepInitStoreScratch h8 slDictCnt rCnt) :=
    placed_append_right (a := [.loadData rCnt rClk]) (by exact hpl6)
  obtain ⟨s6, st6s, pc6, dDC, fr6s, k6s⟩ :=
    sweepInitStoreScratch_steps h8 slDictCnt rCnt (by decide) (by decide)
      (scratch_lt_workCap17 hWork (by decide))
      (by rw [pc6a, hpc5]) hpl6s (by rw [hl6] at hszTotal; omega) (by rw [k6a _ (by decide), h5_one])
  have hpc6 : s6.pc = entry + (l5 ++ l6).length := by
    simp only [pc6, hl6, List.length_append, Nat.add_assoc]
  have hl7 : l7.length = 2 + (sweepInitStoreScratch (bits := bits) h8 slDictSnd rTin).length := rfl
  have h6_clk : (reg s6 rClk).val = dictBase n m := by rw [k6s rClk (by decide), k6a _ (by decide), h5_clk]
  have h6_one : (reg s6 rOne).val = 1 := by rw [k6s rOne (by decide), k6a _ (by decide), h5_one]
  have h6_cnt : (reg s6 rCnt).val = dictCnt := by rw [k6s rCnt (by decide), h6a_cnt]
  have hDictAreaFit : dictBase n m + 1 + 2 * dictCnt < workCap := by
    simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
      rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
    omega
  obtain ⟨s7a, st7a, pc7a, r7a, k7a, d7a⟩ :=
    step_add15_at (input := input) (s := s6) (placed_fetch hpl7 (i := 0) rfl hpc6)
      (by rw [hpc6]; simp only [List.length_append]; rw [hl7] at hszTotal; omega)
  have hpc7a : s7a.pc = entry + (l5 ++ l6).length + 1 := by rw [pc7a, hpc6]
  obtain ⟨s7b, st7b, pc7b, r7b, k7b, d7b⟩ :=
    step_add15_at (input := input) (s := s7a) (placed_fetch hpl7 (i := 1) rfl hpc7a)
      (by rw [hpc7a]; simp only [List.length_append]; rw [hl7] at hszTotal; omega)
  have h7b_tin : (reg s7b rTin).val = dictBase n m + 1 + dictCnt := by
    have h7a_tin : (reg s7a rTin).val = dictBase n m + 1 := by
      rw [r7a, PaperB.WordOps.add_no_wrap _ _ (by rw [h6_clk, h6_one]; omega), h6_clk, h6_one]
    have h7a_cnt : (reg s7a rCnt).val = dictCnt := by rw [k7a _ (by decide), h6_cnt]
    rw [r7b, PaperB.WordOps.add_no_wrap _ _ (by rw [h7a_tin, h7a_cnt]; omega), h7a_tin, h7a_cnt]
  have hpl7s : Placed code (entry + (l5 ++ l6).length + 2)
      (sweepInitStoreScratch h8 slDictSnd rTin) := by
    have h' : Placed code (entry + (l5 ++ l6).length)
        ([.add rTin rClk rOne, .add rTin rTin rCnt] ++ sweepInitStoreScratch h8 slDictSnd rTin) := hpl7
    simpa [Nat.add_assoc] using placed_append_right h'
  obtain ⟨s7, st7s, pc7, dDSnd, fr7s, k7s⟩ :=
    sweepInitStoreScratch_steps h8 slDictSnd rTin (by decide) (by decide)
      (scratch_lt_workCap17 hWork (by decide))
      (by rw [pc7b, hpc7a]) hpl7s
      (by simp only [List.length_append]; rw [hl7] at hszTotal; omega)
      (by rw [k7b _ (by decide), k7a _ (by decide), h6_one])
  have hpc7 : s7.pc = entry + (l5 ++ l6 ++ l7).length := by
    simp only [pc7, hl7, List.length_append, Nat.add_assoc]
  have hl8 : l8.length = 1 + (sweepInitStoreScratch (bits := bits) h8 slDictSlots rTin).length := rfl
  have h7_tin : (reg s7 rTin).val = dictBase n m + 1 + dictCnt := by rw [k7s _ (by decide), h7b_tin]
  have h7_cnt : (reg s7 rCnt).val = dictCnt := by rw [k7s _ (by decide), k7b _ (by decide), k7a _ (by decide), h6_cnt]
  have h7_one : (reg s7 rOne).val = 1 := by rw [k7s _ (by decide), k7b _ (by decide), k7a _ (by decide), h6_one]
  obtain ⟨s8, st8, pc8, rtin8, dDSl, fr8, k8⟩ :=
    add_storeScratch_steps h8 rTin rCnt slDictSlots (by decide) (by decide) (by decide)
      (by decide) (scratch_lt_workCap17 hWork (by decide))
      (by rw [h7_tin, h7_cnt]; omega) hpc7 hpl8
      (by simp only [List.length_append]; rw [hl8] at hszTotal; omega) h7_one (by decide)
  have hpc8 : s8.pc = entry + (l5 ++ l6 ++ l7 ++ l8).length := by
    rw [pc8, ← hl8]; simp only [List.length_append, Nat.add_assoc]
  have hk7_all : ∀ r, r ≠ rTin → r ≠ rTmp → reg s7 r = reg s6 r := fun r hn1 hn2 =>
    (k7s r hn2).trans ((k7b r hn1).trans (k7a r hn1))
  have hk6_all : ∀ r, r ≠ rCnt → r ≠ rTmp → reg s6 r = reg s5 r := fun r hn1 hn2 =>
    (k6s r hn2).trans (k6a r hn1)
  have h8_clk : (reg s8 rClk).val = dictBase n m := by
    rw [k8 _ (by decide) (by decide), hk7_all _ (by decide) (by decide), h6_clk]
  have h8_one : (reg s8 rOne).val = 1 := by rw [k8 _ (by decide) (by decide), h7_one]
  have h8_val : (reg s8 rVal).val = n := by
    rw [k8 _ (by decide) (by decide), hk7_all _ (by decide) (by decide),
        hk6_all _ (by decide) (by decide), h5_val]
  have h8_zero : (reg s8 rZero).val = 0 := by
    rw [k8 _ (by decide) (by decide), hk7_all _ (by decide) (by decide),
        hk6_all _ (by decide) (by decide), h5_zero]
  have h8_stk : (reg s8 rStack).val = n + 1 := by
    rw [k8 _ (by decide) (by decide), hk7_all _ (by decide) (by decide),
        hk6_all _ (by decide) (by decide), h5_stk]
  have hl9 : l9.length = 4 + (sweepInitStoreScratch (bits := bits) h8 slJumpBase rClk).length := rfl
  obtain ⟨s9a, st9a, pc9a, r9a, k9a, d9a⟩ :=
    step_add15_at (input := input) (s := s8) (placed_fetch hpl9 (i := 0) rfl hpc8)
      (by rw [hpc8]; simp only [List.length_append]; rw [hl9] at hszTotal; omega)
  have hpc9a : s9a.pc = entry + (l5 ++ l6 ++ l7 ++ l8).length + 1 := by rw [pc9a, hpc8]
  obtain ⟨s9b, st9b, pc9b, r9b, k9b, d9b⟩ :=
    step_add15_at (input := input) (s := s9a) (placed_fetch hpl9 (i := 1) rfl hpc9a)
      (by rw [hpc9a]; simp only [List.length_append]; rw [hl9] at hszTotal; omega)
  have hpc9b : s9b.pc = entry + (l5 ++ l6 ++ l7 ++ l8).length + 2 := by rw [pc9b, hpc9a]
  obtain ⟨s9c, st9c, pc9c, r9c, k9c, d9c⟩ :=
    step_add15_at (input := input) (s := s9b) (placed_fetch hpl9 (i := 2) rfl hpc9b)
      (by rw [hpc9b]; simp only [List.length_append]; rw [hl9] at hszTotal; omega)
  have hpc9c : s9c.pc = entry + (l5 ++ l6 ++ l7 ++ l8).length + 3 := by rw [pc9c, hpc9b]
  obtain ⟨s9d, st9d, pc9d, r9d, k9d, d9d⟩ :=
    step_add15_at (input := input) (s := s9c) (placed_fetch hpl9 (i := 3) rfl hpc9c)
      (by rw [hpc9c]; simp only [List.length_append]; rw [hl9] at hszTotal; omega)
  have h9d_clk : (reg s9d rClk).val = jumpBase n m := by
    have hJumpFit : jumpBase n m < workCap := by
      simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    have ha : (reg s9a rClk).val = dictBase n m + 1 := by
      rw [r9a, PaperB.WordOps.add_no_wrap _ _ (by rw [h8_clk, h8_one]; omega), h8_clk, h8_one]
    have hb : (reg s9b rTmp).val = 2 * n := by
      have hv := (congrArg Fin.val (k9a rVal (by decide))).trans h8_val
      rw [r9b, PaperB.WordOps.add_no_wrap _ _ (by rw [hv]; omega), hv]; omega
    have hc : (reg s9c rTmp).val = 3 * n := by
      have hv := (congrArg Fin.val (k9b rVal (by decide))).trans ((congrArg Fin.val (k9a rVal (by decide))).trans h8_val)
      rw [r9c, PaperB.WordOps.add_no_wrap _ _ (by rw [hb, hv]; omega), hb, hv]; omega
    have hca : (reg s9c rClk).val = dictBase n m + 1 := by rw [k9c _ (by decide), k9b _ (by decide), ha]
    have hJumpEq : dictBase n m + 1 + 3 * n = jumpBase n m := by
      simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega
    rw [r9d, PaperB.WordOps.add_no_wrap _ _ (by rw [hca, hc]; omega), hca, hc, hJumpEq]
  have hpl9s : Placed code (entry + (l5 ++ l6 ++ l7 ++ l8).length + 4)
      (sweepInitStoreScratch h8 slJumpBase rClk) := by
    have h' : Placed code (entry + (l5 ++ l6 ++ l7 ++ l8).length)
        ([.add rClk rClk rOne, .add rTmp rVal rVal, .add rTmp rTmp rVal, .add rClk rClk rTmp] ++
          sweepInitStoreScratch h8 slJumpBase rClk) := hpl9
    simpa [Nat.add_assoc] using placed_append_right h'
  obtain ⟨s9, st9s, pc9, dJB, fr9s, k9s⟩ :=
    sweepInitStoreScratch_steps h8 slJumpBase rClk (by decide) (by decide)
      (scratch_lt_workCap17 hWork (by decide))
      (by rw [pc9d, hpc9c]) hpl9s (by simp only [List.length_append]; rw [hl9] at hszTotal; omega)
      (by rw [k9d _ (by decide), k9c _ (by decide), k9b _ (by decide), k9a _ (by decide), h8_one])
  have hsteps5 : Steps code input l5.length s s5 := by
    rw [hl5, show 5 + (sweepInitStoreScratch (bits := bits) h8 slDictBase rClk).length =
        1 + (1 + (1 + (1 + (1 + (sweepInitStoreScratch (bits := bits) h8 slDictBase rClk).length)))) by omega]
    exact .cons st5a (.cons st5b (.cons st5c (.cons st5d (.cons st5e st5s))))
  have hsteps6 : Steps code input l6.length s5 s6 := .cons st6a st6s
  have hsteps7 : Steps code input l7.length s6 s7 := by
    rw [hl7, show 2 + (sweepInitStoreScratch (bits := bits) h8 slDictSnd rTin).length =
        1 + (1 + (sweepInitStoreScratch (bits := bits) h8 slDictSnd rTin).length) by omega]
    exact .cons st7a (.cons st7b st7s)
  have hsteps9 : Steps code input l9.length s8 s9 := by
    rw [hl9, show 4 + (sweepInitStoreScratch (bits := bits) h8 slJumpBase rClk).length =
        1 + (1 + (1 + (1 + (sweepInitStoreScratch (bits := bits) h8 slJumpBase rClk).length))) by omega]
    exact .cons st9a (.cons st9b (.cons st9c (.cons st9d st9s)))
  have hstepsAll : Steps code input (p0bPart1b h8).length s s9 := by
    have hl : (p0bPart1b h8).length = l5.length + l6.length + l7.length + l8.length + l9.length := by
      simp only [hp, List.length_append]
    rw [hl]
    exact (((hsteps5.append hsteps6).append hsteps7).append st8).append hsteps9
  have h9dt : ∀ j, j ≠ slJumpBase → s9.data[j]? = s8.data[j]? := fun j hj => by rw [fr9s j hj, d9d, d9c, d9b, d9a]
  have h7dt : ∀ j, j ≠ slDictSnd → s7.data[j]? = s6.data[j]? := fun j hj => by rw [fr7s j hj, d7b, d7a]
  have h6dt : ∀ j, j ≠ slDictCnt → s6.data[j]? = s5.data[j]? := fun j hj => by rw [fr6s j hj, d6a]
  have hk9d : ∀ r, r ≠ rClk → r ≠ rTmp → reg s9 r = reg s8 r := fun r hn1 hn2 =>
    (k9s r hn2).trans ((k9d r hn1).trans ((k9c r hn2).trans ((k9b r hn2).trans (k9a r hn1))))
  refine ⟨s9, hstepsAll, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (p0bPart1b h8).length = (l5 ++ l6 ++ l7 ++ l8).length + l9.length := by
      simp only [hp, List.length_append]
    simp only [pc9, hl9, hl, List.length_append, Nat.add_assoc]
  · rw [hk9d _ (by decide) (by decide), h8_zero]
  · rw [hk9d _ (by decide) (by decide), h8_one]
  · rw [hk9d _ (by decide) (by decide), h8_val]
  · rw [hk9d _ (by decide) (by decide), h8_stk]
  · rw [k9s _ (by decide), h9d_clk]
  · rw [h9dt _ (by decide), fr8 _ (by decide), h7dt _ (by decide), h6dt _ (by decide), dDB, h5e_clk]
  · rw [h9dt _ (by decide), fr8 _ (by decide), h7dt _ (by decide), dDC, h6a_cnt]
  · rw [h9dt _ (by decide), fr8 _ (by decide), dDSnd, h7b_tin]
  · rw [h9dt _ (by decide), dDSl, h7_tin, h7_cnt]; simp only [Nat.two_mul, Nat.add_assoc]
  · rw [dJB, h9d_clk]
  · intro j hj
    have hne : j ≠ slJumpBase ∧ j ≠ slDictSlots ∧ j ≠ slDictSnd ∧ j ≠ slDictCnt ∧ j ≠ slDictBase := by
      rcases hj with h | h <;> refine ⟨by change j ≠ 7; omega, by change j ≠ 6; omega,
        by change j ≠ 5; omega, by change j ≠ 4; omega, by change j ≠ 3; omega⟩
    rw [h9dt j hne.1, fr8 j hne.2.1, h7dt j hne.2.2.1, h6dt j hne.2.2.2.1, hdt5 j hne.2.2.2.2]

private theorem p0bPart1_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m dictCnt : Nat) (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap) (hDict : dictCnt ≤ n)
    {entry : Nat} (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry) (hpl : Placed code entry (p0bPart1 h8))
    (hsz : entry + (p0bPart1 h8).length < code.size)
    (hrZero : (reg s rZero).val = 0) (hrOne : (reg s rOne).val = 1)
    (hrVal : (reg s rVal).val = n) (hrRem : (reg s rRem).val = m)
    (hrStk : (reg s rStack).val = n + 1)
    (hrClk : (reg s rClk).val = orderBase n m)
    (hDictMem : (s.data[dictBase n m]?).map Fin.val = some dictCnt) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (p0bPart1 h8).length s t ∧
      t.pc = entry + (p0bPart1 h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rVal).val = n ∧ (reg t rStack).val = n + 1 ∧
      (reg t rClk).val = jumpBase n m ∧
      (t.data[slOrder]?).map Fin.val = some (orderBase n m) ∧
      (t.data[slRanks]?).map Fin.val = some (ranksBase n m) ∧
      (t.data[slRowStart]?).map Fin.val = some (rowStartBase n m) ∧
      (t.data[slRowEnd]?).map Fin.val = some (rowEndBase n m) ∧
      (t.data[slPredBuf]?).map Fin.val = some (predBufBase n m) ∧
      (t.data[slDictBase]?).map Fin.val = some (dictBase n m) ∧
      (t.data[slDictCnt]?).map Fin.val = some dictCnt ∧
      (t.data[slDictSnd]?).map Fin.val = some (dictBase n m + 1 + dictCnt) ∧
      (t.data[slDictSlots]?).map Fin.val = some (dictBase n m + 1 + 2 * dictCnt) ∧
      (t.data[slJumpBase]?).map Fin.val = some (jumpBase n m) ∧
      (∀ j, j < 3 ∨ 17 ≤ j → t.data[j]? = s.data[j]?) := by
  have hplAB : Placed code entry (p0bPart1a h8 ++ p0bPart1b h8) := by
    rw [← p0bPart1_eq_ab]; exact hpl
  have hLen : (p0bPart1 h8).length = (p0bPart1a h8).length + (p0bPart1b h8).length := by
    rw [p0bPart1_eq_ab, List.length_append]
  obtain ⟨sA, stA, pcA, zA, oA, vA, rA, stkA, clkA,
      dOrd, dRnk, dRS, dRE, dPB, frA⟩ :=
    p0bPart1a_steps h8 n m hWork s hpc (placed_append_left hplAB) (by rw [hLen] at hsz; omega)
      hrZero hrOne hrVal hrRem hrStk hrClk
  have hdDict : (sA.data[dictBase n m]?).map Fin.val = some dictCnt := by
    rw [frA _ (Or.inr (by
      simp only [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase,
        rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega))]
    exact hDictMem
  obtain ⟨sB, stB, pcB, zB, oB, vB, stkB, clkB,
      dDB, dDC, dDS, dDSl, dJB, frB⟩ :=
    p0bPart1b_steps h8 n m dictCnt hn hWork hDict sA pcA (placed_append_right hplAB)
      (by rw [hLen] at hsz; omega) zA oA vA rA stkA clkA hdDict
  refine ⟨sB, hLen ▸ stA.append stB, by rw [pcB, hLen, Nat.add_assoc],
    zB, oB, vB, stkB, clkB, ?_, ?_, ?_, ?_, ?_, dDB, dDC, dDS, dDSl, dJB, ?_⟩
  · rw [frB _ (Or.inr (by decide))]; exact dOrd
  · rw [frB _ (Or.inr (by decide))]; exact dRnk
  · rw [frB _ (Or.inr (by decide))]; exact dRS
  · rw [frB _ (Or.inr (by decide))]; exact dRE
  · rw [frB _ (Or.inr (by decide))]; exact dPB
  · intro j hj
    rcases hj with h | h
    · rw [frB j (Or.inl h), frA j (Or.inl (by omega))]
    · rw [frB j (Or.inr (by omega)), frA j (Or.inr h)]

private theorem p0bPart2_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    {code : Program (layout bits inputCap workCap hi hw)}
    {input : Input (layout bits inputCap workCap hi hw)}
    (n m : Nat) (hn : 3 ≤ n) (hWork : rawWorkCap n m ≤ workCap)
    {entry : Nat} (s : State (layout bits inputCap workCap hi hw))
    (hpc : s.pc = entry) (hpl : Placed code entry (p0bPart2 h8))
    (hsz : entry + (p0bPart2 h8).length < code.size)
    (hrZero : (reg s rZero).val = 0) (hrOne : (reg s rOne).val = 1)
    (hrVal : (reg s rVal).val = n) (hrStk : (reg s rStack).val = n + 1)
    (hrClk : (reg s rClk).val = jumpBase n m) :
    ∃ t : State (layout bits inputCap workCap hi hw),
      Steps code input (p0bPart2 h8).length s t ∧
      t.pc = entry + (p0bPart2 h8).length ∧
      (reg t rZero).val = 0 ∧ (reg t rOne).val = 1 ∧
      (reg t rVal).val = n ∧ (reg t rStack).val = n + 1 ∧
      (reg t rTin).val = backFstBase n m ∧ (reg t rTout).val = backSndBase n m ∧
      (reg t rOff).val = labelsBase n m ∧ (reg t rPtr).val = 0 ∧
      (t.data[slBackFst]?).map Fin.val = some (backFstBase n m) ∧
      (t.data[slBackSnd]?).map Fin.val = some (backSndBase n m) ∧
      (t.data[slLabels]?).map Fin.val = some (labelsBase n m) ∧
      (t.data[slParents]?).map Fin.val = some (parentsBase n m) ∧
      (t.data[slSource]?).map Fin.val = some (sourceBase n m) ∧
      (t.data[slIdx]?).map Fin.val = some 0 ∧
      (t.data[jumpBase n m]?).map Fin.val = some 0 ∧
      (t.data[jumpBase n m + 1]?).map Fin.val = some 0 ∧
      (t.data[jumpBase n m + 2]?).map Fin.val = some 0 ∧
      (t.data[parentsBase n m]?).map Fin.val = some 0 ∧
      (∀ j, (j < 8 ∨ (12 ≤ j ∧ j < 17) ∨ (19 ≤ j ∧ j < jumpBase n m)) →
        t.data[j]? = s.data[j]?) := by
  have hCap : 32 * n + 7 * m + 17 ≤ workCap := hWork
  let l0 := [.storeData rClk rZero, .add rTout rClk rOne, .storeData rTout rZero,
    .add rTout rTout rOne, .storeData rTout rZero,
    .add rTout rStack rStack, .add rTout rTout rStack, .add rClk rClk rTout] ++
    sweepInitStoreScratch (bits := bits) h8 slBackFst rClk
  let l1 := [.mov rTin rClk, .add rClk rClk rStack] ++
    sweepInitStoreScratch (bits := bits) h8 slBackSnd rClk
  let l2 := [.mov rTout rClk, .add rClk rClk rStack] ++
    sweepInitStoreScratch (bits := bits) h8 slLabels rClk
  let l3 := [.mov rOff rClk, .add rClk rClk rVal] ++
    sweepInitStoreScratch (bits := bits) h8 slParents rClk
  let l4 := [.storeData rClk rZero, .add rClk rClk rStack] ++
    sweepInitStoreScratch (bits := bits) h8 slSource rClk
  let l5 := sweepInitStoreScratch (bits := bits) h8 slIdx rZero
  let l6 : List (Instr bits 15) := [.mov rPtr rZero]
  have hp : p0bPart2 h8 = l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6 := rfl
  have hpl012345 : Placed code entry (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5) := placed_append_left hpl
  have hpl01234 : Placed code entry (l0 ++ l1 ++ l2 ++ l3 ++ l4) := placed_append_left hpl012345
  have hpl0123 : Placed code entry (l0 ++ l1 ++ l2 ++ l3) := placed_append_left hpl01234
  have hpl012 : Placed code entry (l0 ++ l1 ++ l2) := placed_append_left hpl0123
  have hpl01 : Placed code entry (l0 ++ l1) := placed_append_left hpl012
  have hpl0 : Placed code entry l0 := placed_append_left hpl01
  have hpl1 : Placed code (entry + l0.length) l1 := placed_append_right hpl01
  have hpl2 : Placed code (entry + (l0 ++ l1).length) l2 := placed_append_right hpl012
  have hpl3 : Placed code (entry + (l0 ++ l1 ++ l2).length) l3 := placed_append_right hpl0123
  have hpl4 : Placed code (entry + (l0 ++ l1 ++ l2 ++ l3).length) l4 := placed_append_right hpl01234
  have hpl5 : Placed code (entry + (l0 ++ l1 ++ l2 ++ l3 ++ l4).length) l5 := placed_append_right hpl012345
  have hpl6 : Placed code (entry + (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5).length) l6 := placed_append_right hpl
  have hszTotal : entry + (l0.length + l1.length + l2.length + l3.length + l4.length + l5.length + l6.length) < code.size := by
    simpa [hp, List.length_append, Nat.add_assoc] using hsz
  -- Segment 0: write 3 root jump words at `jumpBase + 0,1,2`, advance `rClk` to `backFstBase`, store `slBackFst`
  have hl0 : l0.length = 8 + (sweepInitStoreScratch (bits := bits) h8 slBackFst rClk).length := rfl
  obtain ⟨s0a, st0a, pc0a, d0a, k0a⟩ :=
    step_storeData_at (input := input) (s := s) (placed_fetch hpl0 (i := 0) rfl hpc)
      (by rw [hpc]; rw [hl0] at hszTotal; omega)
      (by rw [hrClk]; simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
  have hpc0a : s0a.pc = entry + 1 := by rw [pc0a, hpc]
  obtain ⟨s0b, st0b, pc0b, r0b, k0b, d0b⟩ :=
    step_add15_at (input := input) (s := s0a) (placed_fetch hpl0 (i := 1) rfl hpc0a)
      (by rw [hpc0a]; rw [hl0] at hszTotal; omega)
  have hpc0b : s0b.pc = entry + 2 := by rw [pc0b, hpc0a]
  have h0b_tout : (reg s0b rTout).val = jumpBase n m + 1 := by
    rw [r0b, PaperB.WordOps.add_no_wrap _ _ (by
      rw [k0a rClk, k0a rOne, hrClk, hrOne]; simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega),
      k0a rClk, k0a rOne, hrClk, hrOne]
  obtain ⟨s0c, st0c, pc0c, d0c, k0c⟩ :=
    step_storeData_at (input := input) (s := s0b) (placed_fetch hpl0 (i := 2) rfl hpc0b)
      (by rw [hpc0b]; rw [hl0] at hszTotal; omega)
      (by rw [h0b_tout]; simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
  have hpc0c : s0c.pc = entry + 3 := by rw [pc0c, hpc0b]
  obtain ⟨s0d, st0d, pc0d, r0d, k0d, d0d⟩ :=
    step_add15_at (input := input) (s := s0c) (placed_fetch hpl0 (i := 3) rfl hpc0c)
      (by rw [hpc0c]; rw [hl0] at hszTotal; omega)
  have hpc0d : s0d.pc = entry + 4 := by rw [pc0d, hpc0c]
  have h0d_tout : (reg s0d rTout).val = jumpBase n m + 2 := by
    have ht := (congrArg Fin.val (k0c rTout)).trans h0b_tout
    have ho := (congrArg Fin.val (k0c rOne)).trans ((congrArg Fin.val (k0b rOne (by decide))).trans ((congrArg Fin.val (k0a rOne)).trans hrOne))
    rw [r0d, PaperB.WordOps.add_no_wrap _ _ (by rw [ht, ho]; simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), ht, ho]
  obtain ⟨s0e, st0e, pc0e, d0e, k0e⟩ :=
    step_storeData_at (input := input) (s := s0d) (placed_fetch hpl0 (i := 4) rfl hpc0d)
      (by rw [hpc0d]; rw [hl0] at hszTotal; omega)
      (by rw [h0d_tout]; simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
  have hpc0e : s0e.pc = entry + 5 := by rw [pc0e, hpc0d]
  obtain ⟨s0f, st0f, pc0f, r0f, k0f, d0f⟩ :=
    step_add15_at (input := input) (s := s0e) (placed_fetch hpl0 (i := 5) rfl hpc0e)
      (by rw [hpc0e]; rw [hl0] at hszTotal; omega)
  have hpc0f : s0f.pc = entry + 6 := by rw [pc0f, hpc0e]
  obtain ⟨s0g, st0g, pc0g, r0g, k0g, d0g⟩ :=
    step_add15_at (input := input) (s := s0f) (placed_fetch hpl0 (i := 6) rfl hpc0f)
      (by rw [hpc0f]; rw [hl0] at hszTotal; omega)
  have hpc0g : s0g.pc = entry + 7 := by rw [pc0g, hpc0f]
  obtain ⟨s0h, st0h, pc0h, r0h, k0h, d0h⟩ :=
    step_add15_at (input := input) (s := s0g) (placed_fetch hpl0 (i := 7) rfl hpc0g)
      (by rw [hpc0g]; rw [hl0] at hszTotal; omega)
  have hk0e_all : ∀ r, r ≠ rTout → reg s0e r = reg s r := fun r hn =>
    (k0e r).trans ((k0d r hn).trans ((k0c r).trans ((k0b r hn).trans (k0a r))))
  have h0h_clk : (reg s0h rClk).val = backFstBase n m := by
    have hstk := (congrArg Fin.val (hk0e_all rStack (by decide))).trans hrStk
    have h0f_tout : (reg s0f rTout).val = 2 * (n + 1) := by
      rw [r0f, PaperB.WordOps.add_no_wrap _ _ (by rw [hstk]; omega), hstk]; omega
    have h0g_tout : (reg s0g rTout).val = 3 * (n + 1) := by
      have hstk' := (congrArg Fin.val (k0f rStack (by decide))).trans hstk
      rw [r0g, PaperB.WordOps.add_no_wrap _ _ (by rw [h0f_tout, hstk']; omega), h0f_tout, hstk']; omega
    have h0g_clk : (reg s0g rClk).val = jumpBase n m := by
      rw [k0g _ (by decide), k0f _ (by decide), hk0e_all _ (by decide), hrClk]
    rw [r0h, PaperB.WordOps.add_no_wrap _ _ (by rw [h0g_clk, h0g_tout]; simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), h0g_clk, h0g_tout]
    simp only [backFstBase, jumpBase]
  have hk0h_all : ∀ r, r ≠ rTout → r ≠ rClk → reg s0h r = reg s r := fun r hn1 hn2 =>
    (k0h r hn2).trans ((k0g r hn1).trans ((k0f r hn1).trans (hk0e_all r hn1)))
  have hpl0s : Placed code (entry + 8) (sweepInitStoreScratch h8 slBackFst rClk) := by
    have h' : Placed code entry ([.storeData rClk rZero, .add rTout rClk rOne,
      .storeData rTout rZero, .add rTout rTout rOne, .storeData rTout rZero,
      .add rTout rStack rStack, .add rTout rTout rStack, .add rClk rClk rTout] ++
      sweepInitStoreScratch h8 slBackFst rClk) := hpl0
    exact placed_append_right h'
  obtain ⟨s0, st0s, pc0, dBF, fr0s, k0s⟩ :=
    sweepInitStoreScratch_steps h8 slBackFst rClk (by decide) (by decide)
      (scratch_lt_workCap30 hWork hn (by decide))
      (by rw [pc0h, hpc0g]) hpl0s
      (by rw [hl0] at hszTotal; omega)
      (by rw [hk0h_all _ (by decide) (by decide), hrOne])
  -- Segment 1..3: `mov_add_storeScratch_steps` for `slBackSnd`, `slLabels`, `slParents`
  have hpc0 : s0.pc = entry + l0.length := by rw [pc0, hl0]; omega
  have h0_one : (reg s0 rOne).val = 1 := by rw [k0s _ (by decide), hk0h_all _ (by decide) (by decide), hrOne]
  have h0_zero : (reg s0 rZero).val = 0 := by rw [k0s _ (by decide), hk0h_all _ (by decide) (by decide), hrZero]
  have h0_val : (reg s0 rVal).val = n := by rw [k0s _ (by decide), hk0h_all _ (by decide) (by decide), hrVal]
  have h0_stk : (reg s0 rStack).val = n + 1 := by rw [k0s _ (by decide), hk0h_all _ (by decide) (by decide), hrStk]
  have h0_clk : (reg s0 rClk).val = backFstBase n m := by rw [k0s _ (by decide), h0h_clk]
  have hl1 : l1.length = 2 + (sweepInitStoreScratch (bits := bits) h8 slBackSnd rClk).length := rfl
  obtain ⟨s1, st1, pc1, r1_tin, r1_clk, dBS, fr1, k1⟩ :=
    mov_add_storeScratch_steps h8 rTin rStack slBackSnd (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (scratch_lt_workCap30 hWork hn (by decide))
      (by rw [h0_clk, h0_stk]; simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      hpc0 hpl1 (by rw [hl1] at hszTotal; omega) h0_one
  have hr1_tin : (reg s1 rTin).val = backFstBase n m := by rw [r1_tin, h0_clk]
  have hr1_clk : (reg s1 rClk).val = backSndBase n m := by
    rw [r1_clk, h0_clk, h0_stk]; simp only [backSndBase, backFstBase]
  have hl2 : l2.length = 2 + (sweepInitStoreScratch (bits := bits) h8 slLabels rClk).length := rfl
  obtain ⟨s2, st2, pc2, r2_tout, r2_clk, dLab, fr2, k2⟩ :=
    mov_add_storeScratch_steps h8 rTout rStack slLabels (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (scratch_lt_workCap30 hWork hn (by decide))
      (by rw [hr1_clk, k1 rStack (by decide) (by decide) (by decide), h0_stk]; simp only [backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      (by simp only [pc1, ← hl1, List.length_append, Nat.add_assoc]) hpl2
      (by simp only [List.length_append]; rw [hl2] at hszTotal; omega)
      (by rw [k1 rOne (by decide) (by decide) (by decide), h0_one])
  have hr2_tout : (reg s2 rTout).val = backSndBase n m := by rw [r2_tout, hr1_clk]
  have hr2_clk : (reg s2 rClk).val = labelsBase n m := by
    rw [r2_clk, hr1_clk, k1 rStack (by decide) (by decide) (by decide), h0_stk]
    simp only [labelsBase, backSndBase]
  have hl3 : l3.length = 2 + (sweepInitStoreScratch (bits := bits) h8 slParents rClk).length := rfl
  obtain ⟨s3, st3, pc3, r3_off, r3_clk, dPar, fr3, k3⟩ :=
    mov_add_storeScratch_steps h8 rOff rVal slParents (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (scratch_lt_workCap30 hWork hn (by decide))
      (by rw [hr2_clk, k2 rVal (by decide) (by decide) (by decide), k1 rVal (by decide) (by decide) (by decide), h0_val]
          simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
      (by rw [pc2, ← hl2]; simp only [List.length_append, Nat.add_assoc]) hpl3
      (by simp only [List.length_append]; rw [hl3] at hszTotal; omega)
      (by rw [k2 rOne (by decide) (by decide) (by decide), k1 rOne (by decide) (by decide) (by decide), h0_one])
  have hr3_off : (reg s3 rOff).val = labelsBase n m := by rw [r3_off, hr2_clk]
  have hr3_clk : (reg s3 rClk).val = parentsBase n m := by
    rw [r3_clk, hr2_clk, k2 rVal (by decide) (by decide) (by decide),
        k1 rVal (by decide) (by decide) (by decide), h0_val]
    simp only [parentsBase, labelsBase]
  -- Segment 4: `.storeData rClk rZero`, `.add rClk rClk rStack`, `slSource`
  have hpc3 : s3.pc = entry + (l0 ++ l1 ++ l2 ++ l3).length := by
    rw [pc3, ← hl3]; simp only [List.length_append, Nat.add_assoc]
  have hk3_all : ∀ r, r ≠ rOff → r ≠ rTout → r ≠ rTin → r ≠ rClk → r ≠ rTmp → reg s3 r = reg s0 r :=
    fun r h1 h2 h3 h4 h5 => (k3 r h1 h4 h5).trans ((k2 r h2 h4 h5).trans (k1 r h3 h4 h5))
  have h3_zero : (reg s3 rZero).val = 0 := by rw [hk3_all _ (by decide) (by decide) (by decide) (by decide) (by decide), h0_zero]
  have h3_one : (reg s3 rOne).val = 1 := by rw [hk3_all _ (by decide) (by decide) (by decide) (by decide) (by decide), h0_one]
  have h3_stk : (reg s3 rStack).val = n + 1 := by rw [hk3_all _ (by decide) (by decide) (by decide) (by decide) (by decide), h0_stk]
  have h3_val : (reg s3 rVal).val = n := by rw [hk3_all _ (by decide) (by decide) (by decide) (by decide) (by decide), h0_val]
  have hl4 : l4.length = 2 + (sweepInitStoreScratch (bits := bits) h8 slSource rClk).length := rfl
  obtain ⟨s4a, st4a, pc4a, d4a, k4a⟩ :=
    step_storeData_at (input := input) (s := s3) (placed_fetch hpl4 (i := 0) rfl hpc3)
      (by rw [hpc3]; simp only [List.length_append]; rw [hl4] at hszTotal; omega)
      (by rw [hr3_clk]; simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
  have hpc4a : s4a.pc = entry + (l0 ++ l1 ++ l2 ++ l3).length + 1 := by rw [pc4a, hpc3]
  obtain ⟨s4b, st4b, pc4b, r4b, k4b, d4b⟩ :=
    step_add15_at (input := input) (s := s4a) (placed_fetch hpl4 (i := 1) rfl hpc4a)
      (by rw [hpc4a]; simp only [List.length_append]; rw [hl4] at hszTotal; omega)
  have h4b_clk : (reg s4b rClk).val = sourceBase n m := by
    have hc := (congrArg Fin.val (k4a rClk)).trans hr3_clk
    have hs := (congrArg Fin.val (k4a rStack)).trans h3_stk
    rw [r4b, PaperB.WordOps.add_no_wrap _ _ (by rw [hc, hs]; simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega), hc, hs]
    simp only [sourceBase, parentsBase]
  have hpl4s : Placed code (entry + (l0 ++ l1 ++ l2 ++ l3).length + 2) (sweepInitStoreScratch h8 slSource rClk) := by
    have h' : Placed code (entry + (l0 ++ l1 ++ l2 ++ l3).length)
        ([.storeData rClk rZero, .add rClk rClk rStack] ++ sweepInitStoreScratch h8 slSource rClk) := hpl4
    simpa [Nat.add_assoc] using placed_append_right h'
  obtain ⟨s4, st4s, pc4, dSrc, fr4s, k4s⟩ :=
    sweepInitStoreScratch_steps h8 slSource rClk (by decide) (by decide)
      (scratch_lt_workCap30 hWork hn (by decide))
      (by rw [pc4b, hpc4a]) hpl4s
      (by simp only [List.length_append]; rw [hl4] at hszTotal; omega)
      (by rw [k4b _ (by decide), k4a rOne, h3_one])
  -- Segment 5: `slIdx <- 0`
  have hpc4 : s4.pc = entry + (l0 ++ l1 ++ l2 ++ l3 ++ l4).length := by
    simp only [List.length_append, Nat.add_assoc] at pc4 ⊢; rw [pc4, hl4]
  have h4_zero : (reg s4 rZero).val = 0 := by rw [k4s _ (by decide), k4b _ (by decide), k4a _, h3_zero]
  have h4_one : (reg s4 rOne).val = 1 := by rw [k4s _ (by decide), k4b _ (by decide), k4a _, h3_one]
  have hl5 : l5.length = (sweepInitStoreScratch (bits := bits) h8 slIdx rZero).length := rfl
  obtain ⟨s5, st5, pc5, dIdx, fr5, k5⟩ :=
    sweepInitStoreScratch_steps h8 slIdx rZero (by decide) (by decide)
      (scratch_lt_workCap30 hWork hn (by decide))
      hpc4 hpl5 (by simp only [List.length_append]; rw [← hl5]; omega) h4_one
  -- Segment 6: `.mov rPtr rZero`
  have hpc5 : s5.pc = entry + (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5).length := pc5
  have hl6 : l6.length = 1 := rfl
  obtain ⟨s6, st6, pc6, r6, k6, d6⟩ :=
    step_mov_at (input := input) (s := s5) (placed_fetch hpl6 (i := 0) rfl hpc5)
      (by rw [hpc5]; simp only [List.length_append]; rw [hl6] at hszTotal; omega)
  -- Assemble Steps and facts
  have hsteps0 : Steps code input l0.length s s0 := by
    rw [hl0]
    exact .cons st0a (.cons st0b (.cons st0c (.cons st0d (.cons st0e (.cons st0f (.cons st0g (.cons st0h st0s)))))))
  have hsteps4 : Steps code input l4.length s3 s4 := by
    rw [hl4]; exact .cons st4a (.cons st4b st4s)
  have hsteps6 : Steps code input l6.length s5 s6 := .cons st6 (.zero _)
  have hstepsAll : Steps code input (p0bPart2 h8).length s s6 := by
    have hl : (p0bPart2 h8).length =
        l0.length + l1.length + l2.length + l3.length + l4.length + l5.length + l6.length := by
      simp only [hp, List.length_append]
    rw [hl]
    exact (((((hsteps0.append st1).append st2).append st3).append hsteps4).append st5).append hsteps6
  have h6dt : s6.data = s5.data := d6
  have h5dt : ∀ j, j ≠ slIdx → s5.data[j]? = s4.data[j]? := fr5
  have h4dt : ∀ j, j ≠ slSource → j ≠ parentsBase n m → s4.data[j]? = s3.data[j]? := by
    intro j hj1 hj2
    rw [fr4s j hj1, d4b, d4a, array_set_getElem?_ne _ _ _ _ _ (by rw [hr3_clk]; exact hj2)]
  have h0dt : ∀ j, j ≠ slBackFst → j ≠ jumpBase n m → j ≠ jumpBase n m + 1 → j ≠ jumpBase n m + 2 →
      s0.data[j]? = s.data[j]? := by
    intro j hj1 hj2 hj3 hj4
    rw [fr0s j hj1, d0h, d0g, d0f, d0e, array_set_getElem?_ne _ _ _ _ _ (by rw [h0d_tout]; exact hj4),
        d0d, d0c, array_set_getElem?_ne _ _ _ _ _ (by rw [h0b_tout]; exact hj3),
        d0b, d0a, array_set_getElem?_ne _ _ _ _ _ (by rw [hrClk]; exact hj2)]
  have hScrLtJump : ∀ sl, sl < 19 → sl < jumpBase n m := fun sl hsl => by
    simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
      predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
    omega
  have hjLt : jumpBase n m + 2 < parentsBase n m := by
    simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase]; omega
  have hScrLtPar : ∀ sl, sl < 19 → sl ≠ parentsBase n m := fun sl hsl => by
    have := hScrLtJump sl hsl; omega
  refine ⟨s6, hstepsAll, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hl : (p0bPart2 h8).length =
        (l0 ++ l1 ++ l2 ++ l3 ++ l4 ++ l5).length + 1 := by
      simp only [hp, List.length_append, l6, List.length_cons, List.length_nil]
    rw [pc6, hpc5, hl]; omega
  · rw [k6 _ (by decide), k5 _ (by decide), h4_zero]
  · rw [k6 _ (by decide), k5 _ (by decide), h4_one]
  · rw [k6 _ (by decide), k5 _ (by decide), k4s _ (by decide), k4b _ (by decide), k4a _, h3_val]
  · rw [k6 _ (by decide), k5 _ (by decide), k4s _ (by decide), k4b _ (by decide), k4a _, h3_stk]
  · rw [k6 _ (by decide), k5 _ (by decide), k4s _ (by decide), k4b _ (by decide), k4a _,
        k3 _ (by decide) (by decide) (by decide), k2 _ (by decide) (by decide) (by decide), hr1_tin]
  · rw [k6 _ (by decide), k5 _ (by decide), k4s _ (by decide), k4b _ (by decide), k4a _,
        k3 _ (by decide) (by decide) (by decide), hr2_tout]
  · rw [k6 _ (by decide), k5 _ (by decide), k4s _ (by decide), k4b _ (by decide), k4a _, hr3_off]
  · rw [r6, k5 _ (by decide), h4_zero]
  · rw [h6dt, h5dt _ (by decide), h4dt _ (by decide) (hScrLtPar _ (by decide)), fr3 _ (by decide), fr2 _ (by decide),
        fr1 _ (by decide), dBF, h0h_clk]
  · rw [h6dt, h5dt _ (by decide), h4dt _ (by decide) (hScrLtPar _ (by decide)), fr3 _ (by decide), fr2 _ (by decide),
        dBS, ← r1_clk, hr1_clk]
  · rw [h6dt, h5dt _ (by decide), h4dt _ (by decide) (hScrLtPar _ (by decide)), fr3 _ (by decide), dLab, ← r2_clk, hr2_clk]
  · rw [h6dt, h5dt _ (by decide), h4dt _ (by decide) (hScrLtPar _ (by decide)), dPar, ← r3_clk, hr3_clk]
  · rw [h6dt, h5dt _ (by decide), dSrc, h4b_clk]
  · rw [h6dt, dIdx, h4_zero]
  · have hjNe : ∀ sl, sl < 19 → sl ≠ jumpBase n m := fun sl hsl => by
      have := hScrLtJump sl hsl; omega
    have hset : s0a.data[(reg s rClk).val]? = some (reg s rZero) := by
      rw [d0a]; exact Array.getElem?_set_self (by
        rw [s.data_size, hrClk]; change _ < workCap
        simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
        omega)
    rw [hrClk] at hset
    rw [h6dt, h5dt _ (hjNe slIdx (by decide)).symm,
        h4dt _ (hjNe slSource (by decide)).symm (by have := hScrLtPar (jumpBase n m); omega),
        fr3 _ (hjNe slParents (by decide)).symm, fr2 _ (hjNe slLabels (by decide)).symm,
        fr1 _ (hjNe slBackSnd (by decide)).symm, fr0s _ (hjNe slBackFst (by decide)).symm,
        d0h, d0g, d0f, d0e,
        array_set_getElem?_ne _ _ _ _ _ (by rw [h0d_tout]; omega), d0d, d0c,
        array_set_getElem?_ne _ _ _ _ _ (by rw [h0b_tout]; omega), d0b,
        hset, Option.map_some, hrZero]
  · have hjNe : ∀ sl, sl < 19 → sl ≠ jumpBase n m + 1 := fun sl hsl => by
      have := hScrLtJump sl hsl; omega
    have hset : s0c.data[(reg s0b rTout).val]? = some (reg s0b rZero) := by
      rw [d0c]; exact Array.getElem?_set_self (by
        rw [s0b.data_size, h0b_tout]; change _ < workCap
        simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
        omega)
    rw [h0b_tout] at hset
    rw [h6dt, h5dt _ (hjNe slIdx (by decide)).symm,
        h4dt _ (hjNe slSource (by decide)).symm (by have := hjLt; omega),
        fr3 _ (hjNe slParents (by decide)).symm, fr2 _ (hjNe slLabels (by decide)).symm,
        fr1 _ (hjNe slBackSnd (by decide)).symm, fr0s _ (hjNe slBackFst (by decide)).symm,
        d0h, d0g, d0f, d0e,
        array_set_getElem?_ne _ _ _ _ _ (by rw [h0d_tout]; omega), d0d,
        hset, Option.map_some]
    rw [k0b rZero (by decide), k0a rZero, hrZero]
  · have hjNe : ∀ sl, sl < 19 → sl ≠ jumpBase n m + 2 := fun sl hsl => by
      have := hScrLtJump sl hsl; omega
    have hset : s0e.data[(reg s0d rTout).val]? = some (reg s0d rZero) := by
      rw [d0e]; exact Array.getElem?_set_self (by
        rw [s0d.data_size, h0d_tout]; change _ < workCap
        simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
          predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
        omega)
    rw [h0d_tout] at hset
    rw [h6dt, h5dt _ (hjNe slIdx (by decide)).symm,
        h4dt _ (hjNe slSource (by decide)).symm (by have := hjLt; omega),
        fr3 _ (hjNe slParents (by decide)).symm, fr2 _ (hjNe slLabels (by decide)).symm,
        fr1 _ (hjNe slBackSnd (by decide)).symm, fr0s _ (hjNe slBackFst (by decide)).symm,
        d0h, d0g, d0f, hset, Option.map_some]
    rw [k0d rZero (by decide), k0c rZero, k0b rZero (by decide), k0a rZero, hrZero]
  · have hp0 := hScrLtPar _ (by decide : slIdx < 19)
    have hp1 := hScrLtPar _ (by decide : slSource < 19)
    have hset : s4a.data[(reg s3 rClk).val]? = some (reg s3 rZero) := by
      rw [d4a]; exact Array.getElem?_set_self (by rw [s3.data_size, hr3_clk]; change _ < workCap; simp only [parentsBase, labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)
    rw [hr3_clk] at hset
    rw [h6dt, h5dt _ hp0.symm, fr4s _ hp1.symm, d4b, hset, Option.map_some, h3_zero]
  · intro j hj
    have hJ : 19 ≤ jumpBase n m := by
      simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
        predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
      omega
    have hsi : j ≠ slIdx := by unfold slIdx; rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hss : j ≠ slSource := by unfold slSource; rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hsp : j ≠ slParents := by unfold slParents; rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hsl : j ≠ slLabels := by unfold slLabels; rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hsb2 : j ≠ slBackSnd := by unfold slBackSnd; rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hsb1 : j ≠ slBackFst := by unfold slBackFst; rcases hj with h | ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
    have hneRest : j ≠ parentsBase n m ∧ j ≠ jumpBase n m ∧ j ≠ jumpBase n m + 1 ∧ j ≠ jumpBase n m + 2 := by
      rcases hj with h | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact ⟨by omega, by omega, by omega, by omega⟩
    rw [h6dt, h5dt j hsi, h4dt j hss hneRest.1, fr3 j hsp,
        fr2 j hsl, fr1 j hsb2,
        h0dt j hsb1 hneRest.2.1 hneRest.2.2.1 hneRest.2.2.2]


private theorem sweepInit_init_grounded (H : LabelledQuotient) (dictRows : Rows H)
    (large : 3 ≤ H.vertexCount) :
    Grounded (orderedConfig dictRows large) JumpForest.init
      (initial (orderedConfig dictRows large)
        (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables :=
  initial_grounded (orderedConfig dictRows large)
    (PaperB.Jumps.ConcreteInit.init_layout H.vertexCount) rfl H.vertexCount

private theorem sweepInit_work_le {bits : Nat} (h8 : 8 ≤ 2 ^ bits) {n : Nat} (hn : 3 ≤ n) :
    (sweepInitP0a (bits := bits) h8 ++ sweepInitP0b (bits := bits) h8).length +
      (7 * (n + 1) + 1) + 1 + (5 * n + 1) + 1 ≤ 120 * (n + 1) := by
  have hlP0b : (sweepInitP0b (bits := bits) h8).length ≤ 250 := by
    have hsc : ∀ sl src, (sweepInitStoreScratch (bits := bits) h8 sl src).length ≤ 12 := fun sl src => by
      simp only [sweepInitStoreScratch, List.length_append, List.length_cons, List.length_nil]
      change (immNatAux h8 rTmp rOne 5 sl).length + 1 ≤ 12
      have := immNat_length_le h8 rTmp rOne 5 sl
      omega
    rw [sweepInitP0b_eq_parts]
    simp only [p0bPart1, p0bPart2, List.length_append, List.length_cons, List.length_nil]
    have h0 := hsc slOrder rClk; have h1 := hsc slRanks rClk; have h2 := hsc slRowStart rClk
    have h3 := hsc slRowEnd rClk; have h4 := hsc slPredBuf rClk; have h5 := hsc slDictBase rClk
    have h6 := hsc slDictCnt rCnt; have h7 := hsc slDictSnd rTin; have h8' := hsc slDictSlots rTin
    have h9 := hsc slJumpBase rClk; have h10 := hsc slBackFst rClk; have h11 := hsc slBackSnd rClk
    have h12 := hsc slLabels rClk; have h13 := hsc slParents rClk; have h14 := hsc slSource rClk
    have h15 := hsc slIdx rZero
    omega
  have ha : (sweepInitP0a (bits := bits) h8).length = 21 := rfl
  simp only [List.length_append, ha]
  omega

private theorem sweepInit_init_records {bits n m workCap : Nat}
    (hCap : rawWorkCap n m ≤ workCap) (data : Array (Fin (2 ^ bits)))
    (hsz : data.size = workCap)
    (hj0 : (data[jumpBase n m + 0]?).map Fin.val = some 0)
    (hj1 : (data[jumpBase n m + 1]?).map Fin.val = some 0)
    (hj2 : (data[jumpBase n m + 2]?).map Fin.val = some 0) :
    PaperB.RamForestProgram.DepthSeek.Records (jumpBase n m) JumpForest.init data := by
  refine ⟨ValidJumpForest.init, ?_, ?_, ?_, ?_⟩
  · rw [hsz]
    have hinitSz : JumpForest.init.size = 1 := rfl
    rw [hinitSz]
    have hC : 32 * n + 7 * m + 17 ≤ workCap := hCap
    unfold jumpBase dictBase candSndBBase candFstBBase candSndABase candFstABase
      predBufBase rowEndBase rowStartBase ranksBase orderBase stampsBase indegBase csrArenaWords
    omega
  · intro u hu
    have hu0 : u = 0 := by simp only [JumpForest.init, JumpForest.size, List.length_singleton] at hu; omega
    subst u; exact hj0
  · intro u hu
    have hu0 : u = 0 := by simp only [JumpForest.init, JumpForest.size, List.length_singleton] at hu; omega
    subst u; exact hj1
  · intro u hu
    have hu0 : u = 0 := by simp only [JumpForest.init, JumpForest.size, List.length_singleton] at hu; omega
    subst u; exact hj2

private theorem sweepInit_dict_range (n m ofs : Nat) (hn : 3 ≤ n) (ho : ofs ≤ 3 * n) :
    29 ≤ dictBase n m + ofs ∧ dictBase n m + ofs < jumpBase n m := by
  simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase,
    predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]
  omega

private theorem run_sweepInit_inv {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (dictRows : Rows H) (large : 3 ≤ H.vertexCount)
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (hDictLe : (orderedConfig dictRows large).dict.size ≤ H.vertexCount)
    {s sB2 sD t : State (layout bits inputCap workCap hi hw)}
    (hStage1T : Stage1Output H t order size_order rank rows)
    (hDictHdr : (s.data[dictBase H.vertexCount H.arcCount]?).map Fin.val =
      some (orderedConfig dictRows large).dict.size)
    (hDictAt : ∀ i (hi' : i < (orderedConfig dictRows large).dict.size),
      (s.data[dictBase H.vertexCount H.arcCount + 1 + i]?).map Fin.val =
        some ((orderedConfig dictRows large).dict[i]'hi').1 ∧
      (s.data[dictBase H.vertexCount H.arcCount + 1 +
        (orderedConfig dictRows large).dict.size + i]?).map Fin.val =
        some ((orderedConfig dictRows large).dict[i]'hi').2 ∧
      (s.data[dictBase H.vertexCount H.arcCount + 1 +
        2 * (orderedConfig dictRows large).dict.size + i]?).map Fin.val = some 0)
    (hLabDisj : ∀ j, j < backFstBase H.vertexCount H.arcCount ∨
      labelsBase H.vertexCount H.arcCount + H.vertexCount ≤ j → t.data[j]? = sB2.data[j]?)
    (hPresS : ∀ j, 29 ≤ j ∧ j < jumpBase H.vertexCount H.arcCount → t.data[j]? = s.data[j]?)
    (frE : ∀ j, (∀ k, 0 ≤ k → k < H.vertexCount → j ≠ labelsBase H.vertexCount H.arcCount + k) →
      t.data[j]? = sD.data[j]?)
    (dD : sD.data = sB2.data ∨ ∃ sC : State (layout bits inputCap workCap hi hw),
      sD.data = sC.data ∧ ∀ j,
      (∀ k, 0 ≤ k → k < H.vertexCount + 1 →
        j ≠ backFstBase H.vertexCount H.arcCount + k ∧ j ≠ backSndBase H.vertexCount H.arcCount + k) →
      sC.data[j]? = sB2.data[j]?)
    (backZero : ∀ j, 0 ≤ j → j < H.vertexCount + 1 →
      (sD.data[backFstBase H.vertexCount H.arcCount + j]?).map Fin.val = some 0 ∧
      (sD.data[backSndBase H.vertexCount H.arcCount + j]?).map Fin.val = some 0)
    (labZero : ∀ j, 0 ≤ j → j < H.vertexCount →
      (t.data[labelsBase H.vertexCount H.arcCount + j]?).map Fin.val = some 0)
    (jmp0 : (sB2.data[jumpBase H.vertexCount H.arcCount + 0]?).map Fin.val = some 0)
    (jmp1 : (sB2.data[jumpBase H.vertexCount H.arcCount + 1]?).map Fin.val = some 0)
    (jmp2 : (sB2.data[jumpBase H.vertexCount H.arcCount + 2]?).map Fin.val = some 0)
    (par0 : (sB2.data[parentsBase H.vertexCount H.arcCount]?).map Fin.val = some 0)
    (tNVal : (t.data[slN]?).map Fin.val = some H.vertexCount)
    (tRootVal : (t.data[slRoot]?).map Fin.val = some H.root.val)
    (tNextVal : (t.data[slNext]?).map Fin.val = some 1)
    (tDictBaseVal : (t.data[slDictBase]?).map Fin.val = some (dictBase H.vertexCount H.arcCount))
    (tDictCntVal : (t.data[slDictCnt]?).map Fin.val = some (orderedConfig dictRows large).dict.size)
    (tDictSndVal : (t.data[slDictSnd]?).map Fin.val =
      some (dictBase H.vertexCount H.arcCount + 1 + (orderedConfig dictRows large).dict.size))
    (tDictSlotsVal : (t.data[slDictSlots]?).map Fin.val =
      some (dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size))
    (tJumpVal : (t.data[slJumpBase]?).map Fin.val = some (jumpBase H.vertexCount H.arcCount))
    (tBackFstVal : (t.data[slBackFst]?).map Fin.val = some (backFstBase H.vertexCount H.arcCount))
    (tBackSndVal : (t.data[slBackSnd]?).map Fin.val = some (backSndBase H.vertexCount H.arcCount))
    (tLabelsVal : (t.data[slLabels]?).map Fin.val = some (labelsBase H.vertexCount H.arcCount))
    (tParentsVal : (t.data[slParents]?).map Fin.val = some (parentsBase H.vertexCount H.arcCount))
    (tOrderVal : (t.data[slOrder]?).map Fin.val = some (orderBase H.vertexCount H.arcCount))
    (tRanksVal : (t.data[slRanks]?).map Fin.val = some (ranksBase H.vertexCount H.arcCount))
    (tRowStartVal : (t.data[slRowStart]?).map Fin.val = some (rowStartBase H.vertexCount H.arcCount))
    (tRowEndVal : (t.data[slRowEnd]?).map Fin.val = some (rowEndBase H.vertexCount H.arcCount))
    (tPredBufVal : (t.data[slPredBuf]?).map Fin.val = some (predBufBase H.vertexCount H.arcCount))
    (tSourceVal : (t.data[slSource]?).map Fin.val = some (sourceBase H.vertexCount H.arcCount))
    (tIdxVal : (t.data[slIdx]?).map Fin.val = some 0) :
    SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
      (order := order) (size_order := size_order) (rank := rank) (large := large)
      JumpForest.init
      (initial (orderedConfig dictRows large) (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1
        H.vertexCount) 0 t := by
  let n := H.vertexCount
  let m := H.arcCount
  have hG := sweepInit_init_grounded H dictRows large
  have hPar : t.data[parentsBase n m]? = sB2.data[parentsBase n m]? := by
    rw [frE _ (fun _ _ _ => by dsimp only [n, m]; simp only [parentsBase, labelsBase]; omega)]
    rcases dD with hD | ⟨sC, hDC, hFC⟩
    · rw [hD]
    · rw [hDC]
      exact hFC (parentsBase n m) (fun _ _ _ =>
        ⟨by dsimp only [n, m]; simp only [parentsBase, labelsBase, backSndBase, backFstBase]; omega,
         by dsimp only [n, m]; simp only [parentsBase, labelsBase, backSndBase]; omega⟩)
  exact
    { idxLe := Nat.zero_le _
      sRefLabelsSize := by simp only [initial, Array.size_replicate]
      sRefNextLe := by change 1 ≤ 0 + 1; omega
      labelsLt := fun v => by
        change ((initial (orderedConfig dictRows large)
          (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).labels[v.val]?).getD 0 < 1
        simp [initial, v.isLt]
      backPos := fun k hk1 hk2 => by
        change k < 1 at hk2; omega
      grounded := hG
      stage1 := hStage1T
      slNVal := tNVal
      slRootVal := tRootVal
      slNextVal := tNextVal
      slDictBaseVal := tDictBaseVal
      slDictCntVal := tDictCntVal
      slDictSndVal := tDictSndVal
      slDictSlotsVal := tDictSlotsVal
      slJumpVal := tJumpVal
      slBackFstVal := tBackFstVal
      slBackSndVal := tBackSndVal
      slLabelsVal := tLabelsVal
      slParentsVal := tParentsVal
      slOrderVal := tOrderVal
      slRanksVal := tRanksVal
      slRowStartVal := tRowStartVal
      slRowEndVal := tRowEndVal
      slPredBufVal := tPredBufVal
      slSourceVal := tSourceVal
      slIdxVal := tIdxVal
      records := sweepInit_init_records hCap t.data t.data_size
        (by rw [hLabDisj (jumpBase n m + 0) (Or.inl (by dsimp only [n, m]; simp only [backFstBase]; omega))]; exact jmp0)
        (by rw [hLabDisj (jumpBase n m + 1) (Or.inl (by dsimp only [n, m]; simp only [backFstBase]; omega))]; exact jmp1)
        (by rw [hLabDisj (jumpBase n m + 2) (Or.inl (by dsimp only [n, m]; simp only [backFstBase]; omega))]; exact jmp2)
      dictHeader := by
        rw [hPresS _ (by simpa only [Nat.add_zero] using sweepInit_dict_range n m 0 large (Nat.zero_le _))]
        exact hDictHdr
      dictKeys := fun i hi' => by
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le hi' hDictLe
        constructor
        · rw [hPresS _ (by simpa only [Nat.add_assoc] using sweepInit_dict_range n m (1 + i) large (by omega))]
          exact (hDictAt i hi').1
        · rw [hPresS _ (by simpa only [Nat.add_assoc] using sweepInit_dict_range n m (1 + (orderedConfig dictRows large).dict.size + i) large (by omega))]
          exact (hDictAt i hi').2.1
      dictSlots := fun i hi' => by
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le hi' hDictLe
        rw [hPresS _ (by simpa only [Nat.add_assoc] using sweepInit_dict_range n m (1 + 2 * (orderedConfig dictRows large).dict.size + i) large (by omega))]
        have hzero : (initial (orderedConfig dictRows large)
            (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables.slotAt i = 0 := by
          simp only [initial, _root_.EX24.Tables.slotAt, Array.getElem?_replicate, hi']
          rfl
        rw [hzero]
        exact (hDictAt i hi').2.2
      backMem := fun k hk => by
        have hnone : encodeBackPair ((initial (orderedConfig dictRows large)
            (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables.back[k]?.join) = (0, 0) := by
          have hb : (initial (orderedConfig dictRows large)
              (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables.back[k]?.join = none := by
            simp only [initial, Array.getElem?_replicate]
            split <;> rfl
          rw [hb]; rfl
        rw [hnone]
        constructor
        · rw [frE _ (fun _ _ _ => by simp only [labelsBase, backSndBase, backFstBase]; omega)]
          exact (backZero k (Nat.zero_le k) (by omega)).1
        · rw [frE _ (fun _ _ _ => by simp only [labelsBase, backSndBase]; omega)]
          exact (backZero k (Nat.zero_le k) (by omega)).2
      labelsMem := fun v => by
        have hv : (initial (orderedConfig dictRows large)
            (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).labelAt v.val = 0 := by
          simp only [initial, _root_.EX24.State.labelAt, Array.getElem?_replicate, v.isLt]
          rfl
        rw [hv]
        exact labZero v.val (Nat.zero_le _) v.isLt
      parentsMem := fun u hu => by
        have hu0 : u = 0 := by simp only [JumpForest.init, JumpForest.size, List.length_singleton] at hu; omega
        subst u
        have hp0 : JumpForest.init.parentOf 0 = 0 := rfl
        rw [Nat.add_zero, hp0, hPar]
        exact par0 }

theorem run_sweepInit {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (input : Input (layout bits inputCap workCap hi hw))
    (hRaw : RawQuotientInput input H)
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (dictRows : Rows H) (large : 3 ≤ H.vertexCount)
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    {s : State (layout bits inputCap workCap hi hw)}
    (dso : DictSortOutput H s order size_order rank rows (Nat.le_trans hCap hw)) :
    ∃ t : State (layout bits inputCap workCap hi hw),
    ∃ states : List (State (layout bits inputCap workCap hi hw)),
    ∃ work : Nat,
      work ≤ 120 * (H.vertexCount + 1) ∧
      run (sweepInitPhase hi hw h8).code input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace (sweepInitPhase hi hw h8).code input (Phase.initial s) states ⟨t, work⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 ∧
      t.pc = (sweepInitPhase hi hw h8).haltPC ∧
      (reg t rZero).val = 0 ∧
      (reg t rOne).val = 1 ∧
      SweepInv (hi := hi) (hw := hw) H (rows := rows) (dictRows := dictRows)
        (order := order) (size_order := size_order) (rank := rank) (large := large)
        JumpForest.init
        (initial (orderedConfig dictRows large) (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1
          H.vertexCount) 0 t := by
  let ph := sweepInitPhase hi hw h8
  let n := H.vertexCount
  let m := H.arcCount
  have hBound : rawWorkCap n m ≤ workCap := hCap
  have hDictLe : (orderedConfig dictRows large).dict.size ≤ n := dict_size_le H dictRows large
  obtain ⟨hDictHdr, hDictAt⟩ := dictSortOutput_fields dso dictRows large
  let p0 := sweepInitP0a (bits := bits) h8 ++ sweepInitP0b (bits := bits) h8
  let l1 := p0.length
  let loop := sweepInitLoop (bits := bits) l1
  have hBody : sweepInitBody (bits := bits) h8 = p0 ++ loop := rfl
  have hplBody : Placed ph.code 0 (sweepInitBody h8) :=
    placed_of_phase_body (sweepInitBody h8) (sweepInitBody_nonHalt h8)
  have hplP0 : Placed ph.code 0 p0 := placed_append_left (by simpa only [hBody] using hplBody)
  have hplP0a : Placed ph.code 0 (sweepInitP0a h8) := placed_append_left hplP0
  have hplP0b : Placed ph.code 21 (sweepInitP0b h8) := placed_append_right hplP0
  have hplP0bParts : Placed ph.code 21 (p0bPart1 h8 ++ p0bPart2 h8) := by
    rwa [← sweepInitP0b_eq_parts]
  have hplP0b1 : Placed ph.code 21 (p0bPart1 h8) := placed_append_left hplP0bParts
  have hplP0b2 : Placed ph.code (21 + (p0bPart1 h8).length) (p0bPart2 h8) :=
    placed_append_right hplP0bParts
  have hplLoop : Placed ph.code l1 loop := placed_append_right (by simpa only [hBody] using hplBody)
  have hCodeSz : ph.code.size = (sweepInitBody h8).length + 1 := by
    simp [ph, sweepInitPhase, mkPhase, Phase.ofLast]
  have hBodyLen : (sweepInitBody h8).length = 21 + (p0bPart1 h8).length + (p0bPart2 h8).length + loop.length := by
    simp only [hBody, p0, List.length_append, sweepInitP0b_eq_parts]
    have ha : (sweepInitP0a (bits := bits) h8).length = 21 := rfl
    omega
  have hLoopLen : loop.length = 13 := rfl
  have hL1Eq : l1 = 21 + (p0bPart1 h8).length + (p0bPart2 h8).length := by
    simp only [l1, p0, List.length_append, sweepInitP0b_eq_parts]
    have ha : (sweepInitP0a (bits := bits) h8).length = 21 := rfl
    omega
  -- Run `sweepInitP0a`, `p0bPart1`, `p0bPart2`
  obtain ⟨sA, stA, pcA, zA, oA, vA, rA, stkA, clkA, slNA, slRA, slNxA, frA⟩ :=
    sweepInitP0a_steps h8 H hRaw hCap (Phase.initial s) rfl hplP0a (by rw [hCodeSz, hBodyLen]; omega)
  obtain ⟨sB1, stB1, pcB1, zB1, oB1, vB1, stkB1, clkB1,
      slOrd, slRnk, slRS, slRE, slPB, slDB, slDC, slDS, slDSl, slJB, frB1⟩ :=
    p0bPart1_steps h8 n m (orderedConfig dictRows large).dict.size large hCap hDictLe sA pcA hplP0b1
      (by rw [hCodeSz, hBodyLen]; omega) zA oA vA rA stkA clkA
      (by rw [frA _ (by simp [dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase, csrArenaWords]; omega)]; exact hDictHdr)
  obtain ⟨sB2, stB2, pcB2, zB2, oB2, vB2, stkB2, tinB2, toutB2, offB2, ptrB2,
      slBF, slBS, slLab, slPar, slSrc, slIdx2, jmp0, jmp1, jmp2, par0, frB2⟩ :=
    p0bPart2_steps h8 n m large hCap sB1 pcB1 hplP0b2 (by rw [hCodeSz, hBodyLen]; omega)
      zB1 oB1 vB1 stkB1 clkB1
  -- Run `zeroBack` (`l1 .. l1+7`) and `resetPtr` (`l1+7`) and `zeroLabels` (`l1+8 .. l1+13`)
  have hBackBnd : backSndBase n m + (n + 1) ≤ workCap := by
    simp only [backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase,
      candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase, stampsBase, indegBase,
      csrArenaWords]; change 32 * n + 7 * m + 17 ≤ workCap at hCap; omega
  have hBackDisj : backFstBase n m + (n + 1) ≤ backSndBase n m := by
    simp only [backSndBase, backFstBase]; omega
  obtain ⟨sC, stC, pcC, backZero, frC, kC⟩ :=
    zeroBack_steps l1 (backFstBase n m) (backSndBase n m) n hBackBnd hBackDisj
      (n + 1) 0 sB2 (Nat.zero_add _) (by rw [pcB2, hL1Eq]) ptrB2 stkB2 tinB2 toutB2 zB2 oB2
      (hplLoop 0 _ rfl) (hplLoop 1 _ rfl) (hplLoop 2 _ rfl) (hplLoop 3 _ rfl)
      (hplLoop 4 _ rfl) (hplLoop 5 _ rfl) (hplLoop 6 _ rfl) (by rw [hCodeSz, hBodyLen, hL1Eq]; omega)
  obtain ⟨sD, stD, pcD, rD, kD, dD⟩ :=
    step_mov_at (input := input) (by rw [pcC]; exact hplLoop 7 _ rfl) (by rw [pcC, hCodeSz, hBodyLen, hL1Eq]; omega)
  have hLabBnd : labelsBase n m + n < workCap := by
    simp only [labelsBase, backSndBase, backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
      stampsBase, indegBase, csrArenaWords]; change 32 * n + 7 * m + 17 ≤ workCap at hCap; omega
  obtain ⟨t, stE, pcE, labZero, frE, kE⟩ :=
    zeroLabels_steps (l1 + 8) (labelsBase n m) n hLabBnd n 0 sD (Nat.zero_add _)
      (by rw [pcD, pcC]) (by rw [rD, kC _ (by decide) (by decide), zB2])
      (by rw [kD _ (by decide), kC _ (by decide) (by decide), vB2])
      (by rw [kD _ (by decide), kC _ (by decide) (by decide), offB2])
      (by rw [kD _ (by decide), kC _ (by decide) (by decide), zB2])
      (by rw [kD _ (by decide), kC _ (by decide) (by decide), oB2])
      (hplLoop 8 _ rfl) (hplLoop 9 _ rfl) (hplLoop 10 _ rfl) (hplLoop 11 _ rfl)
      (hplLoop 12 _ rfl) (by rw [hCodeSz, hBodyLen, hL1Eq]; omega)
  have htpc : t.pc = ph.haltPC := by
    have hhalt : ph.haltPC = (sweepInitBody h8).length := rfl
    rw [pcE, hhalt, hBodyLen, hL1Eq, hLoopLen]
  let workSteps := l1 + (7 * (n + 1) + 1) + 1 + (5 * n + 1)
  have hStepsAll : Steps ph.code input workSteps (Phase.initial s) t := by
    have hp0Len : l1 = 21 + (p0bPart1 h8).length + (p0bPart2 h8).length := hL1Eq
    have hstP0 : Steps ph.code input l1 (Phase.initial s) sB2 := by
      rw [hp0Len]; exact (stA.append stB1).append stB2
    exact ((hstP0.append stC).append (.cons stD (.zero _))).append stE
  have hWorkLe : workSteps + 1 ≤ 120 * (H.vertexCount + 1) :=
    sweepInit_work_le h8 large
  have hRun : run ph.code input (workSteps + 1) (Phase.initial s) = some ⟨t, workSteps + 1⟩ := by
    have hh : ph.code[t.pc]? = some .halt := htpc ▸ ph.haltAt
    exact hStepsAll.halts (step_halt_at hh)
  obtain ⟨states, ok⟩ := run_has_successfulTrace hRun
  have hzT : (reg t rZero).val = 0 := by
    rw [kE _ (by decide) (by decide), kD _ (by decide), kC _ (by decide) (by decide), zB2]
  have hoT : (reg t rOne).val = 1 := by
    rw [kE _ (by decide) (by decide), kD _ (by decide), kC _ (by decide) (by decide), oB2]
  -- Frame `t.data` vs `sB2.data`: preserved outside `[backFstBase, labelsBase + n)`
  have hLabDisj : ∀ j, j < backFstBase n m ∨ labelsBase n m + n ≤ j → t.data[j]? = sB2.data[j]? := by
    intro j hj
    have hjLab : ∀ k, 0 ≤ k → k < n → j ≠ labelsBase n m + k := fun k hk1 hk2 => by
      rcases hj with h | h
      · have hbf : backFstBase n m ≤ labelsBase n m := by
          simp only [labelsBase, backSndBase]; omega
        omega
      · omega
    have hjBack : ∀ k, 0 ≤ k → k < n + 1 → j ≠ backFstBase n m + k ∧ j ≠ backSndBase n m + k :=
      fun k hk1 hk2 => by
        rcases hj with h | h
        · have hbs : backFstBase n m ≤ backSndBase n m := by simp only [backSndBase]; omega
          exact ⟨by omega, by omega⟩
        · have hlb : backSndBase n m + (n + 1) ≤ labelsBase n m := by simp only [labelsBase]; omega
          have hbs : backFstBase n m + (n + 1) ≤ backSndBase n m := by simp only [backSndBase]; omega
          exact ⟨by omega, by omega⟩
    rw [frE j hjLab, dD, frC j hjBack]
  have hPresS : ∀ j, (29 ≤ j ∧ j < jumpBase H.vertexCount H.arcCount) → t.data[j]? = s.data[j]? := by
    intro j ⟨hj1, hj2⟩
    dsimp only [n, m] at hLabDisj frB2 frB1 frA
    have hjBF : j < backFstBase H.vertexCount H.arcCount := by
      simp only [backFstBase] at *; omega
    rw [hLabDisj j (Or.inl hjBF), frB2 j (by omega), frB1 j (by omega), frA j (by omega)]
    rfl
  have hStage1T : Stage1Output H t order size_order rank rows :=
    stage1_frame_data dso.stage1 (fun j ⟨h1, h2⟩ => hPresS j ⟨by
      simp only [orderBase, stampsBase, indegBase, csrArenaWords] at h1; omega,
      by simp only [jumpBase, dictBase, candSndBBase, candFstBBase, candSndABase, candFstABase] at h2 ⊢; omega⟩)
  have hLabLt : 19 ≤ backFstBase n m := by
    simp only [backFstBase, jumpBase, dictBase, candSndBBase, candFstBBase,
      candSndABase, candFstABase, predBufBase, rowEndBase, rowStartBase, ranksBase, orderBase,
      stampsBase, indegBase, csrArenaWords]; omega
  have hScr : ∀ j, j < 19 → j < backFstBase n m := fun j hj => by omega
  have hScrB1 : ∀ j, j < 3 ∨ (17 ≤ j ∧ j < 19) → j < 3 ∨ 17 ≤ j := fun j hj => by
    rcases hj with h | ⟨h1, _⟩; exact Or.inl h; exact Or.inr h1
  have hScrB2 : ∀ j, j < 8 ∨ (12 ≤ j ∧ j < 17) →
      j < 8 ∨ (12 ≤ j ∧ j < 17) ∨ (19 ≤ j ∧ j < jumpBase H.vertexCount H.arcCount) :=
    fun j hj => by rcases hj with h | h; exact Or.inl h; exact Or.inr (Or.inl h)
  have tNVal : (t.data[slN]?).map Fin.val = some H.vertexCount := by
    rw [hLabDisj slN (Or.inl (hScr _ (by decide))), frB2 slN (hScrB2 _ (by decide)), frB1 slN (hScrB1 _ (by decide))]; exact slNA
  have tRootVal : (t.data[slRoot]?).map Fin.val = some H.root.val := by
    rw [hLabDisj slRoot (Or.inl (hScr _ (by decide))), frB2 slRoot (hScrB2 _ (by decide)), frB1 slRoot (hScrB1 _ (by decide))]; exact slRA
  have tNextVal : (t.data[slNext]?).map Fin.val = some 1 := by
    rw [hLabDisj slNext (Or.inl (hScr _ (by decide))), frB2 slNext (hScrB2 _ (by decide)), frB1 slNext (hScrB1 _ (by decide))]; exact slNxA
  have tDictBaseVal : (t.data[slDictBase]?).map Fin.val = some (dictBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slDictBase (Or.inl (hScr _ (by decide))), frB2 slDictBase (hScrB2 _ (by decide))]; exact slDB
  have tDictCntVal : (t.data[slDictCnt]?).map Fin.val = some (orderedConfig dictRows large).dict.size := by
    rw [hLabDisj slDictCnt (Or.inl (hScr _ (by decide))), frB2 slDictCnt (hScrB2 _ (by decide))]; exact slDC
  have tDictSndVal : (t.data[slDictSnd]?).map Fin.val =
      some (dictBase H.vertexCount H.arcCount + 1 + (orderedConfig dictRows large).dict.size) := by
    rw [hLabDisj slDictSnd (Or.inl (hScr _ (by decide))), frB2 slDictSnd (hScrB2 _ (by decide))]; exact slDS
  have tDictSlotsVal : (t.data[slDictSlots]?).map Fin.val =
      some (dictBase H.vertexCount H.arcCount + 1 + 2 * (orderedConfig dictRows large).dict.size) := by
    rw [hLabDisj slDictSlots (Or.inl (hScr _ (by decide))), frB2 slDictSlots (hScrB2 _ (by decide))]; exact slDSl
  have tJumpVal : (t.data[slJumpBase]?).map Fin.val = some (jumpBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slJumpBase (Or.inl (hScr _ (by decide))), frB2 slJumpBase (hScrB2 _ (by decide))]; exact slJB
  have tBackFstVal : (t.data[slBackFst]?).map Fin.val = some (backFstBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slBackFst (Or.inl (hScr _ (by decide)))]; exact slBF
  have tBackSndVal : (t.data[slBackSnd]?).map Fin.val = some (backSndBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slBackSnd (Or.inl (hScr _ (by decide)))]; exact slBS
  have tLabelsVal : (t.data[slLabels]?).map Fin.val = some (labelsBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slLabels (Or.inl (hScr _ (by decide)))]; exact slLab
  have tParentsVal : (t.data[slParents]?).map Fin.val = some (parentsBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slParents (Or.inl (hScr _ (by decide)))]; exact slPar
  have tOrderVal : (t.data[slOrder]?).map Fin.val = some (orderBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slOrder (Or.inl (hScr _ (by decide))), frB2 slOrder (hScrB2 _ (by decide))]; exact slOrd
  have tRanksVal : (t.data[slRanks]?).map Fin.val = some (ranksBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slRanks (Or.inl (hScr _ (by decide))), frB2 slRanks (hScrB2 _ (by decide))]; exact slRnk
  have tRowStartVal : (t.data[slRowStart]?).map Fin.val = some (rowStartBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slRowStart (Or.inl (hScr _ (by decide))), frB2 slRowStart (hScrB2 _ (by decide))]; exact slRS
  have tRowEndVal : (t.data[slRowEnd]?).map Fin.val = some (rowEndBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slRowEnd (Or.inl (hScr _ (by decide))), frB2 slRowEnd (hScrB2 _ (by decide))]; exact slRE
  have tPredBufVal : (t.data[slPredBuf]?).map Fin.val = some (predBufBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slPredBuf (Or.inl (hScr _ (by decide))), frB2 slPredBuf (hScrB2 _ (by decide))]; exact slPB
  have tSourceVal : (t.data[slSource]?).map Fin.val = some (sourceBase H.vertexCount H.arcCount) := by
    rw [hLabDisj slSource (Or.inl (hScr _ (by decide)))]; exact slSrc
  have tIdxVal : (t.data[slIdx]?).map Fin.val = some 0 := by
    rw [hLabDisj slIdx (Or.inl (hScr _ (by decide)))]; exact slIdx2
  exact ⟨t, states, workSteps + 1, hWorkLe, hRun, ok, ok.peak_eq, htpc, hzT, hoT,
    run_sweepInit_inv H dictRows large hCap hDictLe hStage1T hDictHdr hDictAt
      hLabDisj hPresS frE (Or.inr ⟨sC, dD, frC⟩)
      (fun j hj1 hj2 => by rw [dD]; exact backZero j hj1 hj2) labZero jmp0 jmp1 jmp2 par0
      tNVal tRootVal tNextVal tDictBaseVal tDictCntVal tDictSndVal tDictSlotsVal
      tJumpVal tBackFstVal tBackSndVal tLabelsVal tParentsVal tOrderVal tRanksVal
      tRowStartVal tRowEndVal tPredBufVal tSourceVal tIdxVal⟩

end SweepInitExec

end PaperB.RamForestProgram.Sweep
