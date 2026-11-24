module

public import PaperB.RamForestRawInterface
public import PaperB.SmallQuotient
public import PaperB.ForestOrderRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Small-quotient (`H.vertexCount < 3`) RAM/word constructor, serialized Lemma 3.2
lookup operations (`O(L)` pair lookup and `O(1)` known-node membership), and
independent case checks (small quotients, parallel arcs, repeated keys, and
memory-layout bounds).
-/

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.ForestSlimIndex
open PaperB.Machine (Word)
open PaperB.WordOps (zero)
open PaperB.RamProgram
open _root_.EX24.PreparedSweep

private def localStartPair {bits cap : Nat} (fit : cap ≤ 2 ^ bits)
    (a size b x y : Word bits) : RamProgram.State (ThreeCalls.layout bits cap fit) where
  regs := Array.ofFn fun i : Fin 16 =>
    if i = 7 then a else if i = 8 then size else if i = 9 then b
    else if i = 11 then x else if i = 12 then y else zero bits
  data := #[]
  pc := 0
  regs_size := by simp
  data_size := rfl

private def localSlotProbed {bits : Nat} (dict : Array (Word bits)) (i : Nat) :
    Nat × Nat :=
  CountedProbe.bindC (CountedProbe.read dict 0) fun header =>
    let base := FlatPairDictionary.slotBase ((header.map Fin.val).getD 0)
    if i < dict.size - base then
      CountedProbe.mapC (fun x => (x.map Fin.val).getD 0)
        (CountedProbe.read dict (base + i))
    else (0, 0)

private theorem localSlotProbed_spec {bits : Nat} (dict : Array (Word bits))
    (valid : FlatPairDictionary.Valid dict) (i : Nat) :
    (localSlotProbed dict i).1 = FlatPairDictionary.slotAt dict valid i ∧
      (localSlotProbed dict i).2 ≤ 2 := by
  unfold localSlotProbed CountedProbe.bindC CountedProbe.read CountedProbe.mapC
  unfold FlatPairDictionary.slotAt
  let base := FlatPairDictionary.slotBase (FlatPairDictionary.rowCount dict)
  have hb : base ≤ dict.size := valid.keysWithin
  change ((if i < dict.size - base then (((dict[base + i]?).map Fin.val).getD 0, 1)
      else (0, 0)).1 = _) ∧
    1 + (if i < dict.size - base then (((dict[base + i]?).map Fin.val).getD 0, 1)
      else (0, 0)).2 ≤ 2
  by_cases hi : i < dict.size - base
  · have hpos : base + i < dict.size := by omega
    have hi' : i < (FlatPairDictionary.slotSlice dict valid).len := hi
    rw [dite_eq_left hi', ite_eq_left hi]
    simp only [getElem?_pos dict (base + i) hpos, Option.map_some, Option.getD_some]
    exact ⟨rfl, by decide⟩
  · have hi' : ¬ i < (FlatPairDictionary.slotSlice dict valid).len := hi
    simp [hi, hi']

private def localBackProbed {bits : Nat} (w : BackWords bits) (i : Nat) :
    Option (Nat × Nat) × Nat :=
  CountedProbe.bindC (CountedProbe.read w.tagAndFirst i) fun a =>
    match a with
    | none => (none, 0)
    | some x =>
      CountedProbe.mapC (fun b => b.map fun y => (x.val, y.val))
        (CountedProbe.read w.second i)

private theorem localBackProbed_spec {bits : Nat} (w : BackWords bits) (i : Nat) :
    (localBackProbed w i).1 = w.read i ∧ (localBackProbed w i).2 ≤ 2 := by
  unfold localBackProbed BackWords.read CountedProbe.bindC CountedProbe.read CountedProbe.mapC
  cases w.tagAndFirst[i]? <;> simp

/-- Check a dictionary hit using only the retained slot and back-key arrays,
without querying `entry`/`stop`. Returns `some a` if `(x, y)` maps to nonzero
forest node `a` whose stored reverse key matches `(x.val + 1, y.val)`. -/
def WordColumns.checkHitSlotProbed {bits : Nat} (w : WordColumns bits)
    (hit : Option Nat) (key : Nat × Nat) : Option Nat × Nat :=
  match hit with
  | none => (none, 0)
  | some i =>
    CountedProbe.bindC (localSlotProbed w.dictionary i) fun a =>
      if a = 0 then (none, 0) else
      CountedProbe.mapC (fun stored => if stored = some key then some a else none)
        (localBackProbed w.back a)

theorem WordColumns.checkHitSlotProbed_spec {bits : Nat} (w : WordColumns bits)
    (valid : FlatPairDictionary.Valid w.dictionary) (hit : Option Nat)
    (key : Nat × Nat) :
    (w.checkHitSlotProbed hit key).2 ≤ 4 ∧
    (∀ v : Nat,
      w.afterHit valid hit key v =
        match (w.checkHitSlotProbed hit key).1 with
        | none => false
        | some a => w.known a v) := by
  cases hit with
  | none =>
    simp [WordColumns.checkHitSlotProbed, WordColumns.afterHit]
  | some i =>
    obtain ⟨slotValue, slotCost⟩ := localSlotProbed_spec w.dictionary valid i
    simp only [WordColumns.checkHitSlotProbed, WordColumns.afterHit,
      CountedProbe.bindC, CountedProbe.mapC]
    rw [slotValue]
    generalize FlatPairDictionary.slotAt w.dictionary valid i = a
    by_cases hzero : a = 0
    · simp only [hzero, ite_true]
      refine ⟨by omega, fun v => ?_⟩
      simp
    · obtain ⟨backValue, backCost⟩ := localBackProbed_spec w.back a
      simp only [hzero, ite_false]
      refine ⟨by omega, fun v => ?_⟩
      by_cases eq : w.back.read a = some key <;>
        simp [hzero, eq, backValue]

/-- Pair-only lookup on the serialized index: runs the fixed `O(L)` RAM
binary search on `w.dictionary` and verifies the candidate slot and reverse key
in `≤ 5` probes, returning `Option Nat` node address `a` for subsequent
`O(1)` (`4`-probe) `WordColumns.knownProbed a v` queries. -/
def WordColumns.lookupSlotProbed {bits : Nat} (w : WordColumns bits)
    (valid : FlatPairDictionary.Valid w.dictionary) (one : 1 < 2 ^ bits)
    (fuel : Nat) (x y : Word bits) : Option (Option Nat × Nat × Nat) :=
  let fit := Nat.le_of_lt valid.capacity
  let rows := FlatPairDictionary.rowCount w.dictionary
  have hrows : FlatPairDictionary.slotBase rows ≤ w.dictionary.size := valid.keysWithin
  have hrows1 : 1 + 2 * rows ≤ w.dictionary.size := by
    change 1 + rows + rows ≤ w.dictionary.size at hrows
    omega
  let base : Word bits := ⟨FlatPairDictionary.secondBase rows, by
    have hc := valid.capacity
    change 1 + rows < 2 ^ bits
    omega⟩
  let state := localStartPair fit ⟨1, one⟩ ⟨rows, by
    have hc := valid.capacity
    omega⟩ base x y
  let input : RamProgram.Input (ThreeCalls.layout bits w.dictionary.size fit) := ⟨w.dictionary, rfl⟩
  (run (ThreeCalls.EqualityTail.checkedProgram fit one (ThreeCalls.concreteSetup bits one))
    input fuel state).map fun out =>
      let hit := if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
        then some (ThreeCalls.setupReg out.finalState 3).val else none
      let (slot?, probes) := w.checkHitSlotProbed hit (x.val + 1, y.val)
      (slot?, out.executed, 1 + probes)

theorem packWordColumns_checkHitSlotProbed_eq_checkedHit
    {H : LabelledQuotient} {p : ForestDictionary.Rows H}
    {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    [DecidableEq (CutPair H)]
    (r : OrderedReaderResult p data size_data rank large)
    {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (q : CutPair H) :
    let s := ofOrderedReader r
    let w := packWordColumns r cap
    let hit := (PairLookup.lookup s.dict (orderedPairCode q)).1
    (w.checkHitSlotProbed hit (encodeBackPair (some q))).1 = checkedHit r q := by
  intro s w hit
  let rep := packWordColumns_dictionary_represents r cap
  have hchecked : checkedHit r q =
      match hit with
      | none => none
      | some i =>
        let a := (s.slots[i]?).getD 0
        if a ≠ 0 ∧ s.back[a]? = some (some q) then some a else none := rfl
  rw [hchecked]
  cases h : hit with
  | none => rfl
  | some i =>
    obtain ⟨slotValue, _⟩ := localSlotProbed_spec w.dictionary rep.valid i
    simp only [WordColumns.checkHitSlotProbed, CountedProbe.bindC, CountedProbe.mapC]
    rw [slotValue, rep.slotAt_eq i]
    generalize (s.slots[i]?).getD 0 = a
    by_cases hzero : a = 0
    · simp [hzero]
    · obtain ⟨backValue, _⟩ := localBackProbed_spec w.back a
      have backIff :
          w.back.read a = some (encodeBackPair (some q)) ↔ s.back[a]? = some (some q) :=
        packBackWords_matches s (by omega : H.vertexCount < 2 ^ bits) a q
      simp only [hzero, ne_eq, not_false_eq_true, true_and, ite_false, backValue]
      by_cases hback : s.back[a]? = some (some q)
      · have hback' : w.back.read a = some (encodeBackPair (some q)) := backIff.mpr hback
        simp [hback, hback']
      · have hback' : w.back.read a ≠ some (encodeBackPair (some q)) :=
          fun hm => hback (backIff.mp hm)
        simp [hback, hback']

theorem packWordColumns_lookupSlotProbed_spec
    {H : LabelledQuotient} {p : ForestDictionary.Rows H}
    {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    [DecidableEq (CutPair H)]
    (r : OrderedReaderResult p data size_data rank large)
    {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (q : CutPair H) :
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    have one : 1 < 2 ^ bits := by omega
    let x : Word bits := ⟨q.fst.val, by have := q.fst.isLt; omega⟩
    let y : Word bits := ⟨q.snd.val, by have := q.snd.isLt; omega⟩
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ steps probes,
      w.lookupSlotProbed rep.valid one fuel x y =
        some (checkedHit r q, steps, probes) ∧
      steps ≤ fuel ∧ probes ≤ 5 := by
  intro w rep one x y fuel
  let s := ofOrderedReader r
  let narrow : RamProgram.Input (Predecessor.layout bits w.dictionary.size (Nat.le_of_lt rep.valid.capacity)) :=
    ⟨w.dictionary, rfl⟩
  let c := FlatPairDictionary.workerColumns narrow.words rep
  let A := FlatPairDictionary.firstSlice w.dictionary rep.valid
  let B := FlatPairDictionary.secondSlice w.dictionary rep.valid
  let fit := Nat.le_of_lt rep.valid.capacity
  have hrows : 1 + 2 * FlatPairDictionary.rowCount w.dictionary ≤ w.dictionary.size := by
    have hw := rep.valid.keysWithin
    change 1 + FlatPairDictionary.rowCount w.dictionary +
      FlatPairDictionary.rowCount w.dictionary ≤ w.dictionary.size at hw
    omega
  have hcap : w.dictionary.size < 2 ^ bits := rep.valid.capacity
  have hrowLt : FlatPairDictionary.rowCount w.dictionary < 2 ^ bits := by
    omega
  have hbaseLt : FlatPairDictionary.secondBase (FlatPairDictionary.rowCount w.dictionary) < 2 ^ bits := by
    change 1 + FlatPairDictionary.rowCount w.dictionary < 2 ^ bits
    omega
  let state := localStartPair fit ⟨1, one⟩
    ⟨FlatPairDictionary.rowCount w.dictionary, hrowLt⟩
    ⟨FlatPairDictionary.secondBase (FlatPairDictionary.rowCount w.dictionary), hbaseLt⟩ x y
  have regs (i : Fin 16) :
      ThreeCalls.setupReg state i =
        if i = 7 then A.base else if i = 8 then (⟨A.len, by have h := A.fits; omega⟩ : Word bits)
        else if i = 9 then B.base else if i = 11 then x else if i = 12 then y else zero bits := by
    unfold ThreeCalls.setupReg state localStartPair
    simp only [Array.getElem_ofFn]
    rfl
  obtain ⟨out', hrun', _, _, hhit⟩ :=
    ThreeCalls.pair_search_correct_from_pc0_with_index (i := narrow)
      (j := (⟨w.dictionary, rfl⟩ : RamProgram.Input (ThreeCalls.layout bits w.dictionary.size fit)))
      fit one c (dict_sorted r) x y rfl state rfl
      (by rw [regs]; rfl) (by rw [regs]; rfl) (by rw [regs]; rfl)
      (by rw [regs]; rfl) (by rw [regs]; rfl)
      (by rw [regs]; rfl) (by rw [regs]; rfl)
  have hsize := ofOrderedReader_dict_size_le r
  have hlog : Nat.log2 (s.dict.size + 1) ≤ Nat.log2 (H.vertexCount + 1) := by
    apply (Nat.le_log2 (by omega : H.vertexCount + 1 ≠ 0)).mpr
    exact Nat.le_trans (Nat.log2_self_le (by omega)) (Nat.add_le_add_right hsize 1)
  have wider : 33 * (Nat.log2 (s.dict.size + 1) + 1) + 39 ≤ fuel := by
    dsimp only [fuel, OracleContract.L]
    omega
  have hrun'' := run_stable_of_le wider hrun'
  let hit := if ThreeCalls.setupReg out'.finalState 0 = (⟨1, one⟩ : Word bits)
    then some (ThreeCalls.setupReg out'.finalState 3).val else none
  have hitEq : hit = (PairLookup.lookup s.dict (orderedPairCode q)).1 := by
    change _ = (PairLookup.lookup (ofOrderedReader r).dict (x.val, y.val)).1
    simpa only [hit, decide_eq_true_eq] using hhit
  obtain ⟨probeCost, _⟩ :=
    w.checkHitSlotProbed_spec rep.valid hit (encodeBackPair (some q))
  have slotEq : (w.checkHitSlotProbed hit (encodeBackPair (some q))).1 =
      checkedHit r q := by
    rw [hitEq]
    exact packWordColumns_checkHitSlotProbed_eq_checkedHit r cap q
  refine ⟨out'.executed, 1 + (w.checkHitSlotProbed hit (encodeBackPair (some q))).2,
    ?_, run_executed_le hrun'', by omega⟩
  unfold WordColumns.lookupSlotProbed
  dsimp only
  change (run (ThreeCalls.EqualityTail.checkedProgram fit one (ThreeCalls.concreteSetup bits one))
      ⟨w.dictionary, rfl⟩ fuel state).map _ = _
  rw [hrun'']
  change some ((w.checkHitSlotProbed hit (x.val + 1, y.val)).1, out'.executed, _) = _
  have keyEq : (x.val + 1, y.val) = encodeBackPair (some q) := rfl
  rw [keyEq, slotEq]

end PaperB.RetainedProperLoss

namespace PaperB.RamForestProgram.RawBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (zero add ltb)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram.Finish
open PaperB.ForestHead (Vertex)
open PaperB.RetainedProperLoss
open PaperB.ForestSlimIndex
open PaperB.SmallQuotient
open _root_.EX24.PreparedSweep

/-! ### 1. Small Quotient (`H.vertexCount < 3`) `Columns` and `WordColumns` -/

/-- Retained columns for any small quotient (`H.vertexCount < 3`): no real pairs,
only the artificial root node `0` with DFS interval `[0, 1)`. -/
def smallColumns (H : LabelledQuotient) : Columns H where
  dict := #[]
  slots := #[]
  back := #[none]
  labels := Array.replicate H.vertexCount 0
  entry := #[0]
  stop := #[1]

theorem smallColumns_fits (H : LabelledQuotient) (bits : Nat) (hbits : 1 < 2 ^ bits) :
    FlatPairDictionary.Fits bits (smallColumns H) where
  first i hi := by simp [smallColumns] at hi
  second i hi := by simp [smallColumns] at hi
  slot i hi := by simp [smallColumns] at hi
  capacity := by
    simpa [FlatPairDictionary.packedSize, FlatPairDictionary.slotBase,
      FlatPairDictionary.secondBase, smallColumns] using hbits

/-- Packed `WordColumns` representation for a small quotient (`H.vertexCount < 3`). -/
def smallWordColumns (H : LabelledQuotient) (bits : Nat) (hbits : 1 < 2 ^ bits) :
    WordColumns bits where
  dictionary := #[⟨0, Nat.two_pow_pos bits⟩]
  back := ⟨#[⟨0, Nat.two_pow_pos bits⟩], #[⟨0, Nat.two_pow_pos bits⟩]⟩
  labels := Array.replicate H.vertexCount ⟨0, Nat.two_pow_pos bits⟩
  entry := #[⟨0, Nat.two_pow_pos bits⟩]
  stop := #[⟨1, hbits⟩]

theorem smallWordColumns_dictionary_eq_serialize (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) :
    (smallWordColumns H bits hbits).dictionary =
      FlatPairDictionary.serialize (smallColumns H) (smallColumns_fits H bits hbits) := by
  let ser := FlatPairDictionary.serialize (smallColumns H) (smallColumns_fits H bits hbits)
  have hsz : ser.size = 1 := by
    simp [ser, FlatPairDictionary.serialize_size, FlatPairDictionary.packedSize,
      FlatPairDictionary.slotBase, FlatPairDictionary.secondBase, smallColumns]
  have hrc : FlatPairDictionary.rowCount ser = 0 :=
    (FlatPairDictionary.rowCount_serialize (smallColumns H) _).trans rfl
  have h0val : (ser[0]'(by omega)).val = 0 := by
    unfold FlatPairDictionary.rowCount at hrc
    rw [getElem?_pos ser 0 (by omega), Option.map_some, Option.getD_some] at hrc
    exact hrc
  apply Array.ext
  · simp [smallWordColumns, FlatPairDictionary.serialize_size, FlatPairDictionary.packedSize,
      FlatPairDictionary.slotBase, FlatPairDictionary.secondBase, smallColumns]
  · intro i hi1 hi2
    have hi0 : i = 0 := by simp [smallWordColumns] at hi1; omega
    subst i
    apply Fin.ext
    exact h0val.symm

theorem smallWordColumns_dictionary_represents (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) :
    FlatPairDictionary.Represents (smallWordColumns H bits hbits).dictionary (smallColumns H) := by
  rw [smallWordColumns_dictionary_eq_serialize H bits hbits]
  exact FlatPairDictionary.serialize_represents _ _

theorem smallWordColumns_dictionary_valid (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) :
    FlatPairDictionary.Valid (smallWordColumns H bits hbits).dictionary :=
  (smallWordColumns_dictionary_represents H bits hbits).valid

theorem smallWordColumns_wordCount (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) :
    (smallWordColumns H bits hbits).wordCount = 5 + H.vertexCount := by
  simp [WordColumns.wordCount, smallWordColumns]
  omega

theorem smallWordColumns_wordCount_le (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) :
    (smallWordColumns H bits hbits).wordCount ≤ 1 + 18 * H.vertexCount := by
  have hpos : 0 < H.vertexCount := Fin.pos H.root
  rw [smallWordColumns_wordCount]
  omega

theorem smallWordColumns_wordCount_const_le (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (hsmall : H.vertexCount < 3) :
    (smallWordColumns H bits hbits).wordCount ≤ 7 := by
  rw [smallWordColumns_wordCount]
  omega

theorem smallWordColumns_packedPayload_size (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) :
    (packedPayload (smallWordColumns H bits hbits)).size = 5 + H.vertexCount := by
  rw [packedPayload_size, smallWordColumns_wordCount]

theorem smallWordColumns_packedPayload_getElem? (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (j : Nat) :
    (packedPayload (smallWordColumns H bits hbits))[j]? =
      if j < 4 + H.vertexCount then some ⟨0, Nat.two_pow_pos bits⟩
      else if j = 4 + H.vertexCount then some ⟨1, hbits⟩
      else none := by
  let w := smallWordColumns H bits hbits
  let z : Word bits := ⟨0, Nat.two_pow_pos bits⟩
  have hszd : w.dictionary.size = 1 := rfl
  have hszb1 : w.back.tagAndFirst.size = 1 := rfl
  have hszb2 : w.back.second.size = 1 := rfl
  have hszl : w.labels.size = H.vertexCount := Array.size_replicate
  have hsze : w.entry.size = 1 := rfl
  have hprefix : packedPrefix w = Array.replicate (3 + H.vertexCount) z := by
    apply Array.ext
    · simp [packedPrefix, hszd, hszb1, hszb2, hszl]
      omega
    · intro i hi1 hi2
      have hi : i < 3 + H.vertexCount := by simpa using hi2
      have ha1 : (w.dictionary ++ w.back.tagAndFirst).size = 2 := by
        simp [hszd, hszb1]
      have ha2 : (w.dictionary ++ w.back.tagAndFirst ++ w.back.second).size = 3 := by
        simp [hszd, hszb1, hszb2]
      have hget : (packedPrefix w)[i]? = some z := by
        unfold packedPrefix
        rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | rfl | hge
        · rw [Array.getElem?_append_left (by rw [ha2]; exact (by decide : 0 < 3)),
            Array.getElem?_append_left (by rw [ha1]; exact (by decide : 0 < 2)),
            Array.getElem?_append_left (by rw [hszd]; exact (by decide : 0 < 1))]
          rfl
        · rw [Array.getElem?_append_left (by rw [ha2]; exact (by decide : 1 < 3)),
            Array.getElem?_append_left (by rw [ha1]; exact (by decide : 1 < 2)),
            Array.getElem?_append_right (by rw [hszd]; exact (by decide : 1 ≤ 1))]
          rfl
        · rw [Array.getElem?_append_left (by rw [ha2]; exact (by decide : 2 < 3)),
            Array.getElem?_append_right (by rw [ha1]; exact (by decide : 2 ≤ 2))]
          rfl
        · rw [Array.getElem?_append_right (by rw [ha2]; exact hge), ha2]
          change w.labels[i - 3]? = some z
          simp [w, smallWordColumns, z, show i - 3 < H.vertexCount by omega]
      rw [getElem?_pos (packedPrefix w) i hi1] at hget
      have hr : (Array.replicate (3 + H.vertexCount) z)[i]'hi2 = z := by simp
      exact (Option.some.inj hget).trans hr.symm
  have hpay : packedPayload w =
      Array.replicate (4 + H.vertexCount) z ++ #[⟨1, hbits⟩] := by
    unfold packedPayload
    rw [hprefix]
    apply Array.ext
    · simp [w, smallWordColumns]
      omega
    · intro i hi1 hi2
      have hget : (Array.replicate (3 + H.vertexCount) z ++ w.entry ++ w.stop)[i]? =
          (Array.replicate (4 + H.vertexCount) z ++ #[⟨1, hbits⟩])[i]? := by
        have hpe : (Array.replicate (3 + H.vertexCount) z ++ w.entry).size = 4 + H.vertexCount := by
          simp [hsze]
          omega
        by_cases hlt : i < 3 + H.vertexCount
        · rw [Array.getElem?_append_left (by rw [hpe]; omega),
            Array.getElem?_append_left (by simp [hlt]),
            Array.getElem?_append_left (by simp; omega),
            Array.getElem?_replicate, ite_eq_left hlt,
            Array.getElem?_replicate, ite_eq_left (by omega : i < 4 + H.vertexCount)]
        · have hle : i = 3 + H.vertexCount ∨ i = 4 + H.vertexCount := by
            simp at hi2
            omega
          rcases hle with rfl | rfl
          · rw [Array.getElem?_append_left (by rw [hpe]; omega),
              Array.getElem?_append_right (by simp),
              Array.getElem?_append_left (by simp)]
            simp [w, smallWordColumns, z]
          · rw [Array.getElem?_append_right (by rw [hpe]; omega), hpe,
              Array.getElem?_append_right (by simp)]
            simp [w, smallWordColumns]
      rw [getElem?_pos _ i hi1, getElem?_pos _ i hi2] at hget
      exact Option.some.inj hget
  rw [show packedPayload (smallWordColumns H bits hbits) = packedPayload w from rfl, hpay]
  by_cases hlt : j < 4 + H.vertexCount
  · rw [ite_eq_left hlt, Array.getElem?_append_left (by simp [hlt]),
      Array.getElem?_replicate, ite_eq_left hlt]
  · rw [ite_eq_right hlt]
    by_cases heq : j = 4 + H.vertexCount
    · subst heq
      rw [ite_eq_left rfl, Array.getElem?_append_right (by simp)]
      simp
    · rw [ite_eq_right heq, getElem?_neg]
      simp
      omega

theorem smallWordColumns_known (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (a v : Nat) :
    (smallWordColumns H bits hbits).known a v = decide (a = 0) := by
  unfold WordColumns.known WordColumns.labelAt smallWordColumns
  have hlab : ((Array.replicate H.vertexCount (⟨0, Nat.two_pow_pos bits⟩ : Word bits))[v]?
      |>.map Fin.val).getD 0 = 0 := by
    by_cases hv : v < H.vertexCount <;> simp [hv]
  rw [hlab]
  by_cases ha : a = 0
  · subst ha
    simp
  · simp [ha]

theorem smallWordColumns_knownProbed (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (a v : Nat) :
    (smallWordColumns H bits hbits).knownProbed a v = (decide (a = 0), 4) := by
  rw [WordColumns.knownProbed_exact, smallWordColumns_known]

theorem smallWordColumns_known_nonzero_false (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) {a : Nat} (ha : a ≠ 0) (v : Nat) :
    (smallWordColumns H bits hbits).known a v = false := by
  rw [smallWordColumns_known]
  simp [ha]

private theorem smallWordColumns_search_miss_of_state (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (x y : Word bits)
    (state : RamProgram.State (ThreeCalls.layout bits (smallWordColumns H bits hbits).dictionary.size
      (Nat.le_of_lt (smallWordColumns_dictionary_valid H bits hbits).capacity)))
    (hpc : state.pc = 0)
    (h7 : ThreeCalls.setupReg state 7 =
      (FlatPairDictionary.firstSlice (smallWordColumns H bits hbits).dictionary
        (smallWordColumns_dictionary_valid H bits hbits)).base)
    (h8 : (ThreeCalls.setupReg state 8).val =
      (FlatPairDictionary.firstSlice (smallWordColumns H bits hbits).dictionary
        (smallWordColumns_dictionary_valid H bits hbits)).len)
    (h9 : ThreeCalls.setupReg state 9 =
      (FlatPairDictionary.secondSlice (smallWordColumns H bits hbits).dictionary
        (smallWordColumns_dictionary_valid H bits hbits)).base)
    (h11 : ThreeCalls.setupReg state 11 = x)
    (h12 : ThreeCalls.setupReg state 12 = y)
    (h4 : ThreeCalls.setupReg state 4 = zero bits)
    (h5 : ThreeCalls.setupReg state 5 = zero bits) :
    let w := smallWordColumns H bits hbits
    let valid := smallWordColumns_dictionary_valid H bits hbits
    let fit := Nat.le_of_lt valid.capacity
    ∃ out,
      run (ThreeCalls.EqualityTail.checkedProgram fit hbits (ThreeCalls.concreteSetup bits hbits))
        ⟨w.dictionary, rfl⟩ (33 * OracleContract.L H.vertexCount + 39) state = some out ∧
      out.executed ≤ 72 ∧
      out.executed ≤ 33 * OracleContract.L H.vertexCount + 39 ∧
      (if ThreeCalls.setupReg out.finalState 0 = (⟨1, hbits⟩ : Word bits)
       then some (ThreeCalls.setupReg out.finalState 3).val else none) = none := by
  intro w valid fit
  let rep := smallWordColumns_dictionary_represents H bits hbits
  let narrow : RamProgram.Input (Predecessor.layout bits w.dictionary.size fit) :=
    ⟨w.dictionary, rfl⟩
  let c := FlatPairDictionary.workerColumns narrow.words rep
  have hsorted : PairLookup.StrictSorted (smallColumns H).dict := by
    intro i j hij
    simp [smallColumns] at j hij
  obtain ⟨out, hrun, _, _, hhit⟩ :=
    ThreeCalls.pair_search_correct_from_pc0_with_index (i := narrow)
      (j := (⟨w.dictionary, rfl⟩ : RamProgram.Input (ThreeCalls.layout bits w.dictionary.size fit)))
      fit hbits c hsorted x y rfl state hpc h7 h8 h9 h11 h12 h4 h5
  have hbound72 : 33 * (Nat.log2 ((smallColumns H).dict.size + 1) + 1) + 39 = 72 := by
    simp [smallColumns]
  have hL : 72 ≤ 33 * OracleContract.L H.vertexCount + 39 := by
    have h1 := OracleContract.one_le_L H.vertexCount
    omega
  have hrun' := run_stable_of_le (hbound72 ▸ hL) hrun
  have hexec72 : out.executed ≤ 72 := hbound72 ▸ run_executed_le hrun
  have hmiss : (PairLookup.lookup (smallColumns H).dict (x.val, y.val)).1 = none := by
    change (PairLookup.lookup (#[] : Array PairLookup.Key) (x.val, y.val)).1 = none
    rfl
  refine ⟨out, hrun', hexec72, by omega, ?_⟩
  simpa only [decide_eq_true_eq, hmiss] using hhit

private def smallStartState (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (x y : Word bits) :
    RamProgram.State (ThreeCalls.layout bits (smallWordColumns H bits hbits).dictionary.size
      (Nat.le_of_lt (smallWordColumns_dictionary_valid H bits hbits).capacity)) where
  regs := #[
    zero bits, zero bits, zero bits, zero bits,
    zero bits, zero bits, zero bits, ⟨1, hbits⟩,
    zero bits, ⟨1, hbits⟩, zero bits, x,
    y, zero bits, zero bits, zero bits
  ]
  data := #[]
  pc := 0
  regs_size := rfl
  data_size := rfl

private theorem smallWordColumns_map_search_miss (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (x y : Word bits)
    (state : RamProgram.State (ThreeCalls.layout bits (smallWordColumns H bits hbits).dictionary.size
      (Nat.le_of_lt (smallWordColumns_dictionary_valid H bits hbits).capacity)))
    (hst : state = smallStartState H bits hbits x y)
    {α : Type} (g : RamProgram.Result (ThreeCalls.layout bits (smallWordColumns H bits hbits).dictionary.size
      (Nat.le_of_lt (smallWordColumns_dictionary_valid H bits hbits).capacity)) → α × Nat × Nat)
    (ans : α)
    (htarg : ∀ out,
      (if ThreeCalls.setupReg out.finalState 0 = (⟨1, hbits⟩ : Word bits)
       then some (ThreeCalls.setupReg out.finalState 3).val else none) = none →
      g out = (ans, out.executed, 1)) :
    let w := smallWordColumns H bits hbits
    let valid := smallWordColumns_dictionary_valid H bits hbits
    let fit := Nat.le_of_lt valid.capacity
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ steps probes,
      (run (ThreeCalls.EqualityTail.checkedProgram fit hbits (ThreeCalls.concreteSetup bits hbits))
        ⟨w.dictionary, rfl⟩ fuel state).map g = some (ans, steps, probes) ∧
      steps ≤ 72 ∧ steps ≤ fuel ∧ probes = 1 := by
  intro w valid fit fuel
  subst state
  obtain ⟨out, hrun, hex72, hexFuel, hmiss⟩ :=
    smallWordColumns_search_miss_of_state H bits hbits x y (smallStartState H bits hbits x y)
      rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨out.executed, 1, ?_, hex72, hexFuel, rfl⟩
  rw [hrun]
  simp only [Option.map_some, htarg out hmiss]

theorem smallWordColumns_keyedProbed (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (x y : Word bits) (v : Nat) :
    let w := smallWordColumns H bits hbits
    let valid := smallWordColumns_dictionary_valid H bits hbits
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ steps probes,
      w.keyedProbed valid hbits fuel x y v = some (false, steps, probes) ∧
      steps ≤ 72 ∧ steps ≤ fuel ∧ probes = 1 := by
  intro w valid fuel
  unfold WordColumns.keyedProbed
  dsimp only
  refine smallWordColumns_map_search_miss H bits hbits x y _ rfl _ false ?_
  intro out hmiss
  rw [hmiss]
  rfl

theorem smallWordColumns_lookupSlotProbed (H : LabelledQuotient) (bits : Nat)
    (hbits : 1 < 2 ^ bits) (x y : Word bits) :
    let w := smallWordColumns H bits hbits
    let valid := smallWordColumns_dictionary_valid H bits hbits
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ steps probes,
      w.lookupSlotProbed valid hbits fuel x y = some (none, steps, probes) ∧
      steps ≤ 72 ∧ steps ≤ fuel ∧ probes = 1 := by
  intro w valid fuel
  unfold WordColumns.lookupSlotProbed
  dsimp only
  refine smallWordColumns_map_search_miss H bits hbits x y _ rfl _ none ?_
  intro out hmiss
  rw [hmiss]
  rfl

theorem smallWordColumns_vacuous_pair_spec (H : LabelledQuotient)
    (hsmall : H.vertexCount < 3) (q : CutPair H) (v : Vertex H) :
    false = true ↔ q.fst < q.snd ∧ H.ProperLoss q v :=
  (cutPair_impossible_of_small (by omega) q).elim

/-! ### 2. Small Quotient (`H.vertexCount < 3`) Single-Pass RAM Program -/

section SmallRam

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- 12-instruction ROM routine writing the serialized small-quotient
`WordColumns` payload (`4 + n_H` zeros followed by `1`) to `s.data[0 .. 5 + n_H)`.
Leaves no uncharged initialization assumptions on `s.regs` or `s.data`. -/
def smallBuildCode (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h4 : 4 < 2 ^ bits) : Program (layout bits inputCap workCap hi hw) :=
  #[.imm 0 (zero bits),
    .imm 1 ⟨1, by omega⟩,
    .loadInput 2 0,
    .imm 3 ⟨4, h4⟩,
    .add 3 3 2,
    .imm 4 (zero bits),
    .branchLt 4 3 7 10,
    .storeData 4 0,
    .add 4 4 1,
    .goto 6,
    .storeData 3 1,
    .halt]

def smallBuildPhase (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h4 : 4 < 2 ^ bits) : Phase L :=
  Phase.ofLast (smallBuildCode hi hw h4) 11 rfl rfl rfl

private theorem step_imm_next {code : Program L} {input : Input L} {s : State L}
    {dst : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.imm dst w)) (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ t.data = s.data ∧
      reg t dst = w ∧ (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  have hd : dst.val < s.regs.size := by simpa only [s.regs_size] using dst.isLt
  let t : State L :=
    { s with
      regs := s.regs.set dst.val w hd
      pc := s.pc + 1
      regs_size := by simp only [Array.size_set, s.regs_size] }
  have hs : step code input s = some (Transition.next t) := by
    unfold step
    rw [hf]
    change (if s.pc + 1 < code.size then some (Transition.next t) else none) = _
    rw [ite_eq_left hn]
  refine ⟨t, hs, rfl, rfl, ?_, ?_⟩
  · change (s.regs.set dst.val w hd)[dst.val]'_ = w
    simp
  · intro r hr
    have hv : r.val ≠ dst.val := fun e => hr (Fin.ext e)
    have hrlt : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
    change (s.regs.set dst.val w hd)[r.val]'_ = s.regs[r.val]'hrlt
    simp [Array.getElem_set, Ne.symm hv]

private theorem step_loadInput_next {code : Program L} {input : Input L} {s : State L}
    {dst addr : Fin 15} {w : Word bits}
    (hf : code[s.pc]? = some (.loadInput dst addr))
    (hread : input.words[(reg s addr).val]? = some w)
    (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧ t.data = s.data ∧
      reg t dst = w ∧ (∀ r : Fin 15, r ≠ dst → reg t r = reg s r) := by
  have hd : dst.val < s.regs.size := by simpa only [s.regs_size] using dst.isLt
  let t : State L :=
    { s with
      regs := s.regs.set dst.val w hd
      pc := s.pc + 1
      regs_size := by simp only [Array.size_set, s.regs_size] }
  have hstep1 : step code input s =
      (input.words[(reg s addr).val]? >>= fun v =>
        if s.pc + 1 < code.size then some (Transition.next
          { s with
            regs := s.regs.set dst.val v hd
            pc := s.pc + 1
            regs_size := by simp only [Array.size_set, s.regs_size] })
        else none) := by
    unfold step
    rw [hf]
    rfl
  have hs : step code input s = some (Transition.next t) := by
    rw [hstep1, hread]
    change (if s.pc + 1 < code.size then some (Transition.next t) else none) = _
    rw [ite_eq_left hn]
  refine ⟨t, hs, rfl, rfl, ?_, ?_⟩
  · change (s.regs.set dst.val w hd)[dst.val]'_ = w
    simp
  · intro r hr
    have hv : r.val ≠ dst.val := fun e => hr (Fin.ext e)
    have hrlt : r.val < s.regs.size := by simpa only [s.regs_size] using r.isLt
    change (s.regs.set dst.val w hd)[r.val]'_ = s.regs[r.val]'hrlt
    simp [Array.getElem_set, Ne.symm hv]

private theorem step_storeData_next {code : Program L} {input : Input L} {s : State L}
    {addr src : Fin 15}
    (hf : code[s.pc]? = some (.storeData addr src))
    (hfit : (reg s addr).val < s.data.size)
    (hn : s.pc + 1 < code.size) :
    ∃ t : State L, step code input s = some (Transition.next t) ∧
      t.pc = s.pc + 1 ∧
      t.data = s.data.set (reg s addr).val (reg s src) hfit ∧
      (∀ r : Fin 15, reg t r = reg s r) := by
  let t : State L :=
    { s with
      data := s.data.set (reg s addr).val (reg s src) hfit
      pc := s.pc + 1
      data_size := by simp only [Array.size_set, s.data_size] }
  have hs : step code input s = some (Transition.next t) := by
    unfold step
    rw [hf]
    change (if h : (reg s addr).val < s.data.size then
      if s.pc + 1 < code.size then
        some (Transition.next { s with
          data := s.data.set (reg s addr).val (reg s src) h
          pc := s.pc + 1
          data_size := by simp only [Array.size_set, s.data_size] })
      else none
      else none) = _
    rw [dite_eq_left hfit, ite_eq_left hn]
  exact ⟨t, hs, rfl, rfl, fun _ => rfl⟩

private structure SmallLoopInv (n lim : Nat) (s : State L) : Prop where
  pc : s.pc = 6
  r0 : reg s 0 = zero bits
  r1 : (reg s 1).val = 1
  r3 : (reg s 3).val = lim
  r4 : (reg s 4).val = n
  written : ∀ j < n, s.data[j]? = some (zero bits)

private theorem small_loop_step (input : Input L) (h4 : 4 < 2 ^ bits) (lim : Nat)
    (hlim : lim ≤ workCap) (hlimBits : lim < 2 ^ bits) (i : Nat) (hlt : i < lim) :
    BlockSpec (smallBuildCode hi hw h4) input 4
      (SmallLoopInv i lim) (SmallLoopInv (i + 1) lim) := by
  intro s inv
  let code : Program L := smallBuildCode hi hw h4
  have hsize : code.size = 12 := rfl
  have f6 : code[s.pc]? = some (.branchLt 4 3 7 10) := by rw [inv.pc]; rfl
  have hltb : ltb (reg s 4) (reg s 3) = true :=
    (PaperB.WordOps.ltb_eq_true _ _).mpr (by rw [inv.r4, inv.r3]; exact hlt)
  let s7 : State L := { s with pc := 7 }
  have st67 : step code input s = some (Transition.next s7) := by
    simpa only [s7, hltb, ite_true] using
      step_branchLt_at (input := input) f6 (by rw [hltb]; exact (show 7 < 12 by decide))
  have hfit : (reg s7 4).val < s7.data.size := by
    change (reg s 4).val < s.data.size
    rw [inv.r4, s.data_size]
    change i < workCap
    omega
  obtain ⟨s8, st78, pc8, data8, regs8⟩ :=
    step_storeData_next (code := code) (input := input) (s := s7) rfl hfit
      (by exact (show (7 : Nat) + 1 < 12 by decide))
  have f8 : code[s8.pc]? = some (.add 4 4 1) := by rw [pc8]; rfl
  obtain ⟨s9, st89, pc9, r4_9, regs9, data9⟩ :=
    step_add_at (code := code) (input := input) (s := s8) f8
      (by rw [pc8]; exact (show (7 : Nat) + 1 + 1 < 12 by decide))
  have f9 : code[s9.pc]? = some (.goto 6) := by rw [pc9, pc8]; rfl
  let s10 : State L := { s9 with pc := 6 }
  have st910 : step code input s9 = some (Transition.next s10) :=
    step_goto_at (code := code) (input := input) f9 (by exact (show 6 < 12 by decide))
  have hsum : (reg s8 4).val + (reg s8 1).val < 2 ^ bits := by
    rw [regs8 4, regs8 1]
    change (reg s 4).val + (reg s 1).val < 2 ^ bits
    rw [inv.r4, inv.r1]
    omega
  have hr4 : (reg s10 4).val = i + 1 := by
    change (reg s9 4).val = i + 1
    rw [r4_9, PaperB.WordOps.add_no_wrap _ _ hsum, regs8 4, regs8 1]
    change (reg s 4).val + (reg s 1).val = i + 1
    rw [inv.r4, inv.r1]
  have hr0 : reg s10 0 = zero bits := by
    change reg s9 0 = _
    rw [regs9 0 (by exact (show (0 : Fin 15) ≠ 4 by decide)), regs8 0]
    exact inv.r0
  have hr1 : (reg s10 1).val = 1 := by
    change (reg s9 1).val = _
    rw [regs9 1 (by exact (show (1 : Fin 15) ≠ 4 by decide)), regs8 1]
    exact inv.r1
  have hr3 : (reg s10 3).val = lim := by
    change (reg s9 3).val = _
    rw [regs9 3 (by exact (show (3 : Fin 15) ≠ 4 by decide)), regs8 3]
    exact inv.r3
  have hsdata : i < s.data.size := by
    rw [s.data_size]
    change i < workCap
    omega
  have hdata : s10.data = s.data.set i (zero bits) hsdata := by
    change s9.data = _
    rw [data9, data8]
    have haddr : (reg s7 4).val = i := inv.r4
    have hval : reg s7 0 = zero bits := inv.r0
    change s.data.set (reg s7 4).val (reg s7 0) hfit = s.data.set i (zero bits) hsdata
    simp only [haddr, hval]
  have hwritten : ∀ j < i + 1, s10.data[j]? = some (zero bits) := by
    intro j hj
    rw [hdata]
    by_cases heq : j = i
    · subst heq
      rw [Array.getElem?_set_self]
    · rw [Array.getElem?_set_ne _ (Ne.symm heq)]
      exact inv.written j (by omega)
  exact ⟨s10, Steps.cons st67 (Steps.cons st78 (Steps.cons st89 (Steps.cons st910 (Steps.zero s10)))),
    ⟨rfl, hr0, hr1, hr3, hr4, hwritten⟩⟩

private theorem four_iterations (k : Nat) : iterationCost (fun _ => 4) k = 4 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [iterationCost, ih, Nat.mul_succ]

/-- Execute the small-quotient constructor from an arbitrary initial state `s₀`
given `RawQuotientInput input H`. Produces the exact serialized `WordColumns`
payload at `t.data[0 .. 5 + H.vertexCount)` in `25 + 4 * H.vertexCount ≤ 33` steps. -/
theorem run_small_build (input : Input L) (H : LabelledQuotient)
    (raw : RawQuotientInput input H) (hsmall : H.vertexCount < 3)
    (h4 : 4 < 2 ^ bits) (hbitsN : 4 + H.vertexCount < 2 ^ bits)
    (hwork : 5 + H.vertexCount ≤ workCap) (s₀ : State L) :
    let h1 : 1 < 2 ^ bits := by omega
    let w := smallWordColumns H bits h1
    ∃ t trace work,
      work = 25 + 4 * H.vertexCount ∧
      work ≤ 33 ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      run (smallBuildCode hi hw h4) input work (Phase.initial s₀) = some ⟨t, work⟩ ∧
      SuccessfulTrace (smallBuildCode hi hw h4) input (Phase.initial s₀) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  intro h1 w
  let code : Program L := smallBuildCode hi hw h4
  let s0 : State L := Phase.initial s₀
  have hs0pc : s0.pc = 0 := rfl
  have hszCode : code.size = 12 := rfl
  obtain ⟨s1, st01, pc1, _, r0_1, _⟩ :=
    step_imm_next (code := code) (input := input) (s := s0) rfl
      (by rw [hs0pc, hszCode]; exact (show (0 : Nat) + 1 < 12 by decide))
  have f1 : code[s1.pc]? = some (.imm 1 ⟨1, by omega⟩) := by rw [pc1, hs0pc]; rfl
  obtain ⟨s2, st12, pc2, _, r1_2, keep2⟩ :=
    step_imm_next (code := code) (input := input) (s := s1) f1
      (by rw [pc1, hs0pc, hszCode]; exact (show (1 : Nat) + 1 < 12 by decide))
  have r0_2 : reg s2 0 = zero bits := (keep2 0 (by exact (show (0 : Fin 15) ≠ 1 by decide))).trans r0_1
  have hr0val2 : (reg s2 0).val = 0 := congrArg Fin.val r0_2
  have hread0 : input.words[(reg s2 0).val]? = some ⟨H.vertexCount, by omega⟩ := by
    rw [hr0val2]
    have hdr := raw.hdr_n
    cases hopt : input.words[0]? with
    | none => simp [hopt] at hdr
    | some v =>
      rw [hopt, Option.map_some] at hdr
      exact congrArg some (Fin.ext (Option.some.inj hdr))
  have f2 : code[s2.pc]? = some (.loadInput 2 0) := by rw [pc2, pc1, hs0pc]; rfl
  obtain ⟨s3, st23, pc3, _, r2_3, keep3⟩ :=
    step_loadInput_next (code := code) (input := input) (s := s2) f2 hread0
      (by rw [pc2, pc1, hs0pc, hszCode]; exact (show (2 : Nat) + 1 < 12 by decide))
  have r0_3 : reg s3 0 = zero bits := (keep3 0 (by exact (show (0 : Fin 15) ≠ 2 by decide))).trans r0_2
  have r1_3 : reg s3 1 = ⟨1, by omega⟩ := (keep3 1 (by exact (show (1 : Fin 15) ≠ 2 by decide))).trans r1_2
  have f3 : code[s3.pc]? = some (.imm 3 ⟨4, h4⟩) := by rw [pc3, pc2, pc1, hs0pc]; rfl
  obtain ⟨s4, st34, pc4, _, r3_4, keep4⟩ :=
    step_imm_next (code := code) (input := input) (s := s3) f3
      (by rw [pc3, pc2, pc1, hs0pc, hszCode]; exact (show (3 : Nat) + 1 < 12 by decide))
  have r0_4 : reg s4 0 = zero bits := (keep4 0 (by exact (show (0 : Fin 15) ≠ 3 by decide))).trans r0_3
  have r1_4 : reg s4 1 = ⟨1, by omega⟩ := (keep4 1 (by exact (show (1 : Fin 15) ≠ 3 by decide))).trans r1_3
  have r2_4 : reg s4 2 = ⟨H.vertexCount, by omega⟩ := (keep4 2 (by exact (show (2 : Fin 15) ≠ 3 by decide))).trans r2_3
  have f4 : code[s4.pc]? = some (.add 3 3 2) := by rw [pc4, pc3, pc2, pc1, hs0pc]; rfl
  obtain ⟨s5, st45, pc5, r3_5, keep5, _⟩ :=
    step_add_at (code := code) (input := input) (s := s4) f4
      (by rw [pc4, pc3, pc2, pc1, hs0pc, hszCode]; exact (show (4 : Nat) + 1 < 12 by decide))
  have hsum32 : (reg s4 3).val + (reg s4 2).val < 2 ^ bits := by
    rw [r3_4, r2_4]
    exact hbitsN
  have r3val_5 : (reg s5 3).val = 4 + H.vertexCount := by
    rw [r3_5, PaperB.WordOps.add_no_wrap _ _ hsum32, r3_4, r2_4]
  have r0_5 : reg s5 0 = zero bits := (keep5 0 (by exact (show (0 : Fin 15) ≠ 3 by decide))).trans r0_4
  have r1_5 : reg s5 1 = ⟨1, by omega⟩ := (keep5 1 (by exact (show (1 : Fin 15) ≠ 3 by decide))).trans r1_4
  have f5 : code[s5.pc]? = some (.imm 4 (zero bits)) := by
    rw [pc5, pc4, pc3, pc2, pc1, hs0pc]; rfl
  obtain ⟨s6, st56, pc6, _, r4_6, keep6⟩ :=
    step_imm_next (code := code) (input := input) (s := s5) f5
      (by rw [pc5, pc4, pc3, pc2, pc1, hs0pc, hszCode]; exact (show (5 : Nat) + 1 < 12 by decide))
  have pc6_eq : s6.pc = 6 := by omega
  have r0_6 : reg s6 0 = zero bits := (keep6 0 (by exact (show (0 : Fin 15) ≠ 4 by decide))).trans r0_5
  have r1_6 : (reg s6 1).val = 1 := by
    rw [keep6 1 (by exact (show (1 : Fin 15) ≠ 4 by decide)), r1_5]
  have r3_6 : (reg s6 3).val = 4 + H.vertexCount := by
    rw [keep6 3 (by exact (show (3 : Fin 15) ≠ 4 by decide)), r3val_5]
  have r4_6_val : (reg s6 4).val = 0 := congrArg Fin.val r4_6
  have startInv : SmallLoopInv 0 (4 + H.vertexCount) s6 :=
    ⟨pc6_eq, r0_6, r1_6, r3_6, r4_6_val, fun j hj => (Nat.not_lt_zero j hj).elim⟩
  obtain ⟨sLoop, stLoop, invEnd⟩ := loop_steps (code := code) (input := input)
    (4 + H.vertexCount) (fun _ => 4) (fun k => SmallLoopInv k (4 + H.vertexCount))
    (small_loop_step input h4 (4 + H.vertexCount) (by omega) hbitsN)
    s6 startInv
  rw [four_iterations] at stLoop
  have fExit : code[sLoop.pc]? = some (.branchLt 4 3 7 10) := by rw [invEnd.pc]; rfl
  have hge : ltb (reg sLoop 4) (reg sLoop 3) = false := by
    cases e : ltb (reg sLoop 4) (reg sLoop 3) with
    | false => rfl
    | true =>
      have lt := (PaperB.WordOps.ltb_eq_true _ _).mp e
      rw [invEnd.r4, invEnd.r3] at lt
      omega
  let s10 : State L := { sLoop with pc := 10 }
  have stExit : step code input sLoop = some (Transition.next s10) := by
    simpa only [s10, hge, Bool.false_eq_true, ite_false] using
      step_branchLt_at (input := input) fExit (by rw [hge]; exact (show 10 < 12 by decide))
  have hfitEnd : (reg s10 3).val < s10.data.size := by
    change (reg sLoop 3).val < sLoop.data.size
    rw [invEnd.r3, sLoop.data_size]
    change 4 + H.vertexCount < workCap
    omega
  obtain ⟨s11, st1011, pc11, data11, _⟩ :=
    step_storeData_next (code := code) (input := input) (s := s10) rfl hfitEnd
      (by exact (show 10 + 1 < 12 by decide))
  have fHalt : code[s11.pc]? = some .halt := by rw [pc11]; rfl
  have stHalt : step code input s11 = some (.halted s11) := step_halt_at fHalt
  have prefixSteps : Steps code input 6 s0 s6 :=
    Steps.cons st01 (Steps.cons st12 (Steps.cons st23 (Steps.cons st34
      (Steps.cons st45 (Steps.cons st56 (Steps.zero s6))))))
  have tailSteps : Steps code input 2 sLoop s11 :=
    Steps.cons stExit (Steps.cons st1011 (Steps.zero s11))
  have allSteps : Steps code input (6 + 4 * (4 + H.vertexCount) + 2) s0 s11 :=
    (prefixSteps.append stLoop).append tailSteps
  have hexec : run code input (6 + 4 * (4 + H.vertexCount) + 2 + 1) s0 =
      some ⟨s11, 6 + 4 * (4 + H.vertexCount) + 2 + 1⟩ :=
    allSteps.halts stHalt
  have hworkEq : 6 + 4 * (4 + H.vertexCount) + 2 + 1 = 25 + 4 * H.vertexCount := by omega
  rw [hworkEq] at hexec
  obtain ⟨trace, ok⟩ := run_has_successfulTrace hexec
  have hsLoopData : 4 + H.vertexCount < sLoop.data.size := by
    rw [sLoop.data_size]
    change 4 + H.vertexCount < workCap
    omega
  have hdata11 : s11.data = sLoop.data.set (4 + H.vertexCount) ⟨1, h1⟩ hsLoopData := by
    rw [data11]
    have haddr : (reg s10 3).val = 4 + H.vertexCount := invEnd.r3
    have hval : reg s10 1 = ⟨1, h1⟩ := by
      apply Fin.ext
      exact invEnd.r1
    change sLoop.data.set (reg s10 3).val (reg s10 1) hfitEnd =
      sLoop.data.set (4 + H.vertexCount) ⟨1, h1⟩ hsLoopData
    simp only [haddr, hval]
  have hextract : s11.data.extract 0 w.wordCount = packedPayload w := by
    have hsz : w.wordCount = 5 + H.vertexCount := smallWordColumns_wordCount H bits h1
    have hwle : w.wordCount ≤ s11.data.size := by
      rw [s11.data_size, hsz]
      change 5 + H.vertexCount ≤ workCap
      exact hwork
    apply Array.ext
    · rw [Array.size_extract, Nat.min_eq_left hwle, Nat.sub_zero, packedPayload_size]
    · intro j hj1 hj2
      have hj : j < 5 + H.vertexCount := by
        rw [Array.size_extract, Nat.min_eq_left hwle, Nat.sub_zero, hsz] at hj1
        exact hj1
      have hLHS : (s11.data.extract 0 w.wordCount)[j]'hj1 = s11.data[j]'(by omega) := by
        simp [Array.getElem_extract]
      rw [hLHS]
      apply Fin.ext
      have hpay := smallWordColumns_packedPayload_getElem? H bits h1 j
      rw [getElem?_pos (packedPayload w) j hj2] at hpay
      have hdataPos : s11.data[j]? = some (s11.data[j]'(by omega)) :=
        getElem?_pos s11.data j (by omega)
      by_cases hlt : j < 4 + H.vertexCount
      · rw [ite_eq_left hlt] at hpay
        have hcell : s11.data[j]? = some (zero bits) := by
          rw [hdata11, Array.getElem?_set_ne _ (by omega)]
          exact invEnd.written j hlt
        rw [hdataPos] at hcell
        have h1' := Option.some.inj hcell
        have h2' := Option.some.inj hpay
        rw [h1', h2']
        rfl
      · have heq : j = 4 + H.vertexCount := by omega
        subst heq
        rw [ite_eq_right (by omega : ¬ 4 + H.vertexCount < 4 + H.vertexCount), ite_eq_left rfl] at hpay
        have hcell : s11.data[4 + H.vertexCount]? = some ⟨1, h1⟩ := by
          rw [hdata11, Array.getElem?_set_self]
        rw [hdataPos] at hcell
        have h1' := Option.some.inj hcell
        have h2' := Option.some.inj hpay
        rw [h1', h2']
  refine ⟨s11, trace, 25 + 4 * H.vertexCount, rfl, by omega, hextract,
    smallWordColumns_wordCount_le H bits h1, hexec, ok, ok.peak_eq⟩

end SmallRam

/-! ### 3. Unified Lemma 3.2 Serialized Index & Lookup Interface -/

/-- Serialized proper-loss index contract for Lemma 3.2 (v1.3):
- `O(n_H)` retained words (`w.wordCount ≤ 1 + 18 * H.vertexCount`),
- valid serialized `FlatPairDictionary`,
- `O(L)` keyed pair lookup via `WordColumns.keyedProbed` (`≤ 33 * L + 39` RAM steps, `≤ 9` probes),
- `O(L)` pair-only lookup via `WordColumns.lookupSlotProbed` (`≤ 33 * L + 39` RAM steps, `≤ 5` probes),
- `O(1)` known-node proper-loss membership via `WordColumns.knownProbed` (`4` word accesses). -/
structure SerializedProperLossIndex (H : LabelledQuotient) {bits : Nat}
    (w : WordColumns bits) : Prop where
  dict_valid : FlatPairDictionary.Valid w.dictionary
  wordCount_le : w.wordCount ≤ 1 + 18 * H.vertexCount
  keyed_spec : ∀ (one : 1 < 2 ^ bits) (hV : H.vertexCount ≤ 2 ^ bits)
      (q : CutPair H) (v : Vertex H),
      let x : Word bits := ⟨q.fst.val, Nat.lt_of_lt_of_le q.fst.isLt hV⟩
      let y : Word bits := ⟨q.snd.val, Nat.lt_of_lt_of_le q.snd.isLt hV⟩
      let fuel := 33 * OracleContract.L H.vertexCount + 39
      ∃ answer steps probes,
        w.keyedProbed dict_valid one fuel x y v.val = some (answer, steps, probes) ∧
        (answer = true ↔ q.fst < q.snd ∧ H.ProperLoss q v) ∧
        steps ≤ fuel ∧ probes ≤ 9
  lookup_and_known_spec : ∀ (one : 1 < 2 ^ bits) (hV : H.vertexCount ≤ 2 ^ bits)
      (q : CutPair H),
      let x : Word bits := ⟨q.fst.val, Nat.lt_of_lt_of_le q.fst.isLt hV⟩
      let y : Word bits := ⟨q.snd.val, Nat.lt_of_lt_of_le q.snd.isLt hV⟩
      let fuel := 33 * OracleContract.L H.vertexCount + 39
      ∃ slot? steps probes,
        w.lookupSlotProbed dict_valid one fuel x y = some (slot?, steps, probes) ∧
        steps ≤ fuel ∧ probes ≤ 5 ∧
        (∀ v : Vertex H, match slot? with
          | none => ¬ (q.fst < q.snd ∧ H.ProperLoss q v)
          | some a => (w.knownProbed a v.val).2 = 4 ∧
            ((w.knownProbed a v.val).1 = true ↔ q.fst < q.snd ∧ H.ProperLoss q v))

theorem smallWordColumns_isSerializedProperLossIndex (H : LabelledQuotient)
    (hsmall : H.vertexCount < 3) {bits : Nat} (hbits : 1 < 2 ^ bits) :
    SerializedProperLossIndex H (smallWordColumns H bits hbits) where
  dict_valid := smallWordColumns_dictionary_valid H bits hbits
  wordCount_le := smallWordColumns_wordCount_le H bits hbits
  keyed_spec _ _ q _ := (cutPair_impossible_of_small (by omega) q).elim
  lookup_and_known_spec _ _ q := (cutPair_impossible_of_small (by omega) q).elim

theorem packWordColumns_isSerializedProperLossIndex
    {H : LabelledQuotient} {p : ForestDictionary.Rows H}
    {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    [DecidableEq (CutPair H)]
    (r : OrderedReaderResult p data size_data rank large)
    {bits : Nat} (cap : 1 + 18 * H.vertexCount < 2 ^ bits) :
    SerializedProperLossIndex H (packWordColumns r cap) := by
  let w := packWordColumns r cap
  let rep := packWordColumns_dictionary_represents r cap
  refine ⟨rep.valid, packWordColumns_count_le r cap, ?_, ?_⟩
  · intro one _ q v
    obtain ⟨steps, probes, hkey, hsteps, hprobes⟩ := packWordColumns_keyedProbed r cap q v.val
    have hspec : (ofOrderedReader r).contains q v.val = true ↔
        q.fst < q.snd ∧ H.ProperLoss q v := by
      have hidx : (orderedConfig p large).vertexIndex v = v.val := rfl
      rw [← hidx, contains_eq r q v]
      exact r.contains_true_iff q v
    exact ⟨(ofOrderedReader r).contains q v.val, steps, probes, hkey, hspec, hsteps, hprobes⟩
  · intro one _ q
    obtain ⟨steps, probes, hslot, hsteps, hprobes⟩ :=
      packWordColumns_lookupSlotProbed_spec r cap q
    refine ⟨checkedHit r q, steps, probes, hslot, hsteps, hprobes, ?_⟩
    intro v
    have hspec : (ofOrderedReader r).contains q v.val = true ↔
        q.fst < q.snd ∧ H.ProperLoss q v := by
      have hidx : (orderedConfig p large).vertexIndex v = v.val := rfl
      rw [← hidx, contains_eq r q v]
      exact r.contains_true_iff q v
    cases hhit : checkedHit r q with
    | none =>
      intro hbad
      have hct : (ofOrderedReader r).contains q v.val = true := hspec.mpr hbad
      unfold Columns.contains at hct
      change (match checkedHit r q with
        | none => false
        | some a => (ofOrderedReader r).known a v.val) = true at hct
      rw [hhit] at hct
      cases hct
    | some a =>
      have hknown := packWordColumns_knownProbed r cap a v.val
      refine ⟨congrArg Prod.snd hknown, ?_⟩
      have h1 : (w.knownProbed a v.val).1 = (ofOrderedReader r).known a v.val :=
        congrArg Prod.fst hknown
      rw [h1]
      have hct : (ofOrderedReader r).contains q v.val = (ofOrderedReader r).known a v.val := by
        unfold Columns.contains
        change (match checkedHit r q with
          | none => false
          | some a' => (ofOrderedReader r).known a' v.val) = _
        rw [hhit]
      rw [← hct]
      exact hspec

/-- Unordered-pair corollary using `q.canonical`: accepts any `q : CutPair H`,
returning the exact `H.ProperLoss q v` decision in `O(L)` steps and `≤ 9` probes. -/
theorem serialized_canonical_keyedProbed_iff
    {H : LabelledQuotient} {bits : Nat} {w : WordColumns bits}
    (idx : SerializedProperLossIndex H w) (one : 1 < 2 ^ bits)
    (hV : H.vertexCount ≤ 2 ^ bits) (q : CutPair H) (v : Vertex H) :
    let qc := q.canonical
    let x : Word bits := ⟨qc.fst.val, Nat.lt_of_lt_of_le qc.fst.isLt hV⟩
    let y : Word bits := ⟨qc.snd.val, Nat.lt_of_lt_of_le qc.snd.isLt hV⟩
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ answer steps probes,
      w.keyedProbed idx.dict_valid one fuel x y v.val = some (answer, steps, probes) ∧
      (answer = true ↔ H.ProperLoss q v) ∧
      steps ≤ fuel ∧ probes ≤ 9 := by
  intro qc x y fuel
  obtain ⟨answer, steps, probes, hrun, hiff, hsteps, hprobes⟩ :=
    idx.keyed_spec one hV qc v
  refine ⟨answer, steps, probes, hrun, ?_, hsteps, hprobes⟩
  have hlt : qc.fst < qc.snd := CutPair.canonical_lt q
  rw [hiff, properLoss_canonical_iff H q v]
  exact ⟨fun h => h.2, fun h => ⟨hlt, h⟩⟩

/-! ### 4. Independent Case Checks (Small Quotients, Parallel Arcs, Repeated Keys, Memory Layout) -/

section CaseChecks

private def smallParallelQuotient : LabelledQuotient where
  origVertexCount := 2
  vertexCount := 2
  root := ⟨0, by decide⟩
  adj := #[
    [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩],
    []
  ]
  adj_size := rfl

private theorem smallParallel_arcCount : smallParallelQuotient.arcCount = 2 := rfl

private theorem smallParallel_small : smallParallelQuotient.vertexCount < 3 := by decide

private theorem smallParallel_retained_bound :
    (smallWordColumns smallParallelQuotient 6 (by decide)).wordCount = 7 ∧
    (smallWordColumns smallParallelQuotient 6 (by decide)).wordCount ≤
      1 + 18 * smallParallelQuotient.vertexCount := by
  refine ⟨smallWordColumns_wordCount _ _ _, smallWordColumns_wordCount_le _ _ _⟩

private theorem smallParallel_keyed_check :
    let w := smallWordColumns smallParallelQuotient 6 (by decide)
    let valid := smallWordColumns_dictionary_valid smallParallelQuotient 6 (by decide)
    ∃ steps probes,
      w.keyedProbed valid (by decide) (33 * OracleContract.L 2 + 39)
        ⟨0, by decide⟩ ⟨1, by decide⟩ 1 = some (false, steps, probes) ∧
      steps ≤ 72 ∧ probes = 1 ∧
      w.knownProbed 0 1 = (true, 4) ∧
      w.knownProbed 1 1 = (false, 4) := by
  obtain ⟨steps, probes, hk, h72, _, hp⟩ :=
    smallWordColumns_keyedProbed smallParallelQuotient 6 (by decide)
      ⟨0, by decide⟩ ⟨1, by decide⟩ 1
  exact ⟨steps, probes, hk, h72, hp,
    smallWordColumns_knownProbed _ _ _ 0 1,
    smallWordColumns_knownProbed _ _ _ 1 1⟩

private def parallelDiamondQuotient : LabelledQuotient where
  origVertexCount := 5
  vertexCount := 4
  root := ⟨0, by decide⟩
  adj := #[
    [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩],
    [⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, ⟨⟨3, by decide⟩, ⟨4, by decide⟩⟩],
    [⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩],
    []
  ]
  adj_size := rfl

private def parallelDiamondOrder : Array (Vertex parallelDiamondQuotient) :=
  #[⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩]

private theorem parallelDiamond_order_size :
    parallelDiamondOrder.size = parallelDiamondQuotient.vertexCount := rfl

private theorem parallelDiamond_arcCount : parallelDiamondQuotient.arcCount = 5 := rfl

private theorem parallelDiamond_flat : parallelDiamondQuotient.IsFlat := by
  have arc01 : parallelDiamondQuotient.HasQuotientArc ⟨0, by decide⟩ ⟨1, by decide⟩ :=
    ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by decide, rfl⟩
  have arc02 : parallelDiamondQuotient.HasQuotientArc ⟨0, by decide⟩ ⟨2, by decide⟩ :=
    ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, by decide, rfl⟩
  have arc13 : parallelDiamondQuotient.HasQuotientArc ⟨1, by decide⟩ ⟨3, by decide⟩ :=
    ⟨⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, by decide, rfl⟩
  have arc23 : parallelDiamondQuotient.HasQuotientArc ⟨2, by decide⟩ ⟨3, by decide⟩ :=
    ⟨⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩, by decide, rfl⟩
  constructor
  · intro v
    rcases v with ⟨_ | _ | _ | _ | k, hv⟩
    · exact AvoidPath.refl _ not_false
    · exact AvoidPath.step _ _ _ not_false arc01 (AvoidPath.refl _ not_false)
    · exact AvoidPath.step _ _ _ not_false arc02 (AvoidPath.refl _ not_false)
    · exact AvoidPath.step _ _ _ not_false arc01
        (AvoidPath.step _ _ _ not_false arc13 (AvoidPath.refl _ not_false))
    · exfalso
      have : k + 4 < 4 := hv
      omega
  · intro u v hu hvu
    have h01 : parallelDiamondQuotient.root ≠ ⟨1, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h02 : parallelDiamondQuotient.root ≠ ⟨2, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h03 : parallelDiamondQuotient.root ≠ ⟨3, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h12 : (⟨1, by decide⟩ : Vertex parallelDiamondQuotient) ≠ ⟨2, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h13 : (⟨1, by decide⟩ : Vertex parallelDiamondQuotient) ≠ ⟨3, by decide⟩ := Fin.ne_of_val_ne (by decide)
    have h23 : (⟨2, by decide⟩ : Vertex parallelDiamondQuotient) ≠ ⟨3, by decide⟩ := Fin.ne_of_val_ne (by decide)
    rcases u with ⟨_ | _ | _ | _ | ku, huLt⟩
    · exact (hu rfl).elim
    · have hu1 : (⟨0 + 1, huLt⟩ : Vertex parallelDiamondQuotient) = ⟨1, by decide⟩ := rfl
      rw [hu1]
      rcases v with ⟨_ | _ | _ | _ | kv, hvLt⟩
      · exact AvoidPath.refl _ h01
      · exact (hvu rfl).elim
      · exact AvoidPath.step _ _ _ h01 arc02 (AvoidPath.refl _ (Ne.symm h12))
      · exact AvoidPath.step _ _ _ h01 arc02
          (AvoidPath.step _ _ _ (Ne.symm h12) arc23 (AvoidPath.refl _ (Ne.symm h13)))
      · exfalso; have : kv + 4 < 4 := hvLt; omega
    · have hu2 : (⟨0 + 1 + 1, huLt⟩ : Vertex parallelDiamondQuotient) = ⟨2, by decide⟩ := rfl
      rw [hu2]
      rcases v with ⟨_ | _ | _ | _ | kv, hvLt⟩
      · exact AvoidPath.refl _ h02
      · exact AvoidPath.step _ _ _ h02 arc01 (AvoidPath.refl _ h12)
      · exact (hvu rfl).elim
      · exact AvoidPath.step _ _ _ h02 arc01
          (AvoidPath.step _ _ _ h12 arc13 (AvoidPath.refl _ (Ne.symm h23)))
      · exfalso; have : kv + 4 < 4 := hvLt; omega
    · have hu3 : (⟨0 + 1 + 1 + 1, huLt⟩ : Vertex parallelDiamondQuotient) = ⟨3, by decide⟩ := rfl
      rw [hu3]
      rcases v with ⟨_ | _ | _ | _ | kv, hvLt⟩
      · exact AvoidPath.refl _ h03
      · exact AvoidPath.step _ _ _ h03 arc01 (AvoidPath.refl _ h13)
      · exact AvoidPath.step _ _ _ h03 arc02 (AvoidPath.refl _ h23)
      · exact (hvu rfl).elim
      · exfalso; have : kv + 4 < 4 := hvLt; omega
    · exfalso; have : ku + 4 < 4 := huLt; omega

private theorem parallelDiamond_index_check :
    ∃ w : WordColumns (OracleContract.wordBits 5 4 0),
      SerializedProperLossIndex parallelDiamondQuotient w := by
  have large : 3 ≤ parallelDiamondQuotient.vertexCount := by decide
  let t := ForestPreparedBuild.orderRanks parallelDiamondOrder (by decide)
  have covers : ∀ v : Vertex parallelDiamondQuotient, ∃ i : Fin 4,
      orderedVertexAt parallelDiamondOrder parallelDiamond_order_size i = v := by
    intro v
    refine ⟨v, ?_⟩
    rcases v with ⟨_ | _ | _ | _ | k, hv⟩ <;> first | rfl | (exfalso; have : k + 4 < 4 := hv; omega)
  have topo : ForestPreparedBuild.IsTopologicalOrder parallelDiamondOrder parallelDiamond_order_size := by
    intro i j ⟨e, he, hhead⟩
    have hord (k : Fin 4) : (orderedVertexAt parallelDiamondOrder parallelDiamond_order_size k).val = k.val := by
      rcases k with ⟨_ | _ | _ | _ | m, hm⟩ <;> first | rfl | (exfalso; have : m + 4 < 4 := hm; omega)
    have hheadVal : e.head.val = j.val := (congrArg Fin.val hhead).trans (hord j)
    have out0 : parallelDiamondQuotient.outArcs ⟨0, by decide⟩ =
        [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩] := rfl
    have out1 : parallelDiamondQuotient.outArcs ⟨1, by decide⟩ =
        [⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, ⟨⟨3, by decide⟩, ⟨4, by decide⟩⟩] := rfl
    have out2 : parallelDiamondQuotient.outArcs ⟨2, by decide⟩ =
        [⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩] := rfl
    have out3 : parallelDiamondQuotient.outArcs ⟨3, by decide⟩ = [] := rfl
    change i.val < j.val
    rcases i with ⟨_ | _ | _ | _ | ki, hi⟩
    · have ho : orderedVertexAt parallelDiamondOrder parallelDiamond_order_size ⟨0, hi⟩ = ⟨0, by decide⟩ := rfl
      rw [ho, out0] at he
      rcases List.mem_cons.mp he with rfl | he
      · change (0 : Nat) < j.val; rw [← hheadVal]; decide
      · rcases List.mem_cons.mp he with rfl | he
        · change (0 : Nat) < j.val; rw [← hheadVal]; decide
        · cases he
    · have ho : orderedVertexAt parallelDiamondOrder parallelDiamond_order_size ⟨0 + 1, hi⟩ = ⟨1, by decide⟩ := rfl
      rw [ho, out1] at he
      rcases List.mem_cons.mp he with rfl | he
      · change (1 : Nat) < j.val; rw [← hheadVal]; decide
      · rcases List.mem_cons.mp he with rfl | he
        · change (1 : Nat) < j.val; rw [← hheadVal]; decide
        · cases he
    · have ho : orderedVertexAt parallelDiamondOrder parallelDiamond_order_size ⟨0 + 1 + 1, hi⟩ = ⟨2, by decide⟩ := rfl
      rw [ho, out2] at he
      rcases List.mem_cons.mp he with rfl | he
      · change (2 : Nat) < j.val; rw [← hheadVal]; decide
      · cases he
    · have ho : orderedVertexAt parallelDiamondOrder parallelDiamond_order_size ⟨0 + 1 + 1 + 1, hi⟩ = ⟨3, by decide⟩ := rfl
      rw [ho, out3] at he
      cases he
    · exfalso; have : ki + 4 < 4 := hi; omega
  let rank := PaperB.KahnDecreasing.readRank t
  have inc := ForestPreparedBuild.orderRanks_increasing parallelDiamondOrder
    parallelDiamond_order_size (by decide)
  have rarc := ForestPreparedBuild.orderRanks_rankArc parallelDiamondOrder
    parallelDiamond_order_size (by decide) covers topo
  let r := ForestPreparedBuild.readerForWords parallelDiamondOrder parallelDiamond_order_size
    rank inc covers rarc parallelDiamond_flat large
  exact ⟨packWordColumns r (local_word_columns_fit 4),
    packWordColumns_isSerializedProperLossIndex r (local_word_columns_fit 4)⟩

private def repeatedKeyQuotient : LabelledQuotient where
  origVertexCount := 5
  vertexCount := 5
  root := ⟨0, by decide⟩
  adj := #[
    [⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩],
    [⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, ⟨⟨4, by decide⟩, ⟨1, by decide⟩⟩],
    [⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩, ⟨⟨4, by decide⟩, ⟨2, by decide⟩⟩],
    [],
    []
  ]
  adj_size := rfl

private theorem repeatedKey_collect_has_duplicate (rows : ForestDictionary.Rows repeatedKeyQuotient) :
    (ForestDictionary.collect rows orderedPairCode).length = 2 ∧
    (ForestDictionary.packedDictionary rows orderedPairCode).size = 1 := by
  let v0 : Vertex repeatedKeyQuotient := ⟨0, by decide⟩
  let v1 : Vertex repeatedKeyQuotient := ⟨1, by decide⟩
  let v2 : Vertex repeatedKeyQuotient := ⟨2, by decide⟩
  let v3 : Vertex repeatedKeyQuotient := ⟨3, by decide⟩
  let v4 : Vertex repeatedKeyQuotient := ⟨4, by decide⟩
  have hrow0 : rows.row v0 = [] := by
    cases h : rows.row v0 with
    | nil => rfl
    | cons u us =>
      have hu := ((rows.spec v0).cover u).mp (h ▸ List.Mem.head _)
      rcases hu with ⟨e, he, hhead⟩
      rcases u with ⟨_ | _ | _ | _ | _ | k, hk⟩
      · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · rcases List.mem_cons.mp he with rfl | he
          · exact absurd (congrArg Fin.val hhead) (by decide)
          · cases he
      · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · rcases List.mem_cons.mp he with rfl | he
          · exact absurd (congrArg Fin.val hhead) (by decide)
          · cases he
      · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
        rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · rcases List.mem_cons.mp he with rfl | he
          · exact absurd (congrArg Fin.val hhead) (by decide)
          · cases he
      · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
        cases he
      · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
        cases he
      · exfalso; have : k + 5 < 5 := hk; omega
  have hkey0 : ForestHead.preparedKey repeatedKeyQuotient (rows.row v0) = none := by
    rw [hrow0]
    rfl
  have singleton_root_key : ∀ (y : Vertex repeatedKeyQuotient)
      (hm0 : v0 ∈ rows.row y) (honly : ∀ u ∈ rows.row y, u = v0),
      ForestHead.preparedKey repeatedKeyQuotient (rows.row y) = none := by
    intro y hm0 honly
    have hnodup := (rows.spec y).nodup
    have hy : rows.row y = [v0] := by
      cases hr : rows.row y with
      | nil => simp [hr] at hm0
      | cons a rest =>
        have ha : a = v0 := honly a (by simp [hr])
        subst a
        cases rest with
        | nil => rfl
        | cons b rest2 =>
          exfalso
          rw [hr] at hnodup
          have hna := (List.pairwise_cons.mp hnodup).1
          have hb : b = v0 := honly b (by simp [hr])
          exact hna b (by simp) hb.symm
    rw [hy]
    rfl
  have hkey1 : ForestHead.preparedKey repeatedKeyQuotient (rows.row v1) = none := by
    refine singleton_root_key v1
      (((rows.spec v1).cover v0).mpr ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by decide, rfl⟩) ?_
    intro u hu
    obtain ⟨e, he, hhead⟩ := ((rows.spec v1).cover u).mp hu
    rcases u with ⟨_ | _ | _ | _ | _ | k, hk⟩
    · rfl
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd (congrArg Fin.val hhead) (by decide)
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd (congrArg Fin.val hhead) (by decide)
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he; cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he; cases he
    · exfalso; have : k + 5 < 5 := hk; omega
  have hkey2 : ForestHead.preparedKey repeatedKeyQuotient (rows.row v2) = none := by
    refine singleton_root_key v2
      (((rows.spec v2).cover v0).mpr ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, by decide, rfl⟩) ?_
    intro u hu
    obtain ⟨e, he, hhead⟩ := ((rows.spec v2).cover u).mp hu
    rcases u with ⟨_ | _ | _ | _ | _ | k, hk⟩
    · rfl
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd (congrArg Fin.val hhead) (by decide)
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd (congrArg Fin.val hhead) (by decide)
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he; cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he; cases he
    · exfalso; have : k + 5 < 5 := hk; omega
  have row_two_mem : ∀ (y : Vertex repeatedKeyQuotient)
      (hm1 : v1 ∈ rows.row y) (hm2 : v2 ∈ rows.row y)
      (honly : ∀ u ∈ rows.row y, u = v1 ∨ u = v2),
      ∃ q : CutPair repeatedKeyQuotient,
        ForestHead.preparedKey repeatedKeyQuotient (rows.row y) = some q ∧ orderedPairCode q = (1, 2) := by
    intro y hm1 hm2 honly
    have hnodup := (rows.spec y).nodup
    have h12 : v1 ≠ v2 := by decide
    have hcases : rows.row y = [v1, v2] ∨ rows.row y = [v2, v1] := by
      cases hr : rows.row y with
      | nil => simp [hr] at hm1
      | cons a rest =>
        rw [hr] at hnodup
        have hna := List.pairwise_cons.mp hnodup
        cases hr2 : rest with
        | nil =>
          subst rest
          have h1 : v1 = a := by simpa [hr] using hm1
          have h2 : v2 = a := by simpa [hr] using hm2
          exact (h12 (h1.trans h2.symm)).elim
        | cons b rest2 =>
          have hnb := List.pairwise_cons.mp (show List.Pairwise (· ≠ ·) (b :: rest2) from hr2 ▸ hna.2)
          cases hr3 : rest2 with
          | cons c rest3 =>
            exfalso
            have hc := honly c (by simp [hr, hr2, hr3])
            have ha := honly a (by simp [hr])
            have hb := honly b (by simp [hr, hr2])
            have hab : a ≠ b := hna.1 b (by simp [hr2])
            have hac : a ≠ c := hna.1 c (by simp [hr2, hr3])
            have hbc : b ≠ c := hnb.1 c (by simp [hr3])
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
              first | exact hab rfl | exact hac rfl | exact hbc rfl
          | nil =>
            have ha := honly a (by simp [hr])
            have hb := honly b (by simp [hr, hr2])
            have hab : a ≠ b := hna.1 b (by simp [hr2])
            rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
            · exact (hab rfl).elim
            · exact Or.inl rfl
            · exact Or.inr rfl
            · exact (hab rfl).elim
    rcases hcases with heq | heq <;> rw [heq]
    · exact ⟨⟨v1, v2, by decide, by decide, by decide⟩, by decide, rfl⟩
    · exact ⟨⟨v1, v2, by decide, by decide, by decide⟩, by decide, rfl⟩
  have h1_3 : v1 ∈ rows.row v3 :=
    ((rows.spec v3).cover v1).mpr ⟨⟨⟨3, by decide⟩, ⟨1, by decide⟩⟩, by decide, rfl⟩
  have h2_3 : v2 ∈ rows.row v3 :=
    ((rows.spec v3).cover v2).mpr ⟨⟨⟨3, by decide⟩, ⟨2, by decide⟩⟩, by decide, rfl⟩
  have honly3 : ∀ u ∈ rows.row v3, u = v1 ∨ u = v2 := by
    intro u hu
    obtain ⟨e, he, hhead⟩ := ((rows.spec v3).cover u).mp hu
    rcases u with ⟨_ | _ | _ | _ | _ | k, hk⟩
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd (congrArg Fin.val hhead) (by decide)
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · cases he
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      cases he
    · exfalso; have : k + 5 < 5 := hk; omega
  have h1_4 : v1 ∈ rows.row v4 :=
    ((rows.spec v4).cover v1).mpr ⟨⟨⟨4, by decide⟩, ⟨1, by decide⟩⟩, by decide, rfl⟩
  have h2_4 : v2 ∈ rows.row v4 :=
    ((rows.spec v4).cover v2).mpr ⟨⟨⟨4, by decide⟩, ⟨2, by decide⟩⟩, by decide, rfl⟩
  have honly4 : ∀ u ∈ rows.row v4, u = v1 ∨ u = v2 := by
    intro u hu
    obtain ⟨e, he, hhead⟩ := ((rows.spec v4).cover u).mp hu
    rcases u with ⟨_ | _ | _ | _ | _ | k, hk⟩
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact absurd (congrArg Fin.val hhead) (by decide)
      · rcases List.mem_cons.mp he with rfl | he
        · exact absurd (congrArg Fin.val hhead) (by decide)
        · cases he
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      cases he
    · simp only [LabelledQuotient.outArcs, repeatedKeyQuotient] at he
      cases he
    · exfalso; have : k + 5 < 5 := hk; omega
  obtain ⟨q3, hq3, hc3⟩ := row_two_mem v3 h1_3 h2_3 honly3
  obtain ⟨q4, hq4, hc4⟩ := row_two_mem v4 h1_4 h2_4 honly4
  have hfinRange : List.finRange 5 = [v0, v1, v2, v3, v4] := rfl
  have hcollect : ForestDictionary.collect rows orderedPairCode = [(1, 2), (1, 2)] := by
    unfold ForestDictionary.collect ForestDictionary.collectFrom
    change List.filterMap (fun y => (ForestHead.preparedKey repeatedKeyQuotient (rows.row y)).map orderedPairCode)
      (List.finRange 5) = [(1, 2), (1, 2)]
    rw [hfinRange]
    simp [List.filterMap, hkey0, hkey1, hkey2, hq3, hq4, hc3, hc4]
  constructor
  · rw [hcollect]
    rfl
  · obtain ⟨hsorted, hmem, _⟩ := ForestDictionary.packedDictionary_spec rows orderedPairCode
    let d := ForestDictionary.packedDictionary rows orderedPairCode
    have h12mem : (1, 2) ∈ d.toList := (hmem (1, 2)).mpr ⟨v3, q3, hq3, hc3⟩
    have hpos : 0 < d.size := by
      cases hs : d.size with
      | zero =>
        have hnil : d.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using hs)
        rw [hnil] at h12mem
        cases h12mem
      | succ _ => omega
    have hle1 : d.size ≤ 1 := by
      by_cases hge2 : 2 ≤ d.size
      · exfalso
        have h0 : 0 < (ForestDictionary.packedDictionary rows orderedPairCode).size := by
          change 0 < d.size; omega
        have h1 : 1 < (ForestDictionary.packedDictionary rows orderedPairCode).size := by
          change 1 < d.size; omega
        have hlt := hsorted 0 1 h0 h1
        have hm0 : d[0] ∈ d.toList := Array.mem_toList_iff.mpr (Array.getElem_mem h0)
        have hm1 : d[1] ∈ d.toList := Array.mem_toList_iff.mpr (Array.getElem_mem h1)
        obtain ⟨y0, q0, hq0, hc0⟩ := (hmem d[0]).mp hm0
        obtain ⟨y1, q1, hq1, hc1⟩ := (hmem d[1]).mp hm1
        have hq0eq : orderedPairCode q0 = (1, 2) := by
          rcases y0 with ⟨_ | _ | _ | _ | _ | k, hk⟩
          · change ForestHead.preparedKey repeatedKeyQuotient (rows.row v0) = some q0 at hq0
            rw [hkey0] at hq0; cases hq0
          · change ForestHead.preparedKey repeatedKeyQuotient (rows.row v1) = some q0 at hq0
            rw [hkey1] at hq0; cases hq0
          · change ForestHead.preparedKey repeatedKeyQuotient (rows.row v2) = some q0 at hq0
            rw [hkey2] at hq0; cases hq0
          · have : q0 = q3 := Option.some.inj (hq0.symm.trans hq3)
            subst q0; exact hc3
          · have : q0 = q4 := Option.some.inj (hq0.symm.trans hq4)
            subst q0; exact hc4
          · exfalso; have : k + 5 < 5 := hk; omega
        have hq1eq : orderedPairCode q1 = (1, 2) := by
          rcases y1 with ⟨_ | _ | _ | _ | _ | k, hk⟩
          · change ForestHead.preparedKey repeatedKeyQuotient (rows.row v0) = some q1 at hq1
            rw [hkey0] at hq1; cases hq1
          · change ForestHead.preparedKey repeatedKeyQuotient (rows.row v1) = some q1 at hq1
            rw [hkey1] at hq1; cases hq1
          · change ForestHead.preparedKey repeatedKeyQuotient (rows.row v2) = some q1 at hq1
            rw [hkey2] at hq1; cases hq1
          · have : q1 = q3 := Option.some.inj (hq1.symm.trans hq3)
            subst q1; exact hc3
          · have : q1 = q4 := Option.some.inj (hq1.symm.trans hq4)
            subst q1; exact hc4
          · exfalso; have : k + 5 < 5 := hk; omega
        have hd0 : d[0] = (1, 2) := hc0.symm.trans hq0eq
        have hd1 : d[1] = (1, 2) := hc1.symm.trans hq1eq
        rw [hd0, hd1] at hlt
        have hlt' := hlt (by decide)
        rcases hlt' with h | ⟨_, h⟩ <;> omega
      · omega
    change d.size = 1
    omega

private theorem memory_layout_fit_checks (n m : Nat) :
    rawInputCap m ≤ 3 * (n + m + 1) ∧
    rawWorkCap n m ≤ 32 * (n + m + 1) ∧
    sourceBase n m + (6 * n + 3) ≤ rawWorkCap n m ∧
    (6 * n + 3 + 2 * (n + 1)) + 5 * (n + 1) + 1 + (n + 1) ≤ sourceBase n m := by
  have hfin := finish_arena_before_source n m (n + 1) (6 * n + 3) (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨rawInputCap_le n m, rawWorkCap_le n m,
    sourceBase_plus_prefix_le n m (6 * n + 3) (Nat.le_refl _), hfin.1⟩

end CaseChecks

end PaperB.RamForestProgram.RawBuild
