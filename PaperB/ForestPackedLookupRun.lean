module

public import PaperB.ForestPackedAfterHit
public import PaperB.RamPairHitRow
public import PaperB.ForestBuildPackedWords

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.ForestSlimIndex
open PaperB.Machine (Word)
open PaperB.WordOps (zero)
open PaperB.RamProgram
open _root_.EX24.PreparedSweep

private def startPair {bits cap : Nat} (fit : cap ≤ 2 ^ bits)
    (a size b x y : Word bits) : RamProgram.State (ThreeCalls.layout bits cap fit) where
  regs := Array.ofFn fun i : Fin 16 =>
    if i = 7 then a else if i = 8 then size else if i = 9 then b
    else if i = 11 then x else if i = 12 then y else zero bits
  data := #[]
  pc := 0
  regs_size := by simp
  data_size := rfl

/-- Cache the header while checking the payload position. The counter
charges each attempted word access, including the header. -/
private def slotProbed {bits : Nat} (dict : Array (Word bits)) (i : Nat) :
    Nat × Nat :=
  CountedProbe.bindC (CountedProbe.read dict 0) fun header =>
    let base := FlatPairDictionary.slotBase ((header.map Fin.val).getD 0)
    if i < dict.size - base then
      CountedProbe.mapC (fun x => (x.map Fin.val).getD 0)
        (CountedProbe.read dict (base + i))
    else (0, 0)

private theorem slotProbed_spec {bits : Nat} (dict : Array (Word bits))
    (valid : FlatPairDictionary.Valid dict) (i : Nat) :
    (slotProbed dict i).1 = FlatPairDictionary.slotAt dict valid i ∧
      (slotProbed dict i).2 ≤ 2 := by
  unfold slotProbed CountedProbe.bindC CountedProbe.read CountedProbe.mapC
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

private def backProbed {bits : Nat} (w : BackWords bits) (i : Nat) :
    Option (Nat × Nat) × Nat :=
  CountedProbe.bindC (CountedProbe.read w.tagAndFirst i) fun a =>
    match a with
    | none => (none, 0)
    | some x =>
      CountedProbe.mapC (fun b => b.map fun y => (x.val, y.val))
        (CountedProbe.read w.second i)

private theorem backProbed_spec {bits : Nat} (w : BackWords bits) (i : Nat) :
    (backProbed w i).1 = w.read i ∧ (backProbed w i).2 ≤ 2 := by
  unfold backProbed BackWords.read CountedProbe.bindC CountedProbe.read CountedProbe.mapC
  cases w.tagAndFirst[i]? <;> simp

def WordColumns.afterHitProbed {bits : Nat} (w : WordColumns bits)
    (hit : Option Nat) (key : Nat × Nat) (v : Nat) : Bool × Nat :=
  match hit with
  | none => (false, 0)
  | some i =>
    CountedProbe.bindC (slotProbed w.dictionary i) fun a =>
      if a = 0 then (false, 0) else
      CountedProbe.bindC (backProbed w.back a) fun stored =>
        if stored = some key then w.knownProbed a v else (false, 0)

theorem WordColumns.afterHitProbed_spec {bits : Nat} (w : WordColumns bits)
    (valid : FlatPairDictionary.Valid w.dictionary)
    (hit : Option Nat) (key : Nat × Nat) (v : Nat) :
    (w.afterHitProbed hit key v).1 = w.afterHit valid hit key v ∧
      (w.afterHitProbed hit key v).2 ≤ 8 := by
  cases hit with
  | none => simp [WordColumns.afterHitProbed, WordColumns.afterHit]
  | some i =>
    obtain ⟨slotValue, slotCost⟩ := slotProbed_spec w.dictionary valid i
    unfold WordColumns.afterHitProbed WordColumns.afterHit CountedProbe.bindC
    simp only [slotValue]
    generalize FlatPairDictionary.slotAt w.dictionary valid i = a
    by_cases zero : a = 0
    · simp [zero]
      omega
    · obtain ⟨backValue, backCost⟩ := backProbed_spec w.back a
      by_cases eq : w.back.read a = some key <;>
        simp [zero, eq, backValue, WordColumns.knownProbed_exact] <;> omega

/-- Lookup from the prebuilt word image. The caller supplies a word-sized
fuel bound. The first counter measures search instructions and the second
measures accesses to retained banks outside the search program. -/
def WordColumns.keyedProbed {bits : Nat} (w : WordColumns bits)
    (valid : FlatPairDictionary.Valid w.dictionary) (one : 1 < 2 ^ bits)
    (fuel : Nat) (x y : Word bits) (v : Nat) : Option (Bool × Nat × Nat) :=
  let fit := Nat.le_of_lt valid.capacity
  let rows := FlatPairDictionary.rowCount w.dictionary
  have hrows : FlatPairDictionary.slotBase rows ≤ w.dictionary.size := valid.keysWithin
  let base : Word bits := ⟨FlatPairDictionary.secondBase rows, by
    have hc := valid.capacity
    unfold FlatPairDictionary.slotBase at hrows
    omega⟩
  let state := startPair fit ⟨1, one⟩ ⟨rows, by
    have hc := valid.capacity
    unfold FlatPairDictionary.slotBase at hrows
    omega⟩ base x y
  let input : RamProgram.Input (ThreeCalls.layout bits w.dictionary.size fit) := ⟨w.dictionary, rfl⟩
  (run (ThreeCalls.EqualityTail.checkedProgram fit one (ThreeCalls.concreteSetup bits one))
    input fuel state).map fun out =>
      let hit := if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
        then some (ThreeCalls.setupReg out.finalState 3).val else none
      let (answer, probes) := w.afterHitProbed hit (x.val + 1, y.val) v
      (answer, out.executed, 1 + probes)

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

/-- The existing fixed search program runs on the dictionary of the actual
word image. The remaining constant-size calculation reads its other banks. -/
theorem packed_dictionary_run {bits : Nat}
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (q : CutPair H) (v : Nat) :
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    let fit := Nat.le_of_lt rep.valid.capacity
    have one : 1 < 2 ^ bits := by omega
    let A := FlatPairDictionary.firstSlice w.dictionary rep.valid
    let B := FlatPairDictionary.secondSlice w.dictionary rep.valid
    let x : Word bits := ⟨q.fst.val, by have := q.fst.isLt; omega⟩
    let y : Word bits := ⟨q.snd.val, by have := q.snd.isLt; omega⟩
    let state := startPair fit A.base ⟨A.len, by have h := A.fits; omega⟩ B.base x y
    let input :
        RamProgram.Input (ThreeCalls.layout bits w.dictionary.size fit) :=
      ⟨w.dictionary, rfl⟩
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ out,
      run (ThreeCalls.EqualityTail.checkedProgram fit one (ThreeCalls.concreteSetup bits one))
          input fuel state = some out ∧
      out.executed ≤ fuel ∧
      (let hit := if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
                  then some (ThreeCalls.setupReg out.finalState 3).val else none
       w.afterHit rep.valid hit (encodeBackPair (some q)) v = (ofOrderedReader r).contains q v) := by
  intro w rep fit one A B x y state input fuel
  let narrow :
      RamProgram.Input (Predecessor.layout bits w.dictionary.size fit) :=
    ⟨w.dictionary, rfl⟩
  let c := FlatPairDictionary.workerColumns narrow.words rep
  have regs (i : Fin 16) :
      ThreeCalls.setupReg state i =
        if i = 7 then A.base else if i = 8 then (⟨A.len, by have h := A.fits; omega⟩ : Word bits)
        else if i = 9 then B.base else if i = 11 then x else if i = 12 then y else zero bits := by
    unfold ThreeCalls.setupReg state startPair
    simp only [Array.getElem_ofFn]
  obtain ⟨out, hrun, _, _, hhit⟩ :=
    ThreeCalls.pair_search_correct_from_pc0_with_index (i := narrow) (j := input) fit one c
      (dict_sorted r) x y rfl state rfl
      (by rw [regs]; rfl) (by rw [regs]; rfl) (by rw [regs]; rfl)
      (by rw [regs]; rfl) (by rw [regs]; rfl)
      (by rw [regs]; rfl) (by rw [regs]; rfl)
  have hsize := ofOrderedReader_dict_size_le r
  have hlog : Nat.log2 ((ofOrderedReader r).dict.size + 1) ≤
      Nat.log2 (H.vertexCount + 1) := by
    apply (Nat.le_log2 (by omega : H.vertexCount + 1 ≠ 0)).mpr
    exact Nat.le_trans (Nat.log2_self_le (by omega)) (Nat.add_le_add_right hsize 1)
  have wider :
      33 * (Nat.log2 ((ofOrderedReader r).dict.size + 1) + 1) + 39 ≤ fuel := by
    dsimp only [fuel, OracleContract.L]
    omega
  have hrun' := run_stable_of_le wider hrun
  refine ⟨out, hrun', run_executed_le hrun', ?_⟩
  dsimp only at hhit ⊢
  rw [show (if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
      then some (ThreeCalls.setupReg out.finalState 3).val else none) =
      (PairLookup.lookup (ofOrderedReader r).dict (x.val, y.val)).1 by
      simpa only [decide_eq_true_eq] using hhit]
  exact packWordColumns_afterHit r cap q v

/-- The executable query returns the source answer. Its fixed search
has logarithmic fuel and the remaining accesses use at most nine probes. -/
theorem packWordColumns_keyedProbed {bits : Nat}
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (q : CutPair H) (v : Nat) :
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    have one : 1 < 2 ^ bits := by omega
    let x : Word bits := ⟨q.fst.val, by have := q.fst.isLt; omega⟩
    let y : Word bits := ⟨q.snd.val, by have := q.snd.isLt; omega⟩
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ steps probes,
      w.keyedProbed rep.valid one fuel x y v =
        some ((ofOrderedReader r).contains q v, steps, probes) ∧
      steps ≤ fuel ∧ probes ≤ 9 := by
  intro w rep one x y fuel
  obtain ⟨out, hrun, hwork, hanswer⟩ := packed_dictionary_run r cap q v
  let hit := if ThreeCalls.setupReg out.finalState 0 = (⟨1, one⟩ : Word bits)
    then some (ThreeCalls.setupReg out.finalState 3).val else none
  obtain ⟨tailAnswer, tailCost⟩ := w.afterHitProbed_spec rep.valid hit
    (encodeBackPair (some q)) v
  refine ⟨out.executed, 1 + (w.afterHitProbed hit (encodeBackPair (some q)) v).2,
    ?_, hwork, by omega⟩
  unfold WordColumns.keyedProbed
  dsimp only
  change run (ThreeCalls.EqualityTail.checkedProgram (Nat.le_of_lt rep.valid.capacity)
      one (ThreeCalls.concreteSetup bits one)) ⟨w.dictionary, rfl⟩ fuel
      (startPair (Nat.le_of_lt rep.valid.capacity) ⟨1, one⟩
        ⟨FlatPairDictionary.rowCount w.dictionary, _⟩
        ⟨FlatPairDictionary.secondBase (FlatPairDictionary.rowCount w.dictionary), _⟩ x y)
      = some out at hrun
  rw [hrun]
  change some ((w.afterHitProbed hit (encodeBackPair (some q)) v).1, _, _) = _
  rw [tailAnswer]
  exact congrArg (fun b => some (b, out.executed,
    1 + (w.afterHitProbed hit (encodeBackPair (some q)) v).2)) hanswer

end PaperB.RetainedProperLoss

namespace PaperB.ForestPreparedBuild

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.RetainedProperLoss
open PaperB.Machine (Word)
open _root_.EX24.PreparedSweep

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

/-- Run the actual keyed query on the returned prebuilt image. The separate
counters record fixed-program instructions and other word probes. -/
theorem buildWords_keyedProbed_spec (large : 3 ≤ H.vertexCount) (q : CutPair H) (v : Vertex H) :
    let r := readerForWords data size_data rank increasing covers rankArc flat large
    let cap := local_word_columns_fit H.vertexCount
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    have one : 1 < 2 ^ OracleContract.wordBits 5 H.vertexCount 0 := by omega
    let x : Word (OracleContract.wordBits 5 H.vertexCount 0) :=
      ⟨q.fst.val, by have := q.fst.isLt; omega⟩
    let y : Word (OracleContract.wordBits 5 H.vertexCount 0) :=
      ⟨q.snd.val, by have := q.snd.isLt; omega⟩
    let fuel := 33 * OracleContract.L H.vertexCount + 39
    ∃ answer steps probes,
      buildWords data size_data rank increasing covers rankArc flat = some w ∧
      w.keyedProbed rep.valid one fuel x y v.val = some (answer, steps, probes) ∧
      (answer = true ↔ q.fst < q.snd ∧ H.ProperLoss q v) ∧
      steps ≤ fuel ∧ probes ≤ 9 := by
  intro r cap w rep one x y fuel
  obtain ⟨steps, probes, hquery, hsteps, hprobes⟩ :=
    packWordColumns_keyedProbed r cap q v.val
  have spec := query_iff data size_data rank increasing covers rankArc flat q v
  rw [build_of_large_readerForWords data size_data rank increasing covers rankArc flat large] at spec
  exact ⟨(ofOrderedReader r).contains q v.val, steps, probes,
    buildWords_of_large data size_data rank increasing covers rankArc flat large,
    hquery, spec, hsteps, hprobes⟩

/-- A slot already obtained for the pair needs only the four interval
accesses. Its checked-slot premise is supplied by pair lookup. -/
theorem buildWords_knownProbed_spec (large : 3 ≤ H.vertexCount)
    (q : CutPair H) (a : Nat) (v : Vertex H) :
    let r := readerForWords data size_data rank increasing covers rankArc flat large
    let cap := local_word_columns_fit H.vertexCount
    let w := packWordColumns r cap
    checkedHit r q = some a →
      buildWords data size_data rank increasing covers rankArc flat = some w ∧
      (w.knownProbed a v.val).2 = 4 ∧
      ((w.knownProbed a v.val).1 = true ↔ q.fst < q.snd ∧ H.ProperLoss q v) := by
  intro r cap w ha
  have read := packWordColumns_knownProbed r cap a v.val
  have spec := query_iff data size_data rank increasing covers rankArc flat q v
  rw [build_of_large_readerForWords data size_data rank increasing covers rankArc flat large]
    at spec
  refine ⟨buildWords_of_large data size_data rank increasing covers rankArc flat large,
    congrArg Prod.snd read, ?_⟩
  change (ofOrderedReader r).contains q v.val = true ↔ _ at spec
  unfold Columns.contains at spec
  change (match checkedHit r q with
    | none => false
    | some slot => (ofOrderedReader r).known slot v.val) = true ↔ _ at spec
  rw [ha] at spec
  rw [read]
  exact spec

end PaperB.ForestPreparedBuild
