module

public import PaperB.RamForestParentFinish
public import PaperB.ForestPackedLookupRun
public import PaperB.ForestEndpointFinish

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.RamForestProgram.Finish

open PaperB.RamProgram PaperB.RamProgram.FixedROM
open PaperB.Machine (Word)
open PaperB.RetainedProperLoss (WordColumns)
open PaperB.ForestLayout (bucketChildLists)
open PaperB.LabelledQuotient (ValidDepthTree)

variable {bits n inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

/-- The banks produced by the earlier quotient sweep, in the same order
as WordColumns.sealBanks. The two interval banks follow this prefix. -/
def packedPrefix (w : WordColumns bits) : Array (Word bits) :=
  w.dictionary ++ w.back.tagAndFirst ++ w.back.second ++ w.labels

def packedPayload (w : WordColumns bits) : Array (Word bits) :=
  packedPrefix w ++ w.entry ++ w.stop

theorem packedPayload_size (w : WordColumns bits) :
    (packedPayload w).size = w.wordCount := by
  simp only [packedPayload, packedPrefix, WordColumns.wordCount, Array.size_append]

private theorem wordOption_ext {a b : Option (Word bits)}
    (h : a.map Fin.val = b.map Fin.val) : a = b := by
  cases a <;> cases b
  · rfl
  · cases h
  · cases h
  · exact congrArg some (Fin.ext (Option.some.inj h))

/-- Fuse both interval columns with the four retained banks. The result
gives exact word equality across the whole retained payload. No packed
endpoint word is supplied to the machine as input. -/
theorem run_packed_payload_finish (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n} {depth : Fin n → Nat}
    (tree : ValidDepthTree root parent depth)
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) (children : a.children ≤ n)
    (s : State L) (ctrl : Control a s) (rootVal : (reg s cmd).val = root.val)
    (parents : ParentAt a parent s.data) (w : WordColumns bits)
    (placement : a.base = (packedPrefix w).size + 2 * n)
    (prefixAt : ∀ j < (packedPrefix w).size, s.data[j]? = (packedPrefix w)[j]?)
    (entrySize : w.entry.size = n) (stopSize : w.stop.size = n)
    (entrySpec : ∀ j : Nat, (w.entry[j]?).map Fin.val =
      (PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)).entries[j]?)
    (stopSpec : ∀ j : Nat, (w.stop[j]?).map Fin.val =
      (PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)).ends[j]?) :
    ∃ t trace work,
      t.data.extract 0 a.base = packedPayload w ∧ work ≤ 106 * n + 44 ∧
      run parentFinishProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace parentFinishProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  have reserved : 2 * n ≤ a.base := by omega
  obtain ⟨t, trace, work, entry, stop, prefixKept, bound, exec, replay, peak⟩ :=
    run_parent_finish input tree mass children reserved s ctrl rootVal parents
  have start : a.base - 2 * n = (packedPrefix w).size := by omega
  have first (i : Fin n) : t.data[(packedPrefix w).size + i.val]? = w.entry[i.val]? := by
    apply wordOption_ext
    rw [entrySpec]
    rw [← start]
    exact entry i
  have second (i : Fin n) : t.data[(packedPrefix w).size + n + i.val]? = w.stop[i.val]? := by
    apply wordOption_ext
    rw [stopSpec]
    rw [← start]
    exact stop i
  have contents (j : Nat) (hj : j < a.base) : t.data[j]? = (packedPayload w)[j]? := by
    unfold packedPayload
    by_cases eTail : j < (packedPrefix w).size + n
    · rw [Array.getElem?_append_left (by rw [Array.size_append, entrySize]; exact eTail)]
      by_cases eHead : j < (packedPrefix w).size
      · rw [Array.getElem?_append_left eHead, prefixKept _ (by rwa [start]), prefixAt j eHead]
      · rw [Array.getElem?_append_right (by omega)]
        let i : Fin n := ⟨j - (packedPrefix w).size, by omega⟩
        have address : (packedPrefix w).size + i.val = j := by dsimp only [i]; omega
        have seen := first i
        rw [address] at seen
        exact seen
    · rw [Array.getElem?_append_right (by rw [Array.size_append, entrySize]; omega)]
      rw [Array.size_append, entrySize]
      let i : Fin n := ⟨j - ((packedPrefix w).size + n), by omega⟩
      have address : (packedPrefix w).size + n + i.val = j := by dsimp only [i]; omega
      have seen := second i
      rw [address] at seen
      exact seen
  have aFits : a.base ≤ t.data.size := by
    have room := a.room
    rw [t.data_size]
    change a.base ≤ workCap
    omega
  refine ⟨t, trace, work, ?_, bound, exec, replay, peak⟩
  apply Array.ext
  · rw [Array.size_extract, Nat.min_eq_left aFits, Nat.sub_zero]
    simp only [packedPayload, Array.size_append, entrySize, stopSize]
    omega
  · intro i hExtract hPacked
    have lt : i < a.base := by
      rw [Array.size_extract, Nat.min_eq_left aFits, Nat.sub_zero] at hExtract
      exact hExtract
    have get := contents i lt
    rw [getElem?_pos t.data i (by omega), getElem?_pos (packedPayload w) i hPacked] at get
    simp only [Array.getElem_extract, Nat.zero_add]
    exact Option.some.inj get

private abbrev copyLayout (bits inputCap workCap : Nat)
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :=
  PaperB.RamSliceCopy.layout bits inputCap workCap hi hw

private def prefixRegisters : Fin 7 → Fin 15
  | 0 => registers.ptr
  | 1 => registers.remain
  | 2 => registers.childBase
  | 3 => registers.zero
  | 4 => clk
  | 5 => registers.value
  | 6 => registers.tmp

private theorem prefixRegisters_inj : ∀ {i j}, prefixRegisters i = prefixRegisters j → i = j :=
  fun {i j} => (by decide : ∀ i j : Fin 7, prefixRegisters i = prefixRegisters j → i = j) i j

private def prefixCopyCode (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  embedProgram prefixRegisters (PaperB.RamSliceCopy.standalone bits inputCap workCap hi hw)

private def prefixCopyPhase : Phase L :=
  Phase.ofLast (prefixCopyCode hi hw) 7
    (@size_embedProgram bits (copyLayout bits inputCap workCap hi hw) L prefixRegisters _)
    (by unfold prefixCopyCode embedProgram; rw [Array.getElem?_map]; rfl)
    (by unfold prefixCopyCode embedProgram; rw [Array.toList_map]; rfl)

/-- The producer supplies a slice of packed prefix words. These are the
input parameters of the physical copy stage. -/
structure PrefixCopyInput (s : State L) (source len : Nat) : Prop where
  cursor : (reg s registers.ptr).val = 0
  src : (reg s registers.childBase).val = source
  unit : (reg s clk).val = 1
  count : (reg s registers.remain).val = len

private theorem prefixCopy (input : Input L) {a : Arena bits workCap n}
    (s : State L) (ctrl : Control a s) (w : WordColumns bits)
    (source : Nat) (fits : source + (packedPrefix w).size ≤ workCap)
    (apart : (packedPrefix w).size ≤ source) (prefixBound : (packedPrefix w).size ≤ a.base)
    (params : PrefixCopyInput s source (packedPrefix w).size)
    (physical : ∀ j < (packedPrefix w).size, s.data[source + j]? = (packedPrefix w)[j]?) :
    ∃ t, run (prefixCopyCode hi hw) input (7 * (packedPrefix w).size + 2) (Phase.initial s) =
        some ⟨t, 7 * (packedPrefix w).size + 2⟩ ∧
      (∀ j < (packedPrefix w).size, t.data[j]? = (packedPrefix w)[j]?) ∧
      (∀ j, a.base ≤ j → t.data[j]? = s.data[j]?) ∧ Control a t ∧ reg t cmd = reg s cmd := by
  let S := copyLayout bits inputCap workCap hi hw
  let small : State S :=
    ⟨Array.ofFn (fun i : Fin 7 => reg s (prefixRegisters i)), s.data, 0,
      Array.size_ofFn, s.data_size⟩
  let readOnly : Input S := ⟨input.words, input.size_eq⟩
  have agree : ArenaAgreement prefixRegisters s small (Phase.initial s) := by
    refine ⟨rfl, rfl, ?_, fun _ _ => rfl⟩
    intro r
    have idx : r.val < (Array.ofFn (fun i : Fin 7 => reg s (prefixRegisters i))).size := by
      rw [Array.size_ofFn]; exact r.isLt
    change (Array.ofFn (fun i : Fin 7 => reg s (prefixRegisters i)))[r.val]'idx = _
    rw [Array.getElem_ofFn]
    exact congrArg (fun i : Fin 7 => reg s (prefixRegisters i)) (Fin.ext rfl)
  have wordFit := a.wordFits
  let x : PaperB.RamSliceCopy.Transfer bits workCap :=
    ⟨source, 0, (packedPrefix w).size, fits, by omega, Or.inl (by omega), by omega⟩
  have cfg : PaperB.RamSliceCopy.Invariant x small.data 0 0 small :=
    ⟨rfl, (congrArg Fin.val (agree.reg_eq (0 : Fin 7))).trans params.cursor,
      (congrArg Fin.val (agree.reg_eq (1 : Fin 7))).trans params.count,
      (congrArg Fin.val (agree.reg_eq (2 : Fin 7))).trans params.src,
      (congrArg Fin.val (agree.reg_eq (3 : Fin 7))).trans ctrl.zero,
      (congrArg Fin.val (agree.reg_eq (4 : Fin 7))).trans params.unit, SliceCopy.Prefix.zero _ _ _⟩
  obtain ⟨t, _, hr, copied, _, _, target⟩ :=
    PaperB.RamSliceCopy.standalone_exact_with_target readOnly x small cfg
  obtain ⟨work, atHalt, route, stop, countEq⟩ := run_has_steps_then_halt hr
  obtain ⟨_, wide, steps, halt, finish⟩ :=
    route.embedRegisterFramesWithStore_thenHalt stop prefixRegisters_inj
      (show readOnly.words = input.words from rfl) agree
  have execution := steps.halts halt
  change 7 * (packedPrefix w).size + 2 = work + 1 at countEq
  rw [← countEq] at execution
  have mem := finish.data_eq
  change t.data = wide.data at mem
  change SliceCopy.Prefix s.data t.data source 0 (packedPrefix w).size at copied
  rw [mem] at copied
  have saved (r : Fin 15) (outside : ∀ q : Fin 7, prefixRegisters q ≠ r) :
      (reg wide r).val = (reg s r).val := congrArg Fin.val (finish.frame r outside)
  have wideCtrl : Control a wide :=
    ⟨(saved count (by decide +revert)).trans ctrl.count_eq,
      (saved registers.one (by decide +revert)).trans ctrl.one,
      (congrArg Fin.val (finish.reg_eq (3 : Fin 7))).symm.trans target,
      (saved registers.stackBase (by decide +revert)).trans ctrl.stackBase_eq,
      (saved tinBase (by decide +revert)).trans ctrl.tin_eq,
      (saved toutBase (by decide +revert)).trans ctrl.tout_eq,
      (saved offsetBase (by decide +revert)).trans ctrl.offset_eq,
      (saved childrenBase (by decide +revert)).trans ctrl.child_eq⟩
  refine ⟨wide, execution, ?_, ?_, wideCtrl, finish.frame cmd (show ∀ q : Fin 7, prefixRegisters q ≠ cmd by decide)⟩
  · intro j hj
    simpa only [Nat.zero_add, physical j hj] using copied.copied j hj
  · intro j hj
    exact copied.untouched j (Or.inr (by omega))

/-- The prefix transfer and parent-to-interval computation share one arena. -/
def fullPackedFinishProgram : Program L :=
  join (prefixCopyPhase (hi := hi) (hw := hw)).code parentFinishProgram
    prefixCopyPhase.haltPC prefixCopyPhase.haltFits

private theorem link_prefix_finish (input : Input L) {s p t : State L} {a b : Nat}
    (first : run (prefixCopyCode hi hw) input a (Phase.initial s) = some ⟨p, a⟩)
    (second : run parentFinishProgram input b (Phase.initial p) = some ⟨t, b⟩) :
    ∃ u trace, u.data = t.data ∧
      run fullPackedFinishProgram input (a + b) (Phase.initial s) = some ⟨u, a + b⟩ ∧
      SuccessfulTrace fullPackedFinishProgram input (Phase.initial s) trace ⟨u, a + b⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let front : Phase L := prefixCopyPhase
  let code : Program L := fullPackedFinishProgram
  have start : relocateStatePC 0 (Phase.initial s) = Phase.initial s := rfl
  have linked : Steps code input a (Phase.initial s) {p with pc := front.code.size} := by
    have jump := linked_return_of_run_multi (linked := code) (base := 0)
      (ret := fun _ => front.code.size) first
      (fun i op hit nonhalt => by
        have neq : i ≠ front.haltPC := fun e => nonhalt
          (Option.some.inj (hit.symm.trans (e.symm ▸ front.haltAt)))
        have same : relocateInstr 0 op = op := by cases op <;> simp [relocateInstr]
        simpa only [Nat.zero_add, same, code, fullPackedFinishProgram] using
          fetch_left front.code parentFinishProgram front.haltFits neq hit)
      (fun i hit => by
        have eq := front.uniqueHalt i hit
        rw [eq, Nat.zero_add]
        have patch := fetch_halt front.code parentFinishProgram front.haltFits
        exact ⟨patch.1, patch.2 (by unfold parentFinishProgram; exact pipeline_nonempty _)⟩)
    rw [start] at jump
    exact jump
  obtain ⟨k, atHalt, route, halt, cost⟩ := run_has_steps_then_halt second
  have placed : RelocatedSlice parentFinishProgram code front.code.size :=
    relocated_right front.code parentFinishProgram front.haltFits
  have route2 := route.relocate placed
  have inPC : relocateStatePC front.code.size (Phase.initial p) =
      {p with pc := front.code.size} := by simp only [relocateStatePC, Phase.initial, Nat.add_zero]
  rw [inPC] at route2
  obtain ⟨fetch, stateEq⟩ := halted_fetch_and_state halt
  have stop : step code input (relocateStatePC front.code.size atHalt) =
      some (.halted (relocateStatePC front.code.size t)) := by
    change t = atHalt at stateEq
    rw [stateEq]
    exact step_halt_at (s := relocateStatePC front.code.size atHalt) (placed atHalt.pc .halt fetch)
  have exec := (linked.append route2).halts stop
  change b = k + 1 at cost
  rw [Nat.add_assoc, ← cost] at exec
  obtain ⟨trace, ok⟩ := run_has_successfulTrace exec
  exact ⟨relocateStatePC front.code.size t, trace, rfl, exec, ok, ok.peak_eq⟩

/-- Copy the actual packed prefix and produce the interval suffix. The
copy's source is a physical producer output and all writes, comparisons,
and phase jumps take place in the single linked RAM trace. -/
theorem run_complete_packed_finish (input : Input L) {a : Arena bits workCap n}
    {root : Fin n} {parent : Fin n → Fin n} {depth : Fin n → Nat}
    (tree : ValidDepthTree root parent depth)
    (mass : rowPrefix (parentDegree root parent) n ≤ a.children) (children : a.children ≤ n)
    (s : State L) (ctrl : Control a s) (rootVal : (reg s cmd).val = root.val)
    (parents : ParentAt a parent s.data) (w : WordColumns bits)
    (placement : a.base = (packedPrefix w).size + 2 * n)
    (source : Nat) (fits : source + (packedPrefix w).size ≤ workCap)
    (apart : (packedPrefix w).size ≤ source)
    (params : PrefixCopyInput s source (packedPrefix w).size)
    (sourceAt : ∀ j < (packedPrefix w).size, s.data[source + j]? = (packedPrefix w)[j]?)
    (entrySize : w.entry.size = n) (stopSize : w.stop.size = n)
    (entrySpec : ∀ j : Nat, (w.entry[j]?).map Fin.val =
      (PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)).entries[j]?)
    (stopSpec : ∀ j : Nat, (w.stop[j]?).map Fin.val =
      (PaperB.ForestLayout.layout (bucketChildLists root parent) root (2 * n)).ends[j]?) :
    ∃ t trace work,
      t.data.extract 0 a.base = packedPayload w ∧
      work ≤ 7 * (packedPrefix w).size + 106 * n + 46 ∧
      run fullPackedFinishProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace fullPackedFinishProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  obtain ⟨p, copied, prefixAt, kept, pCtrl, rootKept⟩ :=
    prefixCopy input s ctrl w source fits apart (by omega) params sourceAt
  have pParents : ParentAt a parent p.data := by
    intro v
    rw [kept _ (by omega)]
    exact parents v
  have sameRoot := (congrArg Fin.val rootKept).trans rootVal
  obtain ⟨t, _, work, payload, cost, execute, _, _⟩ :=
    run_packed_payload_finish input tree mass children p pCtrl sameRoot pParents w placement
      prefixAt entrySize stopSize entrySpec stopSpec
  obtain ⟨u, trace, data, run, success, peak⟩ := link_prefix_finish input copied execute
  exact ⟨u, trace, _, by rw [data, payload], by omega, run, success, peak⟩


section Reader

open PaperB PaperB.LabelledQuotient PaperB.ForestHead
open PaperB.StaticGroupedTreeReader (endpointsOnly endpointsOnly_eq endpointsOnly_resources childScanLength)
open PaperB.ForestLayout (groupedChildLists groupedChildLists_eq_bucketChildLists)
open PaperB.EX24.FinalDFS (packedInput packedInput_ok nodeCount)
open PaperB.RetainedProperLoss (ofOrderedReader packWordColumns)
open _root_.EX24.PreparedSweep (orderedConfig)

private theorem rowPrefix_matches (root : Fin n) (parent : Fin n → Fin n)
    (i : Nat) (bound : i ≤ n) :
    rowPrefix (parentDegree root parent) i =
      (((finElems n).take i).map fun p => ((bucketChildLists root parent).get p).length).sum := by
  induction i with
  | zero => rfl
  | succ i ih =>
    let v : Fin n := ⟨i, by omega⟩
    have within : i < (finElems n).length := by rw [length_finElems]; exact v.isLt
    rw [rowPrefix, List.take_succ_eq_append_getElem within, finElems_index n v,
      List.map_append, List.sum_append, ih (by omega)]
    change _ + parentDegree root parent v.val = _
    rw [parentDegree_at]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]

/-- One child word for each occupied nonroot forest node. -/
theorem packed_parent_mass (x : PaperB.PackedStaticLayout.Input n)
    (tree : ValidDepthTree x.root x.parent.read x.depth.read) :
    rowPrefix (parentDegree x.root x.parent.read) n = n - 1 := by
  rw [rowPrefix_matches _ _ n (Nat.le_refl n)]
  have all : (finElems n).take n = finElems n := by
    apply List.take_of_length_le
    rw [length_finElems]
    exact Nat.le_refl _
  rw [all]
  change childScanLength (bucketChildLists x.root x.parent.read) = n - 1
  have eq := (endpointsOnly_resources x tree).2.1
  rw [groupedChildLists_eq_bucketChildLists] at eq
  exact eq

variable {H : PaperB.LabelledQuotient} {dictRows : PaperB.ForestDictionary.Rows H}
variable {vertices : Array (Vertex H)} {vertexCount : vertices.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]

/-- Connect the physical finish to the exact packed word image used by
the dictionary and membership theorems for this same ordered sweep. -/
theorem run_ordered_reader_finish (input : Input L)
    (r : PaperB.OrderedReaderResult dictRows vertices vertexCount rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    (a : Arena bits workCap (nodeCount (orderedConfig dictRows large) r.out))
    (s : State L) (ctrl : Control a s)
    (rootVal : (reg s cmd).val = (packedInput r.index.ok).root.val)
    (parents : ParentAt a (packedInput r.index.ok).parent.read s.data)
    (mass : (nodeCount (orderedConfig dictRows large) r.out) - 1 ≤ a.children)
    (children : a.children ≤ nodeCount (orderedConfig dictRows large) r.out)
    (place : a.base = (packedPrefix (packWordColumns r width)).size +
      2 * nodeCount (orderedConfig dictRows large) r.out)
    (source : Nat) (fits : source + (packedPrefix (packWordColumns r width)).size ≤ workCap)
    (apart : (packedPrefix (packWordColumns r width)).size ≤ source)
    (params : PrefixCopyInput s source (packedPrefix (packWordColumns r width)).size)
    (sourceAt : ∀ j < (packedPrefix (packWordColumns r width)).size,
      s.data[source + j]? = (packedPrefix (packWordColumns r width))[j]?) :
    let w := packWordColumns r width
    let N := nodeCount (orderedConfig dictRows large) r.out
    ∃ t trace work,
      t.data.extract 0 a.base = packedPayload w ∧
      work ≤ 7 * (packedPrefix w).size + 106 * N + 46 ∧
      work ≤ 232 * H.vertexCount + 159 ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      run fullPackedFinishProgram input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace fullPackedFinishProgram input (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  let x := packedInput r.index.ok
  let N := nodeCount (orderedConfig dictRows large) r.out
  let w := packWordColumns r width
  let ref := PaperB.ForestLayout.layout (bucketChildLists x.root x.parent.read) x.root (2 * N)
  have tree : ValidDepthTree x.root x.parent.read x.depth.read := packedInput_ok r.index.ok
  have exactMass : rowPrefix (parentDegree x.root x.parent.read) N ≤ a.children := by
    rw [packed_parent_mass x tree]; exact mass
  have matchEnd : (endpointsOnly x).entry.data = ref.entries ∧
      (endpointsOnly x).stop.data = ref.ends := by
    have h := (endpointsOnly_resources x tree).2.2.2
    rw [groupedChildLists_eq_bucketChildLists] at h
    exact ⟨h.1, h.2.1⟩
  have shape : (endpointsOnly x).entry.data = (ofOrderedReader r).entry ∧
      (endpointsOnly x).stop.data = (ofOrderedReader r).stop := by
    rw [endpointsOnly_eq, ← r.index.reader.layout_exact]
    exact ⟨rfl, rfl⟩
  have eSize : w.entry.size = N := by
    change (packWordColumns r width).entry.size = N
    simp only [packWordColumns, BoundedScalarArray.size_pack, ← shape.1]
    exact (endpointsOnly x).entry.len
  have sSize : w.stop.size = N := by
    change (packWordColumns r width).stop.size = N
    simp only [packWordColumns, BoundedScalarArray.size_pack, ← shape.2]
    exact (endpointsOnly x).stop.len
  have eVal (j : Nat) : (w.entry[j]?).map Fin.val = ref.entries[j]? := by
    change ((packWordColumns r width).entry[j]?).map Fin.val = _
    rw [packWordColumns, BoundedScalarArray.getElem?_pack_map_val, ← shape.1, matchEnd.1]
  have sVal (j : Nat) : (w.stop[j]?).map Fin.val = ref.ends[j]? := by
    change ((packWordColumns r width).stop[j]?).map Fin.val = _
    rw [packWordColumns, BoundedScalarArray.getElem?_pack_map_val, ← shape.2, matchEnd.2]
  obtain ⟨t, trace, k, payload, work, exec, checked, peak⟩ :=
    run_complete_packed_finish input tree exactMass children s ctrl rootVal
      parents w place source fits apart params sourceAt eSize sSize eVal sVal
  have retained : w.wordCount ≤ 1 + 18 * H.vertexCount :=
    PaperB.RetainedProperLoss.packWordColumns_count_le r width
  have smaller : (packedPrefix w).size ≤ w.wordCount := by
    rw [← packedPayload_size]
    simp only [packedPayload, Array.size_append]
    omega
  have occupied : N ≤ H.vertexCount + 1 := PaperB.EX24.FinalDFS.nodeCount_le r.index.ok
  exact ⟨t, trace, k, payload, work, by omega, retained, exec, checked, peak⟩

/-- A disjoint producer prefix and working arena fit in linear space.
The extra copy may also reuse capacity if the caller proves disjointness
from the destination and the parent representation. -/
theorem packed_finish_arena_bound
    (r : PaperB.OrderedReaderResult dictRows vertices vertexCount rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits) :
    let w := packWordColumns r width
    let N := nodeCount (orderedConfig dictRows large) r.out
    w.wordCount + (5 * N + 1 + N) + (packedPrefix w).size ≤ 42 * H.vertexCount + 9 := by
  intro w N
  have occupied : N ≤ H.vertexCount + 1 := PaperB.EX24.FinalDFS.nodeCount_le r.index.ok
  have retained : w.wordCount ≤ 1 + 18 * H.vertexCount :=
    PaperB.RetainedProperLoss.packWordColumns_count_le r width
  have smaller : (packedPrefix w).size ≤ w.wordCount := by
    rw [← packedPayload_size]
    simp only [packedPayload, Array.size_append]
    omega
  omega

end Reader

theorem fullPackedFinishProgram_cap_indep {bits c₁ d₁ c₂ d₂ : Nat}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) :
    fullPackedFinishProgram (bits := bits) (inputCap := c₁) (workCap := d₁) (hi := h₁) (hw := k₁) =
      fullPackedFinishProgram (bits := bits) (inputCap := c₂) (workCap := d₂) (hi := h₂) (hw := k₂) := by
  have hPreCode : (prefixCopyPhase (bits := bits) (inputCap := c₁) (workCap := d₁) (hi := h₁) (hw := k₁)).code =
      (prefixCopyPhase (bits := bits) (inputCap := c₂) (workCap := d₂) (hi := h₂) (hw := k₂)).code := by
    unfold prefixCopyPhase prefixCopyCode
    dsimp only [FixedROM.Phase.ofLast]
    apply Array.ext
    · rw [@size_embedProgram bits (PaperB.RamSliceCopy.layout bits c₁ d₁ h₁ k₁) (layout bits c₁ d₁ h₁ k₁) prefixRegisters,
        @size_embedProgram bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) prefixRegisters]
      rfl
    · intro i hi1 hi2
      have eq1 := Array.getElem?_eq_getElem hi1
      have eq2 := Array.getElem?_eq_getElem hi2
      apply Option.some.inj
      rw [← eq1, ← eq2,
        @getElem?_embedProgram bits (PaperB.RamSliceCopy.layout bits c₁ d₁ h₁ k₁) (layout bits c₁ d₁ h₁ k₁) prefixRegisters,
        @getElem?_embedProgram bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) prefixRegisters]
      have hEq : (PaperB.RamSliceCopy.standalone bits c₁ d₁ h₁ k₁ : Array (Instr bits 7)) =
          PaperB.RamSliceCopy.standalone bits c₂ d₂ h₂ k₂ := rfl
      cases hOp1 : (PaperB.RamSliceCopy.standalone bits c₁ d₁ h₁ k₁ : Array (Instr bits 7))[i]? with
      | none =>
        have hOp2 : (PaperB.RamSliceCopy.standalone bits c₂ d₂ h₂ k₂ : Array (Instr bits 7))[i]? = none :=
          (congrArg (fun (a : Array (Instr bits 7)) => a[i]?) hEq.symm).trans hOp1
        exact (congrArg (Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) prefixRegisters)) hOp2).symm
      | some op =>
        have hOp2 : (PaperB.RamSliceCopy.standalone bits c₂ d₂ h₂ k₂ : Array (Instr bits 7))[i]? = some op :=
          (congrArg (fun (a : Array (Instr bits 7)) => a[i]?) hEq.symm).trans hOp1
        have hMid : Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₁ d₁ h₁ k₁) (layout bits c₁ d₁ h₁ k₁) prefixRegisters) (some op) =
            Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) prefixRegisters) (some op) := by
          dsimp only [Option.map]; cases op <;> rfl
        exact hMid.trans
          (congrArg (Option.map (@embedInstr bits (PaperB.RamSliceCopy.layout bits c₂ d₂ h₂ k₂) (layout bits c₂ d₂ h₂ k₂) prefixRegisters)) hOp2).symm
  have hPreHalt : (prefixCopyPhase (bits := bits) (inputCap := c₁) (workCap := d₁) (hi := h₁) (hw := k₁)).haltPC =
      (prefixCopyPhase (bits := bits) (inputCap := c₂) (workCap := d₂) (hi := h₂) (hw := k₂)).haltPC := rfl
  have hPar := parentFinishProgram_cap_indep h₁ k₁ h₂ k₂
  unfold fullPackedFinishProgram
  simp only [FixedROM.join, hPreCode, hPreHalt, hPar]

end PaperB.RamForestProgram.Finish
