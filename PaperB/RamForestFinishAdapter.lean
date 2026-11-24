module

public import PaperB.RamForestRawInterface
public import PaperB.RamForestPackedFinish
public import PaperB.RamForestSmallAndLookup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Adapter from the Stage 2 contract (`Stage2Output`) to the Stage 3 physical
finish program (`fullPackedFinishProgram`) and the serialized Lemma 3.2 index
contract (`SerializedProperLossIndex`).
-/

namespace PaperB.RamForestProgram.RawBuild

open PaperB
open PaperB.LabelledQuotient
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram.Finish
open PaperB.RetainedProperLoss
open PaperB.EX24.FinalDFS
open _root_.EX24.PreparedSweep
open PaperB.ForestHead

section FinishAdapter

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "L" => layout bits inputCap workCap hi hw

theorem fullPackedFinishProgram_nonempty :
    0 < (fullPackedFinishProgram (hi := hi) (hw := hw)).size := by
  unfold fullPackedFinishProgram join
  rw [Array.size_append, Array.size_set, Array.size_map]
  have hp : 0 < (parentFinishProgram (bits := bits) (inputCap := inputCap)
      (workCap := workCap) (hi := hi) (hw := hw)).size := by
    unfold parentFinishProgram
    exact pipeline_nonempty _
  omega

/-- Execute `fullPackedFinishProgram` from any `Stage2Output` witness, proving
exact `packedPayload (packWordColumns r width)` extraction, `work ≤ 232 * n_H + 159`,
retained-word bound `≤ 1 + 18 * n_H`, peak footprint `inputCap + workCap + 15`,
and `SerializedProperLossIndex H (packWordColumns r width)`. -/
theorem run_stage2_finish_of_stage2Output (input : Input L)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {dictRows : PaperB.ForestDictionary.Rows H}
    {vertices : Array (Vertex H)} {vertexCount : vertices.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows vertices vertexCount rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s : State L) (hStage2 : Nonempty (Stage2Output H r width s)) :
    let w := packWordColumns r width
    ∃ (t : State L) (trace : List (State L)) (work : Nat),
      w.wordCount ≤ workCap ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      work ≤ 232 * H.vertexCount + 159 ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      SerializedProperLossIndex H w ∧
      run (fullPackedFinishProgram (hi := hi) (hw := hw)) input work (Phase.initial s) =
        some ⟨t, work⟩ ∧
      SuccessfulTrace (fullPackedFinishProgram (hi := hi) (hw := hw)) input
        (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  intro w
  rcases hStage2 with ⟨o⟩
  obtain ⟨t, trace, work, hExtract, _, hWork, hRetained, hRun, hTrace, hPeak⟩ :=
    run_ordered_reader_finish input r width o.arena s o.ctrl o.rootVal o.parents
      o.mass o.children o.place o.src o.fits o.apart o.params o.sourceAt
  have hBaseLe : o.arena.base ≤ workCap := by
    have hRoom := o.arena.room
    omega
  have hBaseLeData : o.arena.base ≤ t.data.size := by
    rw [t.data_size]
    exact hBaseLe
  have hBaseEqWordCount : o.arena.base = w.wordCount := by
    have hSz := congrArg Array.size hExtract
    rw [Array.size_extract, Nat.min_eq_left hBaseLeData, Nat.sub_zero,
      packedPayload_size w] at hSz
    exact hSz
  refine ⟨t, trace, work, ?_, ?_, hWork, hRetained, ?_, hRun, hTrace, hPeak⟩
  · exact hBaseEqWordCount ▸ hBaseLe
  · simpa only [← hBaseEqWordCount] using hExtract
  · exact packWordColumns_isSerializedProperLossIndex r width

/-- Raw-input variant of `run_stage2_finish_of_stage2Output`, bundling the
`RawQuotientInput` and `rawWorkCap` bounds from `RamForestRawInterface`. -/
theorem run_stage2_finish_raw (input : Input L)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    (hRaw : RawQuotientInput input H)
    (hWork : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    {dictRows : PaperB.ForestDictionary.Rows H}
    {vertices : Array (Vertex H)} {vertexCount : vertices.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows vertices vertexCount rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    (s : State L) (hStage2 : Nonempty (Stage2Output H r width s)) :
    let w := packWordColumns r width
    rawInputCap H.arcCount ≤ inputCap ∧
    w.wordCount ≤ rawWorkCap H.vertexCount H.arcCount ∧
    rawWorkCap H.vertexCount H.arcCount ≤ workCap ∧
    ∃ (t : State L) (trace : List (State L)) (work : Nat),
      w.wordCount ≤ workCap ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      work ≤ 232 * H.vertexCount + 159 ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      SerializedProperLossIndex H w ∧
      run (fullPackedFinishProgram (hi := hi) (hw := hw)) input work (Phase.initial s) =
        some ⟨t, work⟩ ∧
      SuccessfulTrace (fullPackedFinishProgram (hi := hi) (hw := hw)) input
        (Phase.initial s) trace ⟨t, work⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  intro w
  obtain ⟨t, trace, work, hwCap, hExtract, hWorkBound, hRetained, hIdx, hRun, hTrace, hPeak⟩ :=
    run_stage2_finish_of_stage2Output input r width s hStage2
  have hRetInRaw : w.wordCount ≤ rawWorkCap H.vertexCount H.arcCount := by
    change (packWordColumns r width).wordCount ≤ rawWorkCap H.vertexCount H.arcCount
    unfold rawWorkCap
    omega
  exact ⟨hRaw.cap_ge, hRetInRaw, hWork, t, trace, work, hwCap, hExtract, hWorkBound, hRetained,
    hIdx, hRun, hTrace, hPeak⟩

/-- Link any returning front `Phase L` whose output state satisfies
`Stage2Output` directly into `fullPackedFinishProgram` in one RAM run. -/
theorem run_linked_stage2_finish (front : Phase L) (input : Input L)
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {dictRows : PaperB.ForestDictionary.Rows H}
    {vertices : Array (Vertex H)} {vertexCount : vertices.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    (r : PaperB.OrderedReaderResult dictRows vertices vertexCount rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits)
    {s₀ sMid : State L} {work₁ : Nat}
    (hFront : run front.code input work₁ (Phase.initial s₀) = some ⟨sMid, work₁⟩)
    (hStage2 : Nonempty (Stage2Output H r width sMid)) :
    let code := join front.code (fullPackedFinishProgram (hi := hi) (hw := hw))
      front.haltPC front.haltFits
    let w := packWordColumns r width
    ∃ (t : State L) (trace : List (State L)) (work₂ : Nat),
      w.wordCount ≤ workCap ∧
      t.data.extract 0 w.wordCount = packedPayload w ∧
      work₂ ≤ 232 * H.vertexCount + 159 ∧
      w.wordCount ≤ 1 + 18 * H.vertexCount ∧
      SerializedProperLossIndex H w ∧
      run code input (work₁ + work₂) (Phase.initial s₀) = some ⟨t, work₁ + work₂⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) trace ⟨t, work₁ + work₂⟩ ∧
      tracePeakWords input trace = inputCap + workCap + 15 := by
  intro code w
  obtain ⟨u, _, work₂, hwCap, hExtract, hWorkBound, hRetained, hIdx, hRun2, _, _⟩ :=
    run_stage2_finish_of_stage2Output input r width sMid hStage2
  obtain ⟨v, trace, _, hDataEq, hRun, hTrace, hPeak⟩ :=
    run_linked_pair front (fullPackedFinishProgram (hi := hi) (hw := hw))
      (fullPackedFinishProgram_nonempty (hi := hi) (hw := hw)) hFront hRun2
  refine ⟨v, trace, work₂, hwCap, ?_, hWorkBound, hRetained, hIdx, hRun, hTrace, ?_⟩
  · rw [hDataEq]
    exact hExtract
  · simpa only [footprint] using hPeak

end FinishAdapter

end PaperB.RamForestProgram.RawBuild
