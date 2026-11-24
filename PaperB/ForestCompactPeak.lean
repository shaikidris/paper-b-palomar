module

public import PaperB.ForestCompactFinishSpace
public import PaperB.ForestDictionaryCollectionSpace
public import PaperB.ForestInputPrepStorage
public import PaperB.ForestProbeWorkspace

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.ForestPreparedBuild

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.Storage
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps PaperB.KahnDecreasing
open PaperB.RetainedProperLoss PaperB.EX24.FinalDFS PaperB.ForestLayout
open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open PaperB.PairDictionary.FixedBank
open PaperB.PairLookup.KeyMerge.Workspace (Span)
open PaperB.ForestDictionary
open PaperB.EX24.InputPrepCheckpoint (InputFits inputPeak immutableUnits)

/-- Keep the input preparation reserve throughout the build. Include both
the supplied vertex order and the inverse rank table in that reserve. -/
def preparationReserve (H : LabelledQuotient) : Nat :=
  inputPeak H (2 * H.vertexCount)

theorem preparationReserve_eq (H : LabelledQuotient) :
    preparationReserve H = 13 * H.vertexCount + 30 * H.arcCount := by
  unfold preparationReserve inputPeak immutableUnits
  rw [H.adj_size]
  omega

theorem rawPreparation_phase_reserve (H : LabelledQuotient) (cells : Nat)
    (h : InputFits H (2 * H.vertexCount) cells) :
    immutableUnits H (2 * H.vertexCount) + cells ≤ preparationReserve H := h

private def chargedCells {actual budget : Nat} (_ : actual ≤ budget) : Nat :=
  actual

/-- Reserve the reached source-row boundary plus a separate full row for
the mapping output. The extra reserve uses the whole occurrence count
even though only one row is converted at a time. -/
theorem source_conversion_reserve (H : LabelledQuotient) (done : List (Vertex H)) :
    immutableUnits H (2 * H.vertexCount) +
      chargedCells (PaperB.EX24.InputPrepCheckpoint.source_prefix_receipt H done) +
        2 * H.arcCount ≤ preparationReserve H := by
  let cells := chargedCells (PaperB.EX24.InputPrepCheckpoint.source_prefix_receipt H done)
  have bound : cells ≤ 2 * H.vertexCount +
      5 * PaperB.EX24.InputPrepCheckpoint.labelMass H (ForestIncomingRaw.prepare H) :=
    PaperB.EX24.InputPrepCheckpoint.source_prefix_receipt H done
  rw [PaperB.EX24.InputPrepCheckpoint.labelMass_prepare] at bound
  change immutableUnits H (2 * H.vertexCount) + cells + 2 * H.arcCount ≤
    preparationReserve H
  unfold preparationReserve inputPeak
  omega

theorem dedup_phase_reserve (H : LabelledQuotient) (done : List (Vertex H))
    (y : Vertex H) (later : List (Vertex H))
    (heads : done ++ y :: later = List.finRange H.vertexCount)
    (seen todo : List (Vertex H))
    (split : seen ++ todo =
      (ForestIncomingPrep.sources H (ForestIncomingRaw.prepare H)).read y) :
    let p := ForestIncomingRaw.prepare H
    let s := ForestIncomingPrep.sources H p
    let b := ForestIncoming.run s done
    let r := ForestIncoming.scan y seen b.marks [] b.visits
    immutableUnits H (2 * H.vertexCount) +
      PaperB.EX24.InputPrepCheckpoint.liveUnits H p s b.rows r.marks r.row ≤
      preparationReserve H := by
  have nd : (done ++ y :: later).Nodup := heads.symm ▸ List.nodup_finRange H.vertexCount
  have fresh : y ∉ done := by
    intro hy
    exact (List.pairwise_append.mp nd).2.2 y hy y (by simp) rfl
  have bound := PaperB.EX24.InputPrepCheckpoint.dedup_prefix_receipt
    H done y fresh seen todo split
  dsimp only at bound ⊢
  unfold preparationReserve inputPeak
  omega

/-- Reserve the collection handoff, the accumulator backing slots and the
fixed-bank sort together. Three words per weighted sort cell cover key
payload and reference, or the abstract unit of a sorting frame. -/
theorem dictionary_phase_reserve {H : LabelledQuotient} (p : ForestDictionary.Rows H) :
    let vertices := H.vertexCount
    let source := collect p orderedPairCode
    let k := source.length
    ∃ final : Array Key, ∃ frames : Nat,
      CollectAt p orderedPairCode (List.finRange vertices) [] final ∧
      final.toList = source ∧
      Calls (ceilBinaryLog k) (Span.root k) frames ∧
      preparationReserve H +
        (vertices + 2 * final.size + 3 * final.toList.length) + vertices +
        3 * (5 * k + (packedDictionary p orderedPairCode).size + frames)
        ≤ 128 * (vertices + H.arcCount) := by
  intro vertices source k
  obtain ⟨final, hfinal⟩ := (collect_reserved_start p orderedPairCode).complete
  obtain ⟨hexact, hcollect⟩ := collect_handoff_words hfinal
  have sort := packedDictionary_construction_space p orderedPairCode 1
  dsimp only at sort
  obtain ⟨_, hfirst, hzero, _, hbank, _, _, _, _, frames, trace, _, hsort⟩ := sort
  simp only [hfirst, Array.size_replicate, hbank] at hsort
  refine ⟨final, frames, hfinal, hexact, trace, ?_⟩
  rw [preparationReserve_eq]
  have positive : 0 < vertices := Nat.zero_lt_of_lt H.root.isLt
  change vertices + 2 * final.size + 3 * final.toList.length ≤ 6 * vertices at hcollect
  change k + k + k + 2 * k + (packedDictionary p orderedPairCode).size + 1 * frames
    ≤ (6 + 1) * (vertices + 1) at hsort
  omega

theorem active_sweep_phase_reserve (H : LabelledQuotient)
    (large : 3 ≤ H.vertexCount) (cells : Nat)
    (bound : cells ≤ 11 * H.vertexCount + 2 * H.arcCount +
      37 * OracleContract.L H.vertexCount + 13) :
    preparationReserve H + cells ≤ 128 * (H.vertexCount + H.arcCount) := by
  rw [preparationReserve_eq]
  have hl := Nat.log2_le_self (H.vertexCount + 1)
  unfold OracleContract.L at bound
  omega

variable {H : LabelledQuotient} (data : Array (Vertex H))
variable (size_data : data.size = H.vertexCount)
variable (unique : data.toList.Nodup)
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat)

open PaperB.ForestLayout.LiveCells

/-- The reached sweep checkpoints and compact finish share one reserve
with input preparation. The early and active-probe receipts above use
the same bound, allowing preparation roots to overlap later phases. -/
theorem buildWordsFromOrder_peak_receipts (large : 3 ≤ H.vertexCount) :
    let N := H.vertexCount
    let rank := readRank (orderRanks data unique)
    let p := (ForestIncomingPrep.build H (by intro u v; rfl)).tests
    let c := packedOrderedConfig p large
    let rows := orderedRows p data size_data
    let mem := (ConcreteInit.initImage N).1
    let s := initial c mem N
    ∃ (out : State H) (log rev : Log H) (ok : OutputOK c rank out)
      (w : WordColumns (OracleContract.wordBits 5 N 0)),
      fromRoot c rank mem N rows = some (out, log) ∧
      Visit c rank rows s [] [] out rev rows.length ∧
      log = rev.reverse ∧
      buildWordsFromOrder data size_data unique covers topo flat = some w ∧
      (∀ {todo : List (Row H)} {t : State H} {acc : Log H} {j : Nat},
        Visit c rank rows s [] todo t acc j →
        preparationReserve H + checkpointCells c data rows t acc + N ≤
          128 * (N + H.arcCount)) ∧
      let x := packedInput ok
      let T := nodeCount c out
      let g := (groupedChildLists x.root x.parent.read).1
      let mass := StaticGroupedTreeReader.childScanLength g
      let base := checkpointCells c data rows out rev + N + log.length
      let extracted := x.parent.data.size + x.depth.data.size
      let grouping := groupedChildListsPeak T T
      let oldColumns := c.dict.size + out.tables.slots.size + out.tables.back.size +
        out.labels.size + (StaticGroupedTreeReader.endpointsOnly x).entry.data.size +
        (StaticGroupedTreeReader.endpointsOnly x).stop.data.size
      (∀ k, k ≤ 2 * T → PrefixLive g x.root mass k) ∧
      preparationReserve H + (base + extracted + grouping + 9 * T + 3 * oldColumns + w.wordCount)
        ≤ 128 * (N + H.arcCount) := by
  intro N rank p c rows mem s
  obtain ⟨out, log, rev, ok, w, run, visit, revEq, packed, dfs, finish⟩ :=
    buildWordsFromOrder_finish_space data size_data unique covers topo flat large
  refine ⟨out, log, rev, ok, w, run, visit, revEq, packed, ?_, dfs, ?_⟩
  · intro todo t acc j hv
    have hc : c = orderedConfig p large := packedOrderedConfig_eq p large
    change Visit c rank rows (initial c mem N) [] todo t acc j at hv
    rw [hc] at hv
    have phase := runOrderedReaderFast_prepared_prefix_storage data size_data rank large
      (orderRanks_increasing data size_data unique) covers hv
    have h : checkpointCells c data rows t acc + N ≤ 11 * N + H.arcCount + 5 := by
      rw [hc]
      exact phase.2
    rw [preparationReserve_eq]
    change 13 * N + 30 * H.arcCount + checkpointCells c data rows t acc + N
      ≤ 128 * (N + H.arcCount)
    omega
  · rw [preparationReserve_eq]
    simp only [c, p, rows]
    omega

end PaperB.ForestPreparedBuild
