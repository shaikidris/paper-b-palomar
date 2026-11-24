module

public import PaperB.ForestCompactBuildWork

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
open PaperB.ForestLayout.LiveCells

variable {H : LabelledQuotient} (data : Array (Vertex H))
variable (size_data : data.size = H.vertexCount)
variable (unique : data.toList.Nodup)
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat)

/-- Reserve the last sweep checkpoint, dense rank array and returned log
through the compact finish. Also reserve the extracted tree input,
grouping workspace, DFS live cells and both generations of query columns.
The charges are initialized cells and fixed-size source records. -/
theorem buildWordsFromOrder_finish_space (large : 3 ≤ H.vertexCount) :
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
      base + extracted + grouping + 9 * T + 3 * oldColumns + w.wordCount
        ≤ 80 * (N + H.arcCount) := by
  intro N rank p c rows mem s
  let increasing := orderRanks_increasing data size_data unique
  let rankArc := orderRanks_rankArc data size_data unique covers topo
  let r := readerForWords data size_data rank increasing covers rankArc flat large
  have hc : c = orderedConfig p large := packedOrderedConfig_eq p large
  have ok : OutputOK c rank r.out := hc.symm ▸ r.index.ok
  have run : fromRoot c rank mem N rows = some (r.out, r.log) :=
    (runOrderedPacked_eq p data size_data rank large).trans r.ran
  have foldRun : foldRows c rank rows s = some (r.out, r.log) := run
  obtain ⟨rev, visit, revEq, logLen⟩ := foldRows_endCheckpoint foldRun
  let w := packWordColumns r (local_word_columns_fit N)
  have packed : buildWordsFromOrder data size_data unique covers topo flat = some w := by
    rw [buildWordsFromOrder_eq]
    exact buildWords_of_large data size_data rank increasing covers rankArc flat large
  refine ⟨r.out, r.log, rev, ok, w, run, visit, revEq, packed, ?_⟩
  dsimp only
  have tree : ValidDepthTree (packedInput ok).root (packedInput ok).parent.read
      (packedInput ok).depth.read := by
    have ht := packedInput_ok ok
    first | exact ht | exact ht.tree | exact ht.1 | exact ht.2 | exact?
  refine ⟨(StaticGroupedTreeReader.endpointsOnly_resources (packedInput ok) tree).2.2.2.2.2, ?_⟩
  have handoff : checkpointCells c data rows r.out rev ≤ 10 * N + H.arcCount + 5 := by
    have hv := visit
    change Visit c rank rows (initial c mem N) [] [] r.out rev rows.length at hv
    rw [hc] at hv
    have hh := runOrderedReaderFast_prepared_prefix_storage data size_data rank large
      increasing covers hv
    rw [hc]
    exact hh.1
  have words := buildWordsFromOrder_retained data size_data unique covers topo flat
  rw [packed] at words
  change w.wordCount ≤ 19 * N at words
  have nT := nodeCount_le ok
  have rowsN : rows.length = N := by simp [rows, orderedRows, N]
  have doneN : r.log.length = N := logLen.trans rowsN
  have hp := (packedInput ok).parent.len
  have hd := (packedInput ok).depth.len
  have he := (StaticGroupedTreeReader.endpointsOnly (packedInput ok)).entry.len
  have hs := (StaticGroupedTreeReader.endpointsOnly (packedInput ok)).stop.len
  have hr : c.dict.size + r.out.tables.slots.size + r.out.tables.back.size +
      r.out.labels.size + nodeCount c r.out + nodeCount c r.out ≤ 9 * N := by
    have hr := RetainedProperLoss.arraySize_le r
    unfold Columns.arraySize ofOrderedReader at hr
    have hn : nodeCount c r.out = nodeCount (orderedConfig p large) r.out := by rw [hc]
    rw [hn, hc]
    rw [r.index.reader.layout.endpoints.entry.len,
      r.index.reader.layout.endpoints.stop.len] at hr
    exact hr
  unfold groupedChildListsPeak
  omega

end PaperB.ForestPreparedBuild
