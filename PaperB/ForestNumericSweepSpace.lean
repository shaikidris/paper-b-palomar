module

public import PaperB.ForestSweepStorage
public import PaperB.ForestPhaseBudget

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps
open AggregateEX24
open _root_.EX24.PreparedSweep.Storage

private abbrev storageReaderPrep (H : LabelledQuotient) :=
  (fun {cv} (_charged : (ForestIncomingPrep.build H cv).visits = H.arcCount) =>
    ForestIncomingPrep.build H cv)
    (ForestPreparedBuild.dedup_visits_eq_arcCount H)

private theorem storage_testCells_eq_entryTotal {H : LabelledQuotient}
    (rows : List (Row H)) : testCells rows = entryTotal rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      simp only [testCells, entryTotal, ih]

/-- The first bound is for sweep checkpoints. The second reserves a separate
`H.vertexCount` cells for final reversal, outside the checkpoint count. -/
theorem runOrderedReaderFast_prepared_prefix_storage
    {H : LabelledQuotient}
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v) :
    let prep := storageReaderPrep H
    let p := prep.tests
    let c := orderedConfig p large
    let rows := orderedRows p data size_data
    let s := initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    ∀ {todo : List (Row H)} {t : State H} {rev : Log H} {k : Nat},
      Visit c rank rows s [] todo t rev k →
      checkpointCells c data rows t rev ≤ 10 * H.vertexCount + H.arcCount + 5 ∧
      checkpointCells c data rows t rev + H.vertexCount ≤
        11 * H.vertexCount + H.arcCount + 5 := by
  intro prep p c rows s todo t rev k hv
  have distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v := by
    intro u v huv
    obtain ⟨i, hi⟩ := covers u
    obtain ⟨j, hj⟩ := covers v
    have hij : i.val = j.val := by
      by_cases hlt : i.val < j.val
      · have h := increasing i j hlt
        rw [hi, hj] at h
        omega
      · by_cases hgt : j.val < i.val
        · have h := increasing j i hgt
          rw [hj, hi] at h
          omega
        · omega
    exact hi.symm.trans
      ((congrArg (orderedVertexAt data size_data) (Fin.ext hij)).trans hj)
  have full : FullRows p rank rows :=
    orderedRows_full p data size_data rank increasing covers
  have ready : Ready rank rows :=
    ⟨distinctRanks, full.ordered, fun row hr =>
      (full.tests_eq row hr).symm ▸ p.spec row.head⟩
  have htests : testCells rows ≤ H.arcCount := by
    rw [storage_testCells_eq_entryTotal]
    have hentries := ForestPreparedBuild.entryTotal_le_arcTotal
      (H := H) (data := data) (size_data := size_data) (rank := rank)
      (increasing := increasing) (covers := covers)
    have harcs := ForestPreparedBuild.dedup_visits_eq_arcCount H
    rw [ForestIncomingPrep.visits_supplied, ForestIncomingRaw.length_supplied] at harcs
    rw [harcs] at hentries
    exact hentries
  have hnodes : c.region.maxNodes = H.vertexCount := rfl
  have hprefix :
      checkpointCells c data rows t rev ≤
        (ConcreteInit.initImage H.vertexCount).1.size + (c.region.maxNodes + 1) +
          testCells rows + 6 * H.vertexCount :=
    Visit.ordered_bound p data size_data large (c := c) rfl ready hv
  rw [hnodes, (ConcreteInit.exact_allocated_words H.vertexCount)] at hprefix
  have hcheckpoint :
      checkpointCells c data rows t rev ≤ 10 * H.vertexCount + H.arcCount + 5 := by
    omega
  refine ⟨hcheckpoint, ?_⟩
  omega

end PaperB
