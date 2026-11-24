module

public import PaperB.ForestBuildPackedWords
public import PaperB.ForestEndpointFinish
public import PaperB.KahnDecreasing

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.ForestPreparedBuild

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.RetainedProperLoss
open PaperB.KahnDecreasing
open _root_.EX24.PreparedSweep

variable {H : LabelledQuotient} (data : Array (Vertex H))
variable (size_data : data.size = H.vertexCount)

/-- Arc order is expressed directly in the supplied permutation. -/
def IsTopologicalOrder : Prop :=
  ∀ i j : Fin H.vertexCount,
    H.HasQuotientArc (orderedVertexAt data size_data i)
      (orderedVertexAt data size_data j) → i < j

theorem isTopologicalOrder_of_rank (rank : Vertex H → Nat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) :
    IsTopologicalOrder data size_data := by
  intro i j h
  have lt := rankArc _ _ h
  change i.val < j.val
  apply Nat.lt_of_not_ge
  intro hge
  rcases Nat.eq_or_lt_of_le hge with eq | gt
  · have same : j = i := Fin.ext eq
    rw [same] at lt
    exact (Nat.lt_irrefl _ lt).elim
  · exact (Nat.lt_asymm lt (increasing j i gt)).elim

variable (unique : data.toList.Nodup)

def orderRanks : InverseRankTable data data.size :=
  inverseRanks data unique

include size_data in
theorem orderRanks_scatter :
    (orderRanks data unique).ranks.size = H.vertexCount ∧
    (orderRanks data unique).orderReads = H.vertexCount ∧
    (orderRanks data unique).indexWrites = H.vertexCount :=
  ⟨(orderRanks data unique).size_eq,
    (orderRanks data unique).reads_eq.trans size_data,
    (orderRanks data unique).writes_eq.trans size_data⟩

theorem orderRanks_at (i : Fin H.vertexCount) :
    readRank (orderRanks data unique) (orderedVertexAt data size_data i) = i.val := by
  have hi : i.val < data.size := by simpa only [size_data] using i.isLt
  exact (orderRanks data unique).lookup i.val hi hi

theorem orderRanks_increasing (i j : Fin H.vertexCount) (hi : i.val < j.val) :
    readRank (orderRanks data unique) (orderedVertexAt data size_data i) <
      readRank (orderRanks data unique) (orderedVertexAt data size_data j) := by
  rw [orderRanks_at, orderRanks_at]
  exact hi

variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)

include covers in
theorem orderRanks_rankArc (topo : IsTopologicalOrder data size_data)
    (u v : Vertex H) (e : H.HasQuotientArc u v) :
    readRank (orderRanks data unique) u < readRank (orderRanks data unique) v := by
  obtain ⟨i, hu⟩ := covers u
  obtain ⟨j, hv⟩ := covers v
  have hi : i < j := topo i j (by rw [hu, hv]; exact e)
  rw [← hu, ← hv]
  exact orderRanks_increasing data size_data unique i j hi

/-- An indexed rank read from an already constructed table. -/
def orderRankProbed (t : InverseRankTable data data.size) (v : Vertex H) : Nat × Nat :=
  CountedProbe.readD t.ranks v.val 0

theorem orderRankProbed_exact (t : InverseRankTable data data.size) (v : Vertex H) :
    orderRankProbed data t v = (readRank t v, 1) := by
  have hv : v.val < t.ranks.size := t.size_eq.symm ▸ v.isLt
  simp only [orderRankProbed, CountedProbe.readD, CountedProbe.mapC, CountedProbe.read,
    getElem?_pos t.ranks v.val hv, Option.getD_some, readRank]

include covers in
theorem orderRank_lt (v : Vertex H) :
    readRank (orderRanks data unique) v < H.vertexCount := by
  obtain ⟨i, hv⟩ := covers v
  rw [← hv, orderRanks_at]
  exact i.isLt

/-- Construct the retained image from a topological permutation. Rank
evaluation inside the sweep is an array access, with no callback supplied
by the caller. The packed output does not retain the inverse rank table. -/
def buildWordsFromOrder
    (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat) :
    Option (WordColumns (OracleContract.wordBits 5 H.vertexCount 0)) :=
  if 3 ≤ H.vertexCount then
    let t := orderRanks data unique
    buildWordsCompact data size_data (readRank t)
      (orderRanks_increasing data size_data unique) covers
      (orderRanks_rankArc data size_data unique covers topo) flat
  else
    none

theorem buildWordsFromOrder_eq
    (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat) :
    buildWordsFromOrder data size_data unique covers topo flat =
      buildWords data size_data (readRank (orderRanks data unique))
        (orderRanks_increasing data size_data unique) covers
        (orderRanks_rankArc data size_data unique covers topo) flat := by
  unfold buildWordsFromOrder
  by_cases large : 3 ≤ H.vertexCount
  · simp only [ite_eq_left large, buildWordsCompact_eq]
  · simp only [ite_eq_right large, buildWords, dite_eq_right large]

theorem buildWordsFromOrder_retained
    (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat) :
    ((buildWordsFromOrder data size_data unique covers topo flat).map
      WordColumns.wordCount).getD 0 ≤ 19 * H.vertexCount := by
  rw [buildWordsFromOrder_eq]
  exact buildWords_retained data size_data (readRank (orderRanks data unique))
    (orderRanks_increasing data size_data unique) covers
    (orderRanks_rankArc data size_data unique covers topo) flat

end PaperB.ForestPreparedBuild
