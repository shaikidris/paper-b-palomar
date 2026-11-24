module

public import PaperB.ForestPreparedBuild
public import PaperB.ForestPackedMembership

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestPreparedBuild

open _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.RetainedProperLoss

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

private def prepared (H : LabelledQuotient) :=
  ForestIncomingPrep.build H (by intro u y; rfl)

/-- The executable reader shared by unencoded and word-encoded membership.
The input is partitioned once and the actual ordered sweep runs once. -/
def readerForWords (large : 3 ≤ H.vertexCount) :
    OrderedReaderResult (prepared H).tests data size_data rank large :=
  runOrderedReaderFast (prepared H).tests data size_data rank large
    increasing covers rankArc flat

def buildWords : Option (WordColumns (OracleContract.wordBits 5 H.vertexCount 0)) :=
  if large : 3 ≤ H.vertexCount then
    some (packWordColumns (readerForWords data size_data rank increasing covers rankArc flat large)
      (local_word_columns_fit H.vertexCount))
  else
    none

theorem buildWords_of_large (large : 3 ≤ H.vertexCount) :
    buildWords data size_data rank increasing covers rankArc flat =
      some (packWordColumns (readerForWords data size_data rank increasing covers rankArc flat large)
        (local_word_columns_fit H.vertexCount)) := by
  simp only [buildWords, dite_eq_left large]

theorem build_of_large_readerForWords (large : 3 ≤ H.vertexCount) :
    build data size_data rank increasing covers rankArc flat =
      some (ofOrderedReader (readerForWords data size_data rank increasing covers rankArc flat large)) := by
  simp only [build, dite_eq_left large]
  rfl

theorem buildWords_retained :
    ((buildWords data size_data rank increasing covers rankArc flat).map
      WordColumns.wordCount).getD 0 ≤ 19 * H.vertexCount := by
  by_cases large : 3 ≤ H.vertexCount
  · rw [buildWords_of_large data size_data rank increasing covers rankArc flat large]
    have hw := packWordColumns_count_le
      (readerForWords data size_data rank increasing covers rankArc flat large)
      (local_word_columns_fit H.vertexCount)
    simpa only [Option.map_some, Option.getD_some] using
      Nat.le_trans hw (by omega : 1 + 18 * H.vertexCount ≤ 19 * H.vertexCount)
  · simp only [buildWords, dite_eq_right large, Option.map_none, Option.getD_none, Nat.zero_le]

end PaperB.ForestPreparedBuild
