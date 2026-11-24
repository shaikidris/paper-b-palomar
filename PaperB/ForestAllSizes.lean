module

public import PaperB.ForestSlimIndex
public import PaperB.SmallQuotient

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.QuotientMembership

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

/-- `none` retains nothing; `some` retains only the six slim arrays. -/
abbrev Index (H : LabelledQuotient) := Option (RetainedProperLoss.Columns H)

/-- Compute the scalar vertex slot without retaining the ordered configuration. -/
private def vertexSlot {H : LabelledQuotient} (v : Vertex H) :
    { i : Nat // ∀ (p : ForestDictionary.Rows H) (large : 3 ≤ H.vertexCount),
        (orderedConfig p large).vertexIndex v = i } := by
  first
  | exact ⟨v.val, fun _ _ => rfl⟩
  | exact ⟨v.val + 1, fun _ _ => rfl⟩
  | exact ⟨_, fun _ _ => rfl⟩

def Index.contains {H : LabelledQuotient} [DecidableEq (CutPair H)]
    (s : Index H) (q : CutPair H) (v : Vertex H) : Bool :=
  match s with
  | none => false
  | some cols => cols.contains q (vertexSlot v).val

def Index.arraySize {H : LabelledQuotient} (s : Index H) : Nat :=
  match s with
  | none => 0
  | some cols => cols.arraySize

section

variable {H : LabelledQuotient} [DecidableEq (CutPair H)]
variable (p : ForestDictionary.Rows H)
variable (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
variable (rank : Vertex H → Nat)
variable (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
  rank (orderedVertexAt data size_data i) <
    rank (orderedVertexAt data size_data j))
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
variable (flat : H.IsFlat)

def build : Index H :=
  if large : 3 ≤ H.vertexCount then
    some (RetainedProperLoss.ofOrderedReader
      (runOrderedReader p data size_data rank large increasing covers rankArc flat))
  else
    none

theorem build_of_small (small : H.vertexCount < 3) :
    build p data size_data rank increasing covers rankArc flat = none := by
  have notLarge : ¬ 3 ≤ H.vertexCount := by omega
  simp only [build, dif_neg notLarge]

/-- Exact agreement with the ordered reader on every valid pair and vertex.
    In the small branch there is no valid cut pair. -/
theorem query_exact (q : CutPair H) (v : Vertex H) :
    Index.contains (build p data size_data rank increasing covers rankArc flat) q v =
      (if large : 3 ≤ H.vertexCount then
        (runOrderedReader p data size_data rank large
          increasing covers rankArc flat).index.contains q v
      else false) := by
  by_cases large : 3 ≤ H.vertexCount
  · have h := RetainedProperLoss.contains_eq
      (runOrderedReader p data size_data rank large increasing covers rankArc flat) q v
    rw [(vertexSlot v).property p large] at h
    simpa only [build, dif_pos large, Index.contains] using h
  · exact (PaperB.SmallQuotient.cutPair_impossible_of_small (by omega) q).elim

/-- Transfer an ordered-reader membership characterization to the data-only API. -/
theorem query_iff_of_reader_spec (P : CutPair H → Vertex H → Prop)
    (readerSpec : ∀ (large : 3 ≤ H.vertexCount) (q : CutPair H) (v : Vertex H),
      (runOrderedReader p data size_data rank large
        increasing covers rankArc flat).index.contains q v = true ↔ P q v)
    (q : CutPair H) (v : Vertex H) :
    Index.contains (build p data size_data rank increasing covers rankArc flat) q v =
      true ↔ P q v := by
  by_cases large : 3 ≤ H.vertexCount
  · rw [query_exact p data size_data rank increasing covers rankArc flat q v,
      dif_pos large]
    exact readerSpec large q v
  · exact (PaperB.SmallQuotient.cutPair_impossible_of_small (by omega) q).elim

theorem arraySize_le :
    Index.arraySize (build p data size_data rank increasing covers rankArc flat) ≤
      9 * H.vertexCount := by
  by_cases large : 3 ≤ H.vertexCount
  · simpa only [build, dif_pos large, Index.arraySize] using
      (RetainedProperLoss.arraySize_le
        (runOrderedReader p data size_data rank large increasing covers rankArc flat))
  · simpa only [build, dif_neg large, Index.arraySize] using
      (Nat.zero_le (9 * H.vertexCount))

end

end PaperB.QuotientMembership
