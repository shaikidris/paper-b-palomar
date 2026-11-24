module

public import PaperB.ForestPackedOrderedReader
public import PaperB.StaticGroupedTreeReader
public import PaperB.ForestSlimIndex

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead

namespace EX24.FinalDFS

variable {H : LabelledQuotient} {c : Config H}
variable {rank : Vertex H → Nat} {out : State H}

/-- Build the final index directly from the occupied packed records. -/
def buildGrouped (h : OutputOK c rank out) : Index c rank out :=
  ⟨h, StaticGroupedTreeReader.build (packedInput h) (packedInput_ok h)⟩

theorem buildGrouped_eq (h : OutputOK c rank out) :
    buildGrouped h = build h :=
  congrArg
    (fun reader : StaticTreeReader.Reader (packedInput h) =>
      (⟨h, reader⟩ : Index c rank out))
    (StaticGroupedTreeReader.build_eq (packedInput h) (packedInput_ok h))

end EX24.FinalDFS

open PaperB.EX24.FinalDFS

/-- Run the sweep with one packed configuration and finish with the grouped
reader. The reference reader is used only in erased proofs. -/
def runOrderedReaderFast {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (data : Array (Vertex H))
    (size_data : data.size = H.vertexCount) (rank : Vertex H → Nat)
    (large : 3 ≤ H.vertexCount) [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) : OrderedReaderResult p data size_data rank large :=
  runOrderedReaderPacked p data size_data rank large increasing covers rankArc flat
    (fun {c} {out} h => buildGrouped (c := c) (out := out) h)
    (fun {c} {out} h => buildGrouped_eq (c := c) (out := out) h)

section FastReaderFacts

variable {H : LabelledQuotient}
variable {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
variable {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
variable {large : 3 ≤ H.vertexCount} [DecidableEq (CutPair H)]
variable
  (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
    rank (orderedVertexAt data size_data i) <
      rank (orderedVertexAt data size_data j))
  (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
    orderedVertexAt data size_data i = v)
  (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
  (flat : H.IsFlat)

theorem runOrderedReaderFast_contains_true_iff (q : CutPair H) (y : Vertex H) :
    (runOrderedReaderFast p data size_data rank large increasing covers rankArc
      flat).index.contains q y = true ↔ q.fst < q.snd ∧ H.ProperLoss q y :=
  (runOrderedReaderFast p data size_data rank large increasing covers rankArc
    flat).contains_true_iff q y

/-- The endpoint columns store exactly the occupied prefix, including slot zero. -/
theorem runOrderedReaderFast_column_sizes :
    let r := runOrderedReaderFast p data size_data rank large increasing covers
      rankArc flat
    let s := RetainedProperLoss.ofOrderedReader r
    s.dict.size ≤ H.vertexCount ∧
      s.slots.size = s.dict.size ∧
      s.back.size = (orderedConfig p large).region.maxNodes + 1 ∧
      s.labels.size ≤ H.vertexCount + 1 ∧
      s.entry.size = r.out.tables.next ∧
      s.stop.size = r.out.tables.next := by
  intro r s
  have hd : s.dict.size ≤ H.vertexCount := by
    change (ForestDictionary.dictionary p (orderedConfig p large).code).size ≤
      H.vertexCount
    exact (ForestDictionary.dictionary_spec p (orderedConfig p large).code).2.2
  have hl : s.labels.size ≤ H.vertexCount + 1 := by
    change r.out.labels.size ≤ H.vertexCount + 1
    have h := r.index.ok.1
    omega
  have hn := nodeCount_eq_next r.index.ok
  obtain ⟨_, _, G, _, _⟩ := r.index.ok.2.2
  exact ⟨hd, G.slot_size, G.back_size, hl,
    r.index.reader.layout.endpoints.entry.len.trans hn,
    r.index.reader.layout.endpoints.stop.len.trans hn⟩

end FastReaderFacts
end PaperB
