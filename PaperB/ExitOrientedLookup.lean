module

public import PaperB.ForestSlimIndex
public import PaperB.OracleRuntime

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.LabelledQuotient
namespace LocalOrderedChecked

open PaperB.RetainedProperLoss PaperB.ForestHead PaperB.EX24.FinalDFS
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep


variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]

/-- The exact retained dictionary address, with the caller's endpoint order. -/
structure CheckedNode where
  node : Nat
  orientation : PaperB.EX44.Orientation

def suppliedOrientation (B : CutPair H) : PaperB.EX44.Orientation :=
  if B.fst < B.snd then .direct else .reversed

/-- `B` supplies two distinct non-root dense IDs in the caller's order.
Only the canonical pair is looked up; no retained nodes or slots are scanned. -/
def query
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) : Option CheckedNode :=
  (RetainedProperLoss.checkedHit r B.canonical).map
    (fun a => ⟨a, suppliedOrientation B⟩)

/-- A hit carries exactly the address returned by the canonical checked read. -/
theorem query_some_iff
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) (hit : CheckedNode) :
    query r B = some hit ↔
      RetainedProperLoss.checkedHit r B.canonical = some hit.node ∧
      hit.orientation = suppliedOrientation B := by
  cases hit with
  | mk a o =>
    cases hc : RetainedProperLoss.checkedHit r B.canonical <;>
      simp [query, hc, Option.map, eq_comm]

theorem query_none_iff
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) :
    query r B = none ↔ RetainedProperLoss.checkedHit r B.canonical = none := by
  cases hc : RetainedProperLoss.checkedHit r B.canonical <;>
    simp [query, hc, Option.map]

/-- Canonicalization changes endpoint order, not the failure predicate. -/
theorem properLoss_canonical_iff (B : CutPair H) (y : Vertex H) :
    H.ProperLoss B.canonical y ↔ H.ProperLoss B y := by
  unfold ProperLoss
  exact and_congr (lost_canonical_iff H B y)
    (not_congr (B.canonical_mem_iff y))

theorem known_true_iff_properLoss_of_query_some
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) (y : Vertex H) (hit : CheckedNode)
    (got : query r B = some hit) :
    (RetainedProperLoss.ofOrderedReader r).known hit.node
        ((orderedConfig p large).vertexIndex y) = true ↔
      H.ProperLoss B y := by
  have hc := ((query_some_iff r B hit).mp got).1
  exact
    (RetainedProperLoss.known_true_iff_properLoss_of_checkedHit_some
      r B.canonical y (CutPair.canonical_lt B) hit.node hc).trans
      (properLoss_canonical_iff B y)

theorem not_properLoss_of_query_none
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) (y : Vertex H) (miss : query r B = none) :
    ¬ H.ProperLoss B y := by
  intro hl
  exact RetainedProperLoss.not_properLoss_of_checkedHit_none
    r B.canonical y (CutPair.canonical_lt B) ((query_none_iff r B).mp miss)
    ((properLoss_canonical_iff B y).mpr hl)

/-- Reorder any two endpoint-indexed coordinates using the stored orientation. -/
theorem query_orders_coordinates
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) (hit : CheckedNode) (got : query r B = some hit)
    {α : Type} (coord : Fin H.vertexCount → α) :
    PaperB.EX44.Orientation.order hit.orientation
        (coord B.canonical.fst, coord B.canonical.snd) =
      (coord B.fst, coord B.snd) := by
  rw [((query_some_iff r B hit).mp got).2]
  by_cases h : B.fst < B.snd <;>
    simp [suppliedOrientation, CutPair.canonical, PaperB.EX44.Orientation.order, h]

theorem query_endpoint_equations
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) (hit : CheckedNode) (got : query r B = some hit) :
    let ends := PaperB.EX44.Orientation.order hit.orientation
      (B.canonical.fst, B.canonical.snd)
    ends.1 = B.fst ∧ ends.2 = B.snd := by
  have he := query_orders_coordinates r B hit got
    (fun s : Fin H.vertexCount => s)
  exact ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩

/-- At a fixed exit endpoint, the same witnesses work for either failure order. -/
theorem exitTailMem_canonical_iff (B : CutPair H)
    (s y : Fin H.vertexCount) (x : Fin H.origVertexCount) :
    H.ExitTailMem B.canonical s y x ↔ H.ExitTailMem B s y x := by
  constructor
  · rintro ⟨e, he, hx, hp⟩
    exact ⟨e, he, hx,
      AvoidPath.mono hp (fun z hz => (B.canonical_mem_iff z).mpr hz)⟩
  · rintro ⟨e, he, hx, hp⟩
    exact ⟨e, he, hx,
      AvoidPath.mono hp (fun z hz => (B.canonical_mem_iff z).mp hz)⟩

/-- The reordered canonical exit coordinates have the supplied-order semantics. -/
theorem query_orders_exitTailMem
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (B : CutPair H) (hit : CheckedNode) (got : query r B = some hit)
    (y : Fin H.vertexCount) (x : Fin H.origVertexCount) :
    let exits := PaperB.EX44.Orientation.order hit.orientation
      (H.ExitTailMem B.canonical B.canonical.fst y x,
        H.ExitTailMem B.canonical B.canonical.snd y x)
    (exits.1 ↔ H.ExitTailMem B B.fst y x) ∧
      (exits.2 ↔ H.ExitTailMem B B.snd y x) := by
  dsimp only
  rw [query_orders_coordinates r B hit got
    (fun s => H.ExitTailMem B.canonical s y x)]
  exact ⟨exitTailMem_canonical_iff B B.fst y x,
    exitTailMem_canonical_iff B B.snd y x⟩

end LocalOrderedChecked
end PaperB.LabelledQuotient
