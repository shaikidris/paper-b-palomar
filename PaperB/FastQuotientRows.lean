module

public import PaperB.QuotientArrays
public import PaperB.ArcBuckets

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.FastQuotientRows

open PaperB.QuotientArrays (ArcOccurrence groupedRow)

variable {n k : Nat}

/-- Build all rows with one `groupMap`, retaining its source-level work count. -/
def ofOccurrencesWithWork (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) : LabelledQuotient × EX51.Work :=
  let p := EX51.groupMap (fun a : ArcOccurrence n k => a.«from»)
    ArcOccurrence.toQuotientArc occurrences
  ( { origVertexCount := n
      vertexCount := k
      root := root
      adj := p.1.cells
      adj_size := p.1.size_eq },
    p.2 )

def ofOccurrences (root : Fin k) (occurrences : List (ArcOccurrence n k)) :
    LabelledQuotient :=
  (ofOccurrencesWithWork root occurrences).1

/-- Exact source-level charges, not a machine running-time bound. -/
theorem ofOccurrencesWithWork_work (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) :
    (ofOccurrencesWithWork root occurrences).2 =
      ⟨k, occurrences.length, occurrences.length, occurrences.length, k⟩ :=
  EX51.groupMap_work (fun a : ArcOccurrence n k => a.«from»)
    ArcOccurrence.toQuotientArc occurrences

theorem ofOccurrences_eq (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) :
    ofOccurrences root occurrences = QuotientArrays.ofOccurrences root occurrences := by
  let rows := (EX51.groupMap (fun a : ArcOccurrence n k => a.«from»)
    ArcOccurrence.toQuotientArc occurrences).1
  have hAdj : rows.cells = Array.ofFn (n := k) (groupedRow occurrences) := by
    apply Array.ext
    · simpa only [Array.size_ofFn] using rows.size_eq
    · intro i hi hj
      have hik : i < k := by simpa only [rows.size_eq] using hi
      rw [Array.getElem_ofFn]
      exact EX51.groupMap_row (fun a : ArcOccurrence n k => a.«from»)
        ArcOccurrence.toQuotientArc occurrences ⟨i, hik⟩
  have mk_eq (a b : Array (List (QuotientArc n k)))
      (ha : a.size = k) (hb : b.size = k) (h : a = b) :
      (⟨n, k, root, a, ha⟩ : LabelledQuotient) = ⟨n, k, root, b, hb⟩ := by
    subst b
    rfl
  exact mk_eq rows.cells (Array.ofFn (n := k) (groupedRow occurrences))
    rows.size_eq (by simp only [Array.size_ofFn]) hAdj

theorem outArcs_ofOccurrences (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) (u : Fin k) :
    (ofOccurrences root occurrences).outArcs u =
      (occurrences.filter (fun a => decide (a.«from» = u))).map
        ArcOccurrence.toQuotientArc := by
  change (EX51.groupMap (fun a : ArcOccurrence n k => a.«from»)
    ArcOccurrence.toQuotientArc occurrences).1.row u = _
  exact EX51.groupMap_row _ _ _ _

theorem outArcs_eq_groupedRow (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) (u : Fin k) :
    (ofOccurrences root occurrences).outArcs u = groupedRow occurrences u :=
  outArcs_ofOccurrences root occurrences u

theorem mem_outArcs_ofOccurrences (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) (u : Fin k)
    (e : QuotientArc n k) :
    e ∈ (ofOccurrences root occurrences).outArcs u ↔
      ∃ a ∈ occurrences,
        a.«from» = u ∧ a.«to» = e.head ∧ a.origTail = e.origTail := by
  rw [outArcs_ofOccurrences]
  have h := QuotientArrays.mem_outArcs_ofOccurrences root occurrences u e
  rw [QuotientArrays.outArcs_ofOccurrences] at h
  exact h

end PaperB.FastQuotientRows
