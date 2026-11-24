module

public import Challenge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Finite labelled quotient arrays

This reference construction groups arc occurrences by source block. Each row
keeps the input order and all repetitions, including occurrences with identical
labels. No running-time bound is asserted.
-/

namespace PaperB.QuotientArrays

/-- One arc occurrence, with quotient endpoints and an original physical tail. -/
structure ArcOccurrence (n k : Nat) where
  «from» : Fin k
  «to» : Fin k
  origTail : Fin n

/-- Once the source row is chosen, retain the head and physical tail unchanged. -/
def ArcOccurrence.toQuotientArc {n k : Nat} (a : ArcOccurrence n k) :
    QuotientArc n k :=
  { head := a.«to», origTail := a.origTail }

variable {n k : Nat}

/-- Select the occurrences leaving `u`, then convert each one to a quotient arc. -/
def groupedRow (occurrences : List (ArcOccurrence n k)) (u : Fin k) :
    List (QuotientArc n k) :=
  (occurrences.filter (fun a => decide (a.«from» = u))).map
    ArcOccurrence.toQuotientArc

/-- Build one adjacency row for each quotient block. -/
def ofOccurrences (root : Fin k) (occurrences : List (ArcOccurrence n k)) :
    LabelledQuotient where
  origVertexCount := n
  vertexCount := k
  root := root
  adj := Array.ofFn (n := k) (groupedRow occurrences)
  adj_size := by simp only [Array.size_ofFn]

theorem outArcs_ofOccurrences (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) (u : Fin k) :
    (ofOccurrences (n := n) (k := k) root occurrences).outArcs u =
      (occurrences.filter (fun a => decide (a.«from» = u))).map
        ArcOccurrence.toQuotientArc := by
  cases u with
  | mk i hi =>
    simp [LabelledQuotient.outArcs, ofOccurrences, groupedRow, Array.getElem_ofFn]

/-- Row membership matches both the quotient head and the physical tail. -/
theorem mem_outArcs_ofOccurrences (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) (u : Fin k)
    (e : QuotientArc n k) :
    e ∈ (ofOccurrences (n := n) (k := k) root occurrences).outArcs u ↔
      ∃ a ∈ occurrences,
        a.«from» = u ∧ a.«to» = e.head ∧ a.origTail = e.origTail := by
  rw [outArcs_ofOccurrences (n := n) (k := k) root occurrences u]
  constructor
  · intro he
    rcases List.mem_map.mp he with ⟨a, ha, rfl⟩
    have hSource : a ∈ occurrences ∧ a.«from» = u := by
      simpa only [List.mem_filter, decide_eq_true_eq] using ha
    exact ⟨a, hSource.1, hSource.2, rfl, rfl⟩
  · rintro ⟨a, ha, hFrom, hTo, hTail⟩
    apply List.mem_map.mpr
    refine ⟨a, ?_, ?_⟩
    · simpa only [List.mem_filter, decide_eq_true_eq] using
        (And.intro ha hFrom)
    · cases e with
      | mk head origTail =>
        change a.«to» = head at hTo
        change a.origTail = origTail at hTail
        change QuotientArc.mk a.«to» a.origTail = QuotientArc.mk head origTail
        rw [hTo, hTail]

/-- Forgetting the physical tail gives exactly the input endpoint relation. -/
theorem hasQuotientArc_ofOccurrences (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) (u w : Fin k) :
    (ofOccurrences (n := n) (k := k) root occurrences).HasQuotientArc u w ↔
      ∃ a ∈ occurrences, a.«from» = u ∧ a.«to» = w := by
  unfold LabelledQuotient.HasQuotientArc
  constructor
  · rintro ⟨e, he, hHead⟩
    rcases (mem_outArcs_ofOccurrences (n := n) (k := k)
      root occurrences u e).mp he with ⟨a, ha, hFrom, hTo, _⟩
    exact ⟨a, ha, hFrom, hTo.trans hHead⟩
  · rintro ⟨a, ha, hFrom, hTo⟩
    refine ⟨a.toQuotientArc, ?_, hTo⟩
    exact (mem_outArcs_ofOccurrences (n := n) (k := k)
      root occurrences u a.toQuotientArc).mpr ⟨a, ha, hFrom, rfl, rfl⟩

end PaperB.QuotientArrays
