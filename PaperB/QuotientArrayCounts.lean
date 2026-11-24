module

public import PaperB.QuotientArrays
public import PaperB.QuotientBudget

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open QuotientArrays QuotientBudget

open LabelledQuotient

private theorem occurrenceRows_lengthSum {α : Type} (rows : List (List α)) :
    listLengthSum rows = (rows.map List.length).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [listLengthSum, ih]

private theorem occurrenceKeys_nodup (k : Nat) :
    (List.ofFn (id : Fin k → Fin k)).Nodup := by
  rw [List.Nodup, List.pairwise_iff_getElem]
  simp only [List.getElem_ofFn, id_eq, ne_eq, Fin.mk.injEq]
  intros
  omega

/-- Each occurrence contributes one arc, including repeated parallel arcs. -/
theorem arcCount_ofOccurrences {n k : Nat} (root : Fin k)
    (occurrences : List (ArcOccurrence n k)) :
    (ofOccurrences root occurrences).arcCount = occurrences.length := by
  change listLengthSum (Array.ofFn (groupedRow occurrences)).toList =
    occurrences.length
  have h := bucketTotal_eq_length (fun a : ArcOccurrence n k => a.«from»)
    (List.ofFn (id : Fin k → Fin k)) occurrences (occurrenceKeys_nodup k) (by
      intro a _
      rw [List.mem_ofFn]
      exact ⟨a.«from», rfl⟩)
  simpa only [Array.toList_ofFn, occurrenceRows_lengthSum, groupedRow,
    bucketTotal, buckets, List.map_ofFn, Function.comp_def, id_eq,
    List.length_map] using h

end PaperB
