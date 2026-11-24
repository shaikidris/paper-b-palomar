module

public import PaperB.DenseRealOwnership
public import PaperB.FastQuotientRows
public import PaperB.DenseArcRow
public import PaperB.QuotientArrays

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.DenseOriginalQuotient

open Digraph PaperB.EX16Assembly
open PackedStaticLayout StaticOriginalSiblingEmitter
open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open PaperB.DenseQuotientRows

def physical {g : Digraph} {k : Nat}
    (xs : List (Digraph.GlobalSibling.Entry g k)) :
    PackedLocalArcs.PhysicalRow k (Fin g.vertexCount) :=
  let buf := xs.toArray
  ⟨buf.size, fun i =>
    let e := (buf[i.val]'i.isLt).emission
    ⟨e.source, e.destination, e.tail⟩⟩

variable {g : Digraph} {r : Fin g.vertexCount} {rank : Fin g.vertexCount → Nat}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (q : OriginalReader g r)
variable (originalRows : EX51.Rows g.vertexCount
  (Digraph.GlobalSibling.Entry g (2 * q.count)))
variable (hRows : originalRows = (StaticOriginalSiblingEmitter.emitAll q).1)
variable (u : Fin q.count)
variable (hd : g.InitiallyReachable r (q.ids.originals.read u))
variable (hFind : q.ids.find (q.ids.originals.read u) = some u)

/-- Read the existing row at the original vertex represented by `u`. -/
def emitted : List (Digraph.GlobalSibling.Entry g (2 * q.count)) :=
  originalRows.row (q.ids.originals.read u)

include progress injective hRows hd hFind in
private theorem physical_valid :
    PackedLocalArcs.Valid (physical (emitted q originalRows u))
      q.input.root q.input.parent.read u := by
  intro i
  have hi : i.val < (emitted q originalRows u).length := by
    simpa [physical] using i.isLt
  have hm :
      (emitted q originalRows u)[i.val]'hi ∈
        (StaticOriginalSiblingEmitter.emitAll q).1.row
          (q.ids.originals.read u) := by
    rw [← hRows]
    exact List.getElem_mem hi
  simpa [physical, hFind] using
    (Digraph.GlobalSibling.ActualOwnership.emitAll_row_own progress injective q hd hm)

variable {buckets : ChildLists q.count}
variable (rows : DenseQuotientRows.Layout buckets)
variable (childOK : ∀ d c : Fin q.count,
  c ∈ buckets.get d ↔ c ≠ q.input.root ∧ q.input.parent.read c = d)

def occurrenceAt
    (p : PackedLocalArcs.PhysicalRow (2 * q.count) (Fin g.vertexCount))
    (own : PackedLocalArcs.Valid p q.input.root q.input.parent.read u)
    (i : Fin p.size) : QuotientArrays.ArcOccurrence g.vertexCount (rows.length u) :=
  let a := PackedLocalArcs.induced rows u childOK p own i
  ⟨a.tail, a.head, a.label⟩

def occurrences : List (QuotientArrays.ArcOccurrence g.vertexCount (rows.length u)) :=
  let xs := emitted q originalRows u
  let p := physical xs
  List.ofFn (occurrenceAt (q := q) u rows childOK p
    (physical_valid progress injective q originalRows hRows u hd hFind))

theorem occurrence_labels :
    (occurrences progress injective q originalRows hRows u hd hFind rows childOK).map
        QuotientArrays.ArcOccurrence.origTail =
      (emitted q originalRows u).map (fun e => e.emission.tail) := by
  apply List.ext_getElem
  · simp [occurrences, physical]
  · intro i hi hj
    simp [occurrences, occurrenceAt, PackedLocalArcs.induced, physical]

def build (hzero : 0 < rows.length u) : LabelledQuotient :=
  FastQuotientRows.ofOccurrences ⟨0, hzero⟩
    (occurrences progress injective q originalRows hRows u hd hFind rows childOK)

/-- Adjacency is the stable restriction of the occurrences, including duplicates. -/
theorem outArcs_build (hzero : 0 < rows.length u) (v : Fin (rows.length u)) :
    (build progress injective q originalRows hRows u hd hFind rows childOK hzero).outArcs v =
      QuotientArrays.groupedRow
        (occurrences progress injective q originalRows hRows u hd hFind rows childOK) v :=
  FastQuotientRows.outArcs_eq_groupedRow ⟨0, hzero⟩
    (occurrences progress injective q originalRows hRows u hd hFind rows childOK) v

end PaperB.DenseOriginalQuotient
