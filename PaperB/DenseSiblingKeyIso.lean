module

public import PaperB.DenseRealOwnership
public import PaperB.DenseArcRecode

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.DenseQuotientRows

open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath
open PaperB.Digraph

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : PaperB.EX16Assembly.OriginalReader g r)

private theorem heldOriginal_inj {a b : Fin q.count}
    (h : q.ids.originals.read a = q.ids.originals.read b) : a = b := by
  apply Option.some.inj
  calc
    some a = q.ids.find (q.ids.originals.read a) := (q.ids.slot_of_original a).symm
    _ = q.ids.find (q.ids.originals.read b) := congrArg q.ids.find h
    _ = some b := q.ids.slot_of_original b

private theorem original_find_getD (v : Fin g.vertexCount)
    (hv : g.InitiallyReachable r v) :
    q.ids.originals.read ((q.ids.find v).getD q.input.root) = v := by
  simpa only [q.find_slot v hv, Option.getD] using q.original_at_slot v hv

variable {buckets : ChildLists q.count} (u : Fin q.count)
variable (childOK : ∀ c : Fin q.count,
  c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)

def occurrenceToOriginal :
    Occurrence buckets u →
      SiblingBlockKey g r (q.ids.originals.read u) q.parent
  | ⟨.inl _, _⟩ => ⟨q.ids.originals.read u, Or.inl rfl⟩
  | ⟨.inr c, hc⟩ =>
      let h := (childOK c).mp hc
      ⟨q.ids.originals.read c, Or.inr
        ⟨(q.parent_at_original c).trans (congrArg q.ids.originals.read h.1),
          fun he => h.2 (heldOriginal_inj q he),
          q.ids.original_reachable c⟩⟩

def originalToOccurrence
    (k : SiblingBlockKey g r (q.ids.originals.read u) q.parent) :
    Occurrence buckets u :=
  if h : k.val = q.ids.originals.read u then
    ⟨.inl u, rfl⟩
  else
    let c := (q.ids.find k.val).getD q.input.root
    ⟨.inr c, by
      change c ∈ buckets.get u
      have hk := k.property.resolve_left h
      have hc : q.ids.originals.read c = k.val :=
        original_find_getD q k.val hk.2.2
      have hp : q.input.parent.read c = u := by
        apply heldOriginal_inj q
        calc
          q.ids.originals.read (q.input.parent.read c) =
              q.parent (q.ids.originals.read c) := (q.parent_at_original c).symm
          _ = q.parent k.val := congrArg q.parent hc
          _ = q.ids.originals.read u := hk.1
      exact (childOK c).mpr
        ⟨hp, fun he => h (hc.symm.trans (congrArg q.ids.originals.read he))⟩⟩

@[simp] theorem originalToOccurrence_occurrenceToOriginal
    (k : Occurrence buckets u) :
    originalToOccurrence q u childOK (occurrenceToOriginal q u childOK k) = k := by
  rcases k with ⟨k, hk⟩
  cases k with
  | inl a =>
      change a = u at hk
      subst a
      apply Subtype.ext
      simp [occurrenceToOriginal, originalToOccurrence]
  | inr c =>
      have hn : q.ids.originals.read c ≠ q.ids.originals.read u :=
        fun he => ((childOK c).mp hk).2 (heldOriginal_inj q he)
      apply Subtype.ext
      simp [occurrenceToOriginal, originalToOccurrence, hn,
        q.ids.slot_of_original c, Option.getD]

@[simp] theorem occurrenceToOriginal_originalToOccurrence
    (k : SiblingBlockKey g r (q.ids.originals.read u) q.parent) :
    occurrenceToOriginal q u childOK (originalToOccurrence q u childOK k) = k := by
  apply Subtype.ext
  by_cases h : k.val = q.ids.originals.read u
  · simpa only [originalToOccurrence, dif_pos h, occurrenceToOriginal] using h.symm
  · have hc := original_find_getD q k.val (k.property.resolve_left h).2.2
    simpa only [originalToOccurrence, dif_neg h, occurrenceToOriginal] using hc

variable (rows : Layout buckets)

def positionToOriginal (i : Fin (rows.length u)) :
    SiblingBlockKey g r (q.ids.originals.read u) q.parent :=
  occurrenceToOriginal q u childOK (rows.decode u i)

def originalToPosition
    (k : SiblingBlockKey g r (q.ids.originals.read u) q.parent) :
    Fin (rows.length u) :=
  rows.encode u (originalToOccurrence q u childOK k)

@[simp] theorem originalToPosition_positionToOriginal (i : Fin (rows.length u)) :
    originalToPosition q u childOK rows (positionToOriginal q u childOK rows i) = i := by
  simp only [originalToPosition, positionToOriginal,
    originalToOccurrence_occurrenceToOriginal, Layout.encode_decode]

@[simp] theorem positionToOriginal_originalToPosition
    (k : SiblingBlockKey g r (q.ids.originals.read u) q.parent) :
    positionToOriginal q u childOK rows (originalToPosition q u childOK rows k) = k := by
  simp only [positionToOriginal, originalToPosition, Layout.decode_encode,
    occurrenceToOriginal_originalToOccurrence]

end PaperB.DenseQuotientRows
