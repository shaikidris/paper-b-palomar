module

public import PaperB.DenseSiblingKeyIso
public import PaperB.DenseArcRecode

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.DenseQuotientRows

open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath PaperB.Digraph

open DenseArcRecode

variable {g : Digraph} {r : Fin g.vertexCount}
variable (q : EX16Assembly.OriginalReader g r)
variable {buckets : ChildLists q.count} (u : Fin q.count)
variable (childOK : ∀ c : Fin q.count,
  c ∈ buckets.get u ↔ q.input.parent.read c = u ∧ c ≠ u)
variable (rows : Layout buckets)

theorem packing_positionToOriginal_eq_codeAt (i : Fin (rows.length u)) :
    StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u)
        (positionToOriginal q u childOK rows i) =
      DenseArcRecode.codeAt (halves q.count) rows u i := by
  change StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u)
      (occurrenceToOriginal q u childOK (rows.decode u i)) =
    (halves q.count).pack (rows.decode u i).val
  cases hi : (rows.decode u i).val with
  | inl a =>
      have ha : a = u := by
        have h := (rows.decode u i).property
        rw [hi] at h
        first | exact h | exact Eq.symm h
      subst a
      have hd : rows.decode u i = (⟨.inl u, rfl⟩ : Occurrence buckets u) :=
        Subtype.ext hi
      rw [hd]
      simp only [StaticOriginalSiblingEmitter.packing, occurrenceToOriginal, if_pos rfl]
      change StaticOriginalSiblingEmitter.rootCode
        ((q.ids.find (q.ids.originals.read u)).getD q.input.root) = _
      rw [q.ids.slot_of_original u] <;> rfl
  | inr c =>
      have hc : c ∈ buckets.get u := by
        have h := (rows.decode u i).property
        rw [hi] at h
        exact h
      have hOcc : Occurs buckets u (.inr c) := hc
      have hd : rows.decode u i = (⟨.inr c, hOcc⟩ : Occurrence buckets u) :=
        Subtype.ext hi
      have hn : q.ids.originals.read c ≠ q.ids.originals.read u := by
        intro h
        have hs := congrArg q.ids.find h
        rw [q.ids.slot_of_original c, q.ids.slot_of_original u] at hs
        exact ((childOK c).mp hc).2 (Option.some.inj hs)
      rw [hd]
      change (if q.ids.originals.read c = q.ids.originals.read u then
        StaticOriginalSiblingEmitter.rootCode
          ((q.ids.find (q.ids.originals.read u)).getD q.input.root)
        else StaticOriginalSiblingEmitter.childCode
          ((q.ids.find (q.ids.originals.read c)).getD q.input.root)) =
        (halves q.count).pack (.inr c)
      rw [if_neg hn]
      rw [q.ids.slot_of_original c] <;>
        first | rfl | exact Fin.ext (Nat.add_comm _ _)

/-- Recoding the packed endpoints of an original sibling emission gives
the row positions of its source and destination, in that order. -/
theorem packedEmission_positions
    (src dst : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
    (hs : Occurs buckets u ((halves q.count).unpack
      (StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) src)))
    (ht : Occurs buckets u ((halves q.count).unpack
      (StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) dst))) :
    (DenseArcRecode.slot (halves q.count) rows u
        (StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) src) hs,
      DenseArcRecode.slot (halves q.count) rows u
        (StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) dst) ht) =
    (originalToPosition q u childOK rows src,
      originalToPosition q u childOK rows dst) := by
  have endpoint (k : SiblingBlockKey g r (q.ids.originals.read u) q.parent)
      (hk : Occurs buckets u ((halves q.count).unpack
        (StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) k))) :
      DenseArcRecode.slot (halves q.count) rows u
          (StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) k) hk =
        originalToPosition q u childOK rows k := by
    have hb : StaticOriginalSiblingEmitter.packing q (q.ids.originals.read u) k =
        DenseArcRecode.codeAt (halves q.count) rows u
          (originalToPosition q u childOK rows k) := by
      simpa only [positionToOriginal_originalToPosition] using
        packing_positionToOriginal_eq_codeAt q u childOK rows
          (originalToPosition q u childOK rows k)
    revert hk
    rw [hb]
    exact fun _ => DenseArcRecode.slot_codeAt (halves q.count) rows u
      (originalToPosition q u childOK rows k)
  exact Prod.ext (endpoint src hs) (endpoint dst ht)

end PaperB.DenseQuotientRows
