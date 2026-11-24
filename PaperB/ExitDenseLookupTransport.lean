module

public import PaperB.ExitOrientedLookup
public import PaperB.DenseLabelledArcIso
public import PaperB.LabelledTransport

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.LabelledQuotient.LocalOrderedChecked

open PaperB.ForestHead
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

variable {H K : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]

/-- The checked read is performed on `H`; its loss and exit-tail semantics
are stated on `K`. The transported cut pair keeps the caller's endpoint order. -/
theorem query_transport
    (r : OrderedReaderResult (H := H) p data size_data rank large)
    (f : Fin H.vertexCount → Fin K.vertexCount)
    (hf : ∀ ⦃u v⦄, f u = f v → u = v)
    (hs : ∀ v, ∃ u, f u = v)
    (hr : f H.root = K.root)
    (hN : H.origVertexCount = K.origVertexCount)
    (ha : Transport.ExactAdj f hN)
    (B : CutPair H) :
    let C := Transport.cutPair f hf hr B
    (query r B = none ∧
      RetainedProperLoss.checkedHit r B.canonical = none ∧
      (∀ y : Vertex H, ¬ K.ProperLoss C (f y))) ∨
    (∃ hit : CheckedNode,
      query r B = some hit ∧
      RetainedProperLoss.checkedHit r B.canonical = some hit.node ∧
      hit.orientation = suppliedOrientation B ∧
      (∀ y : Vertex H,
        (RetainedProperLoss.ofOrderedReader r).known hit.node
            ((orderedConfig p large).vertexIndex y) = true ↔
          K.ProperLoss C (f y)) ∧
      (∀ (y : Vertex H) (x : Fin H.origVertexCount),
        let exits := PaperB.EX44.Orientation.order hit.orientation
          (H.ExitTailMem B.canonical B.canonical.fst y x,
            H.ExitTailMem B.canonical B.canonical.snd y x)
        (exits.1 ↔ K.ExitTailMem C C.fst (f y) (Fin.cast hN x)) ∧
          (exits.2 ↔ K.ExitTailMem C C.snd (f y) (Fin.cast hN x)))) := by
  dsimp only
  have outcome : query r B = none ∨ ∃ hit : CheckedNode, query r B = some hit := by
    cases query r B with
    | none => exact Or.inl rfl
    | some hit => exact Or.inr ⟨hit, rfl⟩
  rcases outcome with miss | ⟨hit, got⟩
  · refine Or.inl ⟨miss, (query_none_iff r B).mp miss, ?_⟩
    intro y hy
    exact not_properLoss_of_query_none r B y miss
      ((Transport.properLoss_iff f hf hr hs hN ha B y).mpr hy)
  · have checked := (query_some_iff r B hit).mp got
    refine Or.inr ⟨hit, got, checked.1, checked.2, ?_, ?_⟩
    · intro y
      exact (known_true_iff_properLoss_of_query_some r B y hit got).trans
        (Transport.properLoss_iff f hf hr hs hN ha B y)
    · intro y x
      have ordered := query_orders_exitTailMem r B hit got y x
      exact ⟨ordered.1.trans (Transport.exitTailMem_iff f hf hr hs hN ha B B.fst y x),
        ordered.2.trans (Transport.exitTailMem_iff f hf hr hs hN ha B B.snd y x)⟩

-- In the dense build, specialize with `H := Dq`, `K := Sq`, `f := dForward`,
-- and `hN := rfl`. Pass `exactAdj_build_denseToOld` (with its section
-- arguments) as `ha`, and the dense map's injectivity, surjectivity, and
-- root equation as `hf`, `hs`, and `hr`.

end PaperB.LabelledQuotient.LocalOrderedChecked
