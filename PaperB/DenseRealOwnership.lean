module

public import PaperB.ActualSiblingEmitter
public import PaperB.DenseArcRow

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph.GlobalSibling.ActualOwnership

open _root_.PaperB.EX16Assembly
open _root_.PaperB.Digraph
open _root_.PaperB.Digraph.GlobalSibling
open _root_.PaperB.StaticOriginalSiblingEmitter
open _root_.PaperB.PackedLocalArcs

variable {g : Digraph} {r : Fin g.vertexCount}

private theorem find_of_reachable (q : OriginalReader g r)
    {v : Fin g.vertexCount} (hv : g.InitiallyReachable r v) :
    ∃ i, q.ids.find v = some i := by
  exact ⟨q.slot v hv, q.find_slot v hv⟩

/-- Ownership is measured against the reader's actual dense input. -/
theorem packing_own (q : OriginalReader g r)
    {d : Fin g.vertexCount} (hd : g.InitiallyReachable r d)
    (k : SiblingBlockKey g r d q.parent) :
    Own q.input.root q.input.parent.read
      ((q.ids.find d).getD q.input.root) (packing q d k) := by
  obtain ⟨u, hu⟩ := find_of_reachable q hd
  rcases k.property with he | ⟨hp, hn, hcReach⟩
  · rw [packing, if_pos he]
    change Own q.input.root q.input.parent.read
      ((q.ids.find d).getD q.input.root)
      (rootCode ((q.ids.find d).getD q.input.root))
    rw [hu]
    refine own_of_packed (k := .inl u) ?_ rfl
    apply Fin.ext
    rfl
  · obtain ⟨c, hc⟩ := find_of_reachable q hcReach
    have hit : q.ids.find d = some (q.input.parent.read c) := by
      rw [← hp]
      have hc' := q.find_slot k.val hcReach
      have eq := Option.some.inj (hc'.symm.trans hc)
      simpa only [eq] using q.find_parent_at_slot k.val hcReach
    have hcu : q.input.parent.read c = u :=
      Option.some.inj (hit.symm.trans hu)
    have hcr : c ≠ q.input.root := by
      intro he
      have hr : q.input.parent.read q.input.root = q.input.root :=
        q.reader.input_ok.parent_root
      have hd' : q.ids.find d = some c := by
        simpa only [he, hr] using hit
      apply hn
      exact (q.ids.original_of_slot k.val c hc).symm.trans
        (q.ids.original_of_slot d c hd')
    rw [packing, if_neg hn]
    change Own q.input.root q.input.parent.read
      ((q.ids.find d).getD q.input.root)
      (childCode ((q.ids.find k.val).getD q.input.root))
    rw [hu, hc]
    refine own_of_packed (k := .inr c) ?_ ⟨hcr, hcu⟩
    apply Fin.ext
    rfl

/-- Both endpoints in a runtime row are owned by that row's held vertex. -/
theorem emitAll_row_own {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (q : OriginalReader g r)
    {d : Fin g.vertexCount} (hd : g.InitiallyReachable r d)
    {x : Entry g (2 * q.count)}
    (hx : x ∈ (GlobalSibling.emitAll (getters q)).1.row d) :
    Own q.input.root q.input.parent.read
        ((q.ids.find d).getD q.input.root) x.emission.source ∧
      Own q.input.root q.input.parent.read
        ((q.ids.find d).getD q.input.root) x.emission.destination := by
  have hrow := emitAll_row (parent := q.parent)
    (progress := progress) (injective := injective) (spec := q.parentSpec)
    (T := getters q) (pack := packing q)
    (checked progress injective q) d
  rw [hrow] at hx
  obtain ⟨a, _, ha⟩ := List.mem_filterMap.mp hx
  cases he : siblingEmission? (d := d) (parent := q.parent)
      progress injective q.parentSpec a with
  | none => simp [he] at ha
  | some e =>
      have hx' : (⟨packEmission (packing q) e, a⟩ :
          Entry g (2 * q.count)) = x := by
        simpa only [he, Option.map_some, Option.some.injEq] using ha
      subst x
      constructor <;> exact packing_own q hd _

end PaperB.Digraph.GlobalSibling.ActualOwnership
