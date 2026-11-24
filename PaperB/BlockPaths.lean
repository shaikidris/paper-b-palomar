module

public import PaperB.Spec

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

structure BlockSystem (V C : Type) where
  block : V → C
  leader : C → V
  leader_block : ∀ c : C, block (leader c) = c
  arc : V → V → Prop
  internal : ∀ (c : C) (v : V), block v = c →
    AvoidPath arc (fun x : V => block x ≠ c) (leader c) v

namespace BlockSystem

variable {V C : Type}

/-- The label `tail` names the physical vertex from which this exit departs. -/
structure LabelledStep (S : BlockSystem V C) (c d : C) (tail : V) : Prop where
  distinct : c ≠ d
  tail_block : S.block tail = c
  out_arc : S.arc tail (S.leader d)

/-- A selected exit can also carry an arbitrary caller-supplied label. -/
structure TaggedExit (S : BlockSystem V C) (Label : Type) (c d : C) where
  label : Label
  tail : V
  witness : S.LabelledStep c d tail

variable (S : BlockSystem V C)

def QuotientEdge (c d : C) : Prop :=
  ∃ tail : V, S.LabelledStep c d tail

def VertexFailed (failed : C → Prop) : V → Prop :=
  fun v => failed (S.block v)

/-- In a surviving block, failure of a vertex implies that it lies outside
the block. This is the implication required by `AvoidPath.mono`. -/
theorem lift_internal {failed : C → Prop} {c : C} {v : V}
    (hc : ¬ failed c) (hv : S.block v = c) :
    AvoidPath S.arc (S.VertexFailed failed) (S.leader c) v := by
  refine AvoidPath.mono (S.internal c v hv) ?_
  intro x hx hxc
  change failed (S.block x) at hx
  exact hc (by simpa only [hxc] using hx)

/-- Lift each quotient step by walking to its witnessed tail and taking its
physical exit arc to the next leader. -/
theorem lift {failed : C → Prop} {s t : C}
    (path : AvoidPath S.QuotientEdge failed s t) :
    AvoidPath S.arc (S.VertexFailed failed) (S.leader s) (S.leader t) := by
  induction path with
  | refl c hc =>
      exact AvoidPath.refl (S.leader c) (by
        simpa only [VertexFailed, S.leader_block] using hc)
  | step c d t hc edge _ ih =>
      rcases edge with ⟨tail, h⟩
      have hAlive : ¬ S.VertexFailed failed tail := by
        simpa only [VertexFailed, h.tail_block] using hc
      exact AvoidPath.trans (S.lift_internal hc h.tail_block)
        (AvoidPath.step tail (S.leader d) (S.leader t) hAlive h.out_arc ih)

/-- Prepend the supplied physical arc, without selecting a tail from an
unlabelled quotient edge. -/
theorem lift_first_arc {failed : C → Prop} {d t : C}
    (tail : V) (hAlive : ¬ failed (S.block tail))
    (hArc : S.arc tail (S.leader d))
    (suffix : AvoidPath S.QuotientEdge failed d t) :
    AvoidPath S.arc (S.VertexFailed failed) tail (S.leader t) :=
  AvoidPath.step tail (S.leader d) (S.leader t) hAlive hArc (S.lift suffix)

/-- Retain the selected exit itself, including its label and exact tail. -/
def lift_tagged_exit {Label : Type} {failed : C → Prop} {c d t : C}
    (first : S.TaggedExit Label c d) (hc : ¬ failed c)
    (suffix : AvoidPath S.QuotientEdge failed d t) :
    { chosen : S.TaggedExit Label c d //
      chosen = first ∧
        AvoidPath S.arc (S.VertexFailed failed) chosen.tail (S.leader t) } := by
  refine ⟨first, ⟨rfl, ?_⟩⟩
  exact S.lift_first_arc first.tail
    (by simpa only [first.witness.tail_block] using hc)
    first.witness.out_arc suffix

end BlockSystem

end PaperB
