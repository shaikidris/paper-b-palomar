module

-- PaperB/FiniteSiblingExitKernels.lean
-- lean-toolchain: leanprover/lean4:v4.35.0-rc3

public import Lean
public import PaperB.FiniteSiblingFlat
public import PaperB.ExitKernels

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.FiniteSiblingExitKernels

open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ExitMap
open PaperB.ExitSummary
open PaperB.BuiltExit

section OriginalInstance

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)
variable (hd : g.InitiallyReachable r d)

/-- The membership certificate supplied by the global one-pass emitter.
The kernel reads the supplied packed rows; it does not construct rows by
filtering the global emission list. -/
abbrev IncomingExact
    (incoming : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount →
      List (SiblingEmission g r d parent)) : Prop :=
  ∀ w e, e ∈ incoming w ↔
    e ∈ siblingEmissions progress injective spec ∧
      e.destination = decodeSiblingBlockKey g r d parent w

variable
  (incoming : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount →
    List (SiblingEmission g r d parent))
variable (incoming_exact : IncomingExact progress injective spec hd incoming)

-- Unlike HasQuotientArc, this bridge retains the original physical tail.
include incoming_exact in
private theorem out_iff_incoming
    (z w : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount)
    (x : Fin (finiteSiblingQuotient progress injective spec hd).origVertexCount) :
    (⟨w, x⟩ : QuotientArc
      (finiteSiblingQuotient progress injective spec hd).origVertexCount
      (finiteSiblingQuotient progress injective spec hd).vertexCount) ∈
        (finiteSiblingQuotient progress injective spec hd).outArcs z ↔
      ∃ e ∈ incoming w,
        encodeSiblingBlockKey g r d parent e.source = z ∧ e.tail = x := by
  change Fin (siblingBlockKeys g r d parent).length at z w
  change Fin g.vertexCount at x
  have hout :
      (⟨w, x⟩ : QuotientArc g.vertexCount (siblingBlockKeys g r d parent).length) ∈
          (finiteSiblingQuotient progress injective spec hd).outArcs z ↔
        ∃ e ∈ siblingEmissions progress injective spec,
          e.source = decodeSiblingBlockKey g r d parent z ∧
            e.destination = decodeSiblingBlockKey g r d parent w ∧ e.tail = x :=
    mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd z
      (a := ⟨w, x⟩)
  constructor
  · intro ha
    obtain ⟨e, he, hs, hw, hx⟩ := hout.mp ha
    refine ⟨e, (incoming_exact w e).mpr ⟨he, hw⟩, ?_, hx⟩
    simpa only [encodeSiblingBlockKey_decodeSiblingBlockKey] using
      congrArg (encodeSiblingBlockKey g r d parent) hs
  · rintro ⟨e, he, hs, hx⟩
    obtain ⟨he', hw⟩ := (incoming_exact w e).mp he
    apply hout.mpr
    refine ⟨e, he', ?_, hw, hx⟩
    simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
      congrArg (decodeSiblingBlockKey g r d parent) hs

include incoming_exact in
private theorem arc_iff_incoming
    (z w : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount) :
    (finiteSiblingQuotient progress injective spec hd).HasQuotientArc z w ↔
      ∃ e ∈ incoming w, encodeSiblingBlockKey g r d parent e.source = z := by
  unfold LabelledQuotient.HasQuotientArc
  constructor
  · rintro ⟨⟨v, x⟩, ha, hv⟩
    change v = w at hv
    subst v
    obtain ⟨e, he, hs, _⟩ :=
      (out_iff_incoming progress injective spec hd incoming incoming_exact z w x).mp ha
    exact ⟨e, he, hs⟩
  · rintro ⟨e, he, hs⟩
    exact ⟨⟨w, e.tail⟩,
      (out_iff_incoming progress injective spec hd incoming incoming_exact
        z w e.tail).mpr ⟨e, he, hs, rfl⟩, rfl⟩

private theorem exit_iff_out
    (B : CutPair (finiteSiblingQuotient progress injective spec hd))
    (s y : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount)
    (x : Fin (finiteSiblingQuotient progress injective spec hd).origVertexCount)
    (_hs : B.Mem s) :
    (finiteSiblingQuotient progress injective spec hd).ExitTailMem B s y x ↔
      ∃ a ∈ (finiteSiblingQuotient progress injective spec hd).outArcs s,
        a.origTail = x ∧
          (finiteSiblingQuotient progress injective spec hd).SurvivingPath B.Mem a.head y := by
  have alive (w : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount)
      (p : (finiteSiblingQuotient progress injective spec hd).SurvivingPath B.Mem w y) :
      ¬ B.Mem w := by
    change AvoidPath (finiteSiblingQuotient progress injective spec hd).HasQuotientArc
      B.Mem w y at p
    cases p <;> assumption
  unfold LabelledQuotient.ExitTailMem
  first
  | rfl
  | (simp only [_hs, true_and, and_true]; done)
  | grind

include incoming_exact in
private theorem exit_iff_incoming
    (B : CutPair (finiteSiblingQuotient progress injective spec hd))
    (s y : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount)
    (x : Fin (finiteSiblingQuotient progress injective spec hd).origVertexCount)
    (hs : B.Mem s) :
    (finiteSiblingQuotient progress injective spec hd).ExitTailMem B s y x ↔
      ∃ w e, e ∈ incoming w ∧
        encodeSiblingBlockKey g r d parent e.source = s ∧ e.tail = x ∧
          (finiteSiblingQuotient progress injective spec hd).SurvivingPath B.Mem w y := by
  refine (exit_iff_out progress injective spec hd B s y x hs).trans ?_
  constructor
  · rintro ⟨⟨w, t⟩, ha, ht, hp⟩
    change t = x at ht
    subst t
    obtain ⟨e, he, heSource, heTail⟩ :=
      (out_iff_incoming progress injective spec hd incoming incoming_exact s w x).mp ha
    exact ⟨w, e, he, heSource, heTail, hp⟩
  · rintro ⟨w, e, he, heSource, heTail, hp⟩
    exact ⟨⟨w, x⟩,
      (out_iff_incoming progress injective spec hd incoming incoming_exact
        s w x).mpr ⟨e, he, heSource, heTail⟩, rfl, hp⟩

private def ends (B : CutPair (finiteSiblingQuotient progress injective spec hd)) :
    Two (Fin (finiteSiblingQuotient progress injective spec hd).vertexCount) :=
  ⟨B.fst, B.snd⟩

private theorem mem_iff_ends
    (B : CutPair (finiteSiblingQuotient progress injective spec hd))
    (s : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount) :
    B.Mem s ↔
      ∃ j : Fin 2, Two.get (ends progress injective spec hd B) j = s := by
  unfold CutPair.Mem
  constructor
  · rintro (h | h)
    · refine ⟨0, ?_⟩
      rw [Two.get_zero]
      first | exact h | exact h.symm
    · refine ⟨1, ?_⟩
      rw [Two.get_one]
      first | exact h | exact h.symm
  · rintro ⟨j, hj⟩
    have hj' : j = 0 ∨ j = 1 := by
      have hlt := j.isLt
      have hv : j.val = 0 ∨ j.val = 1 := by omega
      exact hv.elim (fun h => Or.inl (Fin.ext h))
        (fun h => Or.inr (Fin.ext h))
    rcases hj' with h | h
    · subst j
      rw [Two.get_zero] at hj
      apply Or.inl
      first | exact hj | exact hj.symm
    · subst j
      rw [Two.get_one] at hj
      apply Or.inr
      first | exact hj | exact hj.symm

private theorem owner_proper
    (y : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount)
    (B : CutPair (finiteSiblingQuotient progress injective spec hd))
    (h : (buildProperLossForest (finiteSiblingQuotient progress injective spec hd)
        (finiteSiblingRank progress injective spec hd)).nodeKey?
      ((buildProperLossForest (finiteSiblingQuotient progress injective spec hd)
        (finiteSiblingRank progress injective spec hd)).label y) = some B) :
    (finiteSiblingQuotient progress injective spec hd).ProperLoss B y := by
  have hi : Function.Injective (finiteSiblingRank progress injective spec hd) :=
    finiteSiblingRank_injective progress injective spec hd
  refine (buildProperLossForest_properLoss_iff_of_node
    (H := finiteSiblingQuotient progress injective spec hd)
    (rank := finiteSiblingRank progress injective spec hd)
    (fun u w ha =>
      finiteSiblingRank_lt_of_hasQuotientArc progress injective spec hd ha)
    (fun _ _ hEq => hi hEq)
    (finiteSiblingQuotient_isFlat progress injective spec hd)
    h y).mpr ?_
  apply IsForestAncestor.refl

-- Reference data for wantMap/wantBase, not an enumeration run by a callback.
private noncomputable def referenceTails
    (B : CutPair (finiteSiblingQuotient progress injective spec hd))
    (s y : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount) :
    List (Fin (finiteSiblingQuotient progress injective spec hd).origVertexCount) := by
  classical
  exact (List.finRange (finiteSiblingQuotient progress injective spec hd).origVertexCount).filter
    (fun x => decide ((finiteSiblingQuotient progress injective spec hd).ExitTailMem B s y x))

private theorem mem_referenceTails
    (B : CutPair (finiteSiblingQuotient progress injective spec hd))
    (s y : Fin (finiteSiblingQuotient progress injective spec hd).vertexCount)
    (x : Fin (finiteSiblingQuotient progress injective spec hd).origVertexCount) :
    x ∈ referenceTails progress injective spec hd B s y ↔
      (finiteSiblingQuotient progress injective spec hd).ExitTailMem B s y x := by
  classical
  simp [referenceTails, List.mem_filter]

/-- Read a driver slot without identifying its index with a forest node. -/
def installedNode {n m : Nat} (slots : Array (Fin n))
    (size_eq : slots.size = m) (i : Fin m) : Fin n :=
  slots[i.val]'(by simpa only [size_eq] using i.isLt)

/-- Both lookups must succeed: an installed slot is a real-child/real-parent
edge, and its keys are exactly the keys supplied by the driver. -/
structure InstalledIdentities {m : Nat}
    (slots : Array (Fin ((buildProperLossForest
      (finiteSiblingQuotient progress injective spec hd)
      (finiteSiblingRank progress injective spec hd)).realNodeCount + 1)))
    (size_eq : slots.size = m)
    (childAt parentAt : Fin m → CutPair (finiteSiblingQuotient progress injective spec hd)) :
    Prop where
  child_at : ∀ i,
    (buildProperLossForest (finiteSiblingQuotient progress injective spec hd)
      (finiteSiblingRank progress injective spec hd)).nodeKey?
        (installedNode slots size_eq i) = some (childAt i)
  parent_at : ∀ i,
    (buildProperLossForest (finiteSiblingQuotient progress injective spec hd)
      (finiteSiblingRank progress injective spec hd)).nodeKey?
        ((buildProperLossForest (finiteSiblingQuotient progress injective spec hd)
          (finiteSiblingRank progress injective spec hd)).parent
            (installedNode slots size_eq i)) = some (parentAt i)

/-- `entryRank` is the physical DFS entry rank. The topological
`finiteSiblingRank` still orders the quotient forest and proves transfer. -/
noncomputable def model {m : Nat}
    (entryRank : Fin g.vertexCount → Nat)
    (slots : Array (Fin ((buildProperLossForest
      (finiteSiblingQuotient progress injective spec hd)
      (finiteSiblingRank progress injective spec hd)).realNodeCount + 1)))
    (size_eq : slots.size = m)
    (childAt parentAt : Fin m → CutPair (finiteSiblingQuotient progress injective spec hd))
    (ids : InstalledIdentities progress injective spec hd slots size_eq
      childAt parentAt) :
    PaperB.BuiltExit.Model (finiteSiblingQuotient progress injective spec hd) m := by
  let Q := finiteSiblingQuotient progress injective spec hd
  let qRank := finiteSiblingRank progress injective spec hd
  let F := buildProperLossForest Q qRank
  let node : Fin m → Fin (F.realNodeCount + 1) := installedNode slots size_eq
  have hc (i : Fin m) : F.nodeKey? (node i) = some (childAt i) :=
    ids.child_at i
  have hp (i : Fin m) : F.nodeKey? (F.parent (node i)) = some (parentAt i) :=
    ids.parent_at i
  refine
    { Occ := SiblingEmission g r d parent
      incoming := incoming
      source := fun e => encodeSiblingBlockKey g r d parent e.source
      physicalTail := fun e => e.tail
      rank := entryRank
      arc_iff := arc_iff_incoming progress injective spec hd incoming incoming_exact
      exit_iff := exit_iff_incoming progress injective spec hd incoming incoming_exact
      ends := ends progress injective spec hd
      mem_iff := mem_iff_ends progress injective spec hd
      owner := fun y => F.nodeKey? (F.label y)
      ownerProper := owner_proper progress injective spec hd
      forest := F
      edgeNode := node
      child := childAt
      parent := parentAt
      childKey := hc
      parentKey := hp
      transfer := ?_
      tails := referenceTails progress injective spec hd
      tails_iff := fun B s y x _ => mem_referenceTails progress injective spec hd B s y x }
  intro i s y x hs hy
  have htransfer := buildProperLossForest_edge_exitTailMem_iff
    (H := Q) (rank := qRank)
    (fun u w ha =>
      finiteSiblingRank_lt_of_hasQuotientArc progress injective spec hd ha)
    (finiteSiblingQuotient_isFlat progress injective spec hd)
    (hc i) (hp i) (x := x) hs hy
  unfold IsFreshEndpoint at htransfer
  first
  | exact htransfer
  | simpa only [and_assoc] using htransfer
  | grind

variable {m : Nat}
variable (entryRank : Fin g.vertexCount → Nat)
variable
  (slots : Array (Fin ((buildProperLossForest
    (finiteSiblingQuotient progress injective spec hd)
    (finiteSiblingRank progress injective spec hd)).realNodeCount + 1)))
  (size_eq : slots.size = m)
variable (childAt parentAt : Fin m → CutPair (finiteSiblingQuotient progress injective spec hd))
variable (ids : InstalledIdentities progress injective spec hd slots size_eq
  childAt parentAt)

@[simp] theorem model_child (i : Fin m) :
    (model progress injective spec hd incoming incoming_exact entryRank
      slots size_eq childAt parentAt ids).child i = childAt i := by
  rfl

@[simp] theorem model_parent (i : Fin m) :
    (model progress injective spec hd incoming incoming_exact entryRank
      slots size_eq childAt parentAt ids).parent i = parentAt i := by
  rfl

/-- Expected type of the EX2.4 route/site descriptors for this instance. -/
abbrev KernelFor (deps : Deps (finiteSiblingQuotient progress injective spec hd).vertexCount m) :=
  Kernel (model progress injective spec hd incoming incoming_exact entryRank
    slots size_eq childAt parentAt ids) deps

end OriginalInstance

/-!
At the theorem 4.1 driver site, take `incoming` from the one-pass emitter's
packed rows and `incoming_exact` from its independently proved membership
certificate. Use

  let W := model progress injective spec hd incoming incoming_exact entryRank
    slots size_eq childAt parentAt ids

and specialize the EX2.4 descriptors `K` to

  Kernel W ⟨D.installBase, D.installMap, D.vertexBase, D.vertexMap⟩.

Use `exitCallbacks% K` at type `Callbacks D ExitMap.Map ExitMap.Values` and
`exitExact% K` at type `Exact P C W.wantMap W.wantBase`. This does not run
the reference tail enumeration or install a map on the artificial root edge.
-/

end PaperB.FiniteSiblingExitKernels
