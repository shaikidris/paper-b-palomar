module

public import PaperB.ThirdReachableRoute
public import PaperB.FiniteSiblingFlat
public import PaperB.OriginalStaticConnector

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.EX44

open PaperB
open PaperB.Digraph
open PaperB.Digraph.EX44
open PaperB.LabelledQuotient

section FiniteSibling

variable {g : PaperB.Digraph} {n k B E : Nat}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (R : Runtime g.vertexCount n k B E) (W : World g n)
variable (progress : ∀ i j, g.HasArc i j → rank i < rank j)
variable (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
variable (spec : ParentSpec g (W.vertex R.source) parent)

/-- The quotient used by `ThirdForestGeometry` is definitionally the standard
finite sibling quotient. No runtime table entries are needed here. -/
noncomputable def thirdForestGeometryOfFiniteSibling :
    ThirdForestGeometry R W progress injRank spec where
  qRank := fun _d hd => finiteSiblingRank progress injRank spec hd
  rankArc := fun _d hd _i _j h =>
    finiteSiblingRank_lt_of_hasQuotientArc progress injRank spec hd h
  rankInj := fun _d hd _i _j h =>
    finiteSiblingRank_injective progress injRank spec hd h
  flat := fun _d hd => finiteSiblingQuotient_isFlat progress injRank spec hd
  rooted := fun _d hd i => (finiteSiblingQuotient_isFlat progress injRank spec hd).1 i

@[simp] theorem thirdForestGeometryOfFiniteSibling_qRank
    (d : Fin n)
    (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
    (i : Fin (finiteSiblingQuotient progress injRank spec hd).vertexCount) :
    (thirdForestGeometryOfFiniteSibling R W progress injRank spec).qRank d hd i =
      finiteSiblingRank progress injRank spec hd i :=
  rfl

end FiniteSibling

namespace RetainedRouteProof.OriginalStaticConnector

open PaperB.EX16Assembly

section StaticFacts

variable {g : PaperB.Digraph} {n k B E : Nat}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

/-- Geometry and the static facts for the same runtime and world. The
dictionary, membership, and extrema contracts are separate. -/
structure ThirdGeometryWithStaticTree
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
    (spec : ParentSpec g (W.vertex R.source) parent) where
  geometry : ThirdForestGeometry R W progress injRank spec
  ids : NormalizedIDs R W
  domInterval : ∀ a x : Fin n,
    W.Inside a x ↔ g.Dominates (W.vertex R.source) (W.vertex a) (W.vertex x)

theorem ThirdGeometryWithStaticTree.initiallyReachable
    {R : Runtime g.vertexCount n k B E} {W : World g n}
    {progress : ∀ i j, g.HasArc i j → rank i < rank j}
    {injRank : ∀ ⦃i j⦄, rank i = rank j → i = j}
    {spec : ParentSpec g (W.vertex R.source) parent}
    (C : ThirdGeometryWithStaticTree R W progress injRank spec) (d : Fin n) :
    g.InitiallyReachable (W.vertex R.source) (W.vertex d) := by
  obtain ⟨translateSome, translateNone⟩ := C.ids
  have hit := (translateSome (W.vertex d) d).2 rfl
  apply Classical.byContradiction
  intro notReachable
  have miss := (translateNone (W.vertex d)).2 notReachable
  have impossible : some d = none := hit.symm.trans miss
  cases impossible

end StaticFacts

section Install

variable {g : PaperB.Digraph} {r : Fin g.vertexCount} {k B E : Nat}

private theorem thirdRootReachable : g.InitiallyReachable r r := by
  change AvoidPath g.HasArc (fun _ => False) r r
  constructor <;> simp

variable (q : OriginalReader g r)
variable (base : Runtime g.vertexCount q.count k B E)
variable (debit : Nat) (hdebit : debit ≤ B)

/-- Use the existing static connector, with reflexive reachability supplied
rather than assumed. -/
abbrev thirdInstalledRuntime : Runtime g.vertexCount q.count k B E :=
  install q (thirdRootReachable (g := g) (r := r)) base debit hdebit

theorem thirdInstalled_source_vertex :
    (world q).vertex (thirdInstalledRuntime q base debit hdebit).source = r :=
  source_vertex q (thirdRootReachable (g := g) (r := r)) base debit hdebit

variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

theorem thirdInstalled_parentSpec (spec : ParentSpec g r parent) :
    ParentSpec g
      ((world q).vertex (thirdInstalledRuntime q base debit hdebit).source)
      parent := by
  simpa only [thirdInstalled_source_vertex q base debit hdebit] using spec

variable (progress : ∀ i j, g.HasArc i j → rank i < rank j)
variable (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j)
variable (spec : ParentSpec g r parent)

/-- Install the canonical geometry alongside the original reader's proved
ID and dominator-interval facts. -/
noncomputable def installedThirdGeometry :
    ThirdGeometryWithStaticTree (thirdInstalledRuntime q base debit hdebit)
      (world q) progress injRank
      (thirdInstalled_parentSpec q base debit hdebit spec) where
  geometry :=
    thirdForestGeometryOfFiniteSibling (thirdInstalledRuntime q base debit hdebit)
      (world q) progress injRank
      (thirdInstalled_parentSpec q base debit hdebit spec)
  ids :=
    normalizedIDs q (thirdRootReachable (g := g) (r := r)) base debit hdebit
  domInterval := fun a x =>
    (dominance q (thirdRootReachable (g := g) (r := r)) base debit hdebit a x).symm

@[simp] theorem installedThirdGeometry_qRank
    (d : Fin q.count)
    (hd : g.InitiallyReachable
      ((world q).vertex (thirdInstalledRuntime q base debit hdebit).source)
      ((world q).vertex d))
    (i : Fin (finiteSiblingQuotient progress injRank
      (thirdInstalled_parentSpec q base debit hdebit spec) hd).vertexCount) :
    (installedThirdGeometry q base debit hdebit progress injRank spec).geometry.qRank
        d hd i =
      finiteSiblingRank progress injRank
        (thirdInstalled_parentSpec q base debit hdebit spec) hd i :=
  rfl

end Install

end RetainedRouteProof.OriginalStaticConnector

end PaperB.EX44
