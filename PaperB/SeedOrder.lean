module

public import Lean
public import Lean.Elab.Tactic.Omega

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX42

universe q v n c

/--
The semantic interface to the proper-loss forest on `H`. For
`buildProperLossForest H rank`, use its actual keys, parent, and label, and
`IsForestAncestor` for `ancestor`. The real-key existence field follows from
`buildProperLossForest_exists_node_iff`; the node-wise ancestor field is
`buildProperLossForest_properLoss_iff_of_node`.

`H` is the original labelled quotient. The arc relation is only a proposition
used in the first-loss argument; no arc list is rebuilt or deduplicated.
-/
structure ProperLossForestWitness {Q : Type q} (H : Q)
    (Vertex : Q → Type v) (Node : Type n) (Cut : Type c) where
  rank : Vertex H → Nat
  distinctRanks : ∀ a b, rank a = rank b → a = b
  hasQuotientArc : Vertex H → Vertex H → Prop
  mem : Cut → Vertex H → Prop
  lost : Cut → Vertex H → Prop
  nodeKey? : Node → Option Cut
  parent : Node → Node
  label : Vertex H → Node
  ancestor : Node → Node → Prop
  ancestor_refl : ∀ u, ancestor u u
  real_has_properLoss :
    ∀ {u B}, nodeKey? u = some B → ∃ y, lost B y ∧ ¬ mem B y
  properLoss_iff_ancestor :
    ∀ {u B}, nodeKey? u = some B → ∀ y,
      (lost B y ∧ ¬ mem B y) ↔ ancestor u (label y)
  edge_properLoss_subset :
    ∀ {u P B}, nodeKey? u = some P → nodeKey? (parent u) = some B →
      ∀ y, (lost P y ∧ ¬ mem P y) → lost B y ∧ ¬ mem B y
  edge_endpoints_lost :
    ∀ {u P B}, nodeKey? u = some P → nodeKey? (parent u) = some B →
      ∀ p, mem P p → lost B p
  edge_distinct_cuts :
    ∀ {u P B}, nodeKey? u = some P → nodeKey? (parent u) = some B →
      ¬ (∀ z, mem B z ↔ mem P z)
  properLoss_follows_endpoints :
    ∀ {B y b}, (lost B y ∧ ¬ mem B y) → mem B b → rank b < rank y
  predecessors_iff_endpoints_of_first_properLoss :
    ∀ {B y}, (lost B y ∧ ¬ mem B y) →
      (∀ z, (lost B z ∧ ¬ mem B z) → rank y ≤ rank z) →
      ∀ z, hasQuotientArc z y ↔ mem B z

private theorem existsMinRank {α : Type v} (rank : α → Nat)
    (p : α → Prop) (hex : ∃ y, p y) :
    ∃ y, p y ∧ ∀ z, p z → rank y ≤ rank z := by
  classical
  have search : ∀ k : Nat, (∃ y, p y ∧ rank y ≤ k) →
      ∃ y, p y ∧ ∀ z, p z → rank y ≤ rank z := by
    intro k
    induction k with
    | zero =>
        intro h
        obtain ⟨y, hy, hzero⟩ := h
        exact ⟨y, hy, fun z _ => Nat.le_trans hzero (Nat.zero_le (rank z))⟩
    | succ k ih =>
        intro h
        by_cases hsmall : ∃ y, p y ∧ rank y ≤ k
        · exact ih hsmall
        · obtain ⟨y, hy, hbound⟩ := h
          refine ⟨y, hy, ?_⟩
          intro z hz
          have hzbound : ¬ rank z ≤ k := fun hle => hsmall ⟨z, hz, hle⟩
          omega
  obtain ⟨y, hy⟩ := hex
  exact search (rank y) ⟨y, hy, Nat.le_refl _⟩

namespace ProperLossForestWitness

variable {Q : Type q} {H : Q} {V : Q → Type v} {N : Type n} {C : Type c}
variable (F : ProperLossForestWitness H V N C)

abbrev ProperLoss (B : C) (y : V H) : Prop :=
  F.lost B y ∧ ¬ F.mem B y

abbrev Fresh (B P : C) (p : V H) : Prop :=
  F.mem P p ∧ ¬ F.mem B p

noncomputable def firstProperLossSeed {u : N} {B : C}
    (hu : F.nodeKey? u = some B) : V H :=
  Classical.choose
    (existsMinRank F.rank (F.ProperLoss B) (F.real_has_properLoss hu))

theorem firstProperLossSeed_spec {u : N} {B : C}
    (hu : F.nodeKey? u = some B) :
    F.ProperLoss B (F.firstProperLossSeed hu) ∧
      ∀ z, F.ProperLoss B z → F.rank (F.firstProperLossSeed hu) ≤ F.rank z :=
  Classical.choose_spec
    (existsMinRank F.rank (F.ProperLoss B) (F.real_has_properLoss hu))

theorem firstProperLossSeed_lt_iff {u : N} {B : C}
    (hu : F.nodeKey? u = some B) (y : V H) :
    F.rank (F.firstProperLossSeed hu) < F.rank y ↔
      ∃ z, F.ProperLoss B z ∧ F.rank z < F.rank y := by
  constructor
  · intro h
    exact ⟨F.firstProperLossSeed hu, (F.firstProperLossSeed_spec hu).1, h⟩
  · intro h
    obtain ⟨z, hz, hzy⟩ := h
    exact Nat.lt_of_le_of_lt ((F.firstProperLossSeed_spec hu).2 z hz) hzy

/-- The parent's first-loss label is not even below the child. -/
theorem firstParent_label_distinction {uP : N} {P B : C}
    (huP : F.nodeKey? uP = some P)
    (huB : F.nodeKey? (F.parent uP) = some B) :
    ¬ F.ancestor uP (F.label (F.firstProperLossSeed huB)) := by
  intro hAnc
  let y := F.firstProperLossSeed huB
  have hB : F.ProperLoss B y := (F.firstProperLossSeed_spec huB).1
  have hP : F.ProperLoss P y := (F.properLoss_iff_ancestor huP y).mpr hAnc
  have hFirstB : ∀ z, F.ProperLoss B z → F.rank y ≤ F.rank z :=
    (F.firstProperLossSeed_spec huB).2
  have hFirstP : ∀ z, F.ProperLoss P z → F.rank y ≤ F.rank z :=
    fun z hz => hFirstB z (F.edge_properLoss_subset huP huB z hz)
  have hPredB := F.predecessors_iff_endpoints_of_first_properLoss hB hFirstB
  have hPredP := F.predecessors_iff_endpoints_of_first_properLoss hP hFirstP
  exact F.edge_distinct_cuts huP huB
    (fun z => (hPredB z).symm.trans (hPredP z))

theorem realParent_seed_lt_child_seed {uP : N} {P B : C}
    (huP : F.nodeKey? uP = some P)
    (huB : F.nodeKey? (F.parent uP) = some B) :
    F.rank (F.firstProperLossSeed huB) < F.rank (F.firstProperLossSeed huP) := by
  have hP := (F.firstProperLossSeed_spec huP).1
  have hle := (F.firstProperLossSeed_spec huB).2 _
    (F.edge_properLoss_subset huP huB _ hP)
  by_cases hlt :
      F.rank (F.firstProperLossSeed huB) < F.rank (F.firstProperLossSeed huP)
  · exact hlt
  · have hrank :
        F.rank (F.firstProperLossSeed huB) = F.rank (F.firstProperLossSeed huP) := by
      omega
    have hy := F.distinctRanks _ _ hrank
    exfalso
    apply F.firstParent_label_distinction huP huB
    rw [hy]
    exact (F.properLoss_iff_ancestor huP _).mp hP

/-- In fact both child endpoints precede the seed, whether fresh or shared. -/
theorem childEndpoint_lt_seed {uP : N} {P : C}
    (huP : F.nodeKey? uP = some P) {p : V H} (hp : F.mem P p) :
    F.rank p < F.rank (F.firstProperLossSeed huP) :=
  F.properLoss_follows_endpoints (F.firstProperLossSeed_spec huP).1 hp

/-- Of the child endpoints, exactly the fresh ones are proper parent losses. -/
theorem edge_endpoint_properLoss_iff {uP : N} {P B : C}
    (huP : F.nodeKey? uP = some P)
    (huB : F.nodeKey? (F.parent uP) = some B)
    {p : V H} (hp : F.mem P p) :
    F.ProperLoss B p ↔ ¬ F.mem B p :=
  ⟨fun h => h.2, fun h => ⟨F.edge_endpoints_lost huP huB p hp, h⟩⟩

/-- Shared endpoints precede the parent seed; fresh ones are at or after it. -/
theorem edge_endpoint_order {uP : N} {P B : C}
    (huP : F.nodeKey? uP = some P)
    (huB : F.nodeKey? (F.parent uP) = some B)
    {p : V H} (hp : F.mem P p) :
    (F.mem B p → F.rank p < F.rank (F.firstProperLossSeed huB)) ∧
    (¬ F.mem B p →
      F.rank (F.firstProperLossSeed huB) ≤ F.rank p ∧
        F.rank p < F.rank (F.firstProperLossSeed huP)) := by
  constructor
  · exact F.properLoss_follows_endpoints (F.firstProperLossSeed_spec huB).1
  · intro hf
    exact ⟨(F.firstProperLossSeed_spec huB).2 p
      ((F.edge_endpoint_properLoss_iff huP huB hp).mpr hf),
      F.childEndpoint_lt_seed huP hp⟩

/--
For each fresh endpoint the parent is on its label chain. Every real cut on
that chain has a seed no later than the endpoint, hence strictly earlier than
the child seed. The key hypothesis excludes the artificial root.
-/
theorem freshEndpoint_dependencies {uP : N} {P B : C}
    (huP : F.nodeKey? uP = some P)
    (huB : F.nodeKey? (F.parent uP) = some B)
    {p : V H} (hp : F.Fresh B P p) :
    F.ancestor (F.parent uP) (F.label p) ∧
    F.rank p < F.rank (F.firstProperLossSeed huP) ∧
    ∀ {uA : N} {A : C} (huA : F.nodeKey? uA = some A),
      F.ancestor uA (F.label p) →
      F.rank (F.firstProperLossSeed huA) ≤ F.rank p ∧
        F.rank (F.firstProperLossSeed huA) < F.rank (F.firstProperLossSeed huP) := by
  have hLostB := (F.edge_endpoint_properLoss_iff huP huB hp.1).mpr hp.2
  have hpEarlier := F.childEndpoint_lt_seed huP hp.1
  refine ⟨(F.properLoss_iff_ancestor huB p).mp hLostB, hpEarlier, ?_⟩
  intro uA A huA hAnc
  have hle := (F.firstProperLossSeed_spec huA).2 p
    ((F.properLoss_iff_ancestor huA p).mpr hAnc)
  exact ⟨hle, Nat.lt_of_le_of_lt hle hpEarlier⟩

/-- A real label's map can be installed by the time its vertex base is built. -/
theorem label_seed_le_vertex {y : V H} {B : C}
    (hy : F.nodeKey? (F.label y) = some B) :
    F.rank (F.firstProperLossSeed hy) ≤ F.rank y :=
  (F.firstProperLossSeed_spec hy).2 y
    ((F.properLoss_iff_ancestor hy y).mpr (F.ancestor_refl (F.label y)))

end ProperLossForestWitness
end EX42
