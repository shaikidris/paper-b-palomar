module

public import PaperB.FiniteSiblingFlat
public import PaperB.DominatorTree
public import PaperB.QuotientArrayCounts
public import PaperB.QuotientBudget
public import PaperB.FiniteSiblingBudget
public import PaperB.SiblingVertexBudget
public import PaperB.TopologicalRank
public import PaperB.ForestIntervals

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open Digraph LabelledQuotient

/-- Internal arcs are silent. A crossing records its tag and its actual
physical tail, in order. -/
inductive SiblingPhysicalTrace {V C Label : Type}
    (S : BlockSystem V C) (failed : C → Prop) :
    V → V → List (Label × V) → Prop where
  | refl (u : V) (hu : ¬ failed (S.block u)) :
      SiblingPhysicalTrace (Label := Label) S failed u u []
  | inside (u v t : V) (xs : List (Label × V))
      (hu : ¬ failed (S.block u)) (e : S.arc u v)
      (same : S.block u = S.block v)
      (rest : SiblingPhysicalTrace S failed v t xs) :
      SiblingPhysicalTrace S failed u t xs
  | exit (u v t : V) (tag : Label) (xs : List (Label × V))
      (hu : ¬ failed (S.block u)) (e : S.arc u v)
      (different : S.block u ≠ S.block v)
      (rest : SiblingPhysicalTrace S failed v t xs) :
      SiblingPhysicalTrace S failed u t ((tag, u) :: xs)

/-- Each step uses the specified tail, not a tail selected from an
unlabelled quotient edge. Tags may distinguish parallel occurrences. -/
inductive SiblingLabelledTrace {V C Label : Type}
    (S : BlockSystem V C) (failed : C → Prop) :
    C → C → List (Label × V) → Prop where
  | refl (c : C) (hc : ¬ failed c) :
      SiblingLabelledTrace (Label := Label) S failed c c []
  | step (c d t : C) (tag : Label) (tail : V) (xs : List (Label × V))
      (hc : ¬ failed c) (e : S.LabelledStep c d tail)
      (rest : SiblingLabelledTrace S failed d t xs) :
      SiblingLabelledTrace S failed c t ((tag, tail) :: xs)

namespace SiblingCertification

theorem erase_physicalTrace {V C Label : Type}
    {S : BlockSystem V C} {failed : C → Prop}
    {u v : V} {xs : List (Label × V)}
    (h : SiblingPhysicalTrace S failed u v xs) :
    AvoidPath S.arc (S.VertexFailed failed) u v := by
  induction h with
  | refl u hu => exact AvoidPath.refl u hu
  | inside u w v _ hu e _ _ ih => exact AvoidPath.step u w v hu e ih
  | exit u w v _ _ hu e _ _ ih => exact AvoidPath.step u w v hu e ih

theorem mark_physicalPath {V C Label : Type}
    {S : BlockSystem V C} {failed : C → Prop} {u v : V}
    (tag : V → V → Label)
    (h : AvoidPath S.arc (S.VertexFailed failed) u v) :
    ∃ xs : List (Label × V), SiblingPhysicalTrace S failed u v xs := by
  classical
  induction h with
  | refl u hu => exact ⟨[], .refl u hu⟩
  | step u w v hu e _ ih =>
      obtain ⟨xs, hxs⟩ := ih
      by_cases heq : S.block u = S.block w
      · exact ⟨xs, .inside u w v xs hu e heq hxs⟩
      · exact ⟨(tag u w, u) :: xs, .exit u w v (tag u w) xs hu e heq hxs⟩

theorem project_trace {V C Label : Type}
    {S : BlockSystem V C} {failed : C → Prop}
    (crossing : ∀ u v : V, S.arc u v → S.block u ≠ S.block v →
      S.LabelledStep (S.block u) (S.block v) u)
    {u v : V} {xs : List (Label × V)}
    (h : SiblingPhysicalTrace S failed u v xs) :
    SiblingLabelledTrace S failed (S.block u) (S.block v) xs := by
  induction h with
  | refl u hu => exact .refl (S.block u) hu
  | inside u w v _ _ _ same _ ih =>
      rw [same]
      exact ih
  | exit u w v tag xs hu e different _ ih =>
      exact .step (S.block u) (S.block w) (S.block v) tag u xs
        hu (crossing u w e different) ih

private theorem prepend_internal {V C Label : Type}
    {S : BlockSystem V C} {failed : C → Prop} {c : C}
    {u v t : V} {xs : List (Label × V)}
    (hc : ¬ failed c)
    (h : AvoidPath S.arc (fun a => S.block a ≠ c) u v) :
    SiblingPhysicalTrace S failed v t xs →
      SiblingPhysicalTrace S failed u t xs := by
  induction h with
  | refl _ _ => exact fun rest => rest
  | step a b v ha e suffix ih =>
      intro rest
      have hb : ¬ (S.block b ≠ c) := by
        cases suffix <;> assumption
      have ea : S.block a = c := Classical.not_not.mp ha
      have eb : S.block b = c := Classical.not_not.mp hb
      exact .inside a b t xs (by simpa only [ea] using hc) e
        (ea.trans eb.symm) (ih rest)

theorem lift_trace {V C Label : Type}
    {S : BlockSystem V C} {failed : C → Prop} {s t : C}
    {xs : List (Label × V)}
    (h : SiblingLabelledTrace S failed s t xs) :
    SiblingPhysicalTrace S failed (S.leader s) (S.leader t) xs := by
  induction h with
  | refl c hc =>
      exact .refl (S.leader c) (by simpa only [S.leader_block] using hc)
  | step c d t tag tail xs hc e _ ih =>
      have ht : ¬ failed (S.block tail) := by
        simpa only [e.tail_block] using hc
      have hne : S.block tail ≠ S.block (S.leader d) := by
        simpa only [e.tail_block, S.leader_block] using e.distinct
      exact prepend_internal hc (S.internal c tail e.tail_block)
        (.exit tail (S.leader d) (S.leader t) tag xs ht e.out_arc hne ih)

section Builders

variable {g : Digraph} {r : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

theorem crossing_step {d : Fin g.vertexCount} (hd : g.InitiallyReachable r d) :
    let S := siblingBlockSystem progress injective spec hd
    ∀ u v : SiblingVertex g r d, S.arc u v → S.block u ≠ S.block v →
      S.LabelledStep (S.block u) (S.block v) u := by
  dsimp only
  intro u v e hne
  let S := siblingBlockSystem progress injective spec hd
  change S.arc u v at e
  change S.block u ≠ S.block v at hne
  change S.LabelledStep (S.block u) (S.block v) u
  have ho := siblingBlockSystem_crossing_owner progress injective spec hd u v e hne
  first
  | exact ho.1
  | exact ho.2.1
  | refine ⟨hne, rfl, ?_⟩
    have hv : S.leader (S.block v) = v := by
      first
      | exact ho.1
      | exact ho.1.symm
      | exact ho.2.1
      | exact ho.2.1.symm
      | apply Subtype.ext
        first
        | exact ho.1
        | exact ho.1.symm
        | exact ho.2.1
        | exact ho.2.1.symm
        | exact congrArg Subtype.val ho.1
        | exact congrArg Subtype.val ho.1.symm
        | exact congrArg Subtype.val ho.2.1
        | exact congrArg Subtype.val ho.2.1.symm
        | exact?
    simpa only [hv] using e

abbrev ReachableRoot (g : Digraph) (r : Fin g.vertexCount) :=
  {v : Fin g.vertexCount // g.InitiallyReachable r v}

/-- Mark the retained input occurrences before erasing their emission data.
Filtering a list preserves multiplicity, including parallel occurrences. -/
noncomputable def occurrenceMarker
    (d : ReachableRoot g r) (a : Fin g.vertexCount × Fin g.vertexCount) :
    Option Unit := by
  classical
  exact if g.HasArc a.1 a.2 then
    (siblingEmission? (d := d.val) progress injective spec a).map (fun _ => ())
  else none

theorem occurrence_owner
    (d : ReachableRoot g r) {a : Fin g.vertexCount × Fin g.vertexCount}
    {b : Unit} (h : occurrenceMarker progress injective spec d a = some b) :
    parent a.2 = d.val := by
  classical
  by_cases ha : g.HasArc a.1 a.2
  · cases hs : siblingEmission? (d := d.val) progress injective spec a with
    | none => simp [occurrenceMarker, ha, hs] at h
    | some e =>
        obtain ⟨hu, hv, hne, _⟩ :=
          (siblingEmission?_eq_some_iff progress injective spec a e).mp hs
        exact (siblingBlockSystem_crossing_owner progress injective spec
          d.property (⟨a.1, hu⟩ : SiblingVertex g r d.val)
          (⟨a.2, hv⟩ : SiblingVertex g r d.val) ha hne).2.2
  · simp [occurrenceMarker, ha] at h

private theorem filterMap_length_congr {A B C : Type}
    (xs : List A) (f : A → Option B) (h : A → Option C)
    (hm : ∀ a ∈ xs, (f a).isSome = (h a).isSome) :
    (xs.filterMap f).length = (xs.filterMap h).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hhead := hm a (by simp)
      have htail := ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      cases hf : f a <;> cases hh : h a <;>
        simp [hf, hh] at hhead <;>
        simp [List.filterMap, hf, hh, htail]

theorem arcCount_eq_retained (d : ReachableRoot g r) :
    (finiteSiblingQuotient progress injective spec d.property).arcCount =
      (g.originalArcOccurrences.filterMap
        (occurrenceMarker progress injective spec d)).length := by
  classical
  have h :
      (g.originalArcOccurrences.filterMap
        (occurrenceMarker progress injective spec d)).length =
      (finiteSiblingOccurrences (d := d.val) progress injective spec).length := by
    simp only [finiteSiblingOccurrences, List.length_map, siblingEmissions]
    apply filterMap_length_congr
    intro a ha
    have he : g.HasArc a.1 a.2 :=
      (mem_originalArcOccurrences_iff g a.1 a.2).mp ha
    simp only [occurrenceMarker, ite_eq_left he]
    cases siblingEmission? (d := d.val) progress injective spec a <;> rfl
  simpa only [finiteSiblingQuotient, PaperB.arcCount_ofOccurrences] using h.symm

theorem total_arcCount_le_occurrences
    (roots : List (ReachableRoot g r)) (hn : roots.Nodup) :
    (roots.map (fun d =>
      (finiteSiblingQuotient progress injective spec d.property).arcCount)).sum
      ≤ g.originalArcOccurrences.length :=
  Digraph.sum_finiteSiblingQuotient_arcCount_le_occurrences
    progress injective spec roots hn

end Builders

theorem total_key_count {g : Digraph} {r : Fin g.vertexCount}
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (roots : List (ReachableRoot g r)) (hn : roots.Nodup) :
    (roots.map (fun d => (siblingBlockKeys g r d.val parent).length)).sum
      ≤ 2 * g.vertexCount := by
  have hvals : (roots.map (fun d => d.val)).Nodup := by
    induction roots with
    | nil => simp
    | cons d ds ih =>
        simp only [List.map_cons, List.nodup_cons] at hn ⊢
        refine ⟨?_, ih hn.2⟩
        intro hm
        obtain ⟨e, he, hv⟩ := List.mem_map.mp hm
        have heq : e = d := Subtype.ext hv
        exact hn.1 (heq ▸ he)
  simpa only [List.map_map, Function.comp_def] using
    PaperB.SiblingVertexBudget.sum_siblingBlockKeys_length_le_vertex_budget
      g r parent (roots.map (fun d => d.val)) hvals

private theorem exists_rank {g : Digraph} (dag : g.IsAcyclic) :
    ∃ rank : Fin g.vertexCount → Nat,
      (∀ x y, g.HasArc x y → rank x < rank y) ∧
      (∀ ⦃x y⦄, rank x = rank y → x = y) := by
  exact dag.exists_injective_rank

end SiblingCertification

open SiblingCertification

/-- The precise sufficiency statement for the verified `ParentSpec` API.
The labelled trace uses block keys; `decodeSiblingBlockKey` relates those
keys to the indices of the concrete finite builder. -/
abbrev SiblingQuotientCertification {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent) : Prop :=
  (∀ d : Fin g.vertexCount, ∀ hd : g.InitiallyReachable r d,
    let S := siblingBlockSystem progress injective spec hd
    let H := finiteSiblingQuotient progress injective spec hd
    let qr := finiteSiblingRank progress injective spec hd
    H.IsFlat ∧
    Function.Injective qr ∧
    (∀ u v, H.HasQuotientArc u v → qr u < qr v) ∧
    (∀ u v : SiblingVertex g r d, S.arc u v → S.block u ≠ S.block v →
      S.LabelledStep (S.block u) (S.block v) u) ∧
    (∀ (Label : Type) (failed : SiblingBlockKey g r d parent → Prop)
        (u v : SiblingVertex g r d) (xs : List (Label × SiblingVertex g r d)),
      SiblingPhysicalTrace S failed u v xs →
      SiblingLabelledTrace S failed (S.block u) (S.block v) xs) ∧
    (∀ (Label : Type) (failed : SiblingBlockKey g r d parent → Prop)
        (_tag : SiblingVertex g r d → SiblingVertex g r d → Label)
        (u v : SiblingVertex g r d),
      AvoidPath S.arc (S.VertexFailed failed) u v →
      ∃ xs : List (Label × SiblingVertex g r d),
        SiblingPhysicalTrace S failed u v xs ∧
        SiblingLabelledTrace S failed (S.block u) (S.block v) xs) ∧
    (∀ (Label : Type) (failed : SiblingBlockKey g r d parent → Prop)
        (s t : SiblingBlockKey g r d parent)
        (xs : List (Label × SiblingVertex g r d)),
      SiblingLabelledTrace S failed s t xs →
      SiblingPhysicalTrace S failed (S.leader s) (S.leader t) xs) ∧
    (∀ (failed : SiblingBlockKey g r d parent → Prop)
        (s t : Fin H.vertexCount),
      AvoidPath H.HasQuotientArc
          (fun i => failed (decodeSiblingBlockKey g r d parent i)) s t ↔
        AvoidPath S.QuotientEdge failed
          (decodeSiblingBlockKey g r d parent s)
          (decodeSiblingBlockKey g r d parent t))) ∧
  (∀ roots : List (ReachableRoot g r), roots.Nodup →
    (roots.map (fun d =>
      (finiteSiblingQuotient progress injective spec d.property).vertexCount)).sum
      ≤ 2 * g.vertexCount ∧
    (roots.map (fun d =>
      (finiteSiblingQuotient progress injective spec d.property).arcCount)).sum
      ≤ g.arcCount) ∧
  (∀ d : ReachableRoot g r,
    (finiteSiblingQuotient progress injective spec d.property).arcCount =
      (g.originalArcOccurrences.filterMap
        (occurrenceMarker progress injective spec d)).length) ∧
  (∀ (d : ReachableRoot g r) (a : Fin g.vertexCount × Fin g.vertexCount),
    occurrenceMarker progress injective spec d a = some () →
    parent a.2 = d.val)

theorem sibling_quotients_of_parentSpec {g : Digraph} {r : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent) :
    SiblingQuotientCertification progress injective spec := by
  refine ⟨?_, ?_, arcCount_eq_retained progress injective spec, ?_⟩
  · intro d hd
    have hc := crossing_step progress injective spec hd
    refine ⟨finiteSiblingQuotient_isFlat progress injective spec hd,
      finiteSiblingRank_injective progress injective spec hd,
      ?_, hc, ?_, ?_, ?_, ?_⟩
    · intro u v h
      exact finiteSiblingRank_lt_of_hasQuotientArc progress injective spec hd h
    · intro Label failed u v xs h
      exact project_trace hc h
    · intro Label failed tag u v h
      obtain ⟨xs, hx⟩ := mark_physicalPath tag h
      exact ⟨xs, hx, project_trace hc hx⟩
    · intro Label failed s t xs h
      exact lift_trace h
    · intro failed s t
      exact finiteSiblingQuotient_avoidPath_iff progress injective spec hd failed s t
  · intro roots hn
    constructor
    · change (roots.map (fun d =>
          (siblingBlockKeys g r d.val parent).length)).sum ≤ 2 * g.vertexCount
      exact total_key_count parent roots hn
    · exact Digraph.sum_finiteSiblingQuotient_arcCount_le_arcCount
        progress injective spec roots hn
  · intro d a h
    exact occurrence_owner progress injective spec d h

/-- Lemma 2.1. The DAG supplies an injective topological rank and a semantic
parent map. The second conjunct states exactly what the concrete builders
certify for any parent map verified by `ParentSpec`. -/
theorem sibling_quotients {g : Digraph} (dag : g.IsAcyclic)
    (r : Fin g.vertexCount) :
    ∃ rank : Fin g.vertexCount → Nat,
    ∃ progress : ∀ x y, g.HasArc x y → rank x < rank y,
    ∃ injective : ∀ ⦃x y⦄, rank x = rank y → x = y,
      (∃ parent : Fin g.vertexCount → Fin g.vertexCount,
        ∀ d v : Fin g.vertexCount, g.InitiallyReachable r v →
          (Ancestor parent d v ↔ g.Dominates r d v)) ∧
      (∀ (parent : Fin g.vertexCount → Fin g.vertexCount)
        (spec : ParentSpec g r parent),
        SiblingQuotientCertification progress injective spec) := by
  obtain ⟨rank, progress, injective⟩ := exists_rank dag
  refine ⟨rank, progress, injective, ?_, ?_⟩
  · refine ⟨semanticParent (g := g) (r := r) progress injective, ?_⟩
    intro d v hv
    exact semanticParent_ancestor_iff_dominates (g := g) (r := r)
      progress injective (d := d) hv
  · intro parent spec
    exact sibling_quotients_of_parentSpec progress injective spec

open LabelledQuotient in
/-- Lemma 3.1 for the concrete `buildProperLossForest` witness, including its rooted depth structure. -/
theorem proper_loss_forest {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat) :
    ∃ F : ProperLossForest H,
      (∀ B : CutPair H, B ∈ F.realKeys → B.fst < B.snd) ∧
      F.realKeys.Pairwise (· ≠ ·) ∧
      F.realNodeCount ≤ H.vertexCount ∧
      F.nodeKey? F.rootNode = none ∧
      F.parent F.rootNode = F.rootNode ∧
      F.label H.root = F.rootNode ∧
      (∀ y : Fin H.vertexCount, H.HasQuotientArc H.root y → F.label y = F.rootNode) ∧
      (∀ B : CutPair H,
        (∃ u, F.nodeKey? u = some B) ↔
          B.fst < B.snd ∧ ∃ y : Fin H.vertexCount, H.ProperLoss B y) ∧
      (∀ y : Fin H.vertexCount, sweepChain H rank y = F.nodeChain (F.label y)) ∧
      (∀ B : CutPair H, B.fst < B.snd → ∀ y : Fin H.vertexCount,
        H.ProperLoss B y ↔
          ∃ u, F.nodeKey? u = some B ∧ IsForestAncestor F.parent u (F.label y)) ∧
      (∀ uP : Fin (F.realNodeCount + 1), ∀ P B : CutPair H,
        F.nodeKey? uP = some P → F.nodeKey? (F.parent uP) = some B →
          (∀ p : Fin H.vertexCount, P.Mem p → H.Lost B p) ∧
          (∀ y : Fin H.vertexCount, H.ProperLoss P y → H.ProperLoss B y) ∧
          (∀ p : Fin H.vertexCount, IsFreshEndpoint B P p →
            ∀ b : Fin H.vertexCount, B.Mem b → rank b < rank p)) ∧
      ValidDepthTree F.rootNode F.parent F.depth ∧
      (∀ u : Fin (F.realNodeCount + 1), u ≠ F.rootNode →
        IsForestAncestor F.parent F.rootNode u) := by
  have hTree := buildProperLossForest_validDepthTree rankArc flat
  exact ⟨buildProperLossForest H rank,
    buildProperLossForest_realKeys_canonical H rank,
    buildProperLossForest_realKeys_nodup H rank,
    buildProperLossForest_realNodeCount_le H rank,
    buildProperLossForest_nodeKey?_root H rank,
    buildProperLossForest_parent_root H rank,
    buildProperLossForest_label_root H rank,
    fun _ hArc => buildProperLossForest_label_of_root_arc H rank hArc,
    buildProperLossForest_exists_node_iff rankArc flat,
    buildProperLossForest_sweepChain_eq_nodeChain rankArc distinctRanks flat,
    fun _ hOrd y =>
      buildProperLossForest_properLoss_iff_ancestor rankArc distinctRanks flat hOrd y,
    (fun _ _ _ huP huB =>
      ⟨buildProperLossForest_edge_endpoints_lost rankArc flat huP huB,
        buildProperLossForest_edge_properLoss_subset rankArc distinctRanks flat huP huB,
        buildProperLossForest_edge_fresh_follows_parent rankArc flat huP huB⟩),
    hTree,
    fun u _ => ValidDepthTree.isForestAncestor_root hTree u⟩

/-- Theorem 4.1 on a real forest edge of the concrete finite sibling
quotient, with the endpoint coordinate and original physical tail left
universally quantified. -/
theorem exit_set_transfer {g : Digraph} {r d : Fin g.vertexCount}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ u v, g.HasArc u v → rank u < rank v)
    (injective : ∀ ⦃u v⦄, rank u = rank v → u = v)
    (spec : ParentSpec g r parent)
    (hd : g.InitiallyReachable r d) {x : Fin g.vertexCount} :
    let H : LabelledQuotient := finiteSiblingQuotient progress injective spec hd
    let qRank : Fin H.vertexCount → Nat := finiteSiblingRank progress injective spec hd
    let F : ProperLossForest H := buildProperLossForest H qRank
    ∀ {uP : Fin (F.realNodeCount + 1)} {P B : CutPair H},
      F.nodeKey? uP = some P → F.nodeKey? (F.parent uP) = some B →
      ∀ {s y : Fin H.vertexCount},
        B.Mem s → H.ProperLoss P y →
        (H.ExitTailMem B s y x ↔
          (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
          (P.Mem s ∧ H.ExitTailMem P s y x)) := by
  intro H qRank F uP P B huP huB s y hs proper
  apply Digraph.finiteSiblingQuotient_edge_exitTailMem_iff
    (progress := progress) (injective := injective) (spec := spec) (hd := hd) (x := x) <;>
    assumption

end PaperB
