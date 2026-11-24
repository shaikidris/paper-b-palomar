module

public import PaperB.ArcBuckets
public import PaperB.ArcOwnerTotal

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Place this after `siblingEmission_exists_iff_headParent`, at file scope,
with the module exporting `EX51.groupMap` in scope.

`pack` is the finite block encoding used by the existing quotient. The
two row theorems give equality with and without occurrence metadata.
-/

namespace PaperB.Digraph.GlobalSibling

abbrev Vertex (g : Digraph) := Fin g.vertexCount
abbrev Arc (g : Digraph) := Vertex g × Vertex g

abbrev Packing (g : Digraph) (r : Vertex g)
    (parent : Vertex g → Vertex g) (K : Nat) :=
  (d : Vertex g) → SiblingBlockKey g r d parent → Fin K

structure PackedEmission (g : Digraph) (K : Nat) where
  source : Fin K
  destination : Fin K
  tail : Vertex g

structure Entry (g : Digraph) (K : Nat) where
  emission : PackedEmission g K
  occurrence : Arc g

/-- `headBlock v` is the direct-child code at the stored parent of `v`.
The second result of `childBlock` is its charged work. -/
structure Getters (g : Digraph) (K : Nat) where
  reachable : Vertex g → Bool
  parentOf : Vertex g → Vertex g
  rootBlock : Vertex g → Fin K
  headBlock : Vertex g → Fin K
  childBlock : Vertex g → Vertex g → Fin K × Nat

variable {g : Digraph} {K : Nat}

/-- Enumerate only the outgoing lists of retained tails. In particular,
parallel occurrences are not deduplicated or reordered. -/
def retained (T : Getters g K) : List (Arc g) :=
  ((List.ofFn (fun u : Vertex g => u)).filter T.reachable).flatMap
    (fun u => (g.outArcs u).map (fun v => (u, v)))

def tailBlock (T : Getters g K) (d u : Vertex g) : Fin K × Nat :=
  if u = d then (T.rootBlock d, 0) else T.childBlock d u

def locate (T : Getters g K) (a : Arc g) : Entry g K × Nat :=
  let s := tailBlock T (T.parentOf a.2) a.1
  (⟨⟨s.1, T.headBlock a.2, a.1⟩, a⟩, s.2)

/-- One scatter over the retained occurrences. Finishing the buckets does
not revisit the original adjacency lists. -/
def emitAll (T : Getters g K) :=
  EX51.groupMap
    (fun a : Arc g => T.parentOf a.2)
    (fun a => (locate T a).1)
    (retained T)

private theorem filterOutgoing (T : Getters g K) (u : Vertex g)
    (vs : List (Vertex g)) :
    ((vs.map (fun v => (u, v))).filter
        (fun a => T.reachable a.1)) =
      if T.reachable u then vs.map (fun v => (u, v)) else [] := by
  induction vs with
  | nil =>
      cases h : T.reachable u <;> simp [h]
  | cons v vs ih =>
      cases h : T.reachable u <;> simp [List.filter, h, ih]

private theorem retainedAux (T : Getters g K) (us : List (Vertex g)) :
    (us.filter T.reachable).flatMap
        (fun u => (g.outArcs u).map (fun v => (u, v))) =
      (us.flatMap (fun u => (g.outArcs u).map (fun v => (u, v)))).filter
        (fun a => T.reachable a.1) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
      cases h : T.reachable u <;>
        simp [List.filter, List.flatMap_cons, List.filter_append,
          filterOutgoing, h, ih]

theorem retained_eq_filter (T : Getters g K) :
    retained T =
      g.originalArcOccurrences.filter (fun a => T.reachable a.1) :=
  retainedAux T (List.ofFn (fun u : Vertex g => u))

theorem emitAll_bucket_work (T : Getters g K) :
    (emitAll T).2 =
      ⟨g.vertexCount, (retained T).length, (retained T).length,
        (retained T).length, g.vertexCount⟩ := by
  unfold emitAll
  exact EX51.groupMap_work _ _ _

/- These cost summaries are used only in proofs; emitAll does not run
   either summation. A self-tail takes the branch with no child call. -/
def childCalls (T : Getters g K) (a : Arc g) : Nat :=
  if a.1 = T.parentOf a.2 then 0 else 1

theorem charge_bound (T : Getters g K) (C : Nat)
    (bound : ∀ d u, (T.childBlock d u).2 ≤ C) (xs : List (Arc g)) :
    (xs.map (childCalls T)).sum ≤ xs.length ∧
      (xs.map (fun a => 1 + (locate T a).2)).sum ≤
        xs.length * (1 + C) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have hc : childCalls T a ≤ 1 := by
        by_cases h : a.1 = T.parentOf a.2 <;> simp [childCalls, h]
      have hw : (locate T a).2 ≤ C := by
        by_cases h : a.1 = T.parentOf a.2
        · simp [locate, tailBlock, h]
        · simpa only [locate, tailBlock, if_neg h] using
            bound (T.parentOf a.2) a.1
      obtain ⟨ihc, ihw⟩ := ih
      constructor
      · change childCalls T a + (xs.map (childCalls T)).sum ≤
          xs.length + 1
        omega
      · change (1 + (locate T a).2) +
            (xs.map (fun b => 1 + (locate T b).2)).sum ≤
          (xs.length + 1) * (1 + C)
        rw [Nat.add_mul, Nat.one_mul]
        omega

section Correctness

variable {r d : Vertex g} {rank : Vertex g → Nat}
variable {parent : Vertex g → Vertex g}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- Only static, per-vertex getter contracts. No field specifies an arc
emission or the contents of a bucket. -/
structure Checked (T : Getters g K) (pack : Packing g r parent K)
    (C : Nat) : Prop where
  reachable_ok : ∀ u, T.reachable u = true ↔ g.InitiallyReachable r u
  parent_ok : ∀ v, T.parentOf v = parent v
  root_ok : ∀ d
      (hd : g.InitiallyReachable r d ∧ g.Dominates r d d),
    T.rootBlock d =
      pack d (siblingBlockOf progress injective spec
        (⟨d, hd⟩ : SiblingVertex g r d))
  head_ok : ∀ v
      (hv : g.InitiallyReachable r v ∧ g.Dominates r (parent v) v),
    T.headBlock v =
      pack (parent v) (siblingBlockOf progress injective spec
        (⟨v, hv⟩ : SiblingVertex g r (parent v)))
  child_ok : ∀ d u
      (hu : g.InitiallyReachable r u ∧ g.Dominates r d u),
    u ≠ d →
      (T.childBlock d u).1 =
        pack d (siblingBlockOf progress injective spec
          (⟨u, hu⟩ : SiblingVertex g r d))
  child_bound : ∀ d u, (T.childBlock d u).2 ≤ C

def packEmission (pack : Packing g r parent K)
    (e : SiblingEmission g r d parent) : PackedEmission g K :=
  ⟨pack d e.source, pack d e.destination, e.tail⟩

variable (T : Getters g K) (pack : Packing g r parent K) {C : Nat}

theorem locate_correct (H : Checked progress injective spec T pack C)
    {a : Arc g} (ha : g.HasArc a.1 a.2)
    {e : SiblingEmission g r d parent}
    (he : siblingEmission? progress injective spec a = some e) :
    (locate T a).1 = ⟨packEmission pack e, a⟩ := by
  rcases a with ⟨u, v⟩
  have hp : parent v = d :=
    ((siblingEmission_exists_iff_headParent (d := d)
      progress injective spec (a := (u, v)) ha).mp ⟨e, he⟩).2
  subst d
  obtain ⟨hu, hv, _, hrecord⟩ :=
    (siblingEmission?_eq_some_iff progress injective spec (u, v) e).mp he
  have hs :
      (tailBlock T (T.parentOf v) u).1 =
        pack (parent v) (siblingBlockOf progress injective spec
          (⟨u, hu⟩ : SiblingVertex g r (parent v))) := by
    rw [H.parent_ok v]
    unfold tailBlock
    by_cases h : u = parent v
    · rw [if_pos h]
      subst u
      exact H.root_ok (parent v) hu
    · rw [if_neg h]
      exact H.child_ok (parent v) u hu h
  have ht := H.head_ok v hv
  rw [← hrecord]
  change
    (⟨⟨(tailBlock T (T.parentOf v) u).1, T.headBlock v, u⟩, (u, v)⟩ :
      Entry g K) =
      ⟨⟨pack (parent v) (siblingBlockOf progress injective spec
            (⟨u, hu⟩ : SiblingVertex g r (parent v))),
          pack (parent v) (siblingBlockOf progress injective spec
            (⟨v, hv⟩ : SiblingVertex g r (parent v))), u⟩, (u, v)⟩
  rw [hs, ht]

private theorem entry_step (H : Checked progress injective spec T pack C)
    (d : Vertex g) (a : Arc g) (ha : g.HasArc a.1 a.2) :
    (siblingEmission? (d := d) progress injective spec a).map
        (fun e => (⟨packEmission pack e, a⟩ : Entry g K)) =
      if T.reachable a.1 && decide (T.parentOf a.2 = d) then
        some (locate T a).1
      else none := by
  classical
  have owner := siblingEmission_exists_iff_headParent (d := d)
    progress injective spec (a := a) ha
  cases he : siblingEmission? (d := d) progress injective spec a with
  | none =>
      have hn : ¬ (g.InitiallyReachable r a.1 ∧ parent a.2 = d) := by
        intro hp
        obtain ⟨e, hem⟩ := owner.mpr hp
        rw [he] at hem
        cases hem
      by_cases hu : g.InitiallyReachable r a.1
      · have hk : T.parentOf a.2 ≠ d := by
          intro h
          exact hn ⟨hu, (H.parent_ok a.2).symm.trans h⟩
        simp [hk]
      · have hb : T.reachable a.1 = false := by
          cases h : T.reachable a.1 with
          | false => rfl
          | true => exact False.elim (hu ((H.reachable_ok a.1).mp h))
        simp [hb]
  | some e =>
      obtain ⟨hu, hp⟩ := owner.mp ⟨e, he⟩
      have hb := (H.reachable_ok a.1).mpr hu
      have hk := (H.parent_ok a.2).trans hp
      have hl := locate_correct progress injective spec T pack H ha he
      simp [hb, hk, hl]

private theorem scan_eq (H : Checked progress injective spec T pack C)
    (d : Vertex g) (xs : List (Arc g))
    (hxs : ∀ a ∈ xs, g.HasArc a.1 a.2) :
    ((xs.filter (fun a => T.reachable a.1)).filter
        (fun a => decide (T.parentOf a.2 = d))).map
        (fun a => (locate T a).1) =
      xs.filterMap (fun a =>
        (siblingEmission? (d := d) progress injective spec a).map
          (fun e => (⟨packEmission pack e, a⟩ : Entry g K))) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have htail := ih (fun b hb => hxs b (List.mem_cons.mpr (Or.inr hb)))
      have hstep := entry_step progress injective spec T pack H d a
        (hxs a (by simp))
      by_cases hb : T.reachable a.1 = true
      · by_cases hk : T.parentOf a.2 = d
        · simp [List.filter, hb, hk, hstep] <;> simpa using htail
        · simp [List.filter, hb, hk, hstep] <;> simpa using htail
      · have hf : T.reachable a.1 = false := by
          cases h : T.reachable a.1 with
          | false => rfl
          | true => exact False.elim (hb h)
        simp [List.filter, hf, hstep] <;> simpa using htail

/-- Exact list equality, including order, multiplicity, and the original
arc pair at every emitted position. The filterMap is proof-side only. -/
theorem emitAll_row (H : Checked progress injective spec T pack C)
    (d : Vertex g) :
    (emitAll T).1.row d =
      g.originalArcOccurrences.filterMap (fun a =>
        (siblingEmission? (d := d) progress injective spec a).map
          (fun e => (⟨packEmission pack e, a⟩ : Entry g K))) := by
  unfold emitAll
  rw [EX51.groupMap_row, retained_eq_filter]
  apply scan_eq progress injective spec T pack H d
  intro a ha
  rcases a with ⟨u, v⟩
  exact (mem_originalArcOccurrences_iff g u v).mp ha

private theorem forgetOccurrences (d : Vertex g) (xs : List (Arc g)) :
    (xs.filterMap (fun a =>
      (siblingEmission? (d := d) progress injective spec a).map
        (fun e => (⟨packEmission pack e, a⟩ : Entry g K)))).map
        (fun x => x.emission) =
      (xs.filterMap (siblingEmission? (d := d) progress injective spec)).map
        (packEmission pack) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases he : siblingEmission? (d := d) progress injective spec a <;>
        simp [List.filterMap_cons, he, ih]

/-- Dropping only the occurrence metadata gives the exact finite image
of the existing sibling-emission list at this root. -/
theorem emitAll_row_emissions
    (H : Checked progress injective spec T pack C) (d : Vertex g) :
    ((emitAll T).1.row d).map (fun x => x.emission) =
      (siblingEmissions (d := d) progress injective spec).map
        (packEmission pack) := by
  rw [emitAll_row progress injective spec T pack H d]
  simpa only [siblingEmissions, siblingEmissionsFrom] using
    forgetOccurrences progress injective spec pack d g.originalArcOccurrences

/-- The global scatter charges one occurrence per retained arc
(`emitAll_bucket_work`). Its emitter makes at most one packed child
call per occurrence, and the combined occurrence and child work is
bounded by `length * (1 + C)`. Bucket finishing is accounted for
separately by `emitAll_bucket_work`. -/
theorem emitAll_lookup_work (H : Checked progress injective spec T pack C) :
    ((retained T).map (childCalls T)).sum ≤ (retained T).length ∧
      ((retained T).map (fun a => 1 + (locate T a).2)).sum ≤
        (retained T).length * (1 + C) :=
  charge_bound T C H.child_bound (retained T)

end Correctness
end PaperB.Digraph.GlobalSibling
