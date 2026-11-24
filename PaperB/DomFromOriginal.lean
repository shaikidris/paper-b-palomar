module

public import PaperB.FullDomScan
public import PaperB.ArcBuckets
public import PaperB.Kahn
public import PaperB.JumpRegionInit
public import PaperB.SiblingEmissions

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/- Append after FullDomScan, with Kahn, the EX51 buckets, and the
   concrete jump-region initializer in scope. -/

namespace PaperB.EX15

open PaperB.Jumps
open WholeScan

abbrev OriginalOccurrence (g : Digraph) :=
  Fin g.vertexCount × Fin g.vertexCount

/-- Evaluate the bucket construction once, before returning the row accessor. -/
def originalIncoming (g : Digraph) :
    Fin g.vertexCount → List (OriginalOccurrence g) :=
  let buckets :=
    (EX51.incoming (fun a : OriginalOccurrence g => a.snd)
      g.originalArcOccurrences).1
  buckets.row

/-- This is a list equality, so it also preserves repeated equal occurrences. -/
theorem originalIncoming_row (g : Digraph) (v : Fin g.vertexCount) :
    originalIncoming g v =
      g.originalArcOccurrences.filter (fun a => decide (a.snd = v)) := by
  exact EX51.incoming_row (fun a : OriginalOccurrence g => a.snd)
    g.originalArcOccurrences v

theorem originalIncoming_cover (g : Digraph) (v u : Fin g.vertexCount) :
    g.HasArc u v ↔ ∃ a ∈ originalIncoming g v, a.fst = u := by
  constructor
  · intro huv
    refine ⟨(u, v), ?_, rfl⟩
    rw [originalIncoming_row]
    exact List.mem_filter.mpr
      ⟨(g.mem_originalArcOccurrences_iff u v).mpr huv, by simp⟩
  · rintro ⟨⟨s, t⟩, ha, hs⟩
    rw [originalIncoming_row] at ha
    have ht : t = v := of_decide_eq_true (List.mem_filter.mp ha).2
    change s = u at hs
    exact (g.mem_originalArcOccurrences_iff u v).mp
      (by simpa only [hs, ht] using (List.mem_filter.mp ha).1)

private def bucketMass {α β : Type} [DecidableEq β]
    (key : α → β) (xs : List α) (vs : List β) : Nat :=
  (vs.map (fun v => (xs.filter (fun a => decide (key a = v))).length)).sum

private theorem filter_bucket_other {α β : Type} [DecidableEq β]
    (key : α → β) (xs : List α) {v w : β} (hw : w ≠ v) :
    (xs.filter (fun a => !(decide (key a = v)))).filter
        (fun a => decide (key a = w)) =
      xs.filter (fun a => decide (key a = w)) := by
  rw [List.filter_filter]
  apply congrArg (fun p : α → Bool => xs.filter p)
  funext a
  by_cases he : key a = w
  · simp [he, hw]
  · simp [he]

private theorem bucket_partition_length {α β : Type} [DecidableEq β]
    (key : α → β) (xs : List α) (v : β) :
    (xs.filter (fun a => decide (key a = v))).length +
        (xs.filter (fun a => !(decide (key a = v)))).length =
      xs.length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : key a = v <;> simp [h] <;> omega

private theorem map_eq_of_eq_on {α β : Type} {f h : α → β}
    (xs : List α) (he : ∀ x ∈ xs, f x = h x) :
    xs.map f = xs.map h := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := he x (by simp)
      have ht := ih (fun y hy => he y (by simp [hy]))
      simp only [List.map_cons, hx, ht]

private theorem bucketMass_le {α β : Type} [DecidableEq β]
    (key : α → β) (xs : List α) (vs : List β) (hv : vs.Nodup) :
    bucketMass key xs vs ≤ xs.length := by
  induction vs generalizing xs with
  | nil => simp [bucketMass]
  | cons v vs ih =>
      have hn := List.nodup_cons.mp hv
      let rest := xs.filter (fun a => !(decide (key a = v)))
      have hrest : bucketMass key rest vs ≤ rest.length := by
        apply ih
        exact hn.2
      have hmap :
          vs.map (fun w => (rest.filter (fun a => decide (key a = w))).length) =
            vs.map (fun w => (xs.filter (fun a => decide (key a = w))).length) := by
        apply map_eq_of_eq_on
        intro w hw
        exact congrArg List.length
          (filter_bucket_other key xs (fun e => hn.1 (e ▸ hw)))
      have htail : bucketMass key rest vs = bucketMass key xs vs :=
        congrArg List.sum hmap
      have hsplit :
          (xs.filter (fun a => decide (key a = v))).length + rest.length =
            xs.length :=
        bucket_partition_length key xs v
      simp only [bucketMass, List.map_cons, List.sum_cons] at ⊢
      unfold bucketMass at hrest htail
      omega

private theorem length_le_identityMass {α : Type} [DecidableEq α]
    (xs vs : List α) (hall : ∀ v ∈ vs, v ∈ xs) :
    vs.length ≤ bucketMass id xs vs := by
  induction vs with
  | nil => simp [bucketMass]
  | cons v vs ih =>
      have hm : v ∈ xs.filter (fun a => decide (id a = v)) :=
        List.mem_filter.mpr ⟨hall v (by simp), by simp⟩
      have hp : 0 < (xs.filter (fun a => decide (id a = v))).length := by
        cases h : xs.filter (fun a => decide (id a = v)) with
        | nil =>
            have hempty : v ∈ ([] : List α) := by
              simpa only [h] using hm
            simp at hempty
        | cons a as => simp
      have ht : vs.length ≤ bucketMass id xs vs :=
        ih (fun w hw => hall w (by simp [hw]))
      simp only [bucketMass, List.length_cons, List.map_cons, List.sum_cons] at ⊢
      unfold bucketMass at ht
      omega

private theorem fin_order_length_le {n : Nat} (vs : List (Fin n))
    (hv : vs.Nodup) : vs.length ≤ n := by
  let all := List.ofFn (fun v : Fin n => v)
  have hall (v : Fin n) : v ∈ all := by
    change v ∈ List.ofFn (fun w : Fin n => w)
    exact List.mem_ofFn.mpr ⟨v, rfl⟩
  have h := Nat.le_trans (length_le_identityMass all vs (fun v _ => hall v))
    (bucketMass_le id all vs hv)
  simpa [all] using h

private theorem graph_insertions_le {g : Digraph} (r : Fin g.vertexCount)
    (marked : Fin g.vertexCount → Bool) (order : List (Fin g.vertexCount)) :
    insertions r marked order ≤ order.length := by
  induction order with
  | nil => simp [insertions]
  | cons v vs ih =>
      simp only [WholeScan.insertions, List.length_cons]
      rw [Nat.add_comm vs.length 1]
      by_cases h : WholeScan.Active r marked v
      · have hv : (if WholeScan.Active r marked v then (1 : Nat) else 0) = 1 :=
          if_pos h
        rw [hv]
        exact Nat.add_le_add (Nat.le_refl 1) ih
      · have hv : (if WholeScan.Active r marked v then (1 : Nat) else 0) = 0 :=
          if_neg h
        rw [hv]
        exact Nat.add_le_add (Nat.zero_le 1) ih

private theorem rawRows_le_bucketMass {g : Digraph} (r : Fin g.vertexCount)
    (marked : Fin g.vertexCount → Bool) (order : List (Fin g.vertexCount)) :
    rawRows r marked (originalIncoming g) order ≤
      bucketMass (fun a : OriginalOccurrence g => a.snd)
        g.originalArcOccurrences order := by
  induction order with
  | nil => simp [rawRows, bucketMass]
  | cons v vs ih =>
      simp only [WholeScan.rawRows]
      change _ ≤ ((v :: vs).map (fun w =>
        (g.originalArcOccurrences.filter (fun a => decide (a.snd = w))).length)).sum
      rw [List.map_cons, List.sum_cons]
      by_cases h : WholeScan.Active r marked v
      · have hv : (if WholeScan.Active r marked v then
            (PaperB.EX15.originalIncoming g v).length else 0) =
            (PaperB.EX15.originalIncoming g v).length := if_pos h
        rw [hv, PaperB.EX15.originalIncoming_row]
        exact Nat.add_le_add (Nat.le_refl _) ih
      · have hv : (if WholeScan.Active r marked v then
            (PaperB.EX15.originalIncoming g v).length else 0) = 0 := if_neg h
        rw [hv]
        exact Nat.add_le_add (Nat.zero_le _) ih

theorem original_rawRows_le {g : Digraph} (r : Fin g.vertexCount)
    (marked : Fin g.vertexCount → Bool) (order : List (Fin g.vertexCount))
    (hn : order.Nodup) :
    rawRows r marked (originalIncoming g) order ≤
      g.originalArcOccurrences.length :=
  Nat.le_trans (rawRows_le_bucketMass r marked order)
    (bucketMass_le (fun a : OriginalOccurrence g => a.snd)
      g.originalArcOccurrences order hn)

abbrev GraphAcyclic (g : Digraph) : Prop := by
  first
  | exact Kahn.IsAcyclic g
  | exact Digraph.IsAcyclic g
  | exact IsAcyclic g

abbrev graphRegion (n : Nat) : JumpWordRegion := by
  first
  | exact ConcreteInit.region n
  | exact JumpRegionInit.region n

private abbrev graphInitWords (n : Nat) : Array Nat := by
  first
  | exact (ConcreteInit.initImage n).1
  | exact (JumpRegionInit.initImage n).1

def runGraph (g : Digraph) (r : Fin g.vertexCount) (hacyc : GraphAcyclic g) :=
  let k := Kahn.run g
  let order := k.order.toList
  let topo : g.IsTopologicalList order := Kahn.run_isTopologicalList g hacyc
  let incoming := originalIncoming g
  WholeScan.run (graphRegion g.vertexCount) r order topo
    (fun a : OriginalOccurrence g => a.fst) incoming
    (graphInitWords g.vertexCount)

/--
`Parents` is about the original graph's dominance relation. The two occurrence
bounds are separate: a row inspection and an LCA query can charge the same
occurrence. In fact, queries plus insertions are bounded by the raw row charge.
-/
theorem runGraph_spec (g : Digraph) (r : Fin g.vertexCount)
    (hacyc : GraphAcyclic g) {L : Nat} (hL : g.vertexCount + 2 ≤ 2 ^ L)
    (rootReach : g.InitiallyReachable r r)
    (rootDom : ∀ d, g.Dominates r d r ↔ d = r) :
    let order := (Kahn.run g).order.toList
    let topo := Kahn.run_isTopologicalList g hacyc
    let out := runGraph g r hacyc
    ∃ F,
      Partial (packedJumpOps (OriginalOccurrence g) (graphRegion g.vertexCount))
        r (g.InitiallyReachable r) F out.state ∧
      Parents r (g.InitiallyReachable r) F out.state.slots ∧
      out.rowOccurrences =
        rawRows r (topologicalMark r order topo) (originalIncoming g) order ∧
      out.rowOccurrences ≤ g.originalArcOccurrences.length ∧
      out.foldInputs ≤ out.rowOccurrences ∧
      out.lcaQueries + insertions r (topologicalMark r order topo) order =
        out.foldInputs ∧
      out.lcaQueries + insertions r (topologicalMark r order topo) order ≤
        g.originalArcOccurrences.length ∧
      out.lcaQueries ≤ g.originalArcOccurrences.length ∧
      out.appendAccesses = 14 * insertions r (topologicalMark r order topo) order ∧
      out.appendAccesses ≤ 14 * g.vertexCount := by
  intro order topo out
  have hnd : order.Nodup := topo.1
  have hn : insertions r (topologicalMark r order topo) order ≤ g.vertexCount :=
    Nat.le_trans (graph_insertions_le r (topologicalMark r order topo) order)
      (fin_order_length_le order hnd)
  have hcap : insertions r (topologicalMark r order topo) order ≤
      (graphRegion g.vertexCount).maxNodes := by
    exact hn
  have hLayout : JumpWordLayout (graphRegion g.vertexCount) JumpForest.init
      (graphInitWords g.vertexCount) := by
    first
    | exact ConcreteInit.init_layout _
    | exact JumpRegionInit.init_layout _
  have hSize : JumpForest.init.size = 1 := by
    first
    | rfl
    | decide
  have hAncestor : IsAncestor JumpForest.init 0 0 := by
    first
    | exact ⟨0, rfl⟩
    | apply IsAncestor.refl <;> decide
    | exact?
    | decide
  have hSelf : ∀ x, g.InitiallyReachable r x → g.Dominates r x x := by
    intro x _
    first
    | exact dominates_refl
    | exact Digraph.dominates_refl
    | exact?
  have hScan : ∃ F,
      Partial (packedJumpOps (OriginalOccurrence g) (graphRegion g.vertexCount))
        r (g.InitiallyReachable r) F out.state ∧
      Parents r (g.InitiallyReachable r) F out.state.slots ∧
      out.rowOccurrences =
        rawRows r (topologicalMark r order topo) (originalIncoming g) order ∧
      out.foldInputs ≤ out.rowOccurrences ∧
      out.lcaQueries + insertions r (topologicalMark r order topo) order =
        out.foldInputs ∧
      out.appendAccesses = 14 * insertions r (topologicalMark r order topo) order := by
    dsimp only [out, runGraph]
    apply WholeScan.run_spec (graphRegion g.vertexCount) r order topo
      (fun a : OriginalOccurrence g => a.fst) (originalIncoming g)
    all_goals
      first
      | exact originalIncoming_cover g
      | exact hSelf
      | exact hLayout
      | exact hSize
      | exact hAncestor
      | exact rootReach
      | exact rootDom
      | exact hL
      | exact hn
      | exact hcap
      | exact L
      | intro u v
        exact originalIncoming_cover g v u
      | intro d
        exact (rootDom d).mp
      | intro d
        exact (rootDom d).mpr
      | intro d
        exact (rootDom d).symm
      | intro d hd hdom
        exact hd ((rootDom d).mp hdom)
      | exact?
  obtain ⟨F, hPartial, hParents, hRaw, hFold, hQueries, hAppend⟩ := hScan
  have hRows : out.rowOccurrences ≤ g.originalArcOccurrences.length := by
    rw [hRaw]
    exact original_rawRows_le r (topologicalMark r order topo) order hnd
  have hQueryTotal :
      out.lcaQueries + insertions r (topologicalMark r order topo) order ≤
        g.originalArcOccurrences.length := by
    rw [hQueries]
    exact Nat.le_trans hFold hRows
  refine ⟨F, hPartial, hParents, hRaw, hRows, hFold, hQueries, hQueryTotal,
    ?_, hAppend, ?_⟩
  · exact Nat.le_trans (Nat.le_add_right _ _) hQueryTotal
  · rw [hAppend]
    exact Nat.mul_le_mul_left 14 hn

/--
Separate arithmetic aggregation. `pre` is the preprocessing charge, and
`hTrace` is the sum of the word-trace bounds: linear row overhead, at most
`c * L^2` per LCA, and the already counted append accesses.
-/
theorem aggregateGraphWordBudget
    {n m L pre rows queries appends work a c : Nat}
    (hL : 1 ≤ L ^ 2)
    (hPre : pre ≤ a * (n + m))
    (hRows : rows ≤ m)
    (hQueries : queries ≤ m)
    (hAppends : appends ≤ 14 * n)
    (hTrace : work ≤ pre + rows + queries * (c * L ^ 2) + appends) :
    work ≤ (a + 15 + c) * ((n + m) * L ^ 2) := by
  have hLinear : pre + rows + appends ≤ (a + 15) * (n + m) := by
    rw [Nat.add_mul, Nat.add_assoc]
    refine Nat.add_le_add hPre ?_
    change rows + appends ≤ (1 + 14) * (n + m)
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add (Nat.le_trans hRows (Nat.le_add_left _ _))
      (Nat.le_trans hAppends (Nat.mul_le_mul_left 14 (Nat.le_add_right _ _)))
  have hScaled :
      (a + 15) * (n + m) ≤ ((a + 15) * (n + m)) * L ^ 2 := by
    simpa only [Nat.mul_one] using
      Nat.mul_le_mul_left ((a + 15) * (n + m)) hL
  have hQueryScaled : queries * (c * L ^ 2) ≤ (c * (n + m)) * L ^ 2 := by
    calc
      queries * (c * L ^ 2) ≤ (n + m) * (c * L ^ 2) :=
        Nat.mul_le_mul_right (c * L ^ 2) (Nat.le_trans hQueries (Nat.le_add_left _ _))
      _ = (c * (n + m)) * L ^ 2 := by ac_rfl
  calc
    work ≤ ((a + 15) * (n + m)) * L ^ 2 + (c * (n + m)) * L ^ 2 := by
      refine Nat.le_trans hTrace ?_
      calc
        pre + rows + queries * (c * L ^ 2) + appends =
            (pre + rows + appends) + queries * (c * L ^ 2) := by ac_rfl
        _ ≤ ((a + 15) * (n + m)) * L ^ 2 + (c * (n + m)) * L ^ 2 :=
          Nat.add_le_add (Nat.le_trans hLinear hScaled) hQueryScaled
    _ = (a + 15 + c) * ((n + m) * L ^ 2) := by
      simp only [Nat.add_mul, Nat.mul_assoc]

end PaperB.EX15
