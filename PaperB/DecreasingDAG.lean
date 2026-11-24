module

public import PaperB.ReachScan

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Exact decreasing-index representation for a supplied topological array.
Position zero receives the largest index. Rows retain the order and
multiplicity of the original outgoing occurrences.

Residual: this module does not build the inverse-position table for
`Kahn.run g`. For that instantiation, supply its actual order array to
`ValidOrder.ofTopologicalList`, with the proved topological-list property
and the lookup laws below. Building the inverse table separately requires
initializing n slots and visiting and writing one slot per order entry.
No position search is used in this adapter.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Decreasing

structure FailureDAG where
  vertexCount : Nat
  children : (parent : Fin vertexCount) → List (Fin parent.val)

namespace FailureDAG

def childIndex (g : FailureDAG) (parent : Fin g.vertexCount)
    (child : Fin parent.val) : Fin g.vertexCount :=
  ⟨child.val, Nat.lt_trans child.isLt parent.isLt⟩

inductive ReachAvoid (g : FailureDAG) (failed : Fin g.vertexCount → Prop) :
    Fin g.vertexCount → Fin g.vertexCount → Prop where
  | here (v : Fin g.vertexCount) (alive : ¬ failed v) :
      ReachAvoid g failed v v
  | step (p : Fin g.vertexCount) (c : Fin p.val) (t : Fin g.vertexCount)
      (alive : ¬ failed p) (edge : c ∈ g.children p)
      (tail : ReachAvoid g failed (g.childIndex p c) t) :
      ReachAvoid g failed p t

end FailureDAG

/-- `atPos` is tied pointwise to the given array, not to a separately chosen
permutation. The cost bound assumes constant-time `position` and `atPos`. -/
structure OrderMaps (g : Digraph) (order : Array (Fin g.vertexCount)) where
  size_eq : order.size = g.vertexCount
  position : Fin g.vertexCount → Fin g.vertexCount
  atPos : Fin g.vertexCount → Fin g.vertexCount
  atPos_eq (i : Fin g.vertexCount) :
    atPos i = order[i.val]'(by rw [size_eq]; exact i.isLt)
  at_position (v : Fin g.vertexCount) : atPos (position v) = v
  position_at (i : Fin g.vertexCount) : position (atPos i) = i

structure ValidOrder (g : Digraph) (order : Array (Fin g.vertexCount))
    extends OrderMaps g order where
  forward (u v : Fin g.vertexCount) :
    g.HasArc u v → (position u).val < (position v).val

private theorem member_index {α : Type} {xs : List α} {v : α}
    (h : v ∈ xs) : ∃ j, ∃ hj : j < xs.length, xs[j] = v := by
  induction h with
  | head xs => exact ⟨0, Nat.zero_lt_succ xs.length, rfl⟩
  | tail a _ ih =>
      obtain ⟨j, hj, he⟩ := ih
      exact ⟨j + 1, Nat.succ_lt_succ hj, he⟩

private theorem split_index {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) :
    ∃ pre post, xs = pre ++ (xs[i] :: post) ∧
      ∀ v, v ∈ post → ∃ j, ∃ hj : j < xs.length, i < j ∧ xs[j] = v := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero =>
          refine ⟨[], xs, rfl, ?_⟩
          intro v hv
          obtain ⟨j, hj, he⟩ := member_index hv
          exact ⟨j + 1, Nat.succ_lt_succ hj, Nat.zero_lt_succ j, he⟩
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          obtain ⟨pre, post, he, later⟩ := ih i hi'
          refine ⟨a :: pre, post, congrArg (List.cons a) he, ?_⟩
          intro v hv
          obtain ⟨j, hj, hij, he'⟩ := later v hv
          exact ⟨j + 1, Nat.succ_lt_succ hj, Nat.succ_lt_succ hij, he'⟩

private theorem atPos_toList {g : Digraph} {order : Array (Fin g.vertexCount)}
    (m : OrderMaps g order) (i : Fin g.vertexCount) :
    m.atPos i = order.toList[i.val]'(by simpa [m.size_eq] using i.isLt) := by
  simpa using m.atPos_eq i

namespace ValidOrder

variable {g : Digraph} {order : Array (Fin g.vertexCount)}

/-- The list specification supplies the forward-edge law. This proof does
not perform list searches in the executable construction. -/
def ofTopologicalList (m : OrderMaps g order)
    (h : g.IsTopologicalList order.toList) : ValidOrder g order where
  toOrderMaps := m
  forward := by
    intro u v arc
    have hi : (m.position u).val < order.toList.length := by
      simpa [m.size_eq] using (m.position u).isLt
    obtain ⟨pre, post, hs, later⟩ :=
      split_index order.toList (m.position u).val hi
    have hu : order.toList[(m.position u).val] = u :=
      (atPos_toList m (m.position u)).symm.trans (m.at_position u)
    rw [hu] at hs
    have hv : v ∈ post := by
      apply h.2.2 pre u post hs <;> assumption
    obtain ⟨j, hj, hij, he⟩ := later v hv
    let k : Fin g.vertexCount := ⟨j, by simpa [← m.size_eq] using hj⟩
    have hk : m.atPos k = v := (atPos_toList m k).trans he
    have hkv : m.position v = k :=
      (congrArg m.position hk).symm.trans (m.position_at k)
    rw [hkv]
    exact hij

def reverseIndex {n : Nat} (i : Fin n) : Fin n :=
  ⟨n - 1 - i.val, by have h := i.isLt; omega⟩

@[simp] theorem reverseIndex_reverseIndex {n : Nat} (i : Fin n) :
    reverseIndex (reverseIndex i) = i := by
  apply Fin.ext
  change n - 1 - (n - 1 - i.val) = i.val
  have h := i.isLt
  omega

variable (o : ValidOrder g order)

def encode (v : Fin g.vertexCount) : Fin g.vertexCount :=
  reverseIndex (o.position v)

def decode (i : Fin g.vertexCount) : Fin g.vertexCount :=
  o.atPos (reverseIndex i)

@[simp] theorem decode_encode (v : Fin g.vertexCount) :
    o.decode (o.encode v) = v := by
  simp only [decode, encode, reverseIndex_reverseIndex, o.at_position]

@[simp] theorem encode_decode (i : Fin g.vertexCount) :
    o.encode (o.decode i) = i := by
  simp only [encode, decode, o.position_at, reverseIndex_reverseIndex]

/-- Reading the new indices downward recovers the exact input order. -/
theorem decode_reverseIndex (i : Fin g.vertexCount) :
    o.decode (reverseIndex i) = order[i.val]'(by
      rw [o.size_eq]
      exact i.isLt) := by
  simpa only [decode, reverseIndex_reverseIndex] using o.atPos_eq i

theorem encode_orderEntry (i : Fin g.vertexCount) :
    o.encode (order[i.val]'(by rw [o.size_eq]; exact i.isLt)) =
      reverseIndex i := by
  rw [← o.decode_reverseIndex i, o.encode_decode]

theorem encode_lt_of_arc {u v : Fin g.vertexCount} (arc : g.HasArc u v) :
    (o.encode v).val < (o.encode u).val := by
  have h := o.forward u v arc
  have hv := (o.position v).isLt
  change g.vertexCount - 1 - (o.position v).val <
    g.vertexCount - 1 - (o.position u).val
  omega

private def narrowList {n k : Nat} (f : Fin n → Fin n) :
    (xs : List (Fin n)) →
    (∀ v, v ∈ xs → (f v).val < k) → List (Fin k)
  | [], _ => []
  | v :: vs, h =>
      ⟨(f v).val, h v (List.Mem.head vs)⟩ ::
        narrowList f vs (fun w hw => h w (List.Mem.tail v hw))

private theorem map_narrowList {n k : Nat} (f : Fin n → Fin n)
    (back : Fin k → Fin n) (xs : List (Fin n))
    (h : ∀ v, v ∈ xs → (f v).val < k)
    (inv : ∀ (v : Fin n) (hv : (f v).val < k), back ⟨(f v).val, hv⟩ = v) :
    (narrowList f xs h).map back = xs := by
  induction xs with
  | nil => rfl
  | cons v vs ih => simp only [narrowList, List.map_cons, inv, ih]

def row (p : Fin g.vertexCount) : List (Fin p.val) :=
  narrowList o.encode (g.outArcs (o.decode p)) (fun v hv => by
    have h := o.encode_lt_of_arc (u := o.decode p) (v := v) hv
    simpa only [o.encode_decode] using h)

abbrev PackedRow (n : Nat) := Σ p : Fin n, List (Fin p.val)

/-- Materialization visits n rows and one cons per original arc occurrence,
including parallel arcs. There is one decode per row and one encode per
occurrence. With constant-time maps and original row access, this adds
O(n + m) time and storage, where m counts occurrences, separately from
the existing Kahn and scan counts. -/
def rowTable : Vector (PackedRow g.vertexCount) g.vertexCount :=
  Vector.ofFn (fun p => ⟨p, o.row p⟩)

private theorem rowTable_get (p : Fin g.vertexCount) :
    (o.rowTable[p.val] : PackedRow g.vertexCount) = ⟨p, o.row p⟩ := by
  simp [rowTable]

private def unpack {n : Nat} (p : Fin n) (x : PackedRow n) (h : x.1 = p) :
    List (Fin p.val) :=
  h ▸ x.2

private theorem unpack_eq {n : Nat} (p : Fin n) (xs : List (Fin p.val))
    (x : PackedRow n) (h : x.1 = p) (hx : x = ⟨p, xs⟩) :
    unpack p x h = xs := by
  subst x
  rfl

/-- Capture the materialized table once. Looking up a row does not relabel it. -/
def dag : FailureDAG :=
  let table := o.rowTable
  { vertexCount := g.vertexCount
    children := fun p =>
      unpack p table[p.val]
        (congrArg (fun x : PackedRow g.vertexCount => x.1) (o.rowTable_get p)) }

theorem dag_children (p : Fin g.vertexCount) :
    o.dag.children p = o.row p := by
  change unpack p o.rowTable[p.val] _ = o.row p
  exact unpack_eq p (o.row p) _ _ (o.rowTable_get p)

/-- Exact list equality, not just adjacency: parallel occurrences survive. -/
theorem children_values (p : Fin g.vertexCount) :
    (o.dag.children p).map (fun c => o.decode (o.dag.childIndex p c)) =
      g.outArcs (o.decode p) := by
  rw [o.dag_children]
  unfold row
  apply map_narrowList
  intro v hv
  exact o.decode_encode v

theorem children_length (p : Fin g.vertexCount) :
    (o.dag.children p).length = (g.outArcs (o.decode p)).length := by
  simpa only [List.length_map] using congrArg List.length (o.children_values p)

theorem hasArc_iff_child (p q : Fin g.vertexCount) :
    g.HasArc (o.decode p) (o.decode q) ↔
      ∃ c : Fin p.val, c ∈ o.dag.children p ∧ o.dag.childIndex p c = q := by
  change o.decode q ∈ g.outArcs (o.decode p) ↔ _
  rw [← o.children_values p, List.mem_map]
  constructor
  · rintro ⟨c, hc, he⟩
    refine ⟨c, hc, ?_⟩
    exact (o.encode_decode (o.dag.childIndex p c)).symm.trans
      ((congrArg o.encode he).trans (o.encode_decode q))
  · rintro ⟨c, hc, he⟩
    exact ⟨c, hc, congrArg o.decode he⟩

def failedAt (failed : Fin g.vertexCount → Prop) :
    Fin o.dag.vertexCount → Prop :=
  fun p => failed (o.decode p)

theorem toReachAvoid {failed : Fin g.vertexCount → Prop}
    {u v : Fin g.vertexCount} (h : g.SurvivingPath failed u v) :
    o.dag.ReachAvoid (o.failedAt failed) (o.encode u) (o.encode v) := by
  change AvoidPath g.HasArc failed u v at h
  induction h with
  | refl a alive =>
      refine FailureDAG.ReachAvoid.here (g := o.dag) (o.encode a) ?_
      simpa only [failedAt, o.decode_encode] using alive
  | step a b t alive arc _ ih =>
      have alive' : ¬ o.failedAt failed (o.encode a) := by
        simpa only [failedAt, o.decode_encode] using alive
      have arc' : g.HasArc (o.decode (o.encode a)) (o.decode (o.encode b)) := by
        simpa only [o.decode_encode] using arc
      obtain ⟨c, hc, he⟩ := (o.hasArc_iff_child (o.encode a) (o.encode b)).mp arc'
      refine FailureDAG.ReachAvoid.step (g := o.dag) (o.encode a) c (o.encode t) alive' hc ?_
      rw [he]
      exact ih

theorem ofReachAvoid {failed : Fin g.vertexCount → Prop}
    {p q : Fin o.dag.vertexCount} (h : o.dag.ReachAvoid (o.failedAt failed) p q) :
    g.SurvivingPath failed (o.decode p) (o.decode q) := by
  induction h with
  | here p alive => exact AvoidPath.refl (o.decode p) alive
  | step p c t alive edge _ ih =>
      have arc : g.HasArc (o.decode p) (o.decode (o.dag.childIndex p c)) :=
        (o.hasArc_iff_child p (o.dag.childIndex p c)).mpr ⟨c, edge, rfl⟩
      exact AvoidPath.step (o.decode p) (o.decode (o.dag.childIndex p c))
        (o.decode t) alive arc ih

theorem survivingPath_iff (failed : Fin g.vertexCount → Prop)
    (u v : Fin g.vertexCount) :
    g.SurvivingPath failed u v ↔
      o.dag.ReachAvoid (o.failedAt failed) (o.encode u) (o.encode v) := by
  refine ⟨fun h => o.toReachAvoid h, ?_⟩
  intro h
  simpa only [o.decode_encode] using o.ofReachAvoid h

end ValidOrder
end PaperB.Decreasing
