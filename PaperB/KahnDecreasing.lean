module

public import PaperB.DecreasingDAG
public import PaperB.Kahn
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace KahnDecreasing

open Kahn Decreasing Digraph

set_option autoImplicit false

private theorem mem_index {α : Type} {xs : List α} {v : α}
    (h : v ∈ xs) : ∃ j, ∃ hj : j < xs.length, xs[j] = v := by
  induction h with
  | head xs => exact ⟨0, Nat.zero_lt_succ xs.length, rfl⟩
  | tail a _ ih =>
      obtain ⟨j, hj, he⟩ := ih
      exact ⟨j + 1, Nat.succ_lt_succ hj, he⟩

private theorem listGet_mem {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) : xs[i] ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero =>
          change a ∈ a :: xs
          simp
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          exact List.mem_cons_of_mem a (ih i hi')

private theorem listGet_injective {α : Type} (xs : List α)
    (hn : xs.Nodup) (i j : Nat) (hi : i < xs.length) (hj : j < xs.length)
    (he : xs[i] = xs[j]) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
      obtain ⟨ha, ht⟩ := List.nodup_cons.mp hn
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
              change a = xs[j]'hj' at he
              exact (ha (he.symm ▸ listGet_mem xs j hj')).elim
      | succ i =>
          have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
          cases j with
          | zero =>
              change xs[i]'hi' = a at he
              exact (ha (he ▸ listGet_mem xs i hi')).elim
          | succ j =>
              have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
              exact congrArg Nat.succ (ih ht i j hi' hj' he)

/-- The next scatter write targets a slot untouched by the processed prefix. -/
theorem freshIndex {n : Nat} (order : Array (Fin n))
    (hn : order.toList.Nodup) {i j : Nat} (hi : i < order.size) (hj : j < i) :
    (order[j]'(Nat.lt_trans hj hi)).val ≠ (order[i]'hi).val := by
  intro he
  have hj' : j < order.toList.length := by simpa using Nat.lt_trans hj hi
  have hi' : i < order.toList.length := by simpa using hi
  have hv : order[j]'(Nat.lt_trans hj hi) = order[i]'hi := Fin.ext he
  have hl : order.toList[j]'hj' = order.toList[i]'hi' := by simpa using hv
  have hji := listGet_injective order.toList hn j i hj' hi' hl
  omega

/-- `lookup` certifies all writes in the processed prefix. The counters charge
the scatter pass; the initial `Array.replicate` is a separate linear allocation. -/
structure InverseRankTable {n : Nat} (order : Array (Fin n)) (processed : Nat) where
  ranks : Array Nat
  orderReads : Nat
  indexWrites : Nat
  size_eq : ranks.size = n
  reads_eq : orderReads = processed
  writes_eq : indexWrites = processed
  lookup (j : Nat) (hp : j < processed) (hj : j < order.size) :
    ranks[(order[j]'hj).val]'(by rw [size_eq]; exact (order[j]'hj).isLt) = j

private def writeRank {n : Nat} (order : Array (Fin n))
    (hn : order.toList.Nodup) (i : Nat) (hi : i < order.size)
    (s : InverseRankTable order i) : InverseRankTable order (i + 1) := by
  cases s with
  | mk a reads writes ha hr hw hp =>
      let v := order[i]'hi
      have hv : v.val < a.size := by rw [ha]; exact v.isLt
      let b := a.set v.val i
      have hb : b.size = n := by simpa [b] using ha
      refine ⟨b, reads + 1, writes + 1, hb, congrArg (· + 1) hr,
        congrArg (· + 1) hw, ?_⟩
      intro j hji hj
      by_cases e : j = i
      · subst j
        change b[v.val]'(by rw [hb]; exact v.isLt) = i
        simp [b]
      · have hj₀ : j < i := by omega
        have hne : (order[j]'hj).val ≠ v.val := freshIndex order hn hi hj₀
        calc
          b[(order[j]'hj).val]'(by rw [hb]; exact (order[j]'hj).isLt) =
              a[(order[j]'hj).val]'(by rw [ha]; exact (order[j]'hj).isLt) := by
                simp [b, Array.getElem_set, Ne.symm hne]
          _ = j := hp j hj₀ hj

private def fillRanks {n : Nat} (order : Array (Fin n))
    (hn : order.toList.Nodup) :
    (fuel i : Nat) → i + fuel = order.size →
      InverseRankTable order i → InverseRankTable order order.size
  | 0, i, h, s => by
      have e : i = order.size := by simpa using h
      exact e ▸ s
  | fuel + 1, i, h, s =>
      fillRanks order hn fuel (i + 1) (by omega)
        (writeRank order hn i (by omega) s)

/-- Tail-recursive scatter over the actual array. Each iteration consumes the
old accumulator, reads one order entry, and performs one plain `Array.set`. -/
def inverseRanks {n : Nat} (order : Array (Fin n))
    (hn : order.toList.Nodup) : InverseRankTable order order.size :=
  fillRanks order hn order.size 0 (Nat.zero_add _)
    ⟨Array.replicate n 0, 0, 0, by simp, rfl, rfl, by
      intro j hj _
      omega⟩

private def arrayAt {n : Nat} (order : Array (Fin n))
    (i : Fin order.size) : Fin n :=
  order[i.val]'i.isLt

private theorem arrayAt_surjective {n : Nat} (order : Array (Fin n))
    (hall : ∀ v : Fin n, v ∈ order.toList) (v : Fin n) :
    ∃ i : Fin order.size, arrayAt order i = v := by
  obtain ⟨j, hj, he⟩ := mem_index (hall v)
  let i : Fin order.size := ⟨j, by simpa using hj⟩
  exact ⟨i, by simpa [arrayAt, i] using he⟩

def readRank {n processed : Nat} {order : Array (Fin n)}
    (t : InverseRankTable order processed) (v : Fin n) : Nat :=
  t.ranks[v.val]'(by rw [t.size_eq]; exact v.isLt)

private theorem readRank_at {n : Nat} {order : Array (Fin n)}
    (t : InverseRankTable order order.size) (i : Fin order.size) :
    readRank t (arrayAt order i) = i.val :=
  t.lookup i.val i.isLt i.isLt

private def inversePos {n : Nat} {order : Array (Fin n)}
    (t : InverseRankTable order order.size)
    (hall : ∀ v : Fin n, v ∈ order.toList) (v : Fin n) : Fin order.size :=
  ⟨readRank t v, by
    obtain ⟨i, hi⟩ := arrayAt_surjective order hall v
    rw [← hi, readRank_at]
    exact i.isLt⟩

private theorem inversePos_at {n : Nat} {order : Array (Fin n)}
    (t : InverseRankTable order order.size)
    (hall : ∀ v : Fin n, v ∈ order.toList) (i : Fin order.size) :
    inversePos t hall (arrayAt order i) = i :=
  Fin.ext (readRank_at t i)

private theorem at_inversePos {n : Nat} {order : Array (Fin n)}
    (t : InverseRankTable order order.size)
    (hall : ∀ v : Fin n, v ∈ order.toList) (v : Fin n) :
    arrayAt order (inversePos t hall v) = v := by
  obtain ⟨i, hi⟩ := arrayAt_surjective order hall v
  rw [← hi, inversePos_at]

private def removeSlot {n : Nat} (cut x : Fin (n + 1))
    (hne : x ≠ cut) : Fin n :=
  ⟨if x.val < cut.val then x.val else x.val - 1, by
    have hx := x.isLt
    have hc := cut.isLt
    have hd : x.val ≠ cut.val := fun h => hne (Fin.ext h)
    split <;> omega⟩

private theorem removeSlot_injective {n : Nat} {cut x y : Fin (n + 1)}
    (hx : x ≠ cut) (hy : y ≠ cut)
    (h : removeSlot cut x hx = removeSlot cut y hy) : x = y := by
  apply Fin.ext
  have he := congrArg Fin.val h
  change (if x.val < cut.val then x.val else x.val - 1) =
    (if y.val < cut.val then y.val else y.val - 1) at he
  have hxd : x.val ≠ cut.val := fun e => hx (Fin.ext e)
  have hyd : y.val ≠ cut.val := fun e => hy (Fin.ext e)
  by_cases hxl : x.val < cut.val <;> by_cases hyl : y.val < cut.val <;>
    simp only [hxl, hyl, ite_true, ite_false] at he <;> omega

private theorem fin_le_of_injection {m n : Nat} (f : Fin m → Fin n)
    (hf : ∀ a b, f a = f b → a = b) : m ≤ n := by
  induction n generalizing m with
  | zero =>
      cases m with
      | zero => exact Nat.le_refl 0
      | succ m => exact Fin.elim0 (f ⟨0, Nat.zero_lt_succ m⟩)
  | succ n ih =>
      cases m with
      | zero => exact Nat.zero_le _
      | succ m =>
          let lift (i : Fin m) : Fin (m + 1) :=
            ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self m)⟩
          let last : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
          have avoid (i : Fin m) : f (lift i) ≠ f last := by
            intro he
            have hval : i.val = m :=
              congrArg Fin.val (hf (lift i) last he)
            have hi := i.isLt
            omega
          let f' (i : Fin m) : Fin n := removeSlot (f last) (f (lift i)) (avoid i)
          have hf' (a b : Fin m) (he : f' a = f' b) : a = b :=
            Fin.ext (congrArg (fun x : Fin (m + 1) => x.val)
              (hf (lift a) (lift b) (removeSlot_injective (avoid a) (avoid b) he)))
          exact Nat.succ_le_succ (ih f' hf')

private theorem table_cardinality {n : Nat} {order : Array (Fin n)}
    (t : InverseRankTable order order.size)
    (hall : ∀ v : Fin n, v ∈ order.toList) : order.size = n := by
  apply Nat.le_antisymm
  · apply fin_le_of_injection (arrayAt order)
    intro a b e
    simpa only [inversePos_at] using congrArg (inversePos t hall) e
  · apply fin_le_of_injection (inversePos t hall)
    intro a b e
    simpa only [at_inversePos] using congrArg (arrayAt order) e

theorem exact_cardinality {n : Nat} (order : Array (Fin n))
    (hn : order.toList.Nodup) (hall : ∀ v : Fin n, v ∈ order.toList) :
    order.size = n :=
  table_cardinality (inverseRanks order hn) hall

private def mapsOfTable {g : Digraph} (order : Array (Fin g.vertexCount))
    (spec : g.IsTopologicalList order.toList)
    (t : InverseRankTable order order.size) : Decreasing.OrderMaps g order := by
  have hs := table_cardinality t spec.2.1
  let atPos (i : Fin g.vertexCount) : Fin g.vertexCount :=
    arrayAt order ⟨i.val, by rw [hs]; exact i.isLt⟩
  let position (v : Fin g.vertexCount) : Fin g.vertexCount :=
    ⟨(inversePos t spec.2.1 v).val, by
      exact Nat.lt_of_lt_of_le (inversePos t spec.2.1 v).isLt (Nat.le_of_eq hs)⟩
  have hp (i : Fin g.vertexCount) : position (atPos i) = i := by
    let j : Fin order.size := ⟨i.val, by rw [hs]; exact i.isLt⟩
    exact Fin.ext (congrArg (fun x : Fin order.size => x.val) (inversePos_at t spec.2.1 j))
  have ha (v : Fin g.vertexCount) : atPos (position v) = v :=
    at_inversePos t spec.2.1 v
  exact {
    size_eq := hs
    atPos := atPos
    position := position
    atPos_eq := by
      intro i
      first | rfl | simp [atPos, arrayAt]
    at_position := ha
    position_at := hp
  }

def kahnInverse (g : Digraph) (h : IsAcyclic g) :
    InverseRankTable (Kahn.run g).order (Kahn.run g).order.size :=
  inverseRanks (Kahn.run g).order (Kahn.run_isTopologicalList g h).1

theorem kahn_inverse_cost (g : Digraph) (h : IsAcyclic g) :
    (Kahn.run g).order.size = g.vertexCount ∧
    (kahnInverse g h).ranks.size = g.vertexCount ∧
    (kahnInverse g h).orderReads = g.vertexCount ∧
    (kahnInverse g h).indexWrites = g.vertexCount := by
  let t := kahnInverse g h
  have hs := table_cardinality t (Kahn.run_isTopologicalList g h).2.1
  exact ⟨hs, t.size_eq, t.reads_eq.trans hs, t.writes_eq.trans hs⟩

def kahnValidOrder (g : Digraph) (h : IsAcyclic g) :
    Decreasing.ValidOrder g (Kahn.run g).order :=
  let order := (Kahn.run g).order
  let spec : g.IsTopologicalList order.toList := Kahn.run_isTopologicalList g h
  Decreasing.ValidOrder.ofTopologicalList
    (mapsOfTable order spec (inverseRanks order spec.1)) spec

theorem kahn_position_val (g : Digraph) (h : IsAcyclic g) (v : Fin g.vertexCount) :
    ((kahnValidOrder g h).position v).val = readRank (kahnInverse g h) v :=
  rfl

private def flipRank {n : Nat} (i : Fin n) : Fin n :=
  ⟨n - (i.val + 1), by have hi := i.isLt; omega⟩

private theorem flipRank_flipRank {n : Nat} (i : Fin n) :
    flipRank (flipRank i) = i := by
  apply Fin.ext
  change n - (n - (i.val + 1) + 1) = i.val
  have hi := i.isLt
  omega

section Relabel

variable {g : Digraph} {order : Array (Fin g.vertexCount)}

def decreasingId (m : Decreasing.ValidOrder g order)
    (u : Fin g.vertexCount) : Fin g.vertexCount :=
  flipRank (m.position u)

def originalId (m : Decreasing.ValidOrder g order)
    (i : Fin g.vertexCount) : Fin g.vertexCount :=
  m.atPos (flipRank i)

@[simp] theorem original_decreasing (m : Decreasing.ValidOrder g order)
    (u : Fin g.vertexCount) : originalId m (decreasingId m u) = u := by
  simp only [originalId, decreasingId, flipRank_flipRank, m.at_position]

@[simp] theorem decreasing_original (m : Decreasing.ValidOrder g order)
    (i : Fin g.vertexCount) : decreasingId m (originalId m i) = i := by
  simp only [originalId, decreasingId, m.position_at, flipRank_flipRank]

def RankedArc (m : Decreasing.ValidOrder g order) (i j : Fin g.vertexCount) : Prop :=
  g.HasArc (originalId m i) (originalId m j)

theorem rankedArc_decreases (m : Decreasing.ValidOrder g order)
    {i j : Fin g.vertexCount} (e : RankedArc m i j) : j.val < i.val := by
  have he := m.forward (originalId m i) (originalId m j) e
  simp only [originalId, m.position_at] at he
  change g.vertexCount - (i.val + 1) < g.vertexCount - (j.val + 1) at he
  omega

end Relabel

/-- Directed paths indexed by exact edge count, including the empty path. -/
inductive Path {α : Type} (arc : α → α → Prop) : Nat → α → α → Prop where
  | nil (u : α) : Path arc 0 u u
  | step {k : Nat} {u v w : α} :
      arc u v → Path arc k v w → Path arc (k + 1) u w

private theorem mapPath {α β : Type} {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hf : ∀ a b, R a b → S (f a) (f b))
    {k : Nat} {u v : α} (p : Path R k u v) : Path S k (f u) (f v) := by
  induction p with
  | nil u => exact .nil (f u)
  | step e _ ih => exact .step (hf _ _ e) ih

theorem kahn_path_iff (g : Digraph) (h : IsAcyclic g) (k : Nat)
    (u v : Fin g.vertexCount) :
    Path g.HasArc k u v ↔
      Path (RankedArc (kahnValidOrder g h)) k
        (decreasingId (kahnValidOrder g h) u) (decreasingId (kahnValidOrder g h) v) := by
  let m := kahnValidOrder g h
  change Path g.HasArc k u v ↔ Path (RankedArc m) k (decreasingId m u) (decreasingId m v)
  constructor
  · intro p
    exact mapPath (R := g.HasArc) (S := RankedArc m) (decreasingId m)
      (by
        intro a b e
        simpa only [RankedArc, original_decreasing] using e) p
  · intro p
    simpa only [original_decreasing] using
      (mapPath (R := RankedArc m) (S := g.HasArc) (originalId m) (fun _ _ e => e) p)

/-- Map the occurrence arrays themselves: no sorting or deduplication. -/
def rankedChildren {g : Digraph} {order : Array (Fin g.vertexCount)}
    (m : Decreasing.ValidOrder g order)
    (rows : Fin g.vertexCount → Array (Fin g.vertexCount))
    (i : Fin g.vertexCount) : Array (Fin g.vertexCount) :=
  (rows (originalId m i)).map (decreasingId m)

theorem rankedChildren_mem_iff {g : Digraph} {order : Array (Fin g.vertexCount)}
    (m : Decreasing.ValidOrder g order)
    (rows : Fin g.vertexCount → Array (Fin g.vertexCount))
    (rows_spec : ∀ u v, v ∈ (rows u).toList ↔ g.HasArc u v)
    (i j : Fin g.vertexCount) :
    j ∈ (rankedChildren m rows i).toList ↔ RankedArc m i j := by
  simp only [rankedChildren, Array.toList_map, List.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa only [RankedArc, original_decreasing] using (rows_spec _ _).mp hv
  · intro e
    exact ⟨originalId m j, (rows_spec _ _).mpr e, decreasing_original m j⟩

def childCount {n : Nat} (v : Fin n) : List (Fin n) → Nat
  | [] => 0
  | x :: xs => (if x = v then 1 else 0) + childCount v xs

private theorem childCount_map {g : Digraph} {order : Array (Fin g.vertexCount)}
    (m : Decreasing.ValidOrder g order)
    (v : Fin g.vertexCount) (xs : List (Fin g.vertexCount)) :
    childCount (decreasingId m v) (xs.map (decreasingId m)) = childCount v xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have he : decreasingId m x = decreasingId m v ↔ x = v := by
        constructor
        · intro e
          simpa only [original_decreasing] using congrArg (originalId m) e
        · exact congrArg (decreasingId m)
      simp only [List.map_cons, childCount, he, ih]

/-- Preserve the multiplicity of every child, including parallel arcs. -/
theorem kahn_parallel_child_count (g : Digraph) (h : IsAcyclic g)
    (rows : Fin g.vertexCount → Array (Fin g.vertexCount))
    (u v : Fin g.vertexCount) :
    childCount (decreasingId (kahnValidOrder g h) v)
        (rankedChildren (kahnValidOrder g h) rows
          (decreasingId (kahnValidOrder g h) u)).toList =
      childCount v (rows u).toList := by
  simpa only [rankedChildren, original_decreasing, Array.toList_map] using
    childCount_map (kahnValidOrder g h) v (rows u).toList

theorem kahn_child_array_size (g : Digraph) (h : IsAcyclic g)
    (rows : Fin g.vertexCount → Array (Fin g.vertexCount))
    (u : Fin g.vertexCount) :
    (rankedChildren (kahnValidOrder g h) rows
      (decreasingId (kahnValidOrder g h) u)).size = (rows u).size := by
  simp [rankedChildren]

end KahnDecreasing
end PaperB
