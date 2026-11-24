module

public import PaperB.Kahn
public import PaperB.StaticLinearHead

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.KahnInverse

open StaticLinearHead StaticHeadSweep

variable {n : Nat} (order : Array (Fin n)) (hs : order.size = n)

def vertexAt (i : Fin n) : Fin n :=
  order[i.val]'(by simpa only [hs] using i.isLt)

/-- One traversal of the supplied order forms the identity-by-order column.
    The inverse then uses one scatter pass over that column, with no searches. -/
private def column : Slots n Nat :=
  ⟨order.map Fin.val, by simpa using hs⟩

private theorem column_read (i : Fin n) :
    (column order hs).read i = (vertexAt order hs i).val := by
  change (order.map Fin.val)[i.val]'(by simpa [hs] using i.isLt) = _
  simp [vertexAt]

private theorem column_ok (i : Fin n) : (column order hs).read i < n := by
  rw [column_read]
  exact (vertexAt order hs i).isLt

private theorem column_rank (i : Fin n) :
    StaticLinearHead.rank (column order hs) (column_ok order hs) i =
      vertexAt order hs i :=
  Fin.ext (column_read order hs i)

def build : ScatterState n :=
  if h : 0 < n then inverseSlots ⟨0, h⟩ (column order hs) (column_ok order hs)
  else { slots := ⟨#[], by change 0 = n; omega⟩, writes := 0 }

theorem scatter_writes : (build order hs).writes = n := by
  unfold build
  split
  · exact inverse_scatter_writes _ _ _
  · change 0 = n
    omega

/-- Reference rank of a supplied order. A caller making multiple probes must
    build the inverse once and read its slots directly. -/
def rank (v : Fin n) : Fin n := (build order hs).slots.read v

private theorem vertexAt_inj (hd : order.toList.Nodup) :
    Function.Injective (vertexAt order hs) := by
  change List.Pairwise (· ≠ ·) order.toList at hd
  have sep (i j : Fin n) (hij : i.val < j.val) :
      vertexAt order hs i ≠ vertexAt order hs j := by
    intro he
    exact (List.pairwise_iff_getElem.mp hd) i.val j.val
      (by simpa [hs] using i.isLt) (by simpa [hs] using j.isLt) hij
      (by simpa only [Array.getElem_toList, vertexAt] using he)
  intro i j he
  apply Fin.ext
  rcases Nat.lt_trichotomy i.val j.val with h | h | h
  · exact False.elim (sep i j h he)
  · exact h
  · exact False.elim (sep j i h he.symm)

private theorem vertexAt_surj (hall : ∀ v : Fin n, v ∈ order.toList) :
    Function.Surjective (vertexAt order hs) := by
  intro v
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp (hall v)
  exact ⟨⟨i, by simpa [hs] using hi⟩,
    by simpa only [Array.getElem_toList, vertexAt] using he⟩

theorem rank_vertexAt (hd : order.toList.Nodup) (i : Fin n) :
    rank order hs (vertexAt order hs i) = i := by
  have hi := i.isLt
  have hn : 0 < n := by omega
  have inj {a b : Fin n}
      (h : StaticLinearHead.rank (column order hs) (column_ok order hs) a =
        StaticLinearHead.rank (column order hs) (column_ok order hs) b) : a = b :=
    vertexAt_inj order hs hd (by simpa only [column_rank] using h)
  simpa only [rank, build, dif_pos hn, column_rank] using
    inverse_read ⟨0, hn⟩ (column order hs) (column_ok order hs) inj i

theorem rank_injective (g : Digraph) (xs : Array (Fin g.vertexCount))
    (hx : xs.size = g.vertexCount) (ht : g.IsTopologicalList xs.toList) :
    Function.Injective (rank xs hx) := by
  intro u v huv
  obtain ⟨i, rfl⟩ := vertexAt_surj xs hx ht.2.1 u
  obtain ⟨j, rfl⟩ := vertexAt_surj xs hx ht.2.1 v
  exact congrArg (vertexAt xs hx) (by simpa only [rank_vertexAt xs hx ht.1] using huv)

private theorem split_get {α : Type} (xs : List α) (i : Nat) (hi : i < xs.length) :
    ∃ pre post, pre.length = i ∧ xs = pre ++ xs[i] :: post := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => exact ⟨[], xs, rfl, rfl⟩
    | succ i =>
      obtain ⟨pre, post, hp, he⟩ := ih i (Nat.lt_of_succ_lt_succ hi)
      exact ⟨a :: pre, post, congrArg Nat.succ hp, congrArg (a :: ·) he⟩

private theorem suffix_index {α : Type} (pre : List α) (u : α)
    {post : List α} {v : α} (hv : v ∈ post) :
    ∃ j, ∃ hj : j < (pre ++ u :: post).length,
      pre.length < j ∧ (pre ++ u :: post)[j] = v := by
  induction pre with
  | nil =>
    obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hv
    exact ⟨j + 1, Nat.succ_lt_succ hj, Nat.zero_lt_succ _, he⟩
  | cons a pre ih =>
    obtain ⟨j, hj, hlt, he⟩ := ih
    exact ⟨j + 1, Nat.succ_lt_succ hj, Nat.succ_lt_succ hlt, he⟩

theorem rank_arc (g : Digraph) (xs : Array (Fin g.vertexCount))
    (hx : xs.size = g.vertexCount) (ht : g.IsTopologicalList xs.toList)
    {u v : Fin g.vertexCount} (huv : g.HasArc u v) : rank xs hx u < rank xs hx v := by
  obtain ⟨i, hi⟩ := vertexAt_surj xs hx ht.2.1 u
  have hil : i.val < xs.toList.length := by simpa [hx] using i.isLt
  obtain ⟨pre, post, hp, hspl⟩ := split_get xs.toList i.val hil
  have hu : xs.toList[i.val] = u := by
    simpa only [Array.getElem_toList, vertexAt] using hi
  rw [hu] at hspl
  have hex : ∃ j, ∃ hj : j < xs.toList.length, i.val < j ∧ xs.toList[j] = v := by
    rw [hspl, ← hp]
    exact suffix_index pre u (ht.2.2 pre u post hspl v huv)
  obtain ⟨j, hj, hij, he⟩ := hex
  let k : Fin g.vertexCount := ⟨j, by simpa [hx] using hj⟩
  have hk : vertexAt xs hx k = v := by
    simpa only [Array.getElem_toList, vertexAt, k] using he
  simpa only [rank_vertexAt xs hx ht.1, hi, hk] using
    (show rank xs hx (vertexAt xs hx i) < rank xs hx (vertexAt xs hx k) by
      simpa only [rank_vertexAt xs hx ht.1] using (show i < k from hij))

abbrev ofRun (g : Digraph) (h : (Kahn.run g).order.size = g.vertexCount) :=
  build (Kahn.run g).order h

end PaperB.KahnInverse
