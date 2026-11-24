module

public import PaperB.PackedStaticLayout

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.StaticLinearHead

open StaticHeadSweep LabelledQuotient ForestHeavyPath ForestLayout
open PackedStaticLayout (Input InputOK)

variable {N : Nat}

abbrev entryColumn (x : Input N) : Slots N Nat :=
  (PackedStaticLayout.build x).endpoints.entry

/-- This list is used only in specifications and proofs. -/
abbrev preorderSpec (x : Input N) : List (Fin N) :=
  dfsPreorder x.root x.parent.read x.depth.read

theorem preorder_length (x : Input N) (ht : InputOK x) :
    (preorderSpec x).length = N :=
  length_dfsPreorder ht

private theorem split_at_entry (x : Input N) (ht : InputOK x) (v : Fin N) :
    ∃ l r : List (Fin N), preorderSpec x = l ++ v :: r ∧
      (entryColumn x).read v = l.length := by
  have hTree : ValidDepthTree x.root x.parent.read x.depth.read := ht
  obtain ⟨l, r, hs⟩ := exists_split_dfsPreorder hTree v
  have hv : ∃ t : List (Fin N), preorderSpec x = l ++ v :: t := by
    first
    | exact ⟨r, hs⟩
    | rw [dfsSubtree_unfold hTree v] at hs
      refine ⟨concatMapList (dfsSubtree x.root x.parent.read x.depth.read)
        (bucketChildren x.root x.parent.read v) ++ r, ?_⟩
      simpa only [List.append_assoc, List.cons_append] using hs
  obtain ⟨t, hv⟩ := hv
  refine ⟨l, t, hv, ?_⟩
  rw [PackedStaticLayout.entry_exact x ht v]
  first
  | exact entry_eq_length_of_dfsPreorder_split hTree hs
  | exact entry_eq_length_of_dfsPreorder_split hTree hv
  | exact entry_eq_length_of_dfsPreorder_split hTree
      (by simpa only [List.append_assoc] using hs)
  | exact (entry_eq_length_of_dfsPreorder_split hTree hs).symm
  | exact (entry_eq_length_of_dfsPreorder_split hTree hv).symm

theorem entry_lt (x : Input N) (ht : InputOK x) (v : Fin N) :
    (entryColumn x).read v < N := by
  obtain ⟨l, r, hs, he⟩ := split_at_entry x ht v
  have hlen := congrArg List.length hs
  simp only [preorder_length x ht, List.length_append, List.length_cons] at hlen
  rw [he]
  omega

private theorem get_at_split {α : Type} {xs l r : List α} {v : α} {i : Nat}
    (hs : xs = l ++ v :: r) (hi : i < xs.length) (he : i = l.length) :
    xs[i]'hi = v := by
  subst xs
  subst i
  induction l with
  | nil => rfl
  | cons a l ih =>
    have hb : l.length < (l ++ v :: r).length := by
      simp only [List.cons_append, List.length_cons] at hi
      omega
    exact ih hb

theorem preorder_get_entry (x : Input N) (ht : InputOK x) (v : Fin N) :
    (preorderSpec x)[(entryColumn x).read v]'(by
      rw [preorder_length x ht]
      exact entry_lt x ht v) = v := by
  obtain ⟨l, r, hs, he⟩ := split_at_entry x ht v
  exact get_at_split hs _ he

def rank (entry : Slots N Nat) (ok : ∀ v : Fin N, entry.read v < N)
    (v : Fin N) : Fin N :=
  ⟨entry.read v, ok v⟩

theorem rank_injective (x : Input N) (ht : InputOK x) :
    ∀ {u v : Fin N},
      rank (entryColumn x) (entry_lt x ht) u =
        rank (entryColumn x) (entry_lt x ht) v → u = v := by
  intro u v h
  let atRank (i : Fin N) : Fin N :=
    (preorderSpec x)[i.val]'(by
      rw [preorder_length x ht]
      exact i.isLt)
  have hu : atRank (rank (entryColumn x) (entry_lt x ht) u) = u :=
    preorder_get_entry x ht u
  have hv : atRank (rank (entryColumn x) (entry_lt x ht) v) = v :=
    preorder_get_entry x ht v
  exact hu.symm.trans ((congrArg atRank h).trans hv)

structure ScatterState (N : Nat) where
  slots : Slots N (Fin N)
  writes : Nat

/-- The successor clause writes vertex `k` and tail-calls on the remaining
vertices `0, …, k-1`. The array is threaded as an owned accumulator. -/
private def scatter (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) :
    (n : Nat) → n ≤ N → Slots N (Fin N) → Nat → ScatterState N
  | 0, _, a, writes => ⟨a, writes⟩
  | k + 1, hk, a, writes =>
    let v : Fin N := ⟨k, by omega⟩
    scatter entry ok k (by omega) (a.write (rank entry ok v) v) (writes + 1)

private theorem scatter_write_count (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) (n : Nat) (hn : n ≤ N)
    (a : Slots N (Fin N)) (writes : Nat) :
    (scatter entry ok n hn a writes).writes = writes + n := by
  induction n generalizing a writes with
  | zero => simp [scatter]
  | succ n ih =>
    let v : Fin N := ⟨n, by omega⟩
    have hk : n ≤ N := by omega
    change (scatter entry ok n hk
      (a.write (rank entry ok v) v) (writes + 1)).writes = _
    rw [ih hk (a.write (rank entry ok v) v) (writes + 1)] <;> omega

private theorem scatter_read (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N)
    (inj : ∀ {u v : Fin N}, rank entry ok u = rank entry ok v → u = v)
    (v : Fin N) (n : Nat) (hn : n ≤ N) (a : Slots N (Fin N)) (writes : Nat) :
    (scatter entry ok n hn a writes).slots.read (rank entry ok v) =
      if v.val < n then v else a.read (rank entry ok v) := by
  induction n generalizing a writes with
  | zero => simp [scatter]
  | succ n ih =>
    let u : Fin N := ⟨n, by omega⟩
    have hk : n ≤ N := by omega
    change (scatter entry ok n hk
      (a.write (rank entry ok u) u) (writes + 1)).slots.read (rank entry ok v) = _
    rw [ih hk (a.write (rank entry ok u) u) (writes + 1)]
    by_cases hlt : v.val < n
    · rw [if_pos hlt, if_pos (show v.val < n + 1 by omega)]
    · rw [if_neg hlt]
      by_cases heq : v.val = n
      · have hvu : v = u := Fin.ext heq
        have hu : u.val < n + 1 := Nat.lt_succ_self n
        rw [hvu, Slots.read_write_same, if_pos hu]
      · have hne : rank entry ok v ≠ rank entry ok u :=
          fun h => heq (congrArg Fin.val (inj h))
        rw [Slots.read_write_other _ _ _ _ hne,
          if_neg (show ¬ v.val < n + 1 by omega)]

def inverseSlots (root : Fin N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) : ScatterState N :=
  scatter entry ok N (Nat.le_refl N) (Slots.fill N root) 0

/-- The `N` scatter writes do not include the initialization by `Slots.fill`. -/
theorem inverse_scatter_writes (root : Fin N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) :
    (inverseSlots root entry ok).writes = N := by
  simpa only [inverseSlots, Nat.zero_add] using
    scatter_write_count entry ok N (Nat.le_refl N) (Slots.fill N root) 0

theorem inverse_read (root : Fin N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N)
    (inj : ∀ {u v : Fin N}, rank entry ok u = rank entry ok v → u = v)
    (v : Fin N) :
    (inverseSlots root entry ok).slots.read (rank entry ok v) = v := by
  simpa only [inverseSlots, if_pos v.isLt] using
    scatter_read entry ok inj v N (Nat.le_refl N) (Slots.fill N root) 0

/-- `Array.toList` converts the inverse column in one linear pass, without a
second list or a reversal. No semantic preorder is evaluated here. -/
def inverseOrder (root : Fin N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) : List (Fin N) :=
  (inverseSlots root entry ok).slots.data.toList

theorem inverse_cells (root : Fin N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) :
    (inverseSlots root entry ok).slots.data.size = N :=
  (inverseSlots root entry ok).slots.len

theorem inverse_list_records (root : Fin N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) :
    (inverseOrder root entry ok).length = N := by
  simpa [inverseOrder] using inverse_cells root entry ok

private theorem index_eq_of_nodup {α : Type} (xs : List α) (hn : xs.Nodup)
    (i j : Nat) (hi : i < xs.length) (hj : j < xs.length)
    (he : xs[i]'hi = xs[j]'hj) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons a xs ih =>
    have h := List.nodup_cons.mp hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
        have ha : a = xs[j]'hj' := by simpa using he
        exfalso
        apply h.1
        rw [ha]
        first | exact List.getElem_mem _ | exact List.getElem_mem | exact?
    | succ i =>
      have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
      cases j with
      | zero =>
        have ha : xs[i]'hi' = a := by simpa using he
        exfalso
        apply h.1
        rw [← ha]
        first | exact List.getElem_mem _ | exact List.getElem_mem | exact?
      | succ j =>
        have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
        exact congrArg Nat.succ (ih h.2 i j hi' hj' (by simpa using he))

theorem inverseOrder_eq_preorder (x : Input N) (ht : InputOK x) :
    inverseOrder x.root (entryColumn x) (entry_lt x ht) = preorderSpec x := by
  let e := entryColumn x
  let ok : ∀ v : Fin N, e.read v < N := entry_lt x ht
  let a := (inverseSlots x.root e ok).slots
  change a.data.toList = preorderSpec x
  apply List.ext_getElem
  · simpa using a.len.trans (preorder_length x ht).symm
  · intro i hi hj
    let v : Fin N := (preorderSpec x)[i]'hj
    have hv : (preorderSpec x)[e.read v]'(by
        rw [preorder_length x ht]
        exact ok v) = v := preorder_get_entry x ht v
    have hvi : e.read v = i :=
      index_eq_of_nodup (preorderSpec x) (nodup_dfsPreorder ht) _ _ _ hj hv
    let index : Fin N := ⟨i, by simpa [a.len] using hi⟩
    have hr : rank e ok v = index := Fin.ext hvi
    have hread := inverse_read x.root e ok (rank_injective x ht) v
    change a.read (rank e ok v) = v at hread
    rw [hr] at hread
    simpa [Slots.read, index, v] using hread

def sweepEntries (p : Packed N) (entry : Slots N Nat)
    (ok : ∀ v : Fin N, entry.read v < N) : StaticHeadSweep.State N :=
  let order := inverseOrder p.root entry ok
  StaticHeadSweep.sweep p order

theorem sweepEntries_eq (x : Input N) (ht : InputOK x) :
    sweepEntries (PackedStaticLayout.build x).packed (entryColumn x) (entry_lt x ht) =
      StaticHeadSweep.build (PackedStaticLayout.build x).packed := by
  have ho :
      inverseOrder (PackedStaticLayout.build x).packed.root (entryColumn x)
        (entry_lt x ht) =
      StaticHeadSweep.preorder (PackedStaticLayout.build x).packed :=
    inverseOrder_eq_preorder x ht
  simp only [sweepEntries, StaticHeadSweep.build, ho]

theorem head_writes (x : Input N) (ht : InputOK x) :
    (sweepEntries (PackedStaticLayout.build x).packed (entryColumn x)
      (entry_lt x ht)).writes = N := by
  rw [sweepEntries_eq x ht]
  exact StaticHeadSweep.build_write_count (PackedStaticLayout.build x).packed ht

/--
Build the packed layout once and materialize the head column before creating
the lookup closure. Beyond the packed layout and the output head column, the
adapter uses one transient `N`-cell array and `N` list cons records. In Lean's
unique-array update cost model, filling and scattering the inverse array,
converting it to a list, and sweeping it are linear work. The bound and
correctness proofs are erased; neither loop computes any list lengths.
-/
def tables (x : Input N) (ht : InputOK x) : EX16.Tables (Fin N) :=
  let b := PackedStaticLayout.build x
  let p := b.packed
  let heads := (sweepEntries p b.endpoints.entry (entry_lt x ht)).heads
  { root := p.root
    parent := p.parent.read
    depth := p.depth.read
    heavy := p.heavy.read
    head := heads.read
    size := p.size.read }

theorem tables_eq (x : Input N) (ht : InputOK x) :
    tables x ht = StaticHeadSweep.tables (PackedStaticLayout.build x).packed := by
  simp only [tables, sweepEntries_eq x ht] <;> rfl

theorem valid (x : Input N) (ht : InputOK x) : EX16.Valid (tables x ht) := by
  rw [tables_eq x ht]
  exact PackedStaticLayout.valid x ht

end PaperB.StaticLinearHead
