module

public import PaperB.ArcBuckets
public import PaperB.DenseQuotientRows

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout

open PaperB.LabelledQuotient

variable {N : Nat}

/-- Filter and reverse in one pass. The counter advances for every input
vertex, including the discarded root. -/
private def selectNonRootRev (root : Fin N) :
    List (Fin N) → List (Fin N) → Nat → List (Fin N) × Nat
  | [], acc, visits => (acc, visits)
  | u :: us, acc, visits =>
      selectNonRootRev root us (if u = root then acc else u :: acc)
        (visits + 1)

private theorem selectNonRootRev_spec (root : Fin N)
    (xs acc : List (Fin N)) (visits : Nat) :
    selectNonRootRev root xs acc visits =
      ((xs.filter (fun u => decide (u ≠ root))).reverse ++ acc,
        visits + xs.length) := by
  induction xs generalizing acc visits with
  | nil => simp [selectNonRootRev]
  | cons u us ih =>
      rw [selectNonRootRev, ih]
      by_cases hu : u = root
      · simp [hu] <;> omega
      · simp [hu, List.reverse_cons, List.append_assoc] <;> omega

/-- The old cons pass specifies a filtered row in reverse input order. -/
private theorem bucketPassAux_order (root : Fin N)
    (parent : Fin N → Fin N) (q : Fin N) (xs : List (Fin N))
    (acc : Fin N → List (Fin N)) :
    bucketPassAux root parent xs acc q =
      (((xs.filter (fun u => decide (u ≠ root))).reverse).filter
        (fun u => decide (parent u = q))) ++ acc q := by
  induction xs generalizing acc with
  | nil => rfl
  | cons u us ih =>
      rw [bucketPassAux, ih]
      by_cases hu : u = root
      · simp [addChildToBuckets, hu]
      · by_cases hp : parent u = q
        · simp [addChildToBuckets, hu, hp, List.reverse_cons,
            List.filter_append, List.append_assoc]
        · have hq : q ≠ parent u := fun e => hp e.symm
          simp [addChildToBuckets, hu, hp, hq, List.reverse_cons,
            List.filter_append]

/--
Construction charges only. A root-filter visit tests one vertex and conses
at most one retained vertex. There is no separate input-reversal pass.

`grouping` is the work returned by `EX51.groupMap`: initialized cells,
scatter reads and writes, reversed list cells, and finish-row visits.
Each finish-row visit includes a further row read and write, not counted
in the scatter fields. These are source-level charges, not machine costs.
They do not count generating `finElems`, the cost inside key evaluation,
subsequent row lookups, or the dense layout's `ofBuckets` scan.
-/
structure GroupedChildWork where
  rootFilterVisits : Nat
  grouping : EX51.Work
  deriving Repr

/-- Retain the physical array returned by one call to stable `groupMap`.
Feeding it the reversed non-root enumeration preserves the old cons order. -/
def groupedChildLists (root : Fin N) (parent : Fin N → Fin N) :
    ChildLists N × GroupedChildWork :=
  let input := selectNonRootRev root (finElems N) [] 0
  let grouped := EX51.groupMap parent id input.1
  (⟨grouped.1.cells, grouped.1.size_eq⟩, ⟨input.2, grouped.2⟩)

theorem groupedChildLists_get (root : Fin N) (parent : Fin N → Fin N)
    (q : Fin N) :
    (groupedChildLists root parent).1.get q = bucketChildren root parent q := by
  change
    (EX51.group parent (selectNonRootRev root (finElems N) [] 0).1).1.row q =
      bucketChildren root parent q
  rw [EX51.group_row, selectNonRootRev_spec]
  simpa [bucketChildren] using
    (bucketPassAux_order root parent q (finElems N) (fun _ => [])).symm

theorem groupedChildLists_get_eq_bucketChildLists (root : Fin N)
    (parent : Fin N → Fin N) (q : Fin N) :
    (groupedChildLists root parent).1.get q =
      (bucketChildLists root parent).get q :=
  (groupedChildLists_get root parent q).trans
    (bucketChildLists_get root parent q).symm

theorem mem_groupedChildLists_iff (root : Fin N) (parent : Fin N → Fin N)
    (q c : Fin N) :
    c ∈ (groupedChildLists root parent).1.get q ↔ c ≠ root ∧ parent c = q := by
  rw [groupedChildLists_get]
  exact mem_bucketChildren_iff root parent q c

private theorem childLists_eq_of_row_array_eq {g h : ChildLists N}
    (e : g.rows = h.rows) : g = h := by
  cases g with
  | mk a ha =>
    cases h with
    | mk b hb =>
      change a = b at e
      subst b
      rfl

theorem groupedChildLists_eq_bucketChildLists (root : Fin N)
    (parent : Fin N → Fin N) :
    (groupedChildLists root parent).1 = bucketChildLists root parent := by
  let g := (groupedChildLists root parent).1
  let h := bucketChildLists root parent
  change g = h
  apply childLists_eq_of_row_array_eq
  apply Array.ext
  · rw [g.rows_size, h.rows_size]
  · intro i hiG hiH
    have hi : i < N := by simpa only [g.rows_size] using hiG
    let q : Fin N := ⟨i, hi⟩
    change g.get q = h.get q
    exact groupedChildLists_get_eq_bucketChildLists root parent q

private theorem filter_nonRoot_of_not_mem (root : Fin N) (xs : List (Fin N))
    (hn : root ∉ xs) :
    xs.filter (fun u => decide (u ≠ root)) = xs := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
      have hu : u ≠ root := fun e =>
        hn (List.mem_cons.mpr (Or.inl e.symm))
      have ht : root ∉ us := fun hm =>
        hn (List.mem_cons.mpr (Or.inr hm))
      rw [List.filter_cons_of_pos (p := fun i : Fin N => decide (i ≠ root)) (a := u) (decide_eq_true hu), ih ht]

private theorem filter_nonRoot_length (root : Fin N) (xs : List (Fin N))
    (hn : xs.Pairwise (· ≠ ·)) (hm : root ∈ xs) :
    (xs.filter (fun u => decide (u ≠ root))).length + 1 = xs.length := by
  induction xs with
  | nil => nomatch hm
  | cons u us ih =>
      obtain ⟨hd, ht⟩ := List.pairwise_cons.mp hn
      by_cases hu : u = root
      · subst u
        have hnot : root ∉ us := fun h => hd root h rfl
        rw [List.filter_cons_of_neg (by simp), filter_nonRoot_of_not_mem root us hnot]
        rfl
      · have hmTail : root ∈ us :=
          (List.mem_cons.mp hm).resolve_left (fun e => hu e.symm)
        have hlen := ih ht hmTail
        simp [hu] <;> omega

/-- Exact returned counters: scan all `N` vertices, scatter and reverse
`N - 1` retained entries, and allocate and finish all `N` rows. -/
theorem groupedChildLists_work (root : Fin N) (parent : Fin N → Fin N) :
    (groupedChildLists root parent).2 =
      ⟨N, ⟨N, N - 1, N - 1, N - 1, N⟩⟩ := by
  have hl : ((finElems N).filter (fun u => decide (u ≠ root))).length = N - 1 := by
    have h := filter_nonRoot_length root (finElems N)
      (nodup_finElems N) (mem_finElems root)
    rw [length_finElems N] at h
    omega
  let input := selectNonRootRev root (finElems N) [] 0
  change GroupedChildWork.mk input.2 (EX51.groupMap parent id input.1).2 = _
  rw [EX51.groupMap_work]
  dsimp only [input]
  rw [selectNonRootRev_spec]
  simpa only [List.length_reverse, List.append_nil, length_finElems, Nat.zero_add, hl]

end PaperB.ForestLayout

namespace PaperB.DenseQuotientRows

open PaperB.ForestLayout PaperB.LabelledQuotient

variable {N : Nat}

/-- The layout is indexed by the physically grouped buckets, not by the
old bucket constructor. `bucketWork` accounts for bucketing only. -/
structure GroupedBuild (n : Nat) where
  buckets : ChildLists n
  layout : Layout buckets
  bucketWork : GroupedChildWork

/-- Share the one grouping result between the retained buckets and the
existing layout scan. The reference buckets occur only in proofs. -/
def buildGrouped (x : PackedStaticLayout.Input N) : GroupedBuild N :=
  let b := groupedChildLists x.root x.parent.read
  { buckets := b.1
    layout := ofBuckets x.root x.parent.read b.1
      (groupedChildLists_get x.root x.parent.read)
    bucketWork := b.2 }

theorem buildGrouped_buckets (x : PackedStaticLayout.Input N) :
    (buildGrouped x).buckets = bucketChildLists x.root x.parent.read :=
  groupedChildLists_eq_bucketChildLists x.root x.parent.read

theorem mem_buildGrouped_iff (x : PackedStaticLayout.Input N) (q c : Fin N) :
    c ∈ (buildGrouped x).buckets.get q ↔
      c ≠ x.root ∧ x.parent.read c = q :=
  mem_groupedChildLists_iff x.root x.parent.read q c

theorem buildGrouped_bucketWork (x : PackedStaticLayout.Input N) :
    (buildGrouped x).bucketWork = ⟨N, ⟨N, N - 1, N - 1, N - 1, N⟩⟩ :=
  groupedChildLists_work x.root x.parent.read

/-- Exact record order, including child order and local indices. -/
theorem buildGrouped_cells (x : PackedStaticLayout.Input N) :
    (buildGrouped x).layout.cells.toList = (build x).cells.toList := by
  rw [(buildGrouped x).layout.cells_exact, (build x).cells_exact,
    buildGrouped_buckets x]

theorem buildGrouped_directory (x : PackedStaticLayout.Input N) :
    (buildGrouped x).layout.directory.toList = (build x).directory.toList := by
  rw [(buildGrouped x).layout.directory_exact, (build x).directory_exact,
    buildGrouped_buckets x]

end PaperB.DenseQuotientRows

namespace PaperB.ForestLayout

open PaperB.LabelledQuotient
open EX51 EX51.Storage

variable {N : Nat}

/-- This is the list passed to the single `groupMap` call. -/
abbrev groupedChildInput (root : Fin N) : List (Fin N) :=
  (selectNonRootRev root (finElems N) [] 0).1

theorem groupedChildInput_length (root : Fin N) :
    (groupedChildInput root).length = N - 1 := by
  have h := filter_nonRoot_length root (finElems N)
    (nodup_finElems N) (mem_finElems root)
  rw [length_finElems N] at h
  have hl :
      ((finElems N).filter (fun u => decide (u ≠ root))).length = N - 1 := by
    omega
  simp only [groupedChildInput, selectNonRootRev_spec, List.append_nil,
    List.length_reverse, hl]

/--
Logical list cells and bucket slots, excluding fixed-size scalar state.
Use `reserve = 0` when the original enumeration is no longer retained,
or `reserve = N` to charge it separately throughout. The selected list
itself is already included in the grouping charges.
-/
def groupedChildListsPeak (n reserve : Nat) : Nat :=
  reserve + (n + 3 * (n - 1))

/-- Charge the completed enumeration, before filtering starts. This is
the size of the enumeration list, not a backend allocation bound. -/
theorem groupedChildLists_enumeration_space (reserve : Nat) :
    (finElems N).length = N ∧
      (finElems N).length ≤ groupedChildListsPeak N reserve := by
  rw [length_finElems N]
  unfold groupedChildListsPeak
  exact ⟨rfl, by omega⟩

/-- Actual recursive call boundaries of the private root selector. -/
inductive SelectNonRootAt (root : Fin N) :
    List (Fin N) → List (Fin N) → Nat → Prop where
  | start : SelectNonRootAt root (finElems N) [] 0
  | step {u : Fin N} {us acc : List (Fin N)} {visits : Nat} :
      SelectNonRootAt root (u :: us) acc visits →
      SelectNonRootAt root us (if u = root then acc else u :: acc) (visits + 1)

theorem selectNonRootAt_resume {root : Fin N}
    {unread acc : List (Fin N)} {visits : Nat}
    (atCall : SelectNonRootAt root unread acc visits) :
    selectNonRootRev root unread acc visits =
      selectNonRootRev root (finElems N) [] 0 := by
  induction atCall with
  | start => rfl
  | step _ ih => simpa only [selectNonRootRev] using ih

theorem selectNonRootAt_partition {root : Fin N}
    {unread acc : List (Fin N)} {visits : Nat}
    (atCall : SelectNonRootAt root unread acc visits) :
    unread.length + visits = N ∧ acc.length ≤ visits := by
  induction atCall with
  | start => simp [length_finElems]
  | step _ ih =>
      obtain ⟨hu, ha⟩ := ih
      constructor
      · simp only [List.length_cons] at hu
        omega
      · split <;> (try simp only [List.length_cons]) <;> omega

theorem groupedChildLists_filter_space {root : Fin N}
    {unread acc : List (Fin N)} {visits : Nat}
    (atCall : SelectNonRootAt root unread acc visits) (reserve : Nat) :
    unread.length + acc.length ≤ N ∧
      reserve + (unread.length + acc.length) ≤ reserve + N ∧
      reserve + (unread.length + acc.length) ≤ groupedChildListsPeak N reserve := by
  obtain ⟨hu, ha⟩ := selectNonRootAt_partition atCall
  unfold groupedChildListsPeak
  exact ⟨by omega, by omega, by omega⟩

/-- Includes the initial empty table (`ScatterAt.start`). Charge the
whole selected input, not just its unread suffix. -/
theorem groupedChildLists_scatter_space (root : Fin N) (parent : Fin N → Fin N)
    {unread : List (Fin N)} {s : Rows N (Fin N)} {r w : Nat}
    (atCall : ScatterAt parent id (groupedChildInput root) unread s r w)
    (reserve : Nat) :
    let live := reserve + (s.cells.size + rowMass s + (groupedChildInput root).length)
    s.cells.size = N ∧ rowMass s + unread.length = N - 1 ∧
      live ≤ reserve + (N + 2 * (N - 1)) ∧
      live ≤ groupedChildListsPeak N reserve := by
  obtain ⟨hs, hsplit, _, hspace⟩ := scatter_space atCall
  have hm := groupedChildInput_length root
  dsimp only
  unfold groupedChildListsPeak
  exact ⟨hs, by omega, by omega, by omega⟩

/-- At a finish boundary there is no additional active reversal charge. -/
theorem groupedChildLists_finish_space (root : Fin N) (parent : Fin N → Fin N)
    {s : Rows N (Fin N)} {t c : Nat} {h : t ≤ N}
    (atCall : FinishAt (scatterRows parent id (groupedChildInput root)) t h s c)
    (reserve : Nat) :
    let live := reserve + (s.cells.size + rowMass s + (groupedChildInput root).length)
    s.cells.size = N ∧ rowMass s = N - 1 ∧
      live = reserve + (N + 2 * (N - 1)) ∧
      live ≤ groupedChildListsPeak N reserve := by
  obtain ⟨hs, hmass, hspace⟩ := finish_space atCall
  have hm := groupedChildInput_length root
  dsimp only
  unfold groupedChildListsPeak
  exact ⟨hs, by omega, by omega, by omega⟩

/-- The old row is still in `s`. Charge both the unread suffix and the
accumulator on top of that table, even when the suffix shares cells. -/
theorem groupedChildLists_reversal_space (root : Fin N) (parent : Fin N → Fin N)
    {s : Rows N (Fin N)} {t c charge : Nat} {h : t + 1 ≤ N}
    {unread acc : List (Fin N)}
    (boundary : FinishAt (scatterRows parent id (groupedChildInput root))
      (t + 1) h s c)
    (active : ReverseAt (s.row ⟨t, h⟩) c unread acc charge)
    (reserve : Nat) :
    let live := reserve + (s.cells.size + rowMass s +
      (groupedChildInput root).length + (acc.length + unread.length))
    acc.length + unread.length = (s.row ⟨t, h⟩).length ∧
      live = reserve + (N + 2 * (N - 1) + (s.row ⟨t, h⟩).length) ∧
      live ≤ groupedChildListsPeak N reserve := by
  obtain ⟨hs, hmass, _⟩ := finish_space boundary
  obtain ⟨hsplit, hspace⟩ := reversal_space boundary active
  have hm := groupedChildInput_length root
  dsimp only
  unfold groupedChildListsPeak
  exact ⟨hsplit, by omega, by omega⟩

/-- The completed finish prefix has exactly the array retained by
`groupedChildLists`, and hence exactly the reference rows in order. -/
theorem groupedChildLists_finish_result (root : Fin N) (parent : Fin N → Fin N)
    {s : Rows N (Fin N)} {c : Nat} {h : 0 ≤ N}
    (done : FinishAt (scatterRows parent id (groupedChildInput root)) 0 h s c) :
    s.cells = (groupedChildLists root parent).1.rows ∧
      s.cells = (bucketChildLists root parent).rows := by
  have actual : s.cells = (groupedChildLists root parent).1.rows := by
    change s.cells = (EX51.groupMap parent id (groupedChildInput root)).1.cells
    rw [groupMap_phases, ← finish_resume done] <;> rfl
  exact ⟨actual, actual.trans
    (congrArg ChildLists.rows (groupedChildLists_eq_bucketChildLists root parent))⟩

/-- Add immutable storage to any of the phase bounds. The caller supplies
the recognized raw root's initialized size; neither it nor the input
parent array is charged as grouping workspace. -/
theorem groupedChildLists_add_immutable
    (rawRootInitialized : Nat) (parents : Array (Fin N)) (hp : parents.size = N)
    {live reserve : Nat} (hlive : live ≤ groupedChildListsPeak N reserve) :
    (rawRootInitialized + parents.size) + live ≤
      (rawRootInitialized + N) + groupedChildListsPeak N reserve := by
  rw [hp]
  exact Nat.add_le_add_left hlive _

end PaperB.ForestLayout
