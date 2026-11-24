module

public import PaperB.ForestLayoutTreeCost
public import PaperB.FastOriginalChildBuckets
public import PaperB.StaticTreeReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.StaticGroupedTreeReader

open ForestLayout ForestHeavyPath LabelledQuotient StaticHeadSweep
open PackedStaticLayout (Input InputOK Built Endpoints tabulate read_tabulate)

set_option maxHeartbeats 1000000

variable {N : Nat}

private theorem childLists_ext {g h : ChildLists N}
    (rowsEq : ∀ u, g.get u = h.get u) : g = h := by
  have e : g.rows = h.rows := by
    apply Array.ext
    · rw [g.rows_size, h.rows_size]
    · intro i hi _
      have hN : i < N := by simpa only [g.rows_size] using hi
      exact rowsEq ⟨i, hN⟩
  cases g with
  | mk a ha =>
    cases h with
    | mk b hb =>
      change a = b at e
      subst b
      rfl

private def layoutOn (x : Input N) (g : ChildLists N) : Built N :=
  let s := layout g x.root (2 * N)
  let e : Endpoints N :=
    { entry := ⟨s.entries, s.entries_size⟩
      stop := ⟨s.ends, s.ends_size⟩ }
  let sizes := tabulate fun v => e.stop.read v - e.entry.read v
  let heavy := tabulate fun u =>
    (ForestHeavyPath.scan sizes.read (g.get u)).best.map (fun w => w.node)
  { packed :=
      { root := x.root
        parent := x.parent
        depth := x.depth
        heavy := heavy
        size := sizes }
    endpoints := e
    buckets := g }

def buildLayout (x : Input N) : Built N :=
  layoutOn x (groupedChildLists x.root x.parent.read).1

theorem buildLayout_eq (x : Input N) :
    buildLayout x = PackedStaticLayout.build x := by
  have hg : (groupedChildLists x.root x.parent.read).1 =
      bucketChildLists x.root x.parent.read :=
    childLists_ext (groupedChildLists_get_eq_bucketChildLists
      x.root x.parent.read)
  unfold buildLayout
  rw [hg] <;> rfl

open StaticLinearHead

private def completedRowOn (b : Built N) (u : Fin N) :
    Array (StaticChildLookup.Child (Fin N)) :=
  ExactOrderedChildIntervals.fromCompleted b.buckets
    b.endpoints.entry.data b.endpoints.stop.data
    b.endpoints.entry.len b.endpoints.stop.len u

private def readerOn (x : Input N) (ht : InputOK x) (b : Built N)
    (hb : b = PackedStaticLayout.build x) : StaticTreeReader.Reader x :=
  let s := sweepEntries b.packed b.endpoints.entry (by
    subst b
    exact entry_lt x ht)
  let rows := tabulate (completedRowOn b)
  { layout := b
    tables :=
      { root := b.packed.root
        parent := b.packed.parent.read
        depth := b.packed.depth.read
        heavy := b.packed.heavy.read
        head := s.heads.read
        size := b.packed.size.read }
    ranges := rows
    input_ok := ht
    layout_exact := hb
    tables_exact := by
      have hs : s = StaticHeadSweep.build b.packed := by
        subst b
        exact sweepEntries_eq x ht
      rw [hs] <;> rfl
    ranges_exact := read_tabulate (completedRowOn b) }

private theorem readerOn_eq (x : Input N) (ht : InputOK x) (b : Built N)
    (hb : b = PackedStaticLayout.build x) :
    readerOn x ht b hb = StaticTreeReader.build x ht := by
  subst b
  rfl

def build (x : Input N) (ht : InputOK x) : StaticTreeReader.Reader x :=
  readerOn x ht (buildLayout x) (buildLayout_eq x)

theorem build_eq (x : Input N) (ht : InputOK x) :
    build x ht = StaticTreeReader.build x ht :=
  readerOn_eq x ht (buildLayout x) (buildLayout_eq x)

-- Add `import PaperB.ForestLayoutTreeCost` at the top of the file.
-- Insert this block before `end PaperB.StaticGroupedTreeReader`.

/-- Total list cells in the physical child rows, including empty rows in the
row domain but not in the cell count. This is a specification, not a build pass. -/
def childScanLength (g : ChildLists N) : Nat :=
  ((finElems N).map fun u => (g.get u).length).sum

private def filterLengths (p : Fin N → Fin N) (qs xs : List (Fin N)) : Nat :=
  (qs.map fun q => (xs.filter fun v => decide (p v = q)).length).sum

private theorem filterLengths_cons (p : Fin N → Fin N) (v : Fin N)
    (xs qs : List (Fin N)) (hn : qs.Pairwise (· ≠ ·)) :
    filterLengths p qs (v :: xs) =
      filterLengths p qs xs + (if p v ∈ qs then 1 else 0) := by
  induction qs with
  | nil => simp [filterLengths]
  | cons q qs ih =>
    obtain ⟨hd, ht⟩ := List.pairwise_cons.mp hn
    have hh := ih ht
    by_cases e : p v = q
    · subst q
      have hm : p v ∉ qs := fun h => hd _ h rfl
      simp [filterLengths, List.filter_cons, hm] at hh ⊢ <;> omega
    · simp [filterLengths, List.filter_cons, List.mem_cons, e] at hh ⊢ <;> omega

private theorem filterLengths_all (p : Fin N → Fin N) (xs : List (Fin N)) :
    filterLengths p (finElems N) xs = xs.length := by
  induction xs with
  | nil =>
    generalize finElems N = qs
    induction qs <;> simp_all [filterLengths]
  | cons v xs ih =>
    rw [filterLengths_cons p v xs _ (nodup_finElems N), ih,
      if_pos (mem_finElems (p v))]
    rfl

private theorem childScanLength_group (p : Fin N → Fin N) (xs : List (Fin N)) :
    childScanLength
      ⟨(EX51.groupMap p id xs).1.cells, (EX51.groupMap p id xs).1.size_eq⟩ =
      xs.length := by
  have h (u : Fin N) :
      (EX51.group p xs).1.row u = xs.filter (fun v => decide (p v = u)) := by
    rw [EX51.group_row] <;> simp [eq_comm]
  unfold childScanLength
  change ((finElems N).map fun u => ((EX51.group p xs).1.row u).length).sum =
    xs.length
  simp only [h]
  exact filterLengths_all p xs

private def groupedScatters : GroupedChildWork → Nat
  | ⟨_, ⟨_, k, _, _, _⟩⟩ => k

theorem buildLayout_childScanLength (x : Input N) :
    childScanLength (buildLayout x).buckets = N - 1 := by
  have h := congrArg groupedScatters (groupedChildLists_work x.root x.parent.read)
  unfold groupedChildLists at h
  dsimp only at h
  rw [EX51.groupMap_work] at h
  simp only [buildLayout, layoutOn, groupedChildLists, childScanLength_group]
  exact h

/-- Exact command count for the layout used by the grouped reader. The bucket
equality is used only in the proof; the runtime input is the grouped array. -/
theorem finish_dfs (x : Input N) (ht : InputOK x)
    (tree : ValidDepthTree x.root x.parent.read x.depth.read) :
    let b := (build x ht).layout
    let s := layout b.buckets x.root (2 * N)
    s.stack = [] ∧ s.processed = 2 * N ∧
      b.endpoints.entry.data = s.entries ∧ b.endpoints.stop.data = s.ends := by
  have h :
      let s := layout (groupedChildLists x.root x.parent.read).1 x.root (2 * N)
      s.stack = [] ∧ s.processed = 2 * N := by
    rw [groupedChildLists_eq_bucketChildLists]
    exact layout_bucketChildren_exact tree
  exact ⟨h.1, h.2, rfl, rfl⟩

/-- The heavy and range tabulations consume the same N physical rows, with
N-1 child cells per full pass. In the per-record slot model, charge one size
read per heavy candidate, and two endpoint reads and one output record per
completed child. These are scan lengths and slot charges, not evaluator steps. -/
theorem finish_rows (x : Input N) (ht : InputOK x) :
    let r := build x ht
    let b := r.layout
    b.buckets.rows.size = N ∧ childScanLength b.buckets = N - 1 ∧
    r.ranges.data.size = N ∧
    ∀ u : Fin N,
      b.packed.size.read u = b.endpoints.stop.read u - b.endpoints.entry.read u ∧
      b.packed.heavy.read u =
        (ForestHeavyPath.scan b.packed.size.read (b.buckets.get u)).best.map
          (fun w => w.node) ∧
      r.ranges.read u = ExactOrderedChildIntervals.fromCompleted b.buckets
        b.endpoints.entry.data b.endpoints.stop.data
        b.endpoints.entry.len b.endpoints.stop.len u := by
  refine ⟨(buildLayout x).buckets.rows_size, buildLayout_childScanLength x,
    (build x ht).ranges.len, ?_⟩
  intro u
  exact ⟨read_tabulate _ u, read_tabulate _ u, read_tabulate _ u⟩

private theorem finish_entry_lt (x : Input N) (ht : InputOK x) :
    ∀ v : Fin N, (buildLayout x).endpoints.entry.read v < N := by
  rw [buildLayout_eq]
  exact entry_lt x ht

/-- One entry-slot read and one inverse-slot write per scatter. The write
counter excludes fill; the inverse array and its list conversion each have N
cells/records. No separate DFS entry/stop write counter is inferred from the
endpoint array lengths. -/
theorem finish_inverse (x : Input N) (ht : InputOK x) :
    let b := (build x ht).layout
    let ok := finish_entry_lt x ht
    let inv := inverseSlots b.packed.root b.endpoints.entry ok
    inv.writes = N ∧ inv.slots.data.size = N ∧
      (inverseOrder b.packed.root b.endpoints.entry ok).length = N ∧
      ∀ u : Fin N, (build x ht).tables.head u =
        (sweepEntries b.packed b.endpoints.entry ok).heads.read u := by
  exact ⟨inverse_scatter_writes _ _ _, inverse_cells _ _ _,
    inverse_list_records _ _ _, fun _ => rfl⟩

-- Scope at the fast ordered reader call: N is the occupied packed-input count,
-- not a region capacity. `EX24.FinalDFS.nodeCount_le` thus gives the command
-- upper bound 2 * (H.vertexCount + 1). These estimates exclude packed-input
-- extraction, query processing, allocation/copying, and unmetered sweep work.

end PaperB.StaticGroupedTreeReader
