module

public import PaperB.ForestLayoutRefine
public import PaperB.StaticHeadSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PackedStaticLayout

open StaticHeadSweep ForestLayout LabelledQuotient ForestHeavyPath

variable {N : Nat}

structure Input (N : Nat) where
  root : Fin N
  parent : Slots N (Fin N)
  depth : Slots N Nat

/-- `TreeOK` only inspects the root, parent, and depth fields. The other
fields here occur only in a proposition and are not built at runtime. -/
abbrev InputOK (x : Input N) : Prop :=
  StaticHeadSweep.TreeOK
    { root := x.root
      parent := x.parent
      depth := x.depth
      heavy := Slots.fill N none
      size := Slots.fill N 0 }

def tabulate {α : Type} (f : Fin N → α) : Slots N α :=
  ⟨Array.ofFn f, by simp only [Array.size_ofFn]⟩

@[simp] theorem read_tabulate {α : Type} (f : Fin N → α) (v : Fin N) :
    (tabulate f).read v = f v := by
  simp only [tabulate, Slots.read, Array.getElem_ofFn]

structure Endpoints (N : Nat) where
  entry : Slots N Nat
  stop : Slots N Nat

private def runLayout (g : ChildLists N) (root : Fin N) : Endpoints N :=
  let s := layout g root (2 * N)
  { entry := ⟨s.entries, s.entries_size⟩
    stop := ⟨s.ends, s.ends_size⟩ }

/-- Retained storage consists of the packed columns, the two endpoint
columns, and the array of child lists. Neither the layout stack nor a
preorder list is retained. -/
structure Built (N : Nat) where
  packed : Packed N
  endpoints : Endpoints N
  buckets : ChildLists N

/-- Bucket construction is preprocessing. Layout and heavy selection share
the same rows; a row lookup does not rerun bucket construction. -/
def build (x : Input N) : Built N :=
  let g := bucketChildLists x.root x.parent.read
  let e := runLayout g x.root
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

theorem bucket_read (x : Input N) (u : Fin N) :
    (build x).buckets.get u = bucketChildren x.root x.parent.read u :=
  bucketChildLists_get x.root x.parent.read u

private def layoutFacts (x : Input N) (ht : InputOK x) :=
  (layout_bucket_correct (build x).buckets x.root x.parent.read x.depth.read
    ht (bucket_read x)).2.2

/-- The packed entry read is the specification entry. The proposition is
inferred from `layout_bucket_correct`; the column itself is an array. -/
def entry_exact (x : Input N) (ht : InputOK x) (v : Fin N) :=
  Eq.trans
    (show (build x).endpoints.entry.read v = _ from rfl)
    (layoutFacts x ht v).1

/-- The packed stop read is the specification entry plus the DFS subtree
length, so stop is exclusive. -/
def stop_exact (x : Input N) (ht : InputOK x) (v : Fin N) :=
  Eq.trans
    (show (build x).endpoints.stop.read v = _ from rfl)
    (layoutFacts x ht v).2

theorem size_read (x : Input N) (v : Fin N) :
    (build x).packed.size.read v =
      (build x).endpoints.stop.read v - (build x).endpoints.entry.read v :=
  read_tabulate
    (fun u => (build x).endpoints.stop.read u -
      (build x).endpoints.entry.read u) v

private theorem interval_length (a n : Nat) : (a + n) - a = n := by
  omega

theorem sizes_ok (x : Input N) (ht : InputOK x) :
    StaticHeadSweep.SizesOK (build x).packed := by
  intro v
  rw [size_read, stop_exact x ht v, entry_exact x ht v]
  exact interval_length _ _

theorem heavy_read (x : Input N) (u : Fin N) :
    (build x).packed.heavy.read u =
      (ForestHeavyPath.scan (build x).packed.size.read
        ((build x).buckets.get u)).best.map (fun w => w.node) := by
  have htable : (build x).packed.heavy =
      tabulate (fun v : Fin N =>
        (ForestHeavyPath.scan (build x).packed.size.read
          ((build x).buckets.get v)).best.map (fun w => w.node)) := rfl
  rw [htable, read_tabulate]

/-- Equality with the specification preserves its tie-breaking rule, not
just maximality of the selected child. -/
theorem heavy_ok (x : Input N) : StaticHeadSweep.HeavyOK (build x).packed := by
  intro u
  rw [heavy_read, bucket_read] <;> rfl

theorem valid (x : Input N) (ht : InputOK x) :
    EX16.Valid (StaticHeadSweep.tables (build x).packed) :=
  StaticHeadSweep.valid (build x).packed ht (sizes_ok x ht) (heavy_ok x)

/-!
Optional positional adapter for interval-array consumers. Build this cache
once if needed: it allocates an outer array and a second representation of
the child rows, with one interval record per child. It preserves the exact
row order used by layout. The row equality below does not discharge any
additional sortedness or search invariant required by a lookup API.
-/

structure ChildInterval (N : Nat) where
  child : Fin N
  entry : Nat
  stop : Nat

def childInterval (b : Built N) (c : Fin N) : ChildInterval N :=
  ⟨c, b.endpoints.entry.read c, b.endpoints.stop.read c⟩

def cacheIntervals (b : Built N) : Slots N (Array (ChildInterval N)) :=
  tabulate fun u => ((b.buckets.get u).map (childInterval b)).toArray

theorem interval_row (b : Built N) (u : Fin N) :
    (cacheIntervals b).read u =
      ((b.buckets.get u).map (childInterval b)).toArray :=
  read_tabulate (fun v => ((b.buckets.get v).map (childInterval b)).toArray) u

theorem built_interval_row (x : Input N) (u : Fin N) :
    (cacheIntervals (build x)).read u =
      ((bucketChildren x.root x.parent.read u).map
        (childInterval (build x))).toArray := by
  rw [interval_row, bucket_read]

end PaperB.PackedStaticLayout
