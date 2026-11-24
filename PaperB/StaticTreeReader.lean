module

public import PaperB.PackedStaticLayout
public import PaperB.StaticLinearHead
public import PaperB.ActualChildRanges

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.StaticTreeReader

open ForestLayout ForestHeavyPath LabelledQuotient StaticHeadSweep
open PackedStaticLayout (Input InputOK Built tabulate read_tabulate)
open StaticLinearHead

set_option maxHeartbeats 1000000

variable {N : Nat}

private def completedRow (b : Built N) (u : Fin N) :
    Array (StaticChildLookup.Child (Fin N)) :=
  ExactOrderedChildIntervals.fromCompleted b.buckets
    b.endpoints.entry.data b.endpoints.stop.data
    b.endpoints.entry.len b.endpoints.stop.len u

private def packedRow (b : Built N) (u : Fin N) :
    Array (StaticChildLookup.Child (Fin N)) :=
  StaticChildLookup.pack (b.buckets.get u).toArray
    b.endpoints.entry.read b.endpoints.stop.read

private theorem packList_eq_pack (xs : List (Fin N)) (ent out : Fin N → Nat) :
    ExactOrderedChildIntervals.packList xs ent out =
      StaticChildLookup.pack xs.toArray ent out := by
  apply Array.ext
  · simp [ExactOrderedChildIntervals.packList, StaticChildLookup.pack]
  · intro i hi hj
    have hxs : i < xs.length := by
      simpa only [ExactOrderedChildIntervals.packList_size] using hi
    have h := ExactOrderedChildIntervals.packList_at xs ent out ⟨i, hi⟩ hxs
    change (ExactOrderedChildIntervals.packList xs ent out)[i]'hi =
      ⟨xs[i]'hxs, ent (xs[i]'hxs), out (xs[i]'hxs)⟩ at h
    simpa [StaticChildLookup.pack] using h

private theorem completedRow_eq (b : Built N) (u : Fin N) :
    completedRow b u = packedRow b u := by
  unfold completedRow ExactOrderedChildIntervals.fromCompleted packedRow
  rw [packList_eq_pack] <;> rfl

private def tablesFrom (b : Built N) (s : StaticHeadSweep.State N) :
    EX16.Tables (Fin N) :=
  { root := b.packed.root
    parent := b.packed.parent.read
    depth := b.packed.depth.read
    heavy := b.packed.heavy.read
    head := s.heads.read
    size := b.packed.size.read }

/-- The input index and the three specification fields do not carry
runtime data. The head column is retained by the `tables.head` closure. -/
structure Reader (x : Input N) where
  layout : Built N
  tables : EX16.Tables (Fin N)
  ranges : Slots N (Array (StaticChildLookup.Child (Fin N)))
  input_ok : InputOK x
  layout_exact : layout = PackedStaticLayout.build x
  tables_exact : tables = StaticHeadSweep.tables layout.packed
  ranges_exact : ∀ u, ranges.read u = completedRow layout u

/-- One packed layout, one sweep of its actual entry column, and one
materialization of the child rows from its completed endpoint arrays. -/
def build (x : Input N) (ht : InputOK x) : Reader x :=
  let b := PackedStaticLayout.build x
  let s := sweepEntries b.packed b.endpoints.entry (entry_lt x ht)
  let rows := tabulate (completedRow b)
  { layout := b
    tables := tablesFrom b s
    ranges := rows
    input_ok := ht
    layout_exact := rfl
    tables_exact := by
      have hs : s = StaticHeadSweep.build b.packed := sweepEntries_eq x ht
      change tablesFrom b s = StaticHeadSweep.tables b.packed
      rw [hs] <;> rfl
    ranges_exact := read_tabulate (completedRow b) }

-- Ancestry mentions only the ordinary root and parent, not the layout,
-- the heavy choice, or the result of the head sweep.
private def ordinaryTables (x : Input N) : EX16.Tables (Fin N) :=
  { root := x.root
    parent := x.parent.read
    depth := x.depth.read
    heavy := fun _ => none
    head := id
    size := fun _ => 0 }

abbrev SemanticAncestor (x : Input N) (a v : Fin N) : Prop :=
  EX16.Anc (ordinaryTables x) a v

private theorem anc_transport {T U : EX16.Tables (Fin N)}
    (hr : T.root = U.root) (hp : T.parent = U.parent)
    {a v : Fin N} (h : EX16.Anc T a v) : EX16.Anc U a v := by
  induction h with
  | refl => exact EX16.Path.refl
  | @step w hn _ _ ih =>
      refine EX16.Path.step (b := w) ?_ True.intro ?_
      · simpa only [hr] using hn
      · simpa only [hp] using ih

private theorem anc_trans {T : EX16.Tables (Fin N)} {a b c : Fin N}
    (hab : EX16.Anc T a b) (hbc : EX16.Anc T b c) : EX16.Anc T a c := by
  induction hbc with
  | refl => exact hab
  | @step w hn _ _ ih =>
      exact EX16.Path.step (b := w) hn True.intro ih

private abbrev subtree (x : Input N) (a : Fin N) : List (Fin N) :=
  dfsSubtree x.root x.parent.read x.depth.read a

private abbrev kids (x : Input N) (a : Fin N) : List (Fin N) :=
  bucketChildren x.root x.parent.read a

private theorem mem_kids (x : Input N) (a c : Fin N) :
    c ∈ kids x a ↔ c ≠ x.root ∧ x.parent.read c = a := by
  change c ∈ bucketChildren x.root x.parent.read a ↔ _
  first
  | exact?
  | solve
    | simp [bucketChildren, and_comm, eq_comm]
  | solve
    | simp [bucketChildren, finElems, and_comm, eq_comm]
  | have h : c ∈ bucketChildren x.root x.parent.read a ↔
        x.parent.read c = a ∧ c ≠ x.root := by exact?
    exact h.trans and_comm

private theorem subtree_eq (x : Input N) (ht : InputOK x) (a : Fin N) :
    subtree x a = a :: (kids x a).flatMap (subtree x) := by
  have hTree : ValidDepthTree x.root x.parent.read x.depth.read := ht
  have hFlat (f : Fin N → List (Fin N)) (xs : List (Fin N)) :
      concatMapList f xs = xs.flatMap f := by
    induction xs with
    | nil => rfl
    | cons c cs ih =>
        simp only [concatMapList, List.flatMap_cons, ih]
  change dfsSubtree x.root x.parent.read x.depth.read a =
    a :: (kids x a).flatMap (dfsSubtree x.root x.parent.read x.depth.read)
  have h := dfsSubtree_unfold hTree a
  rw [hFlat] at h
  simpa [kids, bucketChildren, and_comm, eq_comm] using h

private theorem mem_subtree_self (x : Input N) (ht : InputOK x) (a : Fin N) :
    a ∈ subtree x a := by
  rw [subtree_eq x ht a]
  exact List.mem_cons.mpr (Or.inl rfl)

private theorem child_subtree_shorter (x : Input N) (ht : InputOK x)
    (a c : Fin N) (hc : c ∈ kids x a) :
    (subtree x c).length < (subtree x a).length := by
  have bound : ∀ xs : List (Fin N), c ∈ xs →
      (subtree x c).length ≤ (xs.flatMap (subtree x)).length := by
    intro xs
    induction xs with
    | nil => simp
    | cons d ds ih =>
        rw [List.mem_cons, List.flatMap_cons, List.length_append]
        rintro (rfl | hm)
        · omega
        · have hb := ih hm
          omega
  have hb := bound (kids x a) hc
  rw [subtree_eq x ht a, List.length_cons]
  omega

private theorem subtree_closed (x : Input N) (ht : InputOK x)
    (a p c : Fin N) (hp : p ∈ subtree x a) (hc : c ∈ kids x p) :
    c ∈ subtree x a := by
  rw [subtree_eq x ht a, List.mem_cons] at hp
  rw [subtree_eq x ht a, List.mem_cons]
  right
  apply List.mem_flatMap.mpr
  rcases hp with h | h
  · subst p
    exact ⟨c, hc, mem_subtree_self x ht c⟩
  · obtain ⟨d, hd, hpd⟩ := List.mem_flatMap.mp h
    exact ⟨d, hd, subtree_closed x ht d p c hpd hc⟩
termination_by (subtree x a).length
decreasing_by exact child_subtree_shorter x ht a d hd

private theorem ancestor_of_mem_subtree (x : Input N) (ht : InputOK x)
    (a v : Fin N) (h : v ∈ subtree x a) : SemanticAncestor x a v := by
  rw [subtree_eq x ht a, List.mem_cons] at h
  rcases h with he | hm
  · subst v
    exact .refl
  · obtain ⟨c, hc, hv⟩ := List.mem_flatMap.mp hm
    have hk := (mem_kids x a c).mp hc
    have hac : SemanticAncestor x a c := by
      refine EX16.Path.step hk.1 True.intro ?_
      change SemanticAncestor x a (x.parent.read c)
      rw [hk.2]
      exact EX16.Path.refl
    exact anc_trans hac (ancestor_of_mem_subtree x ht c v hv)
termination_by (subtree x a).length
decreasing_by exact child_subtree_shorter x ht a c hc

private theorem mem_subtree_of_ancestor (x : Input N) (ht : InputOK x)
    {a v : Fin N} (h : SemanticAncestor x a v) : v ∈ subtree x a := by
  induction h with
  | refl => exact mem_subtree_self x ht a
  | @step w hn _ _ ih =>
      exact subtree_closed x ht a (x.parent.read w) w ih
        ((mem_kids x (x.parent.read w) w).mpr ⟨hn, rfl⟩)

private theorem mem_subtree_iff_rank (x : Input N) (ht : InputOK x)
    (a v : Fin N) :
    v ∈ subtree x a ↔
      PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read a ≤
        PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read v ∧
      PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read v <
        PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read a +
          (subtree x a).length := by
  have hTree : ValidDepthTree x.root x.parent.read x.depth.read := ht
  first
  | exact ExactOrderedChildIntervals.subtree_interval_iff hTree a v
  | exact (mem_dfsSubtree_iff hTree a v).trans
      (PaperB.LabelledQuotient.isForestAncestor_iff_dfsIntervalContains hTree a v)

namespace Reader

variable {x : Input N}

/-- One read of the stored entry column. -/
def entry (r : Reader x) (v : Fin N) : Nat :=
  r.layout.endpoints.entry.read v

/-- One read of the stored exclusive-stop column. -/
def stop (r : Reader x) (v : Fin N) : Nat :=
  r.layout.endpoints.stop.read v

theorem entry_exact (r : Reader x) (v : Fin N) :
    r.entry v = PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read v := by
  unfold entry
  rw [r.layout_exact]
  exact PackedStaticLayout.entry_exact x r.input_ok v

theorem stop_exact (r : Reader x) (v : Fin N) :
    r.stop v =
      PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read v +
        (dfsSubtree x.root x.parent.read x.depth.read v).length := by
  unfold stop
  rw [r.layout_exact]
  exact PackedStaticLayout.stop_exact x r.input_ok v

theorem ancestor_iff_interval (r : Reader x) (a v : Fin N) :
    SemanticAncestor x a v ↔ r.entry a ≤ r.entry v ∧ r.entry v < r.stop a := by
  rw [r.entry_exact a, r.entry_exact v, r.stop_exact a]
  exact (⟨mem_subtree_of_ancestor x r.input_ok,
    ancestor_of_mem_subtree x r.input_ok a v⟩ :
      SemanticAncestor x a v ↔ v ∈ subtree x a).trans
    (mem_subtree_iff_rank x r.input_ok a v)

/-- The queried vertex's rank is read once, even if both tests need it. -/
def isAncestor (r : Reader x) (a v : Fin N) : Bool :=
  let k := r.entry v
  decide (r.entry a ≤ k) && decide (k < r.stop a)

theorem isAncestor_exact (r : Reader x) (a v : Fin N) :
    r.isAncestor a v = true ↔ SemanticAncestor x a v := by
  simpa [isAncestor] using (r.ancestor_iff_interval a v).symm

theorem valid (r : Reader x) : EX16.Valid r.tables := by
  rw [r.tables_exact, r.layout_exact]
  exact PackedStaticLayout.valid x r.input_ok

private theorem ancestor_tables (r : Reader x) (a v : Fin N) :
    EX16.Anc r.tables a v ↔ SemanticAncestor x a v := by
  have hr : r.tables.root = (ordinaryTables x).root := by
    rw [r.tables_exact, r.layout_exact] <;> rfl
  have hp : r.tables.parent = (ordinaryTables x).parent := by
    rw [r.tables_exact, r.layout_exact] <;> rfl
  exact ⟨anc_transport hr hp, anc_transport hr.symm hp.symm⟩

/-- The query uses the stored tables; `valid` contributes only a proof. -/
def lca (r : Reader x) (u v : Fin N) : EX16.Result r.tables u v :=
  EX16.lca r.valid u v

theorem lca_exact (r : Reader x) (u v a : Fin N) :
    (SemanticAncestor x a u ∧ SemanticAncestor x a v) ↔
      SemanticAncestor x a (r.lca u v).node :=
  (and_congr (r.ancestor_tables a u).symm
    (r.ancestor_tables a v).symm).trans
    (((r.lca u v).correct a).trans
      (r.ancestor_tables a (r.lca u v).node))

/-- One transition per charged jump, then one same-chain stop. -/
theorem lca_execution (r : Reader x) (u v : Fin N) :
    EX16.Execution r.tables u v (r.lca u v).node (r.lca u v).jumps :=
  (r.lca u v).trace

theorem lca_charge (r : Reader x) (u v : Fin N) :
    2 ^ (r.lca u v).jumps * (r.tables.size u * r.tables.size v) ≤
      r.tables.size r.tables.root * r.tables.size r.tables.root :=
  (r.lca u v).charge

theorem lca_pow_jumps_le (r : Reader x) (u v : Fin N) :
    2 ^ (r.lca u v).jumps ≤
      r.tables.size r.tables.root * r.tables.size r.tables.root :=
  EX16.Result.pow_jumps_le r.valid (r.lca u v)

private theorem ranges_valid (r : Reader x) (u : Fin N) :
    StaticChildLookup.Valid (r.ranges.read u) := by
  have validBucket {row : Array (StaticChildLookup.Child (Fin N))} {out : Nat}
      (hs : ExactOrderedChildIntervals.BucketSpec (kids x u) (subtree x)
        (PaperB.LabelledQuotient.entry x.root x.parent.read x.depth.read) u out row) :
      StaticChildLookup.Valid row := by
    first
    | exact hs.valid
    | exact hs.1
    | exact hs.2.1
    | exact hs.2.2.1
    | cases hs <;> assumption
  rw [r.ranges_exact, r.layout_exact]
  have hTree : ValidDepthTree x.root x.parent.read x.depth.read := r.input_ok
  first
  | exact validBucket (ExactOrderedChildIntervals.layout_bucket_intervals
      (PackedStaticLayout.build x).buckets x.root x.parent.read x.depth.read
      hTree (PackedStaticLayout.bucket_read x) u)
  | rw [completedRow_eq]
    unfold packedRow
    rw [PackedStaticLayout.bucket_read x u, ← packList_eq_pack]
    exact validBucket (ExactOrderedChildIntervals.bucket_correct hTree u
      (PackedStaticLayout.build x).endpoints.entry.read
      (PackedStaticLayout.build x).endpoints.stop.read
      (fun v => PackedStaticLayout.entry_exact x r.input_ok v)
      (fun v => PackedStaticLayout.stop_exact x r.input_ok v))

/-- One row access and one entry access before the measured search.
The charge counts record reads and, separately, rank comparisons. -/
def childMeasured (r : Reader x) (u v : Fin N) : Option (Fin N) × Nat :=
  let row := r.ranges.read u
  let k := r.entry v
  let hit := StaticChildLookup.lookupMeasured row k
  (hit.1.map (fun c => c.id), hit.2)

/-- The immediate child of `u` on the path to `v`, if one exists. -/
def child (r : Reader x) (u v : Fin N) : Option (Fin N) :=
  (r.childMeasured u v).1

theorem child_cost_le (r : Reader x) (u v : Fin N) :
    (r.childMeasured u v).2 ≤ Nat.log2 ((kids x u).length + 1) + 2 := by
  have h := StaticChildLookup.lookup_cost_le (r.ranges.read u) (r.entry v)
  have hs : (r.ranges.read u).size = (kids x u).length := by
    rw [r.ranges_exact, completedRow_eq, r.layout_exact]
    simp [packedRow, PackedStaticLayout.bucket_read]
  rw [hs] at h
  exact h

private theorem lookup_id_iff {a : Array (StaticChildLookup.Child (Fin N))}
    (ha : StaticChildLookup.Valid a) (k : Nat) (c : Fin N) :
    (StaticChildLookup.lookup a k).map (fun z => z.id) = some c ↔
      ∃ i : Fin a.size, (StaticChildLookup.childAt a i).id = c ∧
        StaticChildLookup.Contains (StaticChildLookup.childAt a i) k := by
  constructor
  · intro h
    cases he : StaticChildLookup.lookup a k with
    | none => simp [he] at h
    | some z =>
        have hz : z.id = c := by simpa [he] using h
        obtain ⟨i, hi, hk⟩ := (StaticChildLookup.lookup_some_iff ha k z).mp he
        exact ⟨i, (congrArg (fun w : StaticChildLookup.Child (Fin N) =>
          w.id) hi).trans hz, hk⟩
  · rintro ⟨i, hi, hk⟩
    rw [(StaticChildLookup.lookup_some_iff ha k _).mpr ⟨i, rfl, hk⟩]
    simp [hi]

private def rowRecord (b : Built N) (c : Fin N) :
    StaticChildLookup.Child (Fin N) :=
  ⟨c, b.endpoints.entry.read c, b.endpoints.stop.read c⟩

private theorem at_packedRow (b : Built N) (u : Fin N)
    (i : Fin (packedRow b u).size) :
    StaticChildLookup.childAt (packedRow b u) i =
      rowRecord b ((b.buckets.get u)[i.val]'(by
        simpa [packedRow] using i.isLt)) := by
  simp [StaticChildLookup.childAt, packedRow, StaticChildLookup.pack, rowRecord]

private theorem index_of_mem {α : Type} {z : α} {xs : List α} (h : z ∈ xs) :
    ∃ i : Nat, ∃ hi : i < xs.length, xs[i]'hi = z := by
  induction xs with
  | nil => simp at h
  | cons a as ih =>
      rcases List.mem_cons.mp h with h | h
      · exact ⟨0, by simp, h.symm⟩
      · obtain ⟨i, hi, he⟩ := ih h
        exact ⟨i + 1, by simpa using Nat.succ_lt_succ hi, he⟩

private theorem list_at_mem {α : Type} (xs : List α) (i : Nat)
    (hi : i < xs.length) : xs[i]'hi ∈ xs := by
  first
  | exact List.getElem_mem hi
  | exact List.getElem_mem
  | exact?

theorem child_some_iff (r : Reader x) (u v c : Fin N) :
    r.child u v = some c ↔
      c ≠ x.root ∧ x.parent.read c = u ∧ SemanticAncestor x c v := by
  have hrow : r.ranges.read u = packedRow r.layout u :=
    (r.ranges_exact u).trans (completedRow_eq r.layout u)
  have hids : r.layout.buckets.get u = kids x u := by
    rw [r.layout_exact]
    exact PackedStaticLayout.bucket_read x u
  have hv : StaticChildLookup.Valid (packedRow r.layout u) :=
    hrow ▸ r.ranges_valid u
  change (StaticChildLookup.lookup (r.ranges.read u) (r.entry v)).map
    (fun z => z.id) = some c ↔ _
  rw [hrow, lookup_id_iff hv]
  constructor
  · rintro ⟨i, hi, hk⟩
    rw [at_packedRow] at hi hk
    have hb : i.val < (r.layout.buckets.get u).length := by
      simpa [packedRow] using i.isLt
    change (r.layout.buckets.get u)[i.val]'hb = c at hi
    have hm := list_at_mem (r.layout.buckets.get u) i.val hb
    rw [hi, hids] at hm
    have hc := (mem_kids x u c).mp hm
    rw [hi] at hk
    change r.entry c ≤ r.entry v ∧ r.entry v < r.stop c at hk
    exact ⟨hc.1, hc.2, (r.ancestor_iff_interval c v).mpr hk⟩
  · rintro ⟨hn, hp, ha⟩
    have hm := (mem_kids x u c).mpr ⟨hn, hp⟩
    rw [← hids] at hm
    obtain ⟨j, hj, he⟩ := index_of_mem hm
    let i : Fin (packedRow r.layout u).size :=
      ⟨j, by simpa [packedRow] using hj⟩
    refine ⟨i, ?_, ?_⟩
    · rw [at_packedRow]
      exact he
    · rw [at_packedRow]
      change StaticChildLookup.Contains
        (rowRecord r.layout ((r.layout.buckets.get u)[j]'hj)) (r.entry v)
      rw [he]
      change r.entry c ≤ r.entry v ∧ r.entry v < r.stop c
      exact (r.ancestor_iff_interval c v).mp ha

theorem child_none_iff (r : Reader x) (u v : Fin N) :
    r.child u v = none ↔
      ¬ ∃ c, c ≠ x.root ∧ x.parent.read c = u ∧ SemanticAncestor x c v := by
  constructor
  · intro hn
    rintro ⟨c, hc⟩
    have hs := (r.child_some_iff u v c).mpr hc
    rw [hn] at hs
    cases hs
  · intro hn
    cases he : r.child u v with
    | none => rfl
    | some c => exact False.elim (hn ⟨c, (r.child_some_iff u v c).mp he⟩)

end Reader
end PaperB.StaticTreeReader
