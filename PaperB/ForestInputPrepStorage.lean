module

public import PaperB.ForestPreparedBuild

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.EX24.InputPrepCheckpoint

open ForestIncomingRaw (Entry Prepared prepare row supplied length_supplied)
open ForestIncoming (Marks Rows RowResult Result scan sweep run)
open StaticHeadSweep (Slots)

-- Units, not bytes: one per array slot or list spine cell, two payload
-- fields per labelled occurrence, and one payload field per source/test
-- entry. A labelled entry stores the source and a reference to the
-- immutable arc carrying the original tail; it does not copy that arc.
-- `other` is a separate charge for the remaining immutable input and any
-- retained enumeration lists. The adjacency charge includes its outer
-- slots, list spines, and the head and original-tail fields.
def immutableUnits (H : LabelledQuotient) (other : Nat) : Nat :=
  other + H.adj.size + 3 * H.arcCount

def mass {n : Nat} {α : Type} (read : Fin n → List α) : Nat :=
  ((List.finRange n).map fun y => (read y).length).sum

private theorem mapSum_le {α : Type} (xs : List α) (f g : α → Nat)
    (h : ∀ x, f x ≤ g x) : (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    exact Nat.add_le_add (h x) ih

theorem mass_le {n : Nat} {α β : Type}
    (f : Fin n → List α) (g : Fin n → List β)
    (h : ∀ y, (f y).length ≤ (g y).length) : mass f ≤ mass g :=
  mapSum_le _ _ _ h

def labelMass (H : LabelledQuotient) (p : Prepared H) : Nat :=
  mass (row H p)

theorem labelMass_prepare (H : LabelledQuotient) :
    labelMass H (prepare H) = H.arcCount := by
  change ForestIncomingPrep.mapCalls H (prepare H) = H.arcCount
  rw [ForestIncomingPrep.mapCalls_prepare, length_supplied,
    ForestPreparedBuild.arcTotal_eq_arcCount]

private def labelArray {H : LabelledQuotient} (p : Prepared H) :
    Array (List (Entry H)) := by
  first
  | exact p.1.1
  | exact p.1.data
  | exact p.1.rows
  | exact p.1.arr

private theorem labelArray_size {H : LabelledQuotient} (p : Prepared H) :
    (labelArray p).size = H.vertexCount := by
  rcases p with ⟨r, w⟩
  first
  | exact r.2
  | (cases r <;> assumption)
  | (unfold labelArray; exact?)

private def slotArray {n : Nat} {α : Type} (s : Slots n α) : Array α := by
  first
  | exact s.1
  | exact s.data
  | exact s.arr

private theorem slotArray_size {n : Nat} {α : Type} (s : Slots n α) :
    (slotArray s).size = n := by
  first
  | exact s.2
  | (cases s <;> assumption)
  | (unfold slotArray; exact?)

-- The gather step is definitionally the step used by `supplied`.
private def gatherArc (H : LabelledQuotient) (u : Fin H.vertexCount)
    (xs : List (Entry H))
    (a : QuotientArc H.origVertexCount H.vertexCount) : List (Entry H) :=
  (u, a) :: xs

private def gatherRow (H : LabelledQuotient) (xs : List (Entry H))
    (u : Fin H.vertexCount) : List (Entry H) :=
  (H.outArcs u).foldl (gatherArc H u) xs

private theorem gatherArc_length (H : LabelledQuotient)
    (u : Fin H.vertexCount)
    (as : List (QuotientArc H.origVertexCount H.vertexCount))
    (xs : List (Entry H)) :
    (as.foldl (gatherArc H u) xs).length = xs.length + as.length := by
  induction as generalizing xs with
  | nil => simp
  | cons a as ih =>
    rw [List.foldl_cons, ih]
    simp only [gatherArc, List.length_cons]
    omega

private theorem gatherRow_length_mono (H : LabelledQuotient)
    (ys : List (Fin H.vertexCount)) (xs : List (Entry H)) :
    xs.length ≤ (ys.foldl (gatherRow H) xs).length := by
  induction ys generalizing xs with
  | nil => exact Nat.le_refl _
  | cons y ys ih =>
    rw [List.foldl_cons]
    apply Nat.le_trans (m := (gatherRow H xs y).length)
    · simp only [gatherRow, gatherArc_length] <;> omega
    · exact ih _

/-- An actual gather accumulator, including a stop within an adjacency row.
The append equalities are proof parameters, not lists copied by the build. -/
theorem gather_prefix (H : LabelledQuotient)
    (done later : List (Fin H.vertexCount)) (u : Fin H.vertexCount)
    (seen todo : List (QuotientArc H.origVertexCount H.vertexCount))
    (heads : done ++ u :: later = List.finRange H.vertexCount)
    (arcs : seen ++ todo = H.outArcs u) :
    let acc := seen.foldl (gatherArc H u) (done.foldl (gatherRow H) [])
    supplied H = later.foldl (gatherRow H) (todo.foldl (gatherArc H u) acc) ∧
    acc.length ≤ H.arcCount := by
  let acc := seen.foldl (gatherArc H u) (done.foldl (gatherRow H) [])
  have he : supplied H =
      later.foldl (gatherRow H) (todo.foldl (gatherArc H u) acc) := by
    change (List.finRange H.vertexCount).foldl (gatherRow H) [] = _
    rw [← heads, List.foldl_append, List.foldl_cons]
    change later.foldl (gatherRow H)
      ((H.outArcs u).foldl (gatherArc H u) (done.foldl (gatherRow H) [])) = _
    rw [← arcs, List.foldl_append]
  refine ⟨he, ?_⟩
  have hlen : (supplied H).length = H.arcCount :=
    (length_supplied H).trans (ForestPreparedBuild.arcTotal_eq_arcCount H)
  rw [he] at hlen
  have hb : acc.length ≤ (todo.foldl (gatherArc H u) acc).length := by
    exact Nat.le_trans (Nat.le_add_right _ _)
      (Nat.le_of_eq (gatherArc_length H u todo acc).symm)
  rw [← hlen]
  exact Nat.le_trans hb (gatherRow_length_mono H later _)

/-- The raw scatter hand-off, charging even the entire supplied list
alongside the returned rows. This does not account for EX51 scratch arrays
or claim a peak inside `groupMap`. -/
theorem raw_handoff_receipt (H : LabelledQuotient) :
    (labelArray (prepare H)).size +
      3 * labelMass H (prepare H) + 3 * (supplied H).length =
    H.vertexCount + 6 * H.arcCount := by
  rw [labelArray_size, labelMass_prepare, length_supplied,
    ForestPreparedBuild.arcTotal_eq_arcCount]
  omega

private def sourceStep (H : LabelledQuotient) (p : Prepared H)
    (s : Rows H.vertexCount) (y : Fin H.vertexCount) : Rows H.vertexCount :=
  s.write y ((row H p y).map Prod.fst)

def sourcePrefix (H : LabelledQuotient) (p : Prepared H)
    (ys : List (Fin H.vertexCount)) : Rows H.vertexCount :=
  ys.foldl (sourceStep H p) (Slots.fill H.vertexCount [])

theorem sources_continue (H : LabelledQuotient) (p : Prepared H)
    (done todo : List (Fin H.vertexCount))
    (split : done ++ todo = List.finRange H.vertexCount) :
    ForestIncomingPrep.sources H p =
      todo.foldl (sourceStep H p) (sourcePrefix H p done) := by
  change sourcePrefix H p (List.finRange H.vertexCount) = _
  rw [← split, sourcePrefix, List.foldl_append]
  rfl

private theorem sourceFold_read (H : LabelledQuotient) (p : Prepared H)
    (ys : List (Fin H.vertexCount)) (s : Rows H.vertexCount)
    (y : Fin H.vertexCount) :
    (ys.foldl (sourceStep H p) s).read y =
      if y ∈ ys then (row H p y).map Prod.fst else s.read y := by
  induction ys generalizing s with
  | nil => simp
  | cons z zs ih =>
    rw [List.foldl_cons, ih]
    by_cases h : y ∈ zs
    · have ht : y ∈ z :: zs := List.Mem.tail z h
      rw [ite_eq_left h, ite_eq_left ht]
    · by_cases e : y = z
      · subst y
        rw [ite_eq_right h, ite_eq_left (show z ∈ z :: zs from List.Mem.head _)]
        simp [sourceStep]
      · have hn : y ∉ z :: zs := fun hm => (List.mem_cons.mp hm).elim e h
        rw [ite_eq_right h, ite_eq_right hn]
        exact Slots.read_write_other s z y ((row H p z).map Prod.fst) e

theorem sourcePrefix_capacity (H : LabelledQuotient) (p : Prepared H)
    (ys : List (Fin H.vertexCount)) (y : Fin H.vertexCount) :
    ((sourcePrefix H p ys).read y).length ≤ (row H p y).length := by
  rw [sourcePrefix, sourceFold_read]
  by_cases h : y ∈ ys
  · simp [h]
  · simp [h, Slots.read, Slots.fill]

theorem source_prefix_receipt (H : LabelledQuotient)
    (ys : List (Fin H.vertexCount)) :
    let p := prepare H
    let s := sourcePrefix H p ys
    (labelArray p).size + 3 * labelMass H p +
      (slotArray s).size + 2 * mass s.read ≤
      2 * H.vertexCount + 5 * labelMass H p := by
  dsimp only
  have hm := mass_le _ _ (sourcePrefix_capacity H (prepare H) ys)
  change mass (sourcePrefix H (prepare H) ys).read ≤
    labelMass H (prepare H) at hm
  rw [labelArray_size, slotArray_size]
  omega

-- Exact continuations of the actual epoch loops. In particular, a scan
-- prefix keeps its stamps, reversed output accumulator, and visit counter.
theorem scan_append {n : Nat} (y : Fin n) (seen todo : List (Fin n))
    (a : Marks n) (out : List (Fin n)) (k : Nat) :
    scan y (seen ++ todo) a out k =
      let r := scan y seen a out k
      scan y todo r.marks r.row r.visits := by
  induction seen generalizing a out k with
  | nil => simp [scan]
  | cons u us ih =>
    by_cases h : a.read u = some y
    · simpa only [List.cons_append, scan, ite_eq_left h] using ih a out (k + 1)
    · simpa only [List.cons_append, scan, ite_eq_right h] using
        ih (a.write u (some y)) (u :: out) (k + 1)

theorem sweep_append {n : Nat} (s : Rows n) (done todo : List (Fin n))
    (a : Marks n) (out : Rows n) (k : Nat) :
    sweep s (done ++ todo) a out k =
      let r := sweep s done a out k
      sweep s todo r.marks r.rows r.visits := by
  induction done generalizing a out k with
  | nil => simp [sweep]
  | cons y ys ih =>
    let r := scan y (s.read y) a [] k
    simpa only [List.cons_append, sweep] using
      ih r.marks (out.write y r.row) r.visits

theorem run_continue {n : Nat} (s : Rows n)
    (done later : List (Fin n)) (y : Fin n)
    (seen todo : List (Fin n)) (split : seen ++ todo = s.read y) :
    run s (done ++ y :: later) =
      let b := run s done
      let r := scan y seen b.marks [] b.visits
      let t := scan y todo r.marks r.row r.visits
      sweep s later t.marks (b.rows.write y t.row) t.visits := by
  calc
    _ = (let b := run s done
         sweep s (y :: later) b.marks b.rows b.visits) :=
      sweep_append s done (y :: later) _ _ _
    _ = _ := by simp only [sweep, ← split, scan_append]

theorem scan_capacity {n : Nat} (y : Fin n) (todo : List (Fin n))
    (a : Marks n) (out : List (Fin n)) (k : Nat) :
    (scan y todo a out k).row.length ≤ out.length + todo.length := by
  induction todo generalizing a out k with
  | nil => simp [scan]
  | cons u us ih =>
    by_cases h : a.read u = some y
    · rw [scan, ite_eq_left h]
      have hb := ih a out (k + 1)
      simp only [List.length_cons]
      omega
    · rw [scan, ite_eq_right h]
      have hb := ih (a.write u (some y)) (u :: out) (k + 1)
      simp only [List.length_cons] at hb ⊢
      omega

private theorem sweep_capacity {n : Nat} (s : Rows n) (ys : List (Fin n))
    (a : Marks n) (out : Rows n) (k : Nat)
    (cap : ∀ y, (out.read y).length ≤ (s.read y).length) :
    (∀ y, ((sweep s ys a out k).rows.read y).length ≤ (s.read y).length) ∧
    (∀ y, y ∉ ys → (sweep s ys a out k).rows.read y = out.read y) := by
  induction ys generalizing a out k with
  | nil => exact ⟨cap, fun _ _ => rfl⟩
  | cons z zs ih =>
    let r := scan z (s.read z) a [] k
    have hr : r.row.length ≤ (s.read z).length := by
      simpa only [r, List.length_nil, Nat.zero_add] using
        scan_capacity z (s.read z) a [] k
    have hb : ∀ y, ((out.write z r.row).read y).length ≤ (s.read y).length := by
      intro y
      by_cases e : y = z
      · subst y
        simpa using hr
      · rw [Slots.read_write_other out z y r.row e]
        exact cap y
    obtain ⟨hc, he⟩ := ih r.marks (out.write z r.row) r.visits hb
    refine ⟨hc, ?_⟩
    intro y hy
    have hne : y ≠ z := fun e => hy (List.mem_cons.mpr (Or.inl e))
    have hn : y ∉ zs := fun hm => hy (List.Mem.tail z hm)
    change (sweep s zs r.marks (out.write z r.row) r.visits).rows.read y = _
    rw [he y hn, Slots.read_write_other out z y r.row hne]

theorem run_prefix_capacity {n : Nat} (s : Rows n) (done : List (Fin n)) :
    (∀ y, ((run s done).rows.read y).length ≤ (s.read y).length) ∧
    (∀ y, y ∉ done → (run s done).rows.read y = []) := by
  have h := sweep_capacity s done (Slots.fill n none) (Slots.fill n []) 0
    (fun y => by simp [Slots.read, Slots.fill])
  exact ⟨h.1, fun y hy => by simpa [run, Slots.read, Slots.fill] using h.2 y hy⟩

private theorem sum_bump {n : Nat} (zs : List (Fin n)) (nd : zs.Nodup)
    (f : Fin n → Nat) (y : Fin n) (k : Nat) :
    (zs.map (fun z => f z + (if z = y then k else 0))).sum =
      (zs.map f).sum + (if y ∈ zs then k else 0) := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hn := List.nodup_cons.mp nd
    simp only [List.map_cons, List.sum_cons]
    rw [ih hn.2]
    by_cases e : z = y
    · subst z
      simp [hn.1] <;> omega
    · simp [e, Ne.symm e] <;> omega

private theorem mass_write_empty {n : Nat} (s : Rows n) (y : Fin n)
    (out : List (Fin n)) (empty : s.read y = []) :
    mass (s.write y out).read = mass s.read + out.length := by
  have he : (fun z => ((s.write y out).read z).length) =
      (fun z => (s.read z).length + (if z = y then out.length else 0)) := by
    funext z
    by_cases e : z = y
    · subst z
      simp [empty]
    · simp [Slots.read_write_other s y z out e, e]
  have hn : (List.finRange n).Nodup := by
    first | exact List.nodup_finRange n | exact List.nodup_finRange | (simp; done)
  have hy : y ∈ List.finRange n := by simp
  unfold mass
  rw [he, sum_bump _ hn, ite_eq_left hy]

/-- Completed test rows and the unfinished test row share the same source
mass bound. The write in this proof is a specification device: the receipt
below charges only the existing output array and the active list. -/
theorem active_test_capacity {n : Nat} (s : Rows n) (done : List (Fin n))
    (y : Fin n) (fresh : y ∉ done) (seen todo : List (Fin n))
    (split : seen ++ todo = s.read y) :
    let b := run s done
    let r := scan y seen b.marks [] b.visits
    mass b.rows.read + r.row.length ≤ mass s.read := by
  let b := run s done
  let r := scan y seen b.marks [] b.visits
  have hb := run_prefix_capacity s done
  have hr : r.row.length ≤ seen.length := by
    simpa only [r, List.length_nil, Nat.zero_add] using
      scan_capacity y seen b.marks [] b.visits
  have hs : seen.length ≤ (s.read y).length := by
    rw [← split, List.length_append]
    omega
  have hc : mass (b.rows.write y r.row).read ≤ mass s.read := by
    apply mass_le
    intro z
    by_cases e : z = y
    · subst z
      simpa using Nat.le_trans hr hs
    · rw [Slots.read_write_other b.rows y z r.row e]
      exact hb.1 z
  rw [mass_write_empty b.rows y r.row (hb.2 y fresh)] at hc
  exact hc

def stampMass {n : Nat} (a : Marks n) : Nat :=
  ((List.finRange n).map fun u => if (a.read u).isSome then 1 else 0).sum

private theorem ones_sum {α : Type} (xs : List α) :
    (xs.map fun _ => (1 : Nat)).sum = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
    omega

theorem stampMass_le {n : Nat} (a : Marks n) : stampMass a ≤ n := by
  calc
    stampMass a ≤ ((List.finRange n).map fun _ => (1 : Nat)).sum :=
      mapSum_le _ _ _ (fun u => by split <;> omega)
    _ = n := by rw [ones_sum]; simp

/-- Rollup at a dedup loop state: labels, projected sources, the one stamp
array with its occupied payloads, and test rows with any active test list.
Scalar counters and proof fields are not row storage. -/
def liveUnits (H : LabelledQuotient) (p : Prepared H)
    (s out : Rows H.vertexCount) (a : Marks H.vertexCount)
    (active : List (Fin H.vertexCount)) : Nat :=
  (labelArray p).size + 3 * labelMass H p +
  (slotArray s).size + 2 * mass s.read +
  (slotArray a).size + stampMass a +
  (slotArray out).size + 2 * (mass out.read + active.length)

private theorem sourceMass_eq (H : LabelledQuotient) (p : Prepared H) :
    mass (ForestIncomingPrep.sources H p).read = labelMass H p := by
  simp only [mass, labelMass, ForestIncomingPrep.source_row, List.length_map]

private theorem liveUnits_le (H : LabelledQuotient) (p : Prepared H)
    (out : Rows H.vertexCount) (a : Marks H.vertexCount)
    (active : List (Fin H.vertexCount))
    (ht : mass out.read + active.length ≤ labelMass H p) :
    liveUnits H p (ForestIncomingPrep.sources H p) out a active ≤
      5 * H.vertexCount + 7 * labelMass H p := by
  have ha := stampMass_le a
  simp only [liveUnits, labelArray_size, slotArray_size, sourceMass_eq]
  omega

/-- In-row receipt on the actual projected input. `run_continue` identifies
this state with the append split of the real dedup run. Freshness is the
phase invariant supplied by processing each head of `finRange` once. -/
theorem dedup_prefix_receipt (H : LabelledQuotient)
    (done : List (Fin H.vertexCount)) (y : Fin H.vertexCount)
    (fresh : y ∉ done) (seen todo : List (Fin H.vertexCount))
    (split : seen ++ todo = (ForestIncomingPrep.sources H (prepare H)).read y) :
    let p := prepare H
    let s := ForestIncomingPrep.sources H p
    let b := run s done
    let r := scan y seen b.marks [] b.visits
    liveUnits H p s b.rows r.marks r.row ≤
      5 * H.vertexCount + 7 * H.arcCount := by
  have ht := active_test_capacity _ done y fresh seen todo split
  dsimp only at ht ⊢
  rw [sourceMass_eq] at ht
  rw [← labelMass_prepare H]
  exact liveUnits_le H (prepare H) _ _ _ ht

/-- Between rows, there is no active list. This also covers the last dedup
state, conservatively charging the stamps even at hand-off. -/
theorem dedup_row_boundary_receipt (H : LabelledQuotient)
    (done : List (Fin H.vertexCount)) :
    let p := prepare H
    let s := ForestIncomingPrep.sources H p
    let b := run s done
    liveUnits H p s b.rows b.marks [] ≤
      5 * H.vertexCount + 7 * H.arcCount := by
  let s := ForestIncomingPrep.sources H (prepare H)
  have ht : mass (run s done).rows.read ≤ mass s.read :=
    mass_le _ _ (run_prefix_capacity s done).1
  change _ ≤ 5 * H.vertexCount + 7 * H.arcCount
  rw [← labelMass_prepare H]
  apply liveUnits_le
  simpa only [s, sourceMass_eq, List.length_nil, Nat.add_zero] using ht

/-- The actual `build` output reads the dedup rows, not a second test array.
The immutable charge is additive and does not subsidize the rollup. -/
theorem build_receipt (H : LabelledQuotient) (cover : ForestIncomingPrep.Cover H)
    (other : Nat) :
    let b := ForestIncomingPrep.build H cover
    let d := run b.raw (List.finRange H.vertexCount)
    b.tests.row = d.rows.read ∧ b.visits = H.arcCount ∧
    immutableUnits H other + liveUnits H b.labels b.raw d.rows d.marks [] ≤
      immutableUnits H other + (5 * H.vertexCount + 7 * H.arcCount) := by
  refine ⟨rfl, ?_, ?_⟩
  · rw [ForestIncomingPrep.visits_supplied, length_supplied,
      ForestPreparedBuild.arcTotal_eq_arcCount]
  · exact Nat.add_le_add_left
      (dedup_row_boundary_receipt H (List.finRange H.vertexCount))
      (immutableUnits H other)

-- Scope: these are logical storage receipts at the stated construction
-- states, not a Lean runtime heap peak. In particular they do not bound
-- temporary EX51 scatter storage, transient list-map allocations, array
-- copy-on-write, or allocator capacity slack. No dictionary construction
-- or ordered sweep is included.

-- Insert in ForestInputPrepStorage.lean, immediately before
-- `end PaperB.EX24.InputPrepCheckpoint`.

open EX51.Storage (ScatterAt FinishAt ReverseAt scatterRows rowMass)

abbrev inputKey (H : LabelledQuotient) (e : ForestIncomingRaw.Entry H) :
    Fin H.vertexCount :=
  ForestIncomingRaw.arcHead e.2

theorem inputSuppliedCount (H : LabelledQuotient) :
    (supplied H).length = H.arcCount :=
  (length_supplied H).trans (ForestPreparedBuild.arcTotal_eq_arcCount H)

theorem inputPreparePhases (H : LabelledQuotient) :
    prepare H = EX51.groupMap (inputKey H) id (supplied H) := rfl

private theorem inputHeadsNodup (n : Nat) : (List.finRange n).Nodup := by
  first | exact List.nodup_finRange n | exact List.nodup_finRange | simp

-- Sum of independent reserves: gather, EX51, source conversion, dedup.
-- In particular, neither the immutable adjacency nor a shared list spine
-- is used to subsidize an allocation in another phase.
def inputPeak (H : LabelledQuotient) (other : Nat) : Nat :=
  immutableUnits H other + (10 * H.vertexCount + 27 * H.arcCount)

def InputFits (H : LabelledQuotient) (other units : Nat) : Prop :=
  immutableUnits H other + units ≤ inputPeak H other

private theorem inputFits_of_le (H : LabelledQuotient) (other : Nat)
    {units : Nat} (h : units ≤ 5 * H.vertexCount + 9 * H.arcCount) :
    InputFits H other units := by
  unfold InputFits inputPeak
  omega

theorem inputGatherPeak (H : LabelledQuotient) (other : Nat)
    (done later : List (Fin H.vertexCount)) (u : Fin H.vertexCount)
    (seen todo : List (QuotientArc H.origVertexCount H.vertexCount))
    (heads : done ++ u :: later = List.finRange H.vertexCount)
    (arcs : seen ++ todo = H.outArcs u) :
    let acc := seen.foldl (gatherArc H u) (done.foldl (gatherRow H) [])
    InputFits H other (H.vertexCount + 3 * acc.length) := by
  dsimp only
  have h := (gather_prefix H done later u seen todo heads arcs).2
  exact inputFits_of_le H other (by omega)

theorem inputScatterPeak (H : LabelledQuotient) (other : Nat)
    {rest : List (ForestIncomingRaw.Entry H)}
    {s : EX51.Rows H.vertexCount (ForestIncomingRaw.Entry H)} {r w : Nat}
    (v : ScatterAt (inputKey H) id (supplied H) rest s r w) :
    InputFits H other
      (s.cells.size + 3 * (rowMass s + (supplied H).length + rest.length)) := by
  obtain ⟨hs, hm, _, _⟩ := EX51.Storage.scatter_space v
  have hn := inputSuppliedCount H
  exact inputFits_of_le H other (by omega)

theorem inputFinishPeak (H : LabelledQuotient) (other : Nat)
    {s : EX51.Rows H.vertexCount (ForestIncomingRaw.Entry H)}
    {t c : Nat} {h : t ≤ H.vertexCount}
    (v : FinishAt (scatterRows (inputKey H) id (supplied H)) t h s c) :
    InputFits H other (s.cells.size + 3 * (rowMass s + (supplied H).length)) := by
  obtain ⟨hs, hm, _⟩ := EX51.Storage.finish_space v
  have hn := inputSuppliedCount H
  exact inputFits_of_le H other (by omega)

theorem inputReversePeak (H : LabelledQuotient) (other : Nat)
    {s : EX51.Rows H.vertexCount (ForestIncomingRaw.Entry H)}
    {t c charge : Nat} {h : t + 1 ≤ H.vertexCount}
    {unread acc : List (ForestIncomingRaw.Entry H)}
    (v : FinishAt (scatterRows (inputKey H) id (supplied H)) (t + 1) h s c)
    (a : ReverseAt (s.row ⟨t, h⟩) c unread acc charge) :
    InputFits H other
      (s.cells.size + 3 * (rowMass s + (supplied H).length +
        (acc.length + unread.length))) := by
  have hb := (EX51.Storage.reversal_space v a).2
  have hs := s.size_eq
  have hn := inputSuppliedCount H
  exact inputFits_of_le H other (by omega)

theorem inputRawHandoffPeak (H : LabelledQuotient) (other : Nat) :
    InputFits H other
      ((labelArray (prepare H)).size + 3 * labelMass H (prepare H) +
        3 * (supplied H).length) := by
  rw [raw_handoff_receipt]
  exact inputFits_of_le H other (by omega)

end PaperB.EX24.InputPrepCheckpoint
