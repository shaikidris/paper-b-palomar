module

public import PaperB.StaticGroupedTreeReader
public import PaperB.ForestLayoutTreeCost

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ForestLayout.LiveCells

open PaperB.LabelledQuotient

variable {N : Nat}

/-- Splitting the fuel splits the actual run, including runs that stop early. -/
theorem run_fuel_add (g : ChildLists N) (k l : Nat) (s : State N) :
    run g (k + l) s = run g l (run g k s) := by
  induction k generalizing s with
  | zero => simp only [Nat.zero_add, run]
  | succ k ih =>
    rw [Nat.succ_add]
    cases hs : s.stack with
    | nil =>
      cases l <;> simp only [run, hs]
    | cons cmd rest =>
      simpa only [run, hs] using ih (advance g s cmd rest)

/-- An exact full run cannot have stopped early at any of its fuel prefixes. -/
theorem exact_prefix (g : ChildLists N) (root : Fin N) (k fuel : Nat)
    (hk : k ≤ fuel) (hfull : (layout g root fuel).processed = fuel) :
    layout g root fuel = run g (fuel - k) (layout g root k) ∧
      (layout g root k).processed = k := by
  have hsplit : k + (fuel - k) = fuel :=
    (Nat.add_comm k (fuel - k)).trans (Nat.sub_add_cancel hk)
  have hcontinue :
      layout g root fuel = run g (fuel - k) (layout g root k) := by
    change run g fuel (initial root) =
      run g (fuel - k) (run g k (initial root))
    rw [← run_fuel_add, hsplit]
  have hsuffix := run_processed_le g (fuel - k) (layout g root k)
  rw [← hcontinue, hfull] at hsuffix
  have hprefix := layout_processed_le g root k
  change (layout g root k).processed ≤ k at hprefix
  exact ⟨hcontinue, by omega⟩

private theorem run_conserves (g : ChildLists N) (w : Fin N → Nat)
    (hw : ∀ v, w v = 2 + ((g.get v).map w).sum)
    (fuel : Nat) (s : State N) :
    stackPotential w (run g fuel s).stack + (run g fuel s).processed =
      stackPotential w s.stack + s.processed := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : s.stack with
    | nil => simp only [run, hs]
    | cons cmd rest =>
      simp only [run, hs]
      rw [ih (advance g s cmd rest), advance_processed]
      have hstep := advance_stackPotential g w hw s cmd rest
      omega

-- The tree-cost module keeps its weight private. This is the same proof-only
-- weight; the DFS still runs on the supplied rows.
private def treeWeight (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) (v : Fin N) : Nat :=
  2 * (dfsSubtree root parent depth v).length

private theorem concat_length {α β : Type} (f : α → List β) (xs : List α) :
    (concatMapList f xs).length = (xs.map (fun x => (f x).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [concatMapList, List.length_append, List.map_cons, List.sum_cons, ih]

private theorem sum_twice {α : Type} (f : α → Nat) (xs : List α) :
    (xs.map (fun x => 2 * f x)).sum = 2 * (xs.map f).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, Nat.mul_add]

private theorem treeWeight_eq {root : Fin N} {parent : Fin N → Fin N}
    {depth : Fin N → Nat} (inputValid : ValidDepthTree root parent depth)
    (v : Fin N) :
    treeWeight root parent depth v =
      2 + (((bucketChildLists root parent).get v).map
        (treeWeight root parent depth)).sum := by
  rw [bucketChildLists_get]
  change 2 * (dfsSubtree root parent depth v).length =
    2 + ((bucketChildren root parent v).map
      (fun c => 2 * (dfsSubtree root parent depth c).length)).sum
  have hlen :
      (dfsSubtree root parent depth v).length =
        ((bucketChildren root parent v).map
          (fun c => (dfsSubtree root parent depth c).length)).sum + 1 := by
    have h := congrArg (fun xs : List (Fin N) => xs.length)
      (dfsSubtree_unfold inputValid v)
    simpa only [List.length_cons, concat_length] using h
  rw [sum_twice (fun c => (dfsSubtree root parent depth c).length)
    (bucketChildren root parent v), hlen, Nat.mul_add, Nat.mul_one]
  exact Nat.add_comm _ _

private theorem twice_length_le_sum (w : Fin N → Nat)
    (hw : ∀ v, 2 ≤ w v) (xs : List (Fin N)) :
    2 * xs.length ≤ (xs.map w).sum := by
  induction xs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.length_cons, Nat.mul_add, Nat.mul_one, List.map_cons, List.sum_cons]
    rw [Nat.add_comm (2 * vs.length) 2]
    exact Nat.add_le_add (hw v) ih

/-- The right fold processes `done` before `front`. Its stack after the
suffix is exactly the stack returned by `pushChildren done tail`. -/
theorem pushChildren_split (front done : List (Fin N)) (tail : List (Command N)) :
    pushChildren (front ++ done) tail =
      let p := pushChildren done tail
      let q := pushChildren front p.1
      (q.1, q.2 + p.2) := by
  simp only [pushChildren_spec, List.map_append, List.append_assoc,
    List.length_append]

/-- Retained row slots and child cells, entry/stop slots, and pending commands.
This is a slot model, not a measurement of allocator or evaluator overhead. -/
def boundaryCells (g : ChildLists N) (childMass : Nat) (s : State N) : Nat :=
  g.rows.size + childMass + s.entries.size + s.ends.size + s.stack.length

structure PrefixLive (g : ChildLists N) (root : Fin N) (childMass k : Nat) : Prop where
  continuation : layout g root (2 * N) = run g (2 * N - k) (layout g root k)
  processed : (layout g root k).processed = k
  pending : (layout g root k).stack.length ≤ 2 * N
  arraySizes : (layout g root k).entries.size = N ∧
    (layout g root k).ends.size = N
  boundary : boundaryCells g childMass (layout g root k) ≤ 6 * N
  /-- Charge both the old pending stack and the partial new stack in full,
  without taking credit for a shared tail. Reserve one whole child-row
  length for the temporary fold spine. An exit has no child fold. -/
  enterFold : ∀ (v : Fin N) (rest : List (Command N)),
    (layout g root k).stack = .enter v :: rest →
    ∀ (front done : List (Fin N)), g.get v = front ++ done →
      let partialStack := (pushChildren done (.exit v :: rest)).1
      partialStack.length ≤ 2 * N ∧
        (g.get v).length ≤ N ∧
        boundaryCells g childMass (layout g root k) +
          partialStack.length + (g.get v).length ≤ 9 * N

/-- Template for actual prepared rows of any valid depth tree. The row-mass
bound is supplied by the producer of those rows. -/
theorem validTree_prefix {root : Fin N} {parent : Fin N → Fin N}
    {depth : Fin N → Nat} (inputValid : ValidDepthTree root parent depth)
    (g : ChildLists N) (hBuckets : g = bucketChildLists root parent)
    (childMass : Nat) (hMass : childMass ≤ N) (k : Nat) (hk : k ≤ 2 * N) :
    PrefixLive g root childMass k := by
  have hfull : (layout g root (2 * N)).processed = 2 * N := by
    rw [hBuckets]
    exact (layout_bucketChildren_exact inputValid).2
  obtain ⟨hcontinue, hprocessed⟩ := exact_prefix g root k (2 * N) hk hfull
  let w := treeWeight root parent depth
  have hw : ∀ v, w v = 2 + ((g.get v).map w).sum := by
    intro v
    rw [hBuckets]
    exact treeWeight_eq inputValid v
  have hroot : w root = 2 * N := by
    change 2 * (dfsPreorder root parent depth).length = 2 * N
    rw [length_dfsPreorder inputValid]
  have hstart : stackPotential w (initial root).stack = 2 * N := by
    change stackPotential w [Command.enter root] = 2 * N
    simpa only [stackPotential_cons, stackPotential_nil, commandPotential,
      Nat.add_zero] using hroot
  have hpot (j : Nat) : stackPotential w (layout g root j).stack ≤ 2 * N := by
    have h := run_conserves g w hw j (initial root)
    change stackPotential w (layout g root j).stack +
      (layout g root j).processed = stackPotential w (initial root).stack + 0 at h
    rw [hstart, Nat.add_zero] at h
    omega
  have hpending (j : Nat) : (layout g root j).stack.length ≤ 2 * N :=
    Nat.le_trans (length_le_stackPotential g w hw (layout g root j).stack) (hpot j)
  have hbase : boundaryCells g childMass (layout g root k) ≤ 6 * N := by
    unfold boundaryCells
    rw [g.rows_size, (layout g root k).entries_size, (layout g root k).ends_size]
    have hp := hpending k
    omega
  refine ⟨hcontinue, hprocessed, hpending k, layout_sizes g root k, hbase, ?_⟩
  intro v rest hs front done hcut
  have hv : w v ≤ 2 * N := by
    have hp := hpot k
    rw [hs] at hp
    simp only [stackPotential_cons, commandPotential] at hp
    omega
  have hrowWeight := hw v
  have hrowLength := twice_length_le_sum w (weight_ge_two g w hw) (g.get v)
  have hspine : (g.get v).length ≤ N := by omega
  have hnext :
      layout g root (k + 1) = advance g (layout g root k) (.enter v) rest := by
    calc
      layout g root (k + 1) = run g 1 (layout g root k) :=
        run_fuel_add g k 1 (initial root)
      _ = advance g (layout g root k) (.enter v) rest := by
        simp only [run, hs]
  have hnew := hpending (k + 1)
  rw [hnext, (advance_enter_spec g (layout g root k) v rest).1, hcut] at hnew
  simp only [List.map_append, List.length_append, List.length_map] at hnew
  have hpartial : (pushChildren done (.exit v :: rest)).1.length ≤ 2 * N := by
    simp only [pushChildren_spec, List.length_append, List.length_map]
    omega
  exact ⟨hpartial, hspine, by omega⟩

/-- Name the actual measured quantity in a producer's size certificate without
depending on the visibility of the producer's scan-length definition. -/
def measuredCells {actual expected : Nat} (_ : actual = expected) : Nat := actual

end PaperB.ForestLayout.LiveCells

namespace PaperB.StaticGroupedTreeReader

open PaperB.LabelledQuotient
open PaperB.ForestLayout
open PaperB.ForestLayout.LiveCells

/-- The grouped reader's actual DFS finishing run. The grouping contribution
is the prepared table at handoff (`N` row slots and `N - 1` child cells),
not the transient workspace of the grouping algorithm. The initial DFS
state and the final endpoint arrays are counted separately. At command
boundaries the bound is `6 * N`; during the active child fold it is `9 * N`.
Array slots are counted, not allocation or copying overhead. -/
theorem finish_dfs_liveCells {N : Nat} (x) (ht) :
    let b := (build x ht).layout
    let g : ChildLists N := b.buckets
    let childMass := measuredCells (buildLayout_childScanLength x)
    ∀ inputValid : ValidDepthTree x.root x.parent.read x.depth.read,
      childMass = N - 1 ∧
      g.rows.size = N ∧
      g.rows.size + childMass ≤ 2 * N ∧
      boundaryCells g childMass (initial x.root) ≤ 4 * N + 1 ∧
      (let s := layout g x.root (2 * N)
       s.stack = [] ∧ s.processed = 2 * N ∧
         b.endpoints.entry.data = s.entries ∧ b.endpoints.stop.data = s.ends) ∧
      b.endpoints.entry.data.size + b.endpoints.stop.data.size = 2 * N ∧
      ∀ k : Nat, k ≤ 2 * N → PrefixLive g x.root childMass k := by
  dsimp only
  intro inputValid
  let b := (build x ht).layout
  let g : ChildLists N := b.buckets
  let childMass := measuredCells (buildLayout_childScanLength x)
  have hmass : childMass = N - 1 := buildLayout_childScanLength x
  have hmass_le : childMass ≤ N := by omega
  have hgroup : g.rows.size + childMass ≤ 2 * N := by
    rw [g.rows_size]
    omega
  have hinit : boundaryCells g childMass (initial x.root) ≤ 4 * N + 1 := by
    have hstack : (initial x.root).stack.length = 1 := rfl
    unfold boundaryCells
    rw [(initial x.root).entries_size, (initial x.root).ends_size, hstack]
    omega
  have hfinish := finish_dfs x ht inputValid
  change (layout g x.root (2 * N)).stack = [] ∧
    (layout g x.root (2 * N)).processed = 2 * N ∧
    b.endpoints.entry.data = (layout g x.root (2 * N)).entries ∧
    b.endpoints.stop.data = (layout g x.root (2 * N)).ends at hfinish
  have houtput :
      b.endpoints.entry.data.size + b.endpoints.stop.data.size = 2 * N := by
    rw [hfinish.2.2.1, hfinish.2.2.2,
      (layout g x.root (2 * N)).entries_size, (layout g x.root (2 * N)).ends_size]
    omega
  have hBuckets : g = bucketChildLists x.root x.parent.read := by
    first
    | change (groupedChildLists x.root x.parent.read).1 =
        bucketChildLists x.root x.parent.read
      rw [groupedChildLists_eq_bucketChildLists]
    | change (buildLayout x).buckets = bucketChildLists x.root x.parent.read
      rw [buildLayout_eq] <;> rfl
  exact ⟨hmass, g.rows_size, hgroup, hinit, hfinish, houtput,
    fun k hk => validTree_prefix inputValid g hBuckets childMass hmass_le k hk⟩

end PaperB.StaticGroupedTreeReader
