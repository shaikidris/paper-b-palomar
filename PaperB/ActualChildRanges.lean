module

public import PaperB.PackedStaticLayout
public import PaperB.StaticChildLookup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open PaperB PaperB.LabelledQuotient PaperB.ForestLayout

/- Append after the DFS and layout lemmas, in their enclosing namespace. -/
namespace ExactOrderedChildIntervals

open PaperB.StaticChildLookup

variable {α β : Type}

/-- The specification-level sum of the lengths of the preceding subtrees. -/
def preceding (f : α → List β) (xs : List α) (i : Nat) : Nat :=
  ((xs.take i).map (fun c => (f c).length)).sum

private theorem flatMap_length_sum (f : α → List β) (xs : List α) :
    (xs.flatMap f).length = (xs.map (fun c => (f c).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_cons, ih]

private theorem preceding_succ (f : α → List β) (xs : List α)
    (i : Nat) (hi : i < xs.length) :
    preceding f xs (i + 1) = preceding f xs i + (f (xs[i]'hi)).length := by
  unfold preceding
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons,
            List.getElem_cons_succ, ih i hi', Nat.add_assoc]

private theorem take_full (xs : List α) : xs.take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.take_succ_cons, ih]

private theorem flatMap_split (f : α → List β) (xs : List α)
    (i : Nat) (hi : i < xs.length) :
    xs.flatMap f =
      (xs.take i).flatMap f ++ f (xs[i]'hi) ++
        (xs.drop (i + 1)).flatMap f := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      cases i with
      | zero => simp [List.flatMap_cons]
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simpa only [List.flatMap_cons, List.take_succ_cons,
            List.drop_succ_cons, List.getElem_cons_succ, List.append_assoc] using
            congrArg (fun ys => f x ++ ys) (ih i hi')

private theorem subtree_cons {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    dfsSubtree root parent depth u =
      u :: (bucketChildren root parent u).flatMap
        (dfsSubtree root parent depth) := by
  rw [dfsSubtree_unfold hTree u, concatMapList_eq_flatMap]

theorem child_entry {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N)
    (i : Nat) (hi : i < (bucketChildren root parent u).length) :
    entry root parent depth ((bucketChildren root parent u)[i]'hi) =
      entry root parent depth u + 1 +
        preceding (dfsSubtree root parent depth) (bucketChildren root parent u) i := by
  let xs := bucketChildren root parent u
  let f := dfsSubtree root parent depth
  change entry root parent depth (xs[i]'hi) =
    entry root parent depth u + 1 + preceding f xs i
  obtain ⟨pref, suff, hu⟩ := exists_split_dfsPreorder hTree u
  have hcons : f u = u :: xs.flatMap f := subtree_cons hTree u
  have hc : dfsPreorder root parent depth =
      (pref ++ (u :: (xs.take i).flatMap f)) ++
        f (xs[i]'hi) ++ ((xs.drop (i + 1)).flatMap f ++ suff) := by
    calc
      dfsPreorder root parent depth = pref ++ f u ++ suff := hu
      _ = _ := by
        rw [hcons, flatMap_split f xs i hi]
        simp [List.append_assoc]
  rw [entry_eq_length_of_dfsPreorder_split hTree hc,
      entry_eq_length_of_dfsPreorder_split hTree hu]
  simp [preceding, flatMap_length_sum, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

private theorem first_lt_length_iff {α : Type} [DecidableEq α]
    (x : α) (xs : List α) :
    firstOccurrence x xs < xs.length ↔ x ∈ xs := by
  induction xs with
  | nil => simp [firstOccurrence]
  | cons y ys ih =>
      by_cases h : x = y
      · simp [firstOccurrence, h]
      · rw [firstOccurrence, if_neg h]
        simp only [List.length_cons, List.mem_cons, h, false_or, ← ih]
        omega

private theorem first_append {α : Type} [DecidableEq α]
    (x : α) (xs ys : List α) :
    firstOccurrence x (xs ++ ys) =
      if x ∈ xs then firstOccurrence x xs
      else xs.length + firstOccurrence x ys := by
  induction xs with
  | nil => simp
  | cons y xs ih =>
      by_cases h : x = y
      · simp [firstOccurrence, h]
      · by_cases hm : x ∈ xs <;>
          simp [firstOccurrence, h, hm, ih, Nat.add_assoc,
            Nat.add_left_comm, Nat.add_comm]

private theorem first_segment {α : Type} [DecidableEq α]
    (x : α) (pref mid suff : List α)
    (hn : (pref ++ (mid ++ suff)).Nodup) :
    x ∈ mid ↔
      pref.length ≤ firstOccurrence x (pref ++ (mid ++ suff)) ∧
      firstOccurrence x (pref ++ (mid ++ suff)) < pref.length + mid.length := by
  rw [first_append]
  by_cases hp : x ∈ pref
  · rw [if_pos hp]
    have hlt := (first_lt_length_iff x pref).2 hp
    have hm : x ∉ mid := by
      intro hx
      exact (List.pairwise_append.mp hn).2.2 x hp x
        (List.mem_append.mpr (Or.inl hx)) rfl
    exact ⟨fun hx => (hm hx).elim, fun hx => (Nat.not_lt_of_ge hx.1 hlt).elim⟩
  · rw [if_neg hp, first_append]
    by_cases hm : x ∈ mid
    · rw [if_pos hm]
      have hlt := (first_lt_length_iff x mid).2 hm
      exact ⟨fun _ => by omega, fun _ => hm⟩
    · rw [if_neg hm]
      refine ⟨fun hx => (hm hx).elim, fun hx => ?_⟩
      have hlt := hx.2
      omega

/-- The ranks in a subtree are exactly its half-open DFS interval. -/
theorem subtree_interval_iff {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u v : Fin N) :
    v ∈ dfsSubtree root parent depth u ↔
      entry root parent depth u ≤ entry root parent depth v ∧
      entry root parent depth v <
        entry root parent depth u + (dfsSubtree root parent depth u).length := by
  obtain ⟨pref, suff, hs⟩ := exists_split_dfsPreorder hTree u
  have hs' : dfsPreorder root parent depth =
      pref ++ (dfsSubtree root parent depth u ++ suff) := by
    simpa only [List.append_assoc] using hs
  have hn := nodup_dfsPreorder hTree
  rw [hs'] at hn
  rw [entry_eq_length_of_dfsPreorder_split hTree hs]
  unfold entry
  rw [hs']
  exact first_segment v pref (dfsSubtree root parent depth u) suff hn

private def mkRecord (ent out : α → Nat) (id : α) : Child α :=
  ⟨id, ent id, out id⟩

/-- Fused list-to-array packing: one bucket visit, two endpoint reads, and
one push per child. There is no intermediate list or array of records. -/
def packList (xs : List α) (ent out : α → Nat) : Array (Child α) :=
  xs.foldl (fun a c => a.push (mkRecord ent out c)) #[]

private theorem fold_push_toList (f : α → β) (xs : List α) (acc : Array β) :
    (xs.foldl (fun a x => a.push (f x)) acc).toList =
      acc.toList ++ xs.map f := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      change (xs.foldl (fun a y => a.push (f y)) (acc.push (f x))).toList =
        acc.toList ++ (x :: xs).map f
      rw [ih]
      simp [List.append_assoc]

private theorem packList_toList (xs : List α) (ent out : α → Nat) :
    (packList xs ent out).toList = xs.map (mkRecord ent out) := by
  simpa [packList] using fold_push_toList (mkRecord ent out) xs #[]

@[simp] theorem packList_size (xs : List α) (ent out : α → Nat) :
    (packList xs ent out).size = xs.length := by
  simpa using congrArg List.length (packList_toList xs ent out)

private theorem list_get_congr {xs ys : List α} (h : xs = ys) (i : Nat)
    (hx : i < xs.length) (hy : i < ys.length) :
    xs[i]'hx = ys[i]'hy := by
  subst ys
  rfl

theorem packList_at (xs : List α) (ent out : α → Nat)
    (i : Fin (packList xs ent out).size) (hi : i.val < xs.length) :
    childAt (packList xs ent out) i =
      ⟨xs[i.val]'hi, ent (xs[i.val]'hi), out (xs[i.val]'hi)⟩ := by
  have hl : i.val < (packList xs ent out).toList.length := by
    simpa using i.isLt
  have hr : i.val < (xs.map (mkRecord ent out)).length := by
    simpa using hi
  simpa [childAt, mkRecord] using
    list_get_congr (packList_toList xs ent out) i.val hl hr

theorem packList_ids (xs : List α) (ent out : α → Nat) :
    (packList xs ent out).toList.map (fun c => c.id) = xs := by
  rw [packList_toList, List.map_map]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change x :: xs.map ((fun c : Child α => c.id) ∘ mkRecord ent out) = x :: xs
      rw [ih]

private theorem mem_iff_index {x : α} {xs : List α} :
    x ∈ xs ↔ ∃ (i : Nat) (hi : i < xs.length), xs[i]'hi = x := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with he | ht
        · exact ⟨0, by simp, he.symm⟩
        · obtain ⟨i, hi, he⟩ := ih.mp ht
          exact ⟨i + 1, by simpa using hi, he⟩
      · rintro ⟨i, hi, he⟩
        cases i with
        | zero => exact List.mem_cons.mpr (Or.inl he.symm)
        | succ i =>
            exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨i, by simpa using hi, he⟩))

/--
`f` and `e` are specification parameters, not inputs to the packing loop.
For the DFS instance, `v ≠ u ∧ v ∈ f u` is strict descent by
`mem_dfsSubtree_iff`.
-/
structure BucketSpec (xs : List α) (f : α → List α) (e : α → Nat)
    (u : α) (outU : Nat) (a : Array (Child α)) : Prop where
  size_eq : a.size = xs.length
  at_index : ∀ (i : Fin a.size) (hi : i.val < xs.length),
    let c := xs[i.val]'hi
    let b := e u + 1 + preceding f xs i.val
    childAt a i = ⟨c, b, b + (f c).length⟩
  valid : PaperB.StaticChildLookup.Valid a
  adjacent : ∀ i j : Fin a.size, i.val + 1 = j.val →
    (childAt a i).stop = (childAt a j).entry
  stops_strict : ∀ i j : Fin a.size, i.val < j.val →
    (childAt a i).stop < (childAt a j).stop
  parent_stop : outU = e u + 1 + (xs.map (fun c => (f c).length)).sum
  first_entry : ∀ i : Fin a.size, i.val = 0 →
    (childAt a i).entry = e u + 1
  last_stop : ∀ i : Fin a.size, i.val + 1 = a.size →
    (childAt a i).stop = outU
  interval_iff : ∀ (i : Fin a.size) (v : α),
    Contains (childAt a i) (e v) ↔ v ∈ f (childAt a i).id
  descendants : ∀ v : α, (v ≠ u ∧ v ∈ f u) ↔
    ∃ i : Fin a.size, Contains (childAt a i) (e v) ∧
      ∀ j : Fin a.size, Contains (childAt a j) (e v) → j = i

theorem bucket_correct {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N)
    (ent out : Fin N → Nat)
    (hEnt : ∀ v, ent v = entry root parent depth v)
    (hOut : ∀ v, out v =
      entry root parent depth v + (dfsSubtree root parent depth v).length) :
    BucketSpec (bucketChildren root parent u) (dfsSubtree root parent depth)
      (entry root parent depth) u (out u)
      (packList (bucketChildren root parent u) ent out) := by
  let xs := bucketChildren root parent u
  let f := dfsSubtree root parent depth
  let e := entry root parent depth
  let a := packList xs ent out
  let b (i : Nat) := e u + 1 + preceding f xs i
  change BucketSpec xs f e u (out u) a
  have hsize : a.size = xs.length := packList_size xs ent out
  have idx (i : Fin a.size) : i.val < xs.length := by
    simpa only [hsize] using i.isLt
  have hrec (i : Fin a.size) (hi : i.val < xs.length) :
      childAt a i = ⟨xs[i.val]'hi, b i.val, b i.val + (f (xs[i.val]'hi)).length⟩ := by
    have he : e (xs[i.val]'hi) = b i.val := child_entry hTree u i.val hi
    rw [packList_at xs ent out i hi, hEnt, hOut]
    change (⟨xs[i.val]'hi, e (xs[i.val]'hi),
      e (xs[i.val]'hi) + (f (xs[i.val]'hi)).length⟩ : Child (Fin N)) = _
    rw [he]
  have hstart (i : Fin a.size) : (childAt a i).entry = b i.val := by
    rw [hrec i (idx i)]
  have hnext (i : Fin a.size) : (childAt a i).stop = b (i.val + 1) := by
    rw [hrec i (idx i)]
    change b i.val + (f (xs[i.val]'(idx i))).length = b (i.val + 1)
    simp only [b, preceding_succ f xs i.val (idx i), Nat.add_assoc]
  have hne (i : Fin a.size) : (childAt a i).entry < (childAt a i).stop := by
    have hp : 0 < (f (xs[i.val]'(idx i))).length := by
      have hc := subtree_cons hTree (xs[i.val]'(idx i))
      change f (xs[i.val]'(idx i)) = _ at hc
      rw [hc]
      simp
    rw [hrec i (idx i)]
    change b i.val < b i.val + (f (xs[i.val]'(idx i))).length
    omega
  have hadj (i j : Fin a.size) (hij : i.val + 1 = j.val) :
      (childAt a i).stop = (childAt a j).entry := by
    rw [hnext i, hstart j, hij]
  have hv : PaperB.StaticChildLookup.Valid a :=
    valid_of_adjacent hne (fun i j hij => Nat.le_of_eq (hadj i j hij))
  have hcons : f u = u :: xs.flatMap f := subtree_cons hTree u
  have hout : out u = b xs.length := by
    rw [hOut]
    change e u + (f u).length = b xs.length
    rw [hcons]
    simp only [b, preceding, take_full, List.length_cons, flatMap_length_sum]
    omega
  have hmem (i : Fin a.size) (v : Fin N) :
      Contains (childAt a i) (e v) ↔ v ∈ f (childAt a i).id := by
    rw [packList_at xs ent out i (idx i)]
    change (ent (xs[i.val]'(idx i)) ≤ e v ∧ e v < out (xs[i.val]'(idx i))) ↔ _
    rw [hEnt, hOut]
    exact (subtree_interval_iff hTree (xs[i.val]'(idx i)) v).symm
  refine ⟨hsize, hrec, hv, hadj, ?_, ?_, ?_, ?_, hmem, ?_⟩
  · intro i j hij
    exact Nat.lt_of_le_of_lt (hv.2 i j hij) (hne j)
  · simpa only [b, preceding, take_full] using hout
  · intro i hi
    rw [hstart i, hi]
    simp [b, preceding]
  · intro i hi
    rw [hnext i, hout, hi, hsize]
  · intro v
    constructor
    · rintro ⟨hneU, hm⟩
      rw [hcons] at hm
      have ht : v ∈ xs.flatMap f := by
        rcases List.mem_cons.mp hm with he | ht
        · exact (hneU he).elim
        · exact ht
      obtain ⟨c, hc, hvc⟩ := List.mem_flatMap.mp ht
      obtain ⟨k, hk, hkc⟩ := mem_iff_index.mp hc
      let i : Fin a.size := ⟨k, by simpa only [hsize] using hk⟩
      have hid : (childAt a i).id = c := by
        rw [packList_at xs ent out i (idx i)]
        exact hkc
      have hi : Contains (childAt a i) (e v) := (hmem i v).2 (by rwa [hid])
      exact ⟨i, hi, fun j hj => contains_unique hv hj hi⟩
    · rintro ⟨i, hi, _⟩
      have hneU : v ≠ u := by
        intro he
        have hle := hi.1
        rw [hstart i, he] at hle
        dsimp only [b] at hle
        omega
      have hm := (hmem i v).1 hi
      rw [packList_at xs ent out i (idx i)] at hm
      refine ⟨hneU, ?_⟩
      rw [hcons]
      exact List.mem_cons.mpr (Or.inr (List.mem_flatMap.mpr
        ⟨xs[i.val]'(idx i), mem_iff_index.mpr ⟨i.val, idx i, rfl⟩, hm⟩))

/-- Runtime entry point for one bucket. Pass the completed arrays, not a
layout computation. The size proofs are erased. -/
def fromCompleted {N : Nat} (g : ChildLists N) (entries ends : Array Nat)
    (he : entries.size = N) (ho : ends.size = N) (u : Fin N) :
    Array (Child (Fin N)) :=
  packList (g.get u)
    (fun c => entries[c.val]'(by rw [he]; exact c.isLt))
    (fun c => ends[c.val]'(by rw [ho]; exact c.isLt))

theorem layout_bucket_intervals {N : Nat} (g : ChildLists N) (root : Fin N)
    (parent : Fin N → Fin N) (depth : Fin N → Nat)
    (hTree : ValidDepthTree root parent depth)
    (hBuckets : ∀ v, g.get v = bucketChildren root parent v) (u : Fin N) :
    let s := layout g root (2 * N)
    BucketSpec (bucketChildren root parent u) (dfsSubtree root parent depth)
      (entry root parent depth) u
      (s.ends[u.val]'(by rw [s.ends_size]; exact u.isLt))
      (fromCompleted g s.entries s.ends s.entries_size s.ends_size u) := by
  let s := layout g root (2 * N)
  let ent (v : Fin N) := s.entries[v.val]'(by rw [s.entries_size]; exact v.isLt)
  let out (v : Fin N) := s.ends[v.val]'(by rw [s.ends_size]; exact v.isLt)
  change BucketSpec (bucketChildren root parent u) (dfsSubtree root parent depth)
    (entry root parent depth) u (out u) (packList (g.get u) ent out)
  have h := (layout_bucket_correct g root parent depth hTree hBuckets).2.2
  rw [hBuckets u]
  exact bucket_correct hTree u ent out (fun v => (h v).1) (fun v => (h v).2)

/--
Across all buckets: exactly `N - 1` child visits, `2 * (N - 1)` endpoint
array reads, and `N - 1` emitted records. The ID projection in `emitted`
only expresses the output cardinality using `sumBucketLengths`; it is
not executed by the constructor. An outer pass over the buckets adds
one bucket access per vertex.
-/
theorem aggregate_counts {N : Nat} (g : ChildLists N) (root : Fin N)
    (parent : Fin N → Fin N)
    (hBuckets : ∀ v, g.get v = bucketChildren root parent v)
    (entries ends : Array Nat) (he : entries.size = N) (ho : ends.size = N) :
    let visits := sumBucketLengths (fun u => g.get u) (finElems N)
    let emitted := sumBucketLengths
      (fun u => (fromCompleted g entries ends he ho u).toList.map (fun c => c.id))
      (finElems N)
    (visits, 2 * visits, emitted) = (N - 1, 2 * (N - 1), N - 1) := by
  have hg : (fun u => g.get u) = bucketChildren root parent := funext hBuckets
  have hp :
      (fun u => (fromCompleted g entries ends he ho u).toList.map (fun c => c.id)) =
        bucketChildren root parent := by
    funext u
    unfold fromCompleted
    rw [packList_ids, hBuckets u]
  dsimp only
  rw [hg, hp, total_bucketChildren_edges root parent]

end ExactOrderedChildIntervals
