module

public import PaperB.ForestIntervals
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace ForestHeavyPath

open PaperB.LabelledQuotient

/-! The selector takes a size lookup, not a DFS function. It caches the
winning score and keeps the first maximum in bucket order. `seen` is both
the next zero-based index and the number of size lookups performed. -/

structure Winner (α : Type) where
  node : α
  score : Nat
  index : Nat

structure Scan (α : Type) where
  seen : Nat
  comparisons : Nat
  best : Option (Winner α)

def scanStep {α : Type} (size : α → Nat) (s : Scan α) (x : α) : Scan α :=
  let k := size x
  let next : Winner α := ⟨x, k, s.seen⟩
  match s.best with
  | none => ⟨s.seen + 1, s.comparisons, some next⟩
  | some old =>
      ⟨s.seen + 1, s.comparisons + 1,
        some (if old.score < k then next else old)⟩

def scan {α : Type} (size : α → Nat) (xs : List α) : Scan α :=
  xs.foldl (scanStep size) ⟨0, 0, none⟩

structure FirstMax {α : Type} (size : α → Nat) (xs : List α)
    (w : Winner α) : Prop where
  index_lt : w.index < xs.length
  origin : xs[w.index]? = some w.node
  score_eq : w.score = size w.node
  maximal : ∀ x, x ∈ xs → size x ≤ w.score
  earlier : ∀ i x, i < w.index → xs[i]? = some x → size x < w.score

private theorem get_snoc_old {α : Type} (xs : List α) (x : α) (i : Nat)
    (hi : i < xs.length) : (xs ++ [x])[i]? = xs[i]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
      cases i with
      | zero => rfl
      | succ i =>
          change (xs ++ [x])[i]? = xs[i]?
          apply ih
          simp only [List.length_cons] at hi
          omega

private theorem get_snoc_last {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by
  induction xs with
  | nil => rfl
  | cons a xs ih => exact ih

private theorem mem_of_index {α : Type} {xs : List α} {i : Nat} {x : α}
    (h : xs[i]? = some x) : x ∈ xs := by
  induction xs generalizing i with
  | nil =>
      change none = some x at h
      cases h
  | cons a xs ih =>
      cases i with
      | zero =>
          change some a = some x at h
          have he : a = x := Option.some.inj h
          subst x
          simp
      | succ i =>
          change xs[i]? = some x at h
          exact List.mem_cons.mpr (Or.inr (ih h))

theorem FirstMax.mem {α : Type} {size : α → Nat} {xs : List α}
    {w : Winner α} (h : FirstMax size xs w) : w.node ∈ xs :=
  mem_of_index h.origin

theorem FirstMax.first_on_ties {α : Type} {size : α → Nat} {xs : List α}
    {w : Winner α} (h : FirstMax size xs w) {i : Nat} {x : α}
    (hi : xs[i]? = some x) (he : size x = w.score) : w.index ≤ i := by
  by_cases hlt : i < w.index
  · have hs := h.earlier i x hlt hi
    omega
  · omega

private theorem firstMax_single {α : Type} (size : α → Nat) (x : α) :
    FirstMax size [x] ⟨x, size x, 0⟩ := by
  refine ⟨by simp, rfl, rfl, ?_, ?_⟩
  · intro y hy
    have he : y = x := by simpa using hy
    subst y
    exact Nat.le_refl _
  · intro i y hi hy
    change i < 0 at hi
    omega

private theorem firstMax_replace {α : Type} {size : α → Nat}
    {xs : List α} {w : Winner α} (h : FirstMax size xs w)
    (x : α) (hlt : w.score < size x) :
    FirstMax size (xs ++ [x]) ⟨x, size x, xs.length⟩ := by
  refine ⟨by simp, get_snoc_last xs x, rfl, ?_, ?_⟩
  · intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · have hle := h.maximal y hy
      change size y ≤ size x
      omega
    · subst y
      exact Nat.le_refl _
  · intro i y hi hy
    change i < xs.length at hi
    rw [get_snoc_old xs x i hi] at hy
    have hle := h.maximal y (mem_of_index hy)
    change size y < size x
    omega

private theorem firstMax_keep {α : Type} {size : α → Nat}
    {xs : List α} {w : Winner α} (h : FirstMax size xs w)
    (x : α) (hle : size x ≤ w.score) : FirstMax size (xs ++ [x]) w := by
  refine ⟨?_, (get_snoc_old xs x w.index h.index_lt).trans h.origin,
    h.score_eq, ?_, ?_⟩
  · have hi := h.index_lt
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
    omega
  · intro y hy
    simp only [List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | hy
    · exact h.maximal y hy
    · subst y
      exact hle
  · intro i y hi hy
    have hi' : i < xs.length := Nat.lt_trans hi h.index_lt
    rw [get_snoc_old xs x i hi'] at hy
    exact h.earlier i y hi hy

private def Good {α : Type} (size : α → Nat) (xs : List α) (s : Scan α) :
    Prop :=
  s.seen = xs.length ∧ s.comparisons = xs.length - 1 ∧
    match s.best with
    | none => xs = []
    | some w => FirstMax size xs w

private theorem good_step {α : Type} (size : α → Nat) (xs : List α)
    (s : Scan α) (x : α) (hg : Good size xs s) :
    Good size (xs ++ [x]) (scanStep size s x) := by
  unfold Good at hg
  rcases hg with ⟨hseen, hcmp, hbest⟩
  cases hb : s.best with
  | none =>
      have he : xs = [] := by simpa only [hb] using hbest
      subst xs
      have hzero : s.seen = 0 := hseen
      have hczero : s.comparisons = 0 := hcmp
      have hs : scanStep size s x = ⟨1, 0, some ⟨x, size x, 0⟩⟩ := by
        simp [scanStep, hb, hzero, hczero]
      rw [hs]
      exact ⟨rfl, rfl, firstMax_single size x⟩
  | some w =>
      have hw : FirstMax size xs w := by simpa only [hb] using hbest
      have hs : scanStep size s x =
          ⟨xs.length + 1, s.comparisons + 1,
            some (if w.score < size x then ⟨x, size x, xs.length⟩ else w)⟩ := by
        simp [scanStep, hb, hseen]
      rw [hs]
      unfold Good
      refine ⟨by simp, ?_, ?_⟩
      · change s.comparisons + 1 = (xs ++ [x]).length - 1
        have hi := hw.index_lt
        simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
        omega
      · change FirstMax size (xs ++ [x])
          (if w.score < size x then ⟨x, size x, xs.length⟩ else w)
        by_cases hlt : w.score < size x
        · rw [ite_eq_left hlt]
          exact firstMax_replace hw x hlt
        · rw [ite_eq_right hlt]
          exact firstMax_keep hw x (by omega)

private theorem good_fold {α : Type} (size : α → Nat) (rest : List α) :
    ∀ (xs : List α) (s : Scan α), Good size xs s →
      Good size (xs ++ rest) (rest.foldl (scanStep size) s) := by
  induction rest with
  | nil =>
      intro xs s hs
      change Good size (xs ++ []) s
      simpa only [List.append_nil] using hs
  | cons x rest ih =>
      intro xs s hs
      have hh := ih (xs ++ [x]) (scanStep size s x) (good_step size xs s x hs)
      rw [List.append_assoc] at hh
      exact hh

private theorem scan_good {α : Type} (size : α → Nat) (xs : List α) :
    Good size xs (scan size xs) := by
  have hinit : Good size [] (⟨0, 0, none⟩ : Scan α) := ⟨rfl, rfl, rfl⟩
  have h := good_fold size xs [] ⟨0, 0, none⟩ hinit
  simpa only [List.nil_append, scan] using h

theorem scan_counts {α : Type} (size : α → Nat) (xs : List α) :
    (scan size xs).seen = xs.length ∧
    (scan size xs).comparisons = xs.length - 1 := by
  have h := scan_good size xs
  unfold Good at h
  exact ⟨h.1, h.2.1⟩

theorem scan_best_spec {α : Type} (size : α → Nat) (xs : List α) :
    match (scan size xs).best with
    | none => xs = []
    | some w => FirstMax size xs w := by
  have h := scan_good size xs
  unfold Good at h
  exact h.2.2

def heavyScan {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (size : Fin N → Nat) (u : Fin N) : Scan (Fin N) :=
  scan size (bucketChildren root parent u)

def heavyChild {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (size : Fin N → Nat) (u : Fin N) : Option (Fin N) :=
  (heavyScan root parent size u).best.map Winner.node

theorem heavyScan_counts {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (size : Fin N → Nat) (u : Fin N) :
    (heavyScan root parent size u).seen = (bucketChildren root parent u).length ∧
    (heavyScan root parent size u).comparisons =
      (bucketChildren root parent u).length - 1 :=
  scan_counts size (bucketChildren root parent u)

theorem heavyScan_best_spec {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (size : Fin N → Nat) (u : Fin N) :
    match (heavyScan root parent size u).best with
    | none => bucketChildren root parent u = []
    | some w => FirstMax size (bucketChildren root parent u) w := by
  unfold heavyScan
  change (match (scan size (bucketChildren root parent u)).best with
    | none => bucketChildren root parent u = []
    | some w => FirstMax size (bucketChildren root parent u) w)
  cases h : (scan size (bucketChildren root parent u)).best with
  | none => simpa only [h] using (scan_best_spec size (bucketChildren root parent u))
  | some w => simpa only [h] using (scan_best_spec size (bucketChildren root parent u))

def sumBy {α : Type} (f : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => f x + sumBy f xs

/-- The lookup total is `N - 1` on the full vertex enumeration by
`total_bucketChildren_edges`. The comparison total omits one per nonempty
bucket. -/
theorem heavyScan_total_counts {N : Nat} (root : Fin N)
    (parent : Fin N → Fin N) (size : Fin N → Nat) (qs : List (Fin N)) :
    sumBy (fun u => (heavyScan root parent size u).seen) qs =
        sumBucketLengths (bucketChildren root parent) qs ∧
    sumBy (fun u => (heavyScan root parent size u).comparisons) qs =
        sumBy (fun u => (bucketChildren root parent u).length - 1) qs := by
  induction qs with
  | nil => exact ⟨rfl, rfl⟩
  | cons u qs ih =>
      have hc := heavyScan_counts root parent size u
      constructor
      · simp only [sumBy, sumBucketLengths, hc.1, ih.1]
      · simp only [sumBy, hc.2, ih.2]

theorem heavyChild_origin {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {size : Fin N → Nat} {u v : Fin N}
    (h : heavyChild root parent size u = some v) :
    ∃ w, (heavyScan root parent size u).best = some w ∧
      w.node = v ∧ FirstMax size (bucketChildren root parent u) w := by
  have hs := heavyScan_best_spec root parent size u
  cases hb : (heavyScan root parent size u).best with
  | none => simp [heavyChild, hb] at h
  | some w =>
      have he : w.node = v := by simpa [heavyChild, hb] using h
      have hw : FirstMax size (bucketChildren root parent u) w := by
        simpa only [hb] using hs
      exact ⟨w, rfl, he, hw⟩

theorem heavyChild_mem {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {size : Fin N → Nat} {u v : Fin N}
    (h : heavyChild root parent size u = some v) :
    v ∈ bucketChildren root parent u := by
  obtain ⟨w, _, he, hw⟩ := heavyChild_origin h
  simpa only [he] using hw.mem

theorem heavyChild_maximal {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {size : Fin N → Nat} {u v c : Fin N}
    (h : heavyChild root parent size u = some v)
    (hc : c ∈ bucketChildren root parent u) : size c ≤ size v := by
  obtain ⟨w, _, he, hw⟩ := heavyChild_origin h
  simpa only [hw.score_eq, he] using hw.maximal c hc

/-! DFS blocks. The length argument counts two distinct occurrences of
child blocks in the concatenation. The depth/climb argument separately
shows that the two blocks have no vertex in common. -/

def subtreeSize {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) (u : Fin N) : Nat :=
  (dfsSubtree root parent depth u).length

private theorem mem_concat_blocks {N : Nat} (f : Fin N → List (Fin N))
    (x : Fin N) (xs : List (Fin N)) :
    x ∈ concatMapList f xs ↔ ∃ c, c ∈ xs ∧ x ∈ f c := by
  induction xs with
  | nil => simp [concatMapList]
  | cons a xs ih =>
      simp only [concatMapList, List.mem_append, ih, List.mem_cons]
      constructor
      · intro h
        rcases h with ha | ⟨c, hc, hx⟩
        · exact ⟨a, Or.inl rfl, ha⟩
        · exact ⟨c, Or.inr hc, hx⟩
      · rintro ⟨c, hc, hx⟩
        rcases hc with he | hc
        · subst c
          exact Or.inl hx
        · exact Or.inr ⟨c, hc, hx⟩

private theorem one_block_le {N : Nat} (f : Fin N → List (Fin N))
    (xs : List (Fin N)) (a : Fin N) (ha : a ∈ xs) :
    (f a).length ≤ (concatMapList f xs).length := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
      simp only [concatMapList, List.length_append]
      rcases List.mem_cons.mp ha with he | ha'
      · subst a
        omega
      · have h := ih ha'
        omega

private theorem two_blocks_le {N : Nat} (f : Fin N → List (Fin N))
    (xs : List (Fin N)) (a b : Fin N) (ha : a ∈ xs) (hb : b ∈ xs)
    (hab : a ≠ b) :
    (f a).length + (f b).length ≤ (concatMapList f xs).length := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
      simp only [concatMapList, List.length_append]
      rcases List.mem_cons.mp ha with hea | ha'
      · subst a
        rcases List.mem_cons.mp hb with heb | hb'
        · subst b
          exact (hab rfl).elim
        · have h := one_block_le f xs b hb'
          omega
      · rcases List.mem_cons.mp hb with heb | hb'
        · subst b
          have h := one_block_le f xs a ha'
          omega
        · have h := ih ha' hb'
          omega

private def climb {N : Nat} (parent : Fin N → Fin N) : Nat → Fin N → Fin N
  | 0, x => x
  | k + 1, x => parent (climb parent k x)

section Tree

variable {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
  {depth : Fin N → Nat}

theorem subtreeSize_pos (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    0 < subtreeSize root parent depth u := by
  unfold subtreeSize
  rw [dfsSubtree_unfold hTree u]
  simp

theorem child_size_lt (hTree : ValidDepthTree root parent depth)
    {u c : Fin N} (hc : c ∈ bucketChildren root parent u) :
    subtreeSize root parent depth c < subtreeSize root parent depth u := by
  have h := one_block_le (dfsSubtree root parent depth) _ c hc
  unfold subtreeSize
  rw [dfsSubtree_unfold hTree u, List.length_cons]
  omega

theorem child_dfs_mem_parent (hTree : ValidDepthTree root parent depth)
    {u c x : Fin N} (hc : c ∈ bucketChildren root parent u)
    (hx : x ∈ dfsSubtree root parent depth c) :
    x ∈ dfsSubtree root parent depth u := by
  rw [dfsSubtree_unfold hTree u, List.mem_cons]
  exact Or.inr ((mem_concat_blocks (dfsSubtree root parent depth) x _).mpr
    ⟨c, hc, hx⟩)

private theorem dfs_climb (hTree : ValidDepthTree root parent depth) :
    ∀ (m : Nat) (u x : Fin N),
      subtreeSize root parent depth u ≤ m →
      x ∈ dfsSubtree root parent depth u →
      ∃ k, depth x = depth u + k ∧ climb parent k x = u := by
  intro m
  induction m with
  | zero =>
      intro u x hm hx
      have hp := subtreeSize_pos hTree u
      omega
  | succ m ih =>
      intro u x hm hx
      rw [dfsSubtree_unfold hTree u, List.mem_cons] at hx
      rcases hx with he | hx
      · subst x
        exact ⟨0, by simp, rfl⟩
      · obtain ⟨c, hc, hxc⟩ :=
          (mem_concat_blocks (dfsSubtree root parent depth) x _).mp hx
        have hlt := child_size_lt hTree hc
        obtain ⟨k, hk, hp⟩ := ih c x (by omega) hxc
        obtain ⟨hn, hpar⟩ := (mem_bucketChildren_iff root parent u c).mp hc
        have hd := hTree.depth_step c hn
        rw [hpar] at hd
        refine ⟨k + 1, by omega, ?_⟩
        change parent (climb parent k x) = u
        rw [hp, hpar]

theorem child_subtrees_disjoint (hTree : ValidDepthTree root parent depth)
    {u a b : Fin N} (ha : a ∈ bucketChildren root parent u)
    (hb : b ∈ bucketChildren root parent u) (hab : a ≠ b) :
    ∀ x, x ∈ dfsSubtree root parent depth a →
      x ∉ dfsSubtree root parent depth b := by
  intro x hxa hxb
  obtain ⟨i, hi, hpi⟩ := dfs_climb hTree _ a x (Nat.le_refl _) hxa
  obtain ⟨j, hj, hpj⟩ := dfs_climb hTree _ b x (Nat.le_refl _) hxb
  obtain ⟨hna, hpa⟩ := (mem_bucketChildren_iff root parent u a).mp ha
  obtain ⟨hnb, hpb⟩ := (mem_bucketChildren_iff root parent u b).mp hb
  have hda : depth a = depth u + 1 := by
    simpa only [hpa] using hTree.depth_step a hna
  have hdb : depth b = depth u + 1 := by
    simpa only [hpb] using hTree.depth_step b hnb
  have hij : i = j := by omega
  rw [← hij] at hpj
  exact hab (hpi.symm.trans hpj)

/-- Both child subtrees occur in the parent's DFS list, share no vertex,
and together leave at least the parent's own entry uncounted. -/
theorem child_subtrees_pack (hTree : ValidDepthTree root parent depth)
    {u a b : Fin N} (ha : a ∈ bucketChildren root parent u)
    (hb : b ∈ bucketChildren root parent u) (hab : a ≠ b) :
    (∀ x, x ∈ dfsSubtree root parent depth a →
      x ∈ dfsSubtree root parent depth u) ∧
    (∀ x, x ∈ dfsSubtree root parent depth b →
      x ∈ dfsSubtree root parent depth u) ∧
    (∀ x, x ∈ dfsSubtree root parent depth a →
      x ∉ dfsSubtree root parent depth b) ∧
    subtreeSize root parent depth a + subtreeSize root parent depth b <
      subtreeSize root parent depth u := by
  refine ⟨fun _ hx => child_dfs_mem_parent hTree ha hx,
    fun _ hx => child_dfs_mem_parent hTree hb hx,
    child_subtrees_disjoint hTree ha hb hab, ?_⟩
  have h := two_blocks_le (dfsSubtree root parent depth) _ a b ha hb hab
  unfold subtreeSize
  rw [dfsSubtree_unfold hTree u, List.length_cons]
  omega

end Tree

def IsLightEdge {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (size : Fin N → Nat) (u v : Fin N) : Prop :=
  v ∈ bucketChildren root parent u ∧ heavyChild root parent size u ≠ some v

theorem light_edge_halves {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {depth size : Fin N → Nat} (hTree : ValidDepthTree root parent depth)
    (hsize : ∀ x, size x = subtreeSize root parent depth x)
    {u v : Fin N} (h : IsLightEdge root parent size u v) :
    2 * size v < size u := by
  rcases h with ⟨hv, hlight⟩
  have hs := heavyScan_best_spec root parent size u
  cases hb : (heavyScan root parent size u).best with
  | none =>
      have he : bucketChildren root parent u = [] := by
        simpa only [hb] using hs
      rw [he] at hv
      simp at hv
  | some w =>
      have hw : FirstMax size (bucketChildren root parent u) w := by
        simpa only [hb] using hs
      have hne : w.node ≠ v := by
        intro he
        apply hlight
        simp [heavyChild, hb, he]
      have hle : size v ≤ size w.node := by
        simpa only [hw.score_eq] using hw.maximal v hv
      have hp := (child_subtrees_pack hTree hw.mem hv hne).2.2.2
      rw [hsize v, hsize w.node] at hle
      rw [hsize v, hsize u]
      omega

theorem light_edge_subtree_halves {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth size : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth)
    (hsize : ∀ x, size x = subtreeSize root parent depth x)
    {u v : Fin N} (h : IsLightEdge root parent size u v) :
    2 * subtreeSize root parent depth v < subtreeSize root parent depth u := by
  simpa only [hsize] using light_edge_halves hTree hsize h

/-! A logarithmic measure for light-edge jumps. The rank is floor(log₂ n)
for positive `n`, and is zero at `n = 0`. -/

def dyadicRank (n : Nat) : Nat :=
  if h : 2 ≤ n then dyadicRank (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem dyadicRank_step (n : Nat) (hn : 2 ≤ n) :
    dyadicRank n = dyadicRank (n / 2) + 1 := by
  rw [dyadicRank]
  simp only [dite_eq_left hn]

theorem dyadicRank_small (n : Nat) (hn : ¬ 2 ≤ n) : dyadicRank n = 0 := by
  rw [dyadicRank]
  simp only [dite_eq_right hn]

theorem dyadicRank_bounds {n : Nat} (hn : 0 < n) :
    2 ^ dyadicRank n ≤ n ∧ n < 2 ^ (dyadicRank n + 1) := by
  have aux : ∀ m n : Nat, n ≤ m → 0 < n →
      2 ^ dyadicRank n ≤ n ∧ n < 2 ^ (dyadicRank n + 1) := by
    intro m
    induction m with
    | zero =>
        intro n hb hp
        omega
    | succ m ih =>
        intro n hb hp
        by_cases h : 2 ≤ n
        · obtain ⟨hl, hu⟩ := ih (n / 2) (by omega) (by omega)
          rw [dyadicRank_step n h]
          constructor
          · rw [Nat.pow_succ]
            omega
          · rw [Nat.pow_succ]
            omega
        · rw [dyadicRank_small n h]
          change 1 ≤ n ∧ n < 2
          omega
  exact aux n n (Nat.le_refl _) hn

theorem dyadicRank_mono {a b : Nat} (h : a ≤ b) :
    dyadicRank a ≤ dyadicRank b := by
  have aux : ∀ m a b : Nat, b ≤ m → a ≤ b →
      dyadicRank a ≤ dyadicRank b := by
    intro m
    induction m with
    | zero =>
        intro a b hb hab
        rw [dyadicRank_small a (by omega)]
        exact Nat.zero_le _
    | succ m ih =>
        intro a b hb hab
        by_cases ha : 2 ≤ a
        · have hb' : 2 ≤ b := by omega
          have hrec := ih (a / 2) (b / 2) (by omega) (by omega)
          rw [dyadicRank_step a ha, dyadicRank_step b hb']
          omega
        · rw [dyadicRank_small a ha]
          exact Nat.zero_le _
  exact aux b a b (Nat.le_refl _) h

def lightMeasure {α : Type} (size : α → Nat) (u : α) : Nat :=
  dyadicRank (size u)

/-- Each upward light-edge jump gains at least one unit of logarithmic
measure. The inequality is stated additively so it can be summed over jumps. -/
theorem light_edge_measure {N : Nat} {root : Fin N} {parent : Fin N → Fin N}
    {depth size : Fin N → Nat} (hTree : ValidDepthTree root parent depth)
    (hsize : ∀ x, size x = subtreeSize root parent depth x)
    {u v : Fin N} (h : IsLightEdge root parent size u v) :
    lightMeasure size v + 1 ≤ lightMeasure size u := by
  have hv : 0 < size v := by
    rw [hsize v]
    exact subtreeSize_pos hTree v
  have hh := light_edge_halves hTree hsize h
  have hu : 2 ≤ size u := by omega
  have hr := dyadicRank_mono (a := size v) (b := size u / 2) (by omega)
  unfold lightMeasure
  rw [dyadicRank_step (size u) hu]
  omega

end ForestHeavyPath
