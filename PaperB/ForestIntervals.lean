module

public import PaperB.Forest

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Static child bucketing and DFS preorder ancestry intervals `(tin, tout)` for
    `ProperLossForest` (Paper B v1.3, Lemma 3.2 `O(1)` known-node proper-loss test). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace LabelledQuotient

private theorem pairwise_imp_rel {α : Type} {R S : α → α → Prop}
    (hImp : ∀ a b : α, R a b → S a b) {l : List α} (hl : l.Pairwise R) :
    l.Pairwise S := by
  revert hl
  induction l with
  | nil =>
      intro _
      exact List.Pairwise.nil
  | cons x _ ih =>
      intro hl
      let ⟨hx, hxs⟩ := List.pairwise_cons.mp hl
      exact List.pairwise_cons.mpr ⟨(fun y hy => hImp x y (hx y hy)), ih hxs⟩

theorem nodup_finElems (n : Nat) : (finElems n).Pairwise (· ≠ ·) := by
  refine pairwise_imp_rel ?_ (pairwise_lt_finElems n)
  intro a b hlt hEq
  subst b
  exact Nat.lt_irrefl a.val hlt

private theorem length_keepBool_lt_of_mem_false {α : Type} (p : α → Bool) :
    ∀ {l : List α} {x : α}, x ∈ l → p x = false →
      (keepBool p l).length + 1 ≤ l.length
  | [], _, hMem, _ => False.elim (by nomatch hMem)
  | y :: ys, x, hMem, hpx => by
      dsimp [keepBool]
      cases List.mem_cons.mp hMem with
      | inl hxy =>
          rw [← hxy, hpx]
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact Nat.succ_le_succ (length_keepBool_le p ys)
      | inr hxYs =>
          have ih := length_keepBool_lt_of_mem_false p hxYs hpx
          cases p y with
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte]
              exact Nat.le_trans ih (Nat.le_succ ys.length)
          | true =>
              simp only [↓reduceIte]
              exact Nat.succ_le_succ ih

theorem nodup_length_le_of_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Pairwise (· ≠ ·) →
      (∀ x : α, x ∈ l₁ → x ∈ l₂) → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, l₂, hNodup, hSub => by
      let ⟨hxNe, hxsNodup⟩ := List.pairwise_cons.mp hNodup
      have hSubKeep : ∀ z : α, z ∈ xs →
          z ∈ keepBool (fun y => decide (y ≠ x)) l₂ := by
        intro z hz
        refine (mem_keepBool_iff _ l₂ z).mpr ⟨hSub z (List.mem_cons.mpr (Or.inr hz)), ?_⟩
        exact decide_eq_true (hxNe z hz).symm
      have hXsLe : xs.length ≤ (keepBool (fun y => decide (y ≠ x)) l₂).length :=
        nodup_length_le_of_subset hxsNodup hSubKeep
      have hxFalse : decide (x ≠ x) = false := by
        cases hDec : decide (x ≠ x) with
        | false => rfl
        | true => exact False.elim ((of_decide_eq_true hDec) rfl)
      have hKeepLt :
          (keepBool (fun y => decide (y ≠ x)) l₂).length + 1 ≤ l₂.length :=
        length_keepBool_lt_of_mem_false _ (hSub x (List.mem_cons.mpr (Or.inl rfl))) hxFalse
      exact Nat.le_trans (Nat.succ_le_succ hXsLe) hKeepLt

/-! ### Abstract finite depth-graded parent tree & `buildProperLossForest` instance -/

/-- Structural axioms on `(root, parent, depth)` satisfied by any `ProperLossForest`
    produced by `buildProperLossForest`. -/
structure ValidDepthTree {N : Nat} (root : Fin N)
    (parent : Fin N → Fin N) (depth : Fin N → Nat) : Prop where
  parent_root : parent root = root
  depth_root : depth root = 0
  depth_step : ∀ u : Fin N, u ≠ root → depth u = depth (parent u) + 1

namespace ValidDepthTree

theorem depth_pos_of_ne_root {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {u : Fin N} (hu : u ≠ root) :
    0 < depth u := by
  rw [hTree.depth_step u hu]
  exact Nat.zero_lt_succ _

theorem eq_root_of_depth_zero {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {u : Fin N} (hZero : depth u = 0) :
    u = root := by
  by_cases hu : u = root
  · exact hu
  · have hPos := hTree.depth_pos_of_ne_root hu
    rw [hZero] at hPos
    nomatch hPos

theorem depth_parent_le {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    depth (parent u) ≤ depth u := by
  by_cases hu : u = root
  · rw [hu, hTree.parent_root]
    exact Nat.le_refl _
  · rw [hTree.depth_step u hu]
    exact Nat.le_succ _

theorem depth_le_of_isForestAncestor {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {a u : Fin N}
    (hAnc : IsForestAncestor parent a u) : depth a ≤ depth u := by
  induction hAnc with
  | refl => exact Nat.le_refl _
  | step w _ ih => exact Nat.le_trans ih (hTree.depth_parent_le w)

theorem eq_of_isForestAncestor_le_depth {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {a u : Fin N}
    (hAnc : IsForestAncestor parent a u) (hLe : depth u ≤ depth a) : a = u := by
  induction hAnc with
  | refl => rfl
  | step w hPrev _ =>
      by_cases hw : w = root
      · have hPrevLe := hTree.depth_le_of_isForestAncestor hPrev
        have haLe : depth a ≤ 0 := by
          simpa only [hw, hTree.parent_root, hTree.depth_root] using hPrevLe
        have haZero : depth a = 0 := by omega
        exact (hTree.eq_root_of_depth_zero haZero).trans hw.symm
      · have hPrevLe : depth a ≤ depth (parent w) :=
          hTree.depth_le_of_isForestAncestor hPrev
        have hLt : depth a < depth w := by
          rw [hTree.depth_step w hw]
          exact Nat.lt_succ_of_le hPrevLe
        exact False.elim (Nat.not_lt_of_ge hLe hLt)

theorem eq_of_ancestors_same_depth {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {c₁ c₂ x : Fin N}
    (h₁ : IsForestAncestor parent c₁ x)
    (h₂ : IsForestAncestor parent c₂ x)
    (hEqD : depth c₁ = depth c₂) : c₁ = c₂ := by
  induction h₁ with
  | refl =>
      have hLe : depth c₁ ≤ depth c₂ := by
        rw [hEqD]
        exact Nat.le_refl _
      exact (hTree.eq_of_isForestAncestor_le_depth h₂ hLe).symm
  | step w h₁Prev ih =>
      cases h₂ with
      | refl =>
          exact hTree.eq_of_isForestAncestor_le_depth
            (IsForestAncestor.step _ h₁Prev) (Nat.le_of_eq hEqD.symm)
      | step _ h₂Prev =>
          exact ih h₂Prev

private theorem isForestAncestor_root_bounded {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    ∀ (bound : Nat) (u : Fin N), depth u < bound → IsForestAncestor parent root u
  | 0, _, hLt => False.elim (by nomatch hLt)
  | bound + 1, u, hLt => by
      by_cases hu : u = root
      · rw [hu]
        exact IsForestAncestor.refl
      · have hStep := hTree.depth_step u hu
        have hParLt : depth (parent u) < bound := by
          rw [hStep] at hLt
          exact Nat.le_of_succ_le_succ hLt
        exact IsForestAncestor.step u
          (isForestAncestor_root_bounded hTree bound (parent u) hParLt)

theorem isForestAncestor_root {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    IsForestAncestor parent root u :=
  isForestAncestor_root_bounded hTree (depth u + 1) u (Nat.lt_succ_self (depth u))

end ValidDepthTree

theorem buildProperLossForest_validDepthTree {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) :
    ValidDepthTree
      (buildProperLossForest H rank).rootNode
      (buildProperLossForest H rank).parent
      (buildProperLossForest H rank).depth := by
  refine ⟨buildProperLossForest_parent_root H rank,
    buildProperLossForest_depth_root H rank, ?_⟩
  intro u huNeRoot
  cases hu : (buildProperLossForest H rank).nodeKey? u with
  | none =>
      have hEqRoot : u = (buildProperLossForest H rank).rootNode :=
        buildProperLossForest_nodeKey?_inj H rank
          (hu.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      exact False.elim (huNeRoot hEqRoot)
  | some P =>
      exact buildProperLossForest_depth_real rankArc flat hu

/-! ### One-pass static child-list bucketing over `finElems N` -/

def addChildToBuckets {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (buckets : Fin N → List (Fin N)) (u : Fin N) : Fin N → List (Fin N) :=
  if u = root then
    buckets
  else
    fun q => if q = parent u then u :: buckets q else buckets q

def bucketPassAux {N : Nat} (root : Fin N) (parent : Fin N → Fin N) :
    List (Fin N) → (Fin N → List (Fin N)) → (Fin N → List (Fin N))
  | [], buckets => buckets
  | u :: us, buckets =>
      bucketPassAux root parent us (addChildToBuckets root parent buckets u)

/-- One-pass bucketed child lists per node (`O(N)` pass over `finElems N`). -/
def bucketChildren {N : Nat} (root : Fin N) (parent : Fin N → Fin N) :
    Fin N → List (Fin N) :=
  bucketPassAux root parent (finElems N) (fun _ => [])

/-- Concrete `Array` of child lists of size `N`. -/
def bucketChildrenArray {N : Nat} (root : Fin N) (parent : Fin N → Fin N) :
    Array (List (Fin N)) :=
  Array.ofFn (bucketChildren root parent)

private theorem mem_bucketPassAux_iff {n : Nat} (excluded : Fin n)
    (key : Fin n → Fin n) :
    ∀ (us : List (Fin n)) (groups : Fin n → List (Fin n)) (q c : Fin n),
      c ∈ bucketPassAux excluded key us groups q ↔
        c ∈ groups q ∨ (c ∈ us ∧ c ≠ excluded ∧ key c = q) := by
  intro us
  induction us with
  | nil =>
      intro groups q c
      simp only [bucketPassAux, List.not_mem_nil, false_and, or_false]
  | cons u us ih =>
      intro groups q c
      have hupdate :
          c ∈ addChildToBuckets excluded key groups u q ↔
            c ∈ groups q ∨ (c = u ∧ c ≠ excluded ∧ key c = q) := by
        by_cases he : u = excluded
        · simp only [addChildToBuckets, ite_eq_left he]
          constructor
          · intro hg
            exact Or.inl hg
          · intro h
            rcases h with hg | ⟨hcu, hne, _⟩
            · exact hg
            · exact (hne (hcu.trans he)).elim
        · by_cases hk : q = key u
          · simp only [addChildToBuckets, ite_eq_right he, ite_eq_left hk, List.mem_cons]
            constructor
            · intro h
              rcases h with hcu | hg
              · exact Or.inr ⟨hcu, fun hce => he (hcu.symm.trans hce),
                  (congrArg key hcu).trans hk.symm⟩
              · exact Or.inl hg
            · intro h
              rcases h with hg | ⟨hcu, _, _⟩
              · exact Or.inr hg
              · exact Or.inl hcu
          · simp only [addChildToBuckets, ite_eq_right he, ite_eq_right hk]
            constructor
            · intro hg
              exact Or.inl hg
            · intro h
              rcases h with hg | ⟨hcu, _, hcq⟩
              · exact hg
              · exact (hk (hcq.symm.trans (congrArg key hcu))).elim
      simp only [bucketPassAux, ih, hupdate, List.mem_cons]
      constructor
      · intro h
        rcases h with h | ⟨hus, hne, hcq⟩
        · rcases h with hg | ⟨hcu, hne, hcq⟩
          · exact Or.inl hg
          · exact Or.inr ⟨Or.inl hcu, hne, hcq⟩
        · exact Or.inr ⟨Or.inr hus, hne, hcq⟩
      · intro h
        rcases h with hg | ⟨hmem, hne, hcq⟩
        · exact Or.inl (Or.inl hg)
        · rcases hmem with hcu | hus
          · exact Or.inl (Or.inr ⟨hcu, hne, hcq⟩)
          · exact Or.inr ⟨hus, hne, hcq⟩

theorem mem_bucketChildren_iff {n : Nat} (excluded : Fin n)
    (key : Fin n → Fin n) (q c : Fin n) :
    c ∈ bucketChildren excluded key q ↔ c ≠ excluded ∧ key c = q := by
  simp only [bucketChildren, mem_bucketPassAux_iff, List.not_mem_nil, false_or,
    mem_finElems, true_and]

private theorem nodup_bucketPassAux {N : Nat} (root : Fin N)
    (parent : Fin N → Fin N) :
    ∀ (us : List (Fin N)) (buckets : Fin N → List (Fin N)),
      us.Pairwise (· ≠ ·) →
      (∀ q : Fin N, (buckets q).Pairwise (· ≠ ·)) →
      (∀ q x : Fin N, x ∈ buckets q → x ∉ us) →
      ∀ q : Fin N, (bucketPassAux root parent us buckets q).Pairwise (· ≠ ·)
  | [], buckets, _, hBucketsNodup, _, q => hBucketsNodup q
  | u :: us, buckets, hUsNodup, hBucketsNodup, hDisj, q => by
      let ⟨huNeUs, hTailNodup⟩ := List.pairwise_cons.mp hUsNodup
      dsimp [bucketPassAux]
      refine nodup_bucketPassAux root parent us
        (addChildToBuckets root parent buckets u) hTailNodup ?_ ?_ q
      · intro r
        unfold addChildToBuckets
        by_cases hu : u = root
        · rw [ite_eq_left hu]
          exact hBucketsNodup r
        · rw [ite_eq_right hu]
          by_cases hrp : r = parent u
          · rw [ite_eq_left hrp]
            refine List.pairwise_cons.mpr ⟨?_, hBucketsNodup r⟩
            intro z hz hEq
            rw [← hEq] at hz
            exact hDisj r u hz (List.mem_cons.mpr (Or.inl rfl))
          · rw [ite_eq_right hrp]
            exact hBucketsNodup r
      · intro r x hxInNew hxInTail
        unfold addChildToBuckets at hxInNew
        by_cases hu : u = root
        · rw [ite_eq_left hu] at hxInNew
          exact hDisj r x hxInNew (List.mem_cons.mpr (Or.inr hxInTail))
        · rw [ite_eq_right hu] at hxInNew
          by_cases hrp : r = parent u
          · rw [ite_eq_left hrp] at hxInNew
            cases List.mem_cons.mp hxInNew with
            | inl hxu =>
                exact huNeUs x hxInTail hxu.symm
            | inr hxOld =>
                exact hDisj r x hxOld (List.mem_cons.mpr (Or.inr hxInTail))
          · rw [ite_eq_right hrp] at hxInNew
            exact hDisj r x hxInNew (List.mem_cons.mpr (Or.inr hxInTail))

theorem nodup_bucketChildren {N : Nat} (root : Fin N)
    (parent : Fin N → Fin N) (q : Fin N) :
    (bucketChildren root parent q).Pairwise (· ≠ ·) :=
  nodup_bucketPassAux root parent (finElems N) (fun _ => [])
    (nodup_finElems N) (fun _ => List.Pairwise.nil) (fun _ _ h => by nomatch h) q

def sumBucketLengths {N : Nat} (buckets : Fin N → List (Fin N)) :
    List (Fin N) → Nat
  | [] => 0
  | q :: qs => (buckets q).length + sumBucketLengths buckets qs

private theorem sumBucketLengths_congr {N : Nat}
    {b₁ b₂ : Fin N → List (Fin N)} {qs : List (Fin N)}
    (hEq : ∀ q : Fin N, q ∈ qs → b₁ q = b₂ q) :
    sumBucketLengths b₁ qs = sumBucketLengths b₂ qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      dsimp [sumBucketLengths]
      rw [hEq q (List.mem_cons.mpr (Or.inl rfl)),
        ih (fun r hr => hEq r (List.mem_cons.mpr (Or.inr hr)))]

private theorem sumBucketLengths_insert {N : Nat}
    (buckets : Fin N → List (Fin N)) (u p : Fin N) :
    ∀ {qs : List (Fin N)}, qs.Pairwise (· ≠ ·) → p ∈ qs →
      sumBucketLengths (fun q => if q = p then u :: buckets q else buckets q) qs =
        sumBucketLengths buckets qs + 1
  | [], _, hp => False.elim (by nomatch hp)
  | q :: qs, hNodup, hp => by
      let ⟨hqNe, hqsNodup⟩ := List.pairwise_cons.mp hNodup
      dsimp [sumBucketLengths]
      by_cases hqp : q = p
      · rw [ite_eq_left hqp]
        have hTailEq :
            sumBucketLengths
              (fun r => if r = p then u :: buckets r else buckets r) qs =
              sumBucketLengths buckets qs := by
          refine sumBucketLengths_congr (fun r hr => ?_)
          have hrNeP : r ≠ p := fun hrp => hqNe r hr (hqp.trans hrp.symm)
          exact ite_eq_right hrNeP
        rw [hTailEq]
        change ((buckets q).length + 1) + sumBucketLengths buckets qs =
          ((buckets q).length + sumBucketLengths buckets qs) + 1
        omega
      · rw [ite_eq_right hqp]
        have hpTail : p ∈ qs :=
          match List.mem_cons.mp hp with
          | Or.inl h => False.elim (hqp h.symm)
          | Or.inr h => h
        rw [sumBucketLengths_insert buckets u p hqsNodup hpTail] <;> omega

private theorem sumBucketLengths_pass {N : Nat} (root : Fin N)
    (parent : Fin N → Fin N) :
    ∀ (us : List (Fin N)) (buckets : Fin N → List (Fin N)),
      sumBucketLengths (bucketPassAux root parent us buckets) (finElems N) =
        sumBucketLengths buckets (finElems N) +
          (keepBool (fun v => decide (v ≠ root)) us).length
  | [], buckets => by
      dsimp [bucketPassAux, keepBool]
  | u :: us, buckets => by
      dsimp [bucketPassAux, keepBool]
      rw [sumBucketLengths_pass root parent us
        (addChildToBuckets root parent buckets u)]
      unfold addChildToBuckets
      by_cases hu : u = root
      · simp [hu]
      · rw [ite_eq_right hu]
        rw [ite_eq_left (decide_eq_true hu)]
        rw [sumBucketLengths_insert buckets u (parent u)
          (nodup_finElems N) (mem_finElems (parent u))]
        change (sumBucketLengths buckets (finElems N) + 1) +
            (keepBool (fun v => decide (v ≠ root)) us).length =
          sumBucketLengths buckets (finElems N) +
            ((keepBool (fun v => decide (v ≠ root)) us).length + 1)
        omega

private theorem sumBucketLengths_empty {N : Nat} :
    ∀ (qs : List (Fin N)), sumBucketLengths (fun _ : Fin N => ([] : List (Fin N))) qs = 0
  | [] => rfl
  | _ :: qs => by
      simpa only [sumBucketLengths, List.length_nil, Nat.zero_add] using
        (sumBucketLengths_empty qs)

/-- Exact total bucketed child-edge count across all `N` nodes equals `N - 1`. -/
theorem total_bucketChildren_edges {N : Nat} (root : Fin N)
    (parent : Fin N → Fin N) :
    sumBucketLengths (bucketChildren root parent) (finElems N) = N - 1 := by
  unfold bucketChildren
  rw [sumBucketLengths_pass, sumBucketLengths_empty]
  have hFalse : decide (root ≠ root) = false := by
    cases hDec : decide (root ≠ root) with
    | false => rfl
    | true => exact False.elim ((of_decide_eq_true hDec) rfl)
  have hLe1 :
      (keepBool (fun v => decide (v ≠ root)) (finElems N)).length + 1 ≤
        (finElems N).length :=
    length_keepBool_lt_of_mem_false _ (mem_finElems root) hFalse
  have hGe1 :
      (finElems N).length ≤
        (keepBool (fun v => decide (v ≠ root)) (finElems N)).length + 1 := by
    have hSub : ∀ x : Fin N, x ∈ finElems N →
        x ∈ root :: keepBool (fun v => decide (v ≠ root)) (finElems N) := by
      intro x hx
      by_cases hxr : x = root
      · exact List.mem_cons.mpr (Or.inl hxr)
      · exact List.mem_cons.mpr
          (Or.inr ((mem_keepBool_iff _ (finElems N) x).mpr ⟨hx, decide_eq_true hxr⟩))
    exact nodup_length_le_of_subset (nodup_finElems N) hSub
  rw [length_finElems N] at hLe1 hGe1
  omega

/-! ### Pure structural DFS preorder subtree lists -/

theorem flatMap_split_at_mem {α β : Type} (f : α → List β)
    {xs : List α} {x : α} (hx : x ∈ xs) :
    ∃ before after : List β, xs.flatMap f = before ++ f x ++ after := by
  obtain ⟨ys, zs, rfl⟩ := List.append_of_mem hx
  refine ⟨ys.flatMap f, zs.flatMap f, ?_⟩
  simp [List.flatMap_append, List.flatMap_cons, List.append_assoc]

def concatMapList {α β : Type} (f : α → List β) : List α → List β
  | [] => []
  | x :: xs => f x ++ concatMapList f xs

theorem concatMapList_eq_flatMap {α β : Type} (f : α → List β) (l : List α) :
    concatMapList f l = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [concatMapList, List.flatMap_cons, ih]

theorem mem_concatMapList_iff {α β : Type} (f : α → List β) (l : List α) (y : β) :
    y ∈ concatMapList f l ↔ ∃ x : α, x ∈ l ∧ y ∈ f x := by
  rw [concatMapList_eq_flatMap]
  exact List.mem_flatMap

theorem concatMapList_congr {α β : Type} {f g : α → List β} {l : List α}
    (hEq : ∀ x : α, x ∈ l → f x = g x) :
    concatMapList f l = concatMapList g l := by
  revert hEq
  induction l with
  | nil =>
    intro _
    rfl
  | cons x xs ih =>
    intro hEq
    have hHead : f x = g x := hEq x (by simp)
    have hTail : ∀ z : α, z ∈ xs → f z = g z := by
      intro z hz
      exact hEq z (List.mem_cons.mpr (Or.inr hz))
    simp only [concatMapList, hHead, ih hTail]

theorem exists_split_concatMapList {α β : Type} (f : α → List β) :
    ∀ {l : List α} {c : α}, c ∈ l →
      ∃ before after : List β, concatMapList f l = before ++ f c ++ after := by
  intro l c hc
  rw [concatMapList_eq_flatMap]
  exact flatMap_split_at_mem f hc

def maxNatList : List Nat → Nat
  | [] => 0
  | x :: xs => if x ≤ maxNatList xs then maxNatList xs else x

theorem le_maxNatList {l : List Nat} {x : Nat} (hx : x ∈ l) :
    x ≤ maxNatList l := by
  induction l with
  | nil => nomatch hx
  | cons y ys ih =>
      dsimp [maxNatList]
      by_cases hle : y ≤ maxNatList ys
      · rw [ite_eq_left hle]
        cases List.mem_cons.mp hx with
        | inl hxy => rw [hxy]; exact hle
        | inr hxYs => exact ih hxYs
      · rw [ite_eq_right hle]
        cases List.mem_cons.mp hx with
        | inl hxy => rw [hxy]; exact Nat.le_refl _
        | inr hxYs =>
            have hGt : maxNatList ys ≤ y := by omega
            exact Nat.le_trans (ih hxYs) hGt

def maxDepth {N : Nat} (depth : Fin N → Nat) : Nat :=
  maxNatList ((finElems N).map depth)

theorem depth_le_maxDepth {N : Nat} (depth : Fin N → Nat) (u : Fin N) :
    depth u ≤ maxDepth depth :=
  le_maxNatList (List.mem_map.mpr ⟨u, mem_finElems u, rfl⟩)

def dfsSubtreeAux {N : Nat} (children : Fin N → List (Fin N)) :
    Nat → Fin N → List (Fin N)
  | 0, _ => []
  | fuel + 1, u =>
      u :: concatMapList (dfsSubtreeAux children fuel) (children u)

def dfsSubtree {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) (u : Fin N) : List (Fin N) :=
  dfsSubtreeAux (bucketChildren root parent) (maxDepth depth + 1) u

def dfsPreorder {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) : List (Fin N) :=
  dfsSubtree root parent depth root

private theorem dfsSubtreeAux_eq_of_gt {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    ∀ {f₁ f₂ : Nat} {u : Fin N},
      maxDepth depth < depth u + f₁ →
      maxDepth depth < depth u + f₂ →
      dfsSubtreeAux (bucketChildren root parent) f₁ u =
        dfsSubtreeAux (bucketChildren root parent) f₂ u
  | 0, _, u, h₁, _ => by
      have hLe := depth_le_maxDepth depth u
      omega
  | _ + 1, 0, u, _, h₂ => by
      have hLe := depth_le_maxDepth depth u
      omega
  | f₁ + 1, f₂ + 1, u, h₁, h₂ => by
      dsimp [dfsSubtreeAux]
      refine congrArg (List.cons u) (concatMapList_congr (fun c hc => ?_))
      let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hc
      have hStep : depth c = depth u + 1 := by
        rw [← hcPar]
        exact hTree.depth_step c hcNeRoot
      have hc₁ : maxDepth depth < depth c + f₁ := by omega
      have hc₂ : maxDepth depth < depth c + f₂ := by omega
      exact dfsSubtreeAux_eq_of_gt hTree hc₁ hc₂

theorem dfsSubtree_unfold {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    dfsSubtree root parent depth u =
      u :: concatMapList (dfsSubtree root parent depth)
        (bucketChildren root parent u) := by
  change dfsSubtreeAux (bucketChildren root parent) (maxDepth depth + 1) u = _
  dsimp [dfsSubtreeAux]
  refine congrArg (List.cons u) (concatMapList_congr (fun c hc => ?_))
  let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hc
  have hStep : depth c = depth u + 1 := by
    rw [← hcPar]
    exact hTree.depth_step c hcNeRoot
  have hLeU : depth u ≤ maxDepth depth := depth_le_maxDepth depth u
  have hLeC : depth c ≤ maxDepth depth := depth_le_maxDepth depth c
  have hc₁ : maxDepth depth < depth c + maxDepth depth := by omega
  have hc₂ : maxDepth depth < depth c + (maxDepth depth + 1) := by omega
  exact dfsSubtreeAux_eq_of_gt hTree hc₁ hc₂

private theorem dfsSubtree_subset_of_mem_bounded {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    ∀ (rem : Nat) (u p x : Fin N),
      maxDepth depth < depth u + rem →
      p ∈ dfsSubtree root parent depth u →
      x ∈ dfsSubtree root parent depth p →
      x ∈ dfsSubtree root parent depth u
  | 0, u, _, _, hRem, _, _ => by
      have hLe := depth_le_maxDepth depth u
      omega
  | rem + 1, u, p, x, hRem, hpInU, hxInP => by
      rw [dfsSubtree_unfold hTree u] at hpInU ⊢
      cases List.mem_cons.mp hpInU with
      | inl hpu =>
          rw [← hpu]
          rw [← dfsSubtree_unfold hTree p]
          exact hxInP
      | inr hpConcat =>
          let ⟨c, hcChild, hpInC⟩ :=
            (mem_concatMapList_iff (dfsSubtree root parent depth)
              (bucketChildren root parent u) p).mp hpConcat
          let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hcChild
          have hStep : depth c = depth u + 1 := by
            rw [← hcPar]
            exact hTree.depth_step c hcNeRoot
          have hcRem : maxDepth depth < depth c + rem := by omega
          have hxInC : x ∈ dfsSubtree root parent depth c :=
            dfsSubtree_subset_of_mem_bounded hTree rem c p x hcRem hpInC hxInP
          exact List.mem_cons.mpr
            (Or.inr ((mem_concatMapList_iff (dfsSubtree root parent depth)
              (bucketChildren root parent u) x).mpr ⟨c, hcChild, hxInC⟩))

private theorem mem_dfsSubtree_imp_anc_bounded {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    ∀ (rem : Nat) (u v : Fin N),
      maxDepth depth < depth u + rem →
      v ∈ dfsSubtree root parent depth u →
      IsForestAncestor parent u v
  | 0, u, _, hRem, _ => by
      have hLe := depth_le_maxDepth depth u
      omega
  | rem + 1, u, v, hRem, hvMem => by
      rw [dfsSubtree_unfold hTree u] at hvMem
      cases List.mem_cons.mp hvMem with
      | inl hvu =>
          rw [hvu]
          exact IsForestAncestor.refl
      | inr hvConcat =>
          let ⟨c, hcChild, hvInC⟩ :=
            (mem_concatMapList_iff (dfsSubtree root parent depth)
              (bucketChildren root parent u) v).mp hvConcat
          let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hcChild
          have hStep : depth c = depth u + 1 := by
            rw [← hcPar]
            exact hTree.depth_step c hcNeRoot
          have hcRem : maxDepth depth < depth c + rem := by omega
          have hAncCV : IsForestAncestor parent c v :=
            mem_dfsSubtree_imp_anc_bounded hTree rem c v hcRem hvInC
          have hAncUC : IsForestAncestor parent u c := by
            rw [← hcPar]
            exact IsForestAncestor.step c IsForestAncestor.refl
          exact IsForestAncestor.trans hAncUC hAncCV

theorem mem_dfsSubtree_iff {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u v : Fin N) :
    v ∈ dfsSubtree root parent depth u ↔ IsForestAncestor parent u v := by
  constructor
  · intro hvMem
    have hRem : maxDepth depth < depth u + (maxDepth depth + 1) := by omega
    exact mem_dfsSubtree_imp_anc_bounded hTree (maxDepth depth + 1) u v hRem hvMem
  · intro hAnc
    induction hAnc with
    | refl =>
        rw [dfsSubtree_unfold hTree u]
        exact List.mem_cons.mpr (Or.inl rfl)
    | step w _ ih =>
        by_cases hw : w = root
        · rw [hw, hTree.parent_root] at ih
          rw [hw]
          exact ih
        · have hwChild : w ∈ bucketChildren root parent (parent w) :=
            (mem_bucketChildren_iff root parent (parent w) w).mpr ⟨hw, rfl⟩
          have hwInSelf : w ∈ dfsSubtree root parent depth w := by
            rw [dfsSubtree_unfold hTree w]
            exact List.mem_cons.mpr (Or.inl rfl)
          have hwInPar : w ∈ dfsSubtree root parent depth (parent w) := by
            rw [dfsSubtree_unfold hTree (parent w)]
            exact List.mem_cons.mpr
              (Or.inr ((mem_concatMapList_iff (dfsSubtree root parent depth)
                (bucketChildren root parent (parent w)) w).mpr ⟨w, hwChild, hwInSelf⟩))
          have hRem : maxDepth depth < depth u + (maxDepth depth + 1) := by omega
          exact dfsSubtree_subset_of_mem_bounded hTree
            (maxDepth depth + 1) u (parent w) w hRem ih hwInPar

theorem mem_dfsPreorder {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    u ∈ dfsPreorder root parent depth :=
  (mem_dfsSubtree_iff hTree root u).mpr (hTree.isForestAncestor_root u)

private theorem nodup_concatMapList {α β : Type} {f : α → List β} {l : List α}
    (hl : l.Pairwise (· ≠ ·))
    (hfNodup : ∀ c : α, c ∈ l → (f c).Pairwise (· ≠ ·))
    (hDisj : ∀ c₁ c₂ : α, c₁ ∈ l → c₂ ∈ l → c₁ ≠ c₂ →
      ∀ x : β, x ∈ f c₁ → x ∉ f c₂) :
    (concatMapList f l).Pairwise (· ≠ ·) := by
  revert hl hfNodup hDisj
  induction l with
  | nil =>
      intro _ _ _
      exact List.Pairwise.nil
  | cons c cs ih =>
      intro hl hfNodup hDisj
      let ⟨hcNeCs, hcsNodup⟩ := List.pairwise_cons.mp hl
      dsimp [concatMapList]
      refine List.pairwise_append.mpr ⟨hfNodup c (List.mem_cons.mpr (Or.inl rfl)), ?_, ?_⟩
      · exact ih hcsNodup
          (fun c' hc' => hfNodup c' (List.mem_cons.mpr (Or.inr hc')))
          (fun c₁ c₂ h₁ h₂ hne =>
            hDisj c₁ c₂ (List.mem_cons.mpr (Or.inr h₁)) (List.mem_cons.mpr (Or.inr h₂)) hne)
      · intro x hx y hy hxy
        let ⟨c₂, hc₂InCs, hyInC₂⟩ := (mem_concatMapList_iff f cs y).mp hy
        rw [hxy] at hx
        exact hDisj c c₂
          (List.mem_cons.mpr (Or.inl rfl))
          (List.mem_cons.mpr (Or.inr hc₂InCs))
          (hcNeCs c₂ hc₂InCs) y hx hyInC₂

private theorem nodup_dfsSubtree_bounded {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    ∀ (rem : Nat) (u : Fin N),
      maxDepth depth < depth u + rem →
      (dfsSubtree root parent depth u).Pairwise (· ≠ ·)
  | 0, u, hRem => by
      have hLe := depth_le_maxDepth depth u
      omega
  | rem + 1, u, hRem => by
      rw [dfsSubtree_unfold hTree u]
      refine List.pairwise_cons.mpr ⟨?_, ?_⟩
      · intro x hx hux
        rw [← hux] at hx
        let ⟨c, hcChild, huInC⟩ :=
          (mem_concatMapList_iff (dfsSubtree root parent depth)
            (bucketChildren root parent u) u).mp hx
        let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hcChild
        have hStep : depth c = depth u + 1 := by
          rw [← hcPar]
          exact hTree.depth_step c hcNeRoot
        have hAncCU : IsForestAncestor parent c u :=
          (mem_dfsSubtree_iff hTree c u).mp huInC
        have hLe : depth c ≤ depth u := hTree.depth_le_of_isForestAncestor hAncCU
        omega
      · refine nodup_concatMapList (nodup_bucketChildren root parent u) ?_ ?_
        · intro c hcChild
          let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hcChild
          have hStep : depth c = depth u + 1 := by
            rw [← hcPar]
            exact hTree.depth_step c hcNeRoot
          have hcRem : maxDepth depth < depth c + rem := by omega
          exact nodup_dfsSubtree_bounded hTree rem c hcRem
        · intro c₁ c₂ hc₁ hc₂ hne x hx₁ hx₂
          let ⟨h₁Ne, h₁Par⟩ := (mem_bucketChildren_iff root parent u c₁).mp hc₁
          let ⟨h₂Ne, h₂Par⟩ := (mem_bucketChildren_iff root parent u c₂).mp hc₂
          have hd₁ : depth c₁ = depth u + 1 := by
            rw [← h₁Par]; exact hTree.depth_step c₁ h₁Ne
          have hd₂ : depth c₂ = depth u + 1 := by
            rw [← h₂Par]; exact hTree.depth_step c₂ h₂Ne
          have hAnc₁ : IsForestAncestor parent c₁ x :=
            (mem_dfsSubtree_iff hTree c₁ x).mp hx₁
          have hAnc₂ : IsForestAncestor parent c₂ x :=
            (mem_dfsSubtree_iff hTree c₂ x).mp hx₂
          exact hne (hTree.eq_of_ancestors_same_depth hAnc₁ hAnc₂ (hd₁.trans hd₂.symm))

theorem nodup_dfsSubtree {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (u : Fin N) :
    (dfsSubtree root parent depth u).Pairwise (· ≠ ·) :=
  nodup_dfsSubtree_bounded hTree (maxDepth depth + 1) u (by omega)

theorem nodup_dfsPreorder {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    (dfsPreorder root parent depth).Pairwise (· ≠ ·) :=
  nodup_dfsSubtree hTree root

theorem length_dfsPreorder {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    (dfsPreorder root parent depth).length = N := by
  have hLe : (dfsPreorder root parent depth).length ≤ (finElems N).length :=
    nodup_length_le_of_subset (nodup_dfsPreorder hTree) (fun x _ => mem_finElems x)
  have hGe : (finElems N).length ≤ (dfsPreorder root parent depth).length :=
    nodup_length_le_of_subset (nodup_finElems N) (fun x _ => mem_dfsPreorder hTree x)
  rw [length_finElems N] at hLe hGe
  exact Nat.le_antisymm hLe hGe

private theorem exists_split_dfsSubtree_bounded {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) :
    ∀ (rem : Nat) (u a : Fin N),
      maxDepth depth < depth u + rem →
      a ∈ dfsSubtree root parent depth u →
      ∃ pref suff : List (Fin N),
        dfsSubtree root parent depth u =
          pref ++ dfsSubtree root parent depth a ++ suff
  | 0, u, _, hRem, _ => by
      have hLe := depth_le_maxDepth depth u
      omega
  | rem + 1, u, a, hRem, haMem => by
      have hUnfold := dfsSubtree_unfold hTree u
      rw [hUnfold] at haMem
      cases List.mem_cons.mp haMem with
      | inl hau =>
          rw [← hau]
          exact ⟨[], [], (List.append_nil _).symm⟩
      | inr haConcat =>
          let ⟨c, hcChild, haInC⟩ :=
            (mem_concatMapList_iff (dfsSubtree root parent depth)
              (bucketChildren root parent u) a).mp haConcat
          let ⟨before, after, hSplitChild⟩ :=
            exists_split_concatMapList (dfsSubtree root parent depth) hcChild
          let ⟨hcNeRoot, hcPar⟩ := (mem_bucketChildren_iff root parent u c).mp hcChild
          have hStep : depth c = depth u + 1 := by
            rw [← hcPar]
            exact hTree.depth_step c hcNeRoot
          have hcRem : maxDepth depth < depth c + rem := by omega
          let ⟨pSub, sSub, hSubEq⟩ :=
            exists_split_dfsSubtree_bounded hTree rem c a hcRem haInC
          refine ⟨(u :: before) ++ pSub, sSub ++ after, ?_⟩
          rw [hUnfold, hSplitChild, hSubEq]
          simp only [List.cons_append, List.append_assoc]

theorem exists_split_dfsPreorder {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (a : Fin N) :
    ∃ pref suff : List (Fin N),
      dfsPreorder root parent depth =
        pref ++ dfsSubtree root parent depth a ++ suff :=
  exists_split_dfsSubtree_bounded hTree (maxDepth depth + 1) root a
    (by omega) (mem_dfsPreorder hTree a)

/-! ### First occurrence and a list-segment interval lemma -/

/-- Zero-based first occurrence, returning the list length on a miss. -/
def firstOccurrence {α : Type} [DecidableEq α] (x : α) : List α → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else firstOccurrence x ys + 1

private theorem firstOccurrence_append_of_not_mem {α : Type} [DecidableEq α]
    (x : α) {l : List α} (r : List α) (hx : x ∉ l) :
    firstOccurrence x (l ++ r) = l.length + firstOccurrence x r := by
  induction l with
  | nil =>
      simp only [List.nil_append, List.length_nil, Nat.zero_add]
  | cons y ys ih =>
      have hxy : x ≠ y := fun h => hx (List.mem_cons.mpr (Or.inl h))
      have ht : x ∉ ys := fun h => hx (List.mem_cons.mpr (Or.inr h))
      simp only [List.cons_append, firstOccurrence, ite_eq_right hxy, List.length_cons, ih ht]
      omega

private theorem firstOccurrence_append_of_mem {α : Type} [DecidableEq α]
    (x : α) {l : List α} (r : List α) (hx : x ∈ l) :
    firstOccurrence x (l ++ r) = firstOccurrence x l := by
  induction l with
  | nil => nomatch hx
  | cons y ys ih =>
      by_cases hxy : x = y
      · simp only [List.cons_append, firstOccurrence, ite_eq_left hxy]
      · have ht : x ∈ ys := (List.mem_cons.mp hx).resolve_left hxy
        simp only [List.cons_append, firstOccurrence, ite_eq_right hxy, ih ht]

theorem firstOccurrence_eq_length_of_not_mem {α : Type} [DecidableEq α]
    (x : α) {l : List α} (hx : x ∉ l) :
    firstOccurrence x l = l.length := by
  simpa only [List.append_nil, firstOccurrence, Nat.add_zero] using
    firstOccurrence_append_of_not_mem x ([] : List α) hx

private theorem firstOccurrence_at_head_after_prefix {α : Type} [DecidableEq α]
    (x : α) {pref : List α} (suff : List α) (hx : x ∉ pref) :
    firstOccurrence x (pref ++ (x :: suff)) = pref.length := by
  rw [firstOccurrence_append_of_not_mem x (x :: suff) hx]
  simp [firstOccurrence]

/-- A successful search returns precisely the length of the prefix before
    the first copy of `x`, with no copy of `x` in that prefix. -/
theorem firstOccurrence_eq_iff {α : Type} [DecidableEq α]
    (x : α) {l : List α} (hx : x ∈ l) (i : Nat) :
    firstOccurrence x l = i ↔
      ∃ pref suff : List α, l = pref ++ (x :: suff) ∧ x ∉ pref ∧ pref.length = i := by
  constructor
  · intro hi
    induction l generalizing i with
    | nil => nomatch hx
    | cons y ys ih =>
        by_cases hxy : x = y
        · subst y
          exact ⟨[], ys, rfl, List.not_mem_nil, by simpa [firstOccurrence] using hi⟩
        · have ht : x ∈ ys := (List.mem_cons.mp hx).resolve_left hxy
          obtain ⟨pref, suff, hSplit, hNot, hLen⟩ :=
            ih ht (firstOccurrence x ys) rfl
          refine ⟨y :: pref, suff, congrArg (List.cons y) hSplit, ?_, ?_⟩
          · intro hm
            exact (List.mem_cons.mp hm).elim hxy hNot
          · simpa only [List.length_cons, hLen, firstOccurrence, ite_eq_right hxy] using hi
  · rintro ⟨pref, suff, hSplit, hNot, hLen⟩
    rw [hSplit, firstOccurrence_at_head_after_prefix x suff hNot, hLen]

theorem firstOccurrence_lt_length_of_mem {α : Type} [DecidableEq α]
    (x : α) {l : List α} (hx : x ∈ l) :
    firstOccurrence x l < l.length := by
  obtain ⟨pref, suff, hSplit, _, hLen⟩ :=
    (firstOccurrence_eq_iff x hx (firstOccurrence x l)).mp rfl
  rw [← hLen, hSplit, List.length_append, List.length_cons]
  omega

/-- In a duplicate-free concatenation, the first position of an element lies
    in the middle segment's half-open range exactly when the element is in
    that segment. The statement also excludes elements absent from the list. -/
theorem firstOccurrence_in_middle_iff {α : Type} [DecidableEq α]
    (x : α) {pref mid suff : List α}
    (hUnique : (pref ++ mid ++ suff).Pairwise (· ≠ ·)) :
    (pref.length ≤ firstOccurrence x (pref ++ mid ++ suff) ∧
      firstOccurrence x (pref ++ mid ++ suff) < pref.length + mid.length) ↔
      x ∈ mid := by
  rw [List.append_assoc pref mid suff] at hUnique ⊢
  constructor
  · rintro ⟨hLo, hHi⟩
    by_cases hp : x ∈ pref
    · rw [firstOccurrence_append_of_mem x (mid ++ suff) hp] at hLo
      exact False.elim (Nat.not_lt_of_ge hLo (firstOccurrence_lt_length_of_mem x hp))
    · by_cases hm : x ∈ mid
      · exact hm
      · rw [firstOccurrence_append_of_not_mem x (mid ++ suff) hp,
            firstOccurrence_append_of_not_mem x suff hm] at hHi
        omega
  · intro hm
    have hp : x ∉ pref := by
      intro hp
      exact (List.pairwise_append.mp hUnique).2.2 x hp x
        (List.mem_append.mpr (Or.inl hm)) rfl
    rw [firstOccurrence_append_of_not_mem x (mid ++ suff) hp,
        firstOccurrence_append_of_mem x suff hm]
    have hLt := firstOccurrence_lt_length_of_mem x hm
    constructor <;> omega

/-! ### Ancestry intervals in the computed preorder -/

/-- The entry of a node is its zero-based first position in `dfsPreorder`. -/
def entry {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) (a : Fin N) : Nat :=
  firstOccurrence a (dfsPreorder root parent depth)

theorem entry_lt_length_dfsPreorder {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (a : Fin N) :
    entry root parent depth a < (dfsPreorder root parent depth).length :=
  firstOccurrence_lt_length_of_mem a (mem_dfsPreorder hTree a)

theorem entry_eq_length_of_dfsPreorder_split {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {a : Fin N}
    {pref suff : List (Fin N)}
    (hSplit : dfsPreorder root parent depth =
      pref ++ dfsSubtree root parent depth a ++ suff) :
    entry root parent depth a = pref.length := by
  have hUnique := nodup_dfsPreorder hTree
  have hSplit' : dfsPreorder root parent depth =
      pref ++ (dfsSubtree root parent depth a ++ suff) :=
    hSplit.trans (List.append_assoc pref (dfsSubtree root parent depth a) suff)
  rw [hSplit'] at hUnique
  have ha : a ∈ dfsSubtree root parent depth a :=
    (mem_dfsSubtree_iff hTree a a).mpr IsForestAncestor.refl
  have hNot : a ∉ pref := by
    intro hp
    exact (List.pairwise_append.mp hUnique).2.2 a hp a
      (List.mem_append.mpr (Or.inl ha)) rfl
  unfold entry
  rw [hSplit', dfsSubtree_unfold hTree a, List.cons_append]
  exact firstOccurrence_at_head_after_prefix a _ hNot

/-- The entry of `v` lies in `[entry(a), entry(a) + subtree(a).length)`. -/
def dfsIntervalContains {N : Nat} (root : Fin N) (parent : Fin N → Fin N)
    (depth : Fin N → Nat) (a v : Fin N) : Prop :=
  entry root parent depth a ≤ entry root parent depth v ∧
    entry root parent depth v <
      entry root parent depth a + (dfsSubtree root parent depth a).length

/-- Inclusive ancestry is exactly the half-open interval test on the
    computed DFS preorder. -/
theorem isForestAncestor_iff_dfsIntervalContains {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (a v : Fin N) :
    IsForestAncestor parent a v ↔ dfsIntervalContains root parent depth a v := by
  obtain ⟨pref, suff, hSplit⟩ := exists_split_dfsPreorder hTree a
  have hUnique := nodup_dfsPreorder hTree
  rw [hSplit] at hUnique
  unfold dfsIntervalContains
  rw [entry_eq_length_of_dfsPreorder_split hTree hSplit]
  change IsForestAncestor parent a v ↔
    (pref.length ≤ firstOccurrence v (dfsPreorder root parent depth) ∧
      firstOccurrence v (dfsPreorder root parent depth) <
        pref.length + (dfsSubtree root parent depth a).length)
  rw [hSplit]
  exact (mem_dfsSubtree_iff hTree a v).symm.trans
    (firstOccurrence_in_middle_iff v hUnique).symm

theorem dfsIntervalContains_self {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) (a : Fin N) :
    dfsIntervalContains root parent depth a a :=
  (isForestAncestor_iff_dfsIntervalContains hTree a a).mp IsForestAncestor.refl

/-- If a node occurs at the right endpoint, it is not a descendant of `a`. -/
theorem not_isForestAncestor_of_entry_eq_right_endpoint {N : Nat} {root : Fin N}
    {parent : Fin N → Fin N} {depth : Fin N → Nat}
    (hTree : ValidDepthTree root parent depth) {a v : Fin N}
    (hEnd : entry root parent depth v =
      entry root parent depth a + (dfsSubtree root parent depth a).length) :
    ¬ IsForestAncestor parent a v := by
  intro hAnc
  have hLt := ((isForestAncestor_iff_dfsIntervalContains hTree a v).mp hAnc).2
  exact (Nat.ne_of_lt hLt) hEnd

/-! ### Specialization to real proper-loss nodes and quotient labels -/

/-- For an existing real cut-pair node, inclusive ancestry of the forest
    label of `y` is the same computed interval test. -/
theorem buildProperLossForest_ancestor_iff_interval_of_node {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {a : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P : CutPair H}
    (_ha : (buildProperLossForest H rank).nodeKey? a = some P)
    (y : Fin H.vertexCount) :
    let F := buildProperLossForest H rank
    IsForestAncestor F.parent a (F.label y) ↔
      dfsIntervalContains F.rootNode F.parent F.depth a (F.label y) :=
  isForestAncestor_iff_dfsIntervalContains
    (buildProperLossForest_validDepthTree rankArc flat) a
    ((buildProperLossForest H rank).label y)

/-- Under the semantic forest theorem's hypotheses, the interval test for the
    given real node is equivalent to the exact proper-loss predicate. -/
theorem buildProperLossForest_properLoss_iff_interval_of_node {H : LabelledQuotient}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v : Fin H.vertexCount, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Fin H.vertexCount, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {a : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {P : CutPair H}
    (ha : (buildProperLossForest H rank).nodeKey? a = some P)
    (y : Fin H.vertexCount) :
    let F := buildProperLossForest H rank
    H.ProperLoss P y ↔ dfsIntervalContains F.rootNode F.parent F.depth a (F.label y) :=
  (buildProperLossForest_properLoss_iff_of_node rankArc distinctRanks flat ha y).trans
    (buildProperLossForest_ancestor_iff_interval_of_node rankArc flat ha y)

end LabelledQuotient

end PaperB
