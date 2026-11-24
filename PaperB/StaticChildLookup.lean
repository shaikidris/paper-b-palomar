module

public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.StaticChildLookup

universe u

structure Child (α : Type u) where
  id    : α
  entry : Nat
  stop  : Nat

variable {α : Type u}

def childAt (a : Array (Child α)) (i : Fin a.size) : Child α :=
  a[i.val]'(i.isLt)

def Contains (c : Child α) (rank : Nat) : Prop :=
  c.entry ≤ rank ∧ rank < c.stop

/-- Nonempty intervals, ordered and disjoint. Adjacent intervals may touch. -/
def Valid (a : Array (Child α)) : Prop :=
  (∀ i : Fin a.size, (childAt a i).entry < (childAt a i).stop) ∧
  (∀ i j : Fin a.size, i.val < j.val →
    (childAt a i).stop ≤ (childAt a j).entry)

theorem entry_strict {a : Array (Child α)} (h : Valid a)
    (i j : Fin a.size) (hij : i.val < j.val) :
    (childAt a i).entry < (childAt a j).entry :=
  Nat.lt_of_lt_of_le (h.1 i) (h.2 i j hij)

theorem valid_of_adjacent {a : Array (Child α)}
    (hne : ∀ i : Fin a.size, (childAt a i).entry < (childAt a i).stop)
    (hadj : ∀ i j : Fin a.size, i.val + 1 = j.val →
      (childAt a i).stop ≤ (childAt a j).entry) :
    Valid a := by
  refine ⟨hne, ?_⟩
  intro i j hij
  have advance : ∀ (d : Nat) (k : Fin a.size), k.val = i.val + (d + 1) →
      (childAt a i).stop ≤ (childAt a k).entry := by
    intro d
    induction d with
    | zero =>
        intro k hk
        exact hadj i k hk.symm
    | succ d ih =>
        intro k hk
        have hm : i.val + (d + 1) < a.size := by
          have hb := k.isLt
          omega
        let m : Fin a.size := ⟨i.val + (d + 1), hm⟩
        have hmk : m.val + 1 = k.val := by
          change i.val + (d + 1) + 1 = k.val
          omega
        exact Nat.le_trans (ih m rfl)
          (Nat.le_trans (Nat.le_of_lt (hne m)) (hadj m k hmk))
  exact advance (j.val - i.val - 1) j (by omega)

/-- One packed record per element of the input sibling bucket. -/
def pack (ids : Array α) (ent out : α → Nat) : Array (Child α) :=
  ids.map fun id => ⟨id, ent id, out id⟩

@[simp] theorem pack_size (ids : Array α) (ent out : α → Nat) :
    (pack ids ent out).size = ids.size := by
  simp [pack]

theorem pack_valid (ids : Array α) (ent out : α → Nat)
    (hne : ∀ (i : Nat) (hi : i < ids.size),
      ent (ids[i]'hi) < out (ids[i]'hi))
    (hadj : ∀ (i j : Nat) (hi : i < ids.size) (hj : j < ids.size),
      i + 1 = j → out (ids[i]'hi) ≤ ent (ids[j]'hj)) :
    Valid (pack ids ent out) := by
  apply valid_of_adjacent
  · intro i
    have hi : i.val < ids.size := by simpa using i.isLt
    simpa [childAt, pack, Array.getElem_map] using hne i.val hi
  · intro i j hij
    have hi : i.val < ids.size := by simpa using i.isLt
    have hj : j.val < ids.size := by simpa using j.isLt
    simpa [childAt, pack, Array.getElem_map] using
      hadj i.val j.val hi hj hij

/-
A costed variant of PrefixProbe.search. Each call to `p` supplies its
answer and its charge. The let binding shares that single call.
-/
private def bisect (p : Nat → Bool × Nat) : Nat → Nat → Nat → Nat × Nat
  | 0, lo, _ => (lo, 0)
  | fuel + 1, lo, hi =>
      if hi ≤ lo + 1 then (lo, 0)
      else
        let mid := lo + (hi - lo) / 2
        let test := p mid
        let r := if test.1 = true then bisect p fuel mid hi
                 else bisect p fuel lo mid
        (r.1, r.2 + test.2)

private theorem bisect_cost_le (p : Nat → Bool × Nat)
    (hp : ∀ k, (p k).2 ≤ 1) (fuel lo hi : Nat) :
    (bisect p fuel lo hi).2 ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => simp [bisect]
  | succ fuel ih =>
      by_cases hs : hi ≤ lo + 1
      · simp [bisect, hs]
      · let mid := lo + (hi - lo) / 2
        by_cases hm : (p (lo + (hi - lo) / 2)).1 = true
        · simp only [bisect, ite_eq_right hs, ite_eq_left hm]
          exact Nat.add_le_add (ih mid hi) (hp mid)
        · simp only [bisect, ite_eq_right hs, ite_eq_right hm]
          exact Nat.add_le_add (ih lo mid) (hp mid)

private theorem bisect_cutoff (p : Nat → Bool × Nat) (fuel lo hi : Nat)
    (hw : hi - lo ≤ 2 ^ fuel) (hlt : lo < hi)
    (hlo : (p lo).1 = true) (hhi : (p hi).1 = false) :
    let k := (bisect p fuel lo hi).1
    lo ≤ k ∧ k < hi ∧ (p k).1 = true ∧ (p (k + 1)).1 = false := by
  induction fuel generalizing lo hi with
  | zero =>
      simp only [Nat.pow_zero] at hw
      have he : hi = lo + 1 := by omega
      change lo ≤ lo ∧ lo < hi ∧ (p lo).1 = true ∧ (p (lo + 1)).1 = false
      exact ⟨Nat.le_refl _, hlt, hlo, by simpa only [he] using hhi⟩
  | succ fuel ih =>
      by_cases hs : hi ≤ lo + 1
      · have he : hi = lo + 1 := by omega
        simp only [bisect, ite_eq_left hs]
        exact ⟨Nat.le_refl _, hlt, hlo, by simpa only [he] using hhi⟩
      · rw [Nat.pow_succ] at hw
        let mid := lo + (hi - lo) / 2
        have hl : lo < mid := by dsimp only [mid]; omega
        have hr : mid < hi := by dsimp only [mid]; omega
        have hwl : mid - lo ≤ 2 ^ fuel := by dsimp only [mid]; omega
        have hwr : hi - mid ≤ 2 ^ fuel := by dsimp only [mid]; omega
        cases hm : (p mid).1 with
        | false =>
            have hm' : (p (lo + (hi - lo) / 2)).1 = false := hm
            have hn : ¬ ((p (lo + (hi - lo) / 2)).1 = true) := by
              simp [hm']
            simp only [bisect, ite_eq_right hs, ite_eq_right hn]
            obtain ⟨hkl, hkm, hkt, hkf⟩ := ih lo mid hwl hl hlo hm
            exact ⟨hkl, Nat.lt_trans hkm hr, hkt, hkf⟩
        | true =>
            have hm' : (p (lo + (hi - lo) / 2)).1 = true := hm
            simp only [bisect, ite_eq_right hs, ite_eq_left hm']
            obtain ⟨hmk, hkh, hkt, hkf⟩ := ih mid hi hwr hr hm hhi
            exact ⟨Nat.le_trans (Nat.le_of_lt hl) hmk, hkh, hkt, hkf⟩

/--
Offset 0 is the true sentinel; offset `i + 1` tests child `i`.
The right sentinel is `a.size + 1`. A charge of 1 represents both one
record read and one rank comparison. Sentinel cases do neither.
-/
def probe (a : Array (Child α)) (rank : Nat) : Nat → Bool × Nat
  | 0 => (true, 0)
  | i + 1 =>
      if hi : i < a.size then
        let c := a[i]'hi
        (decide (c.entry ≤ rank), 1)
      else (false, 0)

theorem probe_cost_le (a : Array (Child α)) (rank k : Nat) :
    (probe a rank k).2 ≤ 1 := by
  cases k with
  | zero => simp [probe]
  | succ i => by_cases hi : i < a.size <;> simp [probe, hi]

private theorem probe_at (a : Array (Child α)) (rank : Nat) (i : Fin a.size) :
    (probe a rank (i.val + 1)).1 = true ↔ (childAt a i).entry ≤ rank := by
  simp [probe, i.isLt, childAt]

private def run (a : Array (Child α)) (rank : Nat) : Nat × Nat :=
  bisect (probe a rank) (Nat.log2 (a.size + 1) + 1) 0 (a.size + 1)

private theorem run_spec (a : Array (Child α)) (rank : Nat) :
    let k := (run a rank).1
    k < a.size + 1 ∧ (probe a rank k).1 = true ∧
      (probe a rank (k + 1)).1 = false := by
  have hn : a.size + 1 ≠ 0 := by omega
  have hp : a.size + 1 < 2 ^ (Nat.log2 (a.size + 1) + 1) :=
    (Nat.log2_lt hn).mp (Nat.lt_succ_self _)
  have hw : a.size + 1 - 0 ≤ 2 ^ (Nat.log2 (a.size + 1) + 1) := by
    simpa only [Nat.sub_zero] using Nat.le_of_lt hp
  obtain ⟨_, hlt, ht, hf⟩ :=
    bisect_cutoff (probe a rank) (Nat.log2 (a.size + 1) + 1)
      0 (a.size + 1) hw (by omega) (by rfl) (by simp [probe])
  exact ⟨hlt, ht, hf⟩

/-- The cut is the last qualifying entry, with 0 meaning no qualifying entry. -/
theorem last_entry (a : Array (Child α)) (rank : Nat) (h : Valid a)
    (i : Fin a.size) :
    (childAt a i).entry ≤ rank ↔ i.val + 1 ≤ (run a rank).1 := by
  let k := (run a rank).1
  change (childAt a i).entry ≤ rank ↔ i.val + 1 ≤ k
  have hs : k < a.size + 1 ∧ (probe a rank k).1 = true ∧
      (probe a rank (k + 1)).1 = false := run_spec a rank
  obtain ⟨hk, ht, hf⟩ := hs
  constructor
  · intro he
    by_cases hi : i.val + 1 ≤ k
    · exact hi
    · have hj : k < a.size := by
        have hb := i.isLt
        omega
      let j : Fin a.size := ⟨k, hj⟩
      have hje : (childAt a j).entry ≤ rank := by
        by_cases hji : j.val = i.val
        · have heq : j = i := Fin.ext hji
          simpa only [heq] using he
        · have hlt : j.val < i.val := by
            change k ≠ i.val at hji
            change k < i.val
            omega
          exact Nat.le_trans (Nat.le_of_lt (entry_strict h j i hlt)) he
      have hp : (probe a rank (k + 1)).1 = true :=
        (probe_at a rank j).2 hje
      simp [hf] at hp
  · intro hi
    let j : Fin a.size := ⟨k - 1, by omega⟩
    have hjk : j.val + 1 = k := by
      change k - 1 + 1 = k
      omega
    have hje : (childAt a j).entry ≤ rank :=
      (probe_at a rank j).1 (by rw [hjk]; exact ht)
    by_cases hij : i.val = j.val
    · have he : i = j := Fin.ext hij
      simpa only [he] using hje
    · have hlt : i.val < j.val := by omega
      exact Nat.le_trans (Nat.le_of_lt (entry_strict h i j hlt)) hje

private def finish (a : Array (Child α)) (rank : Nat) :
    Nat → Option (Child α) × Nat
  | 0 => (none, 0)
  | i + 1 =>
      if hi : i < a.size then
        let c := a[i]'hi
        ((if rank < c.stop then some c else none), 1)
      else (none, 0)

private theorem finish_at (a : Array (Child α)) (rank : Nat) (i : Fin a.size) :
    (finish a rank (i.val + 1)).1 =
      (if rank < (childAt a i).stop then some (childAt a i) else none) := by
  have hb : i.val < a.size := i.isLt
  by_cases hs : rank < (a[i.val]'hb).stop <;>
    simp [finish, hb, childAt, hs]

private theorem finish_cost_le (a : Array (Child α)) (rank k : Nat) :
    (finish a rank k).2 ≤ 1 := by
  cases k with
  | zero => simp [finish]
  | succ i => by_cases hi : i < a.size <;> simp [finish, hi]

/-- The second component counts record reads, and also rank comparisons. -/
def lookupMeasured (a : Array (Child α)) (rank : Nat) : Option (Child α) × Nat :=
  let b := run a rank
  let f := finish a rank b.1
  (f.1, b.2 + f.2)

def lookup (a : Array (Child α)) (rank : Nat) : Option (Child α) :=
  (lookupMeasured a rank).1

/--
In the array-access cost model, there is at most one record read and one
rank comparison per probe, and at most one of each for the final check.
Index and loop guards add only constant work per search step.
-/
theorem lookup_cost_le (a : Array (Child α)) (rank : Nat) :
    (lookupMeasured a rank).2 ≤ Nat.log2 (a.size + 1) + 2 := by
  have hb : (run a rank).2 ≤ Nat.log2 (a.size + 1) + 1 :=
    bisect_cost_le (probe a rank) (probe_cost_le a rank) _ _ _
  have hf := finish_cost_le a rank (run a rank).1
  change (run a rank).2 + (finish a rank (run a rank).1).2 ≤ _
  omega

private theorem cut_eq_of_contains {a : Array (Child α)} {rank : Nat}
    (h : Valid a) (i : Fin a.size) (hi : Contains (childAt a i) rank) :
    (run a rank).1 = i.val + 1 := by
  let k := (run a rank).1
  change k = i.val + 1
  have hlo : i.val + 1 ≤ k := (last_entry a rank h i).1 hi.1
  have hbound : k < a.size + 1 := (run_spec a rank).1
  let j : Fin a.size := ⟨k - 1, by omega⟩
  have hjk : j.val + 1 = k := by
    change k - 1 + 1 = k
    omega
  have hje : (childAt a j).entry ≤ rank :=
    (last_entry a rank h j).2 (by
      change j.val + 1 ≤ k
      exact Nat.le_of_eq hjk)
  by_cases hij : i.val < j.val
  · have hsep := h.2 i j hij
    have hstop := hi.2
    omega
  · omega

theorem lookup_some_iff {a : Array (Child α)} (h : Valid a)
    (rank : Nat) (c : Child α) :
    lookup a rank = some c ↔
      ∃ i : Fin a.size, childAt a i = c ∧ Contains (childAt a i) rank := by
  change (finish a rank (run a rank).1).1 = some c ↔ _
  constructor
  · intro hr
    have hb := (run_spec a rank).1
    generalize hk : (run a rank).1 = k at hr
    cases k with
    | zero => simp [finish] at hr
    | succ k =>
        let i : Fin a.size := ⟨k, by omega⟩
        have he : (childAt a i).entry ≤ rank :=
          (last_entry a rank h i).2 (by
            change k + 1 ≤ (run a rank).1
            exact Nat.le_of_eq hk.symm)
        change (finish a rank (i.val + 1)).1 = some c at hr
        rw [finish_at] at hr
        by_cases hs : rank < (childAt a i).stop
        · have hr' : some (childAt a i) = some c := by
            simpa only [ite_eq_left hs] using hr
          exact ⟨i, Option.some.inj hr', ⟨he, hs⟩⟩
        · simp [hs] at hr
  · rintro ⟨i, he, hi⟩
    rw [cut_eq_of_contains h i hi, finish_at, ite_eq_left hi.2, he]

theorem lookup_none_iff {a : Array (Child α)} (h : Valid a) (rank : Nat) :
    lookup a rank = none ↔ ¬ ∃ i : Fin a.size, Contains (childAt a i) rank := by
  constructor
  · intro hn hex
    obtain ⟨i, hi⟩ := hex
    have hs := (lookup_some_iff h rank (childAt a i)).2 ⟨i, rfl, hi⟩
    simp [hn] at hs
  · intro hn
    cases hr : lookup a rank with
    | none => rfl
    | some c =>
        obtain ⟨i, _, hi⟩ := (lookup_some_iff h rank c).1 hr
        exact False.elim (hn ⟨i, hi⟩)

theorem contains_unique {a : Array (Child α)} (h : Valid a)
    {rank : Nat} {i j : Fin a.size}
    (hi : Contains (childAt a i) rank) (hj : Contains (childAt a j) rank) :
    i = j := by
  apply Fin.ext
  have hki := cut_eq_of_contains h i hi
  have hkj := cut_eq_of_contains h j hj
  omega

theorem lookup_at_entry {a : Array (Child α)} (h : Valid a) (i : Fin a.size) :
    lookup a (childAt a i).entry = some (childAt a i) :=
  (lookup_some_iff h _ _).2 ⟨i, rfl, ⟨Nat.le_refl _, h.1 i⟩⟩

/-- An exclusive end may be another child's entry, but is not this child's rank. -/
theorem lookup_at_stop_ne_self {a : Array (Child α)} (h : Valid a)
    (i : Fin a.size) :
    lookup a (childAt a i).stop ≠ some (childAt a i) := by
  intro hs
  obtain ⟨j, he, hj⟩ := (lookup_some_iff h _ _).1 hs
  rw [he] at hj
  exact (Nat.lt_irrefl _) hj.2

theorem lookup_at_parent {a : Array (Child α)} (h : Valid a)
    (parentEntry : Nat)
    (hp : ∀ i : Fin a.size, parentEntry < (childAt a i).entry) :
    lookup a parentEntry = none := by
  apply (lookup_none_iff h parentEntry).2
  rintro ⟨i, hi⟩
  exact (Nat.not_le_of_lt (hp i)) hi.1

theorem lookup_at_upper_bound {a : Array (Child α)} (h : Valid a)
    (upper : Nat) (hu : ∀ i : Fin a.size, (childAt a i).stop ≤ upper) :
    lookup a upper = none := by
  apply (lookup_none_iff h upper).2
  rintro ⟨i, hi⟩
  exact (Nat.not_lt_of_ge (hu i)) hi.2

theorem lookup_at_last_stop {a : Array (Child α)} (h : Valid a)
    (i : Fin a.size) (hlast : i.val + 1 = a.size) :
    lookup a (childAt a i).stop = none := by
  apply lookup_at_upper_bound h
  intro j
  by_cases he : j.val = i.val
  · have he' : j = i := Fin.ext he
    subst j
    exact Nat.le_refl _
  · have hj := j.isLt
    have hji : j.val < i.val := by omega
    exact Nat.le_trans (h.2 j i hji) (Nat.le_of_lt (h.1 i))

end PaperB.StaticChildLookup
