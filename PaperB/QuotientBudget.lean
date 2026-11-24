module

-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.QuotientBudget

universe u v w
variable {α : Type u} {β : Type v} {κ : Type w}

/-- Each input position emits zero or one output, even when entries repeat. -/
theorem length_filterMap_le (emit : α → Option β) (xs : List α) :
    (xs.filterMap emit).length ≤ xs.length := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons x xs ih =>
    cases h : emit x with
    | none =>
      simpa [List.filterMap, h] using Nat.le_trans ih (Nat.le_succ xs.length)
    | some y =>
      simpa [List.filterMap, h] using Nat.succ_le_succ ih

/-- One bucket per enumerated key, in key order. Each bucket preserves
the order and multiplicity of its matching input occurrences. -/
def buckets [DecidableEq κ] (key : β → κ) (keys : List κ) (xs : List β) :
    List (List β) :=
  keys.map (fun k => xs.filter (fun x => decide (key x = k)))

def bucketTotal [DecidableEq κ] (key : β → κ) (keys : List κ)
    (xs : List β) : Nat :=
  ((buckets key keys xs).map List.length).sum

private theorem no_matches [DecidableEq κ] (q : κ) (keys : List κ)
    (h : q ∉ keys) :
    (keys.filter (fun k => decide (q = k))).length = 0 := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    have hne : q ≠ k := fun e => h (List.mem_cons.mpr (Or.inl e))
    have ht : q ∉ ks := fun m => h (List.mem_cons.mpr (Or.inr m))
    simp [List.filter, hne, ih ht]

/-- A present key matches exactly one position in a duplicate-free enumeration. -/
theorem unique_match_count [DecidableEq κ] (q : κ) (keys : List κ)
    (hn : keys.Nodup) (hm : q ∈ keys) :
    (keys.filter (fun k => decide (q = k))).length = 1 := by
  induction keys with
  | nil => simp at hm
  | cons k ks ih =>
    have hh := List.nodup_cons.mp hn
    by_cases e : q = k
    · subst q
      simp [List.filter, no_matches k ks hh.1]
    · have ht : q ∈ ks := (List.mem_cons.mp hm).resolve_left e
      simp [List.filter, e, ih hh.2 ht]

private theorem bucketTotal_nil [DecidableEq κ] (key : β → κ)
    (keys : List κ) : bucketTotal key keys [] = 0 := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simpa only [bucketTotal, buckets, List.map_cons, List.sum_cons,
      List.filter_nil, List.length_nil, Nat.zero_add] using ih

private theorem bucketTotal_cons [DecidableEq κ] (key : β → κ)
    (keys : List κ) (x : β) (xs : List β) :
    bucketTotal key keys (x :: xs) =
      (keys.filter (fun k => decide (key x = k))).length +
        bucketTotal key keys xs := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    simp only [bucketTotal, buckets, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    by_cases h : key x = k <;>
      simp [List.filter, h, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Exact accounting for complete, duplicate-free key enumeration. -/
theorem bucketTotal_eq_length [DecidableEq κ] (key : β → κ)
    (keys : List κ) (xs : List β) (hn : keys.Nodup)
    (hc : ∀ x ∈ xs, key x ∈ keys) :
    bucketTotal key keys xs = xs.length := by
  induction xs with
  | nil => exact bucketTotal_nil key keys
  | cons x xs ih =>
    have hx : key x ∈ keys := hc x (List.Mem.head xs)
    have ht : ∀ y ∈ xs, key y ∈ keys :=
      fun y hy => hc y (List.Mem.tail x hy)
    simp only [bucketTotal_cons, unique_match_count (key x) keys hn hx,
      ih ht, List.length_cons, Nat.add_comm 1]

/-- EX1.3: the grouped occurrence count is exactly the emitted count and is
bounded by the original arc occurrence count. This is not a runtime bound. -/
theorem emitted_bucket_budget [DecidableEq κ] (emit : α → Option (κ × β))
    (arcs : List α) (keys : List κ) (hn : keys.Nodup)
    (hc : ∀ p ∈ arcs.filterMap emit, p.1 ∈ keys) :
    bucketTotal Prod.fst keys (arcs.filterMap emit) = (arcs.filterMap emit).length ∧
    bucketTotal Prod.fst keys (arcs.filterMap emit) ≤ arcs.length := by
  have he := bucketTotal_eq_length Prod.fst keys (arcs.filterMap emit) hn hc
  refine ⟨he, ?_⟩
  rw [he]
  exact length_filterMap_le emit arcs

/-- One root record and at most one child record per input position. -/
theorem root_child_budget (root : α → β) (child : α → Option κ)
    (vertices : List α) :
    (vertices.map root).length + (vertices.filterMap child).length ≤
      2 * vertices.length := by
  calc
    _ ≤ vertices.length + vertices.length := by
      rw [List.length_map]
      exact Nat.add_le_add_left (length_filterMap_le child vertices) vertices.length
    _ = 2 * vertices.length := by
      rw [show (2 : Nat) = 1 + 1 from rfl, Nat.add_mul, Nat.one_mul]

private theorem globalOccurrenceCount_le_one {K : Type _} {B : Type _}
    (f : K → Option B) (roots : List K) (hn : roots.Nodup)
    (huniq : ∀ {r s : K} {b c : B}, f r = some b → f s = some c → r = s) :
    (roots.map (fun r => if (f r).isSome then (1 : Nat) else 0)).sum ≤ 1 := by
  have zero_of_none (rs : List K) (hz : ∀ s ∈ rs, f s = none) :
      (rs.map (fun s => if (f s).isSome then (1 : Nat) else 0)).sum = 0 := by
    induction rs with
    | nil => rfl
    | cons s ss ih =>
      have hs := hz s (List.mem_cons.mpr (Or.inl rfl))
      have ht := ih (fun t hm => hz t (List.mem_cons.mpr (Or.inr hm)))
      rw [List.map_cons, List.sum_cons, ht]
      simp [hs]
  induction roots with
  | nil => simp
  | cons r rs ih =>
    have hn' := List.nodup_cons.mp hn
    cases hr : f r with
    | none =>
      simpa [List.sum_cons, hr, Option.isSome] using ih hn'.2
    | some b =>
      have hz : ∀ s ∈ rs, f s = none := by
        intro s hs
        cases ht : f s with
        | none => rfl
        | some c =>
          have hsr : s = r := huniq ht hr
          exact (hn'.1 (hsr ▸ hs)).elim
      rw [List.map_cons, List.sum_cons, zero_of_none rs hz]
      simp [hr, Option.isSome]

private theorem globalOccurrenceSum_cons {K : Type _} {A : Type _} {B : Type _}
    (roots : List K) (emit : K → A → Option B) (a : A) (xs : List A) :
    (roots.map (fun r => ((a :: xs).filterMap (emit r)).length)).sum =
      (roots.map (fun r => if (emit r a).isSome then (1 : Nat) else 0)).sum +
        (roots.map (fun r => (xs.filterMap (emit r)).length)).sum := by
  induction roots with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    cases h : emit r a <;>
      simp [List.filterMap, h, Option.isSome, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]

/-- Over distinct roots, each physical occurrence contributes at most one output. -/
theorem sum_filterMap_length_le_length_of_nodup
    {K : Type _} {A : Type _} {B : Type _}
    (roots : List K) (xs : List A) (emit : K → A → Option B)
    (hn : roots.Nodup)
    (huniq : ∀ {r s : K} {a : A} {b c : B},
      emit r a = some b → emit s a = some c → r = s) :
    (roots.map (fun r => (xs.filterMap (emit r)).length)).sum ≤ xs.length := by
  induction xs with
  | nil =>
    clear hn huniq
    induction roots with
    | nil => simp
    | cons r rs ih => simpa [List.filterMap, List.sum_cons] using ih
  | cons a xs ih =>
    rw [globalOccurrenceSum_cons, Nat.add_comm, List.length_cons]
    exact Nat.add_le_add ih
      (globalOccurrenceCount_le_one (fun r => emit r a) roots hn
        (fun hr hs => huniq (a := a) hr hs))

end PaperB.QuotientBudget
