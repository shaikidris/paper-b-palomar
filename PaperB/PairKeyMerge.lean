module

public import PaperB.PairLookup

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PairLookup.KeyMerge

/-- List invariant for the recursive layer. Strictness rules out duplicates
within each input run. -/
inductive Increasing : List Key → Prop where
  | nil : Increasing []
  | cons {x : Key} {xs : List Key} :
      (∀ y ∈ xs, lexLess x y) → Increasing xs → Increasing (x :: xs)

theorem Increasing.head {x : Key} {xs : List Key}
    (h : Increasing (x :: xs)) : ∀ y ∈ xs, lexLess x y := by
  cases h with
  | cons hhead _ => exact hhead

theorem Increasing.tail {x : Key} {xs : List Key}
    (h : Increasing (x :: xs)) : Increasing xs := by
  cases h with
  | cons _ htail => exact htail

structure MergeResult where
  keys : List Key
  /-- One round compares the two current heads and consumes at least one. -/
  rounds : Nat
  /-- Actual number of `lexLess` tests, including the reverse test if made. -/
  comparisons : Nat
  /-- Rounds that consume both heads and emit just one key. -/
  ties : Nat

private def rest (xs : List Key) : MergeResult :=
  ⟨xs, 0, 0, 0⟩

private def emit (x : Key) (cost extra : Nat) (r : MergeResult) :
    MergeResult :=
  ⟨x :: r.keys, r.rounds + 1, r.comparisons + cost, r.ties + extra⟩

/-- Fuel is computed once, not at each recursive call. The zero-fuel
case can only be reached with both runs empty when called by `merge`. -/
private def mergeAux : Nat → List Key → List Key → MergeResult
  | 0, _, _ => rest []
  | _ + 1, [], ys => rest ys
  | _ + 1, x :: xs, [] => rest (x :: xs)
  | f + 1, x :: xs, y :: ys =>
      if lexLess x y then
        emit x 1 0 (mergeAux f xs (y :: ys))
      else if lexLess y x then
        emit y 2 0 (mergeAux f (x :: xs) ys)
      else
        emit x 2 1 (mergeAux f xs ys)

/-- Merge two sorted runs. An equal pair of heads contributes exactly one
output key. The untouched suffix is shared, rather than copied element by
element. The implementation uses a linear recursion stack. -/
def merge (xs ys : List Key) : MergeResult :=
  mergeAux (xs.length + ys.length) xs ys

structure MergeSpec (xs ys : List Key) (r : MergeResult) : Prop where
  mem_iff : ∀ k : Key, k ∈ r.keys ↔ k ∈ xs ∨ k ∈ ys
  increasing : Increasing r.keys
  /-- A round consumes one input cell, plus one more on a tie.
  This counts the scan before the untouched suffix is returned. -/
  scan_le : r.rounds + r.ties ≤ xs.length + ys.length
  product_le : r.rounds ≤ xs.length * ys.length
  rounds_le_comparisons : r.rounds ≤ r.comparisons
  comparisons_le_twice_rounds : r.comparisons ≤ 2 * r.rounds
  /-- Each tie accounts for exactly one removed input occurrence. -/
  length_charge : r.keys.length + r.ties = xs.length + ys.length

private theorem rest_right (ys : List Key) (h : Increasing ys) :
    MergeSpec [] ys (rest ys) := by
  refine ⟨?_, h, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rest]

private theorem rest_left (xs : List Key) (h : Increasing xs) :
    MergeSpec xs [] (rest xs) := by
  refine ⟨?_, h, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [rest]

private theorem eq_of_no_less {x y : Key}
    (hxy : ¬ lexLess x y) (hyx : ¬ lexLess y x) : x = y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  change ¬ (a < c ∨ (a = c ∧ b < d)) at hxy
  change ¬ (c < a ∨ (c = a ∧ d < b)) at hyx
  have hac : ¬ a < c := fun h => hxy (Or.inl h)
  have hca : ¬ c < a := fun h => hyx (Or.inl h)
  have h₁ : a = c := by omega
  have hbd : ¬ b < d := fun h => hxy (Or.inr ⟨h₁, h⟩)
  have hdb : ¬ d < b := fun h => hyx (Or.inr ⟨h₁.symm, h⟩)
  have h₂ : b = d := by omega
  cases h₁
  cases h₂
  rfl

private theorem product_left (m n : Nat) :
    m * (n + 1) + 1 ≤ (m + 1) * (n + 1) := by
  rw [Nat.add_mul m 1 (n + 1), Nat.one_mul]
  omega

private theorem product_right (m n : Nat) :
    (m + 1) * n + 1 ≤ (m + 1) * (n + 1) := by
  rw [Nat.mul_add (m + 1) n 1, Nat.mul_one]
  omega

private theorem product_both (m n : Nat) :
    m * n + 1 ≤ (m + 1) * (n + 1) := by
  calc
    m * n + 1 ≤ m * (n + 1) + 1 := by
      rw [Nat.mul_add m n 1, Nat.mul_one]
      omega
    _ ≤ (m + 1) * (n + 1) := product_left m n

private theorem emit_spec {xs ys us vs : List Key}
    {x : Key} {r : MergeResult} {cost extra : Nat}
    (hr : MergeSpec us vs r)
    (hmem : ∀ k : Key,
      (k ∈ xs ∨ k ∈ ys) ↔ k = x ∨ (k ∈ us ∨ k ∈ vs))
    (hbelow : ∀ k : Key, (k ∈ us ∨ k ∈ vs) → lexLess x k)
    (hlen : xs.length + ys.length = us.length + vs.length + 1 + extra)
    (hprod : us.length * vs.length + 1 ≤ xs.length * ys.length)
    (hcost₁ : 1 ≤ cost) (hcost₂ : cost ≤ 2) :
    MergeSpec xs ys (emit x cost extra r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    change (k ∈ x :: r.keys) ↔ k ∈ xs ∨ k ∈ ys
    rw [List.mem_cons, hr.mem_iff k, hmem k]
  · change Increasing (x :: r.keys)
    exact Increasing.cons
      (fun k hk => hbelow k ((hr.mem_iff k).mp hk)) hr.increasing
  · change r.rounds + 1 + (r.ties + extra) ≤ xs.length + ys.length
    have h := hr.scan_le
    omega
  · change r.rounds + 1 ≤ xs.length * ys.length
    exact Nat.le_trans (Nat.succ_le_succ hr.product_le) hprod
  · change r.rounds + 1 ≤ r.comparisons + cost
    have h := hr.rounds_le_comparisons
    omega
  · change r.comparisons + cost ≤ 2 * (r.rounds + 1)
    have h := hr.comparisons_le_twice_rounds
    omega
  · change r.keys.length + 1 + (r.ties + extra) = xs.length + ys.length
    have h := hr.length_charge
    omega

private theorem mergeAux_spec (fuel : Nat) (xs ys : List Key)
    (hf : xs.length + ys.length ≤ fuel)
    (hx : Increasing xs) (hy : Increasing ys) :
    MergeSpec xs ys (mergeAux fuel xs ys) := by
  induction fuel generalizing xs ys with
  | zero =>
    cases xs <;> cases ys
    · exact rest_right [] hy
    all_goals
      simp only [List.length_nil, List.length_cons] at hf <;> omega
  | succ f ih =>
    cases xs with
    | nil => exact rest_right ys hy
    | cons x xs =>
      cases ys with
      | nil => exact rest_left (x :: xs) hx
      | cons y ys =>
        by_cases hxy : lexLess x y
        · have hf' : xs.length + (y :: ys).length ≤ f := by
            simp only [List.length_cons] at hf ⊢
            omega
          have hr := ih xs (y :: ys) hf' hx.tail hy
          simp only [mergeAux, if_pos hxy]
          refine emit_spec hr ?_ ?_ ?_ ?_ (by decide) (by decide)
          · intro k
            simp only [List.mem_cons, or_assoc]
          · intro k hk
            rcases hk with hk | hk
            · exact hx.head k hk
            · rcases List.mem_cons.mp hk with hk | hk
              · subst k
                exact hxy
              · exact lexLess_trans hxy (hy.head k hk)
          · simp only [List.length_cons]
            omega
          · exact product_left xs.length ys.length
        · by_cases hyx : lexLess y x
          · have hf' : (x :: xs).length + ys.length ≤ f := by
              simp only [List.length_cons] at hf ⊢
              omega
            have hr := ih (x :: xs) ys hf' hx hy.tail
            simp only [mergeAux, if_neg hxy, if_pos hyx]
            refine emit_spec hr ?_ ?_ ?_ ?_ (by decide) (by decide)
            · intro k
              simp only [List.mem_cons]
              constructor
              · intro hk
                rcases hk with hk | (hk | hk)
                · exact Or.inr (Or.inl hk)
                · exact Or.inl hk
                · exact Or.inr (Or.inr hk)
              · intro hk
                rcases hk with hk | (hk | hk)
                · exact Or.inr (Or.inl hk)
                · exact Or.inl hk
                · exact Or.inr (Or.inr hk)
            · intro k hk
              rcases hk with hk | hk
              · rcases List.mem_cons.mp hk with hk | hk
                · subst k
                  exact hyx
                · exact lexLess_trans hyx (hx.head k hk)
              · exact hy.head k hk
            · simp only [List.length_cons]
              omega
            · exact product_right xs.length ys.length
          · have heq : x = y := eq_of_no_less hxy hyx
            subst y
            have hf' : xs.length + ys.length ≤ f := by
              simp only [List.length_cons] at hf
              omega
            have hr := ih xs ys hf' hx.tail hy.tail
            simp only [mergeAux, if_neg hxy]
            refine emit_spec hr ?_ ?_ ?_ ?_ (by decide) (by decide)
            · intro k
              simp only [List.mem_cons]
              constructor
              · intro hk
                rcases hk with (hk | hk) | (hk | hk)
                · exact Or.inl hk
                · exact Or.inr (Or.inl hk)
                · exact Or.inl hk
                · exact Or.inr (Or.inr hk)
              · intro hk
                rcases hk with hk | (hk | hk)
                · exact Or.inl (Or.inl hk)
                · exact Or.inl (Or.inr hk)
                · exact Or.inr (Or.inr hk)
            · intro k hk
              rcases hk with hk | hk
              · exact hx.head k hk
              · exact hy.head k hk
            · simp only [List.length_cons]
              omega
            · exact product_both xs.length ys.length

/-- Recursive-layer interface: use `increasing` for the next merge,
compose `mem_iff` for exact membership, and sum the local charges. -/
theorem merge_spec {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys) :
    MergeSpec xs ys (merge xs ys) :=
  mergeAux_spec (xs.length + ys.length) xs ys (Nat.le_refl _) hx hy

/-- Bounds on actual `lexLess` calls. For a balanced recursive layer,
the first bound is linear in the sum of that layer's input run lengths. -/
theorem merge_comparison_bounds {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys) :
    (merge xs ys).comparisons ≤ 2 * (xs.length + ys.length) ∧
    (merge xs ys).comparisons ≤ 2 * (xs.length * ys.length) := by
  have h := merge_spec hx hy
  have hscan := h.scan_le
  have hprod := h.product_le
  have hcmp := h.comparisons_le_twice_rounds
  constructor <;> omega

private theorem indexed_mem (xs : List Key) (i : Nat) (hi : i < xs.length) :
    xs[i]'hi ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      change x ∈ x :: xs
      exact List.mem_cons.mpr (Or.inl rfl)
    | succ i =>
      have hi' : i < xs.length := by
        simp only [List.length_cons] at hi
        omega
      change xs[i]'hi' ∈ x :: xs
      exact List.mem_cons.mpr (Or.inr (ih i hi'))

private theorem increasing_indexed {xs : List Key} (h : Increasing xs) :
    ∀ (i j : Nat) (hi : i < xs.length) (hj : j < xs.length),
      i < j → lexLess (xs[i]'hi) (xs[j]'hj) := by
  induction h with
  | nil =>
    intro i j hi hj hij
    simp at hi
  | @cons x xs hhead htail ih =>
    intro i j hi hj hij
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j < xs.length := by
        simp only [List.length_cons] at hj
        omega
      cases i with
      | zero =>
        change lexLess x (xs[j]'hj')
        exact hhead _ (indexed_mem xs j hj')
      | succ i =>
        have hi' : i < xs.length := by
          simp only [List.length_cons] at hi
          omega
        change lexLess (xs[i]'hi') (xs[j]'hj')
        exact ih i j hi' hj' (by omega)

/-- Convert only the final run to an array; intermediate runs can stay lists. -/
theorem increasing_toArray {xs : List Key} (h : Increasing xs) :
    StrictSorted xs.toArray := by
  intro i j hi hj hij
  have hi' : i < xs.length := by
    first | exact hi | simpa using hi
  have hj' : j < xs.length := by
    first | exact hj | simpa using hj
  first
  | exact increasing_indexed h i j hi' hj' hij
  | simpa using increasing_indexed h i j hi' hj' hij

def mergeToArray (xs ys : List Key) : Array Key :=
  (merge xs ys).keys.toArray

/-- Lookup-ready array with exactly the union of the two input key sets. -/
theorem mergeToArray_spec {xs ys : List Key}
    (hx : Increasing xs) (hy : Increasing ys) :
    StrictSorted (mergeToArray xs ys) ∧
      ∀ k : Key, k ∈ (mergeToArray xs ys).toList ↔ k ∈ xs ∨ k ∈ ys := by
  have h := merge_spec hx hy
  refine ⟨increasing_toArray h.increasing, ?_⟩
  intro k
  first
  | exact h.mem_iff k
  | simpa [mergeToArray] using h.mem_iff k

end PaperB.PairLookup.KeyMerge
