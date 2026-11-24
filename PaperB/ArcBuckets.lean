module

public import Std
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX51

universe u v

variable {α : Type u} {β : Type v} {B : Nat}

/-- The size proof is erased. Both passes update this same array of lists. -/
structure Rows (B : Nat) (β : Type v) where
  cells : Array (List β)
  size_eq : cells.size = B

namespace Rows

def row (s : Rows B β) (i : Fin B) : List β :=
  s.cells[i.val]'(by simpa only [s.size_eq] using i.isLt)

def empty : Rows B β :=
  ⟨Array.replicate B [], by simp⟩

def write (s : Rows B β) (i : Fin B) (xs : List β) : Rows B β :=
  ⟨s.cells.set i.val xs (by simpa only [s.size_eq] using i.isLt),
    by simpa using s.size_eq⟩

theorem row_empty (i : Fin B) : (empty : Rows B β).row i = [] := by
  simp [row, empty]

theorem row_write (s : Rows B β) (i j : Fin B) (xs : List β) :
    (s.write i xs).row j = if i = j then xs else s.row j := by
  by_cases h : i = j
  · subst j
    simp [row, write]
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e)
    simp [row, write, Array.getElem_set, h, hv]

end Rows

/--
Source-level charges, not machine load/store counts. A finish visit does
one bucket read and one bucket write, separate from the scatter charges.
-/
structure Work where
  initCells : Nat
  scatterReads : Nat
  scatterWrites : Nat
  reverseCells : Nat
  finishRows : Nat
  deriving Repr

/-- Each nonempty branch selects once, reads one row, and writes one row. -/
private def scatter (key : α → Fin B) (emit : α → β) :
    List α → Rows B β → Nat → Nat → Rows B β × (Nat × Nat)
  | [], s, reads, writes => (s, (reads, writes))
  | a :: xs, s, reads, writes =>
      let i := key a
      let old := s.row i
      scatter key emit xs (s.write i (emit a :: old))
        (reads + 1) (writes + 1)

/-- Charge a reverse cell in the same branch that consumes it. -/
private def reverseCharged : List β → List β → Nat → List β × Nat
  | [], acc, charge => (acc, charge)
  | x :: xs, acc, charge => reverseCharged xs (x :: acc) (charge + 1)

private theorem reverseCharged_eq (xs acc : List β) (charge : Nat) :
    reverseCharged xs acc charge = (xs.reverse ++ acc, charge + xs.length) := by
  induction xs generalizing acc charge with
  | nil => simp [reverseCharged]
  | cons x xs ih =>
      rw [reverseCharged, ih]
      simp [List.reverse_cons, List.append_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Finish rows `t-1` through `0`, overwriting the scatter array. -/
private def finish :
    (t : Nat) → t ≤ B → Rows B β → Nat → Rows B β × Nat
  | 0, _, s, charge => (s, charge)
  | t + 1, h, s, charge =>
      let i : Fin B := ⟨t, by omega⟩
      let r := reverseCharged (s.row i) [] charge
      finish t (by omega) (s.write i r.1) r.2

/--
Stable grouping with an optional payload projection. Under unit-cost
indexing, counters, `key`, and `emit`, the charged work is linear in
`B + xs.length`. No filter or length pass runs in this routine.
-/
def groupMap (key : α → Fin B) (emit : α → β) (xs : List α) :
    Rows B β × Work :=
  let p := scatter key emit xs Rows.empty 0 0
  let reads := p.2.1
  let writes := p.2.2
  let q := finish B (Nat.le_refl B) p.1 0
  (q.1, ⟨B, reads, writes, q.2, B⟩)

def group (key : α → Fin B) (xs : List α) : Rows B α × Work :=
  groupMap key id xs

/- The following mass functions are used only in proofs. -/

private def prefixMass (weight : Fin B → Nat) : (t : Nat) → t ≤ B → Nat
  | 0, _ => 0
  | t + 1, h => prefixMass weight t (by omega) + weight ⟨t, by omega⟩

private def mass (t : Nat) (h : t ≤ B) (s : Rows B β) : Nat :=
  prefixMass (fun i => (s.row i).length) t h

private theorem prefixMass_zero (t : Nat) (h : t ≤ B) :
    prefixMass (fun _ : Fin B => 0) t h = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have ht : t ≤ B := by omega
      change prefixMass (fun _ : Fin B => 0) t ht + 0 = 0
      rw [ih ht]

private theorem prefixMass_bump (weight : Fin B → Nat) (i : Fin B)
    (t : Nat) (h : t ≤ B) :
    prefixMass (fun j => weight j + (if i = j then 1 else 0)) t h =
      prefixMass weight t h + (if i.val < t then 1 else 0) := by
  induction t with
  | zero => simp [prefixMass]
  | succ t ih =>
      have ht : t ≤ B := by omega
      let j : Fin B := ⟨t, by omega⟩
      change
        prefixMass (fun q => weight q + (if i = q then 1 else 0)) t ht +
            (weight j + (if i = j then 1 else 0)) =
          (prefixMass weight t ht + weight j) +
            (if i.val < t + 1 then 1 else 0)
      rw [ih ht]
      by_cases e : i = j
      · subst i
        have hlt : j.val < t + 1 := Nat.lt_succ_self t
        have hnlt : ¬ j.val < t := Nat.lt_irrefl t
        rw [ite_eq_right hnlt, ite_eq_left hlt]
        simp [Nat.add_assoc]
      · have hv : i.val ≠ t := fun eq => e (Fin.ext eq)
        have hs : i.val < t + 1 ↔ i.val < t := by omega
        simp only [ite_eq_right e, hs, Nat.add_zero]
        exact Nat.add_right_comm _ _ _

private theorem mass_empty (B : Nat) :
    mass B (Nat.le_refl B) (Rows.empty : Rows B β) = 0 := by
  simp only [mass, Rows.row_empty, List.length_nil, prefixMass_zero]

private theorem mass_write_cons (s : Rows B β) (i : Fin B) (x : β) :
    mass B (Nat.le_refl B) (s.write i (x :: s.row i)) =
      mass B (Nat.le_refl B) s + 1 := by
  have hw :
      (fun j : Fin B => ((s.write i (x :: s.row i)).row j).length) =
        (fun j => (s.row j).length + (if i = j then 1 else 0)) := by
    funext j
    by_cases e : i = j
    · subst j
      simp [Rows.row_write, Nat.add_comm]
    · simp [Rows.row_write, e]
  simp only [mass, hw, prefixMass_bump, ite_eq_left i.isLt]

private theorem scatter_row (key : α → Fin B) (emit : α → β)
    (xs : List α) (s : Rows B β) (reads writes : Nat) (j : Fin B) :
    (scatter key emit xs s reads writes).1.row j =
      ((xs.filter (fun a => decide (key a = j))).map emit).reverse ++ s.row j := by
  induction xs generalizing s reads writes with
  | nil => simp [scatter]
  | cons a xs ih =>
      rw [scatter, ih]
      by_cases e : key a = j
      · simp [Rows.row_write, e, List.reverse_cons, List.append_assoc]
      · simp [Rows.row_write, e]

private theorem scatter_counts (key : α → Fin B) (emit : α → β)
    (xs : List α) (s : Rows B β) (reads writes : Nat) :
    let p := scatter key emit xs s reads writes
    p.2.1 = reads + xs.length ∧
      p.2.2 = writes + xs.length ∧
      mass B (Nat.le_refl B) p.1 = mass B (Nat.le_refl B) s + xs.length := by
  induction xs generalizing s reads writes with
  | nil => simp [scatter]
  | cons a xs ih =>
      simp only [scatter, List.length_cons]
      obtain ⟨hr, hw, hm⟩ :=
        ih (s.write (key a) (emit a :: s.row (key a))) (reads + 1) (writes + 1)
      rw [hr, hw, hm, mass_write_cons]
      exact ⟨by omega, by omega, by omega⟩

private theorem finish_spec (t : Nat) (h : t ≤ B) (s : Rows B β) (charge : Nat) :
    (∀ j : Fin B, (finish t h s charge).1.row j =
      (if j.val < t then (s.row j).reverse else s.row j)) ∧
    (finish t h s charge).2 = charge + mass t h s := by
  induction t generalizing s charge with
  | zero => simp [finish, mass, prefixMass]
  | succ t ih =>
      have ht : t ≤ B := by omega
      let i : Fin B := ⟨t, by omega⟩
      let s' := s.write i (s.row i).reverse
      simp only [finish, reverseCharged_eq, List.append_nil]
      change
        (∀ j : Fin B, (finish t ht s' (charge + (s.row i).length)).1.row j =
          (if j.val < t + 1 then (s.row j).reverse else s.row j)) ∧
        (finish t ht s' (charge + (s.row i).length)).2 =
          charge + mass (t + 1) h s
      obtain ⟨hr, hc⟩ := ih ht s' (charge + (s.row i).length)
      constructor
      · intro j
        rw [hr j]
        by_cases e : i = j
        · subst j
          have hv : i.val = t := rfl
          simp [s', Rows.row_write, hv]
        · have hv : j.val ≠ t := fun eq => e (Fin.ext eq.symm)
          have hs : j.val < t + 1 ↔ j.val < t := by omega
          simp [s', Rows.row_write, e, hs]
      · rw [hc]
        have hw : (fun j : Fin B => (s'.row j).length) =
            (fun j : Fin B => (s.row j).length) := by
          funext j
          by_cases e : i = j
          · subst j
            simp [s', Rows.row_write]
          · simp [s', Rows.row_write, e]
        change
          charge + (s.row i).length +
              prefixMass (fun j : Fin B => (s'.row j).length) t ht =
            charge + (prefixMass (fun j : Fin B => (s.row j).length) t ht +
              (s.row i).length)
        rw [hw]
        omega

/-- List equality gives stable order, including distinct occurrences with equal labels. -/
theorem groupMap_row (key : α → Fin B) (emit : α → β)
    (xs : List α) (j : Fin B) :
    (groupMap key emit xs).1.row j =
      (xs.filter (fun a => decide (key a = j))).map emit := by
  let s : Rows B β := Rows.empty
  let p := scatter key emit xs s 0 0
  change (finish B (Nat.le_refl B) p.1 0).1.row j = _
  rw [(finish_spec B (Nat.le_refl B) p.1 0).1 j, ite_eq_left j.isLt]
  change ((scatter key emit xs s 0 0).1.row j).reverse = _
  rw [scatter_row]
  simp [s, Rows.row_empty]

theorem group_row (key : α → Fin B) (xs : List α) (j : Fin B) :
    (group key xs).1.row j = xs.filter (fun a => decide (key a = j)) := by
  simpa [group] using groupMap_row key id xs j

/-- In particular, take `p` to be equality with a chosen output label. -/
theorem groupMap_multiplicity (key : α → Fin B) (emit : α → β)
    (xs : List α) (j : Fin B) (p : β → Bool) :
    (((groupMap key emit xs).1.row j).filter p).length =
      (xs.filter (fun a => decide (key a = j) && p (emit a))).length := by
  rw [groupMap_row]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases e : key a = j <;>
        cases hp : p (emit a) <;>
        simp [e, hp, ih]

/-- The counters returned by the executable routine, not a second traversal. -/
theorem groupMap_work (key : α → Fin B) (emit : α → β) (xs : List α) :
    (groupMap key emit xs).2 =
      ⟨B, xs.length, xs.length, xs.length, B⟩ := by
  let s : Rows B β := Rows.empty
  let p := scatter key emit xs s 0 0
  obtain ⟨hr, hw, hm⟩ := scatter_counts key emit xs s 0 0
  have hc : (finish B (Nat.le_refl B) p.1 0).2 = xs.length := by
    rw [(finish_spec B (Nat.le_refl B) p.1 0).2]
    change 0 + mass B (Nat.le_refl B) (scatter key emit xs s 0 0).1 =
      xs.length
    rw [hm]
    simp [s, mass_empty]
  change p.2.1 = 0 + xs.length at hr
  change p.2.2 = 0 + xs.length at hw
  change Work.mk B p.2.1 p.2.2 (finish B (Nat.le_refl B) p.1 0).2 B = _
  simp only [hr, hw, hc, Nat.zero_add]

theorem groupMap_one (key : α → Fin 1) (emit : α → β)
    (xs : List α) (j : Fin 1) :
    (groupMap key emit xs).1.row j = xs.map emit := by
  rw [groupMap_row]
  have he (a : α) : key a = j := by
    apply Fin.ext
    have ha := (key a).isLt
    have hj := j.isLt
    omega
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have ha : decide (key a = j) = true := by simp [he a]
      simp only [List.filter_cons, ha]
      change emit a :: (xs.filter (fun b => decide (key b = j))).map emit =
        emit a :: xs.map emit
      exact congrArg (List.cons (emit a)) ih

theorem groupMap_empty (key : α → Fin B) (emit : α → β) :
    (∀ j : Fin B, (groupMap key emit []).1.row j = []) ∧
      (groupMap key emit []).2 = ⟨B, 0, 0, 0, B⟩ := by
  constructor
  · intro j
    rw [groupMap_row]
    rfl
  · exact groupMap_work key emit []

theorem no_occurrences_with_no_buckets (key : α → Fin 0) (xs : List α) :
    xs = [] := by
  cases xs with
  | nil => rfl
  | cons a xs => exact Fin.elim0 (key a)

/-- Outgoing ownership: choose by source and store the projected arc. -/
def ownership (source : α → Fin B) (toArc : α → β) (xs : List α) :
    Rows B β × Work :=
  groupMap source toArc xs

theorem ownership_row (source : α → Fin B) (toArc : α → β)
    (xs : List α) (u : Fin B) :
    (ownership source toArc xs).1.row u =
      (xs.filter (fun a => decide (source a = u))).map toArc :=
  groupMap_row source toArc xs u

/-- Incoming transpose: choose by head and retain the full labelled occurrence. -/
def incoming (target : α → Fin B) (xs : List α) : Rows B α × Work :=
  group target xs

theorem incoming_row (target : α → Fin B) (xs : List α) (v : Fin B) :
    (incoming target xs).1.row v =
      xs.filter (fun a => decide (target a = v)) :=
  group_row target xs v

namespace Storage

/-
Source-level cell accounting: one owned table of B slots, one cell per
list entry, and fixed scalar state. During a reversal we count the whole
input and the whole current table (including the old row), and count the
unread suffix again even though it shares that row's cells. The visit
relations are proofs, not runtime snapshots or a backend allocation model.
-/

abbrev rowMass (s : Rows B β) : Nat :=
  mass B (Nat.le_refl B) s

abbrev scatterRows (key : α → Fin B) (emit : α → β) (input : List α) :
    Rows B β :=
  (scatter key emit input Rows.empty 0 0).1

theorem groupMap_phases (key : α → Fin B) (emit : α → β) (input : List α) :
    let p := scatter key emit input Rows.empty 0 0
    let q := finish B (Nat.le_refl B) (scatterRows key emit input) 0
    groupMap key emit input = (q.1, ⟨B, p.2.1, p.2.2, q.2, B⟩) := rfl

inductive ScatterAt (key : α → Fin B) (emit : α → β) (input : List α) :
    List α → Rows B β → Nat → Nat → Prop where
  | start : ScatterAt key emit input input Rows.empty 0 0
  | step {a : α} {xs : List α} {s : Rows B β} {r w : Nat} :
      ScatterAt key emit input (a :: xs) s r w →
      ScatterAt key emit input xs (s.write (key a) (emit a :: s.row (key a)))
        (r + 1) (w + 1)

theorem scatter_resume {key : α → Fin B} {emit : α → β}
    {input rest : List α} {s : Rows B β} {r w : Nat}
    (visit : ScatterAt key emit input rest s r w) :
    scatter key emit rest s r w = scatter key emit input Rows.empty 0 0 := by
  induction visit with
  | start => rfl
  | step _ ih => simpa only [scatter] using ih

private theorem scatter_total (key : α → Fin B) (emit : α → β) (input : List α) :
    rowMass (scatterRows key emit input) = input.length := by
  simpa only [rowMass, scatterRows, mass_empty, Nat.zero_add] using
    (scatter_counts key emit input (Rows.empty : Rows B β) 0 0).2.2

theorem scatter_space {key : α → Fin B} {emit : α → β}
    {input rest : List α} {s : Rows B β} {r w : Nat}
    (visit : ScatterAt key emit input rest s r w) :
    s.cells.size = B ∧ rowMass s + rest.length = input.length ∧
      rowMass s ≤ input.length ∧
      s.cells.size + rowMass s + input.length ≤ B + 2 * input.length := by
  have hm : rowMass s + rest.length = input.length := calc
    _ = rowMass (scatter key emit rest s r w).1 :=
      ((scatter_counts key emit rest s r w).2.2).symm
    _ = rowMass (scatterRows key emit input) := by rw [scatter_resume visit]
    _ = _ := scatter_total key emit input
  have hs := s.size_eq
  exact ⟨hs, hm, by omega, by omega⟩

inductive FinishAt (initial : Rows B β) :
    (t : Nat) → t ≤ B → Rows B β → Nat → Prop where
  | start : FinishAt initial B (Nat.le_refl B) initial 0
  | step {t : Nat} {h : t + 1 ≤ B} {s : Rows B β} {c : Nat}
      (prev : FinishAt initial (t + 1) h s c) :
      FinishAt initial t (by omega)
        (s.write ⟨t, h⟩ (reverseCharged (s.row ⟨t, h⟩) [] c).1)
        (reverseCharged (s.row ⟨t, h⟩) [] c).2

theorem finish_resume {initial s : Rows B β} {t c : Nat} {h : t ≤ B}
    (visit : FinishAt initial t h s c) :
    finish t h s c = finish B (Nat.le_refl B) initial 0 := by
  induction visit with
  | start => rfl
  | step _ ih => simpa only [finish] using ih

private theorem finish_total (t : Nat) (h : t ≤ B) (s : Rows B β) (c : Nat) :
    rowMass (finish t h s c).1 = rowMass s := by
  have hw : (fun j : Fin B => ((finish t h s c).1.row j).length) =
      (fun j => (s.row j).length) := by
    funext j
    rw [(finish_spec t h s c).1 j]
    split <;> simp
  unfold rowMass mass
  rw [hw]

theorem finish_space {key : α → Fin B} {emit : α → β} {input : List α}
    {s : Rows B β} {t c : Nat} {h : t ≤ B}
    (visit : FinishAt (scatterRows key emit input) t h s c) :
    s.cells.size = B ∧ rowMass s = input.length ∧
      s.cells.size + rowMass s + input.length = B + 2 * input.length := by
  have hm : rowMass s = input.length := calc
    _ = rowMass (finish t h s c).1 := (finish_total t h s c).symm
    _ = rowMass (finish B (Nat.le_refl B) (scatterRows key emit input) 0).1 := by
      rw [finish_resume visit]
    _ = rowMass (scatterRows key emit input) := finish_total _ _ _ _
    _ = _ := scatter_total key emit input
  have hs := s.size_eq
  exact ⟨hs, hm, by omega⟩

inductive ReverseAt (old : List β) (startCharge : Nat) :
    List β → List β → Nat → Prop where
  | start : ReverseAt old startCharge old [] startCharge
  | step {x : β} {xs acc : List β} {c : Nat} :
      ReverseAt old startCharge (x :: xs) acc c →
      ReverseAt old startCharge xs (x :: acc) (c + 1)

/-- The returned pair is the one used by `FinishAt.step`, even from a mid-row call. -/
theorem reverse_resume {old unread acc : List β} {startCharge c : Nat}
    (visit : ReverseAt old startCharge unread acc c) :
    reverseCharged unread acc c = reverseCharged old [] startCharge := by
  induction visit with
  | start => rfl
  | step _ ih => simpa only [reverseCharged] using ih

theorem reverse_split {old unread acc : List β} {startCharge c : Nat}
    (visit : ReverseAt old startCharge unread acc c) :
    acc.length + unread.length = old.length := by
  induction visit with
  | start => simp
  | step _ ih =>
      simp only [List.length_cons] at ih ⊢
      omega

private theorem row_le_prefix (s : Rows B β) (i : Fin B)
    (t : Nat) (h : t ≤ B) (hi : i.val < t) :
    (s.row i).length ≤ mass t h s := by
  induction t with
  | zero => omega
  | succ t ih =>
      have ht : t ≤ B := by omega
      let j : Fin B := ⟨t, by omega⟩
      change (s.row i).length ≤ mass t ht s + (s.row j).length
      by_cases e : i.val = t
      · have e' : i = j := Fin.ext e
        rw [e']
        omega
      · have hil : i.val < t := by omega
        have hb := ih ht hil
        omega

/-- With `M = input.length`, even counting both sides of the split costs at most `B + 3*M`. -/
theorem reversal_space {key : α → Fin B} {emit : α → β} {input : List α}
    {s : Rows B β} {t c charge : Nat} {h : t + 1 ≤ B} {unread acc : List β}
    (boundary : FinishAt (scatterRows key emit input) (t + 1) h s c)
    (active : ReverseAt (s.row ⟨t, by omega⟩) c unread acc charge) :
    acc.length + unread.length = (s.row ⟨t, by omega⟩).length ∧
      s.cells.size + rowMass s + input.length + (acc.length + unread.length) ≤
        B + 3 * input.length := by
  let i : Fin B := ⟨t, by omega⟩
  have hsplit : acc.length + unread.length = (s.row i).length :=
    reverse_split active
  have hrow : (s.row i).length ≤ rowMass s :=
    row_le_prefix s i B (Nat.le_refl B) i.isLt
  obtain ⟨hs, hm, _⟩ := finish_space boundary
  exact ⟨hsplit, by omega⟩

theorem groupMap_rowMass (key : α → Fin B) (emit : α → β)
    (xs : List α) :
    rowMass (groupMap key emit xs).1 = xs.length := by
  change
    rowMass (finish B (Nat.le_refl B) (scatterRows key emit xs) 0).1 =
      xs.length
  exact (finish_total _ _ _ _).trans (scatter_total key emit xs)

private theorem prefixMass_eq_sum_ofFn (weight : Fin B → Nat)
    (t : Nat) (h : t ≤ B) :
    prefixMass weight t h =
      (List.ofFn (fun i : Fin t =>
        weight ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩)).sum := by
  induction t with
  | zero => simp [prefixMass]
  | succ t ih =>
      have ht : t ≤ B := by omega
      let f (i : Fin t) := weight ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩
      let a := weight ⟨t, by omega⟩
      have hs :
          List.ofFn (fun i : Fin (t + 1) =>
            weight ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩) =
            List.ofFn f ++ [a] := by
        apply List.ext_getElem
        · simp
        · intro i hi hj
          have hi' : i < t + 1 := by
            simpa only [List.length_ofFn] using hi
          by_cases hit : i < t
          · have hleft : i < (List.ofFn f).length := by
              simpa only [List.length_ofFn] using hit
            rw [List.getElem_append_left hleft]
            simp only [List.getElem_ofFn, f]
          · have he : i = t := by omega
            subst i
            have hright : (List.ofFn f).length ≤ t := by simp
            rw [List.getElem_ofFn, List.getElem_append_right hright]
            simp [a]
      rw [hs, List.sum_append]
      change prefixMass weight t ht + a =
        (List.ofFn f).sum + ([a] : List Nat).sum
      rw [show prefixMass weight t ht = (List.ofFn f).sum from ih ht]
      simp

theorem rowMass_eq_ofFn_sum (s : Rows B β) :
    rowMass s = (List.ofFn (fun i => (s.row i).length)).sum :=
  prefixMass_eq_sum_ofFn (fun i => (s.row i).length) B (Nat.le_refl B)

theorem rowMass_eq_cells_sum (s : Rows B β) :
    rowMass s = (s.cells.toList.map List.length).sum := by
  rw [rowMass_eq_ofFn_sum]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp [s.size_eq]
  · intro i hi hj
    simp [Rows.row]

private theorem prefixMass_le_of_pointwise (f w : Fin B → Nat)
    (hle : ∀ i, f i ≤ w i) (t : Nat) (h : t ≤ B) :
    prefixMass f t h ≤ prefixMass w t h := by
  induction t with
  | zero => simp [prefixMass]
  | succ t ih =>
      have ht : t ≤ B := by omega
      let j : Fin B := ⟨t, by omega⟩
      change prefixMass f t ht + f j ≤ prefixMass w t ht + w j
      exact Nat.add_le_add (ih ht) (hle j)

theorem sum_ofFn_le_rowMass (s : Rows B β) (w : Fin B → Nat)
    (hle : ∀ i, w i ≤ (s.row i).length) :
    (List.ofFn w).sum ≤ rowMass s := by
  have hw : prefixMass w B (Nat.le_refl B) = (List.ofFn w).sum :=
    prefixMass_eq_sum_ofFn w B (Nat.le_refl B)
  rw [← hw]
  exact prefixMass_le_of_pointwise w (fun i => (s.row i).length)
    hle B (Nat.le_refl B)

end Storage

end EX51

/-
In the existing EX5.1 file, replace the `ofOccurrences` constructor body with:

  let rows := (EX51.ownership (fun a => a.«from»)
    ArcOccurrence.toQuotientArc occurrences).1
  { origVertexCount := n
    vertexCount := k
    root := root
    adj := rows.cells
    adj_size := rows.size_eq }

`EX51.ownership_row` gives the original `outArcs_ofOccurrences` equation.
For the transpose use `EX51.incoming (fun a => a.«to») occurrences`;
each incoming entry still has its source and its physical `origTail`.
-/
