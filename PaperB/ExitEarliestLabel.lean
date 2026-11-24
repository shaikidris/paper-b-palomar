module

public import PaperB.ExitLinearSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.PhysicalLabelFirst

/-!
These are the Prop-only stepping stones, not a `Schedule` instance.
The excerpt does not give the type of `r.logLabels`, the physical-label
accessor, or the row-coverage field. Accordingly, `read` is the existing
physical accessor, and `logLabels` and `covers` below are its pointwise
log certificate and row coverage, respectively. No array is built here.

For an index hit, the split is the third conjunct of
`headLookup_occupied (r := r) (g := g) full ch hit`.
For an arbitrary positive occupied slot, unpack
`rootFirst ch.slots hk ho`; it supplies the allocating event and split
without a search.
-/

private theorem pairwise_drop_prefix {α : Type _} {R : α → α → Prop}
    (pre tail : List α) (h : (pre ++ tail).Pairwise R) :
    tail.Pairwise R := by
  induction pre with
  | nil => exact h
  | cons a pre ih =>
    change (a :: (pre ++ tail)).Pairwise R at h
    exact ih (List.pairwise_cons.mp h).2

section Earliest

variable {V E Row : Type _}
variable {head : E → V} {rowHead : Row → V}
variable {node : E → Nat} {fresh : E → Bool}
variable {rank : V → Nat} {read : V → Option Nat}
variable {log : List E} {rows : List Row}

theorem earliest_of_creation_split
    (logHeads : log.map head = rows.map rowHead)
    (ordered : rows.Pairwise (fun a b => rank (rowHead a) < rank (rowHead b)))
    (covers : ∀ y, y ∈ rows.map rowHead)
    (logLabels : ∀ x ∈ log, read (head x) = some (node x))
    {pre post : List E} {e : E}
    (split : log = pre ++ e :: post)
    (before : ∀ x ∈ pre, node x ≠ node e) :
    read (head e) = some (node e) ∧
      ∀ y, read y = some (node e) → rank (head e) ≤ rank y := by
  have he : e ∈ log := by
    rw [split]
    exact List.mem_append.mpr (Or.inr (by simp))
  have hheads :
      (log.map head).Pairwise (fun a b => rank a < rank b) := by
    rw [logHeads]
    simpa only [List.pairwise_map] using ordered
  have hlog : log.Pairwise (fun a b => rank (head a) < rank (head b)) := by
    simpa only [List.pairwise_map] using hheads
  rw [split] at hlog
  have hpost := (List.pairwise_cons.mp
    (pairwise_drop_prefix pre (e :: post) hlog)).1
  refine ⟨logLabels e he, ?_⟩
  intro y hy
  have hyHead : y ∈ log.map head := by
    rw [logHeads]
    exact covers y
  obtain ⟨x, hx, hxy⟩ := List.mem_map.mp hyHead
  have hxRead := logLabels x hx
  rw [hxy] at hxRead
  have hxNode : node x = node e :=
    Option.some.inj (hxRead.symm.trans hy)
  rw [← hxy]
  rw [split] at hx
  rcases List.mem_append.mp hx with hx | hx
  · exact (before x hx hxNode).elim
  · rcases List.mem_cons.mp hx with hxe | hx
    · subst x
      exact Nat.le_refl _
    · exact Nat.le_of_lt (hpost x hx)

/-- Unlike an index hit, a fresh event need not have a nonzero parent.
The split obtained from `FirstCreation` identifies it in either case. -/
theorem earliest_of_fresh
    (logHeads : log.map head = rows.map rowHead)
    (ordered : rows.Pairwise (fun a b => rank (rowHead a) < rank (rowHead b)))
    (covers : ∀ y, y ∈ rows.map rowHead)
    (logLabels : ∀ x ∈ log, read (head x) = some (node x))
    {e created : E} {pre post : List E}
    (he : e ∈ log) (hf : fresh e = true)
    (split : log = pre ++ created :: post)
    (sameSlot : node created = node e)
    (before : ∀ x ∈ pre, node x ≠ node e)
    (after : ∀ x ∈ post, node x = node e → fresh x = false) :
    read (head e) = some (node e) ∧
      ∀ y, read y = some (node e) → rank (head e) ≤ rank y := by
  have hcreated : e = created := by
    rw [split] at he
    rcases List.mem_append.mp he with he | he
    · exact (before e he rfl).elim
    · rcases List.mem_cons.mp he with he | he
      · exact he
      · have hfalse := after e he rfl
        rw [hf] at hfalse
        cases hfalse
  subst created
  exact earliest_of_creation_split logHeads ordered covers logLabels split before

end Earliest

section Occupied

variable {V E : Type _}
variable {head : E → V} {node parent : E → Nat} {fresh : E → Bool}
variable {log : List E} {read : V → Option Nat} {lookup : V → Option E}

/-- After unpacking `rootFirst ch.slots hk ho`, use its split, node
equality, and freshness here. `parentRecorded` is the fresh-event
conjunct of `ch.final` for the same final grounded tables. -/
theorem fresh_hit_of_occupied_split
    {stored : Nat → Nat} {k : Nat}
    (nonzeroParent : stored k ≠ 0)
    (parentRecorded :
      ∀ x ∈ log, fresh x = true → stored (node x) = parent x)
    (logLabels : ∀ x ∈ log, read (head x) = some (node x))
    (indexComplete :
      ∀ x ∈ log, fresh x = true → parent x ≠ 0 → lookup (head x) = some x)
    {pre post : List E} {created : E}
    (split : log = pre ++ created :: post)
    (slot : node created = k) (allocated : fresh created = true) :
    ∃ e ∈ log, node e = k ∧ fresh e = true ∧
      stored k = parent e ∧ parent e ≠ 0 ∧
      read (head e) = some k ∧ lookup (head e) = some e := by
  have he : created ∈ log := by
    rw [split]
    exact List.mem_append.mpr (Or.inr (by simp))
  have hp := parentRecorded created he allocated
  rw [slot] at hp
  have hnz : parent created ≠ 0 := by
    rw [← hp]
    exact nonzeroParent
  have hl := logLabels created he
  rw [slot] at hl
  exact ⟨created, he, slot, allocated, hp, hnz, hl,
    indexComplete created he allocated hnz⟩

end Occupied

end PaperB.PhysicalLabelFirst
