module

public import PaperB.ExitCompactDrivers

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitSlotIndex

universe u
variable {α : Type u}

/-- For exit transfer drivers, pass `fun d => d.address` as `address`. -/
def addressAt (dirs : Array α) (address : α → Nat) (j : Fin dirs.size) : Nat :=
  address (dirs[j.val]'j.isLt)

abbrev InRange (physicalSlots : Nat) (dirs : Array α) (address : α → Nat) : Prop :=
  ∀ j : Fin dirs.size, addressAt dirs address j < physicalSlots

/-- Read an already-built table. The bound proof is erased. -/
@[inline] def lookup {d m : Nat} (a : Array (Option (Fin d)))
    (ha : a.size = m) (s : Fin m) : Option (Fin d) :=
  a[s.val]'(by rw [ha]; exact s.isLt)

/-- Pass `actualSlot r y` as `s`, sharing the array across queries. -/
@[inline] def lookup? {d m : Nat} (a : Array (Option (Fin d)))
    (ha : a.size = m) (s : Option (Fin m)) : Option (Fin d) :=
  s.bind (lookup a ha)

private abbrev Table (d m : Nat) :=
  { a : Array (Option (Fin d)) // a.size = m }

private def blank (d m : Nat) : Table d m :=
  ⟨Array.replicate m none, by simp⟩

private def read {d m : Nat} (a : Table d m) (s : Fin m) : Option (Fin d) :=
  lookup a.val a.property s

private def put {d m : Nat} (a : Table d m) (s : Fin m) (j : Fin d) :
    Table d m :=
  ⟨a.val.set s.val (some j) (by rw [a.property]; exact s.isLt),
    by simp [a.property]⟩

private theorem read_put {d m : Nat} (a : Table d m) (s t : Fin m)
    (j : Fin d) :
    read (put a s j) t = if s.val = t.val then some j else read a t := by
  by_cases h : s.val = t.val
  · simp [read, lookup, put, Array.getElem_set, h]
  · simp [read, lookup, put, Array.getElem_set, h, Ne.symm h]

private def driverSlot {m : Nat} (dirs : Array α) (address : α → Nat)
    (h : InRange m dirs address) (j : Fin dirs.size) : Fin m :=
  ⟨addressAt dirs address j, h j⟩

/-- Scan backwards so the remaining count is also the next index plus one.
This does not reorder `dirs` or determine the schedule's traversal order. -/
private def scan {d m : Nat} (slot : Fin d → Fin m)
    (n : Nat) (hn : n ≤ d) (a : Table d m) : Table d m :=
  match n, hn with
  | 0, _ => a
  | k + 1, hk =>
      let j : Fin d := ⟨k, hk⟩
      scan slot k (Nat.le_of_lt j.isLt) (put a (slot j) j)
termination_by structural n

/-- The primary output is one array: initialize it once, then call `Array.set`
once per driver. Injectivity is needed for correctness, not for construction. -/
def build (physicalSlots : Nat) (dirs : Array α) (address : α → Nat)
    (h : InRange physicalSlots dirs address) : Array (Option (Fin dirs.size)) :=
  (scan (driverSlot dirs address h) dirs.size (Nat.le_refl _)
    (blank dirs.size physicalSlots)).val

private def Good {d m : Nat} (slot : Fin d → Fin m) (n : Nat)
    (a : Table d m) : Prop :=
  ∀ (s : Fin m) (j : Fin d),
    read a s = some j ↔ (slot j).val = s.val ∧ n ≤ j.val

private theorem blank_good {d m : Nat} (slot : Fin d → Fin m) :
    Good slot d (blank d m) := by
  intro s j
  have hj := j.isLt
  have hn : ¬ d ≤ j.val := by omega
  simp [read, lookup, blank, hn]

private theorem good_put {d m : Nat} (slot : Fin d → Fin m)
    (hinj : Function.Injective slot) {k : Nat} (hk : k + 1 ≤ d)
    {a : Table d m} (ha : Good slot (k + 1) a) :
    Good slot k (put a (slot ⟨k, hk⟩) ⟨k, hk⟩) := by
  let i : Fin d := ⟨k, hk⟩
  change Good slot k (put a (slot i) i)
  intro s j
  rw [read_put]
  by_cases hi : (slot i).val = s.val
  · rw [if_pos hi]
    constructor
    · intro he
      have hij : i = j := Option.some.inj he
      subst j
      exact ⟨hi, Nat.le_refl k⟩
    · rintro ⟨hj, _⟩
      have hij : i = j := hinj (Fin.ext (hi.trans hj.symm))
      exact congrArg some hij
  · rw [if_neg hi, ha s j]
    constructor
    · rintro ⟨hj, hkj⟩
      exact ⟨hj, Nat.le_trans (Nat.le_succ k) hkj⟩
    · rintro ⟨hj, hkj⟩
      refine ⟨hj, ?_⟩
      have hne : j.val ≠ k := by
        intro he
        have hij : i = j := Fin.ext he.symm
        exact hi (congrArg (fun x => (slot x).val) hij |>.trans hj)
      omega

private theorem scan_good {d m : Nat} (slot : Fin d → Fin m)
    (hinj : Function.Injective slot) (n : Nat) (hn : n ≤ d)
    (a : Table d m) (ha : Good slot n a) :
    Good slot 0 (scan slot n hn a) := by
  induction n generalizing a with
  | zero => simpa only [scan] using ha
  | succ k ih =>
      rw [scan]
      apply ih
      exact good_put slot hinj hn ha

section
variable {m : Nat} {dirs : Array α} {address : α → Nat}
variable (h : InRange m dirs address)

theorem size_build : (build m dirs address h).size = m :=
  (scan (driverSlot dirs address h) dirs.size (Nat.le_refl _)
    (blank dirs.size m)).property

/-- Exactly the driver at its physical address, in both directions. -/
theorem lookup_build_eq_some_iff
    (hinj : Function.Injective (addressAt dirs address))
    (s : Fin m) (j : Fin dirs.size) :
    lookup (build m dirs address h) (size_build h) s = some j ↔
      addressAt dirs address j = s.val := by
  let slot := driverSlot dirs address h
  have hslot : Function.Injective slot := by
    intro i j hij
    exact hinj (congrArg Fin.val hij)
  have hs :=
    scan_good slot hslot dirs.size (Nat.le_refl _) (blank dirs.size m)
      (blank_good slot) s j
  change lookup (build m dirs address h) (size_build h) s = some j ↔
    addressAt dirs address j = s.val ∧ 0 ≤ j.val at hs
  simpa only [Nat.zero_le, and_true] using hs

theorem roundTrip (hinj : Function.Injective (addressAt dirs address))
    (j : Fin dirs.size) :
    lookup (build m dirs address h) (size_build h)
      ⟨addressAt dirs address j, h j⟩ = some j :=
  (lookup_build_eq_some_iff h hinj _ j).2 rfl

theorem noFalseHit (hinj : Function.Injective (addressAt dirs address))
    (s : Fin m) (j : Fin dirs.size)
    (hit : lookup (build m dirs address h) (size_build h) s = some j) :
    addressAt dirs address j = s.val :=
  (lookup_build_eq_some_iff h hinj s j).1 hit

theorem lookup?_build_eq_some_iff
    (hinj : Function.Injective (addressAt dirs address))
    (q : Option (Fin m)) (j : Fin dirs.size) :
    lookup? (build m dirs address h) (size_build h) q = some j ↔
      ∃ s : Fin m, q = some s ∧ addressAt dirs address j = s.val := by
  cases q with
  | none => simp [lookup?]
  | some s =>
      change lookup (build m dirs address h) (size_build h) s = some j ↔
        ∃ t : Fin m, some s = some t ∧ addressAt dirs address j = t.val
      rw [lookup_build_eq_some_iff h hinj s j]
      constructor
      · intro he
        exact ⟨s, rfl, he⟩
      · rintro ⟨t, ht, he⟩
        have hst : s = t := Option.some.inj ht
        subst t
        exact he

end

/-- A proof-only trace of the scan's writes. Each successor records one
`Array.set`; initialization is not counted. This is not an allocation or
array-copy cost model. -/
inductive SetWrites {d : Nat} :
    Nat → Array (Option (Fin d)) → Array (Option (Fin d)) → Prop where
  | done (a : Array (Option (Fin d))) : SetWrites 0 a a
  | step {n : Nat} {a b : Array (Option (Fin d))}
      (s : Nat) (hs : s < a.size) (j : Fin d) :
      SetWrites n (a.set s (some j) hs) b → SetWrites (n + 1) a b

private theorem scan_writes {d m : Nat} (slot : Fin d → Fin m)
    (n : Nat) (hn : n ≤ d) (a : Table d m) :
    SetWrites n a.val (scan slot n hn a).val := by
  induction n generalizing a with
  | zero =>
      rw [scan]
      exact .done _
  | succ k ih =>
      let j : Fin d := ⟨k, hn⟩
      have hs : (slot j).val < a.val.size := by
        rw [a.property]
        exact (slot j).isLt
      rw [scan]
      refine SetWrites.step (slot j).val hs j ?_
      change SetWrites k (put a (slot j) j).val
        (scan slot k (Nat.le_of_lt j.isLt) (put a (slot j) j)).val
      apply ih

theorem writes_build {m : Nat} {dirs : Array α} {address : α → Nat}
    (h : InRange m dirs address) :
    SetWrites dirs.size (Array.replicate m none) (build m dirs address h) :=
  scan_writes (driverSlot dirs address h) dirs.size (Nat.le_refl _)
    (blank dirs.size m)

private theorem scan_eq_of_zero {d m : Nat} (slot : Fin d → Fin m)
    (n : Nat) (hn : n ≤ d) (a : Table d m) (hz : n = 0) :
    scan slot n hn a = a := by
  subst n
  rfl

/-- No drivers: the scan performs no writes and returns the initialized table,
which still has one entry per physical slot. -/
theorem build_of_empty_drivers {m : Nat} {dirs : Array α} {address : α → Nat}
    (h : InRange m dirs address) (hz : dirs.size = 0) :
    build m dirs address h = Array.replicate m none :=
  congrArg (fun a : Table dirs.size m => a.val)
    (scan_eq_of_zero (driverSlot dirs address h) dirs.size (Nat.le_refl _)
      (blank dirs.size m) hz)

/-- With zero physical slots an in-range driver cannot exist. -/
theorem build_of_zero_slots {dirs : Array α} {address : α → Nat}
    (h : InRange 0 dirs address) :
    build 0 dirs address h = #[] := by
  have hz : dirs.size = 0 := by
    by_cases he : dirs.size = 0
    · exact he
    · have hp : 0 < dirs.size := by omega
      have hb := h ⟨0, hp⟩
      omega
  calc
    build 0 dirs address h = Array.replicate 0 none := build_of_empty_drivers h hz
    _ = #[] := by rfl

/-
At the reader call site, bind the table once:
  let dirs := exitTransferDrivers r
  let index := build r.out.tables.next dirs (fun d => d.address) hRange
Then `lookup? index (size_build hRange) (actualSlot r y)` gives the compact
driver index by direct array lookup. No key search or sorted schedule is
part of this module.
-/

end PaperB.ExitSlotIndex
