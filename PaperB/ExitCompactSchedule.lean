module

public import PaperB.ExitLinearSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX42.ArraySweep

variable {n m c : Nat}

def Plan.compactSites (P : Plan n m) (addr : Fin c → Fin m) : Plan n c where
  rank := P.rank
  rank_inj := P.rank_inj
  observe := fun y i => P.observe y (addr i)

@[simp] theorem Plan.compactSites_mapBefore
    (P : Plan n m) (addr : Fin c → Fin m) (k : Nat) (i : Fin c) :
    (P.compactSites addr).mapBefore k i ↔ P.mapBefore k (addr i) :=
  Iff.rfl

@[simp] theorem Plan.compactSites_firstAt
    (P : Plan n m) (addr : Fin c → Fin m) (y : Fin n) (i : Fin c) :
    (P.compactSites addr).firstAt y i ↔ P.firstAt y (addr i) :=
  Iff.rfl

namespace Schedule

variable {P : Plan n m}

private def compactSlots (S : Schedule P) (inv : Slots (Fin c) m) :
    Slots (Fin c) n where
  data := Array.ofFn fun y : Fin n => (S.mapSlot.read y).bind inv.read
  size_data := by simp

private theorem compactSlots_read
    (S : Schedule P) (inv : Slots (Fin c) m) (y : Fin n) :
    (compactSlots S inv).read y = (S.mapSlot.read y).bind inv.read := by
  simp only [Slots.read, compactSlots, Array.getElem_ofFn] <;> rfl

def compactSites (S : Schedule P) (addr : Fin c → Fin m)
    (inv : Slots (Fin c) m)
    (roundTrip : ∀ p i, inv.read p = some i ↔ addr i = p) :
    Schedule (P.compactSites addr) where
  order := S.order
  increasing := S.increasing
  covers := S.covers
  mapSlot := compactSlots S inv
  slot_exact := by
    intro y i
    rw [compactSlots_read, Plan.compactSites_firstAt]
    constructor
    · intro h
      cases hp : S.mapSlot.read y with
      | none => simp [hp, Option.bind] at h
      | some p =>
        have hi : inv.read p = some i := by
          simpa only [hp, Option.bind] using h
        rw [(roundTrip p i).mp hi]
        exact (S.slot_exact y p).mp hp
    · intro h
      rw [(S.slot_exact y (addr i)).mpr h]
      exact (roundTrip (addr i) i).mpr rfl

variable (S : Schedule P) (addr : Fin c → Fin m) (inv : Slots (Fin c) m)
variable (roundTrip : ∀ p i, inv.read p = some i ↔ addr i = p)

@[simp] theorem compactSites_mapSlot_read (y : Fin n) :
    (S.compactSites addr inv roundTrip).mapSlot.read y =
      (S.mapSlot.read y).bind inv.read :=
  compactSlots_read S inv y

@[simp] theorem compactSites_order :
    (S.compactSites addr inv roundTrip).order = S.order :=
  rfl

@[simp] theorem compactSites_cut (j : Nat) :
    (S.compactSites addr inv roundTrip).cut j = S.cut j :=
  rfl

/-- If the inverse is defined on every stored slot, decoding recovers
the physical slot array pointwise. Unwritten sites need not be selected. -/
theorem compactSites_read_back
    (totalOnActive : ∀ y p, S.mapSlot.read y = some p →
      ∃ i, inv.read p = some i) (y : Fin n) :
    ((S.compactSites addr inv roundTrip).mapSlot.read y).map addr =
      S.mapSlot.read y := by
  rw [compactSites_mapSlot_read]
  cases hp : S.mapSlot.read y with
  | none => rfl
  | some p =>
    obtain ⟨i, hi⟩ := totalOnActive y p hp
    change (inv.read p).map addr = some p
    rw [hi]
    exact congrArg some ((roundTrip p i).mp hi)

end Schedule
end EX42.ArraySweep
