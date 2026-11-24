module

public import PaperB.ExitArraySchedule
public import PaperB.ExitPhysicalSchedule
public import PaperB.ExitLinearSchedule
public import PaperB.ExitPhysicalKeys

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB.OrderedFreshHeads

structure ExitTransferDriver (H : LabelledQuotient) where
  address : Nat
  child : CutPair H
  parent : CutPair H

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : _root_.PaperB.OrderedReaderResult p data size_data rank large)

private def transferSlot? (lookup : Vertex H → Option (Event H))
    (y : Vertex H) : Option (Fin r.out.tables.next) :=
  match lookup y with
  | none => none
  | some e =>
    if h : e.node < r.out.tables.next then some ⟨e.node, h⟩ else none

private theorem transferSlot?_eq_actualSlot (y : Vertex H) :
    transferSlot? r (headLookup r) y = actualSlot r y :=
  rfl

private def transferAt? (i : Fin r.out.tables.next) :
    Option (ExitTransferDriver H) :=
  match exitBackKey? r i.val with
  | none => none
  | some child =>
    match exitBackKey? r (actualPhysicalParent r i.val) with
    | none => none
    | some parent => some ⟨i.val, child, parent⟩

/-- Collect successful reads in actual sweep order, sharing one head lookup. -/
def exitTransferDrivers : Array (ExitTransferDriver H) :=
  let lookup : Vertex H → Option (Event H) := headLookup r
  let order := (actualP r).orderAt
  ((List.finRange H.vertexCount).filterMap fun j =>
    (transferSlot? r lookup (order j)).bind (transferAt? r)).toArray

private theorem transferRead?_eq_some_iff (y : Vertex H)
    (d : ExitTransferDriver H) :
    (transferSlot? r (headLookup r) y).bind (transferAt? r) = some d ↔
      ∃ i : Fin r.out.tables.next,
        actualSlot r y = some i ∧ i.val = d.address ∧
          exitHeadKeys? r y = some (d.child, d.parent) := by
  rw [transferSlot?_eq_actualSlot]
  rcases d with ⟨address, child, parent⟩
  cases hs : actualSlot r y with
  | none => simp [Option.bind, hs]
  | some i =>
    cases hc : exitBackKey? r i.val with
    | none => simp [Option.bind, transferAt?, exitHeadKeys?, hs, hc]
    | some c =>
      cases hp : exitBackKey? r (actualPhysicalParent r i.val) <;>
        simp [Option.bind, transferAt?, exitHeadKeys?, hs, hc, hp]

theorem mem_exitTransferDrivers_iff_order (d : ExitTransferDriver H) :
    d ∈ exitTransferDrivers r ↔
      ∃ (j : Fin H.vertexCount) (i : Fin r.out.tables.next),
        actualSlot r ((actualP r).orderAt j) = some i ∧
          i.val = d.address ∧
          exitHeadKeys? r ((actualP r).orderAt j) = some (d.child, d.parent) := by
  simp [exitTransferDrivers, List.mem_filterMap, List.mem_finRange,
    transferRead?_eq_some_iff]

theorem mem_exitTransferDrivers_iff
    (covers : ∀ y : Vertex H, ∃ j : Fin H.vertexCount,
      (actualP r).orderAt j = y)
    (d : ExitTransferDriver H) :
    d ∈ exitTransferDrivers r ↔
      ∃ (y : Vertex H) (i : Fin r.out.tables.next),
        actualSlot r y = some i ∧ i.val = d.address ∧
          exitHeadKeys? r y = some (d.child, d.parent) := by
  rw [mem_exitTransferDrivers_iff_order r d]
  constructor
  · rintro ⟨j, i, hit, hi, keys⟩
    exact ⟨(actualP r).orderAt j, i, hit, hi, keys⟩
  · rintro ⟨y, i, hit, hi, keys⟩
    obtain ⟨j, hj⟩ := covers y
    exact ⟨j, i, by simpa only [hj] using hit, hi,
      by simpa only [hj] using keys⟩

/-- At most one driver per occupied head slot encountered in actual order. -/
theorem exitTransferDrivers_size_le_heads :
    (exitTransferDrivers r).size ≤
      ((List.finRange H.vertexCount).filterMap fun j =>
        actualSlot r ((actualP r).orderAt j)).length := by
  let read := fun j : Fin H.vertexCount =>
    transferSlot? r (headLookup r) ((actualP r).orderAt j)
  have h :
      (((List.finRange H.vertexCount).filterMap read).filterMap
        (transferAt? r)).length ≤
      ((List.finRange H.vertexCount).filterMap read).length := by
    apply List.length_filterMap_le
  simpa [exitTransferDrivers, List.filterMap_filterMap, read,
    transferSlot?_eq_actualSlot] using h

theorem exitTransferDrivers_size_le :
    (exitTransferDrivers r).size ≤ H.vertexCount := by
  calc
    _ ≤ ((List.finRange H.vertexCount).filterMap fun j =>
          actualSlot r ((actualP r).orderAt j)).length :=
      exitTransferDrivers_size_le_heads r
    _ ≤ (List.finRange H.vertexCount).length := by
      apply List.length_filterMap_le
    _ = H.vertexCount := by simp

variable {F : JumpForest} {up : Fin F.size → Fin F.size}
variable {g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}

theorem exitTransferDrivers_provenance
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    {d : ExitTransferDriver H} (hd : d ∈ exitTransferDrivers r) :
    ∃ (y : Vertex H) (i : Fin r.out.tables.next) (a : Fin F.size),
      actualSlot r y = some i ∧
      (actualP r).firstAt y i ∧
      i.val = d.address ∧
      a.val = d.address ∧
      actualPhysicalParent r d.address ≠ 0 ∧
      (up a).val = actualPhysicalParent r d.address ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables d.child =
        some d.address ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables d.parent =
        some (actualPhysicalParent r d.address) ∧
      (buildProperLossForest H rank).nodeKey? (E.image a) = some d.child ∧
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent (E.image a)) = some d.parent := by
  obtain ⟨j, i, hit, hi, keys⟩ := (mem_exitTransferDrivers_iff_order r d).mp hd
  let y := (actualP r).orderAt j
  have firstAt : (actualP r).firstAt y i :=
    (actualSlot_exact r full ch y i).mp hit
  obtain ⟨a, child, parent, ha, hp0, hup, _hcb, _hpb, hcs, hps, hck, hpk, hkeys⟩ :=
    actualSlot_exitHeadKeys r G hUp E hit firstAt
  have hk : (child, parent) = (d.child, d.parent) :=
    Option.some.inj (hkeys.symm.trans keys)
  have hc : child = d.child := congrArg Prod.fst hk
  have hp : parent = d.parent := congrArg Prod.snd hk
  subst child
  subst parent
  refine ⟨y, i, a, hit, firstAt, hi, ha.trans hi, ?_⟩
  rw [← hi]
  exact ⟨hp0, hup, hcs, hps, hck, hpk⟩

private theorem transfer_filterMap_addresses_nodup
    {α β γ : Type _} (read : α → Option β) (address : β → γ)
    (once : ∀ {a b x y}, read a = some x → read b = some y →
      address x = address y → a = b)
    (xs : List α) (hx : xs.Nodup) :
    ((xs.filterMap read).map address).Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hx' := List.nodup_cons.mp hx
    cases ha : read a with
    | none =>
      simpa only [List.filterMap_cons, ha] using ih hx'.2
    | some x =>
      simp only [List.filterMap_cons, ha, List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, ih hx'.2⟩
      intro hm
      obtain ⟨y, hy, haddr⟩ := List.mem_map.mp hm
      obtain ⟨b, hb, hby⟩ := List.mem_filterMap.mp hy
      have hab : a = b := once ha hby haddr.symm
      subst b
      exact hx'.1 hb

private theorem transfer_getElem_inj_of_nodup
    {α : Type _} {xs : List α} (hn : xs.Nodup) {i j : Nat}
    (hi : i < xs.length) (hj : j < xs.length)
    (h : xs[i]'hi = xs[j]'hj) : i = j := by
  induction xs generalizing i j with
  | nil => simp at hi
  | cons x xs ih =>
    have hn' := List.nodup_cons.mp hn
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j =>
        have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
        change x = xs[j]'hj' at h
        have hm : xs[j]'hj' ∈ xs := by
          apply List.getElem_mem <;> exact hj'
        exact (hn'.1 (h.symm ▸ hm)).elim
    | succ i =>
      have hi' : i < xs.length := Nat.lt_of_succ_lt_succ hi
      cases j with
      | zero =>
        change xs[i]'hi' = x at h
        have hm : xs[i]'hi' ∈ xs := by
          apply List.getElem_mem <;> exact hi'
        exact (hn'.1 (h ▸ hm)).elim
      | succ j =>
        have hj' : j < xs.length := Nat.lt_of_succ_lt_succ hj
        change xs[i]'hi' = xs[j]'hj' at h
        exact congrArg Nat.succ (ih hn'.2 hi' hj' h)

/-- Each compact row carries the address of its successful physical-slot read. -/
theorem exitTransferDrivers_address_lt
    (j : Fin (exitTransferDrivers r).size) :
    (exitTransferDrivers r)[j.val].address < r.out.tables.next := by
  have hm : (exitTransferDrivers r)[j.val] ∈ exitTransferDrivers r := by
    apply Array.getElem_mem <;> exact j.isLt
  obtain ⟨_, i, _, hi, _⟩ :=
    (mem_exitTransferDrivers_iff_order r _).mp hm
  rw [← hi]
  exact i.isLt

section ScheduledAddresses

variable
  (increasing : ∀ (a b : Fin H.vertexCount), a.val < b.val →
    (actualP r).rank ((actualP r).orderAt a) <
      (actualP r).rank ((actualP r).orderAt b))
  (covers : ∀ y : Vertex H, ∃ j : Fin H.vertexCount,
    (actualP r).orderAt j = y)
  (full : FullRows p rank (orderedRows p data size_data))
  (chronology : Chronology (orderedConfig p large) g r.out r.log)

include increasing covers full chronology

private theorem transfer_actualSlot_once
    {a b : Fin H.vertexCount} {i : Fin r.out.tables.next}
    (ha : actualSlot r ((actualP r).orderAt a) = some i)
    (hb : actualSlot r ((actualP r).orderAt b) = some i) :
    a = b := by
  let S := actualArraySchedule r
    (increasing := increasing) (covers := covers) full chronology
  have haS : S.mapSlot.read (S.vertex a) = some i := by
    change (driverMapSlot r).read ((driverOrder r).get a) = some i
    simpa only [driverMapSlot_read, driverOrder_get] using ha
  have hbS : S.mapSlot.read (S.vertex b) = some i := by
    change (driverMapSlot r).read ((driverOrder r).get b) = some i
    simpa only [driverMapSlot_read, driverOrder_get] using hb
  -- The same first/rank comparison as PrefixOcc.slot_once.
  have fa := (S.slot_exact _ _).1 haS
  have fb := (S.slot_exact _ _).1 hbS
  have hab : ¬ a.val < b.val := fun h =>
    fb.2 ⟨S.vertex a, S.increasing a b h, fa.1⟩
  have hba : ¬ b.val < a.val := fun h =>
    fa.2 ⟨S.vertex b, S.increasing b a h, fb.1⟩
  exact Fin.ext (by omega)

/-- Distinct compact rows have distinct physical addresses. -/
theorem exitTransferDrivers_addresses_nodup :
    ((exitTransferDrivers r).toList.map ExitTransferDriver.address).Nodup := by
  let read : Fin H.vertexCount → Option (ExitTransferDriver H) := fun j =>
    (transferSlot? r (headLookup r) ((actualP r).orderAt j)).bind
      (transferAt? r)
  have once : ∀ {a b x y}, read a = some x → read b = some y →
      x.address = y.address → a = b := by
    intro a b x y hx hy haddr
    obtain ⟨i, hi, hix, _⟩ :=
      (transferRead?_eq_some_iff r ((actualP r).orderAt a) x).mp hx
    obtain ⟨k, hk, hky, _⟩ :=
      (transferRead?_eq_some_iff r ((actualP r).orderAt b) y).mp hy
    have hik : i = k := Fin.ext (hix.trans (haddr.trans hky.symm))
    subst k
    exact transfer_actualSlot_once r increasing covers full chronology hi hk
  have hsrc : (List.finRange H.vertexCount).Nodup := by
    apply List.nodup_finRange
  simpa [exitTransferDrivers, read] using
    transfer_filterMap_addresses_nodup read ExitTransferDriver.address
      once (List.finRange H.vertexCount) hsrc

theorem exitTransferDrivers_address_injective :
    ∀ ⦃i j : Fin (exitTransferDrivers r).size⦄,
      (exitTransferDrivers r)[i.val].address =
        (exitTransferDrivers r)[j.val].address → i = j := by
  intro i j hij
  let xs := (exitTransferDrivers r).toList.map ExitTransferDriver.address
  have hn : xs.Nodup :=
    exitTransferDrivers_addresses_nodup r increasing covers full chronology
  have hi : i.val < xs.length := by simpa [xs] using i.isLt
  have hj : j.val < xs.length := by simpa [xs] using j.isLt
  have he : xs[i.val]'hi = xs[j.val]'hj := by
    simpa only [xs, List.getElem_map, Array.getElem_toList] using hij
  exact Fin.ext (transfer_getElem_inj_of_nodup hn hi hj he)

end ScheduledAddresses

end PaperB.Exit.OrderedReaderResult
