module

public import PaperB.ExitPhysicalSchedule
public import PaperB.ExitLinearSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB.OrderedFreshHeads

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : _root_.PaperB.OrderedReaderResult p data size_data rank large)

def driverOrder : _root_.EX42.ArraySweep.OrderArray H.vertexCount :=
  ⟨(actualP r).order, (actualP r).order_size⟩

theorem driverOrder_get (j : Fin H.vertexCount) :
    (driverOrder r).get j = (actualP r).orderAt j :=
  rfl

variable
  (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
    (actualP r).rank ((actualP r).orderAt i) <
      (actualP r).rank ((actualP r).orderAt j))
  (covers : ∀ y : Vertex H, ∃ j : Fin H.vertexCount,
    (actualP r).orderAt j = y)

def driverPlan : _root_.EX42.ArraySweep.Plan H.vertexCount r.out.tables.next where
  rank := (actualP r).rank
  rank_inj := by
    intro x y hxy
    obtain ⟨i, hi⟩ := covers x
    obtain ⟨j, hj⟩ := covers y
    have hr : (actualP r).rank ((actualP r).orderAt i) =
        (actualP r).rank ((actualP r).orderAt j) := by
      simpa only [hi, hj] using hxy
    rcases Nat.lt_trichotomy i.val j.val with hlt | heq | hgt
    · exact False.elim (Nat.ne_of_lt (increasing i j hlt) hr)
    · have hij : i = j := Fin.ext heq
      subst j
      exact hi.symm.trans hj
    · exact False.elim (Nat.ne_of_lt (increasing j i hgt) hr.symm)
  observe y i :=
    decide (0 < i.val ∧ (actualP r).parent i ≠ 0 ∧
      (actualP r).observe y = some i.val)

theorem driverPlan_firstAt_iff (y : Vertex H) (i : Fin r.out.tables.next) :
    (driverPlan r increasing covers).firstAt y i ↔ (actualP r).firstAt y i := by
  simp only [_root_.EX42.ArraySweep.Plan.firstAt,
    _root_.EX42.ArraySweep.Plan.mapBefore, driverPlan,
    ActualPlanData.firstAt, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨hpos, hparent, hy⟩, hbefore⟩
    refine ⟨hpos, hparent, hy, ?_⟩
    intro z hz
    exact Nat.le_of_not_gt (fun hlt => hbefore ⟨z, hlt, hpos, hparent, hz⟩)
  · rintro ⟨hpos, hparent, hy, hmin⟩
    refine ⟨⟨hpos, hparent, hy⟩, ?_⟩
    rintro ⟨z, hlt, _, _, hz⟩
    exact Nat.not_lt_of_ge (hmin z hz) hlt

def driverMapSlot :
    _root_.EX42.ArraySweep.Slots (Fin r.out.tables.next) H.vertexCount :=
  let lookup : Vertex H → Option (Event H) := headLookup r
  { data := Array.ofFn (fun y : Fin H.vertexCount =>
      match lookup y with
      | none => none
      | some e =>
        if h : e.node < r.out.tables.next then some ⟨e.node, h⟩ else none)
    size_data := by simp }

theorem driverMapSlot_read (y : Vertex H) :
    (driverMapSlot r).read y = actualSlot r y := by
  simp only [_root_.EX42.ArraySweep.Slots.read, driverMapSlot,
    Array.getElem_ofFn, actualSlot, actualCreationEvent] <;> rfl

variable {F : JumpForest}
variable {g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}

def actualArraySchedule
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log) :
    _root_.EX42.ArraySweep.Schedule (driverPlan r increasing covers) where
  order := driverOrder r
  increasing := by
    intro i j hij
    change (actualP r).rank ((driverOrder r).get i) <
      (actualP r).rank ((driverOrder r).get j)
    simpa only [driverOrder_get] using increasing i j hij
  covers := by
    intro y
    obtain ⟨j, hj⟩ := covers y
    exact ⟨j, (driverOrder_get r j).trans hj⟩
  mapSlot := driverMapSlot r
  slot_exact := by
    intro y i
    rw [driverMapSlot_read r y]
    exact (actualSlot_exact r full ch y i).trans
      (driverPlan_firstAt_iff r increasing covers y i).symm

end PaperB.Exit.OrderedReaderResult
