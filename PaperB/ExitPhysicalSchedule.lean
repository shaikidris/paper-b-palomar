module

public import PaperB.ExitRealFirstLabel
public import PaperB.ExitLinearSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB.OrderedFreshHeads

namespace OrderedReaderResult

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)
variable {F : JumpForest}
variable {g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}

/-- The final physical parent word at slot `k`. -/
def actualPhysicalParent (k : Nat) : Nat :=
  (readRecordWords (orderedConfig p large).region r.out.tables.mem k).1.parent

private theorem storedParent_eq_actualPhysicalParent
    {G : JumpForest} (go : Grounded (orderedConfig p large) G r.out.tables)
    {k : Nat} (hk : k < r.out.tables.next) :
    storedParent go k = actualPhysicalParent r k := by
  have hG : k < G.size := by simpa only [go.size_eq] using hk
  unfold actualPhysicalParent
  rw [storedParent, dif_pos hG, (readRecordWords_spec go.layout hG).1] <;> rfl

theorem nonrootOccupied_iff_physicalParent
    (ch : Chronology (orderedConfig p large) g r.out r.log) (k : Nat) :
    NonrootOccupied r k ↔
      0 < k ∧ k < r.out.tables.next ∧ actualPhysicalParent r k ≠ 0 := by
  constructor
  · rintro ⟨hlo, hhi, G, go, _, _, hp⟩
    refine ⟨hlo, hhi, ?_⟩
    simpa only [storedParent_eq_actualPhysicalParent r go hhi] using hp
  · rintro ⟨hlo, hhi, hp⟩
    obtain ⟨G, go, hfill, _, _, hfinal⟩ := ch.final
    refine ⟨hlo, hhi, G, go, hfill, ?_, ?_⟩
    · exact fun e he hf => (hfinal e he hf).1
    · simpa only [storedParent_eq_actualPhysicalParent r go hhi] using hp

theorem slot_exact_physical
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log) {k : Nat} :
    (∃ e : Event H, e.node = k ∧ headLookup r e.head = some e) ↔
      0 < k ∧ k < r.out.tables.next ∧ actualPhysicalParent r k ≠ 0 :=
  (slot_exact r full ch).trans (nonrootOccupied_iff_physicalParent r ch k)

/-- Computed plan data, retaining physical slot numbers and the supplied order. -/
structure ActualPlanData (H : LabelledQuotient) (m : Nat) where
  order : Array (Vertex H)
  order_size : order.size = H.vertexCount
  rank : Vertex H → Nat
  observe : Vertex H → Option Nat
  parent : Fin m → Nat

def ActualPlanData.orderAt {m : Nat} (P : ActualPlanData H m)
    (j : Fin H.vertexCount) : Vertex H :=
  orderedVertexAt P.order P.order_size j

def ActualPlanData.firstAt {m : Nat} (P : ActualPlanData H m)
    (y : Vertex H) (i : Fin m) : Prop :=
  0 < i.val ∧ P.parent i ≠ 0 ∧ P.observe y = some i.val ∧
    ∀ z, P.observe z = some i.val → P.rank y ≤ P.rank z

def actualP : ActualPlanData H r.out.tables.next where
  order := data
  order_size := size_data
  rank := rank
  observe := forwardLabelObservation r
  parent i :=
    (readRecordWords (orderedConfig p large).region r.out.tables.mem i.val).1.parent

/-- One optional creation event per vertex, using the existing fresh-head index. -/
def actualCreationEvent : Vertex H → Option (Event H) :=
  headLookup r

def actualCreationEventAt (j : Fin H.vertexCount) : Option (Event H) :=
  actualCreationEvent r ((actualP r).orderAt j)

def actualSlot (y : Vertex H) : Option (Fin r.out.tables.next) :=
  match actualCreationEvent r y with
  | none => none
  | some e =>
    if h : e.node < r.out.tables.next then some ⟨e.node, h⟩ else none

private theorem actualSlot_eq_some_iff_hit
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (y : Vertex H) (i : Fin r.out.tables.next) :
    actualSlot r y = some i ↔
      ∃ e : Event H, headLookup r y = some e ∧ e.node = i.val := by
  cases hit : headLookup r y with
  | none => simp [actualSlot, actualCreationEvent, hit]
  | some e =>
    obtain ⟨_, hhi, _, _⟩ := headLookup_occupied r g full ch hit
    have hs : actualSlot r y = some ⟨e.node, hhi⟩ := by
      simp [actualSlot, actualCreationEvent, hit, hhi]
    rw [hs]
    constructor
    · intro h
      exact ⟨e, by simp [hit], congrArg Fin.val (Option.some.inj h)⟩
    · rintro ⟨x, hx, hn⟩
      have he : e = x := by
        apply Option.some.inj
        simpa only [hit] using hx
      subst x
      exact congrArg some (Fin.ext hn)

private theorem actualRowsRankInjective {rows : List (Row H)}
    (ordered : rows.Pairwise (fun a b => rank a.head < rank b.head)) :
    ∀ a ∈ rows, ∀ b ∈ rows, rank a.head = rank b.head → a.head = b.head := by
  revert ordered
  induction rows with
  | nil => simp
  | cons x xs ih =>
    intro ordered
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ordered
    intro a ha b hb hab
    rcases List.mem_cons.mp ha with haEq | haTail
    · subst a
      rcases List.mem_cons.mp hb with hbEq | hbTail
      · subst b
        rfl
      · exact False.elim ((Nat.ne_of_lt (hhead b hbTail)) hab)
    · rcases List.mem_cons.mp hb with hbEq | hbTail
      · subst b
        exact False.elim ((Nat.ne_of_lt (hhead a haTail)) hab.symm)
      · exact ih htail a haTail b hbTail hab

private theorem actualRankInjective
    (full : FullRows p rank (orderedRows p data size_data)) :
    Function.Injective rank := by
  intro y z h
  obtain ⟨a, ha, hay⟩ := full.covers y
  obtain ⟨b, hb, hbz⟩ := full.covers z
  subst y
  subst z
  exact actualRowsRankInjective full.ordered a ha b hb h

theorem actualSlot_exact
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (y : Vertex H) (i : Fin r.out.tables.next) :
    actualSlot r y = some i ↔ (actualP r).firstAt y i := by
  rw [actualSlot_eq_some_iff_hit r full ch y i]
  change
    (∃ e : Event H, headLookup r y = some e ∧ e.node = i.val) ↔
      0 < i.val ∧ actualPhysicalParent r i.val ≠ 0 ∧
        forwardLabelObservation r y = some i.val ∧
          ∀ z, forwardLabelObservation r z = some i.val → rank y ≤ rank z
  constructor
  · rintro ⟨e, hit, hs⟩
    obtain ⟨_, _, _, hy⟩ := (headLookup_eq_some_iff r full y e).mp hit
    have hit' : headLookup r e.head = some e := by
      simpa only [hy] using hit
    have ho := (slot_exact_physical r full ch).mp ⟨e, hs, hit'⟩
    obtain ⟨hl, hmin⟩ := earliest_of_headLookup r full ch hit
    refine ⟨ho.1, ho.2.2, ?_, ?_⟩
    · simpa only [hy, hs] using hl
    · simpa only [hy, hs] using hmin
  · rintro ⟨hpos, hp, hl, hmin⟩
    have ho := (nonrootOccupied_iff_physicalParent r ch i.val).mpr
      ⟨hpos, i.isLt, hp⟩
    obtain ⟨e, _, hs, _, _, heLabel, hit, _⟩ :=
      exists_hit_of_occupied r full ch ho
    have hEy : rank e.head ≤ rank y :=
      (earliest_of_headLookup r full ch hit).2 y (by simpa only [hs] using hl)
    have hy : e.head = y :=
      actualRankInjective full (Nat.le_antisymm hEy (hmin e.head heLabel))
    exact ⟨e, by simpa only [hy] using hit, hs⟩

theorem actualSlot_eq_some_exists_event
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    (y : Vertex H) (i : Fin r.out.tables.next)
    (h : actualSlot r y = some i) :
    ∃ e : Event H,
      e ∈ r.log ∧ e.head = y ∧ e.fresh = true ∧ e.node = i.val := by
  obtain ⟨e, hLookup, hNode⟩ :=
    (actualSlot_eq_some_iff_hit r full ch y i).mp h
  obtain ⟨hMem, hFresh, _, hHead⟩ :=
    (headLookup_eq_some_iff r full y e).mp hLookup
  exact ⟨e, hMem, hHead, hFresh, hNode⟩

end OrderedReaderResult
end PaperB.Exit
