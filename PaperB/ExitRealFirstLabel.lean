module

public import PaperB.ExitActualLog
public import PaperB.ExitEarliestLabel
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

/-- Observe the label in the final state, not the label at an intermediate step. -/
def forwardLabelObservation (y : Vertex H) : Option Nat :=
  some ((selectors (orderedConfig p large) r.out).label y)

theorem forwardLabelObservation_of_mem {e : Event H} (he : e ∈ r.log) :
    forwardLabelObservation r e.head = some e.node :=
  congrArg some (r.logLabels e he)

theorem earliest_of_headLookup
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    {j : Vertex H} {e : Event H} (hit : headLookup r j = some e) :
    forwardLabelObservation r e.head = some e.node ∧
      ∀ y, forwardLabelObservation r y = some e.node → rank e.head ≤ rank y := by
  obtain ⟨he, hf, _, _⟩ := (headLookup_eq_some_iff r full j e).mp hit
  obtain ⟨_, _, ⟨pre, post, hsplit, hbefore, hafter⟩, _⟩ :=
    headLookup_occupied r g full ch hit
  have hcovers : ∀ y : Vertex H, y ∈ (orderedRows p data size_data).map Row.head := by
    intro y
    obtain ⟨row, hrow, hhead⟩ := full.covers y
    exact List.mem_map.mpr ⟨row, hrow, hhead⟩
  exact PhysicalLabelFirst.earliest_of_fresh
    (read := forwardLabelObservation r) r.logHeads full.ordered hcovers
    (fun x hx => forwardLabelObservation_of_mem r hx)
    he hf hsplit rfl hbefore hafter

/-- A positive occupied slot whose final stored parent is nonzero.
The grounding must record the parents of the actual fresh events. -/
def NonrootOccupied (k : Nat) : Prop :=
  0 < k ∧ k < r.out.tables.next ∧
    ∃ (G : JumpForest) (go : Grounded (orderedConfig p large) G r.out.tables),
      Filled r.out.tables ∧
      (∀ e ∈ r.log, e.fresh = true → storedParent go e.node = e.parent) ∧
      storedParent go k ≠ 0

theorem exists_hit_of_occupied
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    {k : Nat} (occupied : NonrootOccupied r k) :
    ∃ e ∈ r.log, e.node = k ∧ e.fresh = true ∧ e.parent ≠ 0 ∧
      forwardLabelObservation r e.head = some k ∧ headLookup r e.head = some e ∧
      ∃ (G : JumpForest) (go : Grounded (orderedConfig p large) G r.out.tables),
        Filled r.out.tables ∧ storedParent go k = e.parent ∧
        ∃ q, e.newKey = some q ∧ r.out.tables.back[k]? = some (some q) := by
  obtain ⟨hk, hu, _, go, _, hparents, hnonzero⟩ := occupied
  obtain ⟨pre, e, post, hsplit, h₁, h₂, _, _⟩ :=
    rootFirst ch.slots hk hu
  have hs : e.node = k := by
    first | assumption | exact h₁.symm | exact h₂.symm
  have hf : e.fresh = true := by
    first | assumption | exact h₁.symm | exact h₂.symm
  have he : e ∈ r.log := by
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr (by simp))
  have hp : e.parent ≠ 0 := by
    rw [← hparents e he hf, hs]
    exact hnonzero
  have hit : headLookup r e.head = some e := by
    apply (headLookup_eq_some_iff r full e.head e).mpr
    simp [he, hf, hp] <;> omega
  have hl : forwardLabelObservation r e.head = some k := by
    simpa only [hs] using forwardLabelObservation_of_mem r he
  obtain ⟨G, gf, hfill, _, _, hfinal⟩ := ch.final
  refine ⟨e, he, hs, hf, hp, hl, hit, G, gf, hfill, ?_⟩
  simpa only [hs] using hfinal e he hf

theorem slot_exact
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    {k : Nat} :
    (∃ e : Event H, e.node = k ∧ headLookup r e.head = some e) ↔
      NonrootOccupied r k := by
  constructor
  · rintro ⟨e, hs, hit⟩
    obtain ⟨hlo, hhi, _, _⟩ := headLookup_occupied r g full ch hit
    obtain ⟨he, hf, h₁, h₂⟩ := (headLookup_eq_some_iff r full e.head e).mp hit
    have hp : e.parent ≠ 0 := by
      first | assumption | omega
    obtain ⟨G, go, hfill, _, _, hfinal⟩ := ch.final
    refine ⟨?_, ?_, G, go, hfill, ?_, ?_⟩
    · simpa only [hs] using hlo
    · simpa only [hs] using hhi
    · exact fun x hx hfx => (hfinal x hx hfx).1
    · rw [← hs, (hfinal e he hf).1]
      exact hp
  · intro occupied
    obtain ⟨e, _, hs, _, _, _, hit, _⟩ :=
      exists_hit_of_occupied r full ch occupied
    exact ⟨e, hs, hit⟩

end OrderedReaderResult
end PaperB.Exit
