module

public import PaperB.ForestOrderedReader
public import PaperB.ForestEventChronology
public import PaperB.ExitGroupedFresh

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open _root_.EX24.PreparedSweep.ChronologicalIndex PaperB
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS

namespace PaperB.OrderedFreshHeads

universe u

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
  {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
  {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount} [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

private theorem rowHeadsNodup {rows : List (Row H)}
    (ord : rows.Pairwise (fun a b => rank a.head < rank b.head)) :
    (rows.map Row.head).Nodup := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    obtain ⟨h, ht⟩ := List.pairwise_cons.mp ord
    refine List.nodup_cons.mpr ⟨?_, ih ht⟩
    intro hm
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hm
    have hl := h x hx
    rw [he] at hl
    exact Nat.lt_irrefl _ hl

theorem logHeadsNodup (full : FullRows p rank (orderedRows p data size_data)) :
    (r.log.map Event.head).Nodup := by
  rw [r.logHeads]
  exact rowHeadsNodup full.ordered

def headLookup : Vertex H → Option (Event H) :=
  let a := FreshHeadIndex.build Event.head Event.fresh (fun e : Event H => decide (e.parent ≠ 0)) r.log
  fun j => FreshHeadIndex.lookup a j

theorem headLookup_eq_some_iff (full : FullRows p rank (orderedRows p data size_data))
    (j : Vertex H) (e : Event H) :
    headLookup r j = some e ↔
      e ∈ r.log ∧ e.fresh = true ∧ e.parent ≠ 0 ∧ e.head = j := by
  simpa [headLookup] using
    (FreshHeadIndex.lookup_eq_some_iff Event.head Event.fresh
      (fun x : Event H => decide (x.parent ≠ 0)) r.log (logHeadsNodup r full) j e)

private theorem slotBounds {t u : Tables H} {log : Log H} (h : SlotRun t log u) :
    t.next ≤ u.next ∧ ∀ e ∈ log, e.fresh = true → e.node < u.next := by
  induction h with
  | nil => simp
  | @reuse t u out x xs hf hx ho hn ht ih =>
    have hm := ih.1
    refine ⟨by omega, ?_⟩
    intro e he hFresh
    rcases List.mem_cons.mp he with he | he
    · subst e
      simp [hf] at hFresh
    · exact ih.2 e he hFresh
  | @alloc t u out x xs hf hx hp hn ht ih =>
    have hm := ih.1
    refine ⟨by omega, ?_⟩
    intro e he hFresh
    rcases List.mem_cons.mp he with he | he
    · subst e
      omega
    · exact ih.2 e he hFresh

variable {F} (g : Grounded (orderedConfig p large) F
  (initial (orderedConfig p large)
    (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables)

theorem chronology (prepared : PreparedInstalls (orderedConfig p large) rank)
    (parents : AppendParents (orderedConfig p large))
    (specs : ∀ row ∈ orderedRows p data size_data, TestSpec row.head row.tests) :
    Chronology (orderedConfig p large) g r.out r.log := by
  refine traceChronology prepared parents r.trace g ?_ specs
  intro k hk0 hk
  change k < 1 at hk
  omega

theorem headLookup_occupied (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    {j : Vertex H} {e : Event H} (hit : headLookup r j = some e) :
    0 < e.node ∧ e.node < r.out.tables.next ∧
    (∃ pre post : Log H, r.log = pre ++ e :: post ∧
      (∀ x ∈ pre, x.node ≠ e.node) ∧
      (∀ x ∈ post, x.node = e.node → x.fresh = false)) ∧
    ∃ G, ∃ go : Grounded (orderedConfig p large) G r.out.tables,
      Filled r.out.tables ∧ storedParent go e.node = e.parent ∧
      ∃ q, e.newKey = some q ∧ r.out.tables.back[e.node]? = some (some q) := by
  obtain ⟨he, hf, _, _⟩ := (headLookup_eq_some_iff r full j e).mp hit
  have hlo := ch.slots.fresh_ge e he hf
  change 1 ≤ e.node at hlo
  have hp : 0 < e.node := by omega
  have hu := (slotBounds ch.slots).2 e he hf
  refine ⟨hp, hu, ?_, ?_⟩
  · obtain ⟨pre, x, post, hs, _, _, hb, ha⟩ := rootFirst ch.slots hp hu
    rw [hs] at he
    rcases List.mem_append.mp he with he | he
    · exact (hb e he rfl).elim
    · rcases List.mem_cons.mp he with he | he
      · subst x
        exact ⟨pre, post, hs, hb, ha⟩
      · have hn := ha e he rfl
        simp [hf] at hn
  · obtain ⟨G, go, hfill, _, _, hfinal⟩ := ch.final
    exact ⟨G, go, hfill, hfinal e he hf⟩

def transferFor {M : Type u} (make : Event H → M) : Event H → Option M :=
  let atHead := headLookup r
  fun e => if e.parent = 0 then none else (atHead e.head).map make

theorem transferFor_top {M : Type u} (make : Event H → M) {e : Event H}
    (h : e.parent = 0) : transferFor r make e = none := by
  simp [transferFor, h]

end PaperB.OrderedFreshHeads
