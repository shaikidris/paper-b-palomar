module

public import PaperB.ForestEventChronology
public import PaperB.ExitParentEarlier
public import PaperB.ExitRealFirstLabel
public import PaperB.ExitLinearSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep.ChronologicalIndex

open PaperB PaperB.LabelledQuotient EX24.PreStep

/-- Split at the actual event, before its allocation. This counts every
allocation, including allocations whose parent is zero. -/
theorem SlotRun.splitBeforeFresh {H : LabelledQuotient}
    {t out : Tables H} {pre post : Log H} {e : Event H}
    (h : SlotRun t (pre ++ e :: post) out) (hf : e.fresh = true) :
    ∃ mid, SlotRun t pre mid ∧ SlotRun mid (e :: post) out ∧
      e.node = mid.next := by
  obtain ⟨mid, hb, ha⟩ := SlotRun.splitAtPrefix h
  refine ⟨mid, hb, ha, ?_⟩
  cases ha with
  | reuse hr hx ho hn ht => simp [hr] at hf
  | alloc hf' hx hp hn ht => exact hx

/-- The split witness and the grounded predecessor need not be identified
as tables: running the same prefix from the same start fixes the cursor. -/
theorem SlotRun.samePrefixNext {H : LabelledQuotient}
    {t a b : Tables H} {pre : Log H}
    (ha : SlotRun t pre a) (hb : SlotRun t pre b) :
    a.next = b.next := by
  have hla : (freshSlotIds pre).length = a.next - t.next := by
    rw [SlotRun.freshSlotIds_eq ha]
    simp
  have hlb : (freshSlotIds pre).length = b.next - t.next := by
    rw [SlotRun.freshSlotIds_eq hb]
    simp
  have hta := ha.next_le
  have htb := hb.next_le
  omega

theorem SlotRun.fresh_lt_end {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out) :
    ∀ z ∈ log, z.fresh = true → z.node < out.next := by
  induction h with
  | nil => simp
  | @reuse t u out e es hf hx ho hn ht ih =>
    intro z hz hzf
    rcases List.mem_cons.mp hz with hze | hzs
    · subst z
      simp [hf] at hzf
    · exact ih z hzs hzf
  | @alloc t u out e es hf hx hp hn ht ih =>
    intro z hz hzf
    rcases List.mem_cons.mp hz with hze | hzs
    · subst z
      have hle := ht.next_le
      omega
    · exact ih z hzs hzf

end EX24.PreparedSweep.ChronologicalIndex

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

/-- `prev` grounds the canonical forest after `pre`, not after `e`.
`seeded` and `written` are facts about physical occupancy at this point:
top-level seeds may come from anywhere in the log, while the writes used
here come only from the processed prefix. The size restriction is imposed
on proof liveness, not on physical occupancy. -/
theorem actualPrefix_live
    {t mid : Tables H} {G : JumpForest}
    {pre post : Log H} {e : Event H}
    (run : SlotRun t r.log r.out.tables) (hinit : t.next = 1)
    (hlog : r.log = pre ++ e :: post)
    (hbefore : SlotRun t pre mid)
    (prev : Grounded (orderedConfig p large) G mid)
    (hf : e.fresh = true) (occ : Nat → Prop)
    (seeded : ∀ z ∈ r.log, z.fresh = true → z.parent = 0 → occ z.node)
    (written : ∀ z ∈ pre, z.fresh = true → z.parent ≠ 0 → occ z.node) :
    e.node = G.size ∧
      ((occ 0 ∧ 0 < G.size) ↔ occ 0) ∧
      (∀ u, 0 < u → ((occ u ∧ u < G.size) ↔
        ∃ z ∈ pre, z.fresh = true ∧ z.node = u)) ∧
      (∀ z ∈ e :: post, z.fresh = true → z.parent = 0 →
        occ z.node ∧ ¬ (occ z.node ∧ z.node < G.size)) ∧
      (0 < e.parent → ScheduledEarlier pre (e :: post) e.parent ∧
        (occ e.parent ∧ e.parent < G.size)) := by
  have run' : SlotRun t (pre ++ e :: post) r.out.tables := by
    simpa only [hlog] using run
  obtain ⟨cut, hpre, hrest, hecut⟩ :=
    ChronologicalIndex.SlotRun.splitBeforeFresh run' hf
  have hsame := ChronologicalIndex.SlotRun.samePrefixNext hpre hbefore
  have hsize := prev.size_eq
  have hcut : cut.next = G.size := by omega
  have hstart := hbefore.next_le

  have hLive : ∀ u, 0 < u → ((occ u ∧ u < G.size) ↔
      ∃ z ∈ pre, z.fresh = true ∧ z.node = u) := by
    intro u hu
    constructor
    · rintro ⟨_, hlt⟩
      obtain ⟨left, z, between, hs, hn, hz, _, _⟩ :=
        hbefore.first u (by omega) (by omega)
      refine ⟨z, ?_, hz, hn⟩
      rw [hs]
      exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
    · rintro ⟨z, hz, hzf, hzu⟩
      have hlt := ChronologicalIndex.SlotRun.fresh_lt_end hbefore z hz hzf
      refine ⟨?_, by omega⟩
      rw [← hzu]
      by_cases hp : z.parent = 0
      · apply seeded z _ hzf hp
        rw [hlog]
        exact List.mem_append.mpr (Or.inl hz)
      · exact written z hz hzf hp

  refine ⟨hecut.trans hcut, ?_, hLive, ?_, ?_⟩
  · have hzero : 0 < G.size := by omega
    simp [hzero]
  · intro z hz hzf hp
    have hzlog : z ∈ r.log := by
      rw [hlog]
      exact List.mem_append.mpr (Or.inr hz)
    have hge := hrest.fresh_ge z hz hzf
    refine ⟨seeded z hzlog hzf hp, ?_⟩
    rintro ⟨_, hlt⟩
    omega
  · intro hp
    have hearlier :=
      ChronologicalIndex.SlotRun.freshParentEarlier run' hinit hf hp
    refine ⟨hearlier, (hLive e.parent hp).2 ?_⟩
    obtain ⟨left, z, between, hs, hn, hz, _, _⟩ := hearlier
    refine ⟨z, ?_, hz, hn⟩
    rw [hs]
    exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- For a dynamic transfer, instantiate `slot` with `j.slot` and `hslot`
with the transfer's physical-slot equality. The head hit certifies final
nonroot occupancy; the chronological prefix fixes the predecessor size. -/
theorem actualDynamicSlot_eq_previousSize
    {F : JumpForest}
    {g : Grounded (orderedConfig p large) F
      (initial (orderedConfig p large)
        (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount).tables}
    (full : FullRows p rank (orderedRows p data size_data))
    (ch : Chronology (orderedConfig p large) g r.out r.log)
    {t mid : Tables H} {G : JumpForest}
    {pre post : Log H} {e : Event H} {slot : Nat}
    (run : SlotRun t r.log r.out.tables)
    (hlog : r.log = pre ++ e :: post)
    (hbefore : SlotRun t pre mid)
    (prev : Grounded (orderedConfig p large) G mid)
    (hf : e.fresh = true)
    (hit : headLookup r e.head = some e)
    (hslot : slot = e.node) :
    slot = G.size ∧ NonrootOccupied r slot := by
  have run' : SlotRun t (pre ++ e :: post) r.out.tables := by
    simpa only [hlog] using run
  obtain ⟨cut, hpre, _, hecut⟩ :=
    ChronologicalIndex.SlotRun.splitBeforeFresh run' hf
  have hsame := ChronologicalIndex.SlotRun.samePrefixNext hpre hbefore
  have hsize := prev.size_eq
  refine ⟨by omega, ?_⟩
  rw [hslot]
  exact (slot_exact r full ch).mp ⟨e, rfl, hit⟩

end OrderedReaderResult
end PaperB.Exit
