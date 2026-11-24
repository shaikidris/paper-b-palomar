module

public import PaperB.ForestEventChronology

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep.ChronologicalIndex

open PaperB PaperB.LabelledQuotient EX24.PreStep

def freshSlotIds {H : LabelledQuotient} (log : Log H) : List Nat :=
  log.filterMap fun e => if e.fresh = true then some e.node else none

theorem SlotRun.freshSlotIds_eq {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out) :
    freshSlotIds log = List.range' t.next (out.next - t.next) := by
  induction h with
  | nil => simp [freshSlotIds]
  | @reuse t u out e es hf hx ho hn ht ih =>
    simpa [freshSlotIds, List.filterMap_cons, hf, hn] using ih
  | @alloc t u out e es hf hx hp hn ht ih =>
    have hu := ht.next_le
    have hlen : out.next - t.next = (out.next - u.next) + 1 := by omega
    calc
      freshSlotIds (e :: es) = e.node :: freshSlotIds es := by
        simp [freshSlotIds, List.filterMap_cons, hf]
      _ = List.range' t.next (out.next - t.next) := by
        rw [ih, hx, hlen, List.range'_succ, hn]

theorem SlotRun.freshSlotIds_fromOne {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out)
    (hinit : t.next = 1) :
    freshSlotIds log = List.range' 1 (out.next - 1) := by
  simpa only [hinit] using h.freshSlotIds_eq

theorem SlotRun.splitAtPrefix {H : LabelledQuotient}
    {t out : Tables H} {pre rest : Log H}
    (h : SlotRun t (pre ++ rest) out) :
    ∃ mid, SlotRun t pre mid ∧ SlotRun mid rest out := by
  induction pre generalizing t with
  | nil => exact ⟨t, by constructor, h⟩
  | cons e es ih =>
    change SlotRun t (e :: (es ++ rest)) out at h
    cases h with
    | reuse hf hx ho hn ht =>
      obtain ⟨mid, hb, ha⟩ := @ih _ ht
      exact ⟨mid, .reuse hf hx ho hn hb, ha⟩
    | alloc hf hx hp hn ht =>
      obtain ⟨mid, hb, ha⟩ := @ih _ ht
      exact ⟨mid, .alloc hf hx hp hn hb, ha⟩

/-- The creator is in the specified physical prefix. No other position
in the full log is a fresh event for this slot. -/
def ScheduledEarlier {H : LabelledQuotient}
    (pre rest : Log H) (k : Nat) : Prop :=
  ∃ (left : Log H) (p : Event H) (between : Log H),
    pre = left ++ p :: between ∧ p.node = k ∧ p.fresh = true ∧
    (∀ z ∈ left, z.node ≠ k) ∧
    (∀ z ∈ between ++ rest, z.node = k → z.fresh = false)

theorem ScheduledEarlier.firstCreation {H : LabelledQuotient}
    {pre rest : Log H} {k : Nat} (h : ScheduledEarlier pre rest k) :
    FirstCreation (pre ++ rest) k := by
  obtain ⟨left, p, between, hs, hn, hf, hb, ha⟩ := h
  exact ⟨left, p, between ++ rest, by simp [hs, List.append_assoc],
    hn, hf, hb, ha⟩

theorem SlotRun.parentEarlier {H : LabelledQuotient}
    {t out : Tables H} {pre post : Log H} {e : Event H}
    (h : SlotRun t (pre ++ e :: post) out) (hinit : t.next = 1)
    (hp : 0 < e.parent) (valid : e.fresh = true ∨ e.parent < e.node) :
    ScheduledEarlier pre (e :: post) e.parent := by
  obtain ⟨mid, hb, ha⟩ := h.splitAtPrefix
  have hcursor : e.parent < mid.next := by
    cases ha with
    | reuse hf hx ho hn ht =>
      rcases valid with hf' | hlt
      · simp [hf] at hf'
      · exact Nat.lt_trans hlt hx
    | alloc hf hx hpar hn ht => exact hpar
  obtain ⟨left, p, between, hs, hn, hf, hleft, hbetween⟩ :=
    hb.first e.parent (by omega) hcursor
  refine ⟨left, p, between, hs, hn, hf, hleft, ?_⟩
  intro z hz hzk
  rcases List.mem_append.mp hz with hz | hz
  · exact hbetween z hz hzk
  · cases hzf : z.fresh with
    | false => rfl
    | true =>
      have hge := ha.fresh_ge z hz hzf
      omega

theorem SlotRun.freshParentEarlier {H : LabelledQuotient}
    {t out : Tables H} {pre post : Log H} {e : Event H}
    (h : SlotRun t (pre ++ e :: post) out) (hinit : t.next = 1)
    (hf : e.fresh = true) (hp : 0 < e.parent) :
    ScheduledEarlier pre (e :: post) e.parent :=
  h.parentEarlier hinit hp (Or.inl hf)

end EX24.PreparedSweep.ChronologicalIndex
