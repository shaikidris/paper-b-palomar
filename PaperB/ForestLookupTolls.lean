module

public import PaperB.ForestInstallCapacity
public import PaperB.ForestEventChronology
public import PaperB.ForestMeasuredWork

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep

open _root_.EX24 _root_.EX24.PreStep PaperB PaperB.LabelledQuotient PaperB.ForestHead

namespace AggregateEX24

theorem stepPrepared_lookupTrace {H : LabelledQuotient}
    {c : Config H} {s : State H} {rank : Vertex H → Nat}
    {row : Row H} {r : HeadResult H}
    (h : stepPrepared c s rank row.head row.tests = some r) :
    (installWithLookupTrace c s.tables r.measured.step).1 = some r.installed ∧
    r.measured.step.parent < s.tables.next ∧
    (installWithLookupTrace c s.tables r.measured.step).2 =
      (match r.measured.step.newPair with | none => [] | some q => [q]) := by
  have hi : install c s.tables r.measured.step = some r.installed := by
    by_cases hy : c.vertexIndex row.head < s.labels.size
    · cases hk : install c s.tables
          (ForestHead.runPrepared (selectors c s) rank row.head row.tests).step with
      | none => simp [stepPrepared, hy, hk] at h
      | some a =>
        simp only [stepPrepared, dif_pos hy, hk, Option.map] at h
        have hr := Option.some.inj h
        subst r
        exact hk
    · simp [stepPrepared, hy] at h
  have hp : r.measured.step.parent < s.tables.next := by
    by_cases hp : r.measured.step.parent < s.tables.next
    · exact hp
    · simp [install, hp] at hi
  refine ⟨(installWithLookupTrace_fst c s.tables r.measured.step).trans hi, hp, ?_⟩
  cases hq : r.measured.step.newPair <;> simp [installWithLookupTrace, hp, hq]

/-- The sum of the comparison counts returned by the recorded dictionary calls. -/
def pairLookupComparisons {H : LabelledQuotient} (c : Config H)
    (qs : List (CutPair H)) : Nat :=
  (qs.map fun q => (PairLookup.lookup c.dict (c.code q)).2).sum

theorem stepPrepared_pairLookupComparisons {H : LabelledQuotient}
    {c : Config H} {s : State H} {rank : Vertex H → Nat}
    {row : Row H} {r : HeadResult H}
    (h : stepPrepared c s rank row.head row.tests = some r) :
    pairLookupComparisons c (installWithLookupTrace c s.tables r.measured.step).2 =
      (match r.measured.step.newPair with
       | none => 0
       | some q => (PairLookup.lookup c.dict (c.code q)).2) := by
  rw [(stepPrepared_lookupTrace h).2.2]
  cases r.measured.step.newPair <;> simp [pairLookupComparisons]

theorem pairLookupComparisons_le {H : LabelledQuotient} (c : Config H)
    (qs : List (CutPair H)) :
    pairLookupComparisons c qs ≤ (Nat.log2 (c.dict.size + 1) + 2) * qs.length := by
  induction qs with
  | nil => simp [pairLookupComparisons]
  | cons q qs ih =>
    rw [List.length_cons, Nat.mul_succ,
      Nat.add_comm ((Nat.log2 (c.dict.size + 1) + 2) * qs.length)]
    simpa only [pairLookupComparisons, List.map_cons, List.sum_cons] using
      Nat.add_le_add (PairLookup.lookup_count_le c.dict (c.code q)) ih

/-- The same successful rows as `WorkTrace`, with calls in execution order. -/
inductive PairLookupTrace {H : LabelledQuotient}
    (c : Config H) (rank : Vertex H → Nat) :
    State H → List (Row H) → State H → Log H → Count → Work →
      List (CutPair H) → Prop where
  | nil (s : State H) : PairLookupTrace c rank s [] s [] Count.zero Work.zero []
  | cons {s out : State H} {row : Row H} {rows : List (Row H)}
      {r : HeadResult H} {log : Log H} {n : Count} {w : Work}
      {qs : List (CutPair H)} :
      stepPrepared c s rank row.head row.tests = some r →
      (installWithLookupTrace c s.tables r.measured.step).1 = some r.installed →
      r.measured.step.parent < s.tables.next →
      PairLookupTrace c rank r.state rows out log n w qs →
      PairLookupTrace c rank s (row :: rows) out
        (Event.ofResult row.head r :: log) (Count.prepend r n)
        ((headWork rank row r).add w)
        ((installWithLookupTrace c s.tables r.measured.step).2 ++ qs)

theorem WorkTrace.withPairLookups {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat} {s out : State H}
    {rows : List (Row H)} {log : Log H} {n : Count} {w : Work}
    (h : WorkTrace c rank s rows out log n w) :
    ∃ qs, PairLookupTrace c rank s rows out log n w qs ∧
      qs.length = w.requests ∧
      pairLookupComparisons c qs ≤ (Nat.log2 (c.dict.size + 1) + 2) * w.requests := by
  induction h with
  | nil s => exact ⟨[], .nil s, rfl, by simp [pairLookupComparisons]⟩
  | @cons s out row rows r log n w hstep hrest ih =>
    obtain ⟨qs, ht, hlen, _⟩ := ih
    have hc := stepPrepared_lookupTrace hstep
    have hf : (headWork rank row r).requests =
        (match r.measured.step.newPair with | none => 0 | some _ => 1) := by
      cases he : r.measured.step.newPair <;> simp [headWork, he] <;> rfl
    let here := (installWithLookupTrace c s.tables r.measured.step).2
    have hh : here.length = (headWork rank row r).requests := by
      change (installWithLookupTrace c s.tables r.measured.step).2.length = _
      rw [hc.2.2, hf]
      cases r.measured.step.newPair <;> rfl
    have hk : (here ++ qs).length = ((headWork rank row r).add w).requests := by
      simp only [List.length_append, hh, hlen, Work.add]
    refine ⟨here ++ qs, .cons hstep hc.1 hc.2.1 ht, hk, ?_⟩
    simpa only [hk] using pairLookupComparisons_le c (here ++ qs)

end AggregateEX24
end EX24.PreparedSweep
