module

public import PaperB.ForestEventChronology
public import PaperB.ForestMeasuredWork

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep

open _root_.EX24 _root_.EX24.PreStep PaperB PaperB.LabelledQuotient PaperB.ForestHead
open _root_.EX24.PreparedSweep.ChronologicalIndex

/-- The install control flow with one trace entry at each keyed lookup.
An entry `q` records the call on `c.code q`, not its comparison count. -/
def installWithLookupTrace {H : LabelledQuotient} (c : Config H)
    (t : Tables H) (req : ForestHead.Step H) :
    Option (Installed H) × List (CutPair H) :=
  if req.parent < t.next then
    match req.newPair with
    | none => (some ⟨t, req.parent, false, []⟩, [])
    | some q =>
      let out : Option (Installed H) :=
        match (PairLookup.lookup c.dict (c.code q)).1 with
        | none => none
        | some i =>
          if hi : i < t.slots.size then
            if t.slotAt i = 0 then
              if hn : t.next < t.back.size then
                let w := appendLeafWords c.region t.mem req.parent
                some ⟨⟨w.1, t.slots.set i t.next hi,
                    t.back.set t.next (some q) hn, t.next + 1⟩,
                  t.next, true, w.2⟩
              else none
            else some ⟨t, t.slotAt i, false, []⟩
          else none
      (out, [q])
  else (none, [])

theorem installWithLookupTrace_fst {H : LabelledQuotient} (c : Config H)
    (t : Tables H) (req : ForestHead.Step H) :
    (installWithLookupTrace c t req).1 = install c t req := by
  by_cases hp : req.parent < t.next
  · cases hq : req.newPair with
    | none =>
      simp only [installWithLookupTrace, install, if_pos hp, hq] <;> rfl
    | some q =>
      cases hk : (PairLookup.lookup c.dict (c.code q)).1 with
      | none =>
        simp only [installWithLookupTrace, install, if_pos hp, hq, hk]
      | some i =>
        by_cases hi : i < t.slots.size
        · by_cases hz : t.slotAt i = 0
          · by_cases hn : t.next < t.back.size
            · simp only [installWithLookupTrace, install, if_pos hp, hq, hk,
                dif_pos hi, if_pos hz, dif_pos hn] <;> rfl
            · simp only [installWithLookupTrace, install, if_pos hp, hq, hk,
                dif_pos hi, if_pos hz, dif_neg hn]
          · simp only [installWithLookupTrace, install, if_pos hp, hq, hk,
              dif_pos hi, if_neg hz] <;> rfl
        · simp only [installWithLookupTrace, install, if_pos hp, hq, hk, dif_neg hi]
  · simp only [installWithLookupTrace, install, if_neg hp]

private theorem installLookupTrace_of_success {H : LabelledQuotient}
    {c : Config H} {t : Tables H} {req : ForestHead.Step H} {a : Installed H}
    (h : install c t req = some a) :
    (installWithLookupTrace c t req).2 =
      (match req.newPair with | none => [] | some q => [q]) := by
  by_cases hp : req.parent < t.next
  · cases hq : req.newPair <;> simp [installWithLookupTrace, hp, hq]
  · simp [install, hp] at h

private theorem installMemSize_of_success {H : LabelledQuotient}
    {c : Config H} {F : JumpForest} {t : Tables H}
    {req : ForestHead.Step H} {a : Installed H}
    (g : Grounded c F t) (h : install c t req = some a) :
    a.tables.mem.size = t.mem.size := by
  by_cases hp : req.parent < t.next
  · cases hq : req.newPair with
    | none =>
      simp only [install, if_pos hp, hq] at h
      have ha := Option.some.inj h
      subst a
      rfl
    | some q =>
      cases hk : (PairLookup.lookup c.dict (c.code q)).1 with
      | none => simp [install, hp, hq, hk] at h
      | some i =>
        by_cases hi : i < t.slots.size
        · by_cases hz : t.slotAt i = 0
          · by_cases hn : t.next < t.back.size
            · simp only [install, if_pos hp, hq, hk, dif_pos hi,
                if_pos hz, dif_pos hn] at h
              have ha := Option.some.inj h
              subst a
              have hpF : req.parent < F.size := by
                simpa only [g.size_eq] using hp
              have hn' : t.next < c.region.maxNodes + 1 := by
                simpa only [g.back_size] using hn
              have hsize := g.size_eq
              have hRoom : F.numInserted < c.region.maxNodes := by
                first
                | change F.size - 1 < c.region.maxNodes
                  omega
                | change F.numInserted + 1 = t.next at hsize
                  omega
                | simp only [JumpForest.numInserted, JumpForest.size] at hsize ⊢
                  omega
              exact (appendLeafWords_spec g.layout hRoom hpF).2.1
            · simp [install, hp, hq, hk, hi, hz, hn] at h
          · simp only [install, if_pos hp, hq, hk, dif_pos hi, if_neg hz] at h
            have ha := Option.some.inj h
            subst a
            rfl
        · simp [install, hp, hq, hk, hi] at h
  · simp [install, hp] at h

private theorem stepPreparedLabelSize_of_success {H : LabelledQuotient}
    {c : Config H} {s : State H} {rank : Vertex H → Nat}
    {y : Vertex H} {xs : List (Vertex H)} {r : HeadResult H}
    (h : stepPrepared c s rank y xs = some r) :
    r.labels.size = s.labels.size := by
  by_cases hy : c.vertexIndex y < s.labels.size
  · cases hi : install c s.tables
        (ForestHead.runPrepared (selectors c s) rank y xs).step with
    | none => simp [stepPrepared, hy, hi] at h
    | some a =>
      simp only [stepPrepared, dif_pos hy, hi, Option.map] at h
      have hr := Option.some.inj h
      subst r
      simp
  · simp [stepPrepared, hy] at h

structure PreparedStepExactCapacity {H : LabelledQuotient}
    (c : Config H) (s : State H) (r : HeadResult H) : Prop where
  accesses_le : r.installed.accesses.length ≤ 14 * r.installed.delta
  lookup_trace :
    (installWithLookupTrace c s.tables r.measured.step).2 =
      (match r.measured.step.newPair with | none => [] | some q => [q])
  one_lookup_iff :
    (installWithLookupTrace c s.tables r.measured.step).2.length = 1 ↔
      r.measured.step.newPair ≠ none
  mem_size : r.installed.tables.mem.size = s.tables.mem.size
  slots_size : r.installed.tables.slots.size = s.tables.slots.size
  back_size : r.installed.tables.back.size = s.tables.back.size
  labels_size : r.labels.size = s.labels.size

theorem stepPrepared_exactCapacity {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat} {F : JumpForest}
    {s : State H} {row : Row H} {r : HeadResult H}
    (installs : PreparedInstalls c rank) (g : Grounded c F s.tables)
    (hs : ForestHead.TestSpec row.head row.tests)
    (hstep : stepPrepared c s rank row.head row.tests = some r) :
    PreparedStepExactCapacity c s r := by
  have hi := installs s row r hs hstep
  have hok := install_spec g hi
  have htrace := installLookupTrace_of_success hi
  refine ⟨hok.trace_bound, htrace, ?_, installMemSize_of_success g hi,
    hok.grounded.slot_size.trans g.slot_size.symm,
    hok.grounded.back_size.trans g.back_size.symm,
    stepPreparedLabelSize_of_success hstep⟩
  rw [htrace]
  cases r.measured.step.newPair <;> simp

end EX24.PreparedSweep
