module

public import PaperB.ForestRealCounts
public import PaperB.ForestInstallCapacity
public import Lean

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace EX24.PreparedSweep.ResidualUnit

open _root_.EX24.PreparedSweep.ChronologicalIndex

open AggregateEX24 EX24.PreStep PaperB PaperB.ForestHead
  PaperB.LabelledQuotient PaperB.PairLookup PaperB.Jumps

/-- Exact sums of access-log lengths and installation deltas on the
successful steps. The capacity witness also records the exact lookup
trace: empty for no request, singleton for a request. -/
inductive AppendTrace {H : LabelledQuotient}
    (c : Config H) (rank : Vertex H → Nat) :
    State H → List (Row H) → State H → Log H → Count → Nat → Nat → Prop where
  | nil (s : State H) : AppendTrace c rank s [] s [] Count.zero 0 0
  | cons {s out : State H} {row : Row H} {rows : List (Row H)}
      {r : HeadResult H} {log : Log H} {n : Count} {a d : Nat} :
      stepPrepared c s rank row.head row.tests = some r →
      PreparedStepExactCapacity c s r →
      AppendTrace c rank r.state rows out log n a d →
      AppendTrace c rank s (row :: rows) out
        (Event.ofResult row.head r :: log) (Count.prepend r n)
        (r.installed.accesses.length + a) (r.installed.delta + d)

theorem append_of_work {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {n : Count} {w : Work}
    (installs : PreparedInstalls c rank)
    (hw : WorkTrace c rank s rows out log n w)
    (sites : Sites c rank (SiteOK c rank) s rows) :
    ∃ a d, AppendTrace c rank s rows out log n a d := by
  revert sites
  induction hw with
  | nil s =>
    intro _
    exact ⟨0, 0, .nil s⟩
  | cons hs _ ih =>
    intro sites
    obtain ⟨hp, htail⟩ := sites _ hs
    obtain ⟨F, hg⟩ := hp.2.1
    have cap := stepPrepared_exactCapacity installs hg hp.1 hs
    obtain ⟨a, d, ht⟩ := ih htail
    exact ⟨_, _, .cons hs cap ht⟩

theorem AppendTrace.counted {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {n : Count} {a d : Nat}
    (ht : AppendTrace c rank s rows out log n a d) :
    CountedTrace c rank s rows out log n := by
  induction ht with
  | nil s => exact .nil s
  | cons hs _ _ ih => exact .cons hs ih

theorem AppendTrace.delta_eq_allocations {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat}
    {s out : State H} {rows : List (Row H)} {log : Log H} {n : Count} {a d : Nat}
    (ht : AppendTrace c rank s rows out log n a d) : d = n.allocations := by
  induction ht with
  | nil _ => rfl
  | cons _ _ _ ih => simp only [Count.prepend, ih]

theorem AppendTrace.accesses_le {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {n : Count} {a d : Nat}
    (ht : AppendTrace c rank s rows out log n a d) : a ≤ 14 * d := by
  induction ht with
  | nil _ => exact Nat.zero_le _
  | cons _ cap _ ih =>
    rw [Nat.mul_add]
    exact Nat.add_le_add cap.accesses_le ih

/-- One unit each per row visit, label bounds test, label write, event
formation, event cons, reversal visit, installation entry and return.
One unit per lookup dispatch, planner tick, search comparison, search
test and logged append access. Reserve `L` units per measured selector
call. No packed-read or dictionary-comparison charge. These are site
charges, not a claim that a site executes one primitive instruction. -/
def toll (L : Nat) (n : Count) (w : Work) (a : Nat) : Nat :=
  8 * n.heads + w.requests + w.planner + w.comparisons + w.tests +
    L * (w.atDepth + w.ancestry) + a

theorem toll_le_with_delta {H : LabelledQuotient} {L V E a d : Nat}
    {rows : List (Row H)} {n : Count} {w : Work}
    (b : Bounds L rows n w) (hv : rows.length = V)
    (he : entryTotal rows ≤ E) (hl : 1 ≤ L) (ha : a ≤ 14 * d) :
    toll L n w a ≤ 30 * (V + E) * L^2 + 14 * d := by
  let S := V + E
  let q := L * S
  let z := L * q
  have hn : n.heads = V := b.heads.trans hv
  have hs : S ≤ q := by
    simpa only [q, Nat.one_mul] using Nat.mul_le_mul_right S hl
  have hq : q ≤ z := by
    simpa only [z, Nat.one_mul] using Nat.mul_le_mul_right q hl
  have hvS : V ≤ S := by dsimp [S]; omega
  have heS : E ≤ S := by dsimp [S]; omega
  have hvq := Nat.le_trans hvS hs
  have hvz := Nat.le_trans hvq hq
  have hez := Nat.le_trans (Nat.le_trans heS hs) hq
  have hactive : w.activeHeads ≤ V := by
    simpa only [hn] using b.activeHeads
  have hsearch : w.comparisons + w.tests ≤ q := by
    have h := Nat.add_le_add b.comparisons b.tests
    rw [← Nat.mul_add] at h
    exact Nat.le_trans h (Nat.mul_le_mul_left L
      (Nat.add_le_add hactive (Nat.le_trans b.activeEntries he)))
  have hsel : w.atDepth + w.ancestry ≤ q + q := by
    have h₁ := b.atDepth
    have h₂ := b.ancestry
    omega
  have hsel' : L * (w.atDepth + w.ancestry) ≤ z + z := by
    simpa only [z, Nat.mul_add] using Nat.mul_le_mul_left L hsel
  have hp := b.planner
  have hr := b.requests
  have ht : toll L n w a ≤ 30 * z + 14 * d := by
    unfold toll
    omega
  have hz : z = (V + E) * L^2 := by
    change L * (L * S) = S * L^2
    calc
      L * (L * S) = (L * L) * S := (Nat.mul_assoc _ _ _).symm
      _ = S * (L * L) := Nat.mul_comm _ _
      _ = S * L^2 := by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul]
  simpa only [hz, Nat.mul_assoc] using ht

/-- Bound the charged control sites and the exact installation access trace. -/
theorem toll_le {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {n : Count} {w : Work} {L V E a d : Nat}
    (ht : AppendTrace c rank s rows out log n a d)
    (b : Bounds L rows n w) (hv : rows.length = V)
    (he : entryTotal rows ≤ E) (hl : 1 ≤ L) :
    toll L n w a ≤ 44 * (V + E) * L^2 := by
  have hn : n.heads = V := b.heads.trans hv
  have halloc : n.allocations ≤ V := by
    simpa only [hn] using b.allocations
  have hvS : V ≤ V + E := by omega
  have hLL : 1 ≤ L^2 := by
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using
      (Nat.mul_le_mul hl hl)
  have hbudget : V ≤ (V + E) * L^2 := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul hvS hLL
  have hdelta := Nat.le_trans (Nat.le_trans (Nat.le_of_eq ht.delta_eq_allocations) halloc) hbudget
  have h := toll_le_with_delta b hv he hl ht.accesses_le
  simp only [Nat.mul_assoc] at h ⊢
  omega

end EX24.PreparedSweep.ResidualUnit

namespace EX24.PreparedSweep

open PaperB PaperB.LabelledQuotient PaperB.ForestHead EX24.PreStep

theorem stepPrepared_writes_exact {H : LabelledQuotient} {c : Config H}
    {s : State H} {rank : Vertex H → Nat} {y : Vertex H} {xs : List (Vertex H)}
    {r : HeadResult H} (run : stepPrepared c s rank y xs = some r) :
    r.installed.writes = 1 + 7 * r.installed.delta := by
  unfold stepPrepared at run
  split at run
  · dsimp only at run
    let req := (runPrepared (selectors c s) rank y xs).step
    cases hit : install c s.tables req with
    | none => simp [req, hit] at run
    | some a =>
      change (install c s.tables req).map _ = _ at run
      rw [hit] at run
      have exactInstall := install_writes_exact hit
      simp only [Option.map_some, Option.some.injEq] at run
      subst r
      exact exactInstall
  · simp at run

/-- The exact successful sweep count includes the next-slot scalar update.
The backing-array writes are the label on every row and six per fresh key. -/
theorem CountedTrace.writes_exact {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat} {s out : State H}
    {rows : List (Row H)} {log : Log H} {n : Count}
    (trace : CountedTrace c rank s rows out log n) :
    n.writes = n.heads + 7 * n.allocations := by
  induction trace with
  | nil => rfl
  | cons run _ ih =>
    have writes := stepPrepared_writes_exact run
    simp only [Count.prepend, writes, ih, Nat.mul_add]
    omega

/-- The logical next-slot counter is the sole non-array write in the
per-row installation charge. -/
theorem CountedTrace.backing_writes_exact {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat} {s out : State H}
    {rows : List (Row H)} {log : Log H} {n : Count}
    (trace : CountedTrace c rank s rows out log n) :
    n.writes - n.allocations = n.heads + 6 * n.allocations := by
  have exactCount := trace.writes_exact
  omega

end EX24.PreparedSweep
