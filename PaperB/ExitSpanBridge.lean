module

public import PaperB.ExitSummary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitSpanBridge

open PaperB.ExitMap

/-- The one-endpoint form of the checked inverse-DFS-entry read. -/
def readEntry {N n : Nat} (unrank : Fin N → Fin N)
    (hold? : Fin N → Option (Fin n)) (k : Nat) : Option (Fin n) :=
  if hk : k < N then hold? (unrank ⟨k, hk⟩) else none

theorem readEntry_rank {N n : Nat} (rank unrank : Fin N → Fin N)
    (unrank_rank : ∀ v, unrank (rank v) = v)
    (hold? : Fin N → Option (Fin n)) (v : Fin N) :
    readEntry unrank hold? (rank v).val = hold? v := by
  unfold readEntry
  rw [dif_pos (rank v).isLt]
  change hold? (unrank (rank v)) = hold? v
  rw [unrank_rank v]

def toSpan {n : Nat} (read : Nat → Option (Fin n)) :
    Interval → Option (Fin n × Fin n)
  | .empty => none
  | .span lo hi => do
      let a ← read lo
      let b ← read hi
      return (a, b)

/--
For a ref coordinate `j`, use `ts := W.tails B (W.endpoint B j) y`.
The retained-to-ref equality followed by `ref` and `get_tab` gives `hs`
when the physical model was built with `entryRank := fun v => (I.rank v).val`.
Use `I.record_extrema` for `extrema` and `I.unrank_rank` for `unrank_rank`.

For EX44 use `Exact := SpanExact W.entry X`. If `X` is physical exit-tail
membership pulled back along `vertex`, `W.tails_iff` at `W.endpoint_mem B j`
gives `mem_iff`. `hold_reach` is the reachable-vertex coverage theorem
for the installed physical-to-held lookup, not a runtime search.
-/
theorem refCoordinate_exact {N n : Nat}
    (rank unrank : Fin N → Fin N)
    (unrank_rank : ∀ v, unrank (rank v) = v)
    (hold? : Fin N → Option (Fin n))
    (vertex : Fin n → Fin N) (entry : Fin n → Nat)
    (entry_eq : ∀ i, entry i = (rank (vertex i)).val)
    (Reach : Fin N → Prop)
    (hold_reach : ∀ v, Reach v →
      ∃ i, hold? v = some i ∧ vertex i = v)
    (ts : List (Fin N)) (reach : ∀ v ∈ ts, Reach v)
    (X : Fin n → Prop) (mem_iff : ∀ i, X i ↔ vertex i ∈ ts)
    (s : Interval)
    (hs : s = ExitSummary.summary (ts.map fun v => (rank v).val))
    (extrema : ts ≠ [] → ∃ a b, a ∈ ts ∧ b ∈ ts ∧
      ExitSummary.summary (ts.map fun v => (rank v).val) =
        .span (rank a).val (rank b).val ∧
      ∀ v ∈ ts,
        (rank a).val ≤ (rank v).val ∧ (rank v).val ≤ (rank b).val)
    {Exact : Option (Fin n × Fin n) → Prop}
    (exactEmpty : (∀ i, ¬ X i) → Exact none)
    (exactSpan : ∀ i j, X i → X j →
      (∀ k, X k → entry i ≤ entry k ∧ entry k ≤ entry j) →
      Exact (some (i, j))) :
    Exact (toSpan (readEntry unrank hold?) s) := by
  by_cases ht : ts = []
  · subst ts
    have hs0 : s = .empty := by
      simpa only [List.map_nil, ExitSummary.summary_nil] using hs
    rw [hs0, toSpan]
    apply exactEmpty
    intro i hi
    simpa using (mem_iff i).mp hi
  · obtain ⟨a, b, ha, hb, hab, bounds⟩ := extrema ht
    obtain ⟨i, hi, hvi⟩ := hold_reach a (reach a ha)
    obtain ⟨j, hj, hvj⟩ := hold_reach b (reach b hb)
    have hout : toSpan (readEntry unrank hold?) s = some (i, j) := by
      rw [hs.trans hab]
      simp only [toSpan, readEntry_rank rank unrank unrank_rank, hi, hj] <;> rfl
    rw [hout]
    apply exactSpan i j
    · apply (mem_iff i).mpr
      simpa only [hvi] using ha
    · apply (mem_iff j).mpr
      simpa only [hvj] using hb
    · intro k hk
      rw [entry_eq i, hvi, entry_eq j, hvj, entry_eq k]
      exact bounds (vertex k) ((mem_iff k).mp hk)

end PaperB.ExitSpanBridge
