module

public import PaperB.StaticOracleTree
public import PaperB.RetainedRouteProof

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.EX44.RetainedRouteProof
open PaperB.Digraph

namespace OriginalStaticConnector

open PaperB.EX16Assembly

variable {g : Digraph} {r : Fin g.vertexCount} {k B E : Nat}

def world (q : OriginalReader g r) : World g q.count :=
  World.mk (vertex := q.ids.originals.read)
    (entry := fun x => (q.reader.entry x : Nat))
    (fun x => (q.reader.stop x : Nat) - 1)

/-- Install only the scan-backed fields. The remaining lookups and their
    contracts belong to the caller. -/
def install (q : OriginalReader g r) (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    Runtime g.vertexCount q.count k B E :=
  { base with
    source := q.slot r hr
    translate := fun i => ⟨q.ids.find i, debit, hdebit⟩
    ancestor := fun a x => ⟨q.reader.isAncestor a x, debit, hdebit⟩ }

theorem source_vertex (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    (world q).vertex (install q hr base debit hdebit).source = r :=
  q.original_at_slot r hr

theorem normalizedIDs (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B) :
    NormalizedIDs (install q hr base debit hdebit) (world q) := by
  constructor
  · intro i x
    change q.ids.find i = some x ↔ q.ids.originals.read x = i
    exact q.find_eq_some_iff_original i x
  · intro i
    change q.ids.find i = none ↔
      ¬ g.InitiallyReachable
        ((world q).vertex (install q hr base debit hdebit).source) i
    rw [source_vertex q hr base debit hdebit]
    exact q.ids.miss_iff i

theorem dominance (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B)
    (a x : Fin q.count) :
    g.Dominates ((world q).vertex (install q hr base debit hdebit).source)
      ((world q).vertex a) ((world q).vertex x) ↔
      (world q).Inside a x := by
  rw [source_vertex q hr base debit hdebit]
  change g.Dominates r (q.ids.originals.read a) (q.ids.originals.read x) ↔
    (q.reader.entry a : Nat) ≤ (q.reader.entry x : Nat) ∧
    (q.reader.entry x : Nat) ≤ (q.reader.stop a : Nat) - 1
  rw [q.held_dominates_iff_interval a x]
  -- Positivity rules out the spurious `stop = 0` case of Nat subtraction.
  have hself := ((q.reader.ancestor_iff_interval a a).mp (by
    first
    | exact ⟨0, rfl⟩
    | rfl
    | exact?)).2
  have hstop : 0 < (q.reader.stop a : Nat) := by omega
  constructor <;> intro h
  · have hx := h.2
    exact ⟨h.1, by omega⟩
  · have hx := h.2
    exact ⟨h.1, by omega⟩

end OriginalStaticConnector

end PaperB.EX44.RetainedRouteProof
