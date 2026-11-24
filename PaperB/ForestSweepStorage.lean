module

public import PaperB.ForestEventChronology
public import PaperB.ForestActualFull

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace EX24.PreparedSweep.Storage

open PaperB PaperB.ForestHead PaperB.LabelledQuotient PaperB.Jumps
open EX24 EX24.PreStep EX24.PreparedSweep.ChronologicalIndex

/-!
EX2.4 — live storage at the compact fold's recursive-call boundaries.

The unit is an initialized array entry or a list entry with a
constant-size payload. In particular, a key, an optional back key, and
an event each have constant-size payloads. These are exact *charged
entry counts*, not Lean heap-byte counts or allocator capacities.

The input charge can use either the full retained row list or just the
remaining suffix. The immutable dictionary is charged once, separately
from its mutable slot column. No old state or HeadResult is charged as
retained by the fold. Temporary step storage, copy-on-write when a caller
retains an alias, and the transient storage of the final reversal are
not bounded by this checkpoint theorem.
-/

def columnCells {H : LabelledQuotient} (c : Config H) (s : State H) : Nat :=
  s.tables.mem.size + s.labels.size + c.dict.size +
    s.tables.slots.size + s.tables.back.size

def testCells {H : LabelledQuotient} : List (Row H) → Nat
  | [] => 0
  | row :: rows => row.tests.length + testCells rows

def inputCells {H : LabelledQuotient} (order : Array (Vertex H))
    (rows : List (Row H)) : Nat :=
  order.size + rows.length + testCells rows

def checkpointCells {H : LabelledQuotient} (c : Config H)
    (order : Array (Vertex H)) (retained : List (Row H))
    (s : State H) (rev : Log H) : Nat :=
  columnCells c s + inputCells order retained + rev.length

/-- A proof-only prefix of the actual `foldRowsAux` recursion.
`here` includes the initial call, the empty-suffix call, and the call
at which a row may fail. `more` crosses only a successful call. -/
inductive Visit {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat) :
    List (Row H) → State H → Log H →
    List (Row H) → State H → Log H → Nat → Prop where
  | here (rows : List (Row H)) (s : State H) (rev : Log H) :
      Visit c rank rows s rev rows s rev 0
  | more {s : State H} {row : Row H} {rows : List (Row H)}
      {rev : Log H} {r : HeadResult H} {todo : List (Row H)}
      {t : State H} {acc : Log H} {k : Nat} :
      stepPrepared c s rank row.head row.tests = some r →
      Visit c rank rows r.state (Event.ofResult row.head r :: rev) todo t acc k →
      Visit c rank (row :: rows) s rev todo t acc (k + 1)

theorem Visit.resume {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows todo : List (Row H)}
    {s t : State H} {rev acc : Log H} {k : Nat}
    (hv : Visit c rank rows s rev todo t acc k) :
    foldRowsAux c rank rows s rev = foldRowsAux c rank todo t acc := by
  induction hv with
  | here => rfl
  | more hs _ ih => simpa only [foldRowsAux, hs] using ih.symm |> Eq.symm

theorem Visit.actualPrefix {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows todo : List (Row H)}
    {s t : State H} {rev acc : Log H} {k : Nat}
    (hv : Visit c rank rows s rev todo t acc k) :
    ∃ done : List (Row H), rows = done ++ todo ∧ done.length = k ∧
      foldRowsAux c rank done s rev = some (t, acc.reverse) := by
  induction hv with
  | here => exact ⟨[], rfl, rfl, rfl⟩
  | @more s row rows rev r todo t acc k hs _ ih =>
    obtain ⟨done, hrows, hlen, hrun⟩ := ih
    refine ⟨row :: done, congrArg (List.cons row) hrows, ?_, ?_⟩
    · simp [hlen]
    · simpa only [foldRowsAux, hs] using hrun

theorem Visit.lengths {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows todo : List (Row H)}
    {s t : State H} {rev acc : Log H} {k : Nat}
    (hv : Visit c rank rows s rev todo t acc k) :
    acc.length = rev.length + k ∧ k + todo.length = rows.length := by
  induction hv with
  | here => simp
  | more _ _ ih =>
    rcases ih with ⟨ha, hr⟩
    simp only [List.length_cons] at ha ⊢
    constructor <;> omega

private theorem trace_visitsEnd {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows : List (Row H)} {s out : State H}
    {log : Log H} (ht : Trace c rank s rows out log) (rev : Log H) :
    ∃ acc : Log H, Visit c rank rows s rev [] out acc rows.length ∧
      acc.reverse = rev.reverse ++ log := by
  induction ht generalizing rev with
  | nil s =>
    exact ⟨rev, Visit.here [] s rev, by simp⟩
  | @cons s out row rows r log hs _ ih =>
    obtain ⟨acc, hv, he⟩ := ih (Event.ofResult row.head r :: rev)
    refine ⟨acc, ?_, ?_⟩
    · simpa only [List.length_cons] using Visit.more hs hv
    · simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append] using he

/-- A successful executable fold reaches the empty-suffix checkpoint.
The returned log has the same entry count as the reversed log there. -/
theorem foldRows_endCheckpoint {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows : List (Row H)} {s out : State H}
    {log : Log H} (hrun : foldRows c rank rows s = some (out, log)) :
    ∃ rev : Log H, Visit c rank rows s [] [] out rev rows.length ∧
      log = rev.reverse ∧ log.length = rows.length := by
  have ht := foldRows_trace hrun
  obtain ⟨rev, hv, he⟩ := trace_visitsEnd ht []
  exact ⟨rev, hv, by simpa using he.symm, ht.length⟩

/-!
Only the size projections of `PreparedStepExactCapacity` are needed here.
With its defining module imported, the adapter is:

  fun g hs h =>
    let e := stepPrepared_exactCapacity installs g hs h
    ⟨e.mem_size, e.slots_size, e.back_size, e.labels_size⟩

The defining module's path is not supplied, so the checked adapter below
uses the same preservation proofs without importing the lookup/work
accounting. In particular it does not assume an arena-size or work bound.
-/

def PreservesColumns {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) : Prop :=
  ∀ {F : JumpForest} {s : State H} {row : Row H} {r : HeadResult H},
    Grounded c F s.tables → TestSpec row.head row.tests →
    stepPrepared c s rank row.head row.tests = some r →
    r.installed.tables.mem.size = s.tables.mem.size ∧
    r.installed.tables.slots.size = s.tables.slots.size ∧
    r.installed.tables.back.size = s.tables.back.size ∧
    r.labels.size = s.labels.size

private theorem install_mem_size {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} {req : ForestHead.Step H}
    {a : Installed H} (g : Grounded c F t)
    (h : install c t req = some a) :
    a.tables.mem.size = t.mem.size := by
  by_cases hp : req.parent < t.next
  · cases hq : req.newPair with
    | none =>
      simp only [install, if_pos hp, hq] at h
      have he := Option.some.inj h
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
              have he := Option.some.inj h
              subst a
              have hpF : req.parent < F.size := by
                simpa only [g.size_eq] using hp
              have hn' : t.next < c.region.maxNodes + 1 := by
                simpa only [g.back_size] using hn
              have hsize := g.size_eq
              have hroom : F.numInserted < c.region.maxNodes := by
                first
                | change F.size - 1 < c.region.maxNodes
                  omega
                | change F.numInserted + 1 = t.next at hsize
                  omega
                | simp only [JumpForest.numInserted, JumpForest.size] at hsize ⊢
                  omega
              exact (appendLeafWords_spec g.layout hroom hpF).2.1
            · simp [install, hp, hq, hk, hi, hz, hn] at h
          · simp only [install, if_pos hp, hq, hk, dif_pos hi, if_neg hz] at h
            have he := Option.some.inj h
            subst a
            rfl
        · simp [install, hp, hq, hk, hi] at h
  · simp [install, hp] at h

theorem preservesColumns {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat}
    (distinct : ∀ a b : Vertex H, rank a = rank b → a = b) :
    PreservesColumns c rank := by
  intro F s row r g hs h
  have parts := prepared_parts (row := row) hs distinct h
  have hi := parts.2.1
  have g' := (install_spec g hi).grounded
  exact ⟨install_mem_size g hi, g'.slot_size.trans g.slot_size.symm,
    g'.back_size.trans g.back_size.symm, parts.2.2.1⟩

theorem Visit.grounded_sizes {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows todo : List (Row H)}
    {s t : State H} {rev acc : Log H} {k : Nat}
    (hv : Visit c rank rows s rev todo t acc k)
    (installs : PreparedInstalls c rank) (preserve : PreservesColumns c rank) :
    ∀ {F : JumpForest}, Grounded c F s.tables →
      (∀ row ∈ rows, TestSpec row.head row.tests) →
      (∃ G : JumpForest, Grounded c G t.tables) ∧
      t.tables.mem.size = s.tables.mem.size ∧ t.labels.size = s.labels.size := by
  induction hv with
  | here =>
    intro F g _
    exact ⟨⟨F, g⟩, rfl, rfl⟩
  | @more s row rows rev r todo t acc k hs _ ih =>
    intro F g specs
    have T := specs row (by simp)
    have g' := (install_spec g (installs s row r T hs)).grounded
    have cap := preserve (row := row) g T hs
    obtain ⟨hg, hm, hl⟩ := ih g'
      (fun a ha => specs a (List.mem_cons_of_mem row ha))
    exact ⟨hg, hm.trans cap.1, hl.trans cap.2.2.2⟩

private theorem testCells_append {H : LabelledQuotient}
    (xs ys : List (Row H)) :
    testCells (xs ++ ys) = testCells xs + testCells ys := by
  induction xs with
  | nil => simp [testCells]
  | cons x xs ih => simp [testCells, ih, Nat.add_assoc]

/-- Exact charge at every visited state. Take `retained := todo` for the
remaining input or `retained := rows` if the full input stays live. -/
theorem Visit.root_exact {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {mem : Array Nat} {vertexCapacity : Nat}
    {rows todo : List (Row H)} {t : State H} {rev : Log H} {k : Nat}
    (hv : Visit c rank rows (initial c mem vertexCapacity) [] todo t rev k)
    (layout : JumpWordLayout c.region JumpForest.init mem)
    (ready : Ready rank rows) (order : Array (Vertex H))
    (retained : List (Row H)) :
    rev.length = k ∧ k ≤ rows.length ∧
      checkpointCells c order retained t rev =
        mem.size + vertexCapacity + 2 * c.dict.size + (c.region.maxNodes + 1) +
          inputCells order retained + k := by
  have g := initial_grounded c layout rfl vertexCapacity
  obtain ⟨⟨G, gt⟩, hm, hl⟩ := hv.grounded_sizes
    (preparedInstalls c rank ready.distinctRanks)
    (preservesColumns ready.distinctRanks) g ready.specs
  change t.tables.mem.size = mem.size at hm
  have hl' : t.labels.size = vertexCapacity := hl.trans (by simp [initial])
  obtain ⟨hr, hk⟩ := hv.lengths
  have hr' : rev.length = k := by simpa using hr
  refine ⟨hr', by omega, ?_⟩
  unfold checkpointCells columnCells
  rw [hm, hl', gt.slot_size, gt.back_size, hr']
  omega

/-- Uniform upper bound, even if the starting order array and all rows
and test lists stay live throughout the sweep. -/
theorem Visit.root_bound {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {mem : Array Nat} {vertexCapacity : Nat}
    {rows todo : List (Row H)} {t : State H} {rev : Log H} {k : Nat}
    (hv : Visit c rank rows (initial c mem vertexCapacity) [] todo t rev k)
    (layout : JumpWordLayout c.region JumpForest.init mem)
    (ready : Ready rank rows) (order : Array (Vertex H)) :
    checkpointCells c order todo t rev ≤ checkpointCells c order rows t rev ∧
    checkpointCells c order rows t rev ≤
      mem.size + vertexCapacity + 2 * c.dict.size + (c.region.maxNodes + 1) +
        inputCells order rows + rows.length := by
  obtain ⟨done, hrows, _, _⟩ := hv.actualPrefix
  obtain ⟨_, hk, he⟩ := hv.root_exact layout ready order rows
  constructor
  · have hi : inputCells order todo ≤ inputCells order rows := by
      simp only [inputCells, hrows, List.length_append, testCells_append]
      omega
    unfold checkpointCells
    omega
  · omega

/-- Ordered specialization, stated by transport so it needs no import of
the packed dictionary builder. For the actual `packedOrderedConfig p large`,
use `packedOrderedConfig_eq p large` as `hc`.

The remaining terms are direct capacities: the initialized image, the
back column, and the entries in the actual test lists. The `6 * n` charges
labels, keys, slots, the starting order, row entries, and event entries.
No sorting banks or accumulated writes are included in the sweep charge. -/
theorem Visit.ordered_bound {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (large : 3 ≤ H.vertexCount) {c : Config H} (hc : c = orderedConfig p large)
    {rank : Vertex H → Nat}
    {todo : List (Row H)} {t : State H} {rev : Log H} {k : Nat}
    (ready : Ready rank (orderedRows p data size_data))
    (hv : Visit c rank (orderedRows p data size_data)
      (initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount)
      [] todo t rev k) :
    checkpointCells c data (orderedRows p data size_data) t rev ≤
      (ConcreteInit.initImage H.vertexCount).1.size + (c.region.maxNodes + 1) +
        testCells (orderedRows p data size_data) + 6 * H.vertexCount := by
  have layout : JumpWordLayout c.region JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1 := by
    rw [hc]
    change JumpWordLayout (ConcreteInit.region H.vertexCount) JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1
    exact?
  have hd : c.dict.size ≤ H.vertexCount := by
    rw [hc]
    change (ForestDictionary.dictionary p orderedPairCode).size ≤ H.vertexCount
    exact (ForestDictionary.dictionary_spec p orderedPairCode).2.2
  have hn : (orderedRows p data size_data).length = H.vertexCount := by
    first
    | simpa [orderedRows, size_data]
    | exact?
  have hb := (hv.root_bound layout ready data).2
  simp only [inputCells, size_data, hn] at hb
  omega

/-- Convert direct capacity estimates to a numerical linear coefficient.
This does not infer a bound on the test input from the vertex count. -/
theorem linear_of_capacity_bounds
    {used arena back tests n a b d : Nat}
    (hused : used ≤ arena + back + tests + 6 * n)
    (ha : arena ≤ a * (n + 1)) (hb : back ≤ b * (n + 1))
    (hd : tests ≤ d * (n + 1)) :
    used ≤ (a + b + d + 6) * (n + 1) := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one] at *
  omega

end EX24.PreparedSweep.Storage
