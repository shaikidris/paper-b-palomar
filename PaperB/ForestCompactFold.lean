module

public import PaperB.ForestPreparedHead
public import PaperB.ForestEndpoints
public import PaperB.ForestWordLaws

public import PaperB.ForestPreparedHead
public import PaperB.ForestEndpoints
public import PaperB.ForestWordLaws

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace EX24

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient
open PreStep

namespace PreparedSweep

/-- The executable fields of a prepared row. -/
structure Row (H : LabelledQuotient) where
  head : Vertex H
  tests : List (Vertex H)

/-- One event per successful row. `parent` is the request's parent;
`newKey` is recorded only on allocation. No state or row tests are retained. -/
structure Event (H : LabelledQuotient) where
  head : Vertex H
  node : Nat
  fresh : Bool
  parent : Nat
  newKey : Option (CutPair H)

def Event.ofResult {H : LabelledQuotient} (head : Vertex H)
    (r : HeadResult H) : Event H :=
  ⟨head, r.installed.node, r.installed.allocated, r.measured.step.parent,
    if r.installed.allocated then r.measured.step.newPair else none⟩

abbrev Log (H : LabelledQuotient) := List (Event H)

/-- The recursive call carries only the next state and the reversed event
log. The final reversal restores the input row order. -/
def foldRowsAux {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) :
    List (Row H) → State H → Log H → Option (State H × Log H)
  | [], s, rev => some (s, rev.reverse)
  | row :: rows, s, rev =>
    match stepPrepared c s rank row.head row.tests with
    | none => none
    | some r =>
      let event := Event.ofResult row.head r
      let next := r.state
      foldRowsAux c rank rows next (event :: rev)

def foldRows {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    (rows : List (Row H)) (s : State H) : Option (State H × Log H) :=
  foldRowsAux c rank rows s []

def fromRoot {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    (mem : Array Nat) (vertexCapacity : Nat) (rows : List (Row H)) :
    Option (State H × Log H) :=
  foldRows c rank rows (initial c mem vertexCapacity)

/-- Each `cons` witnesses the actual call on that row and pre-state. The
`HeadResult` is a witness in this proposition, not an executable log entry. -/
inductive Trace {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat) :
    State H → List (Row H) → State H → Log H → Prop where
  | nil (s : State H) : Trace c rank s [] s []
  | cons {s out : State H} {row : Row H} {rows : List (Row H)}
      {r : HeadResult H} {log : Log H} :
      stepPrepared c s rank row.head row.tests = some r →
      Trace c rank r.state rows out log →
      Trace c rank s (row :: rows) out (Event.ofResult row.head r :: log)

private theorem foldRowsAux_trace {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows : List (Row H)} {s out : State H}
    {rev log : Log H}
    (h : foldRowsAux c rank rows s rev = some (out, log)) :
    ∃ events : Log H, Trace c rank s rows out events ∧
      log = rev.reverse ++ events := by
  induction rows generalizing s out rev log with
  | nil =>
    change some (s, rev.reverse) = some (out, log) at h
    have e := Option.some.inj h
    have hs : s = out := congrArg Prod.fst e
    have hl : rev.reverse = log := congrArg Prod.snd e
    subst out
    exact ⟨[], Trace.nil s, by simpa only [List.append_nil] using hl.symm⟩
  | cons row rows ih =>
    cases hr : stepPrepared c s rank row.head row.tests with
    | none => simp [foldRowsAux, hr] at h
    | some r =>
      have ht : foldRowsAux c rank rows r.state
          (Event.ofResult row.head r :: rev) = some (out, log) := by
        simpa only [foldRowsAux, hr] using h
      obtain ⟨events, htrace, hlog⟩ :=
        ih (s := r.state) (out := out)
          (rev := Event.ofResult row.head r :: rev) (log := log) ht
      refine ⟨Event.ofResult row.head r :: events, Trace.cons hr htrace, ?_⟩
      simpa only [List.reverse_cons, List.append_assoc, List.cons_append,
        List.nil_append] using hlog

theorem foldRows_trace {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {rows : List (Row H)} {s out : State H}
    {log : Log H} (h : foldRows c rank rows s = some (out, log)) :
    Trace c rank s rows out log := by
  change foldRowsAux c rank rows s [] = some (out, log) at h
  obtain ⟨events, ht, he⟩ := foldRowsAux_trace h
  have hlog : log = events := by simpa using he
  rw [hlog]
  exact ht

theorem fromRoot_trace {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {mem : Array Nat} {vertexCapacity : Nat}
    {rows : List (Row H)} {out : State H} {log : Log H}
    (h : fromRoot c rank mem vertexCapacity rows = some (out, log)) :
    Trace c rank (initial c mem vertexCapacity) rows out log := by
  change foldRows c rank rows (initial c mem vertexCapacity) =
    some (out, log) at h
  exact foldRows_trace h

/-- The trace preserves the entire head sequence, not just its length. -/
theorem Trace.heads {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} (ht : Trace c rank s rows out log) :
    log.map Event.head = rows.map Row.head := by
  induction ht with
  | nil => rfl
  | cons _ _ ih => simp [Event.ofResult, ih]

theorem Trace.length {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} (ht : Trace c rank s rows out log) :
    log.length = rows.length := by
  simpa only [List.length_map] using congrArg List.length ht.heads

/-- Static hypotheses for a later topological induction. Strict order
excludes repeated heads; vertex coverage is a separate hypothesis. -/
structure Ready {H : LabelledQuotient} (rank : Vertex H → Nat)
    (rows : List (Row H)) : Prop where
  distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b
  ordered : rows.Pairwise (fun a b => rank a.head < rank b.head)
  specs : ∀ row, row ∈ rows → TestSpec row.head row.tests

theorem Ready.tail {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {rows : List (Row H)} (h : Ready rank (row :: rows)) :
    Ready rank rows :=
  ⟨h.distinctRanks, (List.pairwise_cons.mp h.ordered).2,
    fun r hr => h.specs r (List.mem_cons_of_mem row hr)⟩

theorem Ready.head_spec {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {rows : List (Row H)} (h : Ready rank (row :: rows)) :
    TestSpec row.head row.tests :=
  h.specs row (by simp)

theorem Ready.head_lt {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row r : Row H} {rows : List (Row H)} (h : Ready rank (row :: rows))
    (hr : r ∈ rows) : rank row.head < rank r.head :=
  (List.pairwise_cons.mp h.ordered).1 r hr

/-- Optional accounting for a proof. The executable sweep does not compute
these totals or retain the word-access lists used to justify them. -/
structure Count where
  heads : Nat
  allocations : Nat
  writes : Nat

def Count.zero : Count := ⟨0, 0, 0⟩

def Count.prepend {H : LabelledQuotient} (r : HeadResult H) (tail : Count) :
    Count :=
  ⟨1 + tail.heads, r.installed.delta + tail.allocations,
    r.installed.writes + tail.writes⟩

inductive CountedTrace {H : LabelledQuotient}
    (c : Config H) (rank : Vertex H → Nat) :
    State H → List (Row H) → State H → Log H → Count → Prop where
  | nil (s : State H) : CountedTrace c rank s [] s [] Count.zero
  | cons {s out : State H} {row : Row H} {rows : List (Row H)}
      {r : HeadResult H} {log : Log H} {n : Count} :
      stepPrepared c s rank row.head row.tests = some r →
      CountedTrace c rank r.state rows out log n →
      CountedTrace c rank s (row :: rows) out
        (Event.ofResult row.head r :: log) (Count.prepend r n)

theorem Trace.exists_count {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} (ht : Trace c rank s rows out log) :
    ∃ n : Count, CountedTrace c rank s rows out log n := by
  induction ht with
  | nil s => exact ⟨Count.zero, CountedTrace.nil s⟩
  | cons hs _ ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨_, CountedTrace.cons hs hn⟩

theorem CountedTrace.forget {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {n : Count} (ht : CountedTrace c rank s rows out log n) :
    Trace c rank s rows out log := by
  induction ht with
  | nil s => exact Trace.nil s
  | cons hs _ ih => exact Trace.cons hs ih

theorem root_invariant {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) {mem : Array Nat}
    (layout : JumpWordLayout c.region JumpForest.init mem)
    (vertexCapacity : Nat) :
    Grounded c JumpForest.init (initial c mem vertexCapacity).tables ∧
      Nonempty (Embedding c (initial c mem vertexCapacity) JumpForest.init
        rank initialUp (fun _ => False)) :=
  ⟨initial_grounded c layout rfl vertexCapacity,
    ⟨initial_embedding c rank layout vertexCapacity⟩⟩

/-- Transfer one-step existence from the original kernel to the packed call. -/
theorem prepared_exists_of_step {H : LabelledQuotient} {c : Config H}
    {s : State H} {rank : Vertex H → Nat} {row : Row H}
    (T : TestSpec row.head row.tests)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (hex : ∃ r, step c s rank row.head row.tests = some r) :
    ∃ r, stepPrepared c s rank row.head row.tests = some r := by
  have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
    fun {a b} h => distinctRanks a b h
  simpa only [stepPrepared_eq_step c s rank row.head row.tests T inj] using hex

/-- One prepared call succeeds under the original kernel's local premises.
No claim is made that those premises hold at every row of the sweep. -/
theorem prepared_step_exists {H : LabelledQuotient} {c : Config H}
    {s : State H} {F : JumpForest} {rank : Vertex H → Nat} {row : Row H}
    (T : TestSpec row.head row.tests)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (g : Grounded c F s.tables)
    (hy : c.vertexIndex row.head < s.labels.size)
    (hp : (ForestHead.runHead (selectors c s) rank row.head row.tests).step.parent <
      s.tables.next)
    (cover : ∀ q, (ForestHead.runHead (selectors c s) rank row.head row.tests).step.newPair =
      some q → ∃ i, (PairLookup.lookup c.dict (c.code q)).1 = some i ∧
        (s.tables.slotAt i = 0 → s.tables.next < s.tables.back.size)) :
    ∃ r, stepPrepared c s rank row.head row.tests = some r := by
  exact prepared_exists_of_step (c := c) (s := s) (rank := rank) (row := row)
    T distinctRanks
    (step_exists (y := row.head) (xs := row.tests) g hy hp cover)

/-- A successful packed call has the same one-step install and label
equations as the original kernel. -/
theorem prepared_parts {H : LabelledQuotient} {c : Config H}
    {s : State H} {rank : Vertex H → Nat} {row : Row H} {r : HeadResult H}
    (T : TestSpec row.head row.tests)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (h : stepPrepared c s rank row.head row.tests = some r) :
    r.measured = ForestHead.runHead (selectors c s) rank row.head row.tests ∧
    install c s.tables r.measured.step = some r.installed ∧
    r.labels.size = s.labels.size ∧
    ∀ j, r.labels[j]? =
      if j = c.vertexIndex row.head then some r.installed.node else s.labels[j]? := by
  have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
    fun {a b} he => distinctRanks a b he
  rw [stepPrepared_eq_step c s rank row.head row.tests T inj] at h
  exact step_parts h

end PreparedSweep
end EX24
