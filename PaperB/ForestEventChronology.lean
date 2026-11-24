module

public import PaperB.ForestTopologicalTotal

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Append after the supplied EX24 source. The two source interfaces are
`PreparedInstalls` and `AppendParents`. Their proofs require the omitted
prepared-step and jump-forest material.

The scatter uses the real child slot as the real/real map slot. Edges
whose installed parent is 0 do not receive a scatter entry.
-/

namespace EX24

open PaperB PaperB.ForestHead PaperB.LabelledQuotient EX24.PreStep
namespace PreparedSweep
namespace ChronologicalIndex

def PreparedInstalls {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) : Prop :=
  ∀ (s : State H) (row : Row H) (r : HeadResult H),
    TestSpec row.head row.tests →
    stepPrepared c s rank row.head row.tests = some r →
    install c s.tables r.measured.step = some r.installed

theorem preparedInstalls {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b) :
    PreparedInstalls c rank := by
  intro s row r hs hstep
  exact (prepared_parts (row := row) hs distinctRanks hstep).2.1
def storedParent {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} (g : Grounded c F t) (k : Nat) : Nat :=
  if hk : k < F.size then
    (boundedJumpParent g.layout.valid ⟨k, hk⟩).val
  else
    0

structure AppendParents {H : LabelledQuotient} (c : Config H) : Prop where
  old : ∀ {F : JumpForest} {t u : Tables H} {p : Nat}
    (g : Grounded c F t) (g' : Grounded c (F.appendLeaf p) u),
    p < F.size → ∀ k, k < t.next → storedParent g' k = storedParent g k
  new : ∀ {F : JumpForest} {t u : Tables H} {p : Nat}
    (g : Grounded c F t) (g' : Grounded c (F.appendLeaf p) u),
    p < F.size → storedParent g' t.next = p

theorem appendParents {H : LabelledQuotient} (c : Config H) : AppendParents c := by
  constructor
  · intro F t u p g g' _hp k hk
    have hkF : k < F.size := by simpa only [g.size_eq] using hk
    have hkA : k < (F.appendLeaf p).size := by
      rw [JumpForest.size_appendLeaf]
      omega
    simp only [storedParent, dite_eq_left hkA, dite_eq_left hkF]
    change (F.appendLeaf p).parentOf k = F.parentOf k
    exact parentOf_appendLeaf_old F p hkF
  · intro F t u p g g' hp
    have he : t.next = F.size := by simp only [g.size_eq]
    rw [he]
    have hkA : F.size < (F.appendLeaf p).size := by
      rw [JumpForest.size_appendLeaf]
      omega
    simp only [storedParent, dite_eq_left hkA]
    change (F.appendLeaf p).parentOf F.size = p
    unfold JumpForest.parentOf
    rw [recordAt_appendLeaf_new] <;> first | rfl | simp [JumpForest.mkAppendedRecord, *]
private theorem storedParent_congr {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t u : Tables H} (h : u = t)
    (gu : Grounded c F u) (gt : Grounded c F t) (k : Nat) :
    storedParent gu k = storedParent gt k := by
  subst u
  rfl

def Filled {H : LabelledQuotient} (t : Tables H) : Prop :=
  ∀ k, 0 < k → k < t.next → ∃ q, t.back[k]? = some (some q)

private theorem request_parent_lt {H : LabelledQuotient} {c : Config H}
    {t : Tables H} {req : ForestHead.Step H} {a : Installed H}
    (h : install c t req = some a) : req.parent < t.next := by
  by_cases hp : req.parent < t.next
  · exact hp
  · simp [install, hp] at h

private theorem fresh_install {H : LabelledQuotient} {c : Config H}
    {F : JumpForest} {t : Tables H} {req : ForestHead.Step H}
    {a : Installed H} (g : Grounded c F t)
    (h : install c t req = some a) (hf : a.allocated = true) :
    a.node = t.next ∧
      ∃ q, req.newPair = some q ∧ a.tables.back[a.node]? = some (some q) := by
  have hp := request_parent_lt h
  cases hq : req.newPair with
  | none =>
    simp only [install, if_pos hp, hq] at h
    have he := Option.some.inj h
    rw [← he] at hf
    cases hf
  | some q =>
    cases hk : (PairLookup.lookup c.dict (c.code q)).1 with
    | none => simp [install, hp, hq, hk] at h
    | some i =>
      obtain ⟨hi, _⟩ :=
        (PairLookup.lookup_eq_some_iff c.dict (c.code q) c.sorted i).mp hk
      have hb : i < t.slots.size := by
        simpa only [g.slot_size] using hi
      by_cases hz : t.slotAt i = 0
      · by_cases hn : t.next < t.back.size
        · simp [install, hp, hq, hk, hb, hz, hn] at h
          exact match a, h with
          | _, rfl => by
            refine ⟨rfl, q, rfl, ?_⟩
            change (t.back.set t.next (some q) hn)[t.next]? = some (some q)
            have hidx : t.next < (t.back.set t.next (some q) hn).size := by
              simpa only [Array.size_set] using hn
            rw [getElem?_def, dite_eq_left hidx] <;> simp
        · simp [install, hp, hq, hk, hb, hz, hn] at h
      · simp [install, hp, hq, hk, hb, hz] at h
        rw [← h] at hf
        cases hf

/-- A proof-only view of the log. The intermediate tables are those
obtained in the induction on `Trace`; they are not log entries. -/
inductive SlotRun {H : LabelledQuotient} :
    Tables H → Log H → Tables H → Prop where
  | nil (t : Tables H) : SlotRun t [] t
  | reuse {t u out : Tables H} {e : Event H} {es : Log H} :
      e.fresh = false →
      e.node < t.next →
      (0 < e.node → ∃ q, t.back[e.node]? = some (some q)) →
      u.next = t.next →
      SlotRun u es out →
      SlotRun t (e :: es) out
  | alloc {t u out : Tables H} {e : Event H} {es : Log H} :
      e.fresh = true →
      e.node = t.next →
      e.parent < t.next →
      u.next = t.next + 1 →
      SlotRun u es out →
      SlotRun t (e :: es) out

theorem SlotRun.next_le {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out) :
    t.next ≤ out.next := by
  induction h with
  | nil => exact Nat.le_refl _
  | reuse _ _ _ hn _ ih => omega
  | alloc _ _ _ hn _ ih => omega

theorem SlotRun.node_lt {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out) :
    ∀ e ∈ log, e.node < out.next := by
  induction h with
  | nil => simp
  | @reuse t u out x xs hf hx ho hn ht ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      have hu := ht.next_le
      omega
    · exact ih e he
  | @alloc t u out x xs hf hx hp hn ht ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      have hu := ht.next_le
      omega
    · exact ih e he

theorem SlotRun.fresh_ge {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out) :
    ∀ e ∈ log, e.fresh = true → t.next ≤ e.node := by
  induction h with
  | nil => simp
  | @reuse t u out x xs hf hx ho hn ht ih =>
    intro e he hfe
    rcases List.mem_cons.mp he with he | he
    · subst e
      simp [hf] at hfe
    · simpa only [hn] using ih e he hfe
  | @alloc t u out x xs hf hx hp hn ht ih =>
    intro e he hfe
    rcases List.mem_cons.mp he with he | he
    · subst e
      omega
    · have hh := ih e he hfe
      omega

/-- The split singles out the first selection of `k`. Every later
selection of `k` is a reuse, even if event values repeat. -/
def FirstCreation {H : LabelledQuotient} (log : Log H) (k : Nat) : Prop :=
  ∃ (pre : Log H) (e : Event H) (post : Log H),
    log = pre ++ e :: post ∧ e.node = k ∧ e.fresh = true ∧
    (∀ x ∈ pre, x.node ≠ k) ∧
    (∀ x ∈ post, x.node = k → x.fresh = false)

private theorem FirstCreation.prepend {H : LabelledQuotient}
    {es : Log H} {x : Event H} {k : Nat}
    (h : FirstCreation es k) (hx : x.node ≠ k) :
    FirstCreation (x :: es) k := by
  obtain ⟨pre, e, post, he, hn, hf, hb, ha⟩ := h
  refine ⟨x :: pre, e, post, ?_, hn, hf, ?_, ha⟩
  · exact congrArg (List.cons x) he
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact hx
    · exact hb z hz

theorem SlotRun.first {H : LabelledQuotient}
    {t out : Tables H} {log : Log H} (h : SlotRun t log out) :
    ∀ k, t.next ≤ k → k < out.next → FirstCreation log k := by
  induction h with
  | nil =>
    intro k hk ho
    omega
  | @reuse t u out x xs hf hx ho hn ht ih =>
    intro k hk hb
    exact (ih k (by omega) hb).prepend (by omega)
  | @alloc t u out x xs hf hx hp hn ht ih =>
    intro k hk hb
    by_cases he : k = t.next
    · refine ⟨[], x, xs, rfl, hx.trans he.symm, hf, ?_, ?_⟩
      · simp
      · intro z hz hzk
        cases hzf : z.fresh with
        | false => rfl
        | true =>
          have hge := ht.fresh_ge z hz hzf
          omega
    · exact (ih k (by omega) hb).prepend (by omega)

structure Chronology {H : LabelledQuotient} (c : Config H)
    {F : JumpForest} {s : State H} (g : Grounded c F s.tables)
    (out : State H) (log : Log H) : Prop where
  slots : SlotRun s.tables log out.tables
  final : ∃ (G : JumpForest) (go : Grounded c G out.tables),
    Filled out.tables ∧
    (∀ k, k < s.tables.next → storedParent go k = storedParent g k) ∧
    (∀ k, k < s.tables.next → out.tables.back[k]? = s.tables.back[k]?) ∧
    (∀ e ∈ log, e.fresh = true →
      storedParent go e.node = e.parent ∧
      ∃ q, e.newKey = some q ∧ out.tables.back[e.node]? = some (some q))

theorem traceChronology {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} (prepared : PreparedInstalls c rank)
    (parents : AppendParents c) {s out : State H} {rows : List (Row H)}
    {log : Log H} (ht : Trace c rank s rows out log) {F : JumpForest}
    (g : Grounded c F s.tables) (fill : Filled s.tables)
    (specs : ∀ row ∈ rows, TestSpec row.head row.tests) :
    Chronology c g out log := by
  induction ht generalizing F with
  | nil s =>
    refine ⟨.nil s.tables, F, g, fill, ?_, ?_, ?_⟩
    · intro k hk
      rfl
    · intro k hk
      rfl
    · simp
  | @cons s out row rows r log hr ht ih =>
    have hi := prepared s row r (specs row (by simp)) hr
    have ok := install_spec g hi
    have ts : ∀ x ∈ rows, TestSpec x.head x.tests :=
      fun x hx => specs x (List.mem_cons_of_mem row hx)
    cases ha : r.installed.allocated with
    | false =>
      have eqt : r.state.tables = s.tables := ok.no_allocation ha
      have gn : Grounded c F r.state.tables := by
        change Grounded c F r.installed.tables
        simpa [ha] using ok.grounded
      have fn : Filled r.state.tables := by
        simpa only [eqt] using fill
      have hk : r.installed.node < s.tables.next := by
        have hh : r.installed.node < r.state.tables.next := ok.node_lt
        simpa only [eqt] using hh
      obtain ⟨run, ⟨G, go, fg, hop, hob, hnew⟩⟩ :=
        ih (F := F) gn fn ts
      refine ⟨.reuse ha hk (fun hp => fill _ hp hk)
        (congrArg (fun t : Tables H => t.next) eqt) run,
        G, go, fg, ?_, ?_, ?_⟩
      · intro k hko
        have hkn : k < r.state.tables.next := by simpa only [eqt] using hko
        exact (hop k hkn).trans (storedParent_congr eqt gn g k)
      · intro k hko
        have hkn : k < r.state.tables.next := by simpa only [eqt] using hko
        exact (hob k hkn).trans (ok.old_back k hko)
      · intro e he hf
        rcases List.mem_cons.mp he with he | he
        · subst e
          simp [Event.ofResult, ha] at hf
        · exact hnew e he hf
    | true =>
      obtain ⟨hk, q, hq, hb⟩ := fresh_install g hi ha
      have hp : r.measured.step.parent < F.size := by
        simpa only [g.size_eq] using request_parent_lt hi
      have hn : r.state.tables.next = s.tables.next + 1 := by
        change r.installed.tables.next = s.tables.next + 1
        simpa [Installed.delta, ha] using ok.next_eq
      have gn : Grounded c (F.appendLeaf r.measured.step.parent)
          r.state.tables := by
        change Grounded c (F.appendLeaf r.measured.step.parent) r.installed.tables
        simpa [ha] using ok.grounded
      have fn : Filled r.state.tables := by
        intro k hk0 hkn
        by_cases hko : k < s.tables.next
        · obtain ⟨q', hq'⟩ := fill k hk0 hko
          exact ⟨q', (ok.old_back k hko).trans hq'⟩
        · have he : k = r.installed.node := by omega
          subst k
          exact ⟨q, hb⟩
      obtain ⟨run, ⟨G, go, fg, hop, hob, hnew⟩⟩ :=
        ih (F := F.appendLeaf r.measured.step.parent) gn fn ts
      refine ⟨.alloc ha hk (request_parent_lt hi) hn run,
        G, go, fg, ?_, ?_, ?_⟩
      · intro k hko
        exact (hop k (by omega)).trans (parents.old g gn hp k hko)
      · intro k hko
        exact (hob k (by omega)).trans (ok.old_back k hko)
      · intro e he hf
        rcases List.mem_cons.mp he with he | he
        · subst e
          have hkn : r.installed.node < r.state.tables.next := ok.node_lt
          have hpn : storedParent gn r.installed.node =
              r.measured.step.parent := by
            rw [hk]
            exact parents.new g gn hp
          refine ⟨(hop _ hkn).trans hpn, q, ?_, (hob _ hkn).trans hb⟩
          simp [Event.ofResult, ha, hq]
        · exact hnew e he hf

theorem fromRootChronology {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} (prepared : PreparedInstalls c rank)
    (parents : AppendParents c) {mem : Array Nat} {n : Nat}
    {rows : List (Row H)} {out : State H} {log : Log H} {F : JumpForest}
    (g : Grounded c F (initial c mem n).tables)
    (specs : ∀ row ∈ rows, TestSpec row.head row.tests)
    (h : fromRoot c rank mem n rows = some (out, log)) :
    Chronology c g out log := by
  refine traceChronology prepared parents (fromRoot_trace h) g ?_ specs
  intro k hk0 hk
  change k < 1 at hk
  omega

theorem rootFirst {H : LabelledQuotient} {c : Config H}
    {mem : Array Nat} {n : Nat} {out : State H} {log : Log H}
    (h : SlotRun (initial c mem n).tables log out.tables)
    {k : Nat} (hk : 0 < k) (ho : k < out.tables.next) :
    FirstCreation log k :=
  h.first k (show 1 ≤ k by omega) ho

/-- A single bounded write for a fresh real/real edge. The parent here
is the installed parent because the guard excludes reuse events. -/
def scatterOne {H : LabelledQuotient} (limit : Nat)
    (a : Array (Option Nat)) (e : Event H) : Array (Option Nat) :=
  if e.fresh = true ∧ e.parent ≠ 0 ∧ 0 < e.node ∧ e.node < limit then
    if hi : e.head.val < a.size then
      a.set e.head.val (some e.node) hi
    else
      a
  else
    a

@[simp] theorem scatterOne_size {H : LabelledQuotient} (limit : Nat)
    (a : Array (Option Nat)) (e : Event H) :
    (scatterOne limit a e).size = a.size := by
  unfold scatterOne
  split
  · split <;> simp
  · rfl

/-- Pass `out.tables.next` as `limit`. One pass over the chronological
log, one output array, and no search by vertex or by key. -/
def scatter {H : LabelledQuotient} (limit : Nat) (log : Log H) :
    Array (Option Nat) :=
  log.foldl (scatterOne limit) (Array.replicate H.vertexCount none)

private theorem scatterFold_size {H : LabelledQuotient} (limit : Nat)
    (log : Log H) (a : Array (Option Nat)) :
    (log.foldl (scatterOne limit) a).size = a.size := by
  induction log generalizing a with
  | nil => rfl
  | cons e es ih =>
    change (es.foldl (scatterOne limit) (scatterOne limit a e)).size = a.size
    rw [ih, scatterOne_size]

theorem scatter_size {H : LabelledQuotient} (limit : Nat) (log : Log H) :
    (scatter limit log).size = H.vertexCount := by
  simp [scatter, scatterFold_size]

end ChronologicalIndex
end PreparedSweep
end EX24
