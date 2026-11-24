module

public import PaperB.ForestActualStep
public import PaperB.ForestExactDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open PaperB PaperB.ForestHead

namespace EX24
namespace PreparedSweep

open EX24.PreStep PaperB.LabelledQuotient

/-- Exact tests refer to the same prepared rows used to build the dictionary.
    The length bound is the static bound used in the capacity proof. -/
structure FullRows {H : LabelledQuotient} (p : ForestDictionary.Rows H)
    (rank : Vertex H → Nat) (rows : List (Row H)) : Prop where
  ordered : rows.Pairwise (fun a b => rank a.head < rank b.head)
  covers : ∀ v : Vertex H, ∃ row ∈ rows, row.head = v
  tests_eq : ∀ row ∈ rows, row.tests = p.row row.head
  length_le : rows.length ≤ H.vertexCount

/-- Only the request-parent bound is left as a per-head premise. -/
def ParentAt {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) (row : Row H) : Prop :=
  ∀ (s : State H) (F : JumpForest) (up : Fin F.size → Fin F.size),
    Grounded c F s.tables →
    (∀ a : Fin F.size, (up a).val = F.parentOf a.val) →
    Embedding c s F rank up (fun v => rank v < rank row.head) →
    (ForestHead.runPrepared (selectors c s) rank row.head row.tests).step.parent <
      s.tables.next

/-- The output embedding covers every vertex and has the occupied physical
    forest as its domain, rather than the entire allocated array. -/
def OutputOK {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    (out : State H) : Prop :=
  out.labels.size = H.vertexCount ∧
  out.tables.next ≤ H.vertexCount + 1 ∧
  ∃ (F : JumpForest) (up : Fin F.size → Fin F.size),
    Grounded c F out.tables ∧
    (∀ a : Fin F.size, (up a).val = F.parentOf a.val) ∧
    Nonempty (Embedding c out F rank up (fun _ => True))

theorem OutputOK.labelBack {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {out : State H}
    (h : OutputOK c rank out) (v : Vertex H) :
    out.tables.back[(selectors c out).label v]? =
      some ((buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).label v)) := by
  rcases h.2.2 with ⟨F, _, _, _, ⟨E⟩⟩
  let a : Fin F.size := ⟨(selectors c out).label v, E.label_lt v True.intro⟩
  have he : E.image a = (buildProperLossForest H rank).label v := by
    first
    | exact E.label_eq v True.intro
    | exact (E.label_eq v True.intro).symm
  calc
    _ = some ((buildProperLossForest H rank).nodeKey? (E.image a)) :=
      E.back_eq a
    _ = _ := by rw [he]

/-- A trace preserves untouched labels and identifies the final label
    of each logged head with its logged node. -/
theorem Trace.labelFacts {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} (ht : Trace c rank s rows out log)
    (inj : ∀ {a b : Vertex H}, rank a = rank b → a = b) :
    (∀ row ∈ rows, TestSpec row.head row.tests) →
    rows.Pairwise (fun a b => rank a.head < rank b.head) →
    (∀ v : Vertex H, (∀ row ∈ rows, v ≠ row.head) →
      (selectors c out).label v = (selectors c s).label v) ∧
    (∀ e ∈ log, (selectors c out).label e.head = e.node) := by
  induction ht with
  | nil s =>
    intro _ _
    exact ⟨fun _ _ => rfl, by simp⟩
  | @cons s out row rows r log h _ ih =>
    intro specs ordered
    have hs : step c s rank row.head row.tests = some r :=
      (stepPrepared_eq_step c s rank row.head row.tests
        (specs row (by simp)) inj).symm.trans h
    have hord := List.pairwise_cons.mp ordered
    have tail := ih
      (fun t ht => specs t (List.mem_cons_of_mem row ht)) hord.2
    have hhere : (selectors c r.state).label row.head = r.installed.node := by
      have hw := (step_parts hs).2.2.2 (c.vertexIndex row.head)
      simp only [if_pos rfl] at hw
      change (r.labels[c.vertexIndex row.head]?).getD 0 = r.installed.node
      rw [hw] <;> rfl
    constructor
    · intro v hv
      exact (tail.1 v (fun t ht => hv t (List.mem_cons_of_mem row ht))).trans
        (previous_label hs (hv row (by simp)))
    · intro e he
      rcases List.mem_cons.mp he with he | he
      · subst e
        change (selectors c out).label row.head = r.installed.node
        refine (tail.1 row.head ?_).trans hhere
        intro t ht he
        have hlt := hord.1 t ht
        rw [← he] at hlt
        exact (Nat.lt_irrefl _) hlt
      · exact tail.2 e he

private theorem dictionaryLookup {H : LabelledQuotient} (c : Config H) :
    ∀ k ∈ c.dict.toList, ∃ i, (PairLookup.lookup c.dict k).1 = some i := by
  intro k hk
  apply (PairLookup.lookup_member_iff c.dict k c.sorted).mpr
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem hk
  exact ⟨i, by simpa using hi, by simpa using he⟩

/-- A vertex is past the frontier when its rank is below every remaining head.
    The ranks need not be consecutive. -/
private def Past {H : LabelledQuotient} (rank : Vertex H → Nat)
    (rows : List (Row H)) (v : Vertex H) : Prop :=
  ∀ row ∈ rows, rank v < rank row.head

private def Frontier {H : LabelledQuotient} (rank : Vertex H → Nat)
    (rows : List (Row H)) : Prop :=
  ∀ v : Vertex H, (∃ row ∈ rows, row.head = v) ∨ Past rank rows v

private theorem past_cons {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {rows : List (Row H)}
    (ho : (row :: rows).Pairwise (fun a b => rank a.head < rank b.head)) :
    Past rank (row :: rows) = (fun v => rank v < rank row.head) := by
  funext v
  apply propext
  constructor
  · intro hv
    exact hv row (by simp)
  · intro hv r hr
    rcases List.mem_cons.mp hr with hr | hr
    · subst r
      exact hv
    · exact Nat.lt_trans hv ((List.pairwise_cons.mp ho).1 r hr)

private theorem frontier_tail {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {rows : List (Row H)}
    (ho : (row :: rows).Pairwise (fun a b => rank a.head < rank b.head))
    (hf : Frontier rank (row :: rows)) :
    Frontier rank rows := by
  intro v
  rcases hf v with ⟨r, hr, he⟩ | hv
  · rcases List.mem_cons.mp hr with hr | hr
    · subst r
      right
      intro t ht
      rw [← he]
      exact (List.pairwise_cons.mp ho).1 t ht
    · exact Or.inl ⟨r, hr, he⟩
  · exact Or.inr (fun r hr => hv r (List.mem_cons_of_mem row hr))

private theorem past_tail {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {rows : List (Row H)}
    (ho : (row :: rows).Pairwise (fun a b => rank a.head < rank b.head))
    (hf : Frontier rank (row :: rows)) :
    Past rank rows = (fun v => rank v < rank row.head ∨ v = row.head) := by
  funext v
  apply propext
  constructor
  · intro hv
    rcases hf v with ⟨r, hr, he⟩ | hall
    · rcases List.mem_cons.mp hr with hr | hr
      · subst r
        exact Or.inr he.symm
      · have hlt : rank v < rank v := by simpa only [he] using hv r hr
        exact ((Nat.lt_irrefl _) hlt).elim
    · exact Or.inl (hall row (by simp))
  · intro hv r hr
    have hlt := (List.pairwise_cons.mp ho).1 r hr
    rcases hv with hv | hv
    · exact Nat.lt_trans hv hlt
    · simpa only [hv] using hlt

/-- Combine the prepared embedding invariant with the actual install's
    grounding, growth, and label-capacity guarantees. -/
private theorem occupiedStep
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size} {row : Row H} {r : HeadResult H}
    (hc : c.usePackedWords = c)
    (E : Embedding c s F rank up (fun v => rank v < rank row.head))
    (g : Grounded c F s.tables)
    (oldParent : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (T : TestSpec row.head row.tests)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat)
    (h : stepPrepared c s rank row.head row.tests = some r) :
    let F' := if r.installed.allocated then
      F.appendLeaf r.measured.step.parent
    else F
    Grounded c F' r.state.tables ∧
      r.state.tables.next = s.tables.next + r.installed.delta ∧
      r.installed.delta ≤ 1 ∧
      r.state.labels.size = s.labels.size ∧
      ∃ up' : Fin F'.size → Fin F'.size,
        (∀ b : Fin F'.size, (up' b).val = F'.parentOf b.val) ∧
        Nonempty (Embedding c r.state F' rank up'
          (fun v => rank v < rank row.head ∨ v = row.head)) := by
  have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
    fun {a b} he => distinctRanks a b he
  have hs : step c s rank row.head row.tests = some r :=
    (stepPrepared_eq_step c s rank row.head row.tests T inj).symm.trans h
  have ok := step_spec g hs
  obtain ⟨up', newParent, E', _⟩ :=
    prepared_step_invariant (row := row) hc E g oldParent T
      rankArc distinctRanks flat h
  exact ⟨ok.1.grounded, ok.2.1, ok.2.2.1, (step_parts hs).2.2.1,
    up', newParent, ⟨E'⟩⟩

private theorem foldRowsAux_total {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (c : Config H) (rank : Vertex H → Nat)
    (hc : c.usePackedWords = c)
    (hd : c.dict = ForestDictionary.dictionary p c.code)
    (hmax : c.region.maxNodes = H.vertexCount)
    (hindex : ∀ v : Vertex H, c.vertexIndex v = Fin.val v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat)
    (rows : List (Row H)) :
    ∀ (s : State H) (F : JumpForest) (up : Fin F.size → Fin F.size)
      (rev : Log H),
      rows.Pairwise (fun a b => rank a.head < rank b.head) →
      Frontier rank rows →
      (∀ row ∈ rows, row.tests = p.row row.head) →
      (∀ row ∈ rows, ParentAt c rank row) →
      s.labels.size = H.vertexCount →
      s.tables.next + rows.length ≤ H.vertexCount + 1 →
      Grounded c F s.tables →
      (∀ a : Fin F.size, (up a).val = F.parentOf a.val) →
      Embedding c s F rank up (Past rank rows) →
      ∃ out log, foldRowsAux c rank rows s rev = some (out, log) ∧
        OutputOK c rank out := by
  induction rows with
  | nil =>
    intro s F up rev _ _ _ _ hlabels hbudget g hparent E
    have hnil : Past rank ([] : List (Row H)) = (fun _ => True) := by
      funext v
      apply propext
      simp [Past]
    rw [hnil] at E
    have hnext : s.tables.next ≤ H.vertexCount + 1 := by
      simpa only [List.length_nil, Nat.add_zero] using hbudget
    exact ⟨s, rev.reverse, rfl, hlabels, hnext, F, up, g, hparent, ⟨E⟩⟩
  | cons row rows ih =>
    intro s F up rev ho hf hexact hparents hlabels hbudget g hparent E
    have htest : row.tests = p.row row.head := hexact row (by simp)
    have T : TestSpec row.head row.tests := by
      rw [htest]
      exact p.spec row.head
    have Ehead : Embedding c s F rank up (fun v => rank v < rank row.head) := by
      rw [past_cons ho] at E
      exact E
    have hy : c.vertexIndex row.head < s.labels.size := by
      rw [hindex, hlabels]
      exact row.head.isLt
    have hp := hparents row (by simp) s F up g hparent Ehead
    have hp' :
        (ForestHead.runPrepared (selectors c s) rank row.head
          (p.row row.head)).step.parent < s.tables.next := by
      simpa only [htest] using hp

    have hlen : (row :: rows).length = rows.length + 1 := rfl
    have hroom : s.tables.next < s.tables.back.size := by
      rw [g.back_size, hmax]
      omega
    have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
      fun {a b} he => distinctRanks a b he
    obtain ⟨r, hr⟩ :=
      ForestDictionary.stepPrepared_dictionary_exists
        (c := c) (s := s) (F := F) (rank := rank) (y := row.head)
        p hd inj g hy hp' (dictionaryLookup c)
        (fun _ _ _ _ _ => hroom)
    have hstep : stepPrepared c s rank row.head row.tests = some r := by
      simpa only [htest] using hr

    let F' := if r.installed.allocated then
      F.appendLeaf r.measured.step.parent
    else F
    obtain ⟨g', hnext, hdelta, hsize, up', hparent', ⟨E'⟩⟩ :=
      occupiedStep (row := row) hc Ehead g hparent T rankArc distinctRanks flat hstep
    have Etail : Embedding c r.state F' rank up' (Past rank rows) := by
      rw [past_tail ho hf]
      exact E'
    have hbudget' : r.state.tables.next + rows.length ≤ H.vertexCount + 1 := by
      omega
    obtain ⟨out, log, hfold, hout⟩ :=
      ih r.state F' up' (Event.ofResult row.head r :: rev)
        (List.pairwise_cons.mp ho).2 (frontier_tail ho hf)
        (fun t ht => hexact t (List.mem_cons_of_mem row ht))
        (fun t ht => hparents t (List.mem_cons_of_mem row ht))
        (hsize.trans hlabels) hbudget' g' hparent' Etail
    exact ⟨out, log, by simpa only [foldRowsAux, hstep] using hfold, hout⟩

/-- Totality and output semantics of the original compact prepared fold.
    The trace is recovered from the successful fold equation; the executable
    fold does not retain intermediate states. -/
theorem fromRoot_total {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (c : Config H) (rank : Vertex H → Nat)
    {mem : Array Nat} {rows : List (Row H)}
    (layout : JumpWordLayout c.region JumpForest.init mem)
    (hc : c.usePackedWords = c)
    (hd : c.dict = ForestDictionary.dictionary p c.code)
    (hmax : c.region.maxNodes = H.vertexCount)
    (hindex : ∀ v : Vertex H, c.vertexIndex v = Fin.val v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat)
    (full : FullRows p rank rows)
    (parents : ∀ row ∈ rows, ParentAt c rank row) :
    ∃ (out : State H) (log : Log H),
      fromRoot c rank mem H.vertexCount rows = some (out, log) ∧
      Trace c rank (initial c mem H.vertexCount) rows out log ∧
      log.map Event.head = rows.map Row.head ∧
      log.length = rows.length ∧
      (∀ e ∈ log, (selectors c out).label e.head = e.node) ∧
      OutputOK c rank out := by
  let s := initial c mem H.vertexCount
  have g : Grounded c JumpForest.init s.tables :=
    initial_grounded c layout rfl H.vertexCount
  let up : Fin JumpForest.init.size → Fin JumpForest.init.size :=
    boundedJumpParent g.layout.valid
  have hup : initialUp = up := by
    funext a
    apply Fin.ext
    have ha : (initialUp a).val < 1 := (initialUp a).isLt
    have hb : (up a).val < 1 := (up a).isLt
    omega
  have hpast : Past rank rows = (fun _ => False) := by
    funext v
    apply propext
    constructor
    · intro hv
      obtain ⟨row, hr, he⟩ := full.covers v
      have hlt : rank v < rank v := by simpa only [he] using hv row hr
      exact (Nat.lt_irrefl _) hlt
    · intro h
      exact h.elim
  have E : Embedding c s JumpForest.init rank up (Past rank rows) := by
    rw [← hup, hpast]
    exact initial_embedding c rank layout H.vertexCount
  have hlabels : s.labels.size = H.vertexCount := by
    simp [s, initial]
  have hbudget : s.tables.next + rows.length ≤ H.vertexCount + 1 := by
    change 1 + rows.length ≤ H.vertexCount + 1
    have hlen := full.length_le
    omega
  obtain ⟨out, log, hfold, hout⟩ :=
    foldRowsAux_total p c rank hc hd hmax hindex rankArc distinctRanks flat
      rows s JumpForest.init up [] full.ordered (fun v => Or.inl (full.covers v))
      full.tests_eq parents hlabels hbudget g (fun _ => rfl) E
  have hrun : fromRoot c rank mem H.vertexCount rows = some (out, log) := hfold
  have ht := fromRoot_trace hrun
  have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
    fun {a b} he => distinctRanks a b he
  have specs : ∀ row ∈ rows, TestSpec row.head row.tests := by
    intro row hr
    rw [full.tests_eq row hr]
    exact p.spec row.head
  exact ⟨out, log, hrun, ht, ht.heads, ht.length,
    (ht.labelFacts inj specs full.ordered).2, hout⟩

end PreparedSweep
end EX24

namespace EX24.PreparedSweep

open PaperB PaperB.ForestHead EX24.PreStep PaperB.LabelledQuotient

/-- A Prop-only callback on the occupied prefix immediately before `row`. -/
def PrefixLocalAt {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) (Local : State H → Row H → Prop) (row : Row H) : Prop :=
  ∀ (s : State H) (F : JumpForest) (up : Fin F.size → Fin F.size),
    Grounded c F s.tables →
    (∀ a : Fin F.size, (up a).val = F.parentOf a.val) →
    Embedding c s F rank up (fun v => rank v < rank row.head) →
    TestSpec row.head row.tests →
    Local s row

/-- An actual prepared trace with `Local` certified at each step's input state. -/
inductive LocalTrace {H : LabelledQuotient} (c : Config H)
    (rank : Vertex H → Nat) (Local : State H → Row H → Prop) :
    State H → List (Row H) → State H → Log H → Prop where
  | nil (s : State H) : LocalTrace c rank Local s [] s []
  | cons {s out : State H} {row : Row H} {rows : List (Row H)}
      {r : HeadResult H} {log : Log H} :
      stepPrepared c s rank row.head row.tests = some r →
      Local s row →
      LocalTrace c rank Local r.state rows out log →
      LocalTrace c rank Local s (row :: rows) out (Event.ofResult row.head r :: log)

private theorem trace_addLocal {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) {c : Config H} {rank : Vertex H → Nat}
    {Local : State H → Row H → Prop}
    (hc : c.usePackedWords = c)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat)
    {s out : State H} {rows : List (Row H)} {log : Log H}
    (tr : Trace c rank s rows out log) :
    ∀ (F : JumpForest) (up : Fin F.size → Fin F.size),
      rows.Pairwise (fun a b => rank a.head < rank b.head) →
      Frontier rank rows →
      (∀ row ∈ rows, row.tests = p.row row.head) →
      (∀ row ∈ rows, PrefixLocalAt c rank Local row) →
      Grounded c F s.tables →
      (∀ a : Fin F.size, (up a).val = F.parentOf a.val) →
      Embedding c s F rank up (Past rank rows) →
      LocalTrace c rank Local s rows out log := by
  induction tr with
  | nil s =>
    intro _ _ _ _ _ _ _ _ _
    exact LocalTrace.nil s
  | @cons s out row rows r log hstep tail ih =>
    intro F up ho hf hexact hLocal g hparent E
    have T : TestSpec row.head row.tests := by
      rw [hexact row (by simp)]
      exact p.spec row.head
    have Ehead : Embedding c s F rank up (fun v => rank v < rank row.head) := by
      simpa only [past_cons ho] using E
    have hhere := hLocal row (by simp) s F up g hparent Ehead T
    let F' := if r.installed.allocated then
      F.appendLeaf r.measured.step.parent
    else F
    obtain ⟨g', _, _, _, up', hparent', ⟨E'⟩⟩ :=
      occupiedStep (row := row) hc Ehead g hparent T rankArc distinctRanks flat hstep
    have Etail : Embedding c r.state F' rank up' (Past rank rows) := by
      rw [past_tail ho hf]
      exact E'
    exact LocalTrace.cons hstep hhere
      (ih F' up' (List.pairwise_cons.mp ho).2 (frontier_tail ho hf)
        (fun t ht => hexact t (List.mem_cons_of_mem row ht))
        (fun t ht => hLocal t (List.mem_cons_of_mem row ht))
        g' hparent' Etail)

/-- The complete prepared run retains its original guarantees and certifies `Local`
    at the input state of every row in its trace. -/
theorem fromRoot_total_local {H : LabelledQuotient}
    (p : ForestDictionary.Rows H) (c : Config H) (rank : Vertex H → Nat)
    (Local : State H → Row H → Prop)
    {mem : Array Nat} {rows : List (Row H)}
    (layout : JumpWordLayout c.region JumpForest.init mem)
    (hc : c.usePackedWords = c)
    (hd : c.dict = ForestDictionary.dictionary p c.code)
    (hmax : c.region.maxNodes = H.vertexCount)
    (hindex : ∀ v : Vertex H, c.vertexIndex v = Fin.val v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat)
    (full : FullRows p rank rows)
    (parents : ∀ row ∈ rows, ParentAt c rank row)
    (hLocal : ∀ row ∈ rows, PrefixLocalAt c rank Local row) :
    ∃ (out : State H) (log : Log H),
      fromRoot c rank mem H.vertexCount rows = some (out, log) ∧
      Trace c rank (initial c mem H.vertexCount) rows out log ∧
      log.map Event.head = rows.map Row.head ∧
      log.length = rows.length ∧
      (∀ e ∈ log, (selectors c out).label e.head = e.node) ∧
      OutputOK c rank out ∧
      LocalTrace c rank Local (initial c mem H.vertexCount) rows out log := by
  obtain ⟨out, log, hrun, tr, hheads, hlen, hfinal, hout⟩ :=
    fromRoot_total p c rank layout hc hd hmax hindex rankArc distinctRanks flat full parents
  let s := initial c mem H.vertexCount
  have g : Grounded c JumpForest.init s.tables :=
    initial_grounded c layout rfl H.vertexCount
  let up : Fin JumpForest.init.size → Fin JumpForest.init.size :=
    boundedJumpParent g.layout.valid
  have hparent : ∀ a : Fin JumpForest.init.size, (up a).val = JumpForest.init.parentOf a.val :=
    fun _ => rfl
  have hup : initialUp = up := by
    funext a
    apply Fin.ext
    have ha : (initialUp a).val < 1 := (initialUp a).isLt
    have hb : (up a).val < 1 := (up a).isLt
    omega
  have hpast : Past rank rows = (fun _ => False) := by
    funext v
    apply propext
    refine ⟨?_, fun h => h.elim⟩
    intro hv
    obtain ⟨row, hr, he⟩ := full.covers v
    exact (Nat.lt_irrefl (rank v)) (by simpa only [he] using hv row hr)
  have E : Embedding c s JumpForest.init rank up (Past rank rows) := by
    rw [← hup, hpast]
    exact initial_embedding c rank layout H.vertexCount
  exact ⟨out, log, hrun, tr, hheads, hlen, hfinal, hout,
    trace_addLocal p hc rankArc distinctRanks flat tr
      JumpForest.init up full.ordered (fun v => Or.inl (full.covers v))
      full.tests_eq hLocal g hparent E⟩

end EX24.PreparedSweep
