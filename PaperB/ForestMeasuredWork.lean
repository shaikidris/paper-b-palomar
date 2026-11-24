module

public import PaperB.ForestCompactFold
public import PaperB.ForestExactDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep
open PaperB PaperB.ForestHead PaperB.LabelledQuotient PaperB.PairLookup

/-
Insert this module body in EX24.PreparedSweep, immediately before its
closing `end PreparedSweep`, in the scope of `prepared_parts`. The
excerpts do not specify the file's import path.

WorkTrace annotates CountedTrace; it does not run a second sweep.
`aggregate` proves the measured-count bounds. `foldWordBound` is the
word-model corollary, with separate premises for the local charges and
for their coverage of the executable fold. In particular, the logical
write bound is not a bound on all installation word operations.
-/
namespace AggregateEX24

open ForestHead

def entryTotal {H : LabelledQuotient} : List (Row H) → Nat
  | [] => 0
  | row :: rows => row.tests.length + entryTotal rows

private def flag {α : Type _} : Option α → Nat
  | none => 0
  | some _ => 1

private theorem flag_le {α : Type _} (x : Option α) : flag x ≤ 1 := by
  cases x <;> simp [flag]

structure Work where
  activeHeads : Nat
  activeEntries : Nat
  comparisons : Nat
  tests : Nat
  atDepth : Nat
  ancestry : Nat
  requests : Nat
  planner : Nat

def Work.zero : Work := ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def Work.add (a b : Work) : Work :=
  ⟨a.activeHeads + b.activeHeads, a.activeEntries + b.activeEntries,
   a.comparisons + b.comparisons, a.tests + b.tests,
   a.atDepth + b.atDepth, a.ancestry + b.ancestry,
   a.requests + b.requests, a.planner + b.planner⟩

def headWork {H : LabelledQuotient} (rank : Vertex H → Nat)
    (row : Row H) (r : HeadResult H) : Work :=
  let a := flag (planPrepared rank row.head row.tests)
  ⟨a, a * row.tests.length, r.measured.search.comparisons,
   r.measured.search.tests, r.measured.depthCalls,
   r.measured.search.ancestryCalls, flag r.measured.step.newPair,
   (planPreparedMetered rank row.head row.tests).2⟩

/-- Exact sums on the successful prepared steps, with the original
    row, state, event and Count indices. -/
inductive WorkTrace {H : LabelledQuotient}
    (c : Config H) (rank : Vertex H → Nat) :
    State H → List (Row H) → State H → Log H → Count → Work → Prop where
  | nil (s : State H) : WorkTrace c rank s [] s [] Count.zero Work.zero
  | cons {s out : State H} {row : Row H} {rows : List (Row H)}
      {r : HeadResult H} {log : Log H} {n : Count} {w : Work} :
      stepPrepared c s rank row.head row.tests = some r →
      WorkTrace c rank r.state rows out log n w →
      WorkTrace c rank s (row :: rows) out
        (Event.ofResult row.head r :: log) (Count.prepend r n)
        ((headWork rank row r).add w)

/-- Preconditions on the states actually visited, not on every state
    from which `stepPrepared` happens to return `some`. -/
def Sites {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    (P : State H → Row H → Prop) : State H → List (Row H) → Prop
  | _, [] => True
  | s, row :: rows =>
      ∀ r, stepPrepared c s rank row.head row.tests = some r →
        P s row ∧ Sites c rank P r.state rows

def SiteOK {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    (s : State H) (row : Row H) : Prop :=
  TestSpec row.head row.tests ∧
  (∃ F, Grounded c F s.tables) ∧
  (∀ m key, planPrepared rank row.head row.tests = some (m, key) →
    (selectors c s).depth ((selectors c s).label m) + 1 ≤ s.tables.next)

structure Bounds {H : LabelledQuotient} (L : Nat)
    (rows : List (Row H)) (n : Count) (w : Work) : Prop where
  heads : n.heads = rows.length
  activeHeads : w.activeHeads ≤ n.heads
  activeEntries : w.activeEntries ≤ entryTotal rows
  comparisons : w.comparisons ≤ L * w.activeHeads
  tests : w.tests ≤ L * w.activeEntries
  atDepth : w.atDepth ≤ w.comparisons + w.activeHeads
  ancestry : w.ancestry ≤ w.tests
  requests : w.requests ≤ n.heads
  allocations : n.allocations ≤ n.heads
  writes : n.writes ≤ n.heads + 17 * n.allocations
  planner : w.planner ≤ 2 * entryTotal rows + 16 * n.heads

theorem Bounds.atDepth_le {H : LabelledQuotient} {L : Nat}
    {rows : List (Row H)} {n : Count} {w : Work}
    (b : Bounds L rows n w) :
    w.atDepth ≤ (L + 1) * w.activeHeads := by
  rw [Nat.add_mul, Nat.one_mul]
  exact Nat.le_trans b.atDepth (Nat.add_le_add_right b.comparisons _)

private theorem kernelLocal {H : LabelledQuotient}
    (S : Selectors H) (rank : Vertex H → Nat) (row : Row H)
    (r : HeadResult H) (L : Nat)
    (hm : r.measured = runPrepared S rank row.head row.tests)
    (hlog : ∀ m key, planPrepared rank row.head row.tests = some (m, key) →
      Nat.log2 (S.depth (S.label m) + 1) + 1 ≤ L) :
    let a := headWork rank row r
    a.comparisons ≤ L * a.activeHeads ∧
      a.tests ≤ L * a.activeEntries ∧
      a.atDepth ≤ a.comparisons + a.activeHeads ∧
      a.ancestry ≤ a.tests := by
  cases hp : planPrepared rank row.head row.tests with
  | none =>
      have h : r.measured = stopped := by
        simpa only [runPrepared, hp] using hm
      obtain ⟨hc, ht, hd, ha⟩ := stopped_work (H := H)
      simp [headWork, flag, hp, h, hc, ht, hd, ha]
  | some p =>
      obtain ⟨m, key⟩ := p
      have h : r.measured = active S row.tests m key := by
        simpa only [runPrepared, hp] using hm
      obtain ⟨hc, ht, hd, ha⟩ := active_work S row.tests m key
      have hcL := Nat.le_trans hc (hlog m key hp)
      simp only [headWork, flag, hp, h, Nat.one_mul, Nat.mul_one]
      exact ⟨hcL, Nat.le_trans ht (Nat.mul_le_mul_right _ hcL), hd, ha⟩

/--
The `next + remaining rows` invariant proves the occupied-counter bound
at every call site, not just at the output. For the complete sweep its
initial premise follows from `next = 1` and `rows.length ≤ nH`.
`logBound` is the uniform logarithmic bound; no machine-word size or
arena-storage statement is used.
-/
theorem aggregate {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s out : State H} {rows : List (Row H)}
    {log : Log H} {n : Count} {nH L : Nat}
    (inj : ∀ a b : Vertex H, rank a = rank b → a = b)
    (logBound : ∀ k ≤ nH + 1, Nat.log2 k + 1 ≤ L)
    (ht : CountedTrace c rank s rows out log n) :
    Sites c rank (SiteOK c rank) s rows →
    s.tables.next + rows.length ≤ nH + 1 →
    ∃ w, WorkTrace c rank s rows out log n w ∧
      Bounds L rows n w ∧ out.tables.next = s.tables.next + n.allocations := by
  induction ht with
  | nil s =>
      intro _ _
      refine ⟨Work.zero, WorkTrace.nil s, ?_, ?_⟩
      · constructor <;> simp [Count.zero, Work.zero, entryTotal]
      · simp [Count.zero]
  | @cons s out row rows r log n hs _ ih =>
      intro sites room
      obtain ⟨site, tailSites⟩ := sites r hs
      obtain ⟨T, ⟨F, g⟩, depthFits⟩ := site
      have inj' : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
        fun {a b} e => inj a b e
      have hOld : step c s rank row.head row.tests = some r :=
        (stepPrepared_eq_step c s rank row.head row.tests T inj').symm.trans hs
      obtain ⟨_, hnext, hdelta, hwrites, hnoalloc⟩ := step_spec g hOld
      have hroom : r.state.tables.next + rows.length ≤ nH + 1 := by
        rw [hnext]
        simp only [List.length_cons] at room
        omega
      obtain ⟨tail, htrace, b, hout⟩ := ih tailSites hroom
      obtain ⟨bh, ba, be, bc, bt, bd, ban, br, ball, bw, bp⟩ := b

      have hm : r.measured = runPrepared (selectors c s) rank row.head row.tests :=
        (prepared_parts T inj hs).1.trans
          (runPrepared_eq_runHead (selectors c s) rank row.head row.tests T inj').symm
      let a := headWork rank row r
      have hk : a.comparisons ≤ L * a.activeHeads ∧
          a.tests ≤ L * a.activeEntries ∧
          a.atDepth ≤ a.comparisons + a.activeHeads ∧
          a.ancestry ≤ a.tests :=
        kernelLocal (selectors c s) rank row r L hm (by
          intro m key hp
          apply logBound
          have h := depthFits m key hp
          omega)
      obtain ⟨lc, lt, ld, lan⟩ := hk
      have la : a.activeHeads ≤ 1 := flag_le _
      have le : a.activeEntries ≤ row.tests.length := by
        change a.activeHeads * row.tests.length ≤ row.tests.length
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right row.tests.length la
      have lr : a.requests ≤ 1 := flag_le _
      have lp : a.planner ≤ row.tests.length + row.tests.length + 16 :=
        (planPrepared_work rank row.head row.tests).2
      have lw : r.installed.writes ≤ 1 + 17 * r.installed.delta := by
        cases ha : r.installed.allocated with
        | false =>
            have he := hnoalloc ha
            simp [Installed.delta, ha, he]
        | true =>
            simpa [Installed.delta, ha] using hwrites

      refine ⟨a.add tail, WorkTrace.cons hs htrace, ?_, ?_⟩
      · constructor
        · simp only [Count.prepend, List.length_cons]
          omega
        · simp only [Work.add, Count.prepend]
          omega
        · simp only [Work.add, entryTotal]
          omega
        · simp only [Work.add, Nat.mul_add]
          exact Nat.add_le_add lc bc
        · simp only [Work.add, Nat.mul_add]
          exact Nat.add_le_add lt bt
        · simp only [Work.add]
          omega
        · exact Nat.add_le_add lan ban
        · simp only [Work.add, Count.prepend]
          omega
        · exact Nat.add_le_add hdelta ball
        · simp only [Count.prepend, Nat.mul_add]
          omega
        · simp only [Work.add, Count.prepend, entryTotal, Nat.mul_add]
          omega
      · simp only [hout, hnext, Count.prepend, Nat.add_assoc]

/- Packed calls.

   Instantiate `budgetBound` below after rewriting the concrete layout
   budget with JumpWordLayout.budget_eq. `wordSpec` is the cost
   conclusion of ancestorAtDepthWords_spec or decideAncestorWords_spec,
   with its layout, valid-node and size hypotheses discharged at that
   call. `occupied_le` is for occupied nodes, not array capacity; when
   the layout's occupied count is the grounded `next` counter, the
   invariant in `aggregate` supplies this bound. The formulation does
   not require an equation between the two adapters' measured costs.
-/
theorem packedCallBound {levels : Nat → Nat}
    {occupied nH L budget cost : Nat}
    (occupied_le : occupied ≤ nH + 1)
    (levelBound : ∀ k ≤ nH + 1, levels k ≤ L)
    (budgetBound : budget ≤ 6 * levels occupied + 1)
    (wordSpec : cost ≤ 1 + 3 * budget) :
    cost ≤ 1 + 3 * (6 * L + 1) := by
  have h := levelBound occupied occupied_le
  omega

def PackedCharges (levels : Nat → Nat) (nH : Nat) (costs : List Nat) : Prop :=
  ∀ cost ∈ costs, ∃ occupied budget,
    occupied ≤ nH + 1 ∧ budget ≤ 6 * levels occupied + 1 ∧
      cost ≤ 1 + 3 * budget

private theorem sumBound (costs : List Nat) (b : Nat)
    (h : ∀ x ∈ costs, x ≤ b) : costs.sum ≤ costs.length * b := by
  induction costs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have hs := ih (fun y hy => h y (by simp [hy]))
      simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem packedSumBound {levels : Nat → Nat} {nH L calls : Nat}
    {costs : List Nat} (Lpos : 1 ≤ L)
    (levelBound : ∀ k ≤ nH + 1, levels k ≤ L)
    (charges : PackedCharges levels nH costs)
    (callCount : costs.length ≤ calls) :
    costs.sum ≤ calls * (22 * L) := by
  apply Nat.le_trans (sumBound costs (22 * L) ?_)
    (Nat.mul_le_mul_right (22 * L) callCount)
  intro x hx
  obtain ⟨occupied, budget, ho, hb, hw⟩ := charges x hx
  have h := packedCallBound ho levelBound hb hw
  omega

/-- For the prepared dictionary use `keys := collect rows code` and
    `collect_length_le`. This counts build comparisons, not lookups
    or the other work of constructing the dictionary. -/
theorem dictionaryComparisonBound {keys} {nH L : Nat}
    (collectLength : List.length keys ≤ nH)
    (dictionaryLog : PaperB.PairLookup.KeyMerge.ceilBinaryLog (List.length keys) ≤ L) :
    (PaperB.PairLookup.KeyMerge.build keys).comparisons ≤ 2 * nH * L :=
  Nat.le_trans (PaperB.PairLookup.KeyMerge.build_comparisons_log keys)
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 collectLength) dictionaryLog)

structure WordMeter where
  planner : Nat
  headFixed : Nat
  comparisons : Nat
  tests : Nat
  depths : List Nat
  ancestries : List Nat
  install : Nat
  lookups : List Nat

def WordMeter.total (u : WordMeter) : Nat :=
  u.planner + u.headFixed + u.comparisons + u.tests +
    u.depths.sum + u.ancestries.sum + u.install + u.lookups.sum

/--
`rowCount` and `entryCount` are the complete prepared schedule's
one-row-per-vertex and test-entry bounds. Apply `aggregate` to the
CountedTrace of the computed fold (obtained using `Trace.exists_count`).

The cost lists here are for the executed calls. Their length premises
connect those calls to the two measured counters and the newPair
requests, respectively. `installWords` is a local word-model budget for
non-lookup installation, including its jump-table work and the label
update; it is not inferred from `Installed.writes`. `coversFold` requires
that the charges also pay for residual work, such as label and pair
reads, loop bookkeeping and row/array access, in the indicated pools.
The dictionary-build comparison count is separate.
-/
theorem foldWordBound {H : LabelledQuotient} {rows : List (Row H)}
    {n : Count} {w : Work} {levels : Nat → Nat}
    {nH mH L foldWords : Nat} (u : WordMeter) (p f c t i z b : Nat)
    (B : Bounds L rows n w) (Lpos : 1 ≤ L)
    (rowCount : rows.length ≤ nH) (entryCount : entryTotal rows ≤ mH)
    (levelBound : ∀ k ≤ nH + 1, levels k ≤ L)
    (plannerWords : u.planner ≤ p * w.planner)
    (headWords : u.headFixed ≤ f * n.heads)
    (comparisonWords : u.comparisons ≤ c * w.comparisons)
    (testWords : u.tests ≤ t * w.tests)
    (depthCharges : PackedCharges levels nH u.depths)
    (ancestryCharges : PackedCharges levels nH u.ancestries)
    (depthCount : u.depths.length ≤ w.atDepth)
    (ancestryCount : u.ancestries.length ≤ w.ancestry)
    (installWords : u.install ≤ i * (n.heads * L) + z * (n.writes * L))
    (lookupCount : u.lookups.length ≤ w.requests)
    (lookupWords : ∀ x ∈ u.lookups, x ≤ b * L)
    (coversFold : foldWords ≤ u.total) :
    foldWords ≤ (16 * p + f + c + t + 44 + i + 18 * z + b) *
      ((nH + mH) * (L * L)) := by
  let S := nH + mH
  let K := S * (L * L)
  change foldWords ≤ (16 * p + f + c + t + 44 + i + 18 * z + b) * K
  have hn : n.heads ≤ nH := B.heads ▸ rowCount
  have hnS : n.heads ≤ S := by dsimp [S]; omega
  have hmS : mH ≤ S := by dsimp [S]; omega
  have hSL : S ≤ S * L := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left S Lpos
  have hLK : S * L ≤ K := by
    have h : L ≤ L * L := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left L Lpos
    exact Nat.mul_le_mul_left S h
  have hSK := Nat.le_trans hSL hLK

  have hp : w.planner ≤ 16 * S := by
    have h := B.planner
    dsimp [S]
    rw [Nat.mul_add]
    omega
  have hP : u.planner ≤ (16 * p) * K := calc
    _ ≤ p * w.planner := plannerWords
    _ ≤ p * (16 * K) :=
      Nat.mul_le_mul_left p (Nat.le_trans hp (Nat.mul_le_mul_left 16 hSK))
    _ = _ := by ac_rfl
  have hF : u.headFixed ≤ f * K :=
    Nat.le_trans headWords (Nat.mul_le_mul_left f (Nat.le_trans hnS hSK))

  have hc : w.comparisons ≤ L * nH :=
    Nat.le_trans B.comparisons
      (Nat.mul_le_mul_left L (Nat.le_trans B.activeHeads hn))
  have ht : w.tests ≤ L * mH :=
    Nat.le_trans B.tests
      (Nat.mul_le_mul_left L (Nat.le_trans B.activeEntries entryCount))
  have hcS : w.comparisons ≤ S * L := by
    rw [Nat.mul_comm S L]
    have hnHS : nH ≤ S := by
      dsimp [S]
      omega
    exact Nat.le_trans hc (Nat.mul_le_mul_left L hnHS)
  have htS : w.tests ≤ S * L := by
    rw [Nat.mul_comm S L]
    exact Nat.le_trans ht (Nat.mul_le_mul_left L hmS)
  have hC : u.comparisons ≤ c * K :=
    Nat.le_trans comparisonWords (Nat.mul_le_mul_left c (Nat.le_trans hcS hLK))
  have hT : u.tests ≤ t * K :=
    Nat.le_trans testWords (Nat.mul_le_mul_left t (Nat.le_trans htS hLK))

  have hCalls : w.atDepth + w.ancestry ≤ 2 * (S * L) := by
    have hd := B.atDepth
    have ha := B.ancestry
    have hh := B.activeHeads
    have he : L * nH + L * mH = S * L := by
      simpa only [S, Nat.mul_add] using (Nat.mul_comm L (nH + mH))
    omega
  have hJ : u.depths.sum + u.ancestries.sum ≤ 44 * K := calc
    _ ≤ w.atDepth * (22 * L) + w.ancestry * (22 * L) :=
      Nat.add_le_add (packedSumBound Lpos levelBound depthCharges depthCount)
        (packedSumBound Lpos levelBound ancestryCharges ancestryCount)
    _ = (w.atDepth + w.ancestry) * (22 * L) := (Nat.add_mul _ _ _).symm
    _ ≤ (2 * (S * L)) * (22 * L) := Nat.mul_le_mul_right _ hCalls
    _ = 44 * K := by
      change (2 * (S * L)) * (22 * L) = (2 * 22) * (S * (L * L))
      ac_rfl

  have hw : n.writes ≤ 18 * S := by
    have h := B.writes
    have ha := B.allocations
    omega
  have hI : u.install ≤ (i + 18 * z) * K := calc
    _ ≤ i * (n.heads * L) + z * (n.writes * L) := installWords
    _ ≤ i * K + z * (18 * K) := by
      apply Nat.add_le_add
      · exact Nat.mul_le_mul_left i
          (Nat.le_trans (Nat.mul_le_mul_right L hnS) hLK)
      · apply Nat.mul_le_mul_left z
        calc
          n.writes * L ≤ (18 * S) * L := Nat.mul_le_mul_right L hw
          _ = 18 * (S * L) := Nat.mul_assoc _ _ _
          _ ≤ 18 * K := Nat.mul_le_mul_left 18 hLK
    _ = (i + 18 * z) * K := by
      rw [Nat.add_mul]
      exact congrArg (fun x => i * K + x) (by ac_rfl)

  have hR : u.lookups.sum ≤ b * K := calc
    _ ≤ u.lookups.length * (b * L) := sumBound _ _ lookupWords
    _ ≤ S * (b * L) :=
      Nat.mul_le_mul_right _ (Nat.le_trans lookupCount (Nat.le_trans B.requests hnS))
    _ = b * (S * L) := by ac_rfl
    _ ≤ b * K := Nat.mul_le_mul_left b hLK

  apply Nat.le_trans coversFold
  simp only [WordMeter.total, Nat.add_mul] at hI ⊢
  omega

/-
Thus for fixed local word-model constants the fold charge is
O((nH + mH) * L^2). The source constants in the proof are 16 for the
planner's per-head allowance, 18 for logical installation writes, 22
per L for one packed jump call, and 2 for dictionary-build comparisons.
Nothing here asserts final arena word storage or preserves any
previously stated long-path cost.
-/
end AggregateEX24

end EX24.PreparedSweep
