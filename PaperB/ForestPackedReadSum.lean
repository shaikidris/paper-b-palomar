module

public import PaperB.ForestRealCounts
public import PaperB.ForestPackedSearch

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep.PackedReads

open AggregateEX24 EX24.PreStep PaperB PaperB.ForestHead
open PaperB.LabelledQuotient PaperB.LabelledQuotient.ForestPackedSearch PaperB.Jumps

def packedHead {H : LabelledQuotient} (c : Config H) (s : State H)
    (rank : Vertex H → Nat) (row : Row H) : ChargedActive H :=
  match planPrepared rank row.head row.tests with
  | none => { result := ForestHead.stopped, charge := 0 }
  | some (m, key) => packedActive c s row.tests m key

theorem packedHead_project {H : LabelledQuotient} (c : Config H) (s : State H)
    (rank : Vertex H → Nat) (row : Row H) (hc : c.usePackedWords = c) :
    (packedHead c s rank row).result =
      ForestHead.runPrepared (selectors c s) rank row.head row.tests := by
  cases hp : planPrepared rank row.head row.tests with
  | none => simp [packedHead, ForestHead.runPrepared, hp]
  | some p =>
    rcases p with ⟨m, key⟩
    simpa only [packedHead, ForestHead.runPrepared, hp, hc] using
      packedActive_project c s row.tests m key

private theorem measured_of_step {H : LabelledQuotient} {c : Config H}
    {s : State H} {rank : Vertex H → Nat} {row : Row H} {r : HeadResult H}
    (hc : c.usePackedWords = c)
    (hs : stepPrepared c s rank row.head row.tests = some r) :
    r.measured = (packedHead c s rank row).result := by
  rw [packedHead_project c s rank row hc]
  unfold stepPrepared at hs
  split at hs
  · dsimp only at hs
    cases hi : install c s.tables
        (ForestHead.runPrepared (selectors c s) rank row.head row.tests).step <;>
      simp [hi] at hs
    cases hs
    rfl
  · simp at hs

private theorem prepared_max_mem
    {H : LabelledQuotient} (rank : Vertex H → Nat)
    {xs : List (Vertex H)} {m : Vertex H}
    (hm : maxByRank rank xs = some m) : m ∈ xs := by
  first
  | exact?
  | let pick : Vertex H → List (Vertex H) → Vertex H := by
      first
      | exact maxByRankAux rank
      | exact fun a ys => maxByRankAux rank ys a
    have aux (a : Vertex H) (ys : List (Vertex H)) :
        pick a ys ∈ a :: ys := by
      induction ys generalizing a with
      | nil => simp [pick, maxByRankAux]
      | cons b ys ih =>
          have ha := ih a
          have hb := ih b
          simp only [List.mem_cons] at ha hb ⊢
          simp only [pick, maxByRankAux]
          split
          all_goals
            first
            | exact ha.elim Or.inl (fun ht => Or.inr (Or.inr ht))
            | exact Or.inr hb
            | grind
    cases xs with
    | nil => simp [maxByRank] at hm
    | cons a ys =>
        change some (pick a ys) = some m at hm
        exact (Option.some.inj hm) ▸ aux a ys

private theorem pivotMem {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {m : Vertex H} {key : Option (CutPair H)}
    (hp : planPrepared rank row.head row.tests = some (m, key)) :
    m ∈ row.tests := by
  apply prepared_max_mem rank
  unfold planPrepared at hp
  split at hp
  · simp at hp
  · split at hp
    · simp at hp
    · cases hm : maxByRank rank row.tests <;> simp_all

def PrefixSite {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat)
    (n : Nat) (s : State H) (row : Row H) : Prop :=
  TestSpec row.head row.tests ∧
    ∃ (F : JumpForest) (up : Fin F.size → Fin F.size),
      Grounded c F s.tables ∧
      Nonempty (Embedding c s F rank up (fun v => rank v < rank row.head)) ∧
      F.numInserted ≤ n

set_option maxHeartbeats 1000000 in
theorem packedHead_le {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {s : State H} {row : Row H} {r : HeadResult H}
    {n L : Nat}
    (hc : c.usePackedWords = c)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (hs : stepPrepared c s rank row.head row.tests = some r)
    (site : PrefixSite c rank n s row) (hPow : n + 2 ≤ 2 ^ L) :
    (packedHead c s rank row).charge ≤ 22 * L *
      ((headWork rank row r).comparisons + (headWork rank row r).tests +
        (headWork rank row r).activeHeads) := by
  cases hp : planPrepared rank row.head row.tests with
  | none =>
    have ha : (headWork rank row r).activeHeads = 0 := by
      unfold headWork
      rw [hp] <;> rfl
    simp [packedHead, hp, ha]
  | some p =>
    rcases p with ⟨m, key⟩
    obtain ⟨T, F, up, g, hEmbedding, hInserted⟩ := site
    obtain ⟨E⟩ := hEmbedding
    have hPred (u : Vertex H) (hu : u ∈ row.tests) : rank u < rank row.head :=
      rankArc u row.head ((T.cover u).mp hu)
    have hPrior (u : Vertex H) (hu : rank u < rank row.head) :
        (selectors c s).label u < s.tables.next := by
      first
      | exact?
      | cases E
        first
        | solve_by_elim
        | grind
        | cases g
          grind
    have hPivot : (selectors c s).label m < s.tables.next :=
      hPrior m (hPred m (pivotMem (row := row) hp))
    have hb := packedActive_charge_of_prefix g rank (rank row.head) row.tests m key
      hInserted hPow hPivot hPrior hPred
    have hr := measured_of_step (row := row) hc hs
    rw [packedHead_project c s rank row hc, ForestHead.runPrepared, hp] at hr
    have ha : (headWork rank row r).activeHeads = 1 := by
      unfold headWork
      rw [hp] <;> rfl
    have hComparisons :
        (headWork rank row r).comparisons = r.measured.search.comparisons := rfl
    have hTests : (headWork rank row r).tests = r.measured.search.tests := rfl
    rw [ha, hComparisons, hTests, hr]
    simpa only [packedHead, hp, hc] using hb

/-- Counts only packed reads, following the successor state of each successful step. -/
def packedReadSum {H : LabelledQuotient} (c : Config H) (rank : Vertex H → Nat) :
    State H → List (Row H) → Option Nat
  | _, [] => some 0
  | s, row :: rows => do
    let r ← stepPrepared c s rank row.head row.tests
    let q ← packedReadSum c rank r.state rows
    pure ((packedHead c s rank row).charge + q)

private theorem add_read_bounds {x y A B : Nat}
    (hx : x ≤ A) (hy : y ≤ B) : x + y ≤ A + B := by
  omega

theorem packedReadSum_of_localTrace {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {P : State H → Row H → Prop}
    {s out : State H} {rows : List (Row H)} {log : Log H} {n L : Nat}
    (hc : c.usePackedWords = c)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (hPow : n + 2 ≤ 2 ^ L)
    (atSite : ∀ s row, P s row → PrefixSite c rank n s row)
    (ht : LocalTrace c rank P s rows out log) :
    ∃ (q : Nat) (k : Count) (w : Work), packedReadSum c rank s rows = some q ∧
      WorkTrace c rank s rows out log k w ∧
      q ≤ 22 * L * (w.comparisons + w.tests + w.activeHeads) := by
  have extend {src dst : State H} {row : Row H} {rest : List (Row H)}
      {r : HeadResult H} {tailLog : Log H}
      (hs : stepPrepared c src rank row.head row.tests = some r)
      (hp : P src row)
      (ih : ∃ (q : Nat) (k : Count) (w : Work),
        packedReadSum c rank r.state rest = some q ∧
          WorkTrace c rank r.state rest dst tailLog k w ∧
          q ≤ 22 * L * (w.comparisons + w.tests + w.activeHeads)) :
      ∃ (q : Nat) (k : Count) (w : Work),
        packedReadSum c rank src (row :: rest) = some q ∧
          WorkTrace c rank src (row :: rest) dst
            (Event.ofResult row.head r :: tailLog) k w ∧
          q ≤ 22 * L * (w.comparisons + w.tests + w.activeHeads) := by
    obtain ⟨q, k, w, hq, hw, hb⟩ := ih
    let wHead : Work := headWork rank row r
    let wTotal : Work := wHead.add w
    let kTotal : Count := Count.prepend r k
    let qHead : Nat := (packedHead c src rank row).charge
    let qTotal : Nat := qHead + q
    let scale : Nat := 22 * L
    let a : Nat := wHead.comparisons + wHead.tests + wHead.activeHeads
    let b : Nat := w.comparisons + w.tests + w.activeHeads

    have hHead : qHead ≤ scale * a :=
      packedHead_le hc rankArc hs (atSite src row hp) hPow
    have hTail : q ≤ scale * b := hb
    have hSum : qTotal ≤ scale * a + scale * b :=
      add_read_bounds hHead hTail
    have hParts :
        a + b = wTotal.comparisons + wTotal.tests + wTotal.activeHeads := by
      change
        (wHead.comparisons + wHead.tests + wHead.activeHeads) +
            (w.comparisons + w.tests + w.activeHeads) =
          (wHead.comparisons + w.comparisons) + (wHead.tests + w.tests) +
            (wHead.activeHeads + w.activeHeads)
      omega
    have hBound : qTotal ≤
        22 * L * (wTotal.comparisons + wTotal.tests + wTotal.activeHeads) := by
      change qTotal ≤ scale * (wTotal.comparisons + wTotal.tests + wTotal.activeHeads)
      calc
        qTotal ≤ scale * a + scale * b := hSum
        _ = scale * (a + b) := (Nat.mul_add scale a b).symm
        _ = scale * (wTotal.comparisons + wTotal.tests + wTotal.activeHeads) :=
          congrArg (fun t : Nat => scale * t) hParts

    have hRead : packedReadSum c rank src (row :: rest) = some qTotal := by
      simp [packedReadSum, hs, hq, qTotal, qHead] <;> rfl
    have hWork : WorkTrace c rank src (row :: rest) dst
        (Event.ofResult row.head r :: tailLog) kTotal wTotal :=
      WorkTrace.cons hs hw
    exact ⟨qTotal, kTotal, wTotal, hRead, hWork, hBound⟩

  induction ht with
  | nil s =>
    have hZero : (0 : Nat) ≤ 22 * L *
        (Work.zero.comparisons + Work.zero.tests + Work.zero.activeHeads) :=
      Nat.zero_le _
    exact ⟨0, Count.zero, Work.zero, rfl, WorkTrace.nil s, hZero⟩
  | cons hs hp _ ih =>
    exact extend hs hp ih

end EX24.PreparedSweep.PackedReads
