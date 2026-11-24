module

public import PaperB.ForestActualFull
public import PaperB.ForestTopologicalTotal
public import PaperB.ForestSiteDepth

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep

open AggregateEX24 EX24.PreStep PaperB PaperB.ForestHead PaperB.LabelledQuotient PaperB.Jumps

theorem LocalTrace.sites {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {P : State H → Row H → Prop}
    {s out : State H} {rows : List (Row H)} {log : Log H}
    (ht : LocalTrace c rank P s rows out log) :
    AggregateEX24.Sites c rank P s rows := by
  induction ht with
  | nil s => exact True.intro
  | cons hs hp _ ih =>
      intro r hr
      have heq := Option.some.inj (hs.symm.trans hr)
      cases heq
      exact ⟨hp, ih⟩

private theorem counted_of_localTrace {H : LabelledQuotient} {c : Config H}
    {rank : Vertex H → Nat} {P : State H → Row H → Prop}
    {s out : State H} {rows : List (Row H)} {log : Log H}
    (ht : LocalTrace c rank P s rows out log) :
    ∃ n, CountedTrace c rank s rows out log n := by
  induction ht with
  | nil s => exact ⟨_, .nil s⟩
  | cons hs _ _ ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨_, .cons hs hn⟩

/-- Exact measured counts for the packed ordered run, under one log budget.
Word-level costs and storage bounds are left to future work. -/
theorem runOrdered_realCounts {H : LabelledQuotient}
    (p : ForestDictionary.Rows H)
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (L : Nat) (logBound : ∀ k ≤ H.vertexCount + 1, Nat.log2 k + 1 ≤ L) :
    let c := orderedConfig p large
    let rows := orderedRows p data size_data
    let s := initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    ∃ (out : State H) (log : Log H) (n : Count) (w : Work),
      runOrdered p data size_data rank large = some (out, log) ∧
      CountedTrace c rank s rows out log n ∧
      WorkTrace c rank s rows out log n w ∧
      AggregateEX24.Bounds L rows n w ∧
      out.tables.next = s.tables.next + n.allocations ∧
      OutputOK c rank out := by
  let c := orderedConfig p large
  let rows := orderedRows p data size_data
  let s := initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
  have full : FullRows p rank rows :=
    orderedRows_full p data size_data rank increasing covers
  have distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b := by
    intro a b hab
    obtain ⟨i, hi⟩ := covers a
    obtain ⟨j, hj⟩ := covers b
    have hij : i.val = j.val := by
      by_cases hlt : i.val < j.val
      · have h := increasing i j hlt
        rw [hi, hj] at h
        omega
      · by_cases hgt : j.val < i.val
        · have h := increasing j i hgt
          rw [hj, hi] at h
          omega
        · omega
    exact hi.symm.trans
      ((congrArg (orderedVertexAt data size_data) (Fin.ext hij)).trans hj)
  have layout : JumpWordLayout c.region JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1 := by
    change JumpWordLayout (ConcreteInit.region H.vertexCount) JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1
    exact?
  have hc : c.usePackedWords = c := rfl
  have parents : ∀ row ∈ rows, ParentAt c rank row := by
    intro row hr st F up g _hup E
    have T : TestSpec row.head row.tests := by
      rw [full.tests_eq row hr]
      exact p.spec row.head
    exact EX24.PreparedSweep.runPrepared_parent_occupied
      (c := c) (s := st) (F := F) (rank := rank) (up := up) (row := row)
      hc E g T rankArc
  have hLocal : ∀ row ∈ rows,
      PrefixLocalAt c rank (AggregateEX24.SiteOK c rank) row := by
    intro row _ st F up g _hup E T
    exact siteOK_of_prefix E g T rankArc
  obtain ⟨out, log, hrun, _, _, _, _, hout, ht⟩ :=
    fromRoot_total_local p c rank (AggregateEX24.SiteOK c rank)
      layout hc rfl rfl (fun _ => rfl) rankArc distinctRanks flat full parents hLocal
  obtain ⟨n, hn⟩ := counted_of_localTrace ht
  have hrows : rows.length = H.vertexCount := by
    first
    | simpa [rows, orderedRows, size_data]
    | change (orderedRows p data size_data).length = H.vertexCount
      exact?
  have room : s.tables.next + rows.length ≤ H.vertexCount + 1 := by
    change 1 + rows.length ≤ H.vertexCount + 1
    omega
  obtain ⟨w, hw, hb, hnext⟩ :=
    AggregateEX24.aggregate (nH := H.vertexCount) (L := L)
      distinctRanks logBound hn ht.sites room
  exact ⟨out, log, n, w, hrun, hn, hw, hb, hnext, hout⟩

end EX24.PreparedSweep
