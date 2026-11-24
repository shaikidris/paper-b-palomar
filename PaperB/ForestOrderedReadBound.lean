module

public import PaperB.ForestPackedReadSum
public import PaperB.ForestRealCounts

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace EX24.PreparedSweep

open AggregateEX24 EX24.PreStep PaperB PaperB.ForestHead PaperB.LabelledQuotient PaperB.Jumps

private theorem packedWorkTrace_unique {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat}
    {s out out' : State H} {rows : List (Row H)} {log log' : Log H}
    {n n' : Count} {w w' : Work}
    (ht : WorkTrace c rank s rows out log n w)
    (ht' : WorkTrace c rank s rows out' log' n' w') :
    n = n' ∧ w = w' := by
  induction ht generalizing out' log' n' w' with
  | nil =>
      cases ht'
      exact ⟨rfl, rfl⟩
  | cons hs _ ih =>
      cases ht' with
      | cons hs' tail' =>
          have hr := Option.some.inj (hs.symm.trans hs')
          cases hr
          obtain ⟨hn, hw⟩ := ih tail'
          exact ⟨by rw [hn], by rw [hw]⟩

private theorem aggregateSites_of_packedSites {H : LabelledQuotient}
    {c : Config H} {rank : Vertex H → Nat} {limit : Nat}
    {s : State H} {rows : List (Row H)}
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (hp : Sites c rank (PackedReads.PrefixSite c rank limit) s rows) :
    Sites c rank (AggregateEX24.SiteOK c rank) s rows := by
  induction rows generalizing s with
  | nil => trivial
  | cons row rest ih =>
      intro r hs
      obtain ⟨⟨T, F, up, g, ⟨E⟩, _⟩, tail⟩ := hp r hs
      refine ⟨?_, ih tail⟩
      first
      | exact siteOK_of_prefix E g T rankArc
      | exact?

/-- A bound on packed selector reads along the actual ordered build,
not on the total work of the build. -/
theorem runOrdered_packedSelectorReads_le {H : LabelledQuotient}
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
    ∃ (out : State H) (log : Log H) (q : Nat),
      runOrdered p data size_data rank large = some (out, log) ∧
      PackedReads.packedReadSum c rank s rows = some q ∧
      q ≤ 22 * L * (L * rows.length + L * entryTotal rows + rows.length) := by
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
      PrefixLocalAt c rank (PackedReads.PrefixSite c rank H.vertexCount) row := by
    intro row _ st F up g _hup E T
    have stepLayout : JumpWordLayout c.region F st.tables.mem := g.layout
    have hInserted : F.numInserted ≤ H.vertexCount := by
      first
      | exact stepLayout.inserted_le
      | simpa [c, orderedConfig, Config.usePackedWords, ConcreteInit.region]
          using stepLayout.inserted_le
    exact ⟨T, F, up, g, ⟨E⟩, hInserted⟩
  obtain ⟨out, log, hrun, hTrace, _, _, _, _, ht⟩ :=
    fromRoot_total_local p c rank (PackedReads.PrefixSite c rank H.vertexCount)
      layout hc rfl rfl (fun _ => rfl) rankArc distinctRanks flat full parents hLocal
  obtain ⟨n, hn⟩ := hTrace.exists_count
  have hrows : rows.length = H.vertexCount := by
    first
    | simpa [rows, orderedRows, size_data]
    | change (orderedRows p data size_data).length = H.vertexCount
      exact?
  have room : s.tables.next + rows.length ≤ H.vertexCount + 1 := by
    change 1 + rows.length ≤ H.vertexCount + 1
    omega
  obtain ⟨w, hw, hb, _⟩ :=
    AggregateEX24.aggregate (nH := H.vertexCount) (L := L)
      distinctRanks logBound hn (aggregateSites_of_packedSites rankArc ht.sites) room
  have hPow : H.vertexCount + 2 ≤ 2 ^ L := by
    have hk := logBound (H.vertexCount + 1) (Nat.le_refl _)
    have hlog : Nat.log2 (H.vertexCount + 1) < L := by omega
    have hlt : H.vertexCount + 1 < 2 ^ L := by
      first
      | exact (Nat.log2_lt (by omega)).mp hlog
      | have hsmall : H.vertexCount + 1 <
            2 ^ (Nat.log2 (H.vertexCount + 1) + 1) := by exact?
        exact Nat.lt_of_lt_of_le hsmall (Nat.pow_le_pow_right (by decide) hk)
    omega
  obtain ⟨q, k, wRead, hq, hwRead, hqBound⟩ :=
    PackedReads.packedReadSum_of_localTrace hc rankArc hPow
      (fun _ _ hp => hp) ht
  obtain ⟨_, hWork⟩ := packedWorkTrace_unique hwRead hw
  rw [hWork] at hqBound
  have hHeads : w.activeHeads ≤ rows.length := by
    simpa only [hb.heads] using hb.activeHeads
  have hComparisons : w.comparisons ≤ L * rows.length :=
    Nat.le_trans hb.comparisons (Nat.mul_le_mul_left L hHeads)
  have hTests : w.tests ≤ L * entryTotal rows :=
    Nat.le_trans hb.tests (Nat.mul_le_mul_left L hb.activeEntries)
  have hSum : w.comparisons + w.tests + w.activeHeads ≤
      L * rows.length + L * entryTotal rows + rows.length :=
    Nat.add_le_add (Nat.add_le_add hComparisons hTests) hHeads
  exact ⟨out, log, q, hrun, hq,
    Nat.le_trans hqBound (Nat.mul_le_mul_left (22 * L) hSum)⟩

end EX24.PreparedSweep
