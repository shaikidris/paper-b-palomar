module

public import PaperB.ForestActualSweepBudget
public import PaperB.ForestResidualTolls

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- To append this body to ForestActualSweepBudget itself, add the
-- ForestResidualTolls import to that file's import header and omit the
-- ForestActualSweepBudget self-import.

set_option autoImplicit false

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS PaperB.Jumps
open AggregateEX24

-- Definitionally the preparation used by fourTollPrep. Infer its cover
-- from the same public theorem, without referring to the private name.
private abbrev actualResidualPrep (H : LabelledQuotient) :=
  (fun cv (_ : (ForestIncomingPrep.build H cv).visits = H.arcCount) =>
    ForestIncomingPrep.build H cv) _ (ForestPreparedBuild.dedup_visits_eq_arcCount H)

-- Compare traces before identifying their final states and logs. This
-- leaves only the common starting state and row list to refine in cases.
private theorem actualResidual_workTrace_indices
    {H : LabelledQuotient} {c : Config H} {rank : Vertex H → Nat}
    {s out : State H} {rows : List (Row H)} {log : Log H}
    {cnt : Count} {w : Work}
    (h : WorkTrace c rank s rows out log cnt w) :
    ∀ {out' : State H} {log' : Log H} {cnt' : Count} {w' : Work},
      WorkTrace c rank s rows out' log' cnt' w' →
        cnt = cnt' ∧ w = w' := by
  induction h with
  | nil s =>
      intro out' log' cnt' w' h'
      cases h'
      exact ⟨rfl, rfl⟩
  | cons hs _ ih =>
      intro out' log' cnt' w' h'
      cases h' with
      | cons hs' ht' =>
          have he := Option.some.inj (hs.symm.trans hs')
          cases he
          obtain ⟨hc, hw⟩ := ih ht'
          cases hc
          cases hw
          exact ⟨rfl, rfl⟩

/-- EX2.4 site accounting for the original prepared fast-reader result `r`,
with its World unchanged. The ordered local proof is identified with
`r.out` and `r.log`; it does not change any runtime action.

The four tolls charge packed selector reads, pair-lookup comparisons,
and the two existing arc-count charges. The residual toll separately
charges row visits, label bounds tests and writes, event formation and
cons, reversal visits, installation entries and returns, lookup dispatch,
planner ticks, search comparisons and tests, `L` units per measured
selector call, and the exact logged append accesses. It does not charge
packed reads or pair-lookup comparisons again. The combined bound is
for these charged sites, not for total primitive instructions, uncharged
preprocessing, or storage. -/
theorem runOrderedReaderFast_prepared_fourTolls_residualToll
    {H : LabelledQuotient}
    (data : Array (Vertex H)) (size_data : data.size = H.vertexCount)
    (rank : Vertex H → Nat) (large : 3 ≤ H.vertexCount)
    [DecidableEq (CutPair H)]
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) <
        rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (L : Nat) (logBound : ∀ k ≤ H.vertexCount + 1, Nat.log2 k + 1 ≤ L) :
    let prep := actualResidualPrep H
    let p := prep.tests
    let c := orderedConfig p large
    let rows := orderedRows p data size_data
    let s := initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    let r := runOrderedReaderFast p data size_data rank large increasing covers rankArc flat
    let m := H.arcCount
    ∃ (q : Nat) (cnt : Count) (w : Work) (qs : List (CutPair H)) (a d : Nat),
      runOrdered p data size_data rank large = some (r.out, r.log) ∧
      PackedReads.packedReadSum c rank s rows = some q ∧
      CountedTrace c rank s rows r.out r.log cnt ∧
      WorkTrace c rank s rows r.out r.log cnt w ∧
      AggregateEX24.Bounds L rows cnt w ∧
      PairLookupTrace c rank s rows r.out r.log cnt w qs ∧
      qs.length = w.requests ∧ prep.visits = m ∧
      ResidualUnit.AppendTrace c rank s rows r.out r.log cnt a d ∧
      d = cnt.allocations ∧ a ≤ 14 * d ∧
      q + pairLookupComparisons c qs + m + m ≤
        46 * (H.vertexCount + m) * L ^ 2 ∧
      ResidualUnit.toll L cnt w a ≤
        44 * (H.vertexCount + m) * L ^ 2 ∧
      (q + pairLookupComparisons c qs + m + m) +
        ResidualUnit.toll L cnt w a ≤
          90 * (H.vertexCount + m) * L ^ 2 := by
  intro prep p c rows s r m
  obtain ⟨q, cnt, w, qs, hrun, hread, hc, hw, hlookup, hlen, hvisits, hfour⟩ :=
    runOrderedReaderFast_prepared_fourTolls data size_data rank large
      increasing covers rankArc flat L logBound

  have distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v := by
    intro u v huv
    obtain ⟨i, hi⟩ := covers u
    obtain ⟨j, hj⟩ := covers v
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

  have full : FullRows p rank rows :=
    orderedRows_full p data size_data rank increasing covers
  have layout : JumpWordLayout c.region JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1 := by
    change JumpWordLayout (ConcreteInit.region H.vertexCount) JumpForest.init
      (ConcreteInit.initImage H.vertexCount).1
    exact?
  have hpacked : c.usePackedWords = c := rfl
  have parents : ∀ row ∈ rows, ParentAt c rank row := by
    intro row hr st F up g _hup E
    have T : TestSpec row.head row.tests := by
      rw [full.tests_eq row hr]
      exact p.spec row.head
    exact _root_.EX24.PreparedSweep.runPrepared_parent_occupied
      (c := c) (s := st) (F := F) (rank := rank) (up := up) (row := row)
      hpacked E g T rankArc
  have localAt : ∀ row ∈ rows,
      PrefixLocalAt c rank (AggregateEX24.SiteOK c rank) row := by
    intro row _hr st F up g _hup E T
    exact siteOK_of_prefix E g T rankArc

  have hlocal : LocalTrace c rank (AggregateEX24.SiteOK c rank)
      s rows r.out r.log := by
    obtain ⟨out, log, hrunLocal, _, _, _, _, _, ht⟩ :=
      fromRoot_total_local p c rank (AggregateEX24.SiteOK c rank)
        layout hpacked rfl rfl (fun _ => rfl) rankArc distinctRanks flat
        full parents localAt
    have hrun' : runOrdered p data size_data rank large = some (out, log) :=
      hrunLocal
    have he : (out, log) = (r.out, r.log) :=
      Option.some.inj (hrun'.symm.trans hrun)
    have ho : out = r.out := congrArg Prod.fst he
    have hl : log = r.log := congrArg Prod.snd he
    rw [ho, hl] at ht
    exact ht
  have hsites : AggregateEX24.Sites c rank (AggregateEX24.SiteOK c rank)
      s rows := hlocal.sites
  have hinstalls : ChronologicalIndex.PreparedInstalls c rank :=
    ChronologicalIndex.preparedInstalls c rank distinctRanks
  obtain ⟨a, d, happend⟩ := ResidualUnit.append_of_work hinstalls hw hsites

  have hrows : rows.length = H.vertexCount := by
    simp [rows, orderedRows, size_data]
  have hentries : entryTotal rows ≤ m :=
    Nat.le_trans
      (ForestPreparedBuild.entryTotal_le_arcTotal data size_data rank increasing covers)
      (Nat.le_of_eq (ForestPreparedBuild.arcTotal_eq_arcCount H))
  have room : s.tables.next + rows.length ≤ H.vertexCount + 1 := by
    change 1 + rows.length ≤ H.vertexCount + 1
    omega
  obtain ⟨w', hw', hb', _⟩ :=
    AggregateEX24.aggregate (nH := H.vertexCount) (L := L)
      distinctRanks logBound hc hsites room
  have hwork : w = w' := (actualResidual_workTrace_indices hw hw').2
  have hb : AggregateEX24.Bounds L rows cnt w := by
    simpa only [hwork] using hb'
  have hL : 1 ≤ L := by
    have hz := logBound 0 (Nat.zero_le (H.vertexCount + 1))
    omega
  have hres : ResidualUnit.toll L cnt w a ≤
      44 * (H.vertexCount + m) * L ^ 2 :=
    ResidualUnit.toll_le happend hb hrows hentries hL
  have htotal :
      (q + pairLookupComparisons c qs + m + m) +
        ResidualUnit.toll L cnt w a ≤
          90 * (H.vertexCount + m) * L ^ 2 := calc
    _ ≤ 46 * (H.vertexCount + m) * L ^ 2 +
        44 * (H.vertexCount + m) * L ^ 2 := Nat.add_le_add hfour hres
    _ = 90 * (H.vertexCount + m) * L ^ 2 := by
      rw [← Nat.add_mul, ← Nat.add_mul]

  exact ⟨q, cnt, w, qs, a, d, hrun, hread, hc, hw, hb, hlookup, hlen,
    hvisits, happend, happend.delta_eq_allocations, happend.accesses_le,
    hfour, hres, htotal⟩

end PaperB
