module

public import PaperB.ForestFastOrderedReader
public import PaperB.ForestRealCounts
public import PaperB.ForestOrderedReadBound
public import PaperB.ForestLookupTolls
public import PaperB.ForestPreparedBuild
public import PaperB.ForestExactDictionary

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open AggregateEX24

private theorem fourTolls_le (n m L q a : Nat) (hL : 1 ≤ L)
    (hq : q ≤ 22 * L * (L * n + L * m + n))
    (ha : a ≤ (L + 1) * n) :
    q + a + m + m ≤ 46 * (n + m) * L ^ 2 := by
  let T := (n + m) * L ^ 2
  have hn : n ≤ L * n := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right n hL
  have hb : L * n + L * m + n ≤ 2 * (L * (n + m)) := by
    rw [Nat.mul_add]
    omega
  have hq' : q ≤ 44 * T := calc
    q ≤ 22 * L * (L * n + L * m + n) := hq
    _ ≤ 22 * L * (2 * (L * (n + m))) := Nat.mul_le_mul_left _ hb
    _ = 44 * T := by
      dsimp only [T]
      rw [Nat.pow_succ, Nat.pow_one]
      change _ = (22 * 2) * ((n + m) * (L * L))
      ac_rfl
  have hLL : L ≤ L ^ 2 := by
    rw [Nat.pow_succ, Nat.pow_one]
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right L hL
  have hm : 2 * m ≤ (L + 1) * m :=
    Nat.mul_le_mul_right m (by omega)
  have ha' : a + m + m ≤ 2 * T := calc
    a + m + m ≤ (L + 1) * (n + m) := by
      rw [Nat.mul_add]
      omega
    _ ≤ (2 * L ^ 2) * (n + m) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * T := by
      dsimp only [T]
      ac_rfl
  calc
    q + a + m + m ≤ 46 * T := by omega
    _ = 46 * (n + m) * L ^ 2 := by
      dsimp only [T]
      ac_rfl

-- Infer the build's cover from its public dedup-count theorem.
private abbrev fourTollPrep (H : LabelledQuotient) :=
  (fun cv (_ : (ForestIncomingPrep.build H cv).visits = H.arcCount) =>
    ForestIncomingPrep.build H cv) _ (ForestPreparedBuild.dedup_visits_eq_arcCount H)

theorem runOrderedReaderFast_prepared_fourTolls {H : LabelledQuotient}
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
    let prep := fourTollPrep H
    let p := prep.tests
    let c := orderedConfig p large
    let rows := orderedRows p data size_data
    let s := initial c (PaperB.Jumps.ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    let r := runOrderedReaderFast p data size_data rank large increasing covers rankArc flat
    let m := H.arcCount
    ∃ (q : Nat) (cnt : Count) (w : Work) (qs : List (CutPair H)),
      runOrdered p data size_data rank large = some (r.out, r.log) ∧
      PackedReads.packedReadSum c rank s rows = some q ∧
      CountedTrace c rank s rows r.out r.log cnt ∧
      WorkTrace c rank s rows r.out r.log cnt w ∧
      PairLookupTrace c rank s rows r.out r.log cnt w qs ∧
      qs.length = w.requests ∧ prep.visits = m ∧
      q + pairLookupComparisons c qs + m + m ≤
        46 * (H.vertexCount + m) * L ^ 2 := by
  intro prep p c rows s r m
  obtain ⟨_, _, q, _, hread, hq⟩ :=
    runOrdered_packedSelectorReads_le p data size_data rank large
      increasing covers rankArc flat L logBound
  obtain ⟨out, log, cnt, w, hrun, hc, hw, b, _, _⟩ :=
    runOrdered_realCounts p data size_data rank large
      increasing covers rankArc flat L logBound
  have he : (out, log) = (r.out, r.log) :=
    Option.some.inj (hrun.symm.trans r.ran)
  have ho : out = r.out := congrArg Prod.fst he
  have hl : log = r.log := congrArg Prod.snd he
  rw [ho, hl] at hc hw
  obtain ⟨qs, ht, hlen, ha⟩ := hw.withPairLookups
  have hrows : rows.length = H.vertexCount := by
    simp [rows, orderedRows, size_data]
  have hentries : entryTotal rows ≤ H.arcCount := by
    refine Nat.le_trans
      (ForestPreparedBuild.entryTotal_le_arcTotal data size_data rank increasing covers) ?_
    exact Nat.le_of_eq (ForestPreparedBuild.arcTotal_eq_arcCount H)
  have hd : c.dict.size ≤ H.vertexCount := by
    change (ForestDictionary.dictionary p _).size ≤ H.vertexCount
    exact (ForestDictionary.dictionary_spec p _).2.2
  have hlog : Nat.log2 ((orderedConfig p large).dict.size + 1) + 1 ≤ L :=
    logBound (c.dict.size + 1) (Nat.add_le_add_right hd 1)
  have hreq : w.requests ≤ H.vertexCount :=
    Nat.le_trans b.requests (Nat.le_of_eq (b.heads.trans hrows))
  have ha' : pairLookupComparisons c qs ≤ (L + 1) * H.vertexCount :=
    Nat.le_trans ha (Nat.mul_le_mul (by omega) hreq)
  have hq' : q ≤
      22 * L * (L * H.vertexCount + L * H.arcCount + H.vertexCount) := calc
    q ≤ 22 * L * (L * rows.length + L * entryTotal rows + rows.length) := hq
    _ ≤ _ := by
      rw [hrows]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_right
        (Nat.add_le_add_left (Nat.mul_le_mul_left L hentries) _) _)
  have hL : 1 ≤ L := by
    have hz := logBound 0 (Nat.zero_le _)
    omega
  exact ⟨q, cnt, w, qs, r.ran, hread, hc, hw, ht, hlen,
    ForestPreparedBuild.dedup_visits_eq_arcCount H,
    fourTolls_le H.vertexCount H.arcCount L q _ hL hq' ha'⟩

end PaperB
