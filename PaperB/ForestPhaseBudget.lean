module

public import PaperB.ForestIntegratedSiteToll
public import PaperB.OracleContract
public import PaperB.StaticGroupedTreeReader

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace PaperB

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS PaperB.Jumps
open PaperB.PairLookup PaperB.PairLookup.KeyMerge
open AggregateEX24

-- Use the same preparation as the integrated sweep theorem, without naming
-- that module's private abbreviation.
private abbrev chargedReaderPrep (H : LabelledQuotient) :=
  (fun cv (_ : (ForestIncomingPrep.build H cv).visits = H.arcCount) =>
    ForestIncomingPrep.build H cv) _ (ForestPreparedBuild.dedup_visits_eq_arcCount H)

private theorem oracleLogBound (n : Nat) :
    ∀ k ≤ n + 1, Nat.log2 k + 1 ≤ OracleContract.L n := by
  intro k hk
  change Nat.log2 k + 1 ≤ Nat.log2 (n + 1) + 1
  have hmono : Nat.log2 k ≤ Nat.log2 (n + 1) := by
    by_cases hz : k = 0
    · subst k
      exact Nat.zero_le _
    · exact (Nat.le_log2 (by omega : n + 1 ≠ 0)).mpr
        (Nat.le_trans (Nat.log2_self_le hz) hk)
  exact Nat.add_le_add_right hmono 1

private theorem oracleCeilBound (n : Nat) :
    ceilBinaryLog n ≤ OracleContract.L n := by
  apply (ceilBinaryLog_le_iff n (OracleContract.L n)).2
  change n ≤ 2 ^ (Nat.log2 (n + 1) + 1)
  have hpow : n + 1 < 2 ^ (Nat.log2 (n + 1) + 1) := by
    first
    | exact Nat.lt_two_pow_succ_log2 (n + 1)
    | exact Nat.lt_two_pow_succ_log2 (by omega : 0 < n + 1)
    | exact?
  omega

section Finish

variable {H : LabelledQuotient} {c : Config H}
variable {rank : Vertex H → Nat} {out : State H}

-- Keep the command, row, and inverse contracts on exactly the input and
-- validity proof passed to StaticGroupedTreeReader.build by buildGrouped.
private def actualFinishDFS (h : OutputOK c rank out) :=
  StaticGroupedTreeReader.finish_dfs (packedInput h) (packedInput_ok h) (by
    have hok := packedInput_ok h
    first
    | exact hok
    | exact?
    | (constructor <;>
        (first | assumption | solve_by_elim | exact? | (intros; grind)))
    | (cases hok <;> constructor <;>
        (first | assumption | solve_by_elim | exact? | (intros; grind)))
    | (rcases hok with ⟨ha, hb, hc⟩; constructor <;>
        (first | assumption | solve_by_elim | exact? | (intros; grind))))

private def actualFinishRows (h : OutputOK c rank out) :=
  StaticGroupedTreeReader.finish_rows (packedInput h) (packedInput_ok h)

private def actualFinishInverse (h : OutputOK c rank out) :=
  StaticGroupedTreeReader.finish_inverse (packedInput h) (packedInput_ok h)

private def proofType {P : Prop} (_ : P) : Prop := P

/-- The public finish contracts specialized to `buildGrouped`'s packed input.
They give the exact DFS command count, the physical row and child scan
lengths, and the inverse scatter, array, and list counts. -/
def ChargedGroupedFinishFacts (h : OutputOK c rank out) : Prop :=
  proofType (actualFinishDFS h) ∧
  proofType (actualFinishRows h) ∧
  proofType (actualFinishInverse h)

theorem chargedGroupedFinishFacts (h : OutputOK c rank out) :
    ChargedGroupedFinishFacts h :=
  ⟨actualFinishDFS h, actualFinishRows h, actualFinishInverse h⟩

-- Select the measured side of each public equality. In particular, this does
-- not reconstruct the inverse scatter or name its private entry-bound proof.
private def measured {a b : Nat} (_ : a = b) : Nat := a
private def expected {a b : Nat} (_ : a = b) : Nat := b

private theorem measured_eq {a b : Nat} (h : a = b) :
    measured h = b := h

/-- The occupied node count of `buildGrouped`'s input, not region capacity. -/
def chargedGroupedNodes (h : OutputOK c rank out) : Nat :=
  expected (actualFinishRows h).1

/-- Charge one unit per processed DFS command and per heavy/range row;
one size read per heavy candidate and two endpoint reads plus one output
record per completed child; one read and one write per inverse scatter,
and one record per inverse list cell. Inverse fill is not charged. -/
def chargedGroupedFinish (h : OutputOK c rank out) : Nat :=
  let hd := actualFinishDFS h
  let hr := actualFinishRows h
  let hi := actualFinishInverse h
  measured hd.2.1 +
    measured hr.1 + measured hr.2.2.1 +
    4 * measured hr.2.1 +
    2 * measured hi.1 + measured hi.2.2.1

theorem chargedGroupedFinish_eq (h : OutputOK c rank out) :
    chargedGroupedFinish h =
      7 * chargedGroupedNodes h + 4 * (chargedGroupedNodes h - 1) := by
  simp only [chargedGroupedFinish, chargedGroupedNodes, measured_eq, expected] <;>
    omega

theorem chargedGroupedFinish_le (h : OutputOK c rank out) :
    chargedGroupedFinish h ≤ 11 * (H.vertexCount + 1) := by
  have hn : chargedGroupedNodes h ≤ H.vertexCount + 1 := by
    dsimp only [chargedGroupedNodes, expected]
    first
    | exact PaperB.EX24.FinalDFS.nodeCount_le h
    | apply PaperB.EX24.FinalDFS.nodeCount_le <;> assumption
    | exact?
  rw [chargedGroupedFinish_eq]
  omega

end Finish

/-- EX2.4 accounting for the exact prepared fast reader. The dictionary trace
is for the installed packed dictionary; the sweep traces end at the fast
reader's own output and log. The finish clause applies to the `buildGrouped`
callback exhibited by the definitional equality, on that callback's own
`packedInput`.

The final inequality sums only the specified charges. It is not a whole-life
time bound: it excludes packed-input extraction, unmetered preprocessing and
sweep work, uncharged allocation/copying, and query processing. -/
theorem runOrderedReaderFast_prepared_chargedSites
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
    (flat : H.IsFlat) :
    let prep := chargedReaderPrep H
    let p := prep.tests
    let c := orderedConfig p large
    let rows := orderedRows p data size_data
    let s := initial c (ConcreteInit.initImage H.vertexCount).1 H.vertexCount
    let L := OracleContract.L H.vertexCount
    let r := runOrderedReaderFast p data size_data rank large increasing covers rankArc flat
    r = runOrderedReaderPacked p data size_data rank large increasing covers rankArc flat
      (fun {c} {out} h => buildGrouped (c := c) (out := out) h)
      (fun {c} {out} h => buildGrouped_eq (c := c) (out := out) h) ∧
    ∃ (q : Nat) (cnt : Count) (w : Work) (qs : List (CutPair H))
        (a d sortCost total : Nat),
      runOrdered p data size_data rank large = some (r.out, r.log) ∧
      PackedReads.packedReadSum c rank s rows = some q ∧
      CountedTrace c rank s rows r.out r.log cnt ∧
      WorkTrace c rank s rows r.out r.log cnt w ∧
      AggregateEX24.Bounds L rows cnt w ∧
      PairLookupTrace c rank s rows r.out r.log cnt w qs ∧
      qs.length = w.requests ∧ prep.visits = H.arcCount ∧
      ResidualUnit.AppendTrace c rank s rows r.out r.log cnt a d ∧
      d = cnt.allocations ∧ a ≤ 14 * d ∧
      ForestDictionary.PackedDictionaryConstructionTrace p orderedPairCode
        (packedOrderedConfig p large).dict sortCost total ∧
      total ≤ 34 * H.vertexCount * (L + 1) ∧
      ((q + pairLookupComparisons c qs + H.arcCount + H.arcCount) +
        ResidualUnit.toll L cnt w a) ≤
        90 * (H.vertexCount + H.arcCount) * L ^ 2 ∧
      ∀ {cfg : Config H} {out : State H} (h : OutputOK cfg rank out),
        ChargedGroupedFinishFacts h ∧
        (((q + pairLookupComparisons c qs + H.arcCount + H.arcCount) +
          ResidualUnit.toll L cnt w a) + total) + chargedGroupedFinish h ≤
          (90 * (H.vertexCount + H.arcCount) * L ^ 2 +
            34 * H.vertexCount * (L + 1)) + 11 * (H.vertexCount + 1) := by
  intro prep p c rows s L r
  obtain ⟨q, cnt, w, qs, a, d, hrun, hread, hcnt, hwork, hbounds,
      hlookup, hlen, hvisits, happend, hd, ha, _, _, hsweep⟩ :=
    runOrderedReaderFast_prepared_fourTolls_residualToll
      data size_data rank large increasing covers rankArc flat
      L (oracleLogBound H.vertexCount)
  obtain ⟨sortCost, total, hdict, htotal⟩ :=
    packedOrderedConfig_dictionary_construction_budget p large L
      (oracleCeilBound H.vertexCount)
  refine ⟨rfl, q, cnt, w, qs, a, d, sortCost, total, hrun, hread, hcnt,
    hwork, hbounds, hlookup, hlen, hvisits, happend, hd, ha, hdict, htotal,
    hsweep, ?_⟩
  intro cfg out h
  exact ⟨chargedGroupedFinishFacts h,
    Nat.add_le_add (Nat.add_le_add hsweep htotal) (chargedGroupedFinish_le h)⟩

end PaperB
