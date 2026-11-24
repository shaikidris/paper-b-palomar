module

public import PaperB.ForestOrderRank
public import PaperB.ForestNumericSweepSpace
public import PaperB.ForestPreparationWork
public import PaperB.ForestInitialCharges
public import PaperB.ForestPackingVisits

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.ForestLayout

variable {N : Nat}

/-- Only the initial root and the commands pushed from child lists schedule
new entries. Each completed exit accounts for one scheduled entry. -/
theorem exit_pending_run (g : ChildLists N) (fuel : Nat) (s : State N)
    (balance : s.exits + s.stack.length = 1 + s.childrenQueued) :
    let r := run g fuel s
    r.exits + r.stack.length = 1 + r.childrenQueued := by
  induction fuel generalizing s with
  | zero => exact balance
  | succ n ih =>
    cases h : s.stack with
    | nil => simpa only [run, h] using balance
    | cons cmd tail =>
      simp only [run, h]
      apply ih
      cases cmd with
      | enter v =>
        obtain ⟨hs, _, _, _, he, hq⟩ := advance_enter_spec g s v tail
        rw [hs, he, hq]
        simp only [List.length_append, List.length_map, List.length_cons] at *
        rw [h, List.length_cons] at balance
        omega
      | exit v =>
        obtain ⟨hs, _, _, _, he, hq⟩ := advance_exit_spec g s v tail
        rw [hs, he, hq]
        rw [h, List.length_cons] at balance
        omega

theorem layout_childrenQueued_le (g : ChildLists N) (root : Fin N) (fuel : Nat) :
    let t := layout g root fuel
    t.stack = [] → t.childrenQueued ≤ fuel := by
  intro t done
  have hbal := exit_pending_run g fuel (initial root) rfl
  have hcount := run_processed_le g fuel (initial root)
  change t.exits + t.stack.length = 1 + t.childrenQueued at hbal
  change t.enters + t.exits ≤ 0 + fuel at hcount
  rw [done, List.length_nil] at hbal
  omega

end PaperB.ForestLayout

namespace PaperB.StaticGroupedTreeReader

open ForestLayout LabelledQuotient
open PackedStaticLayout (Input)

variable {N : Nat}

/-- Selected units of the executable interval finish. Include parent/depth
extraction (two reads, two reserved slots and two output writes per occupied slot), the actual
grouping counters, two endpoint fills, both commands and endpoint writes,
and every child command queued by the layout. -/
def endpointSites (x : Input N) : Nat :=
  let grouped := groupedChildLists x.root x.parent.read
  let s := layout grouped.1 x.root (2 * N)
  let w := grouped.2.grouping
  6 * N + grouped.2.rootFilterVisits +
    (w.initCells + w.scatterReads + w.scatterWrites + w.reverseCells + w.finishRows) +
    2 * N + 2 * s.processed + s.childrenQueued

theorem endpointSites_le (x : Input N)
    (tree : ValidDepthTree x.root x.parent.read x.depth.read) :
    endpointSites x ≤ 20 * N := by
  let g := (groupedChildLists x.root x.parent.read).1
  have hg : g = bucketChildLists x.root x.parent.read :=
    groupedChildLists_eq_bucketChildLists _ _
  have cleared : (layout g x.root (2 * N)).stack = [] := by
    rw [hg]
    exact (layout_bucketChildren_exact tree).1
  have queued := layout_childrenQueued_le g x.root (2 * N) cleared
  have worked := (endpointsOnly_resources x tree).2.2.1
  change (layout g x.root (2 * N)).processed = 2 * N at worked
  unfold endpointSites
  dsimp only
  change 6 * N + (groupedChildLists x.root x.parent.read).2.rootFilterVisits +
    _ + 2 * N + 2 * (layout g x.root (2 * N)).processed +
      (layout g x.root (2 * N)).childrenQueued ≤ 20 * N
  rw [worked, groupedChildLists_work]
  dsimp only
  omega

end PaperB.StaticGroupedTreeReader

namespace PaperB.ForestPreparedBuild

open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.LabelledQuotient PaperB.ForestHead PaperB.Jumps
open PaperB.RetainedProperLoss PaperB.EX24.FinalDFS PaperB.KahnDecreasing
open PaperB.PairLookup AggregateEX24

/-- The concrete preparation passes already enumerated by the work theorem. -/
def incomingSites (H : LabelledQuotient) : Nat :=
  PreparationWorkChecks.preparationSites H (by intro u v; rfl)

theorem incomingSites_le (H : LabelledQuotient) :
    incomingSites H ≤ 16 * (H.vertexCount + H.arcCount) :=
  PreparationWorkChecks.preparation_charge_bound H (by intro u v; rfl)

/-- Root memory and the three initialized sweep columns. Row materialization
charges a read of the order, a read of the test row and one output cell
per vertex. The final term reserves the candidate accumulator backing slots. -/
def initialSites {H : LabelledQuotient} (c : Config H) : Nat :=
  ConcreteInit.initCharge H.vertexCount + c.dict.size +
    (c.region.maxNodes + 1) + H.vertexCount + 3 * H.vertexCount + H.vertexCount

private theorem compact_sites_arithmetic {N E L init dict sweep finish pack : Nat}
    (large : 3 ≤ N) (lpos : 1 ≤ L)
    (hin : init ≤ 12 * N) (hd : dict ≤ 34 * N * (L + 1))
    (hs : sweep ≤ 90 * (N + E) * L ^ 2)
    (hf : finish ≤ 20 * (N + 1)) (hp : pack ≤ 19 * N)
    {prep : Nat} (hprep : prep ≤ 16 * (N + E)) :
    3 * N + prep + init + dict + sweep + finish + pack ≤
      256 * (N + E) * L ^ 2 := by
  let K := (N + E) * L ^ 2
  have hLL : L ≤ L ^ 2 := by
    rw [Nat.pow_succ, Nat.pow_one]
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left L lpos
  have hsK : N + E ≤ K := by
    dsimp [K]
    simpa only [Nat.mul_one] using
      (Nat.mul_le_mul_left (N + E) (by omega : 1 ≤ L ^ 2))
  have hdict : dict ≤ 68 * K := by
    calc
      dict ≤ 34 * N * (L + 1) := hd
      _ ≤ 34 * (N + E) * (2 * L ^ 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
      _ = 34 * (2 * K) := by
        rw [Nat.mul_assoc 34, Nat.mul_left_comm (N + E) 2]
      _ = 68 * K := (Nat.mul_assoc 34 2 K).symm
  have hsweep : sweep ≤ 90 * K := by
    simpa only [K, Nat.mul_assoc] using hs
  have hfinal : 256 * (N + E) * L ^ 2 = 256 * K := by
    simp only [K, Nat.mul_assoc]
  rw [hfinal]
  omega

variable {H : LabelledQuotient} (data : Array (Vertex H))
variable (size_data : data.size = H.vertexCount)
variable (unique : data.toList.Nodup)
variable (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
  orderedVertexAt data size_data i = v)
variable (topo : IsTopologicalOrder data size_data) (flat : H.IsFlat)

/-- Compose the named construction charges with the raw sweep and the
packed result of the dense-order builder. The units are the operations in
the component traces, not an instruction count for the Lean runtime. -/
theorem buildWordsFromOrder_phase_sites (large : 3 ≤ H.vertexCount) :
    let N := H.vertexCount
    let E := H.arcCount
    let L := OracleContract.L N
    let t := orderRanks data unique
    let rank := readRank t
    let p := (ForestIncomingPrep.build H (by intro u v; rfl)).tests
    let c := packedOrderedConfig p large
    let rows := orderedRows p data size_data
    let mem := (ConcreteInit.initImage N).1
    let s := initial c mem N
    ∃ (out : State H) (log : Log H) (ok : OutputOK c rank out)
      (w : WordColumns (OracleContract.wordBits 5 N 0))
      (reads : Nat) (cnt : Count) (work : Work) (keys : List (CutPair H))
      (appendSites installs sortSites dictionarySites : Nat),
      fromRoot c rank mem N rows = some (out, log) ∧
      buildWordsFromOrder data size_data unique covers topo flat = some w ∧
      PackedReads.packedReadSum c rank s rows = some reads ∧
      CountedTrace c rank s rows out log cnt ∧
      WorkTrace c rank s rows out log cnt work ∧
      PairLookupTrace c rank s rows out log cnt work keys ∧
      ResidualUnit.AppendTrace c rank s rows out log cnt appendSites installs ∧
      ForestDictionary.PackedDictionaryConstructionTrace p orderedPairCode
        c.dict sortSites dictionarySites ∧
      w.wordCount ≤ 19 * N ∧
      let scatter := t.ranks.size + t.orderReads + t.indexWrites
      let sweepSites := reads + pairLookupComparisons c keys +
        ResidualUnit.toll L cnt work appendSites
      scatter + incomingSites H + initialSites c + dictionarySites +
        sweepSites + StaticGroupedTreeReader.endpointSites (packedInput ok) +
        w.wordCount ≤ 256 * (N + E) * L ^ 2 := by
  intro N E L t rank p c rows mem s
  let increasing := orderRanks_increasing data size_data unique
  let rankArc := orderRanks_rankArc data size_data unique covers topo
  have proof := runOrderedReaderFast_prepared_chargedSites
    data size_data rank large increasing covers rankArc flat
  dsimp only at proof
  obtain ⟨_, reads, cnt, work, keys, a, d, sw, dw, ran, hreads, hcnt, hwork,
    _, hkeys, _, _, happ, _, _, hdict, hd, hs, _⟩ := proof
  let r := readerForWords data size_data rank increasing covers rankArc flat large
  have hc : c = orderedConfig p large := packedOrderedConfig_eq p large
  have ok : OutputOK c rank r.out := hc.symm ▸ r.index.ok
  let w := packWordColumns r (local_word_columns_fit N)
  have hw : buildWordsFromOrder data size_data unique covers topo flat = some w := by
    rw [buildWordsFromOrder_eq]
    exact buildWords_of_large data size_data rank increasing covers rankArc flat large
  have wrds := buildWordsFromOrder_retained data size_data unique covers topo flat
  rw [hw] at wrds
  have hwSize : w.wordCount ≤ 19 * N := wrds
  have kRun : fromRoot c rank mem N rows = some (r.out, r.log) :=
    (runOrderedPacked_eq p data size_data rank large).trans ran
  refine ⟨r.out, r.log, ok, w, reads, cnt, work, keys, a, d, sw, dw, kRun,
    hw, ?_, ?_, ?_, ?_, ?_, hdict, hwSize, ?_⟩
  · simpa only [s, hc] using hreads
  · change CountedTrace c rank (initial c mem N) rows r.out r.log cnt
    rw [hc]
    exact hcnt
  · change WorkTrace c rank (initial c mem N) rows r.out r.log cnt work
    rw [hc]
    exact hwork
  · change PairLookupTrace c rank (initial c mem N) rows r.out r.log cnt work keys
    rw [hc]
    exact hkeys
  · change ResidualUnit.AppendTrace c rank (initial c mem N) rows r.out r.log cnt a d
    rw [hc]
    exact happ
  · dsimp only
    obtain ⟨nr, rd, wr⟩ := orderRanks_scatter data size_data unique
    change t.ranks.size = N at nr
    change t.orderReads = N at rd
    change t.indexWrites = N at wr
    rw [nr, rd, wr]
    have hcap : c.dict.size ≤ N :=
      (ForestDictionary.packedDictionary_spec p orderedPairCode).2.2
    have capN : c.region.maxNodes = N := rfl
    have hin : initialSites c ≤ 12 * N := by
      unfold initialSites
      rw [allocated_initCharge, capN]
      omega
    have hlookup : pairLookupComparisons c keys =
        pairLookupComparisons (orderedConfig p large) keys := by rw [hc]
    have hsw : reads + pairLookupComparisons c keys + ResidualUnit.toll L cnt work a ≤
        90 * (N + E) * L ^ 2 := by
      rw [hlookup]
      change (reads + pairLookupComparisons (orderedConfig p large) keys + E + E) +
        ResidualUnit.toll L cnt work a ≤ 90 * (N + E) * L ^ 2 at hs
      omega
    have htree : ValidDepthTree (packedInput ok).root (packedInput ok).parent.read
        (packedInput ok).depth.read := by
      have ht := packedInput_ok ok
      first | exact ht | exact ht.tree | exact ht.1 | exact ht.2 | exact?
    have hfinish := Nat.le_trans (StaticGroupedTreeReader.endpointSites_le (packedInput ok) htree)
      (Nat.mul_le_mul_left 20 (nodeCount_le ok))
    rw [show N + N + N = 3 * N by omega]
    exact compact_sites_arithmetic large (OracleContract.one_le_L N) hin hd hsw
      hfinish hwSize (incomingSites_le H)

end PaperB.ForestPreparedBuild
