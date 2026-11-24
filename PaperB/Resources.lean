module

public import Challenge
public import PaperB.OracleContract
public import PaperB.SealedBuild
public import PaperB.OracleSealedIndexLayout
public import PaperB.RamOracleQuery
public import PaperB.RamPrefixAndForestLoop
public import PaperB.RamExitSummaryBuild
public import PaperB.RamExitFamilyLoopRun
public import PaperB.RamSealedPacker
public import PaperB.RamSealedOracleBuild

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.1–EX5.4 Word-RAM Resource Summary (`PaperB.Resources`):

Collects the exact bit-width, deterministic build, retained storage, and blind
query bounds for `RamSealedOracleBuild.sealedCandidateInterface`, together with
both `CandidateV13` (`O((n+m) L^2)` build, `O(n+m)` peak words, `O(n)` retained
words, `O(L)` query time) and its `CandidateV12` corollary.
-/

namespace PaperB.Resources

open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.RamOracleQuery
open PaperB.RamSealedOracleBuild
open PaperB.RamSealedOracleAssembly
open PaperB.RamExitFamilyLoop (run_exit_family_loop)
open PaperB.RamDagReach

/-- Fixed word slack `oracleWordSlack = 10`, keeping word width `L(n + m) + 10 = Θ(log(n + m + 2))`. -/
theorem oracleWordSlack_val : oracleWordSlack = 10 := rfl

/-- EX5.1 word-width bounds for the sealed oracle layout. -/
theorem wordBits_summary (n m : Nat) :
    L (n + m) ≤ wordBits oracleWordSlack n m ∧
    wordBits oracleWordSlack n m ≤ 11 * L (n + m) :=
  wordBits_bounds oracleWordSlack n m

/-- EX5.2–EX5.4 unified Word-RAM build & index validity summary. -/
theorem build_resources_summary (g : Digraph) (r : Fin g.vertexCount) (acyc : g.IsAcyclic) :
    let n := g.vertexCount
    let m := g.arcCount
    let bits := wordBits oracleWordSlack n m
    let inCap := rawDagInputCap n m
    let workCap := masterWorkCap n m
    let hi := rawDagInputCap_fits n m
    let hw := masterWorkCap_fits n m
    let h32 := master_h32 n m
    let h100 := master_h100 n m
    let L16 := layout16 bits inCap workCap hi hw
    let code := sealedOracleBuildProgram hi hw h32 h100
    let input := rawInputOfDigraph g r hi hw
    ∃ (t : RamProgram.State L16)
      (states : List (RamProgram.State L16))
      (steps totalWords : Nat) (cfg : SealedBuild.SealLayout L16),
      cfg.k = totalWords ∧
      totalWords ≤ retainedLinearFactor * n ∧
      steps ≤ master_buildFuel n m ∧
      RamProgram.run code input steps (SealedBuild.initialState L16) = some ⟨t, steps⟩ ∧
      RamProgram.SuccessfulTrace code input (SealedBuild.initialState L16) states ⟨t, steps⟩ ∧
      RamProgram.tracePeakWords input states = RamProgram.footprint L16 ∧
      ValidSealedOracleIndex g r (SealedBuild.copyPrefix cfg t) ∧
      (SealedBuild.copyPrefix cfg t).size = totalWords := by
  intro n m bits inCap workCap hi hw h32 h100 L16 code input
  obtain ⟨t, states, steps, totalWords, cfg, hk, htot, hsteps, hrun, htr, hpk, _, hval, hsz, _⟩ :=
    run_sealed_oracle_build_of_exit run_exit_family_loop g r acyc
  exact ⟨t, states, steps, totalWords, cfg, hk, htot, hsteps, hrun, htr, hpk, hval, hsz⟩

/-- EX5.3 query-time and fixed scratch-space summary (`32 + 16` extra query words). -/
theorem query_resources_summary
    {bits : Nat} {g : Digraph} (r : Fin g.vertexCount) (acyc : g.IsAcyclic)
    (I : Array (Machine.Word bits)) (hVal : ValidSealedOracleIndex g r I)
    (F : FailureSet g.vertexCount) (t : Fin g.vertexCount) :
    let hI : I.size ≤ 2 ^ bits := Nat.le_of_lt hVal.index_size_lt
    let hWork : queryWorkCap ≤ 2 ^ bits := hVal.work_le
    let hTag : ExitMap.Retention.TagsFit bits := hVal.tags_fit
    let hn : g.vertexCount ≤ 2 ^ bits := hVal.vertexCount_le
    let p := oracleQueryPhase I hI hWork hTag
    let params := SealedQuery.Params.encode hn hTag F t
    ∃ o : SealedQuery.Observation,
      p.observe params (1200 * L g.vertexCount) = some o ∧
      o.operations ≤ 1200 * L g.vertexCount ∧
      o.words = I.size + queryWorkCap + 16 ∧
      (o.answer = true ↔ g.ReachableAvoiding F r t) :=
  oracleQueryProgram_spec r acyc I hVal (Nat.le_of_lt hVal.index_size_lt) hVal.work_le
    hVal.tags_fit hVal.vertexCount_le F t

/-- The online query observer takes only the flat `WordIndex` `I`, `F`, and `t`
and inspects neither `g` nor any adjacency lists. -/
theorem observeQuery_index_only (I : WordIndex) (F : FailureSet I.vertices) (t : Fin I.vertices) :
    sealedCandidateInterface.observeQuery () I F t =
      if h : I.words.size ≤ 2 ^ I.bits ∧ queryWorkCap ≤ 2 ^ I.bits ∧
          2 < 2 ^ I.bits ∧ I.vertices ≤ 2 ^ I.bits then
        ((oracleQueryPhase I.words h.1 h.2.1 h.2.2.1).observe
          (SealedQuery.Params.encode h.2.2.2 h.2.2.1 F t)
          (1200 * L I.vertices)).map
          fun o => ⟨o.answer, o.operations⟩
      else none := rfl

/-- Full EX5.1–EX5.4 Word-RAM `CandidateV13` theorem. -/
theorem sealed_oracle_v13 : CandidateV13 sealedCandidateInterface :=
  sealedCandidate_v13

/-- Cubic Paper B `CandidateV12` corollary via `v13_implies_v12`. -/
theorem sealed_oracle_v12 : CandidateV12 sealedCandidateInterface :=
  v13_implies_v12 sealedCandidateInterface sealedCandidate_v13

end PaperB.Resources
