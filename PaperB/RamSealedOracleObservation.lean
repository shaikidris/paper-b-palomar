module

public import PaperB.RamSealedOracleAssembly

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
set_option maxRecDepth 1024

namespace PaperB.RamSealedOracleObservation

open PaperB
open PaperB.RamSealedOracleAssembly
open PaperB.Machine (Word)
open PaperB.RamSealedPacker (oracleHeaderSize_eq hdrTotalWords_eq retainedLinearFactor_eq)
open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.RamProgram.FixedROM
open PaperB.RamProgram
open PaperB.RamDagReach
open PaperB.RamOracleQuery
open PaperB.ExitMap.Retention (TagsFit)


private theorem observeSealedState_of_run {bits : Nat} {L : Layout bits} {code : Program L}
    {input : Input L} {fuel : Nat} {t : State L} {steps : Nat}
    (cfg : SealedBuild.SealLayout L)
    (hRun : run code input fuel (SealedBuild.initialState L) = some ⟨t, steps⟩)
    (hHead : ((t.data[hdrTotalWords]?).map Fin.val).getD 0 = cfg.k) :
    let retained := SealedBuild.copyPrefix cfg t
    observeSealedState code input fuel cfg.registerFits =
      some ⟨retained, steps + L.registerCount + L.workCap + retained.size,
        input.words.size + L.registerCount + L.workCap + retained.size, retained.size⟩ := by
  unfold observeSealedState
  rw [hRun]
  dsimp only
  rw [hHead, dite_eq_left cfg.k_le_workCap]

/-- Executable `SealedBuild.build` observation on `rawInputWords` for any acyclic digraph. -/
def sealedBuildObserve (g : Digraph) (r : Fin g.vertexCount) :
    Option (BuildObservation (wordBits oracleWordSlack g.vertexCount g.arcCount)) :=
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
  let words := rawInputWords bits g r
  let wordsSz := rawInputWords_size bits g r
  let fuel := master_buildFuel n m
  observeSealedState code ⟨words, wordsSz⟩ fuel
    (show L16.registerCount ≤ 2 ^ bits from Nat.le_trans (by decide : 16 ≤ 32) h32)

/-- Query adapter for the flat index and failure slots. -/
def sealedQueryObserve (I : WordIndex) (F : FailureSet I.vertices) (t : Fin I.vertices) :
    Option QueryObservation :=
  if h : I.words.size ≤ 2 ^ I.bits ∧ queryWorkCap ≤ 2 ^ I.bits ∧
      2 < 2 ^ I.bits ∧ I.vertices ≤ 2 ^ I.bits then
    ((oracleQueryPhase I.words h.1 h.2.1 h.2.2.1).observe
      (SealedQuery.Params.encode h.2.2.2 h.2.2.1 F t)
      (1200 * L I.vertices)).map
      fun o => ⟨o.answer, o.operations⟩
  else none

/-- The builder and query observers run the fixed word-RAM programs. -/
def sealedCandidateInterface : CandidateInterface oracleWordSlack where
  BuildProgram := Unit
  QueryProgram := Unit
  observeBuild := fun () g r => sealedBuildObserve g r
  observeQuery := fun () I F t => sealedQueryObserve I F t

/-- The halted builder state and the data needed to observe its sealed index. -/
def HaltedBuild (g : Digraph) (r : Fin g.vertexCount) : Prop :=
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
    ∃ (t : State L16) (steps totalWords : Nat)
      (cfg : SealedBuild.SealLayout L16),
      cfg.k = totalWords ∧
      totalWords ≤ retainedLinearFactor * n ∧
      steps ≤ master_buildFuel n m ∧
      run code input steps (SealedBuild.initialState L16) = some ⟨t, steps⟩ ∧
      t.data.size = workCap ∧
      ValidSealedOracleIndex g r (SealedBuild.copyPrefix cfg t) ∧
      (SealedBuild.copyPrefix cfg t).size = totalWords ∧
      ((SealedBuild.copyPrefix cfg t)[hdrTotalWords]?).map Fin.val = some totalWords

/-- The build observer reports the actual sealed payload and its construction resources. -/
theorem sealedBuildObserve_spec (g : Digraph) (r : Fin g.vertexCount) (hRaw : HaltedBuild g r) :
    ∃ b : BuildObservation (wordBits oracleWordSlack g.vertexCount g.arcCount),
      sealedBuildObserve g r = some b ∧
      b.operations ≤ 300000 * ((g.vertexCount + g.arcCount) * L g.vertexCount ^ 2) ∧
      b.peakLiveWords ≤ 300000 * (g.vertexCount + g.arcCount) ∧
      b.words.size ≤ b.retainedWords ∧
      b.retainedWords ≤ 300000 * g.vertexCount ∧
      ValidSealedOracleIndex g r b.words := by
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
  let words := rawInputWords bits g r
  let wordsSz := rawInputWords_size bits g r
  let fuel := master_buildFuel n m
  obtain ⟨t, steps, totalWords, cfg, hCfgK, hTot128, hStepsLe, hRun, htSz,
      hValid, hCpSz, hCpTot⟩ := hRaw
  have hRunFuel : run code ⟨words, wordsSz⟩ fuel (SealedBuild.initialState L16) = some ⟨t, steps⟩ :=
    run_stable_of_le hStepsLe hRun
  have hKVal : ((t.data[hdrTotalWords]?).map Fin.val).getD 0 = totalWords := by
    have hGet : t.data[hdrTotalWords]? = (SealedBuild.copyPrefix cfg t)[hdrTotalWords]? := by
      have hLtK : hdrTotalWords < cfg.k := by
        have hSzI : (SealedBuild.copyPrefix cfg t).size = totalWords := hCpSz
        obtain ⟨_, _, _, _, _, q, _, _, _, _, _, _, Hdr, _⟩ := hValid
        have hHdrFit := Hdr.hdr_fit
        rw [hSzI, oracleHeaderSize_eq] at hHdrFit
        rw [hCfgK, hdrTotalWords_eq]
        omega
      have hLHS : t.data[hdrTotalWords]? = some (t.data[hdrTotalWords]'(by rw [htSz]; exact Nat.lt_of_lt_of_le hLtK cfg.k_le_workCap)) :=
        Array.getElem?_eq_getElem _
      have hRHS : (SealedBuild.copyPrefix cfg t)[hdrTotalWords]? =
          some ((SealedBuild.copyPrefix cfg t)[hdrTotalWords]'(by rw [SealedBuild.copyPrefix_size]; exact hLtK)) :=
        Array.getElem?_eq_getElem _
      rw [hLHS, hRHS, SealedBuild.copyPrefix_getElem cfg t ⟨hdrTotalWords, hLtK⟩]
    rw [hGet, hCpTot]; rfl
  let retained := SealedBuild.copyPrefix cfg t
  let b : BuildObservation bits :=
    ⟨retained, steps + 16 + workCap + retained.size,
      words.size + 16 + workCap + retained.size, retained.size⟩
  have hRetainedSize : retained.size = totalWords := hCpSz
  have hObserve : sealedBuildObserve g r = some b :=
    observeSealedState_of_run cfg hRunFuel (hKVal.trans hCfgK.symm)
  have hn : 1 ≤ n := Fin.pos r
  have hL1 : 1 ≤ L n := one_le_L n
  have hLSq : 1 ≤ L n ^ 2 := by simpa only [Nat.pow_two] using Nat.mul_le_mul hL1 hL1
  have hSumPos : n + m + 1 ≤ 2 * (n + m) := by omega
  have hPeakBd : b.peakLiveWords ≤ 300000 * (n + m) := by
    change words.size + 16 + workCap + retained.size ≤ 300000 * (n + m)
    rw [wordsSz, hRetainedSize]
    change rawDagInputCap n m + 16 + workCap + totalWords ≤ 300000 * (n + m)
    unfold rawDagInputCap workCap masterWorkCap
    rw [retainedLinearFactor_eq] at hTot128
    omega
  have hOpsBd : b.operations ≤ 300000 * ((n + m) * L n ^ 2) := by
    change steps + 16 + workCap + retained.size ≤ 300000 * ((n + m) * L n ^ 2)
    rw [hRetainedSize]
    have hLin : 16 + workCap + totalWords ≤ 2000 * ((n + m) * L n ^ 2) := by
      unfold workCap masterWorkCap
      rw [retainedLinearFactor_eq] at hTot128
      have hBase : 16 + 800 * (n + m + 1) + totalWords ≤ 2000 * (n + m) := by omega
      calc
        _ ≤ 2000 * (n + m) := hBase
        _ ≤ (2000 * (n + m)) * L n ^ 2 :=
          Nat.le_mul_of_pos_right (2000 * (n + m)) hLSq
        _ = 2000 * ((n + m) * L n ^ 2) := Nat.mul_assoc _ _ _
    have hFuelBd : steps ≤ 280000 * ((n + m) * L n ^ 2) := by
      have hm1 : steps ≤ 140000 * ((n + m + 1) * L n ^ 2) := hStepsLe
      have hm2 : (n + m + 1) * L n ^ 2 ≤ 2 * (n + m) * L n ^ 2 := Nat.mul_le_mul_right _ hSumPos
      have hm3 := Nat.mul_le_mul_left 140000 hm2
      have hAssoc : (2 * (n + m)) * L n ^ 2 = 2 * ((n + m) * L n ^ 2) := Nat.mul_assoc _ _ _
      rw [hAssoc, ← Nat.mul_assoc 140000 2] at hm3
      exact Nat.le_trans hm1 hm3
    have hBudget : 280000 * ((n + m) * L n ^ 2) + 2000 * ((n + m) * L n ^ 2) ≤
        300000 * ((n + m) * L n ^ 2) := by omega
    simpa only [Nat.add_assoc] using Nat.le_trans (Nat.add_le_add hFuelBd hLin) hBudget
  have hRetBound : b.retainedWords ≤ 300000 * g.vertexCount := by
    change retained.size ≤ 300000 * n
    rw [hRetainedSize]
    rw [retainedLinearFactor_eq] at hTot128
    change totalWords ≤ 128 * n at hTot128
    omega
  exact ⟨b, hObserve, hOpsBd, hPeakBd, Nat.le_refl _, hRetBound, hValid⟩

theorem sealedQueryObserve_spec {bits : Nat} {g : Digraph} (r : Fin g.vertexCount)
    (acyc : g.IsAcyclic) (I : Array (Word bits)) (hVal : ValidSealedOracleIndex g r I)
    (F : FailureSet g.vertexCount) (tTgt : Fin g.vertexCount) :
    ∃ o : QueryObservation, sealedQueryObserve ⟨g.vertexCount, bits, I⟩ F tTgt = some o ∧
      o.operations ≤ 1200 * L g.vertexCount ∧
      (o.answer = true ↔ g.ReachableAvoiding F r tTgt) := by
  have hAllQ : I.size ≤ 2 ^ bits ∧ queryWorkCap ≤ 2 ^ bits ∧ 2 < 2 ^ bits ∧ g.vertexCount ≤ 2 ^ bits :=
    ⟨Nat.le_of_lt hVal.index_size_lt, hVal.work_le, hVal.tags_fit, hVal.vertexCount_le⟩
  obtain ⟨qo, hQObs, hQOps, _, hQAns⟩ :=
    oracleQueryProgram_spec r acyc I hVal
      hAllQ.1 hAllQ.2.1 hAllQ.2.2.1 hAllQ.2.2.2 F tTgt
  refine ⟨⟨qo.answer, qo.operations⟩, ?_, hQOps, hQAns⟩
  · unfold sealedQueryObserve
    dsimp only
    rw [dite_eq_left hAllQ]
    change ((oracleQueryPhase I hAllQ.1 hAllQ.2.1 hAllQ.2.2.1).observe
      (SealedQuery.Params.encode hAllQ.2.2.2 hAllQ.2.2.1 F tTgt) (1200 * L g.vertexCount)).map _ = _
    rw [hQObs]
    rfl

/-- The fixed builder and query observer satisfy the v1.3 word-RAM contract. -/
theorem sealedCandidate_v13_of_build
    (hRaw : ∀ (g : Digraph) (r : Fin g.vertexCount), g.IsAcyclic → HaltedBuild g r) :
    CandidateV13 sealedCandidateInterface := by
  refine ⟨(), (), 300000, Nat.succ_pos _, ?_⟩
  intro g r acyc
  obtain ⟨b, hBuild, hOps, hPeak, hRetSize, hRetBound, hVal⟩ :=
    sealedBuildObserve_spec g r (hRaw g r acyc)
  refine ⟨b, hBuild, hOps, hPeak, hRetSize, hRetBound, ?_⟩
  intro F t
  obtain ⟨o, hObs, hOps, hAns⟩ := sealedQueryObserve_spec r acyc b.words hVal F t
  refine ⟨o, hObs, ?_, hAns⟩
  rw [Nat.pow_one]
  exact Nat.le_trans hOps (Nat.mul_le_mul_right (L g.vertexCount) (by decide : 1200 ≤ 300000))

end PaperB.RamSealedOracleObservation
