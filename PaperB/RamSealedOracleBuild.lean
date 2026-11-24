module

public import PaperB.RamSealedOracleObservation
public import PaperB.RamExitFamilyLoopRun

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamSealedOracleBuild

open PaperB.OracleContract
open PaperB.RamSealedOracleAssembly
open PaperB.RamSealedOracleObservation
open PaperB.RamExitFamilyLoop

export PaperB.RamSealedOracleObservation (sealedCandidateInterface)

theorem halted_build (g : Digraph) (r : Fin g.vertexCount) (acyc : g.IsAcyclic) :
    HaltedBuild g r := by
  obtain ⟨t, _, steps, total, cfg, hk, hRetain, hSteps, hRun, _, _, hSz, hVal, hSize, hHdr⟩ :=
    run_sealed_oracle_build_of_exit run_exit_family_loop g r acyc
  exact ⟨t, steps, total, cfg, hk, hRetain, hSteps, hRun, hSz, hVal, hSize, hHdr⟩

theorem sealedCandidate_v13 : CandidateV13 sealedCandidateInterface :=
  sealedCandidate_v13_of_build halted_build

end PaperB.RamSealedOracleBuild
