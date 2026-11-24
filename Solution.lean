module

public import Challenge
public import PaperB.StructuralPaper
public import PaperB.LastExitPaper
public import PaperB.RamForestRawBuild
public import PaperB.Index
public import PaperB.Resources
public import PaperB.BytecodeContract

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
Canonical Theorem 1.1 Entrypoint (`Solution`):

Exposes `PaperB.two_failure_dag_oracle` (`CandidateV13`) and its v1.2 cubic
relaxation `PaperB.two_failure_dag_oracle_v12`, importing the certified
Paper B upstream milestone roots (Items 2.1, 2.2, 3.1, 3.2, 4.1, and 5.1).
-/

namespace PaperB

/-- **Theorem 1.1 (two-failure DAG oracle, v1.3 Word-RAM bounds).**
Fixes one 16-register deterministic Word-RAM builder (`sealedOracleBuildProgram`)
and one 16-register query program (`oracleQueryPhase`) satisfying `CandidateV13`:
`O(log(n + m))` word width (`oracleWordSlack = 10`), `O((n + m) log² n)` build
operations, `O(n + m)` peak construction words, `O(n)` retained index words,
and `O(log n)` query operations answering any two-failure reachability query
`g.ReachableAvoiding F r t` from the sealed `WordIndex` alone. -/
theorem two_failure_dag_oracle :
    OracleContract.CandidateV13 RamSealedOracleBuild.sealedCandidateInterface :=
  Resources.sealed_oracle_v13

/-- **Theorem 1.1 (v1.2 cubic relaxation).**
The exact same Word-RAM build and query programs satisfy `CandidateV12`
(`O((n + m) log³ n)` build operations, `O(log³ n)` query operations). -/
theorem two_failure_dag_oracle_v12 :
    OracleContract.CandidateV12 RamSealedOracleBuild.sealedCandidateInterface :=
  Resources.sealed_oracle_v12

end PaperB
