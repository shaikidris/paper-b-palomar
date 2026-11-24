module

public import PaperB.RamSealedOracleBuild

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option warningAsError true

/-! The oracle as one pair of bytecode generators for the declared RAM layouts. -/

namespace PaperB.BytecodeContract

open PaperB.Machine (Word)
open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.RamProgram
open PaperB.RamDagReach
open PaperB.RamOracleQuery (oracleQueryProgram)
open PaperB.RamSealedOracleAssembly

def paperBuilder : BuildCode := fun n m =>
  sealedOracleBuildProgram (rawDagInputCap_fits n m) (masterWorkCap_fits n m)
    (master_h32 n m) (master_h100 n m)

def paperQuery : QueryCode := fun _ _ hI hWork hTag => oracleQueryProgram hI hWork hTag

theorem executeBuilder_paper (g : Digraph) (r : Fin g.vertexCount) :
    executeBuilder paperBuilder g r = RamSealedOracleObservation.sealedBuildObserve g r := by
  rfl

theorem executeQuery_paper (I : WordIndex) (F : FailureSet I.vertices) (t : Fin I.vertices) :
    executeQuery paperQuery I F t = RamSealedOracleObservation.sealedQueryObserve I F t := by
  rfl

/-- Theorem 1.1. For a DAG with `n` vertices and `m` arc occurrences, fix
one builder code generator and one query code generator. Let `L` be
the ceiling of `log₂(n + 2)`. The builder takes `O((n + m)L²)` word operations,
uses `O(n + m)` peak words, and retains `O(n)` words. Using only this retained
index, a query takes `O(L)` operations and decides whether the original
target is reachable from the source after deleting the listed zero, one, or
two vertices. The builder runs before the failure set and target are named. -/
theorem twoFailureOracleBytecode :
    ∃ (build : BuildCode) (query : QueryCode), CandidateV13 (fixedInterface build query) :=
  ⟨paperBuilder, paperQuery, PaperB.RamSealedOracleBuild.sealedCandidate_v13⟩

end PaperB.BytecodeContract
