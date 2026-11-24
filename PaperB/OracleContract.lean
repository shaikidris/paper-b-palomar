module

-- lean-toolchain: leanprover/lean4:v4.35.0-rc3
public import Challenge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! File: PaperB/OracleContract.lean -/
namespace PaperB.OracleContract

private theorem pow_le_next (n k : Nat) :
    L n ^ k ≤ L n ^ (k + 1) := by
  calc
    L n ^ k = L n ^ k * 1 := (Nat.mul_one _).symm
    _ ≤ L n ^ k * L n := Nat.mul_le_mul_left _ (one_le_L n)
    _ = L n ^ (k + 1) := (Nat.pow_succ (L n) k).symm

/-- Relaxing the exponents changes neither the programs nor their observations. -/
theorem v13_implies_v12 {wordSlack : Nat} (M : CandidateInterface wordSlack) :
    CandidateV13 M → CandidateV12 M := by
  intro h
  unfold CandidateV13 Candidate at h
  unfold CandidateV12 Candidate
  rcases h with ⟨build, query, C, hC, h⟩
  refine ⟨build, query, C, hC, ?_⟩
  intro g r hDAG
  rcases h g r hDAG with
    ⟨b, hBuild, hTime, hPeak, hPayload, hRetained, hQuery⟩
  refine ⟨b, hBuild, ?_, hPeak, hPayload, hRetained, ?_⟩
  · exact Nat.le_trans hTime
      (Nat.mul_le_mul_left C
        (Nat.mul_le_mul_left (g.vertexCount + g.arcCount) (pow_le_next g.vertexCount 2)))
  · intro F t
    rcases hQuery F t with ⟨q, hRun, hTimeQuery, hAnswer⟩
    exact ⟨q, hRun, Nat.le_trans hTimeQuery
      (Nat.mul_le_mul_left C
        (Nat.le_trans (pow_le_next g.vertexCount 1) (pow_le_next g.vertexCount 2))),
      hAnswer⟩

end PaperB.OracleContract
