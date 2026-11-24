module

public import PaperB.PrefixProbe

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.CommonAncestorSearch

open PrefixProbe

universe u

variable {α : Type u} [DecidableEq α]

/-!
`maxDepth` is the largest depth valid for both getters. For a jump forest,
use `min (F.depthOf u) (F.depthOf v)` and pass
`fun d => F.ancestorAtDepth u d` and `fun d => F.ancestorAtDepth v d`.
The correctness theorem requires agreement at depth zero and downward-closed
agreement within the shared depth range.
-/

/-- A real probe evaluates each getter once. The upper sentinel evaluates
neither getter. -/
def depthTest (maxDepth : Nat) (getU getV : Nat → α) (d : Nat) : Bool :=
  if d ≤ maxDepth then
    let u := getU d
    let v := getV d
    decide (u = v)
  else
    false

theorem depthTest_true_iff (maxDepth : Nat) (getU getV : Nat → α) (d : Nat) :
    depthTest maxDepth getU getV d = true ↔
      d ≤ maxDepth ∧ getU d = getV d := by
  by_cases hd : d ≤ maxDepth <;> simp [depthTest, hd]

/-- The deepest agreeing depth and the charged probe count. This uses the
same cutoff engine as `PredecessorSearch.run`, without constructing a list. -/
def run (maxDepth : Nat) (getU getV : Nat → α) : Nat × Nat :=
  searchLog (depthTest maxDepth getU getV) 0 (maxDepth + 1)

/-- The returned depth agrees, and a valid depth agrees exactly when it is
no deeper than the returned depth. -/
theorem run_spec (maxDepth : Nat) (getU getV : Nat → α)
    (hroot : getU 0 = getV 0)
    (hdown : ∀ a b : Nat, a ≤ b → b ≤ maxDepth →
      getU b = getV b → getU a = getV a) :
    let cut := (run maxDepth getU getV).1
    cut ≤ maxDepth ∧ getU cut = getV cut ∧
      ∀ d : Nat, d ≤ maxDepth → (getU d = getV d ↔ d ≤ cut) := by
  have hzero : depthTest maxDepth getU getV 0 = true :=
    (depthTest_true_iff maxDepth getU getV 0).2 ⟨Nat.zero_le _, hroot⟩
  have hend : depthTest maxDepth getU getV (maxDepth + 1) = false := by
    have h : ¬ (maxDepth + 1 ≤ maxDepth) := by omega
    simp [depthTest, h]
  have hmono : ∀ a b : Nat, 0 ≤ a → a ≤ b → b ≤ maxDepth + 1 →
      depthTest maxDepth getU getV b = true →
      depthTest maxDepth getU getV a = true := by
    intro a b _ hab _ hb
    obtain ⟨hbDepth, hbAgree⟩ := (depthTest_true_iff maxDepth getU getV b).1 hb
    exact (depthTest_true_iff maxDepth getU getV a).2
      ⟨Nat.le_trans hab hbDepth, hdown a b hab hbDepth hbAgree⟩
  dsimp only [run]
  obtain ⟨_, _, hcut, _, hclass⟩ :=
    searchLog_spec (depthTest maxDepth getU getV) 0 (maxDepth + 1)
      (by omega) hzero hend hmono
  obtain ⟨hcutDepth, hcutAgree⟩ :=
    (depthTest_true_iff maxDepth getU getV _).1 hcut
  refine ⟨hcutDepth, hcutAgree, ?_⟩
  intro d hd
  have hc := (hclass d (by omega) (by omega)).1
  constructor
  · intro hagree
    exact hc.mp ((depthTest_true_iff maxDepth getU getV d).2 ⟨hd, hagree⟩)
  · intro hle
    exact ((depthTest_true_iff maxDepth getU getV d).1 (hc.mpr hle)).2

theorem run_count_le (maxDepth : Nat) (getU getV : Nat → α) :
    (run maxDepth getU getV).2 ≤ Nat.log2 (maxDepth + 1) + 1 := by
  simpa only [run, Nat.sub_zero] using
    (searchLog_count_le (depthTest maxDepth getU getV) 0 (maxDepth + 1))

/-- Charge two ancestor-at-depth evaluations per search probe. This counts
getter calls, not the work performed inside a getter. -/
def ancestorEvalCharge (maxDepth : Nat) (getU getV : Nat → α) : Nat :=
  2 * (run maxDepth getU getV).2

theorem ancestorEvalCharge_le (maxDepth : Nat) (getU getV : Nat → α) :
    ancestorEvalCharge maxDepth getU getV ≤
      2 * (Nat.log2 (maxDepth + 1) + 1) := by
  unfold ancestorEvalCharge
  exact Nat.mul_le_mul_left 2 (run_count_le maxDepth getU getV)

/-- Return the common ancestor and the search probe count. Materializing
the vertex costs one additional getter call, outside the search charge. -/
def lca (maxDepth : Nat) (getU getV : Nat → α) : α × Nat :=
  let result := run maxDepth getU getV
  (getU result.1, result.2)

theorem lca_spec (maxDepth : Nat) (getU getV : Nat → α)
    (hroot : getU 0 = getV 0)
    (hdown : ∀ a b : Nat, a ≤ b → b ≤ maxDepth →
      getU b = getV b → getU a = getV a) :
    (lca maxDepth getU getV).1 = getV (run maxDepth getU getV).1 ∧
      (lca maxDepth getU getV).2 = (run maxDepth getU getV).2 := by
  have hs := run_spec maxDepth getU getV hroot hdown
  exact ⟨hs.2.1, rfl⟩

end PaperB.CommonAncestorSearch
