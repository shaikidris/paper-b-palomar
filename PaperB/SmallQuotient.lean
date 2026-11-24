module

public import PaperB.Forest

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

-- Add after the buildProperLossForest invariants.
open PaperB PaperB.LabelledQuotient

namespace PaperB.SmallQuotient

theorem cutPair_impossible_of_small {H : LabelledQuotient}
    (h : H.vertexCount ≤ 2) (B : CutPair H) : False := by
  have hf := B.fst.isLt
  have hs := B.snd.isLt
  have hr := H.root.isLt
  have hfr : B.fst.val ≠ H.root.val :=
    fun e => B.fst_ne_root (Fin.ext e)
  have hsr : B.snd.val ≠ H.root.val :=
    fun e => B.snd_ne_root (Fin.ext e)
  have hfs : B.fst.val ≠ B.snd.val :=
    fun e => B.ne (Fin.ext e)
  have ff : B.fst.val = 0 ∨ B.fst.val = 1 := by omega
  have ss : B.snd.val = 0 ∨ B.snd.val = 1 := by omega
  have rr : H.root.val = 0 ∨ H.root.val = 1 := by omega
  rcases ff with f | f <;> rcases ss with s | s <;>
    rcases rr with r | r <;> omega

theorem computed_realKeys_nil_of_small (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) (h : H.vertexCount ≤ 2) :
    (buildProperLossForest H rank).realKeys = [] := by
  cases hk : (buildProperLossForest H rank).realKeys with
  | nil => rfl
  | cons B Bs => exact (cutPair_impossible_of_small h B).elim

theorem computed_node_eq_root_of_small (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) (h : H.vertexCount ≤ 2)
    (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)) :
    u = (buildProperLossForest H rank).rootNode := by
  apply Fin.ext
  change u.val = 0
  have hu := u.isLt
  change u.val < (buildProperLossForest H rank).realKeys.length + 1 at hu
  rw [computed_realKeys_nil_of_small H rank h] at hu
  change u.val < 1 at hu
  omega

theorem computed_label_eq_root_of_small (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) (h : H.vertexCount ≤ 2)
    (v : Fin H.vertexCount) :
    (buildProperLossForest H rank).label v =
      (buildProperLossForest H rank).rootNode :=
  computed_node_eq_root_of_small H rank h ((buildProperLossForest H rank).label v)

theorem computed_nodeKey_none_of_small (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) (h : H.vertexCount ≤ 2)
    (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)) :
    (buildProperLossForest H rank).nodeKey? u = none := by
  rw [computed_node_eq_root_of_small H rank h u,
    buildProperLossForest_nodeKey?_root]

def smallRootOnlyForest (H : LabelledQuotient) : ProperLossForest H where
  realKeys := []
  parent := fun _ => ⟨0, by
    change 0 < ([] : List (CutPair H)).length + 1
    exact Nat.zero_lt_succ 0⟩
  depth := fun _ => 0
  label := fun _ => ⟨0, by
    change 0 < ([] : List (CutPair H)).length + 1
    exact Nat.zero_lt_succ 0⟩

private theorem smallBranch_finOne_eq_zero (u : Fin 1) :
    u = (⟨0, by decide⟩ : Fin 1) := by
  apply Fin.ext
  change u.val = 0
  have hu := u.isLt
  omega

private theorem eq_smallRootOnlyForest {H : LabelledQuotient}
    (F : ProperLossForest H) (hk : F.realKeys = [])
    (hd : F.depth F.rootNode = 0) : F = smallRootOnlyForest H := by
  cases F with
  | mk keys parent depth label =>
    change keys = [] at hk
    subst keys
    have hp : parent = (fun _ : Fin 1 => (⟨0, by decide⟩ : Fin 1)) :=
      funext fun u => smallBranch_finOne_eq_zero (parent u)
    have hdepth : depth = (fun _ : Fin 1 => 0) := by
      funext u
      exact (congrArg depth (smallBranch_finOne_eq_zero u)).trans hd
    have hl : label = (fun _ : Fin H.vertexCount => (⟨0, by decide⟩ : Fin 1)) :=
      funext fun v => smallBranch_finOne_eq_zero (label v)
    rw [hp, hdepth, hl] <;> rfl

def buildProperLossForestSmallExact (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) : ProperLossForest H :=
  if H.vertexCount ≤ 2 then smallRootOnlyForest H
  else buildProperLossForest H rank

theorem buildProperLossForestSmallExact_eq (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) :
    buildProperLossForestSmallExact H rank = buildProperLossForest H rank := by
  unfold buildProperLossForestSmallExact
  by_cases h : H.vertexCount ≤ 2
  · rw [if_pos h]
    exact (eq_smallRootOnlyForest (buildProperLossForest H rank)
      (computed_realKeys_nil_of_small H rank h)
      (buildProperLossForest_depth_root H rank)).symm
  · rw [if_neg h]

-- Two index comparisons at most; all bounds and distinctness proofs are erased.
def sentinelDefaultCutPair (H : LabelledQuotient)
    (h : 3 ≤ H.vertexCount) : CutPair H :=
  let i0 : Fin H.vertexCount := ⟨0, by omega⟩
  let i1 : Fin H.vertexCount := ⟨1, by omega⟩
  let i2 : Fin H.vertexCount := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro e
    have hv := congrArg Fin.val e
    change (0 : Nat) = 1 at hv
    omega
  have h02 : i0 ≠ i2 := by
    intro e
    have hv := congrArg Fin.val e
    change (0 : Nat) = 2 at hv
    omega
  have h12 : i1 ≠ i2 := by
    intro e
    have hv := congrArg Fin.val e
    change (1 : Nat) = 2 at hv
    omega
  if h0 : i0 = H.root then
    ⟨i1, i2, fun e => h01 (h0.trans e.symm),
      fun e => h02 (h0.trans e.symm), h12⟩
  else if h1 : i1 = H.root then
    ⟨i0, i2, h0, fun e => h12 (h1.trans e.symm), h02⟩
  else
    ⟨i0, i1, h0, h1, h01⟩

inductive SmallExactKeyRead (H : LabelledQuotient) where
  | noKey
  | real (key : CutPair H)
  | sentinel (padding : CutPair H)

def SmallExactKeyRead.effective? {H : LabelledQuotient} :
    SmallExactKeyRead H → Option (CutPair H)
  | .noKey => none
  | .real B => some B
  | .sentinel _ => none

def readComputedKeySmallExact (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat)
    (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)) :
    SmallExactKeyRead H :=
  if h : H.vertexCount ≤ 2 then
    .noKey
  else
    match (buildProperLossForest H rank).nodeKey? u with
    | some B => .real B
    | none => .sentinel (sentinelDefaultCutPair H (by omega))

-- The effective result is exactly the original lookup. Even if the padding
-- equals a real key by value, the sentinel read never supplies an effective key.
theorem readComputedKeySmallExact_effective (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat)
    (u : Fin ((buildProperLossForest H rank).realNodeCount + 1)) :
    (readComputedKeySmallExact H rank u).effective? =
      (buildProperLossForest H rank).nodeKey? u := by
  by_cases h : H.vertexCount ≤ 2
  · simp only [readComputedKeySmallExact, dif_pos h, SmallExactKeyRead.effective?,
      computed_nodeKey_none_of_small H rank h u]
  · cases hk : (buildProperLossForest H rank).nodeKey? u <;>
      simp only [readComputedKeySmallExact, dif_neg h, hk,
        SmallExactKeyRead.effective?]

theorem readComputedKeySmallExact_root_of_large (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat) (h : 3 ≤ H.vertexCount) :
    readComputedKeySmallExact H rank (buildProperLossForest H rank).rootNode =
      .sentinel (sentinelDefaultCutPair H h) := by
  have hn : ¬ H.vertexCount ≤ 2 := by omega
  simp only [readComputedKeySmallExact, dif_neg hn, buildProperLossForest_nodeKey?_root]

theorem readComputedKeySmallExact_sentinel_only_root (H : LabelledQuotient)
    (rank : Fin H.vertexCount → Nat)
    {u : Fin ((buildProperLossForest H rank).realNodeCount + 1)} {B : CutPair H}
    (h : readComputedKeySmallExact H rank u = .sentinel B) :
    u = (buildProperLossForest H rank).rootNode := by
  have hk : (buildProperLossForest H rank).nodeKey? u = none := by
    exact (readComputedKeySmallExact_effective H rank u).symm.trans
      (congrArg (SmallExactKeyRead.effective? (H := H)) h)
  exact buildProperLossForest_nodeKey?_inj H rank
    (hk.trans (buildProperLossForest_nodeKey?_root H rank).symm)

end PaperB.SmallQuotient
