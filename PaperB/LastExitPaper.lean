module

public import PaperB.LastExitBridge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 2000000

namespace PaperB

open Digraph
open LabelledQuotient

private theorem lastExit_initiallyReachable
    {g : Digraph} {r t : Fin g.vertexCount}
    {F : Fin g.vertexCount → Prop}
    (p : g.SurvivingPath F r t) : g.InitiallyReachable r t :=
  AvoidPath.mono p (fun _ h => False.elim h)

private theorem lastExit_avoid_unreachable
    {g : Digraph} {r f t : Fin g.vertexCount}
    {F : Fin g.vertexCount → Prop}
    (hf : ¬ g.InitiallyReachable r f)
    (p : AvoidPath g.HasArc F r t) :
    AvoidPath g.HasArc (fun x => F x ∨ x = f) r t := by
  have extend {s u : Fin g.vertexCount}
      (q : AvoidPath g.HasArc (fun _ => False) s u) :
      ∀ v, g.HasArc u v → AvoidPath g.HasArc (fun _ => False) s v := by
    induction q with
    | refl w alive =>
        intro v e
        exact .step w v v alive e (.refl v (fun h => h))
    | step w z u alive arc tail ih =>
        intro v e
        exact .step w z v alive arc (ih v e)
  have lift {s u : Fin g.vertexCount} (q : AvoidPath g.HasArc F s u) :
      g.InitiallyReachable r s →
        AvoidPath g.HasArc (fun x => F x ∨ x = f) s u := by
    induction q with
    | refl w alive =>
        intro hrw
        exact .refl w (fun h => h.elim alive (fun hw => hf (hw ▸ hrw)))
    | step w z u alive arc tail ih =>
        intro hrw
        exact .step w z u
          (fun h => h.elim alive (fun hw => hf (hw ▸ hrw)))
          arc (ih (extend hrw z arc))
  exact lift p (.refl r (fun h => h))

private theorem lastExit_drop_unreachable_right
    {g : Digraph} {r a b t : Fin g.vertexCount}
    (hb : ¬ g.InitiallyReachable r b) :
    g.SurvivingPath (fun x => x = a ∨ x = b) r t ↔
      ¬ g.Dominates r a t := by
  change AvoidPath g.HasArc (fun x => x = a ∨ x = b) r t ↔
    ¬ ¬ AvoidPath g.HasArc (fun x => x = a) r t
  constructor
  · intro p hn
    exact hn (AvoidPath.mono p (fun _ h => Or.inl h))
  · intro hp
    exact lastExit_avoid_unreachable hb (Classical.byContradiction hp)

section

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)
variable (hd : g.InitiallyReachable r d)

local notation "S" => (siblingBlockSystem progress injective spec hd)
local notation "Q" => (finiteSiblingQuotient progress injective spec hd)
local notation "SV" => (SiblingVertex g r d)
local notation "Key" => (SiblingBlockKey g r d parent)
local notation "enc" => (encodeSiblingBlockKey g r d parent)
local notation "dec" => (decodeSiblingBlockKey g r d parent)
local notation "blk" => (S).block
local notation "ix" => (fun z : SV => enc (blk z))

/-- The Lemma 2.2 branches, with `A` and `C` in the endpoint order of `B`. -/
def LastExitTestBranches
    (B : CutPair Q) (A C : SV) (F : Fin g.vertexCount → Prop) : Prop :=
  (∀ t : Fin g.vertexCount, g.InitiallyReachable r t →
    ¬ Ancestor parent d t → g.SurvivingPath F r t) ∧
  g.SurvivingPath F r d ∧
  (∀ t : SV, blk t = blk A →
    (g.SurvivingPath F r t.val ↔ ¬ g.Dominates r A.val t.val)) ∧
  (∀ t : SV, blk t = blk C →
    (g.SurvivingPath F r t.val ↔ ¬ g.Dominates r C.val t.val)) ∧
  (∀ t : SV, blk t ≠ blk A → blk t ≠ blk C →
    (g.SurvivingPath F r t.val ↔
      (AvoidPath (Q).HasQuotientArc B.Mem (Q).root (ix t) ∨
        ∃ (s : Fin (Q).vertexCount) (x : Fin g.vertexCount),
          B.Mem s ∧ g.SurvivingPath F r x ∧
            (Q).ExitTailMem B s (ix t) x)) ∧
    (AvoidPath (Q).HasQuotientArc B.Mem (Q).root (ix t) →
      g.SurvivingPath F r t.val) ∧
    ((Q).ProperLoss B (ix t) →
      let xs := lemma22ExitTails Q B B.fst (ix t)
      let ys := lemma22ExitTails Q B B.snd (ix t)
      xs ≠ [] ∧ ys ≠ [] ∧
        ∃ l₁ l₂ : Fin g.vertexCount,
          (g.IsDominatorLCA r xs l₁ ∧
            ∀ m, g.IsDominatorLCA r xs m → m = l₁) ∧
          (g.IsDominatorLCA r ys l₂ ∧
            ∀ m, g.IsDominatorLCA r ys m → m = l₂) ∧
          (∀ f, (¬ g.CommonDominator r xs f) ↔ ¬ g.Dominates r f l₁) ∧
          (∀ f, (¬ g.CommonDominator r ys f) ↔ ¬ g.Dominates r f l₂) ∧
          (g.SurvivingPath F r t.val ↔
            (¬ g.Dominates r A.val l₁) ∨ (¬ g.Dominates r C.val l₂)) ∧
          ((¬ g.SurvivingPath F r t.val) ↔
            g.Dominates r A.val l₁ ∧ g.Dominates r C.val l₂)))

theorem lemma22_last_exit_ordered_branches
    (B : CutPair Q) (a b : SV)
    (hab : ¬ Ancestor parent a.val b.val)
    (hba : ¬ Ancestor parent b.val a.val)
    (hlca : ∀ c,
      (g.Dominates r c a.val ∧ g.Dominates r c b.val) ↔
        g.Dominates r c d)
    (hfst : B.fst = ix a) (hsnd : B.snd = ix b)
    (acyclic : (Q).IsAcyclic) (flat : (Q).IsFlat) :
    LastExitTestBranches progress injective spec hd B a b
      (fun x => x = a.val ∨ x = b.val) := by
  have haReach : g.InitiallyReachable r a.val := by
    first | exact a.property.1 | exact a.property.2
  have hbReach : g.InitiallyReachable r b.val := by
    first | exact b.property.1 | exact b.property.2
  obtain ⟨A, C, hA, hC, hdReach, hda, hdb, hdaNe, hdbNe, hu, hv, huv⟩ :=
    PaperB.Digraph.lemma22_incomparable_below_lca
      progress injective spec haReach hbReach hab hba hlca
  have eA : A = a := Subtype.ext hA
  have eC : C = b := Subtype.ext hC
  subst A
  subst C
  have haNe : a.val ≠ d := Ne.symm hdaNe
  have hbNe : b.val ≠ d := Ne.symm hdbNe
  have hB (i : Fin (Q).vertexCount) :
      B.Mem i ↔ i = ix a ∨ i = ix b := by
    simp [CutPair.Mem, hfst, hsnd]

  unfold LastExitTestBranches
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht hout
    exact lemma22_outside progress spec haReach hbReach ht hda hdb hout
  · exact lemma22_at_d progress spec hdReach haReach hbReach
      hda hdb hdaNe hdbNe
  · intro t ht
    exact lemma22_own progress injective spec hdReach
      (blk a) (blk b) hu hv huv a b t rfl rfl ht
  · intro t ht
    exact lemma22_own_right progress injective spec hdReach
      (blk a) (blk b) hu hv huv a b t rfl rfl ht
  · intro t ht₁ ht₂
    have exits :
        g.SurvivingPath (fun x => x = a.val ∨ x = b.val) r t.val ↔
          (AvoidPath (Q).HasQuotientArc B.Mem (Q).root (ix t) ∨
            ∃ (s : Fin (Q).vertexCount) (x : Fin g.vertexCount),
              B.Mem s ∧
                g.SurvivingPath (fun y => y = a.val ∨ y = b.val) r x ∧
                (Q).ExitTailMem B s (ix t) x) := by
      first
      | apply lemma22_third_survivingPath_iff_exitTailMem <;> assumption
      | apply lemma22_third_survivingPath_iff_exitTailMem <;>
          solve_by_elim [Ne.symm]
    refine ⟨exits, fun clean => exits.mpr (Or.inl clean), ?_⟩
    intro proper
    first
    | apply lemma22_third_properLoss_decomposition <;> assumption
    | apply lemma22_third_properLoss_decomposition <;>
        solve_by_elim [Ne.symm]

private theorem lastExit_below
    {a b : Fin g.vertexCount} (A C : SV)
    (hA : A.val = a) (hC : C.val = b)
    (hab : ¬ Ancestor parent a b) (hba : ¬ Ancestor parent b a)
    (hlca : ∀ c, (g.Dominates r c a ∧ g.Dominates r c b) ↔
      g.Dominates r c d)
    (hu : (blk A).val ≠ d) (hv : (blk C).val ≠ d)
    (huv : blk A ≠ blk C) :
    ∃ (X Y : SV) (B : CutPair Q),
      ((X.val = a ∧ Y.val = b) ∨ (X.val = b ∧ Y.val = a)) ∧
      B.fst = ix X ∧ B.snd = ix Y ∧
      LastExitTestBranches progress injective spec hd B X Y
        (fun x => x = a ∨ x = b) := by
  classical
  have hdec (k : Key) : dec (enc k) = k :=
    decodeSiblingBlockKey_encodeSiblingBlockKey g r d parent k
  have hroot : dec (Q).root = SiblingBlockKey.root g r d parent := by
    change decodeSiblingBlockKey g r d parent
      (encodeSiblingBlockKey g r d parent _) = SiblingBlockKey.root g r d parent
    rw [decodeSiblingBlockKey_encodeSiblingBlockKey] <;>
      exact siblingBlockOf_leader progress injective spec hd
        (SiblingBlockKey.root g r d parent)
  have neRoot (Z : SV) (hz : (blk Z).val ≠ d) : ix Z ≠ (Q).root := by
    intro he
    have hk : blk Z = SiblingBlockKey.root g r d parent :=
      (hdec (blk Z)).symm.trans ((congrArg dec he).trans hroot)
    exact hz (congrArg (fun k : Key => k.val) hk)
  have hi : ix A ≠ (Q).root := neRoot A hu
  have hj : ix C ≠ (Q).root := neRoot C hv
  have hij : ix A ≠ ix C := by
    intro he
    exact huv ((hdec (blk A)).symm.trans
      ((congrArg dec he).trans (hdec (blk C))))
  have hCut :
      ∃ B : CutPair Q,
        (B.fst = ix A ∧ B.snd = ix C) ∨
        (B.fst = ix C ∧ B.snd = ix A) := by
    let B : CutPair Q :=
      { fst := ix A
        snd := ix C
        fst_ne_root := hi
        snd_ne_root := hj
        ne := hij }
    exact ⟨B, Or.inl ⟨rfl, rfl⟩⟩

  let qr := finiteSiblingRank progress injective spec hd
  have hqr {i j : Fin (Q).vertexCount} (e : (Q).HasQuotientArc i j) :
      qr i < qr j :=
    finiteSiblingRank_lt_of_hasQuotientArc progress injective spec hd e
  have path_le {F : Fin (Q).vertexCount → Prop} {i j : Fin (Q).vertexCount}
      (p : AvoidPath (Q).HasQuotientArc F i j) : qr i ≤ qr j := by
    induction p with
    | refl u alive => exact Nat.le_refl _
    | step u w v alive arc tail ih =>
        exact Nat.le_trans (Nat.le_of_lt (hqr arc)) ih
  have acyclic : (Q).IsAcyclic := by
    first
    | exact finiteSiblingQuotient_isAcyclic progress injective spec hd
    | exact ⟨qr, fun _ _ e => hqr e⟩
    | intro i j e p
      exact (Nat.not_lt_of_ge (path_le p)) (hqr e)
    | intro i j p e
      exact (Nat.not_lt_of_ge (path_le p)) (hqr e)
    | exact?
  have flat : (Q).IsFlat :=
    finiteSiblingQuotient_isFlat progress injective spec hd

  have branches (B : CutPair Q) (X Y : SV)
      (hXY : (X.val = a ∧ Y.val = b) ∨ (X.val = b ∧ Y.val = a))
      (hfst : B.fst = ix X) (hsnd : B.snd = ix Y) :
      LastExitTestBranches progress injective spec hd B X Y
        (fun x => x = a ∨ x = b) := by
    have hxy : ¬ Ancestor parent X.val Y.val := by
      rcases hXY with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · simpa only [hx, hy] using hab
      · simpa only [hx, hy] using hba
    have hyx : ¬ Ancestor parent Y.val X.val := by
      rcases hXY with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · simpa only [hx, hy] using hba
      · simpa only [hx, hy] using hab
    have hL : ∀ c, (g.Dominates r c X.val ∧ g.Dominates r c Y.val) ↔
        g.Dominates r c d := by
      intro c
      rcases hXY with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · simpa only [hx, hy] using hlca c
      · rw [hx, hy, and_comm]
        exact hlca c
    have hF : (fun x : Fin g.vertexCount => x = a ∨ x = b) =
        (fun x => x = X.val ∨ x = Y.val) := by
      funext x
      apply propext
      rcases hXY with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · rw [hx, hy]
      · rw [hx, hy]
        exact or_comm
    rw [hF]
    exact lemma22_last_exit_ordered_branches progress injective spec hd
      B X Y hxy hyx hL hfst hsnd acyclic flat

  obtain ⟨B, hB⟩ := hCut
  rcases hB with ⟨hfst, hsnd⟩ | ⟨hfst, hsnd⟩
  · exact ⟨A, C, B, Or.inl ⟨hA, hC⟩, hfst, hsnd,
      branches B A C (Or.inl ⟨hA, hC⟩) hfst hsnd⟩
  · exact ⟨C, A, B, Or.inr ⟨hC, hA⟩, hfst, hsnd,
      branches B C A (Or.inr ⟨hC, hA⟩) hfst hsnd⟩

end

/-- Lemma 2.2 for incomparable failures in either order. Initially unreachable
failures are inert. When both failures are initially reachable, the quotient
branches use the ordinary dominator LCA and the canonical ordered cut pair. -/
theorem last_exit_test
    {g : Digraph} {r a b : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (g_acyclic : g.IsAcyclic)
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent)
    (hab : ¬ Ancestor parent a b) (hba : ¬ Ancestor parent b a) :
    let F := fun x : Fin g.vertexCount => x = a ∨ x = b
    (∀ t, g.SurvivingPath F r t → g.InitiallyReachable r t) ∧
    (¬ g.InitiallyReachable r b → ∀ t,
      g.SurvivingPath F r t ↔ ¬ g.Dominates r a t) ∧
    (¬ g.InitiallyReachable r a → ∀ t,
      g.SurvivingPath F r t ↔ ¬ g.Dominates r b t) ∧
    (¬ g.InitiallyReachable r a → ¬ g.InitiallyReachable r b → ∀ t,
      g.SurvivingPath F r t ↔ g.InitiallyReachable r t) ∧
    (g.InitiallyReachable r a → g.InitiallyReachable r b →
      ∃ (d : Fin g.vertexCount) (hd : g.InitiallyReachable r d),
        (∀ c, (g.Dominates r c a ∧ g.Dominates r c b) ↔
          g.Dominates r c d) ∧
        let Q := finiteSiblingQuotient progress injective spec hd
        let S := siblingBlockSystem progress injective spec hd
        let ix := fun z : SiblingVertex g r d =>
          encodeSiblingBlockKey g r d parent (S.block z)
        ∃ (A C : SiblingVertex g r d) (B : CutPair Q),
          ((A.val = a ∧ C.val = b) ∨ (A.val = b ∧ C.val = a)) ∧
          B.fst = ix A ∧ B.snd = ix C ∧
          LastExitTestBranches progress injective spec hd B A C F) := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t p
    exact lastExit_initiallyReachable p
  · intro hb t
    exact lastExit_drop_unreachable_right hb
  · intro ha t
    exact (lemma22_swap_pair_failures
      (g := g) (r := r) (a := a) (b := b) (t := t)).trans
      (lastExit_drop_unreachable_right ha)
  · intro ha hb t
    refine ⟨lastExit_initiallyReachable, ?_⟩
    intro ht
    have p := lastExit_avoid_unreachable (F := fun _ => False) ha ht
    have q := lastExit_avoid_unreachable hb p
    exact AvoidPath.mono q
      (fun _ h => h.elim (fun ha' => Or.inl (Or.inr ha')) Or.inr)
  · intro ha hb
    have pairCommon (c : Fin g.vertexCount) :
        g.CommonDominator r [a, b] c ↔
          g.Dominates r c a ∧ g.Dominates r c b := by
      constructor
      · intro h
        exact ⟨h a (by simp), h b (by simp)⟩
      · rintro ⟨h₁, h₂⟩ x hx
        simp at hx
        rcases hx with hx | hx <;> subst x <;> assumption
    obtain ⟨d, hPair⟩ := exists_unique_pair_dominatorLCA g_acyclic ha hb
    have hlca : ∀ c, (g.Dominates r c a ∧ g.Dominates r c b) ↔
        g.Dominates r c d := by
      first
      | exact hPair.1
      | exact hPair.2.1
      | exact hPair
      | intro c
        exact (pairCommon c).symm.trans
          (IsDominatorLCA.all_dominates_iff (d := c) hPair.1)
      | intro c
        exact (pairCommon c).symm.trans
          (IsDominatorLCA.all_dominates_iff (d := c) hPair.2.1)
    obtain ⟨A, C, hA, hC, hd, hda, hdb, hdaNe, hdbNe, hu, hv, huv⟩ :=
      PaperB.Digraph.lemma22_incomparable_below_lca
        progress injective spec ha hb hab hba hlca
    exact ⟨d, hd, hlca,
      lastExit_below progress injective spec hd A C hA hC hab hba hlca hu hv huv⟩

end PaperB
