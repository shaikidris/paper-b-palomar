module

public import PaperB.Spec

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Exit-transfer steps on a supplied labelled graph, with the required surviving paths explicit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB

namespace LabelledQuotient

/-- Generic fresh-endpoint exit transfer (core composition step in Theorem 4.1):
    if original physical tail `x` witnesses an exit from `s` to an intermediate
    endpoint `p` in `H - B`, and `p` has an actual surviving path onwards to `y`
    avoiding the parent pair `B`, then the same tail `x` witnesses `x ∈ X^B_s(y)`. -/
theorem exitTailMem_transfer_of_onwardPath
    {H : LabelledQuotient} {B : CutPair H}
    {s p y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hExitToFresh : H.ExitTailMem B s p x)
    (hOnward : H.SurvivingPath B.Mem p y) :
    H.ExitTailMem B s y x := by
  let ⟨e, he, hTail, hToFresh⟩ := hExitToFresh
  exact ⟨e, he, hTail, AvoidPath.trans hToFresh hOnward⟩

/-- Inherited-continuation lemma (Theorem 4.1, shared-endpoint case):
    when `s ∈ P`, `y` is lost under `P`, and every vertex in `B \ {s}` remains
    reachable from `H.root` in `H - P`, any continuation in `H - P` to `y`
    also avoids all of `B`. -/
theorem suffix_avoids_parent_of_shared
    {H : LabelledQuotient} {B P : CutPair H}
    {s w y : Fin H.vertexCount}
    (hsP : P.Mem s)
    (hLostP : H.Lost P y)
    (hReachOther : ∀ v : Fin H.vertexCount, B.Mem v → v ≠ s →
      H.SurvivingPath P.Mem H.root v)
    (hCont : H.SurvivingPath P.Mem w y) :
    H.SurvivingPath B.Mem w y := by
  revert hLostP
  induction hCont with
  | refl z aliveP =>
      intro hLostP
      refine AvoidPath.refl z (fun hzB => ?_)
      have hz_ne_s : z ≠ s := fun hEq => aliveP (by rw [hEq]; exact hsP)
      exact hLostP (hReachOther z hzB hz_ne_s)
  | step z next tgt aliveP arc rest ih =>
      intro hLostP
      refine AvoidPath.step z next tgt (fun hzB => ?_) arc (ih hLostP)
      have hz_ne_s : z ≠ s := fun hEq => aliveP (by rw [hEq]; exact hsP)
      have hPref : H.SurvivingPath P.Mem H.root z := hReachOther z hzB hz_ne_s
      exact hLostP (AvoidPath.trans hPref (AvoidPath.step z next tgt aliveP arc rest))

/-- Inherited exit-tail inclusion `X^P_s(y) ⊆ X^B_s(y)` when `s ∈ B ∩ P`. -/
theorem exitTailMem_transfer_inherited
    {H : LabelledQuotient} {B P : CutPair H}
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hsP : P.Mem s)
    (hLostP : H.Lost P y)
    (hReachOther : ∀ v : Fin H.vertexCount, B.Mem v → v ≠ s →
      H.SurvivingPath P.Mem H.root v)
    (hExitChild : H.ExitTailMem P s y x) :
    H.ExitTailMem B s y x := by
  let ⟨e, he, hTail, hCont⟩ := hExitChild
  exact ⟨e, he, hTail, suffix_avoids_parent_of_shared hsP hLostP hReachOther hCont⟩

/-- Converse path-splitting lemma for Theorem 4.1:
    any path in `H - B` to `y ∉ P` either visits a fresh endpoint `p ∈ P \ B`
    along a prefix in `H - B`, or avoids `P` altogether. -/
theorem split_at_fresh_or_avoid_child
    {H : LabelledQuotient} {B P : CutPair H}
    {w y : Fin H.vertexCount}
    (hPath : H.SurvivingPath B.Mem w y)
    (hyNotP : ¬ P.Mem y) :
    (∃ p : Fin H.vertexCount, IsFreshEndpoint B P p ∧ H.SurvivingPath B.Mem w p) ∨
      H.SurvivingPath P.Mem w y := by
  revert hyNotP
  induction hPath with
  | refl z _ =>
      intro hzNotP
      exact Or.inr (AvoidPath.refl z hzNotP)
  | step z next tgt aliveB arc _ ih =>
      intro hTgtNotP
      if hzP : P.Mem z then
        exact Or.inl ⟨z, ⟨hzP, aliveB⟩, AvoidPath.refl z aliveB⟩
      else
        cases ih hTgtNotP with
        | inl hFresh =>
            let ⟨p, hpFresh, hToP⟩ := hFresh
            exact Or.inl ⟨p, hpFresh, AvoidPath.step z next p aliveB arc hToP⟩
        | inr hAvoidP =>
            exact Or.inr (AvoidPath.step z next tgt hzP arc hAvoidP)

/-- Converse exit-tail decomposition for Theorem 4.1:
    when `y ∈ J(P)` and `s ∉ P → H.root` reaches `s` in `H - P`, every physical
    tail in `X^B_s(y)` comes either from `X^B_s(p)` for some `p ∈ P \ B` or from
    `X^P_s(y)` with `s ∈ P`. -/
theorem exitTailMem_converse_split
    {H : LabelledQuotient} {B P : CutPair H}
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hProperP : H.ProperLoss P y)
    (hReachDisjoint : ¬ P.Mem s → H.SurvivingPath P.Mem H.root s)
    (hExitParent : H.ExitTailMem B s y x) :
    (∃ p : Fin H.vertexCount, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  let ⟨hLostP, hyNotP⟩ := hProperP
  let ⟨e, he, hTail, hContB⟩ := hExitParent
  cases split_at_fresh_or_avoid_child hContB hyNotP with
  | inl hFresh =>
      let ⟨p, hpFresh, hToP⟩ := hFresh
      exact Or.inl ⟨p, hpFresh, ⟨e, he, hTail, hToP⟩⟩
  | inr hAvoidP =>
      if hsP : P.Mem s then
        exact Or.inr ⟨hsP, ⟨e, he, hTail, hAvoidP⟩⟩
      else
        have hRootToS : H.SurvivingPath P.Mem H.root s := hReachDisjoint hsP
        have hArc : H.HasQuotientArc s e.head := ⟨e, he, rfl⟩
        have hSToY : H.SurvivingPath P.Mem s y :=
          AvoidPath.step s e.head y hsP hArc hAvoidP
        exact False.elim (hLostP (AvoidPath.trans hRootToS hSToY))


/-- Pointwise exit-set transfer under explicit path and cut-intersection facts.
The quotient and forest construction must supply these facts for a real forest edge. -/
theorem exitTailMem_iff_of_paths
    {H : LabelledQuotient} {B P : CutPair H}
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (hProper : H.ProperLoss P y)
    (onward : ∀ p, IsFreshEndpoint B P p → H.SurvivingPath B.Mem p y)
    (oldSurvives : ∀ v, B.Mem v → ¬ P.Mem v → H.SurvivingPath P.Mem H.root v)
    (atMostOneShared : ∀ u v, B.Mem u → P.Mem u → B.Mem v → P.Mem v → u = v) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  constructor
  · exact exitTailMem_converse_split hProper (oldSurvives s hs)
  · intro witness
    rcases witness with ⟨p, fresh, exitToP⟩ | ⟨shared, inherited⟩
    · exact exitTailMem_transfer_of_onwardPath exitToP (onward p fresh)
    · refine exitTailMem_transfer_inherited shared hProper.1 ?_ inherited
      intro v hv different
      exact oldSurvives v hv (fun alsoShared => different (atMostOneShared v s hv alsoShared hs shared))

/-- An endpoint of the parent outside the child survives both child deletions. -/
theorem oldEndpoint_survives_of_rank
    {H : LabelledQuotient} {B P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (freshLater : ∀ p, IsFreshEndpoint B P p → ∀ b, B.Mem b → rank b < rank p)
    (atMostOneShared : ∀ u v, B.Mem u → P.Mem u → B.Mem v → P.Mem v → u = v)
    {b : Fin H.vertexCount} (hb : B.Mem b) (hbP : ¬ P.Mem b) :
    H.SurvivingPath P.Mem H.root b := by
  have ranksAlong {u v : Fin H.vertexCount} {failed : Fin H.vertexCount → Prop}
      (path : H.SurvivingPath failed u v) : rank u ≤ rank v := by
    induction path with
    | refl _ _ => exact Nat.le_refl _
    | step start next finish _ arc _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (rankArc start next arc)) ih
  have excludeLater {deleted later u v : Fin H.vertexCount}
      (path : H.SurvivingPath (fun z => z = deleted) u v)
      (hLater : rank v < rank later) :
      H.SurvivingPath (fun z => z = deleted ∨ z = later) u v := by
    induction path with
    | refl node alive =>
      exact .refl node (fun h => h.elim alive (fun hEq => (Nat.ne_of_lt hLater) (congrArg rank hEq)))
    | step start next finish alive arc rest ih =>
      have before := Nat.lt_of_le_of_lt (ranksAlong rest) hLater
      have hStart := Nat.lt_trans (rankArc start next arc) before
      exact .step start next finish
        (fun h => h.elim alive (fun hEq => (Nat.ne_of_lt hStart) (congrArg rank hEq)))
        arc (ih hLater)
  by_cases shared : B.Mem P.fst
  · have fresh : IsFreshEndpoint B P P.snd := by
      refine ⟨Or.inr rfl, fun sharedRight => ?_⟩
      exact P.ne (atMostOneShared P.fst P.snd shared (Or.inl rfl) sharedRight (Or.inr rfl))
    exact excludeLater
      (flat.2 P.fst b P.fst_ne_root (fun h => hbP (Or.inl h))) (freshLater P.snd fresh b hb)
  · have fresh : IsFreshEndpoint B P P.fst := ⟨Or.inl rfl, shared⟩
    have survivor := excludeLater
      (flat.2 P.snd b P.snd_ne_root (fun h => hbP (Or.inr h))) (freshLater P.fst fresh b hb)
    exact AvoidPath.mono survivor (fun _ h => h.elim Or.inr Or.inl)

/-- A new child endpoint has a suffix to every proper child loss, avoiding the parent. -/
theorem freshEndpoint_onward_of_rank
    {H : LabelledQuotient} {B P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {p y : Fin H.vertexCount}
    (fresh : IsFreshEndpoint B P p)
    (freshLater : ∀ b, B.Mem b → rank b < rank p)
    (proper : H.ProperLoss P y) :
    H.SurvivingPath B.Mem p y := by
  have afterParent {u v : Fin H.vertexCount} {failed : Fin H.vertexCount → Prop}
      (path : H.SurvivingPath failed u v) (startsLater : rank p ≤ rank u) :
      H.SurvivingPath B.Mem u v := by
    induction path with
    | refl u _ =>
      exact .refl u (fun hu => Nat.not_lt_of_ge startsLater (freshLater u hu))
    | step u w v _ arc _ rest =>
      have nextLater := Nat.le_trans startsLater (Nat.le_of_lt (rankArc u w arc))
      exact .step u w v (fun hu => Nat.not_lt_of_ge startsLater (freshLater u hu))
        arc (rest nextLater)
  have splitAt {deleted u v : Fin H.vertexCount}
      (path : H.SurvivingPath (fun z => z = deleted) u v) :
      H.SurvivingPath B.Mem p v ∨ H.SurvivingPath (fun z => z = p ∨ z = deleted) u v := by
    induction path with
    | refl u alive =>
      by_cases equal : u = p
      · subst u
        exact Or.inl (.refl p fresh.2)
      · exact Or.inr (.refl u (fun h => h.elim equal alive))
    | step u w v alive arc suffix ih =>
      by_cases equal : u = p
      · subst u
        exact Or.inl (afterParent (.step p w v alive arc suffix) (Nat.le_refl _))
      · exact ih.elim Or.inl (fun rest => Or.inr (.step u w v (fun h => h.elim equal alive) arc rest))
  rcases fresh.1 with left | right
  · subst p
    have path := flat.2 P.snd y P.snd_ne_root (fun h => proper.2 (Or.inr h))
    exact (splitAt path).elim id (fun both => False.elim (proper.1 both))
  · subst p
    have path := flat.2 P.fst y P.fst_ne_root (fun h => proper.2 (Or.inl h))
    exact (splitAt path).elim id (fun both =>
      False.elim (proper.1 (AvoidPath.mono both (fun _ h => h.elim Or.inr Or.inl))))

/-- Exit transfer for two distinct cuts with all fresh child endpoints ordered later. -/
theorem exitTailMem_iff_of_flat_rank
    {H : LabelledQuotient} {B P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (freshLater : ∀ p, IsFreshEndpoint B P p → ∀ b, B.Mem b → rank b < rank p)
    (distinctCuts : ¬ ∀ z, B.Mem z ↔ P.Mem z)
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss P y) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  have exhausts (pair : CutPair H) {u v z : Fin H.vertexCount} (different : u ≠ v)
      (hu : pair.Mem u) (hv : pair.Mem v) :
      pair.Mem z ↔ z = u ∨ z = v := by
    rcases hu with left | right <;> rcases hv with first | second
    · exact False.elim (different (left.trans first.symm))
    · subst u
      subst v
      exact Iff.rfl
    · subst u
      subst v
      exact ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩
    · exact False.elim (different (right.trans second.symm))
  have atMostOneShared (u v : Fin H.vertexCount)
      (huB : B.Mem u) (huP : P.Mem u) (hvB : B.Mem v) (hvP : P.Mem v) : u = v := by
    by_cases equal : u = v
    · exact equal
    · exact False.elim (distinctCuts (fun _ => (exhausts B equal huB hvB).trans
        (exhausts P equal huP hvP).symm))
  exact exitTailMem_iff_of_paths hs proper
    (fun p fresh => freshEndpoint_onward_of_rank rankArc flat fresh (freshLater p fresh) proper)
    (fun _ hb hbP => oldEndpoint_survives_of_rank rankArc flat freshLater atMostOneShared hb hbP)
    atMostOneShared

/-- In a flat DAG, a proper loss strictly follows both endpoints of the cut. -/
theorem properLoss_follows_endpoints
    {H : LabelledQuotient} {B : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    {y b : Fin H.vertexCount} (proper : H.ProperLoss B y) (hb : B.Mem b) :
    rank b < rank y := by
  have ranksAlong {u v : Fin H.vertexCount} {failed : Fin H.vertexCount → Prop}
      (path : H.SurvivingPath failed u v) : rank u ≤ rank v := by
    induction path with
    | refl _ _ => exact Nat.le_refl _
    | step u w _ _ arc _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (rankArc u w arc)) ih
  have beforeOrAvoids {deleted u : Fin H.vertexCount}
      (path : H.SurvivingPath (fun z => z = deleted) u y) :
      rank b < rank y ∨ H.SurvivingPath (fun z => z = b ∨ z = deleted) u y := by
    have notTarget : y ≠ b := fun h => proper.2 (h.symm ▸ hb)
    induction path with
    | refl u alive =>
      exact Or.inr (.refl u (fun h => h.elim notTarget alive))
    | step u v y alive arc rest ih =>
      by_cases equal : u = b
      · subst u
        exact Or.inl (Nat.lt_of_lt_of_le (rankArc b v arc) (ranksAlong rest))
      · exact (ih proper notTarget).elim Or.inl (fun tail => Or.inr (.step u v y (fun h => h.elim equal alive) arc tail))
  rcases hb with first | second
  · subst b
    have path := flat.2 B.snd y B.snd_ne_root (fun h => proper.2 (Or.inr h))
    exact (beforeOrAvoids path).elim id (fun both => False.elim (proper.1 both))
  · subst b
    have path := flat.2 B.fst y B.fst_ne_root (fun h => proper.2 (Or.inl h))
    exact (beforeOrAvoids path).elim id (fun both =>
      False.elim (proper.1 (AvoidPath.mono both (fun _ h => h.elim Or.inr Or.inl))))

/-- Pointwise exit transfer for nested cuts in a flat acyclic quotient. -/
theorem exitTailMem_iff_of_nested_cuts
    {H : LabelledQuotient} {B P : CutPair H}
    (acyclic : H.IsAcyclic) (flat : H.IsFlat)
    (childEndpointsLost : ∀ p, P.Mem p → H.Lost B p)
    (distinctCuts : ¬ ∀ z, B.Mem z ↔ P.Mem z)
    {s y : Fin H.vertexCount} {x : Fin H.origVertexCount}
    (hs : B.Mem s) (proper : H.ProperLoss P y) :
    H.ExitTailMem B s y x ↔
      (∃ p, IsFreshEndpoint B P p ∧ H.ExitTailMem B s p x) ∨
      (P.Mem s ∧ H.ExitTailMem P s y x) := by
  obtain ⟨rank, rankArc⟩ := acyclic
  refine exitTailMem_iff_of_flat_rank rankArc flat ?_ distinctCuts hs proper
  intro p hFresh b hb
  exact properLoss_follows_endpoints rankArc flat ⟨childEndpointsLost p hFresh.1, hFresh.2⟩ hb

/-- The first proper loss of a pair has precisely the two cut endpoints as its distinct predecessors. -/
theorem predecessors_iff_endpoints_of_first_properLoss
    {H : LabelledQuotient} {B : CutPair H} {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {y : Fin H.vertexCount}
    (proper : H.ProperLoss B y)
    (first : ∀ v, H.ProperLoss B v → rank y ≤ rank v) :
    ∀ u, H.HasQuotientArc u y ↔ B.Mem u := by
  let ⟨hLostY, hyNotB⟩ := proper
  have fwd : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → B.Mem u := by
    intro u hArc
    if huB : B.Mem u then
      exact huB
    else
      have hLostU : H.Lost B u := fun hPathU =>
        hLostY (AvoidPath.trans hPathU
          (AvoidPath.step u y y huB hArc (AvoidPath.refl y hyNotB)))
      have hLt : rank u < rank y := rankArc u y hArc
      have hLe : rank y ≤ rank u := first u ⟨hLostU, huB⟩
      exact False.elim (Nat.lt_irrefl (rank u) (Nat.lt_of_lt_of_le hLt hLe))
  have hRootAlive : ¬ B.Mem H.root := by
    intro hMem
    cases hMem with
    | inl hFst => exact B.fst_ne_root hFst.symm
    | inr hSnd => exact B.snd_ne_root hSnd.symm
  have hyNeRoot : H.root ≠ y := by
    intro hEq
    have hRootPath : H.SurvivingPath B.Mem H.root y := by
      rw [← hEq]
      exact AvoidPath.refl H.root hRootAlive
    exact hLostY hRootPath
  have endpointArc : ∀ (keep other : Fin H.vertexCount),
      other ≠ H.root → y ≠ other →
      (∀ p : Fin H.vertexCount, B.Mem p → p ≠ other → p = keep) →
      H.HasQuotientArc keep y := by
    intro keep other hOtherNeRoot hyNeOther hDisj
    have hPath : H.SurvivingPath (fun z => z = other) H.root y :=
      flat.2 other y hOtherNeRoot hyNeOther
    cases AvoidPath.eq_or_exists_last_arc hPath with
    | inl hRootEqY =>
        exact False.elim (hyNeRoot hRootEqY)
    | inr hPred =>
        let ⟨p, hPrefix, hArcPY⟩ := hPred
        have hpNeOther : p ≠ other := fun equal => AvoidPath.target_alive hPrefix equal
        have hpEqKeep : p = keep := hDisj p (fwd p hArcPY) hpNeOther
        rw [← hpEqKeep]
        exact hArcPY
  intro u
  constructor
  · exact fwd u
  · intro huB
    cases huB with
    | inl huFst =>
        rw [huFst]
        exact endpointArc B.fst B.snd B.snd_ne_root
          (fun hEq => hyNotB (Or.inr hEq))
          (fun p hpB hpNeSnd =>
            match hpB with
            | Or.inl hpFst => hpFst
            | Or.inr hpSnd => False.elim (hpNeSnd hpSnd))
    | inr huSnd =>
        rw [huSnd]
        exact endpointArc B.snd B.fst B.fst_ne_root
          (fun hEq => hyNotB (Or.inl hEq))
          (fun p hpB hpNeFst =>
            match hpB with
            | Or.inl hpFst => False.elim (hpNeFst hpFst)
            | Or.inr hpSnd => hpSnd)

/-- A live nonroot vertex is lost exactly when all entering predecessors are lost. -/
theorem properLoss_iff_all_predecessors_lost
    {H : LabelledQuotient} {B : CutPair H} {y : Fin H.vertexCount}
    (notRoot : H.root ≠ y) :
    H.ProperLoss B y ↔ ¬ B.Mem y ∧ ∀ u, H.HasQuotientArc u y → H.Lost B u := by
  constructor
  · intro hProper
    let ⟨hLostY, hyNotB⟩ := hProper
    refine ⟨hyNotB, fun u hArc hPathU => ?_⟩
    have huAlive : ¬ B.Mem u := AvoidPath.target_alive hPathU
    have hStep : H.SurvivingPath B.Mem u y :=
      AvoidPath.step u y y huAlive hArc (AvoidPath.refl y hyNotB)
    exact hLostY (AvoidPath.trans hPathU hStep)
  · intro hRhs
    let ⟨hyNotB, hAllLost⟩ := hRhs
    refine ⟨fun hPathY => ?_, hyNotB⟩
    cases AvoidPath.eq_or_exists_last_arc hPathY with
    | inl hEq =>
        exact notRoot hEq
    | inr hPred =>
        let ⟨u, hPathU, hArcUY⟩ := hPred
        exact hAllLost u hArcUY hPathU

/-- Losing both child endpoints implies losing every vertex the child cut loses. -/
theorem lost_of_nested_endpoints
    {H : LabelledQuotient} {B P : CutPair H}
    (included : ∀ p, P.Mem p → H.Lost B p)
    {v : Fin H.vertexCount} (lost : H.Lost P v) :
    H.Lost B v := by
  have rebuild : ∀ {u w : Fin H.vertexCount},
      H.SurvivingPath B.Mem u w →
      H.SurvivingPath B.Mem H.root u →
      H.SurvivingPath P.Mem u w := by
    intro u w hSuf
    induction hSuf with
    | refl z _ =>
        intro hPref
        exact AvoidPath.refl z (fun hzP => included z hzP hPref)
    | step z next tgt aliveZ arc rest ih =>
        intro hPref
        have hzNotP : ¬ P.Mem z := fun hzP => included z hzP hPref
        have hNextAliveB : ¬ B.Mem next := AvoidPath.source_alive rest
        have hStepB : H.SurvivingPath B.Mem z next :=
          AvoidPath.step z next next aliveZ arc (AvoidPath.refl next hNextAliveB)
        have hPrefNext : H.SurvivingPath B.Mem H.root next :=
          AvoidPath.trans hPref hStepB
        exact AvoidPath.step z next tgt hzNotP arc (ih hPrefNext)
  intro hPathB
  have hRootPref : H.SurvivingPath B.Mem H.root H.root :=
    AvoidPath.refl H.root (AvoidPath.source_alive hPathB)
  exact lost (rebuild hPathB hRootPref)

/-- A pair omitting an entering predecessor can be tested from predecessor losses. -/
theorem properLoss_iff_of_latest_predecessor_not_mem
    {H : LabelledQuotient} {B : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {m y : Fin H.vertexCount}
    (notRoot : H.root ≠ y) (entering : H.HasQuotientArc m y)
    (outside : ¬ B.Mem m) :
    H.ProperLoss B y ↔ H.ProperLoss B m ∧ ∀ u, H.HasQuotientArc u y → H.Lost B u := by
  constructor
  · intro hProperY
    let ⟨_, hAllLost⟩ := (properLoss_iff_all_predecessors_lost notRoot).mp hProperY
    exact ⟨⟨hAllLost m entering, outside⟩, hAllLost⟩
  · intro hRhs
    let ⟨properM, hAllLost⟩ := hRhs
    have hyNotB : ¬ B.Mem y := by
      intro hyB
      have hYBeforeM : rank y < rank m :=
        properLoss_follows_endpoints rankArc flat properM hyB
      have hMBeforeY : rank m < rank y := rankArc m y entering
      exact Nat.lt_irrefl (rank y) (Nat.lt_trans hYBeforeM hMBeforeY)
    exact (properLoss_iff_all_predecessors_lost notRoot).mpr ⟨hyNotB, hAllLost⟩

/-- If a latest predecessor belongs to the cut, proper loss occurs exactly at the vertices with both endpoints as their distinct predecessors. -/
theorem properLoss_iff_predecessors_are_endpoints_of_latest_mem
    {H : LabelledQuotient} {B : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {m y : Fin H.vertexCount}
    (notRoot : H.root ≠ y) (_entering : H.HasQuotientArc m y)
    (latest : ∀ u, H.HasQuotientArc u y → rank u ≤ rank m)
    (isEndpoint : B.Mem m) :
    H.ProperLoss B y ↔ ∀ u, H.HasQuotientArc u y ↔ B.Mem u := by
  constructor
  · intro hProperY
    let ⟨hyNotB, hAllLost⟩ := (properLoss_iff_all_predecessors_lost notRoot).mp hProperY
    have fwd : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → B.Mem u := by
      intro u hArcUY
      if huB : B.Mem u then
        exact huB
      else
        have hProperU : H.ProperLoss B u := ⟨hAllLost u hArcUY, huB⟩
        have hMBeforeU : rank m < rank u :=
          properLoss_follows_endpoints rankArc flat hProperU isEndpoint
        have hULeM : rank u ≤ rank m := latest u hArcUY
        exact False.elim (Nat.lt_irrefl (rank m) (Nat.lt_of_lt_of_le hMBeforeU hULeM))
    have endpointArc : ∀ (keep other : Fin H.vertexCount),
        other ≠ H.root → y ≠ other →
        (∀ p : Fin H.vertexCount, B.Mem p → p ≠ other → p = keep) →
        H.HasQuotientArc keep y := by
      intro keep other hOtherNeRoot hyNeOther hDisj
      have hPath : H.SurvivingPath (fun z => z = other) H.root y :=
        flat.2 other y hOtherNeRoot hyNeOther
      cases AvoidPath.eq_or_exists_last_arc hPath with
      | inl hRootEqY =>
          exact False.elim (notRoot hRootEqY)
      | inr hPred =>
          let ⟨p, hPrefix, hArcPY⟩ := hPred
          have hpNeOther : p ≠ other :=
            fun equal => AvoidPath.target_alive hPrefix equal
          have hpEqKeep : p = keep := hDisj p (fwd p hArcPY) hpNeOther
          rw [← hpEqKeep]
          exact hArcPY
    intro u
    constructor
    · exact fwd u
    · intro huB
      cases huB with
      | inl huFst =>
          rw [huFst]
          exact endpointArc B.fst B.snd B.snd_ne_root
            (fun hEq => hyNotB (Or.inr hEq))
            (fun p hpB hpNeSnd =>
              match hpB with
              | Or.inl hpFst => hpFst
              | Or.inr hpSnd => False.elim (hpNeSnd hpSnd))
      | inr huSnd =>
          rw [huSnd]
          exact endpointArc B.snd B.fst B.fst_ne_root
            (fun hEq => hyNotB (Or.inl hEq))
            (fun p hpB hpNeFst =>
              match hpB with
              | Or.inl hpFst => False.elim (hpNeFst hpFst)
              | Or.inr hpSnd => hpSnd)
  · intro hIff
    have hyNotB : ¬ B.Mem y := by
      intro hyB
      have hSelfArc : H.HasQuotientArc y y := (hIff y).mpr hyB
      exact Nat.lt_irrefl (rank y) (rankArc y y hSelfArc)
    have hAllLost : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost B u :=
      fun u hArcUY hPathU => AvoidPath.target_alive hPathU ((hIff u).mp hArcUY)
    exact (properLoss_iff_all_predecessors_lost notRoot).mpr ⟨hyNotB, hAllLost⟩

/-- The cuts that lose every predecessor form an initial segment of a nested ancestor chain. -/
theorem predecessor_losses_form_prefix
    {H : LabelledQuotient} {y : Fin H.vertexCount}
    (chain : List (CutPair H))
    (nested : chain.Pairwise
      (fun ancestor child => ∀ p, child.Mem p → H.Lost ancestor p))
    (test : ∀ B : CutPair H,
      Decidable (∀ u, H.HasQuotientArc u y → H.Lost B u)) :
    ∃ accepted rejected : List (CutPair H),
      chain = accepted ++ rejected ∧
      (∀ B, B ∈ accepted → ∀ u, H.HasQuotientArc u y → H.Lost B u) ∧
      (∀ B, B ∈ rejected → ¬ (∀ u, H.HasQuotientArc u y → H.Lost B u)) := by
  have memCases {B head : CutPair H} {tail : List (CutPair H)}
      (mem : B ∈ head :: tail) : B = head ∨ B ∈ tail := by
    cases mem with
    | head _ => exact Or.inl rfl
    | tail _ rest => exact Or.inr rest
  revert nested
  induction chain with
  | nil =>
      intro _nested
      refine ⟨[], [], rfl, ?_, ?_⟩
      · intro _ hMem
        nomatch hMem
      · intro _ hMem
        nomatch hMem
  | cons head tail ih =>
      intro nested
      let ⟨headNested, tailNested⟩ := List.pairwise_cons.mp nested
      cases test head with
      | isTrue hHeadPass =>
          let ⟨accepted, rejected, hAppend, hAcc, hRej⟩ := ih tailNested
          refine ⟨head :: accepted, rejected, congrArg (List.cons head) hAppend, ?_, hRej⟩
          intro B hMem u hArc
          cases memCases hMem with
          | inl hEq =>
              rw [hEq]
              exact hHeadPass u hArc
          | inr hInAcc =>
              exact hAcc B hInAcc u hArc
      | isFalse hHeadFail =>
          refine ⟨[], head :: tail, rfl, ?_, ?_⟩
          · intro _ hMem
            nomatch hMem
          · intro B hMem hPassB
            cases memCases hMem with
            | inl hEq =>
                have hHeadPass : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost head u := by
                  rw [← hEq]
                  exact hPassB
                exact hHeadFail hHeadPass
            | inr hInTail =>
                have hIncluded : ∀ p : Fin H.vertexCount, B.Mem p → H.Lost head p :=
                  headNested B hInTail
                have hHeadPass : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost head u :=
                  fun u hArc => lost_of_nested_endpoints hIncluded (hPassB u hArc)
                exact hHeadFail hHeadPass

theorem takeWhile_predecessor_losses_iff
    {H : LabelledQuotient} {y : Fin H.vertexCount}
    (chain : List (CutPair H))
    (nested : chain.Pairwise
      (fun ancestor child => ∀ p, child.Mem p → H.Lost ancestor p))
    (passes : CutPair H → Bool)
    (correct : ∀ B, passes B = true ↔ ∀ u, H.HasQuotientArc u y → H.Lost B u)
    (B : CutPair H) :
    B ∈ chain.takeWhile passes ↔
      B ∈ chain ∧ ∀ u, H.HasQuotientArc u y → H.Lost B u := by
  revert nested
  induction chain with
  | nil =>
      intro _nested
      constructor
      · intro hMem
        change B ∈ [] at hMem
        nomatch hMem
      · intro hRhs
        nomatch hRhs.1
  | cons head tail ih =>
      intro nested
      let ⟨headNested, tailNested⟩ := List.pairwise_cons.mp nested
      if hHead : passes head = true then
        rw [List.takeWhile_cons_of_pos hHead]
        constructor
        · intro hMem
          cases List.mem_cons.mp hMem with
          | inl hEq =>
              refine ⟨List.mem_cons.mpr (Or.inl hEq), ?_⟩
              rw [hEq]
              exact (correct head).mp hHead
          | inr hInTailTake =>
              let ⟨hInTail, hLostB⟩ := (ih tailNested).mp hInTailTake
              exact ⟨List.mem_cons.mpr (Or.inr hInTail), hLostB⟩
        · intro hRhs
          let ⟨hInCons, hLostB⟩ := hRhs
          cases List.mem_cons.mp hInCons with
          | inl hEq =>
              exact List.mem_cons.mpr (Or.inl hEq)
          | inr hInTail =>
              exact List.mem_cons.mpr (Or.inr ((ih tailNested).mpr ⟨hInTail, hLostB⟩))
      else
        rw [List.takeWhile_cons_of_neg hHead]
        constructor
        · intro hMem
          nomatch hMem
        · intro hRhs
          let ⟨hInCons, hLostB⟩ := hRhs
          have hHeadNotLost : ¬ (∀ u, H.HasQuotientArc u y → H.Lost head u) :=
            fun hAll => hHead ((correct head).mpr hAll)
          cases List.mem_cons.mp hInCons with
          | inl hEq =>
              have hHeadLost : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost head u := by
                rw [← hEq]
                exact hLostB
              exact False.elim (hHeadNotLost hHeadLost)
          | inr hInTail =>
              have hIncluded : ∀ p : Fin H.vertexCount, B.Mem p → H.Lost head p :=
                headNested B hInTail
              have hHeadLost : ∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost head u :=
                fun u hArc => lost_of_nested_endpoints hIncluded (hLostB u hArc)
              exact False.elim (hHeadNotLost hHeadLost)

theorem sweep_parent_eq_for_reused_pair_key
    {H : LabelledQuotient} {P : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (distinctRanks : ∀ a b, rank a = rank b → a = b)
    (ancestors : Fin H.vertexCount → List (CutPair H))
    {y z mY mZ : Fin H.vertexCount}
    (keyY : ∀ u, H.HasQuotientArc u y ↔ P.Mem u)
    (keyZ : ∀ u, H.HasQuotientArc u z ↔ P.Mem u)
    (edgeY : H.HasQuotientArc mY y) (edgeZ : H.HasQuotientArc mZ z)
    (latestY : ∀ u, H.HasQuotientArc u y → rank u ≤ rank mY)
    (latestZ : ∀ u, H.HasQuotientArc u z → rank u ≤ rank mZ)
    (passesY passesZ : CutPair H → Bool)
    (correctY : ∀ B, passesY B = true ↔ ∀ u, H.HasQuotientArc u y → H.Lost B u)
    (correctZ : ∀ B, passesZ B = true ↔ ∀ u, H.HasQuotientArc u z → H.Lost B u) :
    ((ancestors mY).takeWhile passesY).getLast? =
      ((ancestors mZ).takeWhile passesZ).getLast? := by
  have hmYToZ : H.HasQuotientArc mY z := (keyZ mY).mpr ((keyY mY).mp edgeY)
  have hmZToY : H.HasQuotientArc mZ y := (keyY mZ).mpr ((keyZ mZ).mp edgeZ)
  have hRankEq : rank mY = rank mZ :=
    Nat.le_antisymm (latestZ mY hmYToZ) (latestY mZ hmZToY)
  have hMEq : mY = mZ := distinctRanks mY mZ hRankEq
  have hPassesEq : passesY = passesZ := by
    funext B
    have hPropIff :
        (∀ u : Fin H.vertexCount, H.HasQuotientArc u y → H.Lost B u) ↔
        (∀ u : Fin H.vertexCount, H.HasQuotientArc u z → H.Lost B u) := by
      constructor
      · intro hLostY u hArcUZ
        exact hLostY u ((keyY u).mpr ((keyZ u).mp hArcUZ))
      · intro hLostZ u hArcUY
        exact hLostZ u ((keyZ u).mpr ((keyY u).mp hArcUY))
    cases hBY : passesY B with
    | false =>
        cases hBZ : passesZ B with
        | false => exact rfl
        | true =>
            have hYTrue : passesY B = true :=
              (correctY B).mpr (hPropIff.mpr ((correctZ B).mp hBZ))
            exact Eq.trans hBY.symm hYTrue
    | true =>
        cases hBZ : passesZ B with
        | false =>
            have hZTrue : passesZ B = true :=
              (correctZ B).mpr (hPropIff.mp ((correctY B).mp hBY))
            exact Eq.trans hZTrue.symm hBZ
        | true => exact rfl
  rw [hMEq, hPassesEq]

theorem sweep_step_preserves_proper_loss_labels
    {H : LabelledQuotient} {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {m y : Fin H.vertexCount}
    (notRoot : H.root ≠ y) (entering : H.HasQuotientArc m y)
    (latest : ∀ u, H.HasQuotientArc u y → rank u ≤ rank m)
    (chain : List (CutPair H))
    (nested : chain.Pairwise
      (fun ancestor child => ∀ p, child.Mem p → H.Lost ancestor p))
    (priorSound : ∀ B, B ∈ chain → H.ProperLoss B m)
    (priorComplete : ∀ B : CutPair H, B.fst < B.snd → H.ProperLoss B m → B ∈ chain)
    (passes : CutPair H → Bool)
    (correct : ∀ B, passes B = true ↔ ∀ u, H.HasQuotientArc u y → H.Lost B u)
    (candidate : Option (CutPair H))
    (candidateExact : ∀ B : CutPair H, candidate = some B ↔
      B.fst < B.snd ∧ ∀ u, H.HasQuotientArc u y ↔ B.Mem u) :
    let next := chain.takeWhile passes ++ candidate.toList
    next.Pairwise (fun ancestor child => ∀ p, child.Mem p → H.Lost ancestor p) ∧
      ∀ B : CutPair H, B.fst < B.snd → (B ∈ next ↔ H.ProperLoss B y) := by
  refine ⟨?_, ?_⟩
  · refine List.pairwise_append.mpr ⟨?_, ?_, ?_⟩
    · exact nested.sublist (by apply List.takeWhile_sublist)
    · cases candidate <;> simp
    · intro ancestor hAncestor child hChild p hp
      have hLost :=
        ((takeWhile_predecessor_losses_iff chain nested passes correct ancestor).mp hAncestor).2
      rw [Option.mem_toList] at hChild
      have hArc : H.HasQuotientArc p y :=
        (((candidateExact child).mp hChild).2 p).mpr hp
      exact hLost p hArc
  · intro B hOrder
    change B ∈ chain.takeWhile passes ++ candidate.toList ↔ H.ProperLoss B y
    rw [List.mem_append, Option.mem_toList]
    constructor
    · intro hMem
      cases hMem with
      | inl hPrefix =>
          have ⟨hInChain, hAllLost⟩ :=
            (takeWhile_predecessor_losses_iff chain nested passes correct B).mp hPrefix
          have hProperM : H.ProperLoss B m := priorSound B hInChain
          have hmNotMem : ¬ B.Mem m := hProperM.2
          exact (properLoss_iff_of_latest_predecessor_not_mem
            rankArc flat notRoot entering hmNotMem).mpr ⟨hProperM, hAllLost⟩
      | inr hCand =>
          have ⟨_, hEndpoints⟩ := (candidateExact B).mp hCand
          have hmMem : B.Mem m := (hEndpoints m).mp entering
          exact (properLoss_iff_predecessors_are_endpoints_of_latest_mem
            rankArc flat notRoot entering latest hmMem).mpr hEndpoints
    · intro hProperY
      by_cases hm : B.Mem m
      · have hEndpoints : ∀ u, H.HasQuotientArc u y ↔ B.Mem u :=
          (properLoss_iff_predecessors_are_endpoints_of_latest_mem
            rankArc flat notRoot entering latest hm).mp hProperY
        have hSome : candidate = some B := (candidateExact B).mpr ⟨hOrder, hEndpoints⟩
        exact Or.inr hSome
      · have ⟨hProperM, hAllLost⟩ :=
          (properLoss_iff_of_latest_predecessor_not_mem
            rankArc flat notRoot entering hm).mp hProperY
        have hInChain : B ∈ chain := priorComplete B hOrder hProperM
        exact Or.inl
          ((takeWhile_predecessor_losses_iff chain nested passes correct B).mpr
            ⟨hInChain, hAllLost⟩)

end LabelledQuotient

end PaperB
