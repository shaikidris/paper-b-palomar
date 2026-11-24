module

public import PaperB.MeasuredCutRange
public import PaperB.ForestCompactFold
public import PaperB.ForestEndpoints
public import PaperB.ForestPreparedHead
public import PaperB.ForestWordLaws
public import PaperB.ForestCanonicalLaws

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/- This module has not been compiler-checked: I do not have access to the
   PaperB sources or a Lean runtime here. -/

namespace EX24

open PaperB PaperB.ForestHead PaperB.PairLookup PaperB.LabelledQuotient
open PreStep

namespace PreparedSweep

private theorem append_parent (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).parentOf F.size = p := by
  unfold JumpForest.parentOf
  rw [recordAt_appendLeaf_new F p]
  rfl

private theorem append_depth (F : JumpForest) (p : Nat) :
    (F.appendLeaf p).depthOf F.size = F.depthOf p + 1 := by
  unfold JumpForest.depthOf
  rw [recordAt_appendLeaf_new F p]
  rfl

private theorem max_mem
    {H : LabelledQuotient} (rank : Vertex H → Nat)
    {xs : List (Vertex H)} {m : Vertex H}
    (hm : maxByRank rank xs = some m) : m ∈ xs := by
  first
  | exact?
  | let pick : Vertex H → List (Vertex H) → Vertex H := by
      first
      | exact maxByRankAux rank
      | exact fun a ys => maxByRankAux rank ys a
    have aux (a : Vertex H) (ys : List (Vertex H)) :
        pick a ys ∈ a :: ys := by
      induction ys generalizing a with
      | nil => simp [pick, maxByRankAux]
      | cons b ys ih =>
          have ha := ih a
          have hb := ih b
          simp only [List.mem_cons] at ha hb ⊢
          simp only [pick, maxByRankAux]
          split
          all_goals
            first
            | exact ha.elim Or.inl (fun ht => Or.inr (Or.inr ht))
            | exact Or.inr hb
            | grind
    cases xs with
    | nil => simp [maxByRank] at hm
    | cons a ys =>
        change some (pick a ys) = some m at hm
        exact (Option.some.inj hm) ▸ aux a ys

private theorem arc_of_pred_mem
    {H : LabelledQuotient} {u y : Vertex H}
    (hu : u ∈ preds H y) : H.HasQuotientArc u y := by
  first
  | exact?
  | have hb : H.hasQuotientArcBool u y = true := by
      first
      | exact (List.mem_filter.mp hu).2
      | exact?
      | simp [preds] at hu
        grind
    first
    | exact?
    | simpa [LabelledQuotient.hasQuotientArcBool] using hb
  | simp [preds] at hu
    grind

private theorem test_arc
    {H : LabelledQuotient} {u y : Vertex H} {xs : List (Vertex H)}
    (T : TestSpec y xs) (hu : u ∈ xs) : H.HasQuotientArc u y := by
  have cover := T.cover
  first
  | exact (cover u).mp hu
  | exact (cover u).mpr hu
  | exact cover u hu
  | exact cover hu
  | apply arc_of_pred_mem
    first
    | exact (cover u).mp hu
    | exact (cover u).mpr hu
    | exact cover u hu
    | exact cover hu
    | exact cover.mem_iff.mp hu
    | exact cover.mem_iff.mpr hu
    | simpa only [cover] using hu
    | simpa only [← cover] using hu
    | grind
  | grind

/-- One successful prepared head with packed word callbacks extends the prefix
    embedding. `oldParent` identifies the old map with the physical parent map;
    the new map is the bounded physical parent map of the resulting forest. -/
theorem prepared_step_invariant
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size}
    {row : Row H} {r : HeadResult H}
    (hc : c.usePackedWords = c)
    (E : Embedding c s F rank up (fun v => rank v < rank row.head))
    (g : Grounded c F s.tables)
    (oldParent : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (T : TestSpec row.head row.tests)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ a b : Vertex H, rank a = rank b → a = b)
    (flat : H.IsFlat)
    (h : stepPrepared c s rank row.head row.tests = some r) :
    let F' := if r.installed.allocated then
      F.appendLeaf r.measured.step.parent
    else F
    ∃ up' : Fin F'.size → Fin F'.size,
      (∀ b : Fin F'.size, (up' b).val = F'.parentOf b.val) ∧
      ∃ E' : Embedding c r.state F' rank up'
          (fun v => rank v < rank row.head ∨ v = row.head),
        (∀ (a : Fin F.size) (b : Fin F'.size), b.val = a.val →
          E'.image b = E.image a) ∧
        (∀ b : Fin F'.size, b.val = r.installed.node →
          E'.image b = (buildProperLossForest H rank).label row.head) ∧
        (∀ (a : Fin F.size) (b : Fin F'.size), b.val = a.val →
          r.state.tables.back[b.val]? = s.tables.back[a.val]?) ∧
        (∀ v, rank v < rank row.head →
          (selectors c r.state).label v = (selectors c s).label v ∧
          r.state.tables.back[(selectors c r.state).label v]? =
            s.tables.back[(selectors c s).label v]?) ∧
        r.measured = ForestHead.runPrepared
          (selectors c s) rank row.head row.tests := by
  have inj : ∀ {a b : Vertex H}, rank a = rank b → a = b :=
    fun {a b} he => distinctRanks a b he
  have hs : step c s rank row.head row.tests = some r :=
    (stepPrepared_eq_step c s rank row.head row.tests T inj).symm.trans h
  have hp₀ : r.measured.step.parent < F.size := (step_install_cases g hs).1
  have h0 : 0 < F.size := by omega

  let F' := if r.installed.allocated then
    F.appendLeaf r.measured.step.parent
  else F
  have g' : Grounded c F' r.state.tables := (step_spec g hs).1.grounded

  let up' : Fin F'.size → Fin F'.size := boundedJumpParent g'.layout.valid
  have newParent : ∀ b : Fin F'.size, (up' b).val = F'.parentOf b.val :=
    fun _ => rfl

  have W : WordLaws c s F up := by
    have gp : Grounded c.usePackedWords F s.tables := by
      rw [hc]
      exact g
    have hup : up = boundedJumpParent gp.layout.valid := by
      funext a
      apply Fin.ext
      exact oldParent a
    rw [← hc, hup]
    exact wordLaws_of_packed_grounded c s gp
  have L : CanonicalLaws H rank := canonicalLaws_of_flat_forward rankArc flat
  have rootView : view E 0 = [] := view_root E L h0
  have readyY : ∀ m, row.head ≠ H.root →
      H.hasQuotientArcBool H.root row.head = false →
      maxByRank rank (preds H row.head) = some m →
      H.HasQuotientArc m row.head ∧
        PaperB.ForestHead.Ready (selectors c s) (view E) rank row.head m row.tests := by
    intro m _ _ hm
    have hmy : H.HasQuotientArc m row.head :=
      arc_of_pred_mem (max_mem rank hm)
    exact ⟨hmy, ready E rankArc distinctRanks flat W L h0
      (rankArc m row.head hmy)
      (fun u hu => rankArc u row.head (test_arc T hu))⟩

  have sem := step_request_semantics hs (view E) T rootView rankArc readyY
  obtain ⟨hp, hlast, hback, halloc, _⟩ :=
    step_endpoint_facts E g hs rankArc distinctRanks flat L sem
  let z := (buildProperLossForest H rank).label row.head
  let k := (buildProperLossForest H rank).nodeKey? z
  have canonicalLast : (sweepChain H rank row.head).getLast? = k :=
    (congrArg (fun l : List (CutPair H) => l.getLast?) sem).symm.trans hlast
  have forest_eq : F' =
      (if r.installed.allocated then F.appendLeaf r.measured.step.parent else F) :=
    rfl
  obtain ⟨E', keep, selected⟩ :=
    step_embedding_of_endpoint E g hs h0 forest_eq g.size_eq.symm g'.size_eq
      (fun a => occupied_depth_eq (s := s) g a)
      (fun b => occupied_depth_eq (s := r.state) g' b)
      oldParent newParent z k rfl hback
      (fun ha n _hn => (halloc ha).2.1 n) (fun _ => hp)
      (fun _ => append_parent F r.measured.step.parent)
      (fun _ => append_depth F r.measured.step.parent)
      (fun ha => (halloc ha).2.2.1) (fun ha => (halloc ha).2.2.2)
      T rootView rankArc readyY hlast canonicalLast

  have keepBack (a : Fin F.size) (b : Fin F'.size) (he : b.val = a.val) :
      r.state.tables.back[b.val]? = s.tables.back[a.val]? := by
    rw [E'.back_eq b, keep a b he, E.back_eq a]
  refine ⟨up', newParent, E', keep, selected, keepBack, ?_, ?_⟩
  · intro v hv
    have hne : v ≠ row.head := by
      intro he
      subst v
      exact (Nat.lt_irrefl _) hv
    have hl := previous_label hs hne
    exact ⟨hl, keepBack
      ⟨(selectors c s).label v, E.label_lt v hv⟩
      ⟨(selectors c r.state).label v, E'.label_lt v (Or.inl hv)⟩ hl⟩
  · exact (step_parts hs).1.trans
      (ForestHead.runPrepared_eq_runHead
        (selectors c s) rank row.head row.tests T inj).symm

end PreparedSweep
end EX24

namespace EX24.PreparedSweep

open PaperB PaperB.ForestHead EX24.PreStep

private theorem packed_nodeAt_lt_next
    {H : LabelledQuotient} {F : JumpForest}
    (c : Config H) (s : State H)
    (g : Grounded c.usePackedWords F s.tables)
    (a : Fin F.size) (d : Nat)
    (hd : d ≤ (selectors c.usePackedWords s).depth a.val) :
    nodeAt (selectors c.usePackedWords s) a.val d < s.tables.next := by
  have w := wordLaws_of_packed_grounded c s g
  rw [← g.size_eq]
  by_cases hz : d = 0
  · subst d
    rw [w.node_zero a.val]
    have ha := a.isLt
    omega
  · have hp : 0 < d := by omega
    rw [w.node_pos a.val d hp hd, w.at_depth a d hp hd]
    exact
      (climb (boundedJumpParent g.layout.valid)
        ((selectors c.usePackedWords s).depth a.val - d) a).isLt

theorem runPrepared_parent_occupied
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size} {row : Row H}
    (hc : c.usePackedWords = c)
    (E : Embedding c s F rank up (fun v => rank v < rank row.head))
    (g : Grounded c F s.tables)
    (T : TestSpec row.head row.tests)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) :
    (ForestHead.runPrepared (selectors c s) rank row.head row.tests).step.parent
      < s.tables.next := by
  have gp : Grounded c.usePackedWords F s.tables := by
    simpa only [hc] using g
  -- At positive depth this is the occupancy consequence of packed WordLaws.at_depth.
  have read_lt (a : Fin F.size) (d : Nat)
      (hd : d ≤ (selectors c s).depth a.val) :
      ForestHead.nodeAt (selectors c s) a.val d < s.tables.next := by
    have hdp : d ≤ (selectors c.usePackedWords s).depth a.val := by
      simpa only [hc] using hd
    simpa only [hc] using packed_nodeAt_lt_next c s gp a d hdp
  have hroot : 0 < s.tables.next := by
    obtain ⟨_, inv⟩ := g.layout.valid.exists_forestInvariant
    simpa only [g.size_eq] using inv.size_pos
  cases hp : ForestHead.planPrepared rank row.head row.tests with
  | none =>
      simpa only [ForestHead.runPrepared, hp, ForestHead.stopped, ForestHead.finish]
        using hroot
  | some plan =>
      rcases plan with ⟨m, key⟩
      have hmax : PaperB.LabelledQuotient.maxByRank rank row.tests = some m := by
        unfold ForestHead.planPrepared at hp
        split at hp
        · simp at hp
        · split at hp
          · simp at hp
          · cases hm : PaperB.LabelledQuotient.maxByRank rank row.tests with
            | none => simp [hm] at hp
            | some a =>
                simp only [hm, Option.map, Option.some.injEq] at hp
                exact congrArg Option.some (congrArg Prod.fst hp)
      have hmem : m ∈ row.tests := max_mem rank hmax
      have harc : H.HasQuotientArc m row.head := by
        first
        | exact (T.cover m).mp hmem
        | exact (T.cover m).mpr hmem
        | exact T.cover.mp hmem
        | exact T.cover.mpr hmem
        | exact T.cover m hmem
        | exact T.cover hmem
        | exact arc_of_pred_mem ((T.cover m).mp hmem)
        | exact arc_of_pred_mem ((T.cover m).mpr hmem)
        | exact arc_of_pred_mem (by simpa only [T.cover] using hmem)
        | exact arc_of_pred_mem (by simpa only [← T.cover] using hmem)
      have hearlier : rank m < rank row.head := rankArc m row.head harc
      have hlabel : (selectors c s).label m < F.size := by
        first
        | exact E.label_lt m hearlier
        | exact E.label_lt hearlier
      let d := (ForestHead.active (selectors c s) row.tests m key).search.cut
      have hd : d ≤ (selectors c s).depth ((selectors c s).label m) := by
        dsimp only [d, ForestHead.active, ForestHead.measuredLog]
        exact Nat.le_of_lt_succ
          (ForestHead.measuredSearch_cut_lt_hi _ _ 0 _ (Nat.zero_lt_succ _))
      simp only [ForestHead.runPrepared, hp]
      change ForestHead.nodeAt (selectors c s) ((selectors c s).label m) d
        < s.tables.next
      by_cases hz : d = 0
      · simpa only [ForestHead.nodeAt, if_pos hz] using hroot
      · simpa only [ForestHead.nodeAt, if_neg hz] using
          read_lt (⟨(selectors c s).label m, hlabel⟩ : Fin F.size) d hd

end EX24.PreparedSweep
