module

public import PaperB.ForestMeasuredWork
public import PaperB.ForestPhysicalReflection

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false
/- Place after the PreparedSweep and ForestMeasuredWork declarations, with
   their existing imports. This proves the local SiteOK obligation and its
   uniform bound; it does not assert propagation through the whole Trace. -/

namespace EX24.PreparedSweep

open EX24.PreStep PaperB PaperB.LabelledQuotient PaperB.ForestHead

theorem depthOf_le_physicalSlot {F : JumpForest} {exps : Nat → List Nat}
    (inv : ForestInvariant F exps) :
    ∀ u : Nat, u < F.size → F.depthOf u ≤ u := by
  intro u
  induction u using Nat.strongRecOn
  rename_i u ih
  intro hu
  by_cases hz : u = 0
  · subst u
    simpa only [inv.root_depth] using (Nat.le_refl 0)
  · have hpos : 0 < u := by omega
    have node := inv.nodes u hu
    have hparent : F.parentOf u < u := node.pos_parent_lt hpos
    have hoccupied : F.parentOf u < F.size := Nat.lt_trans hparent hu
    have hdepth := ih (F.parentOf u) hparent hoccupied
    rw [node.pos_depth hpos]
    omega

private theorem measuredSlot_depth_eq
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} (g : Grounded c F s.tables)
    {u : Nat} (hu : u < F.size) :
    (selectors c s).depth u = F.depthOf u := by
  have hn : u < s.tables.next := by simpa only [g.size_eq] using hu
  have layout := g.layout
  first
  | exact?
  | simp only [selectors, JumpForest.depthOf] <;>
      first
      | exact?
      | congr 1 <;> exact?
      | cases layout <;>
          first
          | solve_by_elim
          | congr 1 <;> solve_by_elim
          | simp_all (disch := omega) [JumpForest.recordAt] <;> grind
  | cases g <;>
      cases layout <;>
      simp_all (disch := omega) [selectors, JumpForest.depthOf,
        JumpForest.recordAt] <;> grind

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

private theorem measuredPlan_max
    {H : LabelledQuotient} {rank : Vertex H → Nat}
    {row : Row H} {m : Vertex H} {key : Option (CutPair H)}
    (hp : ForestHead.planPrepared rank row.head row.tests = some (m, key)) :
    PaperB.LabelledQuotient.maxByRank rank row.tests = some m := by
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

private theorem measuredTest_arc
    {H : LabelledQuotient} {m y : Vertex H} {xs : List (Vertex H)}
    (T : TestSpec y xs) (hm : m ∈ xs) : H.HasQuotientArc m y := by
  have cover := T.cover
  first
  | exact (cover m).mp hm
  | exact (cover m).mpr hm
  | exact cover.mp hm
  | exact cover.mpr hm
  | exact cover m hm
  | exact cover hm
  | have hpred : m ∈ preds H y := by
      first
      | exact (cover m).mp hm
      | exact (cover m).mpr hm
      | exact cover.mp hm
      | exact cover.mpr hm
      | exact cover m hm
      | exact cover hm
      | exact cover.mem_iff.mp hm
      | exact cover.mem_iff.mpr hm
      | simpa only [cover] using hm
      | simpa only [← cover] using hm
    first
    | exact arc_of_pred_mem hpred
    | exact?
    | have hb : H.hasQuotientArcBool m y = true := by
        first
        | exact (List.mem_filter.mp hpred).2
        | simp [preds] at hpred
          grind
      first
      | exact?
      | simpa [LabelledQuotient.hasQuotientArcBool] using hb
    | simp [preds] at hpred
      grind
  | grind

/-- The local work premise at the same prefix embedding used by
    `foldRowsAux_total` before its prepared step. -/
theorem siteOK_of_prefix
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size} {row : Row H}
    (E : Embedding c s F rank up (fun v => rank v < rank row.head))
    (g : Grounded c F s.tables)
    (T : TestSpec row.head row.tests)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v) :
    AggregateEX24.SiteOK c rank s row := by
  refine ⟨T, ⟨F, g⟩, ?_⟩
  intro m key hp
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
  have hm : m ∈ row.tests := by
    first
    | exact max_mem rank hmax
    | exact?
  have hearlier : rank m < rank row.head :=
    rankArc m row.head (measuredTest_arc T hm)
  have hlabel : (selectors c s).label m < F.size := by
    first
    | exact E.label_lt m hearlier
    | exact E.label_lt hearlier
  obtain ⟨exps, inv⟩ := g.layout.valid.exists_forestInvariant
  have hdepth := depthOf_le_physicalSlot inv ((selectors c s).label m) hlabel
  rw [measuredSlot_depth_eq g hlabel]
  rw [g.size_eq] at hlabel
  omega

/-- At a nonempty fold suffix, the totality proof's budget bounds `next`
    by `nH`, not by `nH + 1`. Thus the same `nH` bounds every live depth
    argument plus one. Instantiate `nH` with `H.vertexCount` for FullRows. -/
theorem siteOK_and_uniform_of_exact_row
    {H : LabelledQuotient} {c : Config H} {s : State H}
    {F : JumpForest} {rank : Vertex H → Nat}
    {up : Fin F.size → Fin F.size} {row : Row H} {rows : List (Row H)}
    {nH : Nat} (p : ForestDictionary.Rows H)
    (hexact : row.tests = p.row row.head)
    (E : Embedding c s F rank up (fun v => rank v < rank row.head))
    (g : Grounded c F s.tables)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (hbudget : s.tables.next + (row :: rows).length ≤ nH + 1) :
    AggregateEX24.SiteOK c rank s row ∧
      (∀ m key, ForestHead.planPrepared rank row.head row.tests = some (m, key) →
        (selectors c s).depth ((selectors c s).label m) + 1 ≤ nH) := by
  have T : TestSpec row.head row.tests := by
    rw [hexact]
    exact p.spec row.head
  have site := siteOK_of_prefix E g T rankArc
  have hnext : s.tables.next ≤ nH := by
    simp only [List.length_cons] at hbudget
    omega
  refine ⟨site, ?_⟩
  intro m key hp
  exact Nat.le_trans (site.2.2 m key hp) hnext

end EX24.PreparedSweep
