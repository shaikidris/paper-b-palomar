module

public import Std
public import PaperB.TopologicalRank

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

def CommonDominator (g : Digraph) (r : Fin g.vertexCount)
    (vs : List (Fin g.vertexCount)) (d : Fin g.vertexCount) : Prop :=
  ∀ v ∈ vs, g.Dominates r d v

/-- The LCA is a common dominator dominated by every common dominator. -/
def IsDominatorLCA (g : Digraph) (r : Fin g.vertexCount)
    (vs : List (Fin g.vertexCount)) (l : Fin g.vertexCount) : Prop :=
  g.CommonDominator r vs l ∧
    ∀ d, g.CommonDominator r vs d → g.Dominates r d l

variable {g : Digraph}
variable {r d : Fin g.vertexCount} {vs : List (Fin g.vertexCount)}

private theorem lca_start_alive {failed : Fin g.vertexCount → Prop}
    {u v : Fin g.vertexCount} (p : AvoidPath g.HasArc failed u v) :
    ¬ failed u := by
  induction p with
  | refl u alive => exact alive
  | step u w v alive arc tail ih => exact alive

private theorem lca_root_dominates (r v : Fin g.vertexCount) :
    g.Dominates r r v := by
  intro p
  have hp : AvoidPath g.HasArc (fun x => x = r) r v := p
  exact lca_start_alive hp rfl

private theorem lca_avoid_or_prefix {failed : Fin g.vertexCount → Prop}
    {u v a : Fin g.vertexCount} (p : AvoidPath g.HasArc failed u v) :
    AvoidPath g.HasArc (fun x => x = a) u v ∨
      AvoidPath g.HasArc failed u a := by
  classical
  induction p with
  | refl u alive =>
      by_cases h : u = a
      · subst a
        exact Or.inr (AvoidPath.refl u alive)
      · exact Or.inl (AvoidPath.refl u h)
  | step u w v alive arc tail ih =>
      by_cases h : u = a
      · subst a
        exact Or.inr (AvoidPath.refl u alive)
      · rcases ih with hAvoid | hPrefix
        · exact Or.inl (AvoidPath.step u w v h arc hAvoid)
        · exact Or.inr (AvoidPath.step u w a alive arc hPrefix)

private theorem lca_dominates_trans {a b v : Fin g.vertexCount}
    (hab : g.Dominates r a b) (hbv : g.Dominates r b v) :
    g.Dominates r a v := by
  intro p
  have hp : AvoidPath g.HasArc (fun x => x = a) r v := p
  rcases lca_avoid_or_prefix (a := b) hp with hAvoid | hPrefix
  · exact hbv hAvoid
  · exact hab hPrefix

/-- Scan a finite enumeration, starting with an already feasible candidate. -/
private theorem lca_max_on_list {α : Type} (score : α → Nat)
    (feasible : α → Prop) (seed : α) (hseed : feasible seed)
    (ids : List α) :
    ∃ m, feasible m ∧ ∀ x ∈ ids, feasible x → score x ≤ score m := by
  classical
  induction ids with
  | nil =>
      refine ⟨seed, hseed, ?_⟩
      intro x hx _
      simp at hx
  | cons y ys ih =>
      obtain ⟨m, hm, hmax⟩ := ih
      by_cases hy : feasible y ∧ score m < score y
      · refine ⟨y, hy.1, ?_⟩
        intro x hx hfx
        rcases List.mem_cons.mp hx with hxy | hxs
        · subst x
          exact Nat.le_refl _
        · exact Nat.le_trans (hmax x hxs hfx) (Nat.le_of_lt hy.2)
      · refine ⟨m, hm, ?_⟩
        intro x hx hfx
        rcases List.mem_cons.mp hx with hxy | hxs
        · subst x
          have hn : ¬ score m < score y := fun h => hy ⟨hfx, h⟩
          omega
        · exact hmax x hxs hfx

theorem exists_unique_dominatorLCA_of_rank
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hne : vs ≠ []) (hReach : ∀ v ∈ vs, g.InitiallyReachable r v) :
    ∃ l, g.IsDominatorLCA r vs l ∧
      ∀ m, g.IsDominatorLCA r vs m → m = l := by
  -- Refinement breaks ties without assuming the supplied rank is injective.
  let score : Fin g.vertexCount → Nat := g.rankWithVertexIndex rank
  have hprogress : ∀ x y, g.HasArc x y → score x < score y := by
    intro x y hxy
    exact rankWithVertexIndex_lt_of_rank_lt (g := g) rank (progress x y hxy)
  have hinjective : ∀ ⦃x y : Fin g.vertexCount⦄, score x = score y → x = y :=
    rankWithVertexIndex_injective (g := g) rank
  let ids : List (Fin g.vertexCount) := List.ofFn (fun i : Fin g.vertexCount => i)
  have hID (x : Fin g.vertexCount) : x ∈ ids := by
    change x ∈ List.ofFn (fun i : Fin g.vertexCount => i)
    exact List.mem_ofFn.mpr ⟨x, rfl⟩
  have hroot : g.CommonDominator r vs r := by
    intro v _
    exact lca_root_dominates r v
  obtain ⟨l, hl, hmax⟩ :=
    lca_max_on_list score (g.CommonDominator r vs) r hroot ids
  have hmember : ∃ v, v ∈ vs := by
    cases vs with
    | nil => exact False.elim (hne rfl)
    | cons v tail => exact ⟨v, by simp⟩
  obtain ⟨v, hvMem⟩ := hmember
  have hv := hReach v hvMem
  have hlReach := initiallyReachable_of_dominates hv (hl v hvMem)
  have hlSpec : g.IsDominatorLCA r vs l := by
    refine ⟨hl, ?_⟩
    intro c hc
    -- A single reachable list member witnesses comparability.
    rcases dominators_comparable hprogress hinjective hv
        (hc v hvMem) (hl v hvMem) with hcl | hlc
    · exact hcl
    · by_cases he : l = c
      · subst c
        exact dominates_refl
      · have hcReach := initiallyReachable_of_dominates hv (hc v hvMem)
        have hlt := rank_lt_of_strict_dominator hprogress hcReach hlc he
        have hle := hmax c (hID c) hc
        omega
  refine ⟨l, hlSpec, ?_⟩
  intro m hm
  by_cases he : m = l
  · exact he
  · have hml : g.Dominates r m l := hlSpec.2 m hm.1
    have hlm : g.Dominates r l m := hm.2 l hl
    have hmReach := initiallyReachable_of_dominates hv (hm.1 v hvMem)
    have hlt₁ := rank_lt_of_strict_dominator hprogress hlReach hml he
    have hlt₂ := rank_lt_of_strict_dominator hprogress hmReach hlm (Ne.symm he)
    exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans hlt₁ hlt₂))

theorem exists_unique_dominatorLCA (hacyc : g.IsAcyclic)
    (hne : vs ≠ []) (hReach : ∀ v ∈ vs, g.InitiallyReachable r v) :
    ∃ l, g.IsDominatorLCA r vs l ∧
      ∀ m, g.IsDominatorLCA r vs m → m = l := by
  obtain ⟨rank, progress⟩ := hacyc
  exact exists_unique_dominatorLCA_of_rank progress hne hReach

noncomputable def dominatorLCA (g : Digraph) (r : Fin g.vertexCount)
    (vs : List (Fin g.vertexCount)) (hacyc : g.IsAcyclic)
    (hne : vs ≠ []) (hReach : ∀ v ∈ vs, g.InitiallyReachable r v) :
    Fin g.vertexCount :=
  Classical.choose (exists_unique_dominatorLCA hacyc hne hReach)

theorem dominatorLCA_spec (hacyc : g.IsAcyclic)
    (hne : vs ≠ []) (hReach : ∀ v ∈ vs, g.InitiallyReachable r v) :
    g.IsDominatorLCA r vs (g.dominatorLCA r vs hacyc hne hReach) :=
  (Classical.choose_spec (exists_unique_dominatorLCA hacyc hne hReach)).1

theorem eq_dominatorLCA_of_isDominatorLCA {l : Fin g.vertexCount}
    (hacyc : g.IsAcyclic) (hne : vs ≠ [])
    (hReach : ∀ v ∈ vs, g.InitiallyReachable r v)
    (hl : g.IsDominatorLCA r vs l) :
    l = g.dominatorLCA r vs hacyc hne hReach :=
  (Classical.choose_spec (exists_unique_dominatorLCA hacyc hne hReach)).2 l hl

theorem IsDominatorLCA.all_dominates_iff {l : Fin g.vertexCount}
    (hl : g.IsDominatorLCA r vs l) :
    (∀ v ∈ vs, g.Dominates r d v) ↔ g.Dominates r d l := by
  constructor
  · intro hd
    exact hl.2 d hd
  · intro hd v hv
    exact lca_dominates_trans hd (hl.1 v hv)

/-- Exact all-tail domination, for every nonempty reachable tail list. -/
theorem all_tail_dominates_iff_dominates_lca (hacyc : g.IsAcyclic)
    (hne : vs ≠ []) (hReach : ∀ v ∈ vs, g.InitiallyReachable r v) :
    (∀ v ∈ vs, g.Dominates r d v) ↔
      g.Dominates r d (g.dominatorLCA r vs hacyc hne hReach) :=
  IsDominatorLCA.all_dominates_iff (dominatorLCA_spec hacyc hne hReach)

@[simp] theorem dominatorLCA_singleton (hacyc : g.IsAcyclic)
    (v : Fin g.vertexCount) (hne : [v] ≠ [])
    (hReach : ∀ x ∈ [v], g.InitiallyReachable r x) :
    g.dominatorLCA r [v] hacyc hne hReach = v := by
  apply Eq.symm
  apply eq_dominatorLCA_of_isDominatorLCA hacyc hne hReach
  constructor
  · intro x hx
    have he : x = v := by simpa using hx
    subst x
    exact dominates_refl
  · intro c hc
    exact hc v (by simp)

/-- The pair LCA is uniquely characterized by its dominators. -/
theorem exists_unique_pair_dominatorLCA {a b : Fin g.vertexCount}
    (hacyc : g.IsAcyclic)
    (ha : g.InitiallyReachable r a) (hb : g.InitiallyReachable r b) :
    ∃ l,
      (∀ c, (g.Dominates r c a ∧ g.Dominates r c b) ↔
        g.Dominates r c l) ∧
      ∀ m, (∀ c, (g.Dominates r c a ∧ g.Dominates r c b) ↔
        g.Dominates r c m) → m = l := by
  have hrPair : ∀ x ∈ [a, b], g.InitiallyReachable r x := by
    intro x hx
    have he : x = a ∨ x = b := by simpa using hx
    rcases he with rfl | rfl
    · exact ha
    · exact hb
  have hPair (c : Fin g.vertexCount) :
      g.CommonDominator r [a, b] c ↔
        (g.Dominates r c a ∧ g.Dominates r c b) := by
    constructor
    · intro hc
      exact ⟨hc a (by simp), hc b (by simp)⟩
    · rintro ⟨hca, hcb⟩ x hx
      have he : x = a ∨ x = b := by simpa using hx
      rcases he with rfl | rfl
      · exact hca
      · exact hcb
  obtain ⟨l, hl, hunique⟩ :=
    exists_unique_dominatorLCA hacyc (by simp) hrPair
  refine ⟨l, ?_, ?_⟩
  · intro c
    exact (hPair c).symm.trans (IsDominatorLCA.all_dominates_iff (d := c) hl)
  · intro m hm
    apply hunique m
    refine ⟨(hPair m).mpr ((hm m).mpr dominates_refl), ?_⟩
    intro c hc
    exact (hm c).mp ((hPair c).mp hc)

end PaperB.Digraph
