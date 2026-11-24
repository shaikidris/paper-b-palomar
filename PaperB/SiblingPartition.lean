module

public import PaperB.DominatorTree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

variable {g : Digraph} {r d v : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

private theorem exists_child_ancestor (h : Ancestor parent d v) :
    v ≠ d → ∃ c, parent c = d ∧ c ≠ d ∧ Ancestor parent c v := by
  induction h with
  | refl =>
      intro hne
      exact False.elim (hne rfl)
  | step w _ ih =>
      intro hne
      by_cases hp : parent w = d
      · exact ⟨w, hp, hne, Ancestor.refl⟩
      · obtain ⟨c, hc, hcd, hcw⟩ := ih hp
        exact ⟨c, hc, hcd, Ancestor.step w hcw⟩

/-- A reachable vertex distinct from its dominator lies below exactly one
reachable, non-self child of that dominator. -/
theorem existsUnique_dominator_child
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent)
    (hv : g.InitiallyReachable r v) (hd : g.Dominates r d v)
    (hvd : v ≠ d) :
    ∃ c : Fin g.vertexCount,
      (parent c = d ∧ c ≠ d ∧ g.InitiallyReachable r c ∧ g.Dominates r c v) ∧
      ∀ e : Fin g.vertexCount,
        (parent e = d ∧ e ≠ d ∧ g.InitiallyReachable r e ∧ g.Dominates r e v) →
        e = c := by
  have hAnc := (ancestor_iff_dominates progress spec hv).mpr hd
  obtain ⟨c, hpc, hcd, hcv⟩ := exists_child_ancestor hAnc hvd
  have hcDom := (ancestor_iff_dominates progress spec hv).mp hcv
  have hcReach := initiallyReachable_of_dominates hv hcDom
  have hdReach := initiallyReachable_of_dominates hv hd
  have child_nonroot {x : Fin g.vertexCount}
      (hp : parent x = d) (hxd : x ≠ d) : x ≠ r := by
    intro hxr
    subst x
    exact hxd (spec.root.symm.trans hp)
  have no_strict_domination {a b : Fin g.vertexCount}
      (hpa : parent a = d) (had : a ≠ d) (ha : g.InitiallyReachable r a)
      (hpb : parent b = d) (hbd : b ≠ d) (hb : g.InitiallyReachable r b)
      (hab : a ≠ b) (habDom : g.Dominates r a b) : False := by
    have hi := spec.immediate hb (child_nonroot hpb hbd)
    have haDom : g.Dominates r a d := by
      simpa only [hpb] using hi.2.2 a hab habDom
    have hdaLt : rank d < rank a := by
      simpa only [hpa] using
        (parent_reachable_rank_lt progress spec ha (child_nonroot hpa had)).2
    have hadLt := rank_lt_of_strict_dominator progress hdReach haDom had
    exact Nat.lt_irrefl _ (Nat.lt_trans hdaLt hadLt)
  refine ⟨c, ⟨hpc, hcd, hcReach, hcDom⟩, ?_⟩
  intro e he
  obtain ⟨hpe, hed, heReach, heDom⟩ := he
  by_cases hec : e = c
  · exact hec
  · rcases dominators_comparable progress injective hv heDom hcDom with hecDom | hceDom
    · exact False.elim
        (no_strict_domination hpe hed heReach hpc hcd hcReach hec hecDom)
    · exact False.elim
        (no_strict_domination hpc hcd hcReach hpe hed heReach (Ne.symm hec) hceDom)

end PaperB.Digraph
