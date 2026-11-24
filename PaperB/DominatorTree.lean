module

public import PaperB.ImmediateDominator

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

/-- A parent map fixes the root and unreachable vertices, and assigns an
immediate dominator to every reachable nonroot. -/
structure ParentSpec (g : Digraph) (r : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount) : Prop where
  root : parent r = r
  nonroot : ∀ v, v ≠ r →
    (g.InitiallyReachable r v ∧ g.IsImmediateDominator r (parent v) v) ∨
    (¬ g.InitiallyReachable r v ∧ parent v = v)

/-- Inclusive ancestry, obtained by following parents from the descendant. -/
inductive Ancestor {V : Type} (parent : V → V) (d : V) : V → Prop where
  | refl : Ancestor parent d d
  | step (v : V) : Ancestor parent d (parent v) → Ancestor parent d v

variable {g : Digraph} {r v : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

theorem ParentSpec.immediate (spec : ParentSpec g r parent)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    g.IsImmediateDominator r (parent v) v := by
  rcases spec.nonroot v hvr with ⟨_, hi⟩ | ⟨hn, _⟩
  · exact hi
  · exact False.elim (hn hv)

theorem parent_reachable_rank_lt
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (spec : ParentSpec g r parent) (hv : g.InitiallyReachable r v)
    (hvr : v ≠ r) :
    g.InitiallyReachable r (parent v) ∧ rank (parent v) < rank v := by
  have hi := spec.immediate hv hvr
  exact ⟨initiallyReachable_of_dominates hv hi.2.1,
    rank_lt_of_strict_dominator progress hv hi.2.1 hi.1⟩

private theorem parent_dominates (spec : ParentSpec g r parent)
    (w : Fin g.vertexCount) : g.Dominates r (parent w) w := by
  by_cases hwr : w = r
  · subst w
    rw [spec.root]
    exact dominates_refl
  · rcases spec.nonroot w hwr with ⟨_, hi⟩ | ⟨_, he⟩
    · exact hi.2.1
    · rw [he]
      exact dominates_refl

private theorem ancestor_dominates (spec : ParentSpec g r parent)
    {d : Fin g.vertexCount} (h : Ancestor parent d v) :
    g.Dominates r d v := by
  induction h with
  | refl => exact dominates_refl
  | step w _ ih => exact dominates_trans ih (parent_dominates spec w)

theorem ancestor_iff_dominates
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (spec : ParentSpec g r parent) {d : Fin g.vertexCount}
    (hv : g.InitiallyReachable r v) :
    Ancestor parent d v ↔ g.Dominates r d v := by
  constructor
  · exact ancestor_dominates spec
  · let P (n : Nat) : Prop :=
      ∀ w, rank w = n → g.InitiallyReachable r w → g.Dominates r d w →
        Ancestor parent d w
    have allRanks (n : Nat) : P n := by
      refine Nat.strongRecOn (motive := P) n ?_
      intro k ih w hr hw hd
      by_cases hdw : d = w
      · cases hdw
        exact Ancestor.refl
      · by_cases hwr : w = r
        · subst w
          exact False.elim (hdw (dominates_source_iff.mp hd))
        · have hi := spec.immediate hw hwr
          obtain ⟨hp, hlt⟩ := parent_reachable_rank_lt progress spec hw hwr
          have hlt' : rank (parent w) < k := hr ▸ hlt
          exact Ancestor.step w
            (ih (rank (parent w)) hlt' (parent w) rfl hp (hi.2.2 d hdw hd))
    exact allRanks (rank v) v rfl hv

noncomputable def semanticParent
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (w : Fin g.vertexCount) : Fin g.vertexCount := by
  classical
  exact if hwr : w = r then r
    else if hw : g.InitiallyReachable r w then
      Classical.choose (existsUnique_immediateDominator progress injective hw hwr)
    else w

theorem semanticParent_spec
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y) :
    ParentSpec g r (semanticParent (r := r) progress injective) := by
  refine ⟨?_, ?_⟩
  · simp [semanticParent]
  · intro w hwr
    by_cases hw : g.InitiallyReachable r w
    · refine Or.inl ⟨hw, ?_⟩
      simpa only [semanticParent, dite_eq_right hwr, dite_eq_left hw] using
        (Classical.choose_spec
          (existsUnique_immediateDominator progress injective hw hwr)).1
    · exact Or.inr ⟨hw, by simp only [semanticParent, dite_eq_right hwr, dite_eq_right hw]⟩

theorem semanticParent_reachable_rank_lt
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    g.InitiallyReachable r (semanticParent (r := r) progress injective v) ∧
      rank (semanticParent (r := r) progress injective v) < rank v :=
  parent_reachable_rank_lt progress (semanticParent_spec progress injective) hv hvr

theorem semanticParent_ancestor_iff_dominates
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    {d : Fin g.vertexCount} (hv : g.InitiallyReachable r v) :
    Ancestor (semanticParent (r := r) progress injective) d v ↔ g.Dominates r d v :=
  ancestor_iff_dominates progress (semanticParent_spec progress injective) hv

end PaperB.Digraph
