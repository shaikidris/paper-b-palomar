module

-- Lean v4.35.0-rc3
public import Std
public import PaperB.DominatorChain

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

private theorem exists_rank_max {α : Type} (rank : α → Nat)
    (p : α → Prop) (xs : List α) (hw : ∃ x, x ∈ xs ∧ p x) :
    ∃ x, x ∈ xs ∧ p x ∧ ∀ y, y ∈ xs → p y → rank y ≤ rank x := by
  letI : (q : Prop) → Decidable q := Classical.propDecidable
  induction xs with
  | nil =>
      obtain ⟨x, hx, _⟩ := hw
      simp at hx
  | cons a xs ih =>
      simp only [List.mem_cons] at hw ⊢
      by_cases ht : ∃ x, x ∈ xs ∧ p x
      · obtain ⟨b, hb, hpb, hmax⟩ := ih ht
        by_cases ha : p a ∧ rank b ≤ rank a
        · refine ⟨a, Or.inl rfl, ha.1, ?_⟩
          rintro y (rfl | hy) hpy
          · exact Nat.le_refl _
          · exact Nat.le_trans (hmax y hy hpy) ha.2
        · refine ⟨b, Or.inr hb, hpb, ?_⟩
          rintro y (rfl | hy) hpy
          · exact Nat.le_of_not_gt (fun h => ha ⟨hpy, Nat.le_of_lt h⟩)
          · exact hmax y hy hpy
      · have hpa : p a := by
          rcases hw with ⟨y, (rfl | hy), hpy⟩
          · exact hpy
          · exact False.elim (ht ⟨y, hy, hpy⟩)
        refine ⟨a, Or.inl rfl, hpa, ?_⟩
        rintro y (rfl | hy) hpy
        · exact Nat.le_refl _
        · exact False.elim (ht ⟨y, hy, hpy⟩)

def IsImmediateDominator (g : Digraph) (r d v : Fin g.vertexCount) : Prop :=
  d ≠ v ∧ g.Dominates r d v ∧
    ∀ a, a ≠ v → g.Dominates r a v → g.Dominates r a d

theorem existsUnique_immediateDominator {g : Digraph} {r v : Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (hv : g.InitiallyReachable r v) (hvr : v ≠ r) :
    ∃ d, g.IsImmediateDominator r d v ∧
      ∀ e, g.IsImmediateDominator r e v → e = d := by
  let vertices := List.ofFn (fun i : Fin g.vertexCount => i)
  have hmem (i : Fin g.vertexCount) : i ∈ vertices :=
    List.mem_ofFn.mpr ⟨i, rfl⟩
  let p (i : Fin g.vertexCount) : Prop := i ≠ v ∧ g.Dominates r i v
  have hw : ∃ i, i ∈ vertices ∧ p i :=
    ⟨r, hmem r, Ne.symm hvr, source_dominates⟩
  obtain ⟨d, _, ⟨hdv, hd⟩, hmax⟩ := exists_rank_max rank p vertices hw
  have reach {x : Fin g.vertexCount} (hx : g.Dominates r x v) :
      g.InitiallyReachable r x :=
    initiallyReachable_of_dominates hv hx
  have strongest : ∀ a, a ≠ v → g.Dominates r a v → g.Dominates r a d := by
    intro a hav ha
    rcases dominators_comparable progress injective hv ha hd with had | hda
    · exact had
    · by_cases h : a = d
      · subst a
        exact dominates_refl
      · have hlt := rank_lt_of_strict_dominator progress (reach ha) hda (Ne.symm h)
        exact False.elim (Nat.not_lt_of_ge (hmax a (hmem a) ⟨hav, ha⟩) hlt)
  refine ⟨d, ⟨hdv, hd, strongest⟩, ?_⟩
  intro e he
  unfold IsImmediateDominator at he
  obtain ⟨hev, heDom, heStrong⟩ := he
  by_cases h : e = d
  · exact h
  · have hed := rank_lt_of_strict_dominator progress (reach hd) (strongest e hev heDom) h
    have hde := rank_lt_of_strict_dominator progress (reach heDom)
      (heStrong d hdv hd) (Ne.symm h)
    exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans hed hde))

end PaperB.Digraph
