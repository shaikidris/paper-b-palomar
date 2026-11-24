module

public import PaperB.Dom

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

private theorem avoid_or_split {V : Type} {edge : V → V → Prop}
    {failed : V → Prop} {u v d : V} (path : AvoidPath edge failed u v) :
    AvoidPath edge (fun x => failed x ∨ x = d) u v ∨
      (AvoidPath edge failed u d ∧ AvoidPath edge failed d v) := by
  classical
  induction path with
  | refl u alive =>
      by_cases h : u = d
      · subst d
        exact Or.inr ⟨AvoidPath.refl u alive, AvoidPath.refl u alive⟩
      · exact Or.inl (AvoidPath.refl u (fun hf => hf.elim alive h))
  | step u w v alive arc tail ih =>
      by_cases h : u = d
      · subst d
        exact Or.inr ⟨AvoidPath.refl u alive, AvoidPath.step u w v alive arc tail⟩
      · rcases ih with hAvoid | ⟨hPrefix, suffix⟩
        · exact Or.inl (AvoidPath.step u w v (fun hf => hf.elim alive h) arc hAvoid)
        · exact Or.inr ⟨AvoidPath.step u w d alive arc hPrefix, suffix⟩

variable {g : Digraph} {r a b d v : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}

private theorem split_of_dominates (hv : g.InitiallyReachable r v)
    (hd : g.Dominates r d v) :
    g.InitiallyReachable r d ∧ g.InitiallyReachable d v := by
  have path : AvoidPath g.HasArc (fun _ => False) r v := hv
  rcases avoid_or_split (d := d) path with hAvoid | hSplit
  · exact False.elim (hd (AvoidPath.mono hAvoid (fun _ he => Or.inr he)))
  · exact hSplit

theorem initiallyReachable_of_dominates (hv : g.InitiallyReachable r v)
    (hd : g.Dominates r d v) : g.InitiallyReachable r d :=
  (split_of_dominates hv hd).1

private theorem eq_or_rank_lt_of_path
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop} {u : Fin g.vertexCount}
    (path : AvoidPath g.HasArc failed u v) : u = v ∨ rank u < rank v := by
  induction path with
  | refl u _ => exact Or.inl rfl
  | step u w v _ arc _ ih =>
      rcases ih with he | hlt
      · subst v
        exact Or.inr (progress u w arc)
      · exact Or.inr (Nat.lt_trans (progress u w arc) hlt)

theorem rank_lt_of_strict_dominator
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hv : g.InitiallyReachable r v) (hd : g.Dominates r d v) (hdv : d ≠ v) :
    rank d < rank v := by
  have path : AvoidPath g.HasArc (fun _ => False) d v := (split_of_dominates hv hd).2
  rcases eq_or_rank_lt_of_path progress path with he | hlt
  · exact False.elim (hdv he)
  · exact hlt

private theorem avoid_of_rank_lt_start
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop} {u : Fin g.vertexCount}
    (path : AvoidPath g.HasArc failed u v) :
    rank a < rank u → AvoidPath g.HasArc (fun x => x = a) u v := by
  induction path with
  | refl u _ =>
      intro h
      exact AvoidPath.refl u (fun he => Nat.ne_of_lt h (congrArg rank he.symm))
  | step u w v _ arc _ ih =>
      intro h
      exact AvoidPath.step u w v
        (fun he => Nat.ne_of_lt h (congrArg rank he.symm))
        arc (ih (Nat.lt_trans h (progress u w arc)))

theorem dominates_of_rank_lt
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hv : g.InitiallyReachable r v) (ha : g.Dominates r a v)
    (hb : g.Dominates r b v) (hab : rank a < rank b) : g.Dominates r a b := by
  intro path
  have suffix : AvoidPath g.HasArc (fun _ => False) b v := (split_of_dominates hv hb).2
  exact ha (AvoidPath.trans path (avoid_of_rank_lt_start progress suffix hab))

theorem dominators_comparable
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (hv : g.InitiallyReachable r v) (ha : g.Dominates r a v)
    (hb : g.Dominates r b v) : g.Dominates r a b ∨ g.Dominates r b a := by
  rcases Nat.lt_trichotomy (rank a) (rank b) with h | h | h
  · exact Or.inl (dominates_of_rank_lt progress hv ha hb h)
  · have he : a = b := injective h
    subst b
    exact Or.inl dominates_refl
  · exact Or.inr (dominates_of_rank_lt progress hv hb ha h)

theorem initiallyReachable_suffix_of_dominates (hv : g.InitiallyReachable r v)
    (hd : g.Dominates r d v) : g.InitiallyReachable d v :=
  (split_of_dominates hv hd).2

theorem survivingPath_suffix_of_dominates {failed : Fin g.vertexCount → Prop}
    (path : g.SurvivingPath failed r v) (hd : g.Dominates r d v) :
    g.SurvivingPath failed d v := by
  have hPath : AvoidPath g.HasArc _ r v := path
  rcases avoid_or_split (d := d) hPath with hAvoid | ⟨_, suffix⟩
  · exact False.elim (hd (AvoidPath.mono hAvoid (fun _ he => Or.inr he)))
  · exact suffix

end PaperB.Digraph
