module

public import PaperB.LastExit

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph

/--
`hlca` is the characterization returned by
`exists_unique_pair_dominatorLCA g_acyclic ha hb`. In particular, neither
strictness of `d` nor distinctness of the two child blocks is assumed.
-/
theorem lemma22_incomparable_below_lca
    {g : Digraph} {r d a b : Fin g.vertexCount}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent)
    (ha : g.InitiallyReachable r a) (hb : g.InitiallyReachable r b)
    (hab : ¬ Ancestor parent a b) (hba : ¬ Ancestor parent b a)
    (hlca : ∀ c, (g.Dominates r c a ∧ g.Dominates r c b) ↔
      g.Dominates r c d) :
    ∃ A C : SiblingVertex g r d,
      A.val = a ∧ C.val = b ∧
      g.InitiallyReachable r d ∧
      Ancestor parent d a ∧ Ancestor parent d b ∧
      d ≠ a ∧ d ≠ b ∧
      (siblingBlockOf progress injective spec A).val ≠ d ∧
      (siblingBlockOf progress injective spec C).val ≠ d ∧
      siblingBlockOf progress injective spec A ≠
        siblingBlockOf progress injective spec C := by
  classical
  have endAlive {s t : Fin g.vertexCount}
      (p : AvoidPath g.HasArc (fun x => x = d) s t) : t ≠ d := by
    induction p with
    | refl u alive => exact alive
    | step u w v alive arc tail ih => exact ih
  have hdd : g.Dominates r d d := by
    change ¬ AvoidPath g.HasArc (fun x => x = d) r d
    intro p
    exact endAlive p rfl
  obtain ⟨hDomA, hDomB⟩ := (hlca d).2 hdd
  have hda := (ancestor_iff_dominates progress spec ha).2 hDomA
  have hdb := (ancestor_iff_dominates progress spec hb).2 hDomB
  have hdaNe : d ≠ a := by
    intro h
    exact hab (h ▸ hdb)
  have hdbNe : d ≠ b := by
    intro h
    exact hba (h ▸ hda)

  have prefixOrAvoid {s t : Fin g.vertexCount}
      (p : AvoidPath g.HasArc (fun _ => False) s t) :
      AvoidPath g.HasArc (fun _ => False) s d ∨
        AvoidPath g.HasArc (fun x => x = d) s t := by
    induction p with
    | refl u alive =>
        by_cases hu : u = d
        · subst u
          exact Or.inl (.refl _ alive)
        · exact Or.inr (.refl _ hu)
    | step u w v alive arc tail ih =>
        by_cases hu : u = d
        · subst u
          exact Or.inl (.refl _ alive)
        · rcases ih with p | p
          · exact Or.inl (.step _ _ _ alive arc p)
          · exact Or.inr (.step _ _ _ hu arc p)
  have hd : g.InitiallyReachable r d :=
    (prefixOrAvoid ha).resolve_right hDomA

  let A : SiblingVertex g r d := ⟨a, by
    first | exact ⟨ha, hDomA⟩ | exact ⟨hDomA, ha⟩⟩
  let C : SiblingVertex g r d := ⟨b, by
    first | exact ⟨hb, hDomB⟩ | exact ⟨hDomB, hb⟩⟩
  let D : SiblingVertex g r d := ⟨d, by
    first | exact ⟨hd, hdd⟩ | exact ⟨hdd, hd⟩⟩

  have childValueNe (X : SiblingVertex g r d) (hx : X.val ≠ d) :
      (siblingBlockOf progress injective spec X).val ≠ d := by
    intro he
    have hroot : siblingBlockOf progress injective spec X =
        SiblingBlockKey.root g r d parent := Subtype.ext he
    exact hx ((siblingBlockOf_eq_root_iff progress injective spec X).1 hroot)

  have hu := childValueNe A (Ne.symm hdaNe)
  have hv := childValueNe C (Ne.symm hdbNe)
  refine ⟨A, C, rfl, rfl, hd, hda, hdb, hdaNe, hdbNe, hu, hv, ?_⟩
  intro he
  let u := siblingBlockOf progress injective spec A
  have hua : g.Dominates r u.val a :=
    (siblingBlockOf_eq_child_iff progress injective spec A u hu).1 rfl
  have hub : g.Dominates r u.val b :=
    (siblingBlockOf_eq_child_iff progress injective spec C u hu).1 he.symm
  have hud : g.Dominates r u.val d := (hlca u.val).1 ⟨hua, hub⟩
  have hDu : siblingBlockOf progress injective spec D = u :=
    (siblingBlockOf_eq_child_iff progress injective spec D u hu).2 hud
  have hDr : siblingBlockOf progress injective spec D =
      SiblingBlockKey.root g r d parent :=
    (siblingBlockOf_eq_root_iff progress injective spec D).2 rfl
  exact hu (congrArg (fun k : SiblingBlockKey g r d parent => k.val)
    (hDu.symm.trans hDr))

theorem lemma22_swap_pair_failures
    {g : Digraph} {r a b t : Fin g.vertexCount} :
    g.SurvivingPath (fun x => x = a ∨ x = b) r t ↔
      g.SurvivingPath (fun x => x = b ∨ x = a) r t := by
  constructor <;> intro p
  · exact AvoidPath.mono p (fun _ h => h.elim Or.inr Or.inl)
  · exact AvoidPath.mono p (fun _ h => h.elim Or.inr Or.inl)

end PaperB.Digraph
