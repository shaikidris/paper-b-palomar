module

/- lean-toolchain: leanprover/lean4:v4.35.0-rc3 (bundled Std) -/
public import PaperB.SiblingPartition
public import Std

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.Digraph

/-- A key is the subtree root `d` or a reachable, non-self child of `d`. -/
def SiblingBlockKey (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount) :=
  {c : Fin g.vertexCount //
    c = d ∨ (parent c = d ∧ c ≠ d ∧ g.InitiallyReachable r c)}

def SiblingBlockKey.root (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount) :
    SiblingBlockKey g r d parent :=
  ⟨d, Or.inl rfl⟩

/-- The reachable original vertices in the dominator subtree at `d`. -/
def SiblingVertex (g : Digraph) (r d : Fin g.vertexCount) :=
  {v : Fin g.vertexCount // g.InitiallyReachable r v ∧ g.Dominates r d v}

/-- Enumerate actual keys by filtering the original finite vertex set. -/
noncomputable def siblingBlockKeys (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount) :
    List (SiblingBlockKey g r d parent) := by
  classical
  exact (List.ofFn (fun i : Fin g.vertexCount => i)).filterMap fun c =>
    if h : c = d ∨ (parent c = d ∧ c ≠ d ∧ g.InitiallyReachable r c) then
      some ⟨c, h⟩
    else
      none

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

theorem mem_siblingBlockKeys (c : SiblingBlockKey g r d parent) :
    c ∈ siblingBlockKeys g r d parent := by
  classical
  unfold siblingBlockKeys
  apply List.mem_filterMap.mpr
  refine ⟨c.val, List.mem_ofFn.mpr ⟨c.val, rfl⟩, ?_⟩
  simp only [dite_eq_left c.property] <;>
    first | rfl | exact congrArg some (Subtype.ext rfl)

private theorem sibling_child_ne_start (spec : ParentSpec g r parent)
    {c : Fin g.vertexCount} (hp : parent c = d) (hc : c ≠ d) :
    c ≠ r := by
  intro hcr
  subst c
  exact hc (spec.root.symm.trans hp)

/-- The leader is the original vertex named by the key. Reachability of `d`
is needed for the root key to have a leader in the subtree. -/
def siblingBlockLeader (spec : ParentSpec g r parent)
    (hd : g.InitiallyReachable r d) (c : SiblingBlockKey g r d parent) :
    SiblingVertex g r d :=
  ⟨c.val, by
    rcases c.property with h | ⟨hp, hc, hReach⟩
    · rw [h]
      exact ⟨hd, dominates_refl⟩
    · have hi := spec.immediate hReach (sibling_child_ne_start spec hp hc)
      refine ⟨hReach, ?_⟩
      simpa only [hp] using hi.2.1⟩

section Assignment

variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- Assign `d` to the root key and every other subtree vertex to its unique
dominating child key. This is a semantic assignment on original vertices. -/
noncomputable def siblingBlockOf (x : SiblingVertex g r d) :
    SiblingBlockKey g r d parent := by
  classical
  exact if hx : x.val = d then
    SiblingBlockKey.root g r d parent
  else
    let h := existsUnique_dominator_child progress injective spec
      x.property.1 x.property.2 hx
    let hc := (Classical.choose_spec h).1
    ⟨Classical.choose h, Or.inr ⟨hc.1, hc.2.1, hc.2.2.1⟩⟩

private theorem siblingBlockOf_child_spec (x : SiblingVertex g r d)
    (hx : x.val ≠ d) :
    let k := (siblingBlockOf progress injective spec x).val
    (parent k = d ∧ k ≠ d ∧ g.InitiallyReachable r k ∧
      g.Dominates r k x.val) ∧
      ∀ e : Fin g.vertexCount,
        (parent e = d ∧ e ≠ d ∧ g.InitiallyReachable r e ∧
          g.Dominates r e x.val) → e = k := by
  classical
  simpa [siblingBlockOf, hx] using
    (Classical.choose_spec
      (existsUnique_dominator_child progress injective spec
        x.property.1 x.property.2 hx))

theorem siblingBlockOf_eq_root_iff (x : SiblingVertex g r d) :
    siblingBlockOf progress injective spec x = SiblingBlockKey.root g r d parent ↔
      x.val = d := by
  constructor
  · intro h
    by_cases hx : x.val = d
    · exact hx
    · have hk := (siblingBlockOf_child_spec progress injective spec x hx).1.2.1
      exact False.elim
        (hk (congrArg (fun k : SiblingBlockKey g r d parent => k.val) h))
  · intro hx
    classical
    simp [siblingBlockOf, hx]

theorem siblingBlockOf_eq_child_iff (x : SiblingVertex g r d)
    (c : SiblingBlockKey g r d parent) (hc : c.val ≠ d) :
    siblingBlockOf progress injective spec x = c ↔ g.Dominates r c.val x.val := by
  have hChild : parent c.val = d ∧ c.val ≠ d ∧ g.InitiallyReachable r c.val := by
    rcases c.property with h | h
    · exact False.elim (hc h)
    · exact h
  obtain ⟨hp, _, hReach⟩ := hChild
  by_cases hx : x.val = d
  · have hRoot := (siblingBlockOf_eq_root_iff progress injective spec x).2 hx
    constructor
    · intro h
      exact False.elim
        (hc (congrArg (fun k : SiblingBlockKey g r d parent => k.val)
          (h.symm.trans hRoot)))
    · intro hDom
      have hdReach : g.InitiallyReachable r d := by
        simpa only [hx] using x.property.1
      have hcDom : g.Dominates r c.val d := by
        simpa only [hx] using hDom
      have hdc : rank d < rank c.val := by
        simpa only [hp] using
          (parent_reachable_rank_lt progress spec hReach
            (sibling_child_ne_start spec hp hc)).2
      have hcd := rank_lt_of_strict_dominator progress hdReach hcDom hc
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans hdc hcd))
  · have hs := siblingBlockOf_child_spec progress injective spec x hx
    constructor
    · intro h
      simpa only [h] using hs.1.2.2.2
    · intro hDom
      exact Subtype.ext (hs.2 c.val ⟨hp, hc, hReach, hDom⟩).symm

theorem siblingBlockOf_leader (hd : g.InitiallyReachable r d)
    (c : SiblingBlockKey g r d parent) :
    siblingBlockOf progress injective spec (siblingBlockLeader spec hd c) = c := by
  by_cases hc : c.val = d
  · have hKey : c = SiblingBlockKey.root g r d parent := Subtype.ext hc
    have hRoot :=
      (siblingBlockOf_eq_root_iff progress injective spec
        (siblingBlockLeader spec hd c)).2 hc
    exact hRoot.trans hKey.symm
  · apply (siblingBlockOf_eq_child_iff progress injective spec
      (siblingBlockLeader spec hd c) c hc).2
    change g.Dominates r c.val c.val
    exact dominates_refl

end Assignment

end PaperB.Digraph
