module

public import PaperB.FiniteSiblingFlat
public import PaperB.QuotientArrayCounts
public import PaperB.QuotientBudget

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph

section

variable {g : Digraph} {r : Fin g.vertexCount}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- Erase the dependent emission record, keeping one output per crossing
occurrence. The guard rejects pairs that are not arcs of the original graph. -/
noncomputable def siblingBudgetEmit
    (d : {v : Fin g.vertexCount // g.InitiallyReachable r v})
    (a : Fin g.vertexCount × Fin g.vertexCount) : Option Unit := by
  classical
  exact if g.HasArc a.1 a.2 then
    (siblingEmission? (d := d.val) progress injective spec a).map (fun _ => ())
  else none

theorem siblingBudgetEmit_owner
    (d : {v : Fin g.vertexCount // g.InitiallyReachable r v})
    {a : Fin g.vertexCount × Fin g.vertexCount} {b : Unit}
    (he : siblingBudgetEmit progress injective spec d a = some b) :
    parent a.2 = d.val := by
  classical
  by_cases ha : g.HasArc a.1 a.2
  · cases hs : siblingEmission? (d := d.val) progress injective spec a with
    | none =>
        simp [siblingBudgetEmit, ha, hs] at he
    | some e =>
        obtain ⟨hu, hv, hne, _⟩ :=
          (siblingEmission?_eq_some_iff progress injective spec a e).mp hs
        exact (siblingBlockSystem_crossing_owner progress injective spec
          d.property (⟨a.1, hu⟩ : SiblingVertex g r d.val)
          (⟨a.2, hv⟩ : SiblingVertex g r d.val) ha hne).2.2
  · simp [siblingBudgetEmit, ha] at he

theorem siblingBudgetEmit_unique
    {d₁ d₂ : {v : Fin g.vertexCount // g.InitiallyReachable r v}}
    {a : Fin g.vertexCount × Fin g.vertexCount} {b₁ b₂ : Unit}
    (h₁ : siblingBudgetEmit progress injective spec d₁ a = some b₁)
    (h₂ : siblingBudgetEmit progress injective spec d₂ a = some b₂) :
    d₁ = d₂ := by
  apply Subtype.ext
  exact (siblingBudgetEmit_owner progress injective spec d₁ h₁).symm.trans
    (siblingBudgetEmit_owner progress injective spec d₂ h₂)

private theorem siblingBudget_filterMap_length_congr
    {A B C : Type _} (xs : List A) (f : A → Option B) (h : A → Option C)
    (hm : ∀ a ∈ xs, (f a).isSome = (h a).isSome) :
    (xs.filterMap f).length = (xs.filterMap h).length := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hhead := hm a (by simp)
      have htail := ih (fun x hx => hm x (List.mem_cons_of_mem _ hx))
      cases hf : f a <;> cases hh : h a <;>
        simp [hf, hh] at hhead <;>
        simp [List.filterMap, hf, hh, htail]

theorem siblingBudgetEmit_filterMap_length
    (d : {v : Fin g.vertexCount // g.InitiallyReachable r v}) :
    (g.originalArcOccurrences.filterMap
      (siblingBudgetEmit progress injective spec d)).length =
      (finiteSiblingOccurrences (d := d.val) progress injective spec).length := by
  classical
  simp only [finiteSiblingOccurrences, List.length_map, siblingEmissions]
  apply siblingBudget_filterMap_length_congr
  intro a ha
  have harc : g.HasArc a.1 a.2 :=
    (mem_originalArcOccurrences_iff g a.1 a.2).mp ha
  simp only [siblingBudgetEmit, ite_eq_left harc]
  cases siblingEmission? (d := d.val) progress injective spec a <;> rfl

/-- The actual quotient arc counts are bounded by the number of input
occurrences, including parallel occurrences. -/
theorem sum_finiteSiblingQuotient_arcCount_le_occurrences
    (roots : List {v : Fin g.vertexCount // g.InitiallyReachable r v})
    (hn : roots.Nodup) :
    (roots.map (fun d =>
      (finiteSiblingQuotient progress injective spec d.property).arcCount)).sum
      ≤ g.originalArcOccurrences.length := by
  have hcount (d : {v : Fin g.vertexCount // g.InitiallyReachable r v}) :
      (finiteSiblingQuotient progress injective spec d.property).arcCount =
        (g.originalArcOccurrences.filterMap
          (siblingBudgetEmit progress injective spec d)).length := by
    simpa only [finiteSiblingQuotient, PaperB.arcCount_ofOccurrences] using
      (siblingBudgetEmit_filterMap_length progress injective spec d).symm
  simp only [hcount]
  exact PaperB.QuotientBudget.sum_filterMap_length_le_length_of_nodup
    roots g.originalArcOccurrences (siblingBudgetEmit progress injective spec)
    hn (fun h₁ h₂ => siblingBudgetEmit_unique progress injective spec h₁ h₂)

end

private theorem siblingBudget_flatMap_row_length
    {A B : Type _} (xs : List A) (row : A → List B) :
    (xs.flatMap (fun u => (row u).map (fun v => (u, v)))).length =
      ((xs.map row).map List.length).sum := by
  induction xs with
  | nil => rfl
  | cons u xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.map_cons,
        List.length_map, List.sum_cons, ih]

theorem originalArcOccurrences_length_eq_arcCount_forSiblingBudget
    (g : Digraph) : g.originalArcOccurrences.length = g.arcCount := by
  have hrows :
      (List.ofFn (fun u : Fin g.vertexCount => u)).map g.outArcs =
        List.ofFn g.outArcs := by
    simp only [List.map_ofFn, Function.comp_def]
  calc
    g.originalArcOccurrences.length =
        (((List.ofFn (fun u : Fin g.vertexCount => u)).map g.outArcs).map
          List.length).sum :=
      siblingBudget_flatMap_row_length _ g.outArcs
    _ = ((List.ofFn g.outArcs).map List.length).sum := by rw [hrows]
    _ = g.arcCount := by
      have hrowsArray : List.ofFn g.outArcs = g.adj.toList := by
        apply List.ext_getElem
        · simp [g.adj_size]
        · intro i hi hj
          simp [List.getElem_ofFn, Digraph.outArcs]
      have h (rows : List (List (Fin g.vertexCount))) :
          (rows.map List.length).sum = listLengthSum rows := by
        induction rows with
        | nil => rfl
        | cons row rows ih =>
            simpa [listLengthSum] using congrArg (Nat.add row.length) ih
      rw [hrowsArray]
      simpa only [arcCount] using h g.adj.toList

/-- Any duplicate-free list of reachable roots, in particular an enumeration
of all reachable roots, has total finite sibling quotient arc count at most
the original graph's arc count. -/
theorem sum_finiteSiblingQuotient_arcCount_le_arcCount
    {g : Digraph} {r : Fin g.vertexCount}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent)
    (roots : List {v : Fin g.vertexCount // g.InitiallyReachable r v})
    (hn : roots.Nodup) :
    (roots.map (fun d =>
      (finiteSiblingQuotient progress injective spec d.property).arcCount)).sum
      ≤ g.arcCount := by
  exact Nat.le_trans
    (sum_finiteSiblingQuotient_arcCount_le_occurrences progress injective spec roots hn)
    (Nat.le_of_eq (originalArcOccurrences_length_eq_arcCount_forSiblingBudget g))

end PaperB.Digraph
