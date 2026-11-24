module

public import PaperB.DominatorTree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph

variable {g : Digraph}

/-- Break rank ties by vertex index, using the vertex count as the block width.
The resulting rank still takes values in `Nat`, with no finite ordinal bound. -/
def rankWithVertexIndex (g : Digraph) (rank : Fin g.vertexCount → Nat)
    (v : Fin g.vertexCount) : Nat :=
  rank v * g.vertexCount + v.val

theorem rankWithVertexIndex_lt_of_rank_lt (rank : Fin g.vertexCount → Nat)
    {x y : Fin g.vertexCount} (h : rank x < rank y) :
    g.rankWithVertexIndex rank x < g.rankWithVertexIndex rank y := by
  change rank x * g.vertexCount + x.val < rank y * g.vertexCount + y.val
  have hstep : rank x + 1 ≤ rank y := Nat.succ_le_of_lt h
  calc
    rank x * g.vertexCount + x.val
        < rank x * g.vertexCount + g.vertexCount :=
          Nat.add_lt_add_left x.isLt _
    _ = (rank x + 1) * g.vertexCount := by
          rw [Nat.add_mul, Nat.one_mul]
    _ ≤ rank y * g.vertexCount :=
          Nat.mul_le_mul_right g.vertexCount hstep
    _ ≤ rank y * g.vertexCount + y.val := by
          simpa only [Nat.add_zero] using
            (Nat.add_le_add_left (Nat.zero_le y.val) (rank y * g.vertexCount))

/-- The refined rank orders vertices lexicographically by rank and index. -/
theorem rankWithVertexIndex_lt_iff (rank : Fin g.vertexCount → Nat)
    {x y : Fin g.vertexCount} :
    g.rankWithVertexIndex rank x < g.rankWithVertexIndex rank y ↔
      rank x < rank y ∨ (rank x = rank y ∧ x.val < y.val) := by
  constructor
  · intro hxy
    rcases Nat.lt_trichotomy (rank x) (rank y) with hlt | heq | hgt
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      change rank x * g.vertexCount + x.val < rank y * g.vertexCount + y.val at hxy
      rw [heq] at hxy
      exact Nat.lt_of_add_lt_add_left hxy
    · have hyx := rankWithVertexIndex_lt_of_rank_lt (g := g) rank hgt
      exact False.elim (Nat.lt_irrefl _ (Nat.lt_trans hxy hyx))
  · intro h
    rcases h with hlt | ⟨heq, hval⟩
    · exact rankWithVertexIndex_lt_of_rank_lt (g := g) rank hlt
    · change rank x * g.vertexCount + x.val < rank y * g.vertexCount + y.val
      rw [heq]
      exact Nat.add_lt_add_left hval _

theorem rankWithVertexIndex_injective (rank : Fin g.vertexCount → Nat) :
    ∀ ⦃x y : Fin g.vertexCount⦄,
      g.rankWithVertexIndex rank x = g.rankWithVertexIndex rank y → x = y := by
  intro x y hxy
  rcases Nat.lt_trichotomy (rank x) (rank y) with hlt | heq | hgt
  · have h := rankWithVertexIndex_lt_of_rank_lt (g := g) rank hlt
    rw [hxy] at h
    exact False.elim (Nat.lt_irrefl _ h)
  · apply Fin.ext
    change rank x * g.vertexCount + x.val = rank y * g.vertexCount + y.val at hxy
    rw [heq] at hxy
    exact Nat.add_left_cancel hxy
  · have h := rankWithVertexIndex_lt_of_rank_lt (g := g) rank hgt
    rw [← hxy] at h
    exact False.elim (Nat.lt_irrefl _ h)

theorem IsAcyclic.exists_injective_rank (h : g.IsAcyclic) :
    ∃ rank : Fin g.vertexCount → Nat,
      (∀ x y : Fin g.vertexCount, g.HasArc x y → rank x < rank y) ∧
      (∀ ⦃x y : Fin g.vertexCount⦄, rank x = rank y → x = y) := by
  rcases h with ⟨rank, progress⟩
  refine ⟨g.rankWithVertexIndex rank, ?_,
    rankWithVertexIndex_injective (g := g) rank⟩
  intro x y harc
  exact rankWithVertexIndex_lt_of_rank_lt (g := g) rank (progress x y harc)

/-- One refined rank gives a semantic parent map for every root of the same
graph. The ancestry equivalence applies to every reachable target, with no
exception for the root. -/
theorem IsAcyclic.exists_semantic_parent_family (h : g.IsAcyclic) :
    ∃ parent : Fin g.vertexCount → Fin g.vertexCount → Fin g.vertexCount,
      ∀ r d v : Fin g.vertexCount, g.InitiallyReachable r v →
        (Ancestor (parent r) d v ↔ g.Dominates r d v) := by
  rcases IsAcyclic.exists_injective_rank h with ⟨rank, progress, injective⟩
  refine ⟨fun r => semanticParent (g := g) (r := r) progress injective, ?_⟩
  intro r d v hv
  exact semanticParent_ancestor_iff_dominates (g := g) (r := r)
    progress injective (d := d) hv

/-- The semantic parent map for a specified source vertex. -/
theorem IsAcyclic.exists_semantic_parent (h : g.IsAcyclic)
    (r : Fin g.vertexCount) :
    ∃ parent : Fin g.vertexCount → Fin g.vertexCount,
      ∀ d v : Fin g.vertexCount, g.InitiallyReachable r v →
        (Ancestor parent d v ↔ g.Dominates r d v) := by
  rcases IsAcyclic.exists_semantic_parent_family h with ⟨parent, hparent⟩
  exact ⟨parent r, hparent r⟩

end PaperB.Digraph
