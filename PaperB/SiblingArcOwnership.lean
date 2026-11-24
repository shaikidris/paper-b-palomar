module

public import PaperB.SiblingBlockSystem

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
namespace Digraph

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- A represented crossing enters a non-root leader whose parent owns the edge. -/
theorem siblingBlockSystem_crossing_owner (hd : g.InitiallyReachable r d)
    (u v : SiblingVertex g r d) (harc : g.HasArc u.val v.val)
    (hne : siblingBlockOf progress injective spec u ≠
      siblingBlockOf progress injective spec v) :
    v = siblingBlockLeader spec hd (siblingBlockOf progress injective spec v) ∧
      v.val ≠ d ∧ parent v.val = d := by
  let c := siblingBlockOf progress injective spec v
  have henter : v = siblingBlockLeader spec hd c :=
    siblingBlockSystem_enter progress injective spec hd u v harc hne
  have hval : v.val = c.val :=
    congrArg (fun x : SiblingVertex g r d => x.val) henter
  have hdu : rank d ≤ rank u.val := by
    by_cases h : d = u.val
    · simpa only [h] using (Nat.le_refl (rank u.val))
    · exact Nat.le_of_lt
        (rank_lt_of_strict_dominator progress u.property.1 u.property.2 h)
  have hvd : v.val ≠ d := by
    intro h
    have hlt : rank u.val < rank d := by
      simpa only [h] using (progress u.val v.val harc)
    exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hdu hlt)
  refine ⟨henter, hvd, ?_⟩
  rcases c.property with hc | hc
  · exact (hvd (hval.trans hc)).elim
  · exact (congrArg parent hval).trans hc.1

/-- Two crossing representations of the same physical edge have the same
owner: equality of heads already suffices. This does not identify parallel
input occurrences, which can still be counted separately. -/
theorem siblingBlockSystem_owner_unique {d₁ d₂ : Fin g.vertexCount}
    (hd₁ : g.InitiallyReachable r d₁) (hd₂ : g.InitiallyReachable r d₂)
    {u₁ v₁ : SiblingVertex g r d₁} {u₂ v₂ : SiblingVertex g r d₂}
    (ha₁ : g.HasArc u₁.val v₁.val) (ha₂ : g.HasArc u₂.val v₂.val)
    (hn₁ : siblingBlockOf progress injective spec u₁ ≠
      siblingBlockOf progress injective spec v₁)
    (hn₂ : siblingBlockOf progress injective spec u₂ ≠
      siblingBlockOf progress injective spec v₂)
    (hhead : v₁.val = v₂.val) : d₁ = d₂ := by
  have hp₁ := (siblingBlockSystem_crossing_owner
    progress injective spec hd₁ u₁ v₁ ha₁ hn₁).2.2
  have hp₂ := (siblingBlockSystem_crossing_owner
    progress injective spec hd₂ u₂ v₂ ha₂ hn₂).2.2
  exact hp₁.symm.trans ((congrArg parent hhead).trans hp₂)

include progress in
private theorem siblingArc_path_rank_le
    {failed : SiblingVertex g r d → Prop} {u v : SiblingVertex g r d}
    (p : AvoidPath (fun x y : SiblingVertex g r d => g.HasArc x.val y.val)
      failed u v) : rank u.val ≤ rank v.val := by
  induction p with
  | refl u _ => exact Nat.le_refl _
  | step u w v _ harc _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (progress u.val w.val harc)) ih

/-- A quotient arc strictly increases the rank of its block leaders. -/
theorem siblingBlockSystem_quotient_rank_lt (hd : g.InitiallyReachable r d)
    {s t : SiblingBlockKey g r d parent}
    (h : (siblingBlockSystem progress injective spec hd).QuotientEdge s t) :
    rank ((siblingBlockSystem progress injective spec hd).leader s).val <
      rank ((siblingBlockSystem progress injective spec hd).leader t).val := by
  let S := siblingBlockSystem progress injective spec hd
  change S.QuotientEdge s t at h
  change rank (S.leader s).val < rank (S.leader t).val
  have across (u v : SiblingVertex g r d) (hu : S.block u = s)
      (hv : S.block v = t) (ha : S.arc u v) (hne : S.block u ≠ S.block v) :
      rank (S.leader s).val < rank (S.leader t).val := by
    have hle : rank (S.leader s).val ≤ rank u.val := by
      rw [← hu]
      let c := S.block u
      have hp : AvoidPath S.arc (fun z : SiblingVertex g r d => S.block z ≠ S.block u) (S.leader (S.block u)) u := S.internal c u rfl
      exact siblingArc_path_rank_le (r := r) (d := d) progress hp
    have he : v = S.leader t := by
      rw [← hv]
      exact siblingBlockSystem_enter progress injective spec hd u v ha hne
    rw [← he]
    exact Nat.lt_of_le_of_lt hle (progress u.val v.val ha)
  rcases h with ⟨u, hu⟩
  apply across u (S.leader t) hu.tail_block (S.leader_block t) hu.out_arc
  rw [hu.tail_block, S.leader_block t]
  exact hu.distinct

end Digraph
end PaperB
