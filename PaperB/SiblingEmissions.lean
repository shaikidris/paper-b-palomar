module

public import PaperB.SiblingBlockSystem
public import PaperB.SiblingEncoding

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph

/-- Enumerate the original arc occurrences in tail order and then in outgoing-list
order. Parallel arcs remain separate entries. -/
def originalArcOccurrences (g : Digraph) :
    List (Fin g.vertexCount × Fin g.vertexCount) :=
  (List.ofFn (fun u : Fin g.vertexCount => u)).flatMap
    (fun u => (g.outArcs u).map (fun v => (u, v)))

theorem mem_originalArcOccurrences_iff (g : Digraph)
    (u v : Fin g.vertexCount) :
    (u, v) ∈ g.originalArcOccurrences ↔ g.HasArc u v := by
  unfold originalArcOccurrences HasArc
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨x, _, hx⟩
    obtain ⟨y, hy, hxy⟩ := List.mem_map.mp hx
    have hxu : x = u := congrArg Prod.fst hxy
    have hyv : y = v := congrArg Prod.snd hxy
    simpa only [hxu, hyv] using hy
  · intro hv
    refine ⟨u, ?_, List.mem_map.mpr ⟨v, hv, rfl⟩⟩
    exact List.mem_ofFn.mpr ⟨u, rfl⟩

/-- A crossing carries its two block keys and the physical tail of the original
arc, not necessarily the leader of the source block. -/
structure SiblingEmission (g : Digraph) (r d : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount) where
  source : SiblingBlockKey g r d parent
  destination : SiblingBlockKey g r d parent
  tail : Fin g.vertexCount

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- Emit exactly when both endpoints are sibling vertices and their blocks
differ. This function uses the semantic block assignment. -/
noncomputable def siblingEmission?
    (a : Fin g.vertexCount × Fin g.vertexCount) :
    Option (SiblingEmission g r d parent) := by
  classical
  exact
    if hu : g.InitiallyReachable r a.1 ∧ g.Dominates r d a.1 then
      if hv : g.InitiallyReachable r a.2 ∧ g.Dominates r d a.2 then
        let c := siblingBlockOf progress injective spec (⟨a.1, hu⟩ : SiblingVertex g r d)
        let b := siblingBlockOf progress injective spec (⟨a.2, hv⟩ : SiblingVertex g r d)
        if c ≠ b then some ⟨c, b, a.1⟩ else none
      else none
    else none

theorem siblingEmission?_eq_some_iff
    (a : Fin g.vertexCount × Fin g.vertexCount)
    (e : SiblingEmission g r d parent) :
    siblingEmission? progress injective spec a = some e ↔
      ∃ (hu : g.InitiallyReachable r a.1 ∧ g.Dominates r d a.1)
        (hv : g.InitiallyReachable r a.2 ∧ g.Dominates r d a.2),
        siblingBlockOf progress injective spec (⟨a.1, hu⟩ : SiblingVertex g r d) ≠
          siblingBlockOf progress injective spec (⟨a.2, hv⟩ : SiblingVertex g r d) ∧
        (⟨siblingBlockOf progress injective spec (⟨a.1, hu⟩ : SiblingVertex g r d),
          siblingBlockOf progress injective spec (⟨a.2, hv⟩ : SiblingVertex g r d),
          a.1⟩ : SiblingEmission g r d parent) = e := by
  classical
  constructor
  · intro he
    by_cases hu : g.InitiallyReachable r a.1 ∧ g.Dominates r d a.1
    · by_cases hv : g.InitiallyReachable r a.2 ∧ g.Dominates r d a.2
      · by_cases hne :
            siblingBlockOf progress injective spec (⟨a.1, hu⟩ : SiblingVertex g r d) ≠
              siblingBlockOf progress injective spec (⟨a.2, hv⟩ : SiblingVertex g r d)
        · refine ⟨hu, hv, hne, ?_⟩
          apply Option.some.inj
          simpa only [siblingEmission?, dite_eq_left hu, dite_eq_left hv, ite_eq_left hne] using he
        · simp only [siblingEmission?, dite_eq_left hu, dite_eq_left hv, ite_eq_right hne] at he <;>
            cases he
      · simp only [siblingEmission?, dite_eq_left hu, dite_eq_right hv] at he <;> cases he
    · simp only [siblingEmission?, dite_eq_right hu] at he <;> cases he
  · rintro ⟨hu, hv, hne, hrecord⟩
    simpa only [siblingEmission?, dite_eq_left hu, dite_eq_left hv, ite_eq_left hne] using
      congrArg some hrecord

/-- Filter the input occurrences without deduplicating the emitted records. -/
noncomputable def siblingEmissionsFrom
    (raw : List (Fin g.vertexCount × Fin g.vertexCount)) :
    List (SiblingEmission g r d parent) :=
  raw.filterMap (siblingEmission? progress injective spec)

theorem mem_siblingEmissionsFrom_iff
    (raw : List (Fin g.vertexCount × Fin g.vertexCount))
    (e : SiblingEmission g r d parent) :
    e ∈ siblingEmissionsFrom progress injective spec raw ↔
      ∃ a, a ∈ raw ∧ siblingEmission? progress injective spec a = some e := by
  unfold siblingEmissionsFrom
  exact List.mem_filterMap

/-- The semantic reference list on the original arc occurrences, not a fast
constructor. -/
noncomputable def siblingEmissions : List (SiblingEmission g r d parent) :=
  siblingEmissionsFrom progress injective spec g.originalArcOccurrences

/-- A reference-list record is present exactly when its original tail can be
attached to the sibling subtree and witnesses the stated labelled step. -/
theorem mem_siblingEmissions_iff_labelledStep
    (hd : g.InitiallyReachable r d) (e : SiblingEmission g r d parent) :
    e ∈ siblingEmissions progress injective spec ↔
      ∃ ht : g.InitiallyReachable r e.tail ∧ g.Dominates r d e.tail,
        BlockSystem.LabelledStep (siblingBlockSystem progress injective spec hd)
          e.source e.destination ⟨e.tail, ht⟩ := by
  unfold siblingEmissions
  rw [mem_siblingEmissionsFrom_iff]
  let S := siblingBlockSystem progress injective spec hd
  constructor
  · rintro ⟨⟨u, v⟩, hraw, he⟩
    obtain ⟨hu, hv, hne, heq⟩ :=
      (siblingEmission?_eq_some_iff progress injective spec (u, v) e).mp he
    let x : SiblingVertex g r d := ⟨u, hu⟩
    let y : SiblingVertex g r d := ⟨v, hv⟩
    have harc : S.arc x y := (mem_originalArcOccurrences_iff g u v).mp hraw
    have hcross : S.block x ≠ S.block y := hne
    have hentry : y = S.leader (S.block y) :=
      siblingBlockSystem_enter progress injective spec hd x y harc hcross
    have hout : S.arc x (S.leader (S.block y)) := by
      simpa only [← hentry] using harc
    have hrecord : (⟨S.block x, S.block y, u⟩ : SiblingEmission g r d parent) = e :=
      heq
    rw [← hrecord]
    exact ⟨hu, ⟨hcross, rfl, hout⟩⟩
  · rintro ⟨ht, hstep⟩
    let x : SiblingVertex g r d := ⟨e.tail, ht⟩
    let y : SiblingVertex g r d := S.leader e.destination
    have hx : S.block x = e.source := hstep.tail_block
    have hy : S.block y = e.destination := S.leader_block e.destination
    have harc : g.HasArc x.val y.val := hstep.out_arc
    have hne : S.block x ≠ S.block y := by
      simpa only [hx, hy] using hstep.distinct
    refine ⟨(x.val, y.val), (mem_originalArcOccurrences_iff g x.val y.val).mpr harc, ?_⟩
    apply (siblingEmission?_eq_some_iff progress injective spec (x.val, y.val) e).mpr
    refine ⟨x.property, y.property, hne, ?_⟩
    change (⟨S.block x, S.block y, e.tail⟩ : SiblingEmission g r d parent) = e
    rw [hx, hy] <;> cases e <;> rfl

end PaperB.Digraph
