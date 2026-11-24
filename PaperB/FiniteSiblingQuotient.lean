module

public import PaperB.SiblingEmissions
public import PaperB.QuotientArrays
public import PaperB.SiblingArcOwnership

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- Encode the endpoints of one emitted occurrence, leaving its physical tail intact. -/
noncomputable def encodeSiblingEmission (e : SiblingEmission g r d parent) :
    QuotientArrays.ArcOccurrence g.vertexCount (siblingBlockKeys g r d parent).length :=
  ⟨encodeSiblingBlockKey g r d parent e.source,
    encodeSiblingBlockKey g r d parent e.destination, e.tail⟩

/-- Map the original emission list without changing its order or multiplicities. -/
noncomputable def finiteSiblingOccurrences :
    List (QuotientArrays.ArcOccurrence g.vertexCount
      (siblingBlockKeys g r d parent).length) :=
  (siblingEmissions progress injective spec).map encodeSiblingEmission

private noncomputable def finiteSiblingRootKey
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (spec : ParentSpec g r parent) (hd : g.InitiallyReachable r d) :
    SiblingBlockKey g r d parent := by
  first
  | exact (siblingBlockSystem progress injective spec hd).block
      (⟨d, hd, by exact?⟩ : SiblingVertex g r d)
  | exact ⟨d, Or.inl rfl⟩
  | exact ⟨d, Or.inr rfl⟩
  | exact .root

/-- Group the encoded occurrences into finite adjacency rows. -/
noncomputable def finiteSiblingQuotient (hd : g.InitiallyReachable r d) :
    LabelledQuotient :=
  QuotientArrays.ofOccurrences
    (encodeSiblingBlockKey g r d parent (finiteSiblingRootKey progress injective spec hd))
    (finiteSiblingOccurrences progress injective spec)

private theorem encodeSiblingBlockKey_eq_iff
    (b : SiblingBlockKey g r d parent)
    (i : Fin (siblingBlockKeys g r d parent).length) :
    encodeSiblingBlockKey g r d parent b = i ↔
      b = decodeSiblingBlockKey g r d parent i := by
  constructor
  · intro h
    simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
      congrArg (decodeSiblingBlockKey g r d parent) h
  · intro h
    simpa only [encodeSiblingBlockKey_decodeSiblingBlockKey] using
      congrArg (encodeSiblingBlockKey g r d parent) h

/-- Outgoing membership matches the decoded endpoints and the original tail. -/
theorem mem_outArcs_finiteSiblingQuotient_iff
    (hd : g.InitiallyReachable r d)
    (u : Fin (siblingBlockKeys g r d parent).length)
    (a : QuotientArc g.vertexCount (siblingBlockKeys g r d parent).length) :
    a ∈ (finiteSiblingQuotient progress injective spec hd).outArcs u ↔
      ∃ e ∈ siblingEmissions progress injective spec,
        e.source = decodeSiblingBlockKey g r d parent u ∧
        e.destination = decodeSiblingBlockKey g r d parent a.head ∧
        e.tail = a.origTail := by
  unfold finiteSiblingQuotient
  rw [QuotientArrays.mem_outArcs_ofOccurrences]
  constructor
  · rintro ⟨o, ho, hs, ht, hx⟩
    change o ∈ (siblingEmissions progress injective spec).map encodeSiblingEmission at ho
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp ho
    exact ⟨e, he, (encodeSiblingBlockKey_eq_iff e.source u).mp hs,
      (encodeSiblingBlockKey_eq_iff e.destination a.head).mp ht, hx⟩
  · rintro ⟨e, he, hs, ht, hx⟩
    refine ⟨encodeSiblingEmission e, ?_, ?_, ?_, hx⟩
    · change encodeSiblingEmission e ∈
        (siblingEmissions progress injective spec).map encodeSiblingEmission
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    · exact (encodeSiblingBlockKey_eq_iff e.source u).mpr hs
    · exact (encodeSiblingBlockKey_eq_iff e.destination a.head).mpr ht

/-- Equivalently, an original arc occurrence emits exactly the decoded record. -/
theorem mem_outArcs_finiteSiblingQuotient_iff_raw
    (hd : g.InitiallyReachable r d)
    (u : Fin (siblingBlockKeys g r d parent).length)
    (a : QuotientArc g.vertexCount (siblingBlockKeys g r d parent).length) :
    a ∈ (finiteSiblingQuotient progress injective spec hd).outArcs u ↔
      ∃ raw ∈ g.originalArcOccurrences,
        siblingEmission? progress injective spec raw =
          some ⟨decodeSiblingBlockKey g r d parent u,
            decodeSiblingBlockKey g r d parent a.head, a.origTail⟩ := by
  rw [mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd u a]
  constructor
  · rintro ⟨⟨s, t, x⟩, he, hs, ht, hx⟩
    change s = decodeSiblingBlockKey g r d parent u at hs
    change t = decodeSiblingBlockKey g r d parent a.head at ht
    change x = a.origTail at hx
    subst s
    subst t
    subst x
    exact (mem_siblingEmissionsFrom_iff progress injective spec
      g.originalArcOccurrences _).mp he
  · intro h
    refine ⟨⟨decodeSiblingBlockKey g r d parent u,
      decodeSiblingBlockKey g r d parent a.head, a.origTail⟩, ?_, rfl, rfl, rfl⟩
    exact (mem_siblingEmissionsFrom_iff progress injective spec
      g.originalArcOccurrences _).mpr h

/-- Forgetting the tail label gives exactly the original sibling quotient edge. -/
theorem finiteSiblingQuotient_hasQuotientArc_iff
    (hd : g.InitiallyReachable r d)
    (u w : Fin (siblingBlockKeys g r d parent).length) :
    (finiteSiblingQuotient progress injective spec hd).HasQuotientArc u w ↔
      (siblingBlockSystem progress injective spec hd).QuotientEdge
        (decodeSiblingBlockKey g r d parent u)
        (decodeSiblingBlockKey g r d parent w) := by
  unfold LabelledQuotient.HasQuotientArc
  constructor
  · rintro ⟨a, ha, hw⟩
    obtain ⟨e, he, hs, ht, _⟩ :=
      (mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd u a).mp ha
    obtain ⟨hx, hstep⟩ :=
      (mem_siblingEmissions_iff_labelledStep progress injective spec hd e).mp he
    refine ⟨⟨e.tail, hx⟩, ?_⟩
    simpa only [hs, ht, hw] using hstep
  · rintro ⟨x, hstep⟩
    let e : SiblingEmission g r d parent :=
      ⟨decodeSiblingBlockKey g r d parent u,
        decodeSiblingBlockKey g r d parent w, x.val⟩
    have he : e ∈ siblingEmissions progress injective spec :=
      (mem_siblingEmissions_iff_labelledStep progress injective spec hd e).mpr
        ⟨x.property, hstep⟩
    refine ⟨⟨w, x.val⟩, ?_, rfl⟩
    exact (mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd u
      ⟨w, x.val⟩).mpr ⟨e, he, rfl, rfl, rfl⟩

/-- The rank at a finite index is the rank of its decoded block leader. -/
noncomputable def finiteSiblingRank (hd : g.InitiallyReachable r d)
    (u : Fin (siblingBlockKeys g r d parent).length) : Nat :=
  rank ((siblingBlockSystem progress injective spec hd).leader
    (decodeSiblingBlockKey g r d parent u)).val

theorem finiteSiblingRank_lt_of_hasQuotientArc
    (hd : g.InitiallyReachable r d)
    {u w : Fin (siblingBlockKeys g r d parent).length}
    (h : (finiteSiblingQuotient progress injective spec hd).HasQuotientArc u w) :
    finiteSiblingRank progress injective spec hd u <
      finiteSiblingRank progress injective spec hd w :=
  siblingBlockSystem_quotient_rank_lt progress injective spec hd
    ((finiteSiblingQuotient_hasQuotientArc_iff progress injective spec hd u w).mp h)

end PaperB.Digraph
