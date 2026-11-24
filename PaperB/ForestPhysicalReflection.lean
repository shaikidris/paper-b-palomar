module

public import PaperB.ForestTopologicalTotal
public import PaperB.ForestCanonicalLaws

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB

open EX24 EX24.PreStep EX24.PreparedSweep LabelledQuotient ForestHead

section

variable {H : LabelledQuotient}
variable {c : Config H} {out : State H} {rank : Vertex H → Nat}
variable {F : JumpForest} {up : Fin F.size → Fin F.size}

/-- Look up an occupied real slot, checking the key in the physical back table.
This uses no forest traversal. Slot zero is reserved for the root. -/
def physicalPairSlot? (c : Config H) (t : Tables H) (q : CutPair H) :
    Option Nat :=
  match (PairLookup.lookup c.dict (c.code q)).1 with
  | none => none
  | some i =>
      let n := t.slotAt i
      if n = 0 then none
      else
        match t.back[n]? with
        | some (some stored) => if stored = q then some n else none
        | _ => none

theorem physicalPairSlot?_eq_some_iff {t : Tables H}
    (G : Grounded c F t) (q : CutPair H) (n : Nat) :
    physicalPairSlot? c t q = some n ↔ t.back[n]? = some (some q) := by
  constructor
  · intro h
    cases hi : (PairLookup.lookup c.dict (c.code q)).1 with
    | none => simp [physicalPairSlot?, hi] at h
    | some i =>
        by_cases hz : t.slotAt i = 0
        · simp [physicalPairSlot?, hi, hz] at h
        · obtain ⟨stored, _, hb⟩ := G.forward i hz
          by_cases he : stored = q
          · have hn : t.slotAt i = n := by
              simpa [physicalPairSlot?, hi, hz, hb, he] using h
            simpa only [hn, he] using hb
          · simp [physicalPairSlot?, hi, hz, hb, he] at h
  · intro hb
    obtain ⟨_, hn, i, hi, hs⟩ := G.backward n q hb
    simp [physicalPairSlot?, hi, hs, hn, hb]

theorem physicalPairSlot?_iff_image
    (G : Grounded c F out.tables)
    (E : Embedding c out F rank up (fun _ => True))
    (q : CutPair H) (n : Nat) :
    physicalPairSlot? c out.tables q = some n ↔
      ∃ a : Fin F.size, a.val = n ∧
        (buildProperLossForest H rank).nodeKey? (E.image a) = some q := by
  rw [physicalPairSlot?_eq_some_iff G q n]
  constructor
  · intro hb
    have hn : n < F.size := by
      simpa only [G.size_eq] using (G.backward n q hb).1
    let a : Fin F.size := ⟨n, hn⟩
    exact ⟨a, rfl, Option.some.inj ((E.back_eq a).symm.trans hb)⟩
  · rintro ⟨a, rfl, ha⟩
    exact (E.back_eq a).trans (congrArg some ha)

private theorem groundedRootLt (G : Grounded c F out.tables) :
    0 < F.size := by
  obtain ⟨_, inv⟩ := G.layout.valid.exists_forestInvariant
  exact inv.size_pos

private theorem finalImageClimb
    (E : Embedding c out F rank up (fun _ => True))
    (k : Nat) (b : Fin F.size) :
    E.image (climb up k b) =
      climb (buildProperLossForest H rank).parent k (E.image b) := by
  first
  | exact E.image_climb k b
  | exact image_climb E k b

private theorem physicalClimbVal
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (k : Nat) (b : Fin F.size) :
    (climb up k b).val = climb F.parentOf k b.val := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [climb, hUp, ih]

/-- Every final embedding is onto. A real node has a proper-loss witness,
so it lies on the inclusive parent chain of that witness's final label. -/
theorem Embedding.finalSurjective
    (E : Embedding c out F rank up (fun _ => True))
    (h0 : 0 < F.size)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v)
    (flat : H.IsFlat)
    (L : CanonicalLaws H rank) :
    Function.Surjective E.image := by
  intro a
  cases ha : (buildProperLossForest H rank).nodeKey? a with
  | none =>
      have hRoot : a = (buildProperLossForest H rank).rootNode :=
        buildProperLossForest_nodeKey?_inj H rank
          (ha.trans (buildProperLossForest_nodeKey?_root H rank).symm)
      exact ⟨⟨0, h0⟩, (E.root_eq h0).trans hRoot.symm⟩
  | some q =>
      obtain ⟨_, y, hy⟩ :=
        (buildProperLossForest_exists_node_iff rankArc flat q).mp ⟨a, ha⟩
      have hAnc :=
        (buildProperLossForest_properLoss_iff_of_node
          rankArc distinctRanks flat ha y).mp hy
      have hDepth : 0 < (buildProperLossForest H rank).depth a := by
        rw [buildProperLossForest_depth_real rankArc flat ha]
        omega
      obtain ⟨k, hk⟩ := (L.ancestor a _ hDepth).mp hAnc
      let b : Fin F.size := ⟨(selectors c out).label y, E.label_lt y True.intro⟩
      have hb : E.image b = (buildProperLossForest H rank).label y :=
        E.label_eq y True.intro
      exact ⟨climb up k b, (finalImageClimb E k b).trans (by
        simpa only [hb] using hk)⟩

private theorem physicalAncestor_iff
    (E : Embedding c out F rank up (fun _ => True))
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (L : CanonicalLaws H rank)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat)
    (a b : Fin F.size) {q : CutPair H}
    (ha : (buildProperLossForest H rank).nodeKey? (E.image a) = some q) :
    (∃ k, climb F.parentOf k b.val = a.val) ↔
      IsForestAncestor (buildProperLossForest H rank).parent
        (E.image a) (E.image b) := by
  have hDepth : 0 < (buildProperLossForest H rank).depth (E.image a) := by
    rw [buildProperLossForest_depth_real rankArc flat ha]
    omega
  rw [L.ancestor (E.image a) (E.image b) hDepth]
  constructor
  · rintro ⟨k, hk⟩
    have hab : climb up k b = a :=
      Fin.ext ((physicalClimbVal hUp k b).trans hk)
    exact ⟨k, (finalImageClimb E k b).symm.trans (congrArg E.image hab)⟩
  · rintro ⟨k, hk⟩
    have hab : climb up k b = a :=
      E.injective ((finalImageClimb E k b).trans hk)
    exact ⟨k, (physicalClimbVal hUp k b).symm.trans
      (congrArg (fun z : Fin F.size => z.val) hab)⟩

/-- Use the actual forest and embedding supplied by `OutputOK`. The `climb`
on physical slots specifies inclusive ancestry; it is not a runtime query. -/
theorem OutputOK.physicalReflection
    (h : OutputOK c rank out)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v)
    (flat : H.IsFlat) :
    ∃ (F : JumpForest) (up : Fin F.size → Fin F.size),
      Grounded c F out.tables ∧
      (∀ a : Fin F.size, (up a).val = F.parentOf a.val) ∧
      ∃ E : Embedding c out F rank up (fun _ => True),
        (∃ h0 : 0 < F.size,
          E.image ⟨0, h0⟩ = (buildProperLossForest H rank).rootNode) ∧
        Function.Surjective E.image ∧
        (∀ (q : CutPair H) (n : Nat),
          physicalPairSlot? c out.tables q = some n ↔
            ∃ a : Fin F.size, a.val = n ∧
              (buildProperLossForest H rank).nodeKey? (E.image a) = some q) ∧
        (∀ (q : CutPair H) (y : Vertex H),
          (q.fst < q.snd ∧ H.ProperLoss q y) ↔
            ∃ n, physicalPairSlot? c out.tables q = some n ∧
              ∃ k, climb F.parentOf k ((selectors c out).label y) = n) := by
  rcases h.2.2 with ⟨F, up, G, hUp, ⟨E⟩⟩
  have L : CanonicalLaws H rank := canonicalLaws_of_flat_forward rankArc flat
  have h0 : 0 < F.size := groundedRootLt G
  have hSurj := PaperB.Embedding.finalSurjective E h0 rankArc distinctRanks flat L
  refine ⟨F, up, G, hUp, E, ⟨h0, E.root_eq h0⟩, hSurj,
    physicalPairSlot?_iff_image G E, ?_⟩
  intro q y
  let b : Fin F.size := ⟨(selectors c out).label y, E.label_lt y True.intro⟩
  have hb : E.image b = (buildProperLossForest H rank).label y :=
    E.label_eq y True.intro
  constructor
  · rintro ⟨hOrder, hy⟩
    obtain ⟨u, hu, hAnc⟩ :=
      (buildProperLossForest_properLoss_iff_ancestor
        rankArc distinctRanks flat hOrder y).mp hy
    obtain ⟨a, ha⟩ := hSurj u
    have hKey : (buildProperLossForest H rank).nodeKey? (E.image a) = some q := by
      simpa only [ha] using hu
    refine ⟨a.val, (physicalPairSlot?_iff_image G E q a.val).mpr
      ⟨a, rfl, hKey⟩, ?_⟩
    change ∃ k, climb F.parentOf k b.val = a.val
    exact (physicalAncestor_iff E hUp L rankArc flat a b hKey).mpr (by
      simpa only [ha, hb] using hAnc)
  · rintro ⟨n, hn, hAnc⟩
    obtain ⟨a, ha, hKey⟩ := (physicalPairSlot?_iff_image G E q n).mp hn
    have hOrder :=
      ((buildProperLossForest_exists_node_iff rankArc flat q).mp
        ⟨E.image a, hKey⟩).1
    have hPhysical : ∃ k, climb F.parentOf k b.val = a.val := by
      simpa only [ha] using hAnc
    have hCanonical :=
      (physicalAncestor_iff E hUp L rankArc flat a b hKey).mp hPhysical
    rw [hb] at hCanonical
    exact ⟨hOrder, (buildProperLossForest_properLoss_iff_of_node
      rankArc distinctRanks flat hKey y).mpr hCanonical⟩

/-- A physical dictionary hit exists exactly for a canonical real key. -/
theorem OutputOK.physicalPairSlot?_exists_iff
    (h : OutputOK c rank out)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (distinctRanks : ∀ u v : Vertex H, rank u = rank v → u = v)
    (flat : H.IsFlat) (q : CutPair H) :
    (∃ n, physicalPairSlot? c out.tables q = some n) ↔
      q.fst < q.snd ∧ ∃ y : Vertex H, H.ProperLoss q y := by
  rcases PaperB.OutputOK.physicalReflection h rankArc distinctRanks flat with
    ⟨_, _, _, _, E, _, hSurj, hKey, _⟩
  rw [← buildProperLossForest_exists_node_iff rankArc flat q]
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨a, _, ha⟩ := (hKey q n).mp hn
    exact ⟨E.image a, ha⟩
  · rintro ⟨u, hu⟩
    obtain ⟨a, ha⟩ := hSurj u
    exact ⟨a.val, (hKey q a.val).mpr ⟨a, rfl, by
      simpa only [ha] using hu⟩⟩

/-- Runtime interface: a checked dictionary lookup followed by at most one
physical ancestry test. The implementation of `ancestor` is separate. -/
def physicalPairMember (c : Config H) (t : Tables H)
    (ancestor : Nat → Nat → Bool) (q : CutPair H) (labelSlot : Nat) : Bool :=
  match physicalPairSlot? c t q with
  | none => false
  | some n => ancestor n labelSlot

/-- Connect a future physical ancestry implementation to the reflection
theorem. Its contract is needed only for occupied real dictionary hits. -/
theorem physicalPairMember_eq_true_iff
    (G : Grounded c F out.tables) (ancestor : Nat → Nat → Bool)
    (q : CutPair H) (y : Vertex H)
    (hAncestor : ∀ n, n < F.size → n ≠ 0 →
      (ancestor n ((selectors c out).label y) = true ↔
        ∃ k, climb F.parentOf k ((selectors c out).label y) = n))
    (hReflect : (q.fst < q.snd ∧ H.ProperLoss q y) ↔
      ∃ n, physicalPairSlot? c out.tables q = some n ∧
        ∃ k, climb F.parentOf k ((selectors c out).label y) = n) :
    physicalPairMember c out.tables ancestor q ((selectors c out).label y) =
        true ↔
      q.fst < q.snd ∧ H.ProperLoss q y := by
  rw [hReflect]
  cases hs : physicalPairSlot? c out.tables q with
  | none => simp [physicalPairMember, hs]
  | some n =>
      have hBack := (physicalPairSlot?_eq_some_iff G q n).mp hs
      obtain ⟨hlt, hnz, _⟩ := G.backward n q hBack
      have hn : n < F.size := by simpa only [G.size_eq] using hlt
      simpa [physicalPairMember, hs] using hAncestor n hn hnz

end

end PaperB
