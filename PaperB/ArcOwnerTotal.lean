module

public import PaperB.StructuralPaper

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

include progress in
private theorem retainedArc_rank_le_of_path
    {u v : Fin g.vertexCount}
    (p : AvoidPath g.HasArc (fun _ => False) u v) :
    rank u ≤ rank v := by
  induction p with
  | refl u _ => exact Nat.le_refl _
  | step u w v _ harc _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (progress u w harc)) ih

/-- The physical tail stored in a quotient emission. -/
def siblingEmissionPhysicalTail
    (e : SiblingEmission g r d parent) : Fin g.vertexCount :=
  match e with
  | ⟨_, _, tail⟩ => tail

private theorem emitAtHeadParent
    {a : Fin g.vertexCount × Fin g.vertexCount}
    (ha : g.HasArc a.1 a.2) (hu : g.InitiallyReachable r a.1) :
    g.InitiallyReachable r (parent a.2) ∧
      ∃ e : SiblingEmission g r (parent a.2) parent,
        siblingEmission? (d := parent a.2) progress injective spec a = some e ∧
          siblingEmissionPhysicalTail e = a.1 := by
  have path : AvoidPath g.HasArc (fun _ => False) r a.1 := hu
  have hru : rank r ≤ rank a.1 :=
    retainedArc_rank_le_of_path progress path
  have huv : rank a.1 < rank a.2 := progress a.1 a.2 ha
  have hrv : rank r < rank a.2 := Nat.lt_of_le_of_lt hru huv
  have hvr : a.2 ≠ r := by
    intro h
    exact Nat.lt_irrefl (rank r) (by simpa only [h] using hrv)
  have hv : g.InitiallyReachable r a.2 := initiallyReachable_extend hu ha
  rcases spec.nonroot a.2 hvr with ⟨_, hi⟩ | ⟨hn, _⟩
  · have hpv : g.Dominates r (parent a.2) a.2 := by
      first
      | exact hi.1
      | exact hi.1.1
      | exact hi.1.2
      | exact hi.2.1
    have hpne : a.2 ≠ parent a.2 := by
      apply Ne.symm
      first
      | exact hi.1
      | exact hi.1.1
      | exact hi.1.2
      | exact hi.2.1
      | exact hi.2.1.1
      | exact hi.2.1.2
    have hp : g.InitiallyReachable r (parent a.2) :=
      initiallyReachable_of_dominates hv hpv
    have hpu := dominates_reachable_predecessor_of_ne ha hu hpne hpv
    let u : SiblingVertex g r (parent a.2) := ⟨a.1, hu, hpu⟩
    let v : SiblingVertex g r (parent a.2) := ⟨a.2, hv, hpv⟩
    let c : SiblingBlockKey g r (parent a.2) parent :=
      ⟨a.2, Or.inr ⟨rfl, hpne, hv⟩⟩
    have hself : g.Dominates r a.2 a.2 := dominates_refl
    have hvc : siblingBlockOf progress injective spec v = c :=
      (siblingBlockOf_eq_child_iff progress injective spec v c hpne).2 hself
    have hcross :
        siblingBlockOf progress injective spec u ≠
          siblingBlockOf progress injective spec v := by
      intro h
      have hdom : g.Dominates r a.2 a.1 :=
        (siblingBlockOf_eq_child_iff progress injective spec u c hpne).1
          (h.trans hvc)
      have hne : a.2 ≠ a.1 := by
        intro he
        exact Nat.lt_irrefl (rank a.1) (by simpa only [he] using huv)
      have hback := rank_lt_of_strict_dominator progress hu hdom hne
      exact (Nat.not_lt_of_ge (Nat.le_of_lt huv)) hback
    let e : SiblingEmission g r (parent a.2) parent :=
      ⟨siblingBlockOf progress injective spec u,
        siblingBlockOf progress injective spec v, a.1⟩
    exact ⟨hp, e, (siblingEmission?_eq_some_iff progress injective spec a e).2
      ⟨u.property, v.property, hcross, rfl⟩, rfl⟩
  · exact (hn hv).elim

/-- A retained arc has one emission at its head's parent, with its physical
tail unchanged. -/
theorem retainedArc_exact
    {a : Fin g.vertexCount × Fin g.vertexCount}
    (ha : g.HasArc a.1 a.2) (hu : g.InitiallyReachable r a.1) :
    g.InitiallyReachable r (parent a.2) ∧
      ∃ e : SiblingEmission g r (parent a.2) parent,
        siblingEmission? (d := parent a.2) progress injective spec a = some e ∧
        siblingEmissionPhysicalTail e = a.1 ∧
        ∀ e' : SiblingEmission g r (parent a.2) parent,
          siblingEmission? (d := parent a.2) progress injective spec a = some e' →
            e' = e := by
  obtain ⟨hp, e, he, ht⟩ := emitAtHeadParent progress injective spec ha hu
  refine ⟨hp, e, he, ht, ?_⟩
  intro e' he'
  exact Option.some.inj (he'.symm.trans he)

theorem siblingEmission_exists_iff_headParent
    {a : Fin g.vertexCount × Fin g.vertexCount} (ha : g.HasArc a.1 a.2) :
    (∃ e, siblingEmission? (d := d) progress injective spec a = some e) ↔
      g.InitiallyReachable r a.1 ∧ parent a.2 = d := by
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨hu, hv, hcross, _⟩ :=
      (siblingEmission?_eq_some_iff progress injective spec a e).1 he
    let u : SiblingVertex g r d := ⟨a.1, hu⟩
    let v : SiblingVertex g r d := ⟨a.2, hv⟩
    have hd : g.InitiallyReachable r d :=
      initiallyReachable_of_dominates v.property.1 v.property.2
    exact ⟨u.property.1,
      (siblingBlockSystem_crossing_owner progress injective spec hd u v ha hcross).2.2⟩
  · rintro ⟨hu, rfl⟩
    obtain ⟨_, e, he, _⟩ := retainedArc_exact progress injective spec ha hu
    exact ⟨e, he⟩

theorem siblingEmission_physicalTail
    {a : Fin g.vertexCount × Fin g.vertexCount}
    (ha : g.HasArc a.1 a.2) {e : SiblingEmission g r d parent}
    (he : siblingEmission? (d := d) progress injective spec a = some e) :
    siblingEmissionPhysicalTail e = a.1 := by
  obtain ⟨hu, hp⟩ :=
    (siblingEmission_exists_iff_headParent progress injective spec ha).1 ⟨e, he⟩
  subst d
  obtain ⟨_, e₀, _, ht, huniq⟩ := retainedArc_exact progress injective spec ha hu
  exact (congrArg siblingEmissionPhysicalTail (huniq e he)).trans ht

/-- One owner entry per retained raw occurrence, without deduplication. -/
noncomputable def retainedArcOwner? (r : Fin g.vertexCount)
    (parent : Fin g.vertexCount → Fin g.vertexCount)
    (a : Fin g.vertexCount × Fin g.vertexCount) : Option (Fin g.vertexCount) := by
  classical
  exact if g.InitiallyReachable r a.1 then some (parent a.2) else none

private theorem retainedArcOwner_eq_some_iff
    {a : Fin g.vertexCount × Fin g.vertexCount} :
    retainedArcOwner? (g := g) r parent a = some d ↔
      g.InitiallyReachable r a.1 ∧ parent a.2 = d := by
  by_cases hu : g.InitiallyReachable r a.1 <;> simp [retainedArcOwner?, hu]

private theorem map_filterMap_eq_map_filter
    {A B C : Type} (xs : List A) (emit : A → Option B) (keep : A → Bool)
    (out : B → C) (raw : A → C)
    (hkeep : ∀ a ∈ xs, (∃ e, emit a = some e) ↔ keep a = true)
    (hout : ∀ a ∈ xs, ∀ e, emit a = some e → out e = raw a) :
    (xs.filterMap emit).map out = (xs.filter keep).map raw := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have ha : a ∈ a :: xs := by simp
      have hka := hkeep a ha
      have htail := ih
        (fun b hb => hkeep b (List.mem_cons_of_mem _ hb))
        (fun b hb => hout b (List.mem_cons_of_mem _ hb))
      cases he : emit a with
      | none =>
          have hk : keep a = false := by
            cases hk : keep a with
            | false => rfl
            | true =>
                obtain ⟨e, h⟩ := hka.mpr hk
                rw [he] at h
                cases h
          simp [List.filterMap, List.filter, he, hk, htail]
      | some e =>
          have hk : keep a = true := hka.mp ⟨e, he⟩
          have ht := hout a ha e he
          simp [List.filterMap, List.filter, he, hk, ht, htail]

/-- The emitted tails are exactly the tails of the raw occurrences owned by
`d`, in input order and with multiplicity. -/
theorem siblingEmissions_preserve_retained_occurrences :
    (g.originalArcOccurrences.filterMap
      (siblingEmission? (d := d) progress injective spec)).map
        siblingEmissionPhysicalTail =
      (g.originalArcOccurrences.filter
        (fun a => decide (retainedArcOwner? (g := g) r parent a = some d))).map
          Prod.fst := by
  apply map_filterMap_eq_map_filter
  · intro a ha
    have harc := (mem_originalArcOccurrences_iff g a.1 a.2).1 ha
    rw [siblingEmission_exists_iff_headParent progress injective spec harc]
    simp only [decide_eq_true_eq, retainedArcOwner_eq_some_iff]
  · intro a ha e he
    exact siblingEmission_physicalTail progress injective spec
      ((mem_originalArcOccurrences_iff g a.1 a.2).1 ha) he

private theorem length_filterMap_eq_ownerCount
    {A B V : Type} [BEq V] [LawfulBEq V]
    (xs : List A) (emit : A → Option B) (owner : A → Option V) (d : V)
    (h : ∀ a ∈ xs, (∃ e, emit a = some e) ↔ owner a = some d) :
    (xs.filterMap emit).length = (xs.filterMap owner).count d := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hhead := h a (by simp)
      have htail := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      clear h ih
      cases he : emit a <;> cases ho : owner a <;>
        simp_all [List.filterMap, eq_comm]

theorem finiteSiblingQuotient_arcCount_eq_ownerCount
    (hd : g.InitiallyReachable r d) :
    (finiteSiblingQuotient progress injective spec hd).arcCount =
      (g.originalArcOccurrences.filterMap (retainedArcOwner? r parent)).count d := by
  simp only [finiteSiblingQuotient, PaperB.arcCount_ofOccurrences,
    finiteSiblingOccurrences, List.length_map, siblingEmissions]
  apply length_filterMap_eq_ownerCount
  intro a ha
  rw [siblingEmission_exists_iff_headParent progress injective spec
    ((mem_originalArcOccurrences_iff g a.1 a.2).1 ha)]
  exact retainedArcOwner_eq_some_iff.symm

private theorem sum_ownerCounts {V : Type} [DecidableEq V] [BEq V] [LawfulBEq V]
    (ds xs : List V) (hn : ds.Nodup) (hall : ∀ x, x ∈ ds) :
    (ds.map (fun d => xs.count d)).sum = xs.length := by
  have step (x : V) (ys es : List V) (he : es.Nodup) :
      (es.map (fun d => (x :: ys).count d)).sum =
        (es.map (fun d => ys.count d)).sum + (if x ∈ es then 1 else 0) := by
    induction es with
    | nil => simp
    | cons d es ih =>
        obtain ⟨hd, ht⟩ := List.nodup_cons.mp he
        simp only [List.map_cons, List.sum_cons, ih ht]
        by_cases h : x = d
        · subst d
          simp [hd] <;> omega
        · simp [h, Nat.add_assoc]
  induction xs with
  | nil =>
      clear hn hall
      induction ds with
      | nil => rfl
      | cons d ds ih =>
          simp only [List.map_cons, List.sum_cons, ih] <;> rfl
  | cons x xs ih =>
      rw [step x xs ds hn, ih]
      simp [hall x]

/-- The quotient's actual arc count, or zero if the vertex has no quotient. -/
noncomputable def finiteSiblingArcCountAt (v : Fin g.vertexCount) : Nat := by
  classical
  exact if hv : g.InitiallyReachable r v then
    (finiteSiblingQuotient progress injective spec hv).arcCount
  else 0

/-- Actual quotient arc counts, indexed by vertex. -/
noncomputable def finiteSiblingArcCounts : Array Nat :=
  ((List.finRange g.vertexCount).map
    (finiteSiblingArcCountAt progress injective spec)).toArray

theorem finiteSiblingArcCounts_size :
    (finiteSiblingArcCounts progress injective spec).size = g.vertexCount := by
  simp [finiteSiblingArcCounts]

theorem finiteSiblingArcCounts_getElem (v : Fin g.vertexCount) :
    (finiteSiblingArcCounts progress injective spec)[v.val]'(
      by simpa only [finiteSiblingArcCounts_size progress injective spec] using v.isLt) =
      finiteSiblingArcCountAt progress injective spec v := by
  rcases v with ⟨i, hi⟩
  simp [finiteSiblingArcCounts] <;> rfl

theorem total_finiteSiblingArcCount_eq_retained :
    (finiteSiblingArcCounts progress injective spec).toList.sum =
      (g.originalArcOccurrences.filterMap (retainedArcOwner? r parent)).length := by
  classical
  let xs := g.originalArcOccurrences.filterMap (retainedArcOwner? r parent)
  have hc (v : Fin g.vertexCount) :
      finiteSiblingArcCountAt progress injective spec v = xs.count v := by
    by_cases hv : g.InitiallyReachable r v
    · simpa [finiteSiblingArcCountAt, hv, xs] using
        (finiteSiblingQuotient_arcCount_eq_ownerCount progress injective spec hv)
    · have hn : v ∉ xs := by
        intro hm
        obtain ⟨a, ha, he⟩ := List.mem_filterMap.mp hm
        obtain ⟨hu, hp⟩ := retainedArcOwner_eq_some_iff.mp he
        apply hv
        rw [← hp]
        exact (retainedArc_exact progress injective spec
          ((mem_originalArcOccurrences_iff g a.1 a.2).1 ha) hu).1
      have hz : xs.count v = 0 := by
        first
        | exact List.count_eq_zero.mpr hn
        | exact List.count_eq_zero_of_not_mem hn
      simpa [finiteSiblingArcCountAt, hv] using hz.symm
  have hfn :
      finiteSiblingArcCountAt progress injective spec =
        (fun v : Fin g.vertexCount => xs.count v) := funext hc
  have hn : (List.finRange g.vertexCount).Nodup := by
    first | exact List.nodup_finRange _ | exact List.nodup_finRange
  have hall (v : Fin g.vertexCount) : v ∈ List.finRange g.vertexCount := by
    first | exact List.mem_ofFn.mpr ⟨v, rfl⟩ | solve | simp
  unfold finiteSiblingArcCounts
  rw [hfn]
  simpa using sum_ownerCounts (List.finRange g.vertexCount) xs hn hall

theorem total_finiteSiblingArcCount_le_original :
    (finiteSiblingArcCounts progress injective spec).toList.sum ≤
      g.originalArcOccurrences.length := by
  rw [total_finiteSiblingArcCount_eq_retained progress injective spec]
  apply List.length_filterMap_le

end PaperB.Digraph
