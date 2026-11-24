module

public import PaperB.OriginalStaticFull

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.EX44.RetainedRouteProof.OriginalStaticConnector.Full

open PaperB
open PaperB.Digraph
open PaperB.EX16Assembly
open PaperB.LabelledQuotient
open PaperB.EX44

theorem bothTables_install
    {g : PaperB.Digraph} {r : Fin g.vertexCount} {k B E : Nat}
    {rank : Fin g.vertexCount → Nat}
    (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B)
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j) :
    let R := install q hr base debit hdebit
    let W := world q
    ∀ (spec : ParentSpec g (W.vertex R.source) q.parent)
      (intervals : Contracts R W)
      (transSome : ∀ z i,
        (R.fetch (.translate z)).value = some i ↔ W.vertex i = z)
      (transNone : ∀ z,
        (R.fetch (.translate z)).value = none ↔
          ¬ g.InitiallyReachable (W.vertex R.source) z)
      (lcaSpec : ∀ a b d, (R.fetch (.lca a b)).value = d ↔
        ∀ c : Fin g.vertexCount,
          (g.Dominates (W.vertex R.source) c (W.vertex a) ∧
           g.Dominates (W.vertex R.source) c (W.vertex b)) ↔
          g.Dominates (W.vertex R.source) c (W.vertex d))
      (encodeInj : ∀ d : Fin q.count,
        Function.Injective
          (encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent)),
      BothTables R W progress injRank spec := by
  classical
  intro R W spec intervals transSome transNone lcaSpec encodeInj
  have retained (i : Fin q.count) :
      g.InitiallyReachable (W.vertex R.source) (W.vertex i) := by
    apply Classical.byContradiction
    intro h
    have hn := (transNone (W.vertex i)).2 h
    rw [(transSome (W.vertex i) i).2 rfl] at hn
    cases hn
  have vinj : Function.Injective W.vertex := by
    intro i j h
    exact Option.some.inj
      (((transSome (W.vertex j) i).2 h).symm.trans
        ((transSome (W.vertex j) j).2 rfl))
  have tree (i j : Fin q.count) :
      W.Inside i j ↔ Ancestor q.parent (W.vertex i) (W.vertex j) :=
    treeInterval q progress injRank i j
  have dom (i j : Fin q.count) :
      W.Inside i j ↔
        g.Dominates (W.vertex R.source) (W.vertex i) (W.vertex j) :=
    (tree i j).trans (ancestor_iff_dominates progress spec (retained j))
  have out := childOutside q hr base debit hdebit
  have label := childLabel q hr base debit hdebit progress injRank
  have blockVal (d : Fin q.count)
      (hd : g.InitiallyReachable (W.vertex R.source) (W.vertex d))
      {x u : Fin q.count}
      (Z : SiblingVertex g (W.vertex R.source) (W.vertex d))
      (hZ : Z.val = W.vertex x)
      (hu : (R.fetch (.child d x)).value = some u) :
      ((siblingBlockSystem progress injRank spec hd).block Z).val =
        W.vertex u := by
    obtain ⟨hne, hp, ha⟩ := label d x u hu
    have hc : W.vertex u ≠ W.vertex d := fun h => hne (vinj h)
    let c : SiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent :=
      ⟨W.vertex u, Or.inr ⟨hp, hc, retained u⟩⟩
    have hcDom : g.Dominates (W.vertex R.source) c.val Z.val := by
      rw [hZ]
      exact (dom u x).1 ((tree u x).2 ha)
    change (siblingBlockOf progress injRank spec Z).val = W.vertex u
    exact congrArg
      (fun K : SiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent =>
        K.val)
      ((siblingBlockOf_eq_child_iff progress injRank spec Z c hc).2 hcDom)
  refine
    { intervals := intervals
      vertexInj := vinj
      translateSome := transSome
      translateNone := transNone
      treeInterval := tree
      domInterval := dom
      lca := lcaSpec
      childDomain := ?_
      childOutside := out
      childLabel := label
      childFiber := ?_ }
  · intro d x
    constructor
    · rintro ⟨u, hu⟩
      have hnot : ¬ (W.vertex x = W.vertex d ∨
          ¬ g.Dominates (W.vertex R.source) (W.vertex d) (W.vertex x)) := by
        intro h
        have hn := (out d x).2 h
        rw [hu] at hn
        cases hn
      have hd : g.Dominates (W.vertex R.source) (W.vertex d) (W.vertex x) :=
        Classical.byContradiction (fun h => hnot (Or.inr h))
      exact ⟨fun h => hnot (Or.inl h), ⟨⟨W.vertex x, retained x, hd⟩, rfl⟩⟩
    · rintro ⟨hne, Z, hZ⟩
      cases h : (R.fetch (.child d x)).value with
      | some u => exact ⟨u, rfl⟩
      | none =>
        rcases (out d x).1 h with he | hnd
        · exact False.elim (hne he)
        · have hd : g.Dominates (W.vertex R.source) (W.vertex d) (W.vertex x) := by
            rw [← hZ]
            exact Z.property.2
          exact False.elim (hnd hd)
  · intro d hd x x' u u' Z Z' hZ hZ' hu hu'
    dsimp only
    have hv := blockVal d hd Z hZ hu
    have hv' := blockVal d hd Z' hZ' hu'
    have hblock : u = u' ↔
        (siblingBlockSystem progress injRank spec hd).block Z =
          (siblingBlockSystem progress injRank spec hd).block Z' := by
      constructor
      · intro e
        apply Subtype.ext
        rw [hv, hv', e]
      · intro e
        apply vinj
        rw [← hv, ← hv', e]
    refine ⟨hblock, ?_⟩
    constructor
    · intro e
      exact congrArg
        (encodeSiblingBlockKey g (W.vertex R.source) (W.vertex d) q.parent)
        (hblock.1 e)
    · intro e
      exact hblock.2 (encodeInj d e)


theorem bothTables_actual
    {g : PaperB.Digraph} {r : Fin g.vertexCount} {k B E : Nat}
    {rank : Fin g.vertexCount → Nat}
    (q : OriginalReader g r)
    (hr : g.InitiallyReachable r r)
    (base : Runtime g.vertexCount q.count k B E)
    (debit : Nat) (hdebit : debit ≤ B)
    (progress : ∀ i j, g.HasArc i j → rank i < rank j)
    (injRank : ∀ ⦃i j⦄, rank i = rank j → i = j) :
    ∃ spec : ParentSpec g
        ((world q).vertex (install q hr base debit hdebit).source) q.parent,
      BothTables (install q hr base debit hdebit) (world q)
        progress injRank spec := by
  have hs := source_vertex q hr base debit hdebit
  have spec : ParentSpec g
      ((world q).vertex (install q hr base debit hdebit).source) q.parent := by
    rw [hs]
    exact q.parentSpec
  obtain ⟨someId, noneId⟩ := normalizedIDs q hr base debit hdebit
  refine ⟨spec, bothTables_install q hr base debit hdebit progress injRank spec
    (intervals q hr base debit hdebit) someId noneId ?_ ?_⟩
  · intro a b d
    change (q.reader.lca a b).node = d ↔ _
    rw [hs]
    exact lca_exact q progress injRank a b d
  · intro d a b h
    simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
      congrArg (decodeSiblingBlockKey g
        ((world q).vertex (install q hr base debit hdebit).source)
        ((world q).vertex d) q.parent) h

end PaperB.EX44.RetainedRouteProof.OriginalStaticConnector.Full
