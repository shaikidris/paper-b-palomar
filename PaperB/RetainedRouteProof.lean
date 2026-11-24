module

public import PaperB.OracleRuntimeProof

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.EX44
open PaperB.Digraph PaperB.Digraph.EX44
/-
First split: exact normalization and the route theorem when both original
failure IDs are present, are incomparable, and at least one is unreachable.
This covers the unreachable-target, zero, oneFirst, and oneSecond leaves
under those hypotheses, using the original `last_exit_test`.

This is not the full route theorem. The supplied excerpt cuts off the
reachable/reachable conclusion of `last_exit_test` and omits the definition
of `earlyDecision`. Those are needed for the remaining arms: in particular
the original LCA/block identifications and the quotient/physical-exit
theorems. No route-case correctness grants are assumed below.

Place this in the context (namespace and opens) of `LeafContract`.
-/
namespace RetainedRouteProof

variable {g : PaperB.Digraph} {N n k B E : Nat}

def idAt (R : Runtime N n k B E) (p : Option (Fin N)) : Option (Fin n) :=
  ((withID p fun x => (.stop x : Plan N n k (Option (Fin n)) 0 0)).run R).value

def lcaAt (R : Runtime N n k B E) (a b : Fin n) : Fin n :=
  ((.fast (.lca a b) fun d => .stop d : Plan N n k (Fin n) 1 0).run R).value

def childAt (R : Runtime N n k B E) (d x : Fin n) : Option (Fin n) :=
  ((.fast (.child d x) fun u => .stop u :
      Plan N n k (Option (Fin n)) 1 0).run R).value

structure NormalizedIDs
    (R : Runtime g.vertexCount n k B E) (W : World g n) : Prop where
  present : ∀ i x, idAt R (some i) = some x ↔ W.vertex x = i
  absent : ∀ i, idAt R (some i) = none ↔
    ¬ g.InitiallyReachable (W.vertex R.source) i

def ActualChildBlock (W : World g n)
    (parent : Fin g.vertexCount → Fin g.vertexCount) (d u x : Fin n) : Prop :=
  W.vertex u ≠ W.vertex d ∧
    parent (W.vertex u) = W.vertex d ∧
    Ancestor parent (W.vertex u) (W.vertex x)

structure TreeLookups
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (parent : Fin g.vertexCount → Fin g.vertexCount) : Prop where
  ancestor : ∀ a x, (R.ancestor a x).value = true ↔
    Ancestor parent (W.vertex a) (W.vertex x)
  dominance : ∀ a x, g.Dominates (W.vertex R.source) (W.vertex a) (W.vertex x) ↔
    W.Inside a x
  lca : ∀ a b c,
    Ancestor parent (W.vertex c) (W.vertex (lcaAt R a b)) ↔
      Ancestor parent (W.vertex c) (W.vertex a) ∧
      Ancestor parent (W.vertex c) (W.vertex b)
  child : ∀ d x u, childAt R d x = some u ↔ ActualChildBlock W parent d u x

theorem childAt_none
    {R : Runtime g.vertexCount n k B E} {W : World g n}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (D : TreeLookups R W parent) (d x : Fin n) :
    childAt R d x = none ↔ ∀ u, ¬ ActualChildBlock W parent d u x := by
  constructor
  · intro h u hu
    have he := (D.child d x u).2 hu
    rw [h] at he
    cases he
  · intro h
    cases he : childAt R d x with
    | none => rfl
    | some u => exact False.elim (h u ((D.child d x u).1 he))

theorem route_value (R : Runtime N n k B E) (r : Fin n)
    (p q : Option (Fin N)) (t : Fin N) :
    ((route r p q t).run R).value =
      ((routeRetained r (idAt R p) (idAt R q) (idAt R (some t))).run R).value := by
  cases p <;> cases q <;> first
  | rfl
  | simp [route, routeRetained, withID, idAt, Plan.run]

private theorem idAt_failure_sound
    {R : Runtime g.vertexCount n k B E} {W : World g n}
    (I : NormalizedIDs R W) (p q : Option (Fin g.vertexCount)) (x : Fin n) :
    Fails (idAt R p) (idAt R q) x → Fails p q (W.vertex x) := by
  have lift (i : Option (Fin g.vertexCount)) (h : some x = idAt R i) :
      some (W.vertex x) = i := by
    cases i with
    | none =>
        change some x = none at h
        cases h
    | some j =>
        exact congrArg some ((I.present j x).1 h.symm)
  intro h
  exact h.elim (fun hp => Or.inl (lift p hp)) (fun hq => Or.inr (lift q hq))

theorem route_contract_of_unreachable_failure
    (R : Runtime g.vertexCount n k B E) (W : World g n)
    (I : NormalizedIDs R W)
    {rank : Fin g.vertexCount → Nat}
    {parent : Fin g.vertexCount → Fin g.vertexCount}
    (acyclic : g.IsAcyclic)
    (progress : ∀ u v, g.HasArc u v → rank u < rank v)
    (injective : ∀ ⦃u v⦄, rank u = rank v → u = v)
    (spec : ParentSpec g (W.vertex R.source) parent)
    (dom : ∀ a x, g.Dominates (W.vertex R.source) (W.vertex a) (W.vertex x) ↔
      W.Inside a x)
    {a b t : Fin g.vertexCount}
    (hab : ¬ Ancestor parent a b) (hba : ¬ Ancestor parent b a)
    (dead : (¬ g.InitiallyReachable (W.vertex R.source) a) ∨
      (¬ g.InitiallyReachable (W.vertex R.source) b))
    (hs : ¬ Fails (some a) (some b) (W.vertex R.source))
    (ht : ¬ Fails (some a) (some b) t) :
    LeafContract R W (some a) (some b) t
      ((route R.source (some a) (some b) t).run R).value := by
  have L := last_exit_test (rank := rank) acyclic progress injective spec hab hba
  have hf : Fails (some a) (some b) =
      (fun z : Fin g.vertexCount => z = a ∨ z = b) := by
    funext z
    apply propext
    simp [Fails]
  have hs' : ¬ Fails (idAt R (some a)) (idAt R (some b)) R.source :=
    fun h => hs (idAt_failure_sound I (some a) (some b) R.source h)
  rw [route_value]
  simp only [routeRetained, ite_eq_right hs']
  cases hx : idAt R (some t) with
  | none =>
      change ¬ Goal R W (some a) (some b) t
      intro h
      change g.SurvivingPath (Fails (some a) (some b)) (W.vertex R.source) t at h
      rw [hf] at h
      exact (I.absent t).1 hx (L.1 t h)
  | some x =>
      have hxt := (I.present t x).1 hx
      have ht' : ¬ Fails (idAt R (some a)) (idAt R (some b)) x := by
        intro h
        apply ht
        rw [← hxt]
        exact idAt_failure_sound I (some a) (some b) x h
      simp only [ite_eq_right ht']
      cases ha : idAt R (some a) with
      | none =>
          cases hb : idAt R (some b) with
          | none =>
              change g.SurvivingPath (Fails (some a) (some b)) (W.vertex R.source) t
              rw [hf]
              apply (L.2.2.2.1 ((I.absent a).1 ha) ((I.absent b).1 hb) t).2
              apply Classical.byContradiction
              intro hn
              have he := (I.absent t).2 hn
              rw [hx] at he
              cases he
          | some v =>
              change g.SurvivingPath (Fails (some a) (some b)) (W.vertex R.source) t
                ↔ ¬ W.Inside v x
              have hd := dom v x
              rw [(I.present b v).1 hb, hxt] at hd
              rw [hf, ← hd]
              exact L.2.2.1 ((I.absent a).1 ha) t
      | some u =>
          cases hb : idAt R (some b) with
          | none =>
              change g.SurvivingPath (Fails (some a) (some b)) (W.vertex R.source) t
                ↔ ¬ W.Inside u x
              have hd := dom u x
              rw [(I.present a u).1 ha, hxt] at hd
              rw [hf, ← hd]
              exact L.2.1 ((I.absent b).1 hb) t
          | some v =>
              exfalso
              rcases dead with h | h
              · have he := (I.absent a).2 h
                rw [ha] at he
                cases he
              · have he := (I.absent b).2 h
                rw [hb] at he
                cases he

end RetainedRouteProof

end PaperB.EX44
