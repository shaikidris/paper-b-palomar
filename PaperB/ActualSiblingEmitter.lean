module

public import PaperB.StaticOracleTree
public import PaperB.GlobalSiblingEmitter

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.StaticOriginalSiblingEmitter

open EX16Assembly
open PaperB.Digraph

variable {g : Digraph} {r : Fin g.vertexCount}

/-- The two halves of the global ID space are disjoint. -/
def rootCode {n : Nat} (x : Fin n) : Fin (2 * n) :=
  ⟨x.val, by have hx := x.isLt; omega⟩

def childCode {n : Nat} (x : Fin n) : Fin (2 * n) :=
  ⟨n + x.val, by have hx := x.isLt; omega⟩

theorem rootCode_ne_childCode {n : Nat} (a b : Fin n) :
    rootCode a ≠ childCode b := by
  intro h
  have hv := congrArg Fin.val h
  change a.val = n + b.val at hv
  have ha := a.isLt
  omega

/-- The fallback is used only to totalize the getters on unretained IDs. -/
private def held (q : OriginalReader g r) (v : Fin g.vertexCount) :
    Fin q.count :=
  (q.ids.find v).getD q.input.root

def packing (q : OriginalReader g r) :
    PaperB.Digraph.GlobalSibling.Packing g r q.parent (2 * q.count) :=
  fun d k =>
    if k.val = d then rootCode (held q d)
    else childCode (held q k.val)

private def measuredCode (q : OriginalReader g r) (a b : Fin q.count) :
    Fin (2 * q.count) × Nat :=
  let hit := q.reader.childMeasured a b
  ((match hit.1 with
    | some c => childCode c
    | none => rootCode a), hit.2)

def getters (q : OriginalReader g r) :
    PaperB.Digraph.GlobalSibling.Getters g (2 * q.count) where
  reachable v := (q.ids.find v).isSome
  parentOf := q.parent
  rootBlock d := rootCode (held q d)
  headBlock v :=
    let d := q.parent v
    if v = d then rootCode (held q d) else childCode (held q v)
  childBlock d u :=
    match q.ids.find d, q.ids.find u with
    | some a, some b => measuredCode q a b
    | _, _ => (rootCode q.input.root, 0)

private theorem retained_iff (q : OriginalReader g r)
    (v : Fin g.vertexCount) :
    (q.ids.find v).isSome = true ↔ g.InitiallyReachable r v := by
  constructor
  · intro h
    cases e : q.ids.find v with
    | none => simp [e] at h
    | some a =>
      have ha := (q.find_eq_some_iff_original v a).mp e
      rw [← ha]
      exact q.ids.original_reachable a
  · intro hv
    rw [q.find_slot v hv]
    rfl

private theorem original_injective (q : OriginalReader g r)
    {a b : Fin q.count}
    (h : q.ids.originals.read a = q.ids.originals.read b) : a = b :=
  Option.some.inj
    ((q.ids.slot_of_original a).symm.trans
      ((congrArg q.ids.find h).trans (q.ids.slot_of_original b)))

private theorem parent_read_iff (q : OriginalReader g r)
    (c a : Fin q.count) :
    q.input.parent.read c = a ↔
      q.parent (q.ids.originals.read c) = q.ids.originals.read a := by
  rw [q.parent_at_original c]
  exact ⟨congrArg q.ids.originals.read, original_injective q⟩

/-- The stored child test, with its ancestry clause transported back to
original-graph dominance by the EX16 interval equivalence. -/
theorem child_some_original (q : OriginalReader g r)
    (a b c : Fin q.count) :
    q.reader.child a b = some c ↔
      c ≠ q.input.root ∧
      q.parent (q.ids.originals.read c) = q.ids.originals.read a ∧
      g.Dominates r (q.ids.originals.read c) (q.ids.originals.read b) := by
  rw [q.reader.child_some_iff a b c, parent_read_iff q c a,
    q.reader.ancestor_iff_interval c b,
    ← q.held_dominates_iff_interval c b]

theorem child_none_original (q : OriginalReader g r)
    (a b : Fin q.count) :
    q.reader.child a b = none ↔
      ¬ ∃ c : Fin q.count, c ≠ q.input.root ∧
        q.parent (q.ids.originals.read c) = q.ids.originals.read a ∧
        g.Dominates r (q.ids.originals.read c) (q.ids.originals.read b) := by
  rw [q.reader.child_none_iff a b]
  apply not_congr
  apply exists_congr
  intro c
  rw [parent_read_iff q c a, q.reader.ancestor_iff_interval c b,
    ← q.held_dominates_iff_interval c b]

private theorem stored_root_fixed (q : OriginalReader g r) :
    q.input.parent.read q.input.root = q.input.root :=
  q.reader.input_ok.parent_root

private theorem self_dominates (_q : OriginalReader g r)
    (v : Fin g.vertexCount) (_hv : g.InitiallyReachable r v) :
    g.Dominates r v v :=
  dominates_refl (g := g) (r := r) (v := v)

/-- The checked lookup bound at one held parent. The row size is the
stored range count, not a scan of the row. -/
def rowBound (q : OriginalReader g r) (a : Fin q.count) : Nat :=
  Nat.log2 ((q.reader.ranges.read a).size + 1) + 2

def queryBound (q : OriginalReader g r) : Nat :=
  (List.ofFn (rowBound q)).foldr Nat.max 0

private theorem le_fold_max (x : Nat) (xs : List Nat) (h : x ∈ xs) :
    x ≤ xs.foldr Nat.max 0 := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    rcases List.mem_cons.mp h with h | h
    · subst x
      exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

private theorem rowBound_le (q : OriginalReader g r) (a : Fin q.count) :
    rowBound q a ≤ queryBound q :=
  le_fold_max _ _ (List.mem_ofFn.mpr ⟨a, rfl⟩)

private theorem measuredCode_cost_le (q : OriginalReader g r)
    (a b : Fin q.count) :
    (measuredCode q a b).2 ≤ queryBound q := by
  have h : (q.reader.childMeasured a b).2 ≤ rowBound q a :=
    StaticChildLookup.lookup_cost_le
      (q.reader.ranges.read a) (q.reader.entry b)
  exact Nat.le_trans h (rowBound_le q a)

theorem childBlock_cost_le (q : OriginalReader g r)
    (d u : Fin g.vertexCount) :
    ((getters q).childBlock d u).2 ≤ queryBound q := by
  cases hd : q.ids.find d with
  | none => simp [getters, hd]
  | some a =>
    cases hu : q.ids.find u with
    | none => simp [getters, hd, hu]
    | some b =>
      simpa only [getters, hd, hu] using measuredCode_cost_le q a b

theorem checked {rank : Fin g.vertexCount → Nat}
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
    (q : OriginalReader g r) :
    PaperB.Digraph.GlobalSibling.Checked
      (g := g) (r := r) (rank := rank) (parent := q.parent)
      progress injective q.parentSpec (getters q) (packing q) (queryBound q) := by
  refine ⟨retained_iff q, fun _ => rfl, ?_, ?_, ?_, childBlock_cost_le q⟩
  · intro d hd
    let x : SiblingVertex g r d := ⟨d, hd⟩
    have he := (siblingBlockOf_eq_root_iff
(parent := q.parent)       progress injective q.parentSpec x).mpr rfl
    change rootCode (held q d) =
      packing q d (siblingBlockOf (parent := q.parent) progress injective q.parentSpec x)
    rw [he]
    change rootCode (held q d) =
      (if d = d then rootCode (held q d) else childCode (held q d))
    rw [if_pos rfl]
  · intro v hv
    let d := q.parent v
    let x : SiblingVertex g r d := ⟨v, hv⟩
    change (if v = d then rootCode (held q d) else childCode (held q v)) =
      packing q d (siblingBlockOf (parent := q.parent) progress injective q.parentSpec x)
    by_cases h : v = d
    · have he := (siblingBlockOf_eq_root_iff
(parent := q.parent)         progress injective q.parentSpec x).mpr h
      rw [if_pos h, he]
      change rootCode (held q d) =
        (if d = d then rootCode (held q d) else childCode (held q d))
      rw [if_pos rfl]
    · let k : SiblingBlockKey g r d q.parent :=
        ⟨v, Or.inr ⟨rfl, h, hv.1⟩⟩
      have he : siblingBlockOf (parent := q.parent) progress injective q.parentSpec x = k :=
        (siblingBlockOf_eq_child_iff (parent := q.parent) progress injective q.parentSpec x k h).mpr
          (self_dominates q v hv.1)
      rw [if_neg h, he]
      change childCode (held q v) =
        (if v = d then rootCode (held q d) else childCode (held q v))
      rw [if_neg h]
  · intro d u hu hne
    let x : SiblingVertex g r d := ⟨u, hu⟩
    let k := siblingBlockOf (parent := q.parent) progress injective q.parentSpec x
    have hkd : k.val ≠ d := by
      intro h
      have he : k = SiblingBlockKey.root g r d q.parent := Subtype.ext h
      exact hne ((siblingBlockOf_eq_root_iff
(parent := q.parent)         progress injective q.parentSpec x).mp he)
    have hk : q.parent k.val = d ∧ k.val ≠ d ∧
        g.InitiallyReachable r k.val := by
      rcases k.property with h | h
      · exact (hkd h).elim
      · exact h
    have hdom : g.Dominates r k.val u :=
      (siblingBlockOf_eq_child_iff (parent := q.parent) progress injective q.parentSpec x k hkd).mp rfl

    let c := q.slot k.val hk.2.2
    let a := q.input.parent.read c
    let b := q.slot u hu.1
    have hfindD : q.ids.find d = some a :=
      (congrArg q.ids.find hk.1).symm.trans
        (q.find_parent_at_slot k.val hk.2.2)
    have hfindU : q.ids.find u = some b := q.find_slot u hu.1
    have hfindC : q.ids.find k.val = some c := q.find_slot k.val hk.2.2
    have ha := (q.find_eq_some_iff_original d a).mp hfindD
    have hb := q.original_at_slot u hu.1
    have hc := q.original_at_slot k.val hk.2.2
    have hcne : c ≠ q.input.root := by
      intro h
      have hca : c = a := by
        change c = q.input.parent.read c
        rw [h, stored_root_fixed q]
      exact hkd (hc.symm.trans
        ((congrArg q.ids.originals.read hca).trans ha))
    have hparent :
        q.parent (q.ids.originals.read c) = q.ids.originals.read a := by
      rw [hc, ha]
      exact hk.1
    have hancestor :
        g.Dominates r (q.ids.originals.read c) (q.ids.originals.read b) := by
      change g.Dominates r (q.ids.originals.read c)
        (q.ids.originals.read (q.slot u hu.1))
      rw [hc, hb]
      exact hdom

    change ((getters q).childBlock d u).1 = packing q d k
    simp only [getters, hfindD, hfindU]
    change (match q.reader.child a b with
      | some z => childCode z
      | none => rootCode a) = packing q d k
    cases e : q.reader.child a b with
    | none =>
      exact ((child_none_original q a b).mp e
        ⟨c, hcne, hparent, hancestor⟩).elim
    | some z =>
      have hit : q.reader.child a b = some c :=
        (child_some_original q a b c).mpr ⟨hcne, hparent, hancestor⟩
      have ez : z = c := Option.some.inj (e.symm.trans hit)
      subst z
      simp only [packing, if_neg hkd, held, hfindC, Option.getD]

/-- The actual scatter over the retained outgoing occurrences. -/
def emitAll (q : OriginalReader g r) :=
  PaperB.Digraph.GlobalSibling.emitAll (getters q)

/-- The measured component charges one child lookup, or zero if the
tail is the parent itself. The arc is not used to run a graph search. -/
theorem locate_cost_le (q : OriginalReader g r)
    (a : Fin g.vertexCount × Fin g.vertexCount) :
    (PaperB.Digraph.GlobalSibling.locate (getters q) a).2 ≤ queryBound q := by
  change (PaperB.Digraph.GlobalSibling.tailBlock (getters q) (q.parent a.2) a.1).2 ≤
    queryBound q
  unfold PaperB.Digraph.GlobalSibling.tailBlock
  split
  · exact Nat.zero_le _
  · exact childBlock_cost_le q _ _

end PaperB.StaticOriginalSiblingEmitter
