module

public import PaperB.QuotientArrays
public import PaperB.ArcBuckets

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.ForestIncomingRaw

abbrev Entry (H : LabelledQuotient) :=
  Fin H.vertexCount × QuotientArc H.origVertexCount H.vertexCount

abbrev Prepared (H : LabelledQuotient) :=
  EX51.Rows H.vertexCount (Entry H) × EX51.Work

def arcHead {n k : Nat} (a : QuotientArc n k) : Fin k := by
  first
  | exact a.head
  | exact a.«to»
  | exact a.dst
  | cases a <;> assumption

private def key (H : LabelledQuotient) (e : Entry H) : Fin H.vertexCount :=
  arcHead e.2

private def pushRow (H : LabelledQuotient) (acc : List (Entry H))
    (u : Fin H.vertexCount) : List (Entry H) :=
  (H.outArcs u).foldl (fun es a => (u, a) :: es) acc

def supplied (H : LabelledQuotient) : List (Entry H) :=
  (List.finRange H.vertexCount).foldl (pushRow H) []

def prepare (H : LabelledQuotient) : Prepared H :=
  EX51.groupMap (key H) id (supplied H)

def row (H : LabelledQuotient) (p : Prepared H) (y : Fin H.vertexCount) :
    List (Entry H) :=
  p.1.row y

/-- Read the scatter input counter, without traversing any list. -/
def rawTotal (H : LabelledQuotient) (p : Prepared H) : Nat :=
  match p.2 with
  | ⟨_, n, _, _, _⟩ => n

/-- Specification only; neither `prepare` nor `rawTotal` evaluates this sum. -/
def arcTotal (H : LabelledQuotient) : Nat :=
  ((List.finRange H.vertexCount).map fun u => (H.outArcs u).length).sum

private theorem foldCons {α β : Type} (f : α → β) (xs : List α)
    (acc : List β) :
    xs.foldl (fun es x => f x :: es) acc = xs.reverse.map f ++ acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    change xs.foldl (fun es z => f z :: es) (f x :: acc) =
      (x :: xs).reverse.map f ++ acc
    rw [ih, List.reverse_cons, List.map_append, List.append_assoc] <;> rfl

private theorem mem_pushRow (H : LabelledQuotient) (acc : List (Entry H))
    (u v : Fin H.vertexCount)
    (a : QuotientArc H.origVertexCount H.vertexCount) :
    (v, a) ∈ pushRow H acc u ↔
      (v = u ∧ a ∈ H.outArcs u) ∨ (v, a) ∈ acc := by
  rw [pushRow, foldCons, List.mem_append, List.mem_map]
  simp only [List.mem_reverse, Prod.mk.injEq]
  constructor
  · rintro (⟨b, hb, hu, ha⟩ | h)
    · subst u
      subst b
      exact Or.inl ⟨rfl, hb⟩
    · exact Or.inr h
  · rintro (⟨h, ha⟩ | h)
    · subst v
      exact Or.inl ⟨a, ha, rfl, rfl⟩
    · exact Or.inr h

private theorem length_pushRow (H : LabelledQuotient) (acc : List (Entry H))
    (u : Fin H.vertexCount) :
    (pushRow H acc u).length = acc.length + (H.outArcs u).length := by
  rw [pushRow, foldCons, List.length_append, List.length_map,
    List.length_reverse, Nat.add_comm]

private theorem gather_spec (H : LabelledQuotient) (us : List (Fin H.vertexCount))
    (acc : List (Entry H)) (v : Fin H.vertexCount)
    (a : QuotientArc H.origVertexCount H.vertexCount) :
    ((v, a) ∈ us.foldl (pushRow H) acc ↔
      (v, a) ∈ acc ∨ (v ∈ us ∧ a ∈ H.outArcs v)) ∧
    (us.foldl (pushRow H) acc).length =
      acc.length + (us.map fun u => (H.outArcs u).length).sum := by
  induction us generalizing acc with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    obtain ⟨hm, hn⟩ := ih (pushRow H acc u)
    refine ⟨?_, ?_⟩
    · rw [hm, mem_pushRow, List.mem_cons]
      constructor
      · rintro ((⟨e, ha⟩ | h) | ⟨hv, ha⟩)
        · subst v
          exact Or.inr ⟨Or.inl rfl, ha⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr hv, ha⟩
      · rintro (h | ⟨e | hv, ha⟩)
        · exact Or.inl (Or.inr h)
        · subst v
          exact Or.inl (Or.inl ⟨rfl, ha⟩)
        · exact Or.inr ⟨hv, ha⟩
    · rw [hn, length_pushRow, Nat.add_assoc]

private theorem mem_heads {n : Nat} (v : Fin n) : v ∈ List.finRange n := by
  first
  | exact List.mem_finRange v
  | exact List.mem_finRange
  | apply List.mem_iff_getElem.mpr
    have h : v.val < (List.finRange n).length := by simpa using v.isLt
    exact ⟨v.val, h, by simp⟩

theorem mem_supplied (H : LabelledQuotient) (u : Fin H.vertexCount)
    (a : QuotientArc H.origVertexCount H.vertexCount) :
    (u, a) ∈ supplied H ↔ a ∈ H.outArcs u := by
  simpa only [supplied, List.not_mem_nil, false_or, mem_heads, true_and] using
    (gather_spec H (List.finRange H.vertexCount) [] u a).1

private theorem length_gather (H : LabelledQuotient) (us : List (Fin H.vertexCount))
    (acc : List (Entry H)) :
    (us.foldl (pushRow H) acc).length =
      acc.length + (us.map fun u => (H.outArcs u).length).sum := by
  induction us generalizing acc with
  | nil => simp
  | cons u us ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih (pushRow H acc u), length_pushRow, Nat.add_assoc]

theorem length_supplied (H : LabelledQuotient) :
    (supplied H).length = arcTotal H := by
  simpa only [supplied, arcTotal, List.length_nil, Nat.zero_add] using
    length_gather H (List.finRange H.vertexCount) []

/-- List equality preserves multiplicity, not just membership. -/
theorem row_eq (H : LabelledQuotient) (y : Fin H.vertexCount) :
    row H (prepare H) y =
      (supplied H).filter (fun e => decide (arcHead e.2 = y)) :=
  EX51.group_row (key H) (supplied H) y

theorem mem_row (H : LabelledQuotient) (u y : Fin H.vertexCount)
    (a : QuotientArc H.origVertexCount H.vertexCount) :
    (u, a) ∈ row H (prepare H) y ↔
      a ∈ H.outArcs u ∧ arcHead a = y := by
  rw [row_eq, List.mem_filter]
  simp only [mem_supplied, decide_eq_true_eq]

theorem prepare_work (H : LabelledQuotient) :
    (prepare H).2 =
      ⟨H.vertexCount, arcTotal H, arcTotal H, arcTotal H, H.vertexCount⟩ := by
  simpa only [prepare, length_supplied] using
    (EX51.groupMap_work (key H) (id : Entry H → Entry H) (supplied H))

theorem rawTotal_prepare (H : LabelledQuotient) :
    rawTotal H (prepare H) = arcTotal H := by
  unfold rawTotal
  rw [prepare_work]

end PaperB.ForestIncomingRaw
