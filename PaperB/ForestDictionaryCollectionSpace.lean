module

public import PaperB.ForestPackedOrderedSweep

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false

namespace PaperB.ForestDictionary

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.PairLookup

private def candidate {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) (y : Vertex H) : Option Key :=
  (preparedKey H (p.row y)).map code

/-- The cursor follows Lean's compiled version of `collectFrom`, which uses
an array accumulator rather than suspending one frame per emitted key. -/
inductive CollectAt {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) (input : List (Vertex H)) :
    List (Vertex H) → Array Key → Prop where
  | start : CollectAt p code input input #[]
  | skip {y : Vertex H} {ys : List (Vertex H)} {acc : Array Key}
      (prev : CollectAt p code input (y :: ys) acc)
      (miss : candidate p code y = none) : CollectAt p code input ys acc
  | emit {y : Vertex H} {ys : List (Vertex H)} {acc : Array Key} {k : Key}
      (prev : CollectAt p code input (y :: ys) acc)
      (hit : candidate p code y = some k) :
      CollectAt p code input ys (acc.push k)

theorem CollectAt.mass {H : LabelledQuotient} {p : Rows H}
    {code : CutPair H → Key} {input todo : List (Vertex H)} {acc : Array Key}
    (cursor : CollectAt p code input todo acc) :
    acc.size + todo.length ≤ input.length := by
  induction cursor with
  | start => simp
  | skip _ _ ih =>
    simp only [List.length_cons] at ih
    omega
  | emit _ _ ih =>
    simp only [List.length_cons] at ih
    rw [Array.size_push]
    omega

theorem CollectAt.resume {H : LabelledQuotient} {p : Rows H}
    {code : CutPair H → Key} {input todo : List (Vertex H)} {acc : Array Key}
    (cursor : CollectAt p code input todo acc) :
    List.filterMapTR.go (candidate p code) todo acc = collectFrom p code input := by
  induction cursor with
  | start =>
    rw [collectFrom, List.filterMap_eq_filterMapTR]
    rfl
  | skip _ miss ih =>
    simpa only [List.filterMapTR.go, miss] using ih
  | emit _ hit ih =>
    simpa only [List.filterMapTR.go, hit] using ih

theorem CollectAt.complete {H : LabelledQuotient} {p : Rows H}
    {code : CutPair H → Key} {input todo : List (Vertex H)} {acc : Array Key}
    (cursor : CollectAt p code input todo acc) :
    ∃ final : Array Key, CollectAt p code input [] final := by
  induction todo generalizing acc with
  | nil => exact ⟨acc, cursor⟩
  | cons y ys ih =>
    cases h : candidate p code y with
    | none => exact ih (.skip cursor h)
    | some k => exact ih (.emit cursor h)

/-- When the reserved collector reaches a nonempty suffix, its next
possible push fits in the capacity set at initialization. -/
theorem collect_push_fits {H : LabelledQuotient} {p : Rows H}
    {code : CutPair H → Key} {y : Vertex H} {todo : List (Vertex H)} {acc : Array Key}
    (cursor : CollectAt p code (List.finRange H.vertexCount) (y :: todo) acc) :
    acc.size + 1 ≤ H.vertexCount := by
  have h := cursor.mass
  simp only [List.length_cons, List.length_finRange] at h
  omega

/-- The cursor starts at the exact accumulator used by the reserved worker. -/
theorem collect_reserved_start {H : LabelledQuotient} (p : Rows H)
    (code : CutPair H → Key) :
    CollectAt p code (List.finRange H.vertexCount) (List.finRange H.vertexCount)
      (Array.emptyWithCapacity H.vertexCount) :=
  .start

/-- Reserve the entire enumeration, unread suffix, and two accumulator
versions during a push. The estimate counts initialized scalar words,
with two words per candidate key and one per vertex index. -/
theorem collect_push_words {H : LabelledQuotient} {p : Rows H}
    {code : CutPair H → Key} {y : Vertex H} {todo : List (Vertex H)}
    {acc : Array Key} (k : Key)
    (cursor : CollectAt p code (List.finRange H.vertexCount) (y :: todo) acc) :
    H.vertexCount + (y :: todo).length + 2 * acc.size + 2 * (acc.push k).size
      ≤ 5 * H.vertexCount := by
  have prev := cursor.mass
  rw [List.length_finRange] at prev
  simp only [List.length_cons, Array.size_push] at prev ⊢
  omega

/-- At handoff the collector has the exact input of the dictionary sort.
Reserve both the initialized array and the resulting list, including
two payload words and one link per output list entry. -/
theorem collect_handoff_words {H : LabelledQuotient} {p : Rows H}
    {code : CutPair H → Key} {acc : Array Key}
    (cursor : CollectAt p code (List.finRange H.vertexCount) [] acc) :
    acc.toList = collect p code ∧
      H.vertexCount + 2 * acc.size + 3 * acc.toList.length ≤ 6 * H.vertexCount := by
  have hm := cursor.mass
  simp only [List.length_nil, Nat.add_zero, List.length_finRange] at hm
  refine ⟨cursor.resume, ?_⟩
  simp only [Array.length_toList]
  omega

end PaperB.ForestDictionary
