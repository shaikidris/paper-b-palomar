module

public import PaperB.ForestPackedBackRead
public import PaperB.ForestPackedMembership

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.RetainedProperLoss

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.ForestSlimIndex
open _root_.EX24.PreparedSweep

/-- Consume a dictionary hit using only the retained word banks. -/
def WordColumns.afterHit {bits : Nat} (w : WordColumns bits)
    (valid : FlatPairDictionary.Valid w.dictionary) (hit : Option Nat)
    (key : Nat × Nat) (v : Nat) : Bool :=
  match hit with
  | none => false
  | some i =>
    let a := FlatPairDictionary.slotAt w.dictionary valid i
    if a ≠ 0 ∧ w.back.read a = some key then w.known a v else false

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)

theorem packWordColumns_afterHit {bits : Nat}
    (cap : 1 + 18 * H.vertexCount < 2 ^ bits) (q : CutPair H) (v : Nat) :
    let s := ofOrderedReader r
    let w := packWordColumns r cap
    let rep := packWordColumns_dictionary_represents r cap
    let hit := (PairLookup.lookup s.dict (orderedPairCode q)).1
    w.afterHit rep.valid hit (encodeBackPair (some q)) v = s.contains q v := by
  let s := ofOrderedReader r
  let w := packWordColumns r cap
  let rep := packWordColumns_dictionary_represents r cap
  let hit := (PairLookup.lookup s.dict (orderedPairCode q)).1
  change w.afterHit rep.valid hit (encodeBackPair (some q)) v = s.contains q v
  have checked : s.checked (orderedPairCode q) q =
      (match hit with
      | none => none
      | some i =>
        let a := (s.slots[i]?).getD 0
        if a ≠ 0 ∧ s.back[a]? = some (some q) then some a else none) := rfl
  unfold Columns.contains
  change w.afterHit rep.valid hit (encodeBackPair (some q)) v =
    (match s.checked (orderedPairCode q) q with
     | none => false
     | some a => s.known a v)
  rw [checked]
  cases h : hit with
  | none => rfl
  | some i =>
    simp only [WordColumns.afterHit]
    rw [rep.slotAt_eq i]
    let a := (s.slots[i]?).getD 0
    have back :
        w.back.read a = some (encodeBackPair (some q)) ↔
          s.back[a]? = some (some q) :=
      packBackWords_matches s (by omega : H.vertexCount < 2 ^ bits) a q
    change (if a ≠ 0 ∧ w.back.read a = some (encodeBackPair (some q)) then w.known a v else false) =
      (match (if a ≠ 0 ∧ s.back[a]? = some (some q) then some a else none) with
      | none => false
      | some a => s.known a v)
    have test := and_congr (Iff.rfl : a ≠ 0 ↔ a ≠ 0) back
    by_cases valid : a ≠ 0 ∧ s.back[a]? = some (some q)
    · simp only [ite_eq_left valid, ite_eq_left (test.mpr valid)]
      exact packWordColumns_known r cap a v
    · have invalid : ¬ (a ≠ 0 ∧ w.back.read a = some (encodeBackPair (some q))) :=
        fun h => valid (test.mp h)
      simp only [ite_eq_right valid, ite_eq_right invalid]

end PaperB.RetainedProperLoss
