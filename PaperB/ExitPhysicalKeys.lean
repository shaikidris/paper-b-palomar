module

public import PaperB.ExitPhysicalSchedule

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Exit.OrderedReaderResult

open PaperB.LabelledQuotient PaperB.ForestHead PaperB.EX24.FinalDFS
open PaperB.Jumps
open _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep

section

variable {H : LabelledQuotient} {p : ForestDictionary.Rows H}
variable {data : Array (Vertex H)} {size_data : data.size = H.vertexCount}
variable {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
variable [DecidableEq (CutPair H)]
variable (r : OrderedReaderResult p data size_data rank large)
variable {F : JumpForest} {up : Fin F.size → Fin F.size}

/-- Read a key from the final back table, treating slot zero as the sentinel. -/
def exitBackKey? (k : Nat) : Option (CutPair H) :=
  if k = 0 then none
  else
    match r.out.tables.back[k]? with
    | none => none
    | some q => q

/-- Read the child key and then the key at its physical parent word. -/
def exitHeadKeys? (y : Vertex H) : Option (CutPair H × CutPair H) :=
  match actualSlot r y with
  | none => none
  | some i =>
      match exitBackKey? r i.val with
      | none => none
      | some child =>
          match exitBackKey? r (actualPhysicalParent r i.val) with
          | none => none
          | some parent => some (child, parent)

/-- Use the original final-label decoder and the final back table. -/
def exitDenseOwnerKey? (y : Vertex H) : Option (CutPair H) :=
  exitBackKey? r ((selectors (orderedConfig p large) r.out).label y)

private theorem exitBackKey?_eq_image
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    (a : Fin F.size) :
    exitBackKey? r a.val =
      (buildProperLossForest H rank).nodeKey? (E.image a) := by
  by_cases hz : a.val = 0
  · have h0 : 0 < F.size := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have ha : a = (⟨0, h0⟩ : Fin F.size) := Fin.ext hz
    rw [ha, E.root_eq h0, buildProperLossForest_nodeKey?_root]
    <;> rfl
  · simp only [exitBackKey?, if_neg hz, E.back_eq a]

/-- Every final dense label gives the canonical owner's key, including root. -/
theorem exitDenseOwnerKey?_eq_canonical
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    (y : Vertex H) :
    exitDenseOwnerKey? r y =
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).label y) := by
  let b : Fin F.size :=
    ⟨(selectors (orderedConfig p large) r.out).label y,
      E.label_lt y True.intro⟩
  have hb : E.image b = (buildProperLossForest H rank).label y :=
    E.label_eq y True.intro
  change exitBackKey? r b.val =
    (buildProperLossForest H rank).nodeKey?
      ((buildProperLossForest H rank).label y)
  rw [← hb]
  exact exitBackKey?_eq_image r E b

private theorem exitParentWord_eq_parentOf
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (a : Fin F.size) (ha : a.val ≠ 0) :
    actualPhysicalParent r a.val = F.parentOf a.val := by
  have hlt : a.val < F.size := a.isLt
  unfold actualPhysicalParent
  rw [(readRecordWords_spec G.layout hlt).1] <;>
    first
    | rfl
    | (simp [JumpForest.parentOf, hlt, ha] <;> done)
    | simp_all [JumpForest.parentOf, JumpForest.size]

private theorem exitRealKeyAt
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    (a : Fin F.size) (ha : a.val ≠ 0) :
    ∃ q : CutPair H,
      r.out.tables.back[a.val]? = some (some q) ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables q =
        some a.val ∧
      (buildProperLossForest H rank).nodeKey? (E.image a) = some q := by
  cases hk : (buildProperLossForest H rank).nodeKey? (E.image a) with
  | none =>
      have h0 : 0 < F.size := Nat.lt_of_le_of_lt (Nat.zero_le _) a.isLt
      let z : Fin F.size := ⟨0, h0⟩
      have hz : (buildProperLossForest H rank).nodeKey? (E.image z) = none :=
        (congrArg (buildProperLossForest H rank).nodeKey? (E.root_eq h0)).trans
          (buildProperLossForest_nodeKey?_root H rank)
      have he : a = z :=
        E.injective
          (buildProperLossForest_nodeKey?_inj H rank (hk.trans hz.symm))
      exact (ha (congrArg (fun b : Fin F.size => b.val) he)).elim
  | some q =>
      have hb : r.out.tables.back[a.val]? = some (some q) :=
        (E.back_eq a).trans (congrArg some hk)
      exact ⟨q, hb, (physicalPairSlot?_eq_some_iff G q a.val).mpr hb,
        by simp only [hk]⟩

/-- A scheduled first-install hit reads a real child and a real parent from
the final tables. Both keys round-trip through the checked physical lookup. -/
theorem actualSlot_exitHeadKeys
    (G : Grounded (orderedConfig p large) F r.out.tables)
    (hUp : ∀ a : Fin F.size, (up a).val = F.parentOf a.val)
    (E : Embedding (orderedConfig p large) r.out F rank up (fun _ => True))
    {y : Vertex H} {i : Fin r.out.tables.next}
    (hit : actualSlot r y = some i)
    (hFirst : (actualP r).firstAt y i) :
    ∃ (a : Fin F.size) (child parent : CutPair H),
      a.val = i.val ∧
      actualPhysicalParent r i.val ≠ 0 ∧
      (up a).val = actualPhysicalParent r i.val ∧
      r.out.tables.back[i.val]? = some (some child) ∧
      r.out.tables.back[actualPhysicalParent r i.val]? = some (some parent) ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables child =
        some i.val ∧
      physicalPairSlot? (orderedConfig p large) r.out.tables parent = some (actualPhysicalParent r i.val) ∧
      (buildProperLossForest H rank).nodeKey? (E.image a) = some child ∧
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent (E.image a)) = some parent ∧
      exitHeadKeys? r y = some (child, parent) := by
  have hi : i.val ≠ 0 := Nat.ne_of_gt hFirst.1
  have hp0 : actualPhysicalParent r i.val ≠ 0 := hFirst.2.1
  let a : Fin F.size := ⟨i.val, by simpa only [G.size_eq] using i.isLt⟩
  have hp : (up a).val = actualPhysicalParent r i.val :=
    (hUp a).trans (exitParentWord_eq_parentOf r G a hi).symm
  have hup0 : (up a).val ≠ 0 := fun h => hp0 (hp.symm.trans h)

  obtain ⟨child, hcb, hcs, hck⟩ := exitRealKeyAt r G E a hi
  obtain ⟨parent, hpb, hps, hpk⟩ := exitRealKeyAt r G E (up a) hup0
  change r.out.tables.back[i.val]? = some (some child) at hcb
  change physicalPairSlot? (orderedConfig p large) r.out.tables child =
    some i.val at hcs
  rw [hp] at hpb hps

  have hImageParent :
      E.image (up a) =
        (buildProperLossForest H rank).parent (E.image a) := by
    exact E.parent_eq a
  have hParentKey :
      (buildProperLossForest H rank).nodeKey?
        ((buildProperLossForest H rank).parent (E.image a)) = some parent := by
    simpa only [hImageParent] using hpk

  have hChildRead : exitBackKey? r i.val = some child := by
    simp only [exitBackKey?, if_neg hi, hcb]
  have hParentRead :
      exitBackKey? r (actualPhysicalParent r i.val) = some parent := by
    simp only [exitBackKey?, if_neg hp0, hpb]
  exact ⟨a, child, parent, rfl, hp0, hp, hcb, hpb, hcs, hps, hck,
    hParentKey, by simp only [exitHeadKeys?, hit, hChildRead, hParentRead]⟩

end

end PaperB.Exit.OrderedReaderResult
