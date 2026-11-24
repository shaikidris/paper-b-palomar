module

public import PaperB.ActualJumpMaps

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.ExitMap.CheckedFold

/-- Build the map record from the parent and jump already read from the
physical record. Only the skew branch reads old map records. -/
def buildOneSlot (old : Store) (packedParent packedJump : Nat)
    (edge : Map) : Stored :=
  if packedJump = packedParent then
    Stored.parentOnly packedParent edge
  else
    let rp := old packedParent
    let rq := old rp.jump
    Stored.skew packedParent edge rp rq

/-- `rank` is the common depth view, including the new slot. The old
certificates concern the pre-write store and are needed only in the skew
branch. -/
theorem buildOneSlot_exact
    (F : JumpForest) (p packedParent packedJump : Nat)
    (old : Store) (rank : Nat → Nat) (edge : Map)
    (hParent : packedParent = p)
    (hPackedJump :
      let a := F.jumpOf p
      let b := F.jumpOf a
      let len1 := F.depthOf p - F.depthOf a
      let len2 := F.depthOf a - F.depthOf b
      packedJump = (if 0 < len1 ∧ len1 = len2 then b else p))
    (hPJump : packedJump ≠ packedParent →
      (old packedParent).jump = F.jumpOf packedParent)
    (hQJump : packedJump ≠ packedParent →
      (old (old packedParent).jump).jump = F.jumpOf (old packedParent).jump)
    (down : rank packedParent < rank F.size)
    (hPOK : packedJump ≠ packedParent → JumpOK old rank packedParent)
    (hQOK : packedJump ≠ packedParent →
      JumpOK old rank (old packedParent).jump) :
    let r := buildOneSlot old packedParent packedJump edge
    let read : Store := fun u => if u = F.size then r else old u
    (read F.size).parent = (F.mkAppendedRecord p).parent ∧
      (read F.size).jump = (F.mkAppendedRecord p).jump ∧
      JumpOK read rank F.size := by
  subst packedParent
  let r := buildOneSlot old p packedJump edge
  let read : Store := fun u => if u = F.size then r else old u
  change (read F.size).parent = (F.mkAppendedRecord p).parent ∧
    (read F.size).jump = (F.mkAppendedRecord p).jump ∧
    JumpOK read rank F.size
  have hNew : read F.size = r := by
    simp [read]
  have hSpecParent : p = (F.mkAppendedRecord p).parent := rfl
  have hSpecJump : packedJump = (F.mkAppendedRecord p).jump := by
    exact hPackedJump
  by_cases hBranch : packedJump = p
  · have hRec : read F.size = Stored.parentOnly p edge := by
      simpa only [r, buildOneSlot, if_pos hBranch] using hNew
    refine ⟨?_, ?_, jumpOK_parentOnly hRec down⟩
    · simpa only [hRec, Stored.parentOnly] using hSpecParent
    · simpa only [hRec, Stored.parentOnly] using (hBranch.symm.trans hSpecJump)
  · have hDest : packedJump = F.jumpOf (F.jumpOf p) := by
      dsimp only at hPackedJump
      split at hPackedJump
      · exact hPackedJump
      · exact False.elim (hBranch hPackedJump)
    have hStoredJump : (old (old p).jump).jump = packedJump :=
      (hQJump hBranch).trans
        ((congrArg F.jumpOf (hPJump hBranch)).trans hDest.symm)
    have hRec : read F.size = Stored.skew p edge (old p) (old (old p).jump) := by
      simpa only [r, buildOneSlot, if_neg hBranch] using hNew
    refine ⟨?_, ?_, ?_⟩
    · simpa only [hRec, Stored.skew] using hSpecParent
    · simpa only [hRec, Stored.skew] using (hStoredJump.trans hSpecJump)
    · have hOld {u : Nat} (hu : rank u < rank F.size) : read u = old u := by
        have hne : u ≠ F.size := by
          intro he
          subst u
          exact (Nat.lt_irrefl _) hu
        simp only [read, if_neg hne]
      -- Below the new slot's rank, a decreasing path cannot read that slot.
      have liftPath {u v : Nat} {m : Map}
          (path : ParentPath old rank u v m) :
          rank u < rank F.size →
            ParentPath read rank u v m ∧ rank v < rank F.size := by
        induction path with
        | nil u =>
          intro hu
          exact ⟨ParentPath.nil u, hu⟩
        | @cons u a m hd tail ih =>
          intro hu
          have huRead : read u = old u := hOld hu
          obtain ⟨ht, ha⟩ := ih (Nat.lt_trans hd hu)
          have hd' : rank (read u).parent < rank u := by
            simpa only [huRead] using hd
          have ht' : ParentPath read rank (read u).parent a m := by
            simpa only [huRead] using ht
          exact ⟨by simpa only [huRead] using (ParentPath.cons u hd' ht'), ha⟩
      obtain ⟨hpPath, hqDown⟩ := liftPath (hPOK hBranch) down
      obtain ⟨hqPath, _⟩ := liftPath (hQOK hBranch) hqDown
      have ep : read p = old p := hOld down
      have eq : read (old p).jump = old (old p).jump := hOld hqDown
      have hpOK : JumpOK read rank p := by
        simpa only [JumpOK, ep] using hpPath
      have hqOK : JumpOK read rank (read p).jump := by
        simpa only [JumpOK, ep, eq] using hqPath
      have hRec' :
          read F.size = Stored.skew p edge (read p) (read (read p).jump) := by
        simpa only [ep, eq] using hRec
      exact jumpOK_skew hRec' down hpOK hqOK

end PaperB.ExitMap.CheckedFold
