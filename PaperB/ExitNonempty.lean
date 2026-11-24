module

public import PaperB.Forest

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB
namespace LabelledQuotient

/-- Each endpoint of `B` has a physical exit tail on `H` to every proper loss. -/
theorem properLoss_both_exitTailMem_nonempty_of_flat_rank
    {H : LabelledQuotient} {B : CutPair H}
    {rank : Fin H.vertexCount → Nat}
    (rankArc : ∀ u v, H.HasQuotientArc u v → rank u < rank v)
    (flat : H.IsFlat) {y : Fin H.vertexCount}
    (proper : H.ProperLoss B y) :
    (∃ x : Fin H.origVertexCount, H.ExitTailMem B B.fst y x) ∧
    (∃ x : Fin H.origVertexCount, H.ExitTailMem B B.snd y x) := by
  have endpointExit (keep deleted : Fin H.vertexCount)
      (hDeleted : deleted ≠ H.root)
      (hyKeep : y ≠ keep) (hyDeleted : y ≠ deleted)
      (endpoints : ∀ z, B.Mem z → z = keep ∨ z = deleted) :
      ∃ x : Fin H.origVertexCount, H.ExitTailMem B keep y x := by
    -- After the exit step, rank rules out any return to `keep`.
    have afterKeep {u v : Fin H.vertexCount}
        (path : H.SurvivingPath (fun z => z = deleted) u v) :
        rank keep < rank u → H.SurvivingPath B.Mem u v := by
      have aliveOfRank (z : Fin H.vertexCount)
          (later : rank keep < rank z) (alive : z ≠ deleted) : ¬ B.Mem z := by
        intro hz
        rcases endpoints z hz with hKeep | hDel
        · exact (Nat.ne_of_lt later) (congrArg rank hKeep.symm)
        · exact alive hDel
      induction path with
      | refl z alive =>
          intro later
          exact AvoidPath.refl z (aliveOfRank z later alive)
      | step z next tgt alive arc rest ih =>
          intro later
          exact AvoidPath.step z next tgt (aliveOfRank z later alive) arc
            (ih (Nat.lt_trans later (rankArc z next arc)))

    -- Split at `keep`, or rebuild the path avoiding both endpoints.
    have splitAtKeep {u v : Fin H.vertexCount}
        (path : H.SurvivingPath (fun z => z = deleted) u v) :
        v ≠ keep →
          (∃ x : Fin H.origVertexCount, H.ExitTailMem B keep v x) ∨
            H.SurvivingPath B.Mem u v := by
      induction path with
      | refl z alive =>
          intro hzKeep
          exact Or.inr (AvoidPath.refl z (fun hz => (endpoints z hz).elim hzKeep alive))
      | step z next tgt alive arc rest ih =>
          intro htgt
          by_cases hz : z = keep
          · subst z
            have suffix : H.SurvivingPath B.Mem next tgt :=
              afterKeep rest (rankArc keep next arc)
            rcases arc with ⟨e, he, hHead⟩
            subst next
            exact Or.inl ⟨_, e, he, rfl, suffix⟩
          · rcases ih htgt with hExit | hAvoid
            · exact Or.inl hExit
            · exact Or.inr (AvoidPath.step z next tgt
                (fun h => (endpoints z h).elim hz alive) arc hAvoid)

    have path : H.SurvivingPath (fun z => z = deleted) H.root y :=
      flat.2 deleted y hDeleted hyDeleted
    rcases splitAtKeep path hyKeep with hExit | hAvoid
    · exact hExit
    · exact False.elim (proper.1 hAvoid)

  have hyFst : y ≠ B.fst := fun h => proper.2 (Or.inl h)
  have hySnd : y ≠ B.snd := fun h => proper.2 (Or.inr h)
  exact ⟨endpointExit B.fst B.snd B.snd_ne_root hyFst hySnd (fun _ h => h),
    endpointExit B.snd B.fst B.fst_ne_root hySnd hyFst
      (fun _ h => h.elim Or.inr Or.inl)⟩

/-- The same labelled witnesses under the quotient's acyclicity contract. -/
theorem properLoss_both_exitTailMem_nonempty_of_flat_acyclic
    {H : LabelledQuotient} {B : CutPair H}
    (acyclic : H.IsAcyclic) (flat : H.IsFlat)
    {y : Fin H.vertexCount} (proper : H.ProperLoss B y) :
    (∃ x : Fin H.origVertexCount, H.ExitTailMem B B.fst y x) ∧
    (∃ x : Fin H.origVertexCount, H.ExitTailMem B B.snd y x) := by
  obtain ⟨rank, rankArc⟩ := acyclic
  exact properLoss_both_exitTailMem_nonempty_of_flat_rank rankArc flat proper

end LabelledQuotient
end PaperB
