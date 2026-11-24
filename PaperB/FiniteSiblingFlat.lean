module

-- PaperB/FiniteSiblingFlat.lean
-- Repository lean-toolchain: leanprover/lean4:v4.35.0-rc3

public import PaperB.FiniteSiblingQuotient
public import PaperB.Exit

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB.Digraph

open PaperB.LabelledQuotient

private theorem avoidPath_mapTransport
    {α β : Type} {edge : α → α → Prop} {edge' : β → β → Prop}
    {failed : α → Prop} {failed' : β → Prop}
    (f : α → β)
    (mapEdge : ∀ a b, edge a b → edge' (f a) (f b))
    (reflectFailure : ∀ a, failed' (f a) → failed a)
    {s t : α} (h : AvoidPath edge failed s t) :
    AvoidPath edge' failed' (f s) (f t) := by
  have mapAlive (a : α) (ha : ¬ failed a) : ¬ failed' (f a) :=
    fun hf => ha (reflectFailure a hf)
  induction h <;> constructor <;>
    first
    | assumption
    | exact mapEdge _ _ (by assumption)
    | exact mapAlive _ (by assumption)

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)

/-- Failure of a finite index means failure of its decoded block key. -/
theorem finiteSiblingQuotient_avoidPath_iff
    (hd : g.InitiallyReachable r d)
    (failed : SiblingBlockKey g r d parent → Prop)
    (s t : Fin (siblingBlockKeys g r d parent).length) :
    AvoidPath (finiteSiblingQuotient progress injective spec hd).HasQuotientArc
        (fun i => failed (decodeSiblingBlockKey g r d parent i)) s t ↔
      AvoidPath (siblingBlockSystem progress injective spec hd).QuotientEdge
        failed (decodeSiblingBlockKey g r d parent s)
          (decodeSiblingBlockKey g r d parent t) := by
  constructor
  · intro h
    exact avoidPath_mapTransport (decodeSiblingBlockKey g r d parent)
      (fun u w hu =>
        (finiteSiblingQuotient_hasQuotientArc_iff
          progress injective spec hd u w).mp hu)
      (fun _ hf => hf) h
  · intro h
    have henc := avoidPath_mapTransport
      (edge' := (finiteSiblingQuotient progress injective spec hd).HasQuotientArc)
      (failed' := fun i => failed (decodeSiblingBlockKey g r d parent i))
      (encodeSiblingBlockKey g r d parent)
      (fun a b hab =>
        (finiteSiblingQuotient_hasQuotientArc_iff progress injective spec hd
          (encodeSiblingBlockKey g r d parent a)
          (encodeSiblingBlockKey g r d parent b)).mpr (by
            simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using hab))
      (fun a ha => by
        simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using ha)
      h
    simpa only [encodeSiblingBlockKey_decodeSiblingBlockKey] using henc

private theorem finiteSiblingQuotient_decode_root
    (hd : g.InitiallyReachable r d) :
    decodeSiblingBlockKey g r d parent
        (finiteSiblingQuotient progress injective spec hd).root =
      SiblingBlockKey.root g r d parent := by
  change decodeSiblingBlockKey g r d parent
    (encodeSiblingBlockKey g r d parent _) = SiblingBlockKey.root g r d parent
  rw [decodeSiblingBlockKey_encodeSiblingBlockKey] <;>
    exact siblingBlockOf_leader progress injective spec hd
      (SiblingBlockKey.root g r d parent)

/-- EX1.3 for the finite quotient, independently of construction time. -/
theorem finiteSiblingQuotient_isFlat (hd : g.InitiallyReachable r d) :
    (finiteSiblingQuotient progress injective spec hd).IsFlat := by
  let Q := finiteSiblingQuotient progress injective spec hd
  let decode := decodeSiblingBlockKey g r d parent
  have hdecode : Function.Injective decode := by
    intro i j hij
    simpa only [decode, encodeSiblingBlockKey_decodeSiblingBlockKey] using
      congrArg (encodeSiblingBlockKey g r d parent) hij
  have hroot : decode Q.root = SiblingBlockKey.root g r d parent :=
    finiteSiblingQuotient_decode_root progress injective spec hd
  have reach (t : Fin Q.vertexCount) :
      AvoidPath Q.HasQuotientArc (fun _ => False) Q.root t := by
    apply (finiteSiblingQuotient_avoidPath_iff progress injective spec hd
      (fun _ => False) Q.root t).mpr
    change AvoidPath (siblingBlockSystem progress injective spec hd).QuotientEdge
      (fun _ => False) (decode Q.root) (decode t)
    rw [hroot]
    exact siblingBlockSystem_root_path progress injective spec hd (decode t)
  have avoid (b t : Fin Q.vertexCount) (hb : b ≠ Q.root) (ht : t ≠ b) :
      AvoidPath Q.HasQuotientArc (fun i => i = b) Q.root t := by
    have hb' : decode b ≠ SiblingBlockKey.root g r d parent :=
      fun h => hb (hdecode (h.trans hroot.symm))
    have ht' : decode t ≠ decode b :=
      fun h => ht (hdecode h)
    have hp : AvoidPath Q.HasQuotientArc (fun i => decode i = decode b) Q.root t := by
      apply (finiteSiblingQuotient_avoidPath_iff progress injective spec hd
        (fun k => k = decode b) Q.root t).mpr
      change AvoidPath (siblingBlockSystem progress injective spec hd).QuotientEdge
        (fun k => k = decode b) (decode Q.root) (decode t)
      rw [hroot]
      exact siblingBlockSystem_root_path_avoiding progress injective spec hd
        (decode b) (decode t) hb' ht'
    exact AvoidPath.mono hp (fun _ hi => congrArg decode hi)
  have avoid' (b t : Fin Q.vertexCount) (hb : b ≠ Q.root) (ht : t ≠ b) :
      AvoidPath Q.HasQuotientArc (fun i => b = i) Q.root t :=
    AvoidPath.mono (avoid b t hb ht) (fun _ hi => hi.symm)
  change Q.IsFlat
  exact ⟨reach, avoid⟩

theorem finiteSiblingRank_injective (hd : g.InitiallyReachable r d) :
    Function.Injective (finiteSiblingRank progress injective spec hd) := by
  let S := siblingBlockSystem progress injective spec hd
  let decode := decodeSiblingBlockKey g r d parent
  intro u w huw
  have hv : (S.leader (decode u)).val = (S.leader (decode w)).val :=
    injective huw
  have hl : S.leader (decode u) = S.leader (decode w) :=
    Subtype.ext hv
  have hk : decode u = decode w := by
    simpa only [S.leader_block] using congrArg S.block hl
  simpa only [decode, encodeSiblingBlockKey_decodeSiblingBlockKey] using
    congrArg (encodeSiblingBlockKey g r d parent) hk

/-- EX3.3 on a real edge of the proper-loss forest of the finite sibling
quotient. The forest-edge hypotheses are those of the exact transfer theorem.
The argument `x` is the original physical tail, not a block index. -/
noncomputable abbrev finiteSiblingQuotient_edge_exitTailMem_iff
    (hd : g.InitiallyReachable r d) {x : Fin g.vertexCount} :=
  @buildProperLossForest_edge_exitTailMem_iff
    (H := finiteSiblingQuotient progress injective spec hd)
    (rank := finiteSiblingRank progress injective spec hd)
    (rankArc := by
      intro u w h
      exact finiteSiblingRank_lt_of_hasQuotientArc progress injective spec hd h)
    (flat := finiteSiblingQuotient_isFlat progress injective spec hd)
    (x := x)

end PaperB.Digraph
