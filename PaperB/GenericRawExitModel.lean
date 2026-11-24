module

-- PaperB/GenericRawExitModel.lean
public import PaperB.ExitRawIncoming
public import PaperB.ForestIncomingRaw
public import PaperB.PhysicalExitModel

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PaperB.GenericRawExitModel

open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ExitMap
open PaperB.ExitSummary

/-- Executable inputs. `entryRank` reads physical DFS entry ranks; it is
not the topological rank used to certify the quotient forest. -/
structure Runtime (H : LabelledQuotient) where
  raw : ForestIncomingRaw.Prepared H
  entryRank : Fin H.origVertexCount → Nat

def Runtime.incoming {H : LabelledQuotient} (R : Runtime H)
    (y : Fin H.vertexCount) : List (ForestIncomingRaw.Entry H) :=
  ForestIncomingRaw.row H R.raw y

def source {H : LabelledQuotient} (e : ForestIncomingRaw.Entry H) :
    Fin H.vertexCount :=
  e.1

def physicalTail {H : LabelledQuotient} (e : ForestIncomingRaw.Entry H) :
    Fin H.origVertexCount :=
  e.2.origTail

/-- Read the existing row. The preparation identity is used only in proofs;
neither extraction of the row nor either occurrence projection uses it. -/
theorem mem_incoming {H : LabelledQuotient} (R : Runtime H)
    (raw_eq : R.raw = ForestIncomingRaw.prepare H)
    (z y : Fin H.vertexCount)
    (a : QuotientArc H.origVertexCount H.vertexCount) :
    (z, a) ∈ R.incoming y ↔ a ∈ H.outArcs z ∧ a.head = y := by
  unfold Runtime.incoming
  rw [raw_eq]
  exact ForestIncomingRaw.mem_row H z y a

theorem arc_iff_incoming {H : LabelledQuotient} (R : Runtime H)
    (raw_eq : R.raw = ForestIncomingRaw.prepare H)
    (z y : Fin H.vertexCount) :
    H.HasQuotientArc z y ↔
      ∃ e ∈ R.incoming y, source (H := H) e = z := by
  unfold LabelledQuotient.HasQuotientArc
  constructor
  · rintro ⟨a, ha, hy⟩
    exact ⟨(z, a), (mem_incoming R raw_eq z y a).mpr ⟨ha, hy⟩, rfl⟩
  · rintro ⟨⟨u, a⟩, he, hu⟩
    change u = z at hu
    subst u
    obtain ⟨ha, hy⟩ := (mem_incoming R raw_eq z y a).mp he
    exact ⟨a, ha, hy⟩

/-- Last-exit equivalence in outgoing-occurrence form. The surviving suffix
starts at the head of the exit arc, not at its deleted source. -/
private theorem lastExit_iff_out {H : LabelledQuotient}
    (B : CutPair H) (s y : Fin H.vertexCount)
    (x : Fin H.origVertexCount) (hs : B.Mem s) :
    H.ExitTailMem B s y x ↔
      ∃ a ∈ H.outArcs s,
        a.origTail = x ∧ H.SurvivingPath B.Mem a.head y := by
  unfold LabelledQuotient.ExitTailMem
  first
  | rfl
  | (simp only [hs, true_and, and_true]; done)
  | have alive (w : Fin H.vertexCount)
        (p : H.SurvivingPath B.Mem w y) : ¬ B.Mem w := by
      change AvoidPath H.HasQuotientArc B.Mem w y at p
      cases p <;> assumption
    grind

theorem exit_iff_incoming {H : LabelledQuotient} (R : Runtime H)
    (raw_eq : R.raw = ForestIncomingRaw.prepare H)
    (B : CutPair H) (s y : Fin H.vertexCount)
    (x : Fin H.origVertexCount) (hs : B.Mem s) :
    H.ExitTailMem B s y x ↔
      ∃ w e, e ∈ R.incoming w ∧ source (H := H) e = s ∧
        physicalTail (H := H) e = x ∧ H.SurvivingPath B.Mem w y := by
  refine (lastExit_iff_out B s y x hs).trans ?_
  constructor
  · rintro ⟨a, ha, hx, hp⟩
    exact ⟨a.head, (s, a),
      (mem_incoming R raw_eq s a.head a).mpr ⟨ha, rfl⟩, rfl, hx, hp⟩
  · rintro ⟨w, ⟨u, a⟩, he, hu, hx, hp⟩
    change u = s at hu
    subst u
    obtain ⟨ha, hw⟩ := (mem_incoming R raw_eq s w a).mp he
    refine ⟨a, ha, hx, ?_⟩
    simpa only [hw] using hp

def ends {H : LabelledQuotient} (B : CutPair H) :
    Two (Fin H.vertexCount) :=
  ⟨B.fst, B.snd⟩

theorem mem_iff_ends {H : LabelledQuotient} (B : CutPair H)
    (s : Fin H.vertexCount) :
    B.Mem s ↔ ∃ j : Fin 2, Two.get (ends B) j = s := by
  unfold CutPair.Mem
  constructor
  · rintro (h | h)
    · refine ⟨0, ?_⟩
      rw [Two.get_zero]
      first | exact h | exact h.symm
    · refine ⟨1, ?_⟩
      rw [Two.get_one]
      first | exact h | exact h.symm
  · rintro ⟨j, hj⟩
    have hlt := j.isLt
    have hv : j.val = 0 ∨ j.val = 1 := by omega
    have hj' : j = 0 ∨ j = 1 :=
      hv.elim (fun h => Or.inl (Fin.ext h)) (fun h => Or.inr (Fin.ext h))
    rcases hj' with h | h
    · subst j
      rw [Two.get_zero] at hj
      apply Or.inl
      first | exact hj | exact hj.symm
    · subst j
      rw [Two.get_one] at hj
      apply Or.inr
      first | exact hj | exact hj.symm

/-- Driver inputs. A physical edge slot is not itself a forest node index. -/
structure ForestInputs (H : LabelledQuotient) (F : ProperLossForest H)
    (m : Nat) where
  owner : Fin H.vertexCount → Option (CutPair H)
  slots : Array (Fin (F.realNodeCount + 1))
  size_eq : slots.size = m
  child : Fin m → CutPair H
  parent : Fin m → CutPair H

def ForestInputs.edgeNode {H : LabelledQuotient} {F : ProperLossForest H}
    {m : Nat} (D : ForestInputs H F m) (i : Fin m) :
    Fin (F.realNodeCount + 1) :=
  D.slots[i.val]'(by simpa only [D.size_eq] using i.isLt)

/-- Agreement of the supplied owner and decoded physical keys with the actual
labels and parent links. These are lookup certificates, not loss or transfer
hypotheses. -/
structure KeyAgreement {H : LabelledQuotient} {F : ProperLossForest H}
    {m : Nat} (D : ForestInputs H F m) : Prop where
  owner_eq : ∀ y, D.owner y = F.nodeKey? (F.label y)
  child_at : ∀ i, F.nodeKey? (D.edgeNode i) = some (D.child i)
  parent_at : ∀ i, F.nodeKey? (F.parent (D.edgeNode i)) = some (D.parent i)

private abbrev antecedent {P Q : Prop} (_ : P → Q) : Prop := P

/-- The exact flatness premise of the canonical forest labelling law. Taking
it from the law avoids introducing another definition of quotient flatness. -/
abbrev FlatLaw (H : LabelledQuotient) (qRank : Fin H.vertexCount → Nat)
    (progress : ∀ u v, H.HasQuotientArc u v → qRank u < qRank v)
    (injective : Function.Injective qRank) : Prop :=
  antecedent (fun flat
    (n : Fin ((buildProperLossForest H qRank).realNodeCount + 1))
    (B : CutPair H)
    (hk : (buildProperLossForest H qRank).nodeKey? n = some B)
    (y : Fin H.vertexCount) =>
      buildProperLossForest_properLoss_iff_of_node
        (H := H) (rank := qRank) progress
        (fun _ _ h => injective h) flat hk y)

/-- Specification only. No runtime reader calls this function. -/
private noncomputable def referenceTails {H : LabelledQuotient}
    (B : CutPair H) (s y : Fin H.vertexCount) :
    List (Fin H.origVertexCount) := by
  classical
  exact (List.finRange H.origVertexCount).filter
    (fun x => decide (H.ExitTailMem B s y x))

private theorem mem_referenceTails {H : LabelledQuotient}
    (B : CutPair H) (s y : Fin H.vertexCount) (x : Fin H.origVertexCount) :
    x ∈ referenceTails B s y ↔ H.ExitTailMem B s y x := by
  classical
  simp [referenceTails, List.mem_filter]

/-- Proof-only EX4.2 model. Its runtime projections are definitionally the raw
row reader, the two packed occurrence projections, and the supplied rank and
driver readers. In particular it does not run `prepare` again. -/
noncomputable def model {H : LabelledQuotient} {m : Nat}
    (R : Runtime H) (raw_eq : R.raw = ForestIncomingRaw.prepare H)
    (qRank : Fin H.vertexCount → Nat)
    (progress : ∀ u v, H.HasQuotientArc u v → qRank u < qRank v)
    (injective : Function.Injective qRank)
    (flat : FlatLaw H qRank progress injective)
    (D : ForestInputs H (buildProperLossForest H qRank) m)
    (keys : KeyAgreement D) : BuiltExit.Model H m := by
  refine
    { Occ := ForestIncomingRaw.Entry H
      incoming := R.incoming
      source := source (H := H)
      physicalTail := physicalTail (H := H)
      rank := R.entryRank
      arc_iff := arc_iff_incoming R raw_eq
      exit_iff := exit_iff_incoming R raw_eq
      ends := ends
      mem_iff := mem_iff_ends
      owner := D.owner
      ownerProper := ?_
      forest := buildProperLossForest H qRank
      edgeNode := D.edgeNode
      child := D.child
      parent := D.parent
      childKey := keys.child_at
      parentKey := keys.parent_at
      transfer := ?_
      tails := referenceTails
      tails_iff := fun B s y x _ => mem_referenceTails B s y x }
  · intro y B h
    have hk : (buildProperLossForest H qRank).nodeKey?
        ((buildProperLossForest H qRank).label y) = some B :=
      (keys.owner_eq y).symm.trans h
    refine (buildProperLossForest_properLoss_iff_of_node
      (H := H) (rank := qRank) progress
      (fun _ _ he => injective he) flat hk y).mpr ?_
    apply IsForestAncestor.refl
  · intro i s y x hs hy
    have ht := buildProperLossForest_edge_exitTailMem_iff
      (H := H) (rank := qRank) progress flat
      (keys.child_at i) (keys.parent_at i) (x := x) hs hy
    unfold IsFreshEndpoint at ht
    first
    | exact ht
    | simpa only [and_assoc] using ht
    | grind

end PaperB.GenericRawExitModel
