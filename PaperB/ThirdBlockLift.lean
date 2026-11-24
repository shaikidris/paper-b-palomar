module

public import PaperB.FiniteSiblingFlat

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Backward reconstruction from an exact decoded exit witness. The `ExitTailMem`
wrapper takes exact-label soundness as an argument: an unlabelled quotient
edge cannot replace the selected physical tail.
-/

namespace PaperB

/-- Forget subtype membership while preserving arcs and vertex failures. -/
theorem AvoidPath.projectSubtypeVal
    {V : Type} {member failed : V → Prop} {arc : V → V → Prop}
    {s t : Subtype member}
    (p : AvoidPath (fun x y : Subtype member => arc x.val y.val)
      (fun x => failed x.val) s t) :
    AvoidPath arc failed s.val t.val := by
  induction p with
  | refl x hx =>
      exact AvoidPath.refl x.val hx
  | step x y z hx hxy _ ih =>
      exact AvoidPath.step x.val y.val z.val hx hxy ih

private theorem lemma22_backward_end_alive
    {V : Type} {arc : V → V → Prop} {failed : V → Prop} {s t : V}
    (p : AvoidPath arc failed s t) : ¬ failed t := by
  induction p with
  | refl _ hx => exact hx
  | step _ _ _ _ _ _ ih => exact ih

namespace Digraph

open LabelledQuotient

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

private theorem lemma22_backward_rank_le
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop} {s t : Fin g.vertexCount}
    (p : AvoidPath g.HasArc failed s t) : rank s ≤ rank t := by
  induction p with
  | refl x _ =>
      exact Nat.le_refl (rank x)
  | step x y _ _ hxy _ ih =>
      exact Nat.le_trans (Nat.le_of_lt (progress x y hxy)) ih

private theorem lemma22_backward_avoid_later
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    {failed : Fin g.vertexCount → Prop} {s t : Fin g.vertexCount}
    (p : g.InitiallyReachable s t) :
    (∀ x, failed x → rank t < rank x) →
      g.SurvivingPath failed s t := by
  change AvoidPath g.HasArc (fun _ => False) s t at p
  change (∀ x, failed x → rank t < rank x) → AvoidPath g.HasArc failed s t
  induction p with
  | refl x _ =>
      intro later
      exact AvoidPath.refl x (fun hx => Nat.lt_irrefl (rank x) (later x hx))
  | step x y z _ hxy tail ih =>
      intro later
      refine AvoidPath.step x y z ?_ hxy (ih later)
      intro hx
      have hxz : rank x < rank z :=
        Nat.lt_of_lt_of_le (progress x y hxy)
          (lemma22_backward_rank_le progress tail)
      exact Nat.lt_irrefl (rank x) (Nat.lt_trans hxz (later x hx))

private theorem lemma22_backward_prefix
    (progress : ∀ x y, g.HasArc x y → rank x < rank y)
    (hd : g.InitiallyReachable r d)
    (a b : SiblingVertex g r d) (ha : a.val ≠ d) (hb : b.val ≠ d) :
    g.SurvivingPath (fun x => x = a.val ∨ x = b.val) r d := by
  have hra : rank d < rank a.val :=
    rank_lt_of_strict_dominator progress a.property.1 a.property.2 (Ne.symm ha)
  have hrb : rank d < rank b.val :=
    rank_lt_of_strict_dominator progress b.property.1 b.property.2 (Ne.symm hb)
  apply lemma22_backward_avoid_later progress hd
  intro x hx
  rcases hx with h | h
  · exact h.symm ▸ hra
  · exact h.symm ▸ hrb

section

variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)
variable (hd : g.InitiallyReachable r d)

include g r d rank parent progress injective spec hd

local notation "Q" => (finiteSiblingQuotient progress injective spec hd)
local notation "S" => (siblingBlockSystem progress injective spec hd)
local notation "enc" => (encodeSiblingBlockKey g r d parent)
local notation "dec" => (decodeSiblingBlockKey g r d parent)

private theorem lemma22_backward_root_value :
    ((S).leader (dec ((Q).root))).val = d := by
  have hroot : dec ((Q).root) = SiblingBlockKey.root g r d parent := by
    change dec (enc _) = SiblingBlockKey.root g r d parent
    rw [decodeSiblingBlockKey_encodeSiblingBlockKey] <;>
      exact siblingBlockOf_leader progress injective spec hd
        (SiblingBlockKey.root g r d parent)
  rw [hroot] <;> rfl

/-- Decode the finite continuation, lift it between leaders, and append the
internal path to the actual original target vertex. -/
private theorem lemma22_third_backward_suffix
    (B : CutPair Q) (a b t : SiblingVertex g r d)
    (haB : B.Mem (enc ((S).block a))) (hbB : B.Mem (enc ((S).block b)))
    {i : Fin (Q).vertexCount}
    (p : AvoidPath (Q).HasQuotientArc B.Mem i (enc ((S).block t))) :
    g.SurvivingPath (fun x => x = a.val ∨ x = b.val)
      ((S).leader (dec i)).val t.val := by
  let failedKey : SiblingBlockKey g r d parent → Prop :=
    fun c => B.Mem (enc c)
  have hp : AvoidPath (Q).HasQuotientArc (fun j => failedKey (dec j))
      i (enc ((S).block t)) := by
    have hfailed : (fun j : Fin (Q).vertexCount => failedKey (dec j)) = B.Mem := by
      funext j
      apply propext
      change B.Mem (enc (dec j)) ↔ B.Mem j
      have hj : enc (dec j) = j := by
        apply encodeSiblingBlockKey_decodeSiblingBlockKey
      rw [hj]
    rw [hfailed]
    exact p
  have hkey : AvoidPath (S).QuotientEdge failedKey (dec i) ((S).block t) := by
    have h := (finiteSiblingQuotient_avoidPath_iff progress injective spec hd
      failedKey i (enc ((S).block t))).mp hp
    simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using h
  have htAlive : ¬ failedKey ((S).block t) :=
    lemma22_backward_end_alive
      (V := SiblingBlockKey g r d parent) (arc := (S).QuotientEdge)
      (failed := failedKey) (s := dec i) (t := (S).block t) hkey
  have hinternal : AvoidPath (S).arc ((S).VertexFailed failedKey)
      ((S).leader ((S).block t)) t :=
    (S).lift_internal htAlive rfl
  have hlift : AvoidPath (S).arc ((S).VertexFailed failedKey)
      ((S).leader (dec i)) t :=
    AvoidPath.trans ((S).lift hkey) hinternal
  have hsub : AvoidPath (S).arc (fun v => v.val = a.val ∨ v.val = b.val)
      ((S).leader (dec i)) t := by
    refine AvoidPath.mono hlift ?_
    intro v hv
    rcases hv with hva | hvb
    · have he : v = a := Subtype.ext hva
      rw [he]
      exact haB
    · have he : v = b := Subtype.ext hvb
      rw [he]
      exact hbB
  exact AvoidPath.projectSubtypeVal
    (arc := g.HasArc) (failed := fun x => x = a.val ∨ x = b.val) hsub

/-- Take the exact physical exit arc. The root-to-tail seed uses the same
two-vertex failure predicate as the resulting path. -/
theorem lemma22_third_backward_from_exact_exit
    (B : CutPair Q) (a b t : SiblingVertex g r d)
    (haB : B.Mem (enc ((S).block a))) (hbB : B.Mem (enc ((S).block b)))
    {x : Fin g.vertexCount} {i : Fin (Q).vertexCount}
    (seed : g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r x)
    (out : g.HasArc x ((S).leader (dec i)).val)
    (continuation : AvoidPath (Q).HasQuotientArc B.Mem i (enc ((S).block t))) :
    g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r t.val := by
  have tailAlive : ¬ (x = a.val ∨ x = b.val) :=
    lemma22_backward_end_alive
      (V := Fin g.vertexCount) (arc := g.HasArc)
      (failed := fun v => v = a.val ∨ v = b.val) (s := r) (t := x) seed
  have suffix := lemma22_third_backward_suffix progress injective spec hd
    B a b t haB hbB continuation
  exact AvoidPath.trans seed
    (AvoidPath.step x ((S).leader (dec i)).val t.val tailAlive out suffix)

/-- A direct exit into the target block uses a zero-length quotient
continuation. The internal leader-to-target path is still appended. -/
theorem lemma22_third_backward_from_direct_exit
    (B : CutPair Q) (a b t : SiblingVertex g r d)
    (haB : B.Mem (enc ((S).block a))) (hbB : B.Mem (enc ((S).block b)))
    {x : Fin g.vertexCount}
    (seed : g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r x)
    (out : g.HasArc x ((S).leader (dec (enc ((S).block t)))).val)
    (ht : ¬ B.Mem (enc ((S).block t))) :
    g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r t.val :=
  lemma22_third_backward_from_exact_exit progress injective spec hd
    B a b t haB hbB seed out (AvoidPath.refl (enc ((S).block t)) ht)

/-- Backward implication with the exit alternative in exact witness form. -/
theorem lemma22_third_backward_of_witness
    (B : CutPair Q) (a b t : SiblingVertex g r d)
    (ha : a.val ≠ d) (hb : b.val ≠ d)
    (haB : B.Mem (enc ((S).block a))) (hbB : B.Mem (enc ((S).block b)))
    (h :
      AvoidPath (Q).HasQuotientArc B.Mem (Q).root (enc ((S).block t)) ∨
      ∃ x : Fin g.vertexCount,
        g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r x ∧
        ∃ i : Fin (Q).vertexCount,
          g.HasArc x ((S).leader (dec i)).val ∧
          AvoidPath (Q).HasQuotientArc B.Mem i (enc ((S).block t))) :
    g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r t.val := by
  rcases h with p | ⟨x, seed, i, out, continuation⟩
  · have suffix := lemma22_third_backward_suffix progress injective spec hd
      B a b t haB hbB p
    have suffix' :
        g.SurvivingPath (fun v => v = a.val ∨ v = b.val) d t.val := by
      simpa only [lemma22_backward_root_value progress injective spec hd]
        using suffix
    exact AvoidPath.trans (lemma22_backward_prefix progress hd a b ha hb) suffix'
  · exact lemma22_third_backward_from_exact_exit progress injective spec hd
      B a b t haB hbB seed out continuation

/-- Backward reconstruction from an `ExitTailMem` test, given the
exact-label decoding obligation for the actual finite sibling encoding. -/
theorem lemma22_third_backward_of_exitTailMem
    (B : CutPair Q) (a b t : SiblingVertex g r d)
    (ha : a.val ≠ d) (hb : b.val ≠ d)
    (haB : B.Mem (enc ((S).block a))) (hbB : B.Mem (enc ((S).block b)))
    (decodeExitTail :
      ∀ {s : Fin (Q).vertexCount} {x : Fin g.vertexCount},
        B.Mem s → (Q).ExitTailMem B s (enc ((S).block t)) x →
        ∃ i : Fin (Q).vertexCount,
          g.HasArc x ((S).leader (dec i)).val ∧
          AvoidPath (Q).HasQuotientArc B.Mem i (enc ((S).block t)))
    (h :
      AvoidPath (Q).HasQuotientArc B.Mem (Q).root (enc ((S).block t)) ∨
      ∃ (s : Fin (Q).vertexCount) (x : Fin g.vertexCount),
        B.Mem s ∧ g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r x ∧
        (Q).ExitTailMem B s (enc ((S).block t)) x) :
    g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r t.val := by
  apply lemma22_third_backward_of_witness progress injective spec hd
    B a b t ha hb haB hbB
  rcases h with p | ⟨s, x, hs, seed, hexit⟩
  · exact Or.inl p
  · exact Or.inr ⟨x, seed, decodeExitTail (s := s) (x := x) hs hexit⟩

end

end Digraph
end PaperB
