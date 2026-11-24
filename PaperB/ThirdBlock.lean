module

public import PaperB.ThirdBlockForward
public import PaperB.ThirdBlockLift

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace PaperB.Digraph

open LabelledQuotient

/-- Split the given path itself, rather than finding a new path to `m`. -/
private theorem splitSurvivingAt {V : Type} {arc : V → V → Prop}
    {failed : V → Prop} {s t : V} (m : V)
    (p : AvoidPath arc failed s t) :
    AvoidPath arc (fun v => failed v ∨ v = m) s t ∨
      (AvoidPath arc failed s m ∧ AvoidPath arc failed m t) := by
  classical
  induction p with
  | refl v hv =>
      by_cases h : v = m
      · subst v
        exact Or.inr ⟨AvoidPath.refl m hv, AvoidPath.refl m hv⟩
      · exact Or.inl (AvoidPath.refl v (fun hf => hf.elim hv h))
  | step v w z hv edge tail ih =>
      by_cases h : v = m
      · subst v
        exact Or.inr ⟨AvoidPath.refl m hv, AvoidPath.step m w z hv edge tail⟩
      · rcases ih with clean | ⟨prePath, suffix⟩
        · exact Or.inl (AvoidPath.step v w z (fun hf => hf.elim hv h) edge clean)
        · exact Or.inr ⟨AvoidPath.step v w m hv edge prePath, suffix⟩

/-- Restrict a path to a subtype when every vertex on the path is a member. -/
private theorem liftSurvivingSubtype {V : Type} {arc : V → V → Prop}
    {member failed : V → Prop} {s t : V}
    (p : AvoidPath arc (fun v => failed v ∨ ¬ member v) s t) :
    ∀ (hs : member s) (ht : member t),
      AvoidPath (fun u v : Subtype member => arc u.val v.val)
        (fun v => failed v.val) ⟨s, hs⟩ ⟨t, ht⟩ := by
  induction p with
  | refl v hv =>
      intro hs ht
      exact AvoidPath.refl (⟨v, hs⟩ : Subtype member) (fun hf => hv (Or.inl hf))
  | step v w z hv edge tail ih =>
      intro hs ht
      have hw : member w :=
        Classical.byContradiction (fun hn => tail.source_alive (Or.inr hn))
      exact AvoidPath.step
        (⟨v, hs⟩ : Subtype member) ⟨w, hw⟩ ⟨z, ht⟩
        (fun hf => hv (Or.inl hf)) edge (ih hw ht)

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}

private theorem splitSurvivingAtDominator
    {failed : Fin g.vertexCount → Prop} (t : SiblingVertex g r d)
    (p : g.SurvivingPath failed r t.val) :
    g.SurvivingPath failed r d ∧ g.SurvivingPath failed d t.val := by
  rcases splitSurvivingAt d p with clean | split
  · exfalso
    have avoidD : g.SurvivingPath (fun v => v = d) r t.val :=
      AvoidPath.mono clean (fun _ h => Or.inr h)
    first
    | exact t.property.2 avoidD
    | exact t.property.2 (AvoidPath.mono avoidD (fun _ h => h.symm))
  · exact split

section

variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)
variable (hd : g.InitiallyReachable r d)

include g r d rank parent progress injective spec hd

local notation "S" => (siblingBlockSystem progress injective spec hd)
local notation "Q" => (finiteSiblingQuotient progress injective spec hd)
local notation "Key" => (SiblingBlockKey g r d parent)
local notation "rootKey" => (SiblingBlockKey.root g r d parent)
local notation "enc" => (encodeSiblingBlockKey g r d parent)
local notation "dec" => (decodeSiblingBlockKey g r d parent)

private theorem thirdEncodeRoot : enc rootKey = (Q).root := by
  change enc rootKey = enc _
  refine congrArg (encodeSiblingBlockKey g r d parent) ?_
  first
  | rfl
  | exact (siblingBlockOf_leader progress injective spec hd rootKey).symm

private theorem thirdEncodePath (B : CutPair Q) {c k : Key}
    (p : AvoidPath (S).QuotientEdge (fun b => B.Mem (enc b)) c k) :
    AvoidPath (Q).HasQuotientArc B.Mem (enc c) (enc k) := by
  have hp := (finiteSiblingQuotient_avoidPath_iff progress injective spec hd
    (fun b => B.Mem (enc b)) (enc c) (enc k)).mpr
      (by simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using p)
  have hFail : (fun i : Fin (Q).vertexCount => B.Mem (enc (dec i))) = B.Mem := by
    funext i
    have hi : enc (dec i) = i := by
      apply encodeSiblingBlockKey_decodeSiblingBlockKey
    have hm : B.Mem (enc (dec i)) = B.Mem i :=
      congrArg (fun j : Fin (Q).vertexCount => B.Mem j) hi
    exact propext ⟨Eq.mp hm, Eq.mpr hm⟩
  rw [← hFail]
  exact hp

/-- Encode this particular crossing, keeping its physical tail as the label. -/
private theorem thirdEncodeLabel {c k : Key} {x : SiblingVertex g r d}
    (h : (S).LabelledStep c k x) :
    (⟨enc k, x.val⟩ : QuotientArc g.vertexCount (Q).vertexCount) ∈
      (Q).outArcs (enc c) := by
  let e : SiblingEmission g r d parent := ⟨c, k, x.val⟩
  have he : e ∈ siblingEmissions progress injective spec :=
    (mem_siblingEmissions_iff_labelledStep progress injective spec hd e).mpr
      ⟨x.property, h⟩
  refine (mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd
    (enc c) ⟨enc k, x.val⟩).mpr ⟨e, he, ?_, ?_, rfl⟩
  · change c = dec (enc c)
    rw [decodeSiblingBlockKey_encodeSiblingBlockKey]
  · change k = dec (enc k)
    rw [decodeSiblingBlockKey_encodeSiblingBlockKey]

/-- Decode the label of the selected occurrence, not just its endpoints. -/
private theorem thirdDecodeLabel {s : Fin (Q).vertexCount}
    {a : QuotientArc g.vertexCount (Q).vertexCount}
    (ha : a ∈ (Q).outArcs s) :
    g.HasArc a.origTail ((S).leader (dec a.head)).val := by
  obtain ⟨e, he, _, hdst, htail⟩ :=
    (mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd s a).mp ha
  obtain ⟨_, hstep⟩ :=
    (mem_siblingEmissions_iff_labelledStep progress injective spec hd e).mp he
  rcases hstep with ⟨_, _, hout⟩
  change g.HasArc e.tail ((S).leader e.destination).val at hout
  simpa only [hdst, htail] using hout

private theorem thirdExitTailMemIff (B : CutPair Q)
    {s j : Fin (Q).vertexCount} {x : Fin g.vertexCount}
    (hs : B.Mem s) (hj : ¬ B.Mem j) :
    (Q).ExitTailMem B s j x ↔
      ∃ a ∈ (Q).outArcs s,
        a.origTail = x ∧ AvoidPath (Q).HasQuotientArc B.Mem a.head j := by
  have zero : AvoidPath (Q).HasQuotientArc B.Mem j j := AvoidPath.refl j hj
  have alive (i : Fin (Q).vertexCount)
      (p : AvoidPath (Q).HasQuotientArc B.Mem i j) : ¬ B.Mem i :=
    p.source_alive
  first
  | rfl
  | unfold LabelledQuotient.ExitTailMem
    grind [alive]

/-- The cut must name exactly the two designated sibling blocks. The two
failed vertices need not be the leaders of those blocks. -/
theorem lemma22_third_survivingPath_iff_exitTailMem
    (B : CutPair Q) (a b t : SiblingVertex g r d)
    (ha : a.val ≠ d) (hb : b.val ≠ d)
    (ht₁ : (S).block t ≠ (S).block a)
    (ht₂ : (S).block t ≠ (S).block b)
    (hB : ∀ i : Fin (Q).vertexCount,
      B.Mem i ↔ i = enc ((S).block a) ∨ i = enc ((S).block b)) :
    g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r t.val ↔
      (AvoidPath (Q).HasQuotientArc B.Mem (Q).root (enc ((S).block t)) ∨
        ∃ (s : Fin (Q).vertexCount) (x : Fin g.vertexCount),
          B.Mem s ∧
          g.SurvivingPath (fun v => v = a.val ∨ v = b.val) r x ∧
          (Q).ExitTailMem B s (enc ((S).block t)) x) := by
  let failed : Fin g.vertexCount → Prop := fun v => v = a.val ∨ v = b.val
  have hKey (k : Key) :
      B.Mem (enc k) ↔ k = (S).block a ∨ k = (S).block b := by
    rw [hB (enc k)]
    constructor
    · rintro (h | h)
      · exact Or.inl (by
          simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
            congrArg (decodeSiblingBlockKey g r d parent) h)
      · exact Or.inr (by
          simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
            congrArg (decodeSiblingBlockKey g r d parent) h)
    · rintro (h | h)
      · exact Or.inl (congrArg (encodeSiblingBlockKey g r d parent) h)
      · exact Or.inr (congrArg (encodeSiblingBlockKey g r d parent) h)
  have htB : ¬ B.Mem (enc ((S).block t)) :=
    fun h => ((hKey ((S).block t)).mp h).elim ht₁ ht₂
  constructor
  · intro p
    change g.SurvivingPath failed r t.val at p
    obtain ⟨prePath, suffix⟩ := splitSurvivingAtDominator t p
    have within := survivingPath_within_dominator_subtree
      (r := r) (d := d) (failed := failed)
      progress t.property.1 t.property.2 suffix
    have sub : AvoidPath (S).arc (fun v => failed v.val) ((S).leader rootKey) t :=
      liftSurvivingSubtype within ((S).leader rootKey).property t.property
    have encodeClean {c k : Key}
        (path : AvoidPath (S).QuotientEdge
          (fun j => j = (S).block a ∨ j = (S).block b) c k) :
        AvoidPath (Q).HasQuotientArc B.Mem (enc c) (enc k) :=
      thirdEncodePath progress injective spec hd B
        (AvoidPath.mono path (fun j hj => (hKey j).mp hj))
    rcases (S).forward_last_exit
        (siblingBlockSystem_enter progress injective spec hd) sub ht₁ ht₂ with
        clean | ⟨x, y, hx, toX, _, _, labelled, _, afterExit⟩
    · exact Or.inl (by
        simpa only [thirdEncodeRoot progress injective spec hd] using encodeClean clean)
    · have tailPrefix : g.SurvivingPath failed d x.val :=
        AvoidPath.projectSubtypeVal (arc := g.HasArc) (failed := failed) toX
      have seed : g.SurvivingPath failed r x.val :=
        AvoidPath.trans prePath tailPrefix
      have hxB : B.Mem (enc ((S).block x)) := (hKey ((S).block x)).mpr hx
      have hlabel := thirdEncodeLabel progress injective spec hd labelled
      have hexit : (Q).ExitTailMem B (enc ((S).block x)) (enc ((S).block t)) x.val :=
        (thirdExitTailMemIff progress injective spec hd B hxB htB).mpr
          ⟨⟨enc ((S).block y), x.val⟩, hlabel, rfl, encodeClean afterExit⟩
      exact Or.inr ⟨enc ((S).block x), x.val, hxB, seed, hexit⟩
  · intro h
    have haB : B.Mem (enc ((S).block a)) := (hKey ((S).block a)).mpr (Or.inl rfl)
    have hbB : B.Mem (enc ((S).block b)) := (hKey ((S).block b)).mpr (Or.inr rfl)
    refine lemma22_third_backward_of_exitTailMem progress injective spec hd
      B a b t ha hb haB hbB ?_ h
    intro s x hs hexit
    obtain ⟨e, he, htail, continuation⟩ :=
      (thirdExitTailMemIff progress injective spec hd B hs htB).mp hexit
    refine ⟨e.head, ?_, continuation⟩
    simpa only [htail] using thirdDecodeLabel progress injective spec hd he

end

end PaperB.Digraph
