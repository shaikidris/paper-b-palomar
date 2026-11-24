module

public import PaperB.ThirdBlock
public import PaperB.ExitNonempty
public import PaperB.PartialBlock
public import PaperB.SemanticLCA

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option quotPrecheck false

namespace PaperB.Digraph

open LabelledQuotient

/-- Enumerate physical tail vertices, not quotient heads or arc occurrences. -/
noncomputable def lemma22ExitTails (H : LabelledQuotient)
    (B : CutPair H) (s j : Fin H.vertexCount) : List (Fin H.origVertexCount) := by
  classical
  exact (List.ofFn (fun i : Fin H.origVertexCount => i)).filter
    (fun x => decide (H.ExitTailMem B s j x))

@[simp] theorem mem_lemma22ExitTails {H : LabelledQuotient}
    {B : CutPair H} {s j : Fin H.vertexCount} {x : Fin H.origVertexCount} :
    x ∈ lemma22ExitTails H B s j ↔ H.ExitTailMem B s j x := by
  classical
  have hx : x ∈ List.ofFn (fun i : Fin H.origVertexCount => i) :=
    List.mem_ofFn.mpr ⟨x, rfl⟩
  simp [lemma22ExitTails, List.mem_filter, hx]

private theorem someSurvivingTail_iff_not_commonDominator
    {g : Digraph} {r f : Fin g.vertexCount} {xs : List (Fin g.vertexCount)}
    {P : Fin g.vertexCount → Prop}
    (own : ∀ x ∈ xs, P x ↔ ¬ g.Dominates r f x) :
    (∃ x ∈ xs, P x) ↔ ¬ g.CommonDominator r xs f := by
  classical
  constructor
  · rintro ⟨x, hx, hp⟩ hall
    exact (own x hx).mp hp (hall x hx)
  · intro hn
    by_cases he : ∃ x ∈ xs, P x
    · exact he
    · exfalso
      apply hn
      intro x hx
      exact Classical.byContradiction
        (fun hdom => he ⟨x, hx, (own x hx).mpr hdom⟩)

private theorem not_commonDominator_iff_not_dominates_lca
    {g : Digraph} {r f l : Fin g.vertexCount} {xs : List (Fin g.vertexCount)}
    (hl : g.IsDominatorLCA r xs l) :
    (¬ g.CommonDominator r xs f) ↔ ¬ g.Dominates r f l := by
  have h : g.CommonDominator r xs f ↔ g.Dominates r f l :=
    IsDominatorLCA.all_dominates_iff (d := f) hl
  exact ⟨fun hn hd => hn (h.mpr hd), fun hn hc => hn (h.mp hc)⟩

section

variable {g : Digraph} {r d : Fin g.vertexCount}
variable {rank : Fin g.vertexCount → Nat}
variable {parent : Fin g.vertexCount → Fin g.vertexCount}
variable (progress : ∀ x y, g.HasArc x y → rank x < rank y)
variable (injective : ∀ ⦃x y⦄, rank x = rank y → x = y)
variable (spec : ParentSpec g r parent)
variable (hd : g.InitiallyReachable r d)

include g r d rank parent progress injective spec hd

local notation "S" => (siblingBlockSystem progress injective spec hd)
local notation "Q" => (finiteSiblingQuotient progress injective spec hd)
local notation "SV" => (SiblingVertex g r d)
local notation "Key" => (SiblingBlockKey g r d parent)
local notation "enc" => (encodeSiblingBlockKey g r d parent)
local notation "dec" => (decodeSiblingBlockKey g r d parent)
local notation "blk" => (S).block
local notation "ix" => (fun z : SV => enc (blk z))
local notation "fails" =>
  (fun (a b : SV) (v : Fin g.vertexCount) => v = a.val ∨ v = b.val)

private theorem semanticExitTailMem_iff
    (B : CutPair Q) {s j : Fin (Q).vertexCount} {x : Fin g.vertexCount}
    (hs : B.Mem s) (hj : ¬ B.Mem j) :
    (Q).ExitTailMem B s j x ↔
      ∃ e ∈ (Q).outArcs s,
        e.origTail = x ∧ AvoidPath (Q).HasQuotientArc B.Mem e.head j := by
  have zero : AvoidPath (Q).HasQuotientArc B.Mem j j := AvoidPath.refl j hj
  have alive (i : Fin (Q).vertexCount)
      (p : AvoidPath (Q).HasQuotientArc B.Mem i j) : ¬ B.Mem i :=
    p.source_alive
  first
  | rfl
  | unfold LabelledQuotient.ExitTailMem
    grind [alive]

/-- Decode the actual labelled occurrence. Its emission supplies both the
reachable sibling vertex and its source block. -/
theorem lemma22_exitTail_provenance
    (B : CutPair Q) {k : Key} {j : Fin (Q).vertexCount}
    {x : Fin g.vertexCount}
    (hk : B.Mem (enc k)) (hj : ¬ B.Mem j)
    (hx : (Q).ExitTailMem B (enc k) j x) :
    (∃ z : SV, z.val = x ∧ blk z = k) ∧ g.InitiallyReachable r x := by
  obtain ⟨e, he, htail, _⟩ :=
    (semanticExitTailMem_iff progress injective spec hd B hk hj).mp hx
  obtain ⟨m, hm, hsrc, _, hmTail⟩ :=
    (mem_outArcs_finiteSiblingQuotient_iff progress injective spec hd
      (enc k) e).mp he
  obtain ⟨hz, hstep⟩ :=
    (mem_siblingEmissions_iff_labelledStep progress injective spec hd m).mp hm
  let z : SV := ⟨m.tail, hz⟩
  have hval : z.val = x := hmTail.trans htail
  rcases hstep with ⟨h₁, h₂, _⟩
  have hblock : blk z = dec (enc k) := by
    first
    | exact h₁.trans hsrc
    | exact h₁.symm.trans hsrc
    | exact h₂.trans hsrc
    | exact h₂.symm.trans hsrc
  refine ⟨⟨z, hval, ?_⟩, ?_⟩
  · simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using hblock
  · rw [← hval]
    exact z.property.1

private theorem semanticCutMem
    (B : CutPair Q) {a b : SV}
    (hfst : B.fst = ix a) (hsnd : B.snd = ix b)
    (i : Fin (Q).vertexCount) :
    B.Mem i ↔ i = ix a ∨ i = ix b := by
  simp only [CutPair.Mem, hfst, hsnd, eq_comm]

private theorem semanticThirdAlive
    (B : CutPair Q) {a b t : SV}
    (hfst : B.fst = ix a) (hsnd : B.snd = ix b)
    (ht₁ : blk t ≠ blk a) (ht₂ : blk t ≠ blk b) :
    ¬ B.Mem (ix t) := by
  intro ht
  rcases (semanticCutMem progress injective spec hd B hfst hsnd (ix t)).mp ht
    with h | h
  · apply ht₁
    simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
      congrArg (decodeSiblingBlockKey g r d parent) h
  · apply ht₂
    simpa only [decodeSiblingBlockKey_encodeSiblingBlockKey] using
      congrArg (decodeSiblingBlockKey g r d parent) h

/-- Each endpoint's list inherits provenance from its physical exit labels.
The own-block theorems then decide survival for those same vertices. -/
theorem lemma22_third_endpoint_tail_semantics
    (B : CutPair Q) (a b t : SV)
    (hu : (blk a).val ≠ d) (hv : (blk b).val ≠ d) (huv : blk a ≠ blk b)
    (hfst : B.fst = ix a) (hsnd : B.snd = ix b)
    (ht₁ : blk t ≠ blk a) (ht₂ : blk t ≠ blk b) :
    (∀ x ∈ lemma22ExitTails Q B B.fst (ix t),
      (∃ z : SV, z.val = x ∧ blk z = blk a) ∧
      g.InitiallyReachable r x ∧
      (g.SurvivingPath (fails a b) r x ↔ ¬ g.Dominates r a.val x)) ∧
    (∀ x ∈ lemma22ExitTails Q B B.snd (ix t),
      (∃ z : SV, z.val = x ∧ blk z = blk b) ∧
      g.InitiallyReachable r x ∧
      (g.SurvivingPath (fails a b) r x ↔ ¬ g.Dominates r b.val x)) := by
  have hB := semanticCutMem progress injective spec hd B hfst hsnd
  have ht := semanticThirdAlive progress injective spec hd B hfst hsnd ht₁ ht₂
  have hA : B.Mem (ix a) := (hB (ix a)).mpr (Or.inl rfl)
  have hC : B.Mem (ix b) := (hB (ix b)).mpr (Or.inr rfl)
  constructor
  · intro x hx
    have he := mem_lemma22ExitTails.mp hx
    rw [hfst] at he
    obtain ⟨⟨z, hval, hz⟩, hr⟩ :=
      lemma22_exitTail_provenance progress injective spec hd B hA ht he
    refine ⟨⟨z, hval, hz⟩, hr, ?_⟩
    simpa only [hval] using
      (lemma22_own progress injective spec hd (blk a) (blk b) hu hv huv
        a b z rfl rfl hz)
  · intro x hx
    have he := mem_lemma22ExitTails.mp hx
    rw [hsnd] at he
    obtain ⟨⟨z, hval, hz⟩, hr⟩ :=
      lemma22_exitTail_provenance progress injective spec hd B hC ht he
    refine ⟨⟨z, hval, hz⟩, hr, ?_⟩
    simpa only [hval] using
      (lemma22_own_right progress injective spec hd (blk a) (blk b) hu hv huv
        a b z rfl rfl hz)

/-- The third-block decomposition before LCA compression. The clean quotient
branch requires no nonemptiness assumption on either tail list. -/
theorem lemma22_third_survivingPath_iff_not_all_tail_dominates
    (B : CutPair Q) (a b t : SV)
    (ha : a.val ≠ d) (hb : b.val ≠ d)
    (hu : (blk a).val ≠ d) (hv : (blk b).val ≠ d) (huv : blk a ≠ blk b)
    (hfst : B.fst = ix a) (hsnd : B.snd = ix b)
    (ht₁ : blk t ≠ blk a) (ht₂ : blk t ≠ blk b) :
    g.SurvivingPath (fails a b) r t.val ↔
      AvoidPath (Q).HasQuotientArc B.Mem (Q).root (ix t) ∨
      (¬ g.CommonDominator r (lemma22ExitTails Q B B.fst (ix t)) a.val) ∨
      (¬ g.CommonDominator r (lemma22ExitTails Q B B.snd (ix t)) b.val) := by
  let xs := lemma22ExitTails Q B B.fst (ix t)
  let ys := lemma22ExitTails Q B B.snd (ix t)
  have hB := semanticCutMem progress injective spec hd B hfst hsnd
  have core :=
    lemma22_third_survivingPath_iff_exitTailMem progress injective spec hd
      B a b t ha hb ht₁ ht₂ hB
  obtain ⟨ownL, ownR⟩ :=
    lemma22_third_endpoint_tail_semantics progress injective spec hd
      B a b t hu hv huv hfst hsnd ht₁ ht₂
  have leftIff :
      (∃ x ∈ xs, g.SurvivingPath (fails a b) r x) ↔
        ¬ g.CommonDominator r xs a.val :=
    someSurvivingTail_iff_not_commonDominator (fun x hx => (ownL x hx).2.2)
  have rightIff :
      (∃ x ∈ ys, g.SurvivingPath (fails a b) r x) ↔
        ¬ g.CommonDominator r ys b.val :=
    someSurvivingTail_iff_not_commonDominator (fun x hx => (ownR x hx).2.2)
  constructor
  · intro p
    rcases core.mp p with clean | ⟨s, x, hs, px, he⟩
    · exact Or.inl clean
    · rcases (hB s).mp hs with h | h
      · have heq : s = B.fst := h.trans hfst.symm
        rw [heq] at he
        exact Or.inr (Or.inl (leftIff.mp ⟨x, mem_lemma22ExitTails.mpr he, px⟩))
      · have heq : s = B.snd := h.trans hsnd.symm
        rw [heq] at he
        exact Or.inr (Or.inr (rightIff.mp ⟨x, mem_lemma22ExitTails.mpr he, px⟩))
  · rintro (clean | hL | hR)
    · exact core.mpr (Or.inl clean)
    · obtain ⟨x, hx, px⟩ := leftIff.mpr hL
      exact core.mpr (Or.inr
        ⟨B.fst, x, (hB B.fst).mpr (Or.inl hfst), px, mem_lemma22ExitTails.mp hx⟩)
    · obtain ⟨x, hx, px⟩ := rightIff.mpr hR
      exact core.mpr (Or.inr
        ⟨B.snd, x, (hB B.snd).mpr (Or.inr hsnd), px, mem_lemma22ExitTails.mp hx⟩)

/-- On a proper quotient loss, both tail lists are nonempty. Their exact,
unique dominator LCAs compress the two all-tail tests: the third-block
target is lost precisely when both failures dominate their respective LCAs. -/
theorem lemma22_third_properLoss_decomposition
    (B : CutPair Q) (a b t : SV)
    (ha : a.val ≠ d) (hb : b.val ≠ d)
    (hu : (blk a).val ≠ d) (hv : (blk b).val ≠ d) (huv : blk a ≠ blk b)
    (hfst : B.fst = ix a) (hsnd : B.snd = ix b)
    (ht₁ : blk t ≠ blk a) (ht₂ : blk t ≠ blk b)
    (acyclic : (Q).IsAcyclic) (flat : (Q).IsFlat)
    (proper : (Q).ProperLoss B (ix t)) :
    let xs := lemma22ExitTails Q B B.fst (ix t)
    let ys := lemma22ExitTails Q B B.snd (ix t)
    xs ≠ [] ∧ ys ≠ [] ∧
      ∃ l₁ l₂ : Fin g.vertexCount,
        (g.IsDominatorLCA r xs l₁ ∧
          ∀ m, g.IsDominatorLCA r xs m → m = l₁) ∧
        (g.IsDominatorLCA r ys l₂ ∧
          ∀ m, g.IsDominatorLCA r ys m → m = l₂) ∧
        (∀ f, (¬ g.CommonDominator r xs f) ↔ ¬ g.Dominates r f l₁) ∧
        (∀ f, (¬ g.CommonDominator r ys f) ↔ ¬ g.Dominates r f l₂) ∧
        (g.SurvivingPath (fails a b) r t.val ↔
          (¬ g.Dominates r a.val l₁) ∨ (¬ g.Dominates r b.val l₂)) ∧
        ((¬ g.SurvivingPath (fails a b) r t.val) ↔
          g.Dominates r a.val l₁ ∧ g.Dominates r b.val l₂) := by
  classical
  dsimp only
  let xs := lemma22ExitTails Q B B.fst (ix t)
  let ys := lemma22ExitTails Q B B.snd (ix t)
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ :=
    properLoss_both_exitTailMem_nonempty_of_flat_acyclic acyclic flat proper
  have hxMem : x ∈ xs := mem_lemma22ExitTails.mpr hx
  have hyMem : y ∈ ys := mem_lemma22ExitTails.mpr hy
  have hxs : xs ≠ [] := by
    intro he
    simpa only [he, List.not_mem_nil] using hxMem
  have hys : ys ≠ [] := by
    intro he
    simpa only [he, List.not_mem_nil] using hyMem
  obtain ⟨ownL, ownR⟩ :=
    lemma22_third_endpoint_tail_semantics progress injective spec hd
      B a b t hu hv huv hfst hsnd ht₁ ht₂
  have reachL : ∀ v ∈ xs, g.InitiallyReachable r v :=
    fun v hm => (ownL v hm).2.1
  have reachR : ∀ v ∈ ys, g.InitiallyReachable r v :=
    fun v hm => (ownR v hm).2.1
  obtain ⟨l₁, hl₁, uniqueL⟩ :=
    exists_unique_dominatorLCA_of_rank progress hxs reachL
  obtain ⟨l₂, hl₂, uniqueR⟩ :=
    exists_unique_dominatorLCA_of_rank progress hys reachR
  have negL (f : Fin g.vertexCount) :
      (¬ g.CommonDominator r xs f) ↔ ¬ g.Dominates r f l₁ :=
    not_commonDominator_iff_not_dominates_lca hl₁
  have negR (f : Fin g.vertexCount) :
      (¬ g.CommonDominator r ys f) ↔ ¬ g.Dominates r f l₂ :=
    not_commonDominator_iff_not_dominates_lca hl₂
  have noClean : ¬ AvoidPath (Q).HasQuotientArc B.Mem (Q).root (ix t) := by
    change ¬ (Q).SurvivingPath B.Mem (Q).root (ix t)
    first
    | exact proper.1
    | exact proper.2
    | exact proper.1.1
    | exact proper.1.2
    | exact proper.2.1
    | exact proper.2.2
    | exact proper.2.2.1
    | exact proper.2.2.2
    | grind [LabelledQuotient.ProperLoss]
  have raw :=
    lemma22_third_survivingPath_iff_not_all_tail_dominates progress injective spec hd
      B a b t ha hb hu hv huv hfst hsnd ht₁ ht₂
  have survive :
      g.SurvivingPath (fails a b) r t.val ↔
        (¬ g.Dominates r a.val l₁) ∨ (¬ g.Dominates r b.val l₂) := by
    constructor
    · intro p
      rcases raw.mp p with clean | hL | hR
      · exact False.elim (noClean clean)
      · exact Or.inl ((negL a.val).mp hL)
      · exact Or.inr ((negR b.val).mp hR)
    · rintro (hL | hR)
      · exact raw.mpr (Or.inr (Or.inl ((negL a.val).mpr hL)))
      · exact raw.mpr (Or.inr (Or.inr ((negR b.val).mpr hR)))
  refine ⟨hxs, hys, l₁, l₂, ⟨hl₁, uniqueL⟩, ⟨hl₂, uniqueR⟩,
    negL, negR, survive, ?_⟩
  constructor
  · intro lost
    exact ⟨
      Classical.byContradiction (fun h => lost (survive.mpr (Or.inl h))),
      Classical.byContradiction (fun h => lost (survive.mpr (Or.inr h)))⟩
  · rintro ⟨hL, hR⟩ p
    rcases survive.mp p with h | h
    · exact h hL
    · exact h hR

end

end PaperB.Digraph
