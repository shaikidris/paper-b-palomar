module

public import PaperB.ForestTopologicalTotal
public import PaperB.StaticOracleTree

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PaperB
open _root_.EX16 _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.ForestHead PaperB.LabelledQuotient PaperB.PairLookup

namespace EX24.FinalDFS

open EX15.WholeScan.PackedInput

universe u

variable {H : LabelledQuotient} {c : Config H}
variable {rank : Vertex H → Nat} {out : State H}

/-- The DFS domain is the occupied prefix, including artificial slot zero.
    It is not the capacity of the jump region or of the reverse dictionary. -/
abbrev nodeCount (c : Config H) (out : State H) : Nat :=
  occupied c.region out.tables.mem

private theorem layoutExists (h : OutputOK c rank out) :
    ∃ F : JumpForest, JumpWordLayout c.region F out.tables.mem := by
  obtain ⟨F, _, G, _, _⟩ := h.2.2
  exact ⟨F, G.layout⟩

theorem nodeCount_eq_next (h : OutputOK c rank out) :
    nodeCount c out = out.tables.next := by
  obtain ⟨F, _, G, _, _⟩ := h.2.2
  exact (show nodeCount c out = F.size from G.layout.size_word).trans G.size_eq

theorem nodeCount_le (h : OutputOK c rank out) :
    nodeCount c out ≤ H.vertexCount + 1 :=
  (nodeCount_eq_next h).symm ▸ h.2.1

def packedInput (h : OutputOK c rank out) :
    PackedStaticLayout.Input (nodeCount c out) :=
  EX15.WholeScan.PackedInput.ofWords c.region out.tables.mem (layoutExists h)

theorem packedInput_ok (h : OutputOK c rank out) :
    PackedStaticLayout.InputOK (packedInput h) :=
  ofWords_ok (layoutExists h)

theorem packedInput_parent (h : OutputOK c rank out) {F : JumpForest}
    (G : Grounded c F out.tables) (a : Fin (nodeCount c out)) :
    ((packedInput h).parent.read a).val = F.parentOf a.val :=
  ofWords_parent G.layout (layoutExists h) a

theorem packedInput_depth (h : OutputOK c rank out) {F : JumpForest}
    (G : Grounded c F out.tables) (a : Fin (nodeCount c out)) :
    (packedInput h).depth.read a = F.depthOf a.val :=
  ofWords_depth G.layout (layoutExists h) a

@[simp] theorem packedInput_root (h : OutputOK c rank out) :
    (packedInput h).root.val = 0 :=
  ofWords_root (layoutExists h)

private theorem packedInput_root_fixed (h : OutputOK c rank out) :
    (packedInput h).parent.read (packedInput h).root = (packedInput h).root := by
  have hok := packedInput_ok h
  first
  | exact hok.root_parent
  | exact hok.parent_root
  | cases hok <;> assumption
  | obtain ⟨F, _, G, _, _⟩ := h.2.2
    apply Fin.ext
    rw [packedInput_parent h G, packedInput_root h]
    have hv := G.layout.valid
    first
    | rfl
    | exact hv.parent_root
    | exact hv.root_parent
    | exact?
    | obtain ⟨J, inv⟩ := hv.exists_forestInvariant
      first
      | exact inv.parent_root
      | exact inv.root_parent
      | exact?

/-- This is the label in the final state's label array, not the label
    of a vertex in a separately built canonical forest. -/
theorem finalLabel_lt (h : OutputOK c rank out) (v : Vertex H) :
    (selectors c out).label v < nodeCount c out := by
  obtain ⟨F, _, G, _, ⟨E⟩⟩ := h.2.2
  rw [show nodeCount c out = F.size from G.layout.size_word]
  exact E.label_lt v True.intro

theorem finalLabel_lt_grounded (h : OutputOK c rank out) {F : JumpForest}
    (G : Grounded c F out.tables) (v : Vertex H) :
    (selectors c out).label v < F.size := by
  rw [← (show nodeCount c out = F.size from G.layout.size_word)]
  exact finalLabel_lt h v

private theorem iter_iff_reader (h : OutputOK c rank out)
    (a b : Fin (nodeCount c out)) :
    EX15.WholeScan.PackedInput.SemanticAncestor (packedInput h) a b ↔
      StaticTreeReader.SemanticAncestor (packedInput h) a b := by
  have hr := packedInput_root_fixed h
  first
  | exact parentIter_iff_readerAncestor (packedInput h) hr a b
  | exact StaticTreeReader.parentIter_iff_readerAncestor (packedInput h) hr a b
  | exact?

structure Index (c : Config H) (rank : Vertex H → Nat) (out : State H) where
  ok : OutputOK c rank out
  reader : StaticTreeReader.Reader (packedInput ok)

/-- Run once per final quotient. `ofWords` packs the occupied records once;
    `StaticTreeReader.build` builds the static layout from that input. There
    is no additional traversal here. The construction is linear in the
    occupied count, which is at most `H.vertexCount + 1`. -/
def build (h : OutputOK c rank out) : Index c rank out := by
  let x := packedInput h
  have hx : PackedStaticLayout.InputOK x := packedInput_ok h
  refine ⟨h, ?_⟩
  first
  | exact StaticTreeReader.build x hx
  | exact StaticTreeReader.build (x := x) hx
  | exact StaticTreeReader.build hx

/-- A dictionary lookup supplies a candidate slot, not a membership answer.
    Check both the empty-slot sentinel and the full reverse key. -/
def checkedNode? (c : Config H) (out : State H) [DecidableEq (CutPair H)]
    (q : CutPair H) : Option Nat :=
  match (PairLookup.lookup c.dict (c.code q)).1 with
  | none => none
  | some i =>
      let a := out.tables.slotAt i
      if a ≠ 0 ∧ out.tables.back[a]? = some (some q) then some a else none

theorem checkedNode_iff_back [DecidableEq (CutPair H)]
    (h : OutputOK c rank out) {q : CutPair H} {a : Nat} :
    checkedNode? c out q = some a ↔ out.tables.back[a]? = some (some q) := by
  constructor
  · intro hit
    cases hd : (PairLookup.lookup c.dict (c.code q)).1 with
    | none => simp [checkedNode?, hd] at hit
    | some i =>
        by_cases hs : out.tables.slotAt i ≠ 0 ∧
            out.tables.back[out.tables.slotAt i]? = some (some q)
        · have ha : out.tables.slotAt i = a := by
            simpa [checkedNode?, hd, hs] using hit
          exact ha ▸ hs.2
        · simp [checkedNode?, hd, hs] at hit
  · intro hb
    obtain ⟨F, _, G, _, _⟩ := h.2.2
    obtain ⟨_, hn, i, hd, hs⟩ := G.backward a q hb
    simp [checkedNode?, hd, hs, hn, hb]

theorem checkedNode_occupied [DecidableEq (CutPair H)]
    (h : OutputOK c rank out) {q : CutPair H} {a : Nat}
    (hit : checkedNode? c out q = some a) :
    a < nodeCount c out ∧ a ≠ 0 := by
  have hb := (checkedNode_iff_back h).mp hit
  obtain ⟨F, _, G, _, _⟩ := h.2.2
  obtain ⟨ha, hn, _⟩ := G.backward a q hb
  exact ⟨(nodeCount_eq_next h).symm ▸ ha, hn⟩

namespace Index

def label (I : Index c rank out) (v : Vertex H) : Fin (nodeCount c out) :=
  ⟨(selectors c out).label v, finalLabel_lt I.ok v⟩

@[simp] theorem label_val (I : Index c rank out) (v : Vertex H) :
    (I.label v).val = (selectors c out).label v := rfl

/-- One final-label read and three stored DFS-field reads: entry of the
    label, entry of the candidate, and exclusive stop of the candidate.
    The queried entry is shared by the two comparisons. -/
def known (I : Index c rank out) (a : Fin (nodeCount c out))
    (v : Vertex H) : Bool :=
  I.reader.isAncestor a (I.label v)

private theorem reader_iff_jump (I : Index c rank out) {F : JumpForest}
    (G : Grounded c F out.tables) (a b : Fin (nodeCount c out)) :
    StaticTreeReader.SemanticAncestor (packedInput I.ok) a b ↔
      IsAncestor F a.val b.val :=
  (iter_iff_reader I.ok a b).symm.trans
    (semanticAncestor_iff_jump (packedInput_parent I.ok G) a b)

/-- Inclusive ancestry (the witness may be zero), with an exclusive stop. -/
theorem iterParent_iff_interval (I : Index c rank out) {F : JumpForest}
    (G : Grounded c F out.tables) (a : Fin (nodeCount c out)) (v : Vertex H) :
    (∃ k : Nat, F.iterParent k ((selectors c out).label v) = a.val) ↔
      I.reader.entry a ≤ I.reader.entry (I.label v) ∧
        I.reader.entry (I.label v) < I.reader.stop a :=
  (I.reader_iff_jump G a (I.label v)).symm.trans
    (I.reader.ancestor_iff_interval a (I.label v))

theorem known_exact (I : Index c rank out) {F : JumpForest}
    (G : Grounded c F out.tables) (a : Fin (nodeCount c out)) (v : Vertex H) :
    I.known a v = true ↔ IsAncestor F a.val ((selectors c out).label v) :=
  (I.reader.isAncestor_exact a (I.label v)).trans
    (I.reader_iff_jump G a (I.label v))

theorem root_has_no_key (I : Index c rank out) :
    out.tables.back[(packedInput I.ok).root.val]? = some none := by
  rw [packedInput_root]
  obtain ⟨F, _, G, _, _⟩ := I.ok.2.2
  exact G.zero

/-- A vertex still labelled zero is at the artificial root. Its only
    inclusive ancestor is zero, which is never returned as a key hit. -/
theorem known_on_zero_label (I : Index c rank out)
    (a : Fin (nodeCount c out)) (v : Vertex H)
    (hv : (selectors c out).label v = 0) :
    I.known a v = true ↔ a.val = 0 := by
  let x := packedInput I.ok
  have hl : I.label v = x.root := Fin.ext (hv.trans (packedInput_root I.ok).symm)
  have hr (k : Nat) : parentIter x k x.root = x.root := by
    induction k with
    | zero => rfl
    | succ k ih =>
        change parentIter x k (x.parent.read x.root) = x.root
        rw [show x.parent.read x.root = x.root from packedInput_root_fixed I.ok]
        exact ih
  change I.reader.isAncestor a (I.label v) = true ↔ a.val = 0
  rw [I.reader.isAncestor_exact, ← iter_iff_reader I.ok a (I.label v)]
  change (∃ k : Nat, parentIter x k (I.label v) = a) ↔ a.val = 0
  rw [hl]
  constructor
  · rintro ⟨k, hk⟩
    have he : a = x.root := hk.symm.trans (hr k)
    exact (congrArg Fin.val he).trans (packedInput_root I.ok)
  · intro ha
    exact ⟨0, Fin.ext ((packedInput_root I.ok).trans ha.symm)⟩

private def atHit (I : Index c rank out) (v : Vertex H) :
    (hit : Option Nat) →
    (∀ a, hit = some a → a < nodeCount c out) → Bool
  | none, _ => false
  | some a, bound => I.known ⟨a, bound a rfl⟩ v

/-- Only the checked dictionary lookup precedes the constant-time test.
    The occupied bound is a proof, not another scan or runtime lookup. -/
def contains (I : Index c rank out) [DecidableEq (CutPair H)]
    (q : CutPair H) (v : Vertex H) : Bool :=
  I.atHit v (checkedNode? c out q)
    (fun _ hit => (checkedNode_occupied I.ok hit).1)

private theorem atHit_some (I : Index c rank out) (v : Vertex H)
    {hit : Option Nat} {a : Nat}
    (bound : ∀ b, hit = some b → b < nodeCount c out)
    (hh : hit = some a) :
    I.atHit v hit bound = I.known ⟨a, bound a hh⟩ v := by
  subst hit
  rfl

private theorem atHit_none (I : Index c rank out) (v : Vertex H)
    {hit : Option Nat}
    (bound : ∀ b, hit = some b → b < nodeCount c out)
    (hh : hit = none) :
    I.atHit v hit bound = false := by
  subst hit
  rfl

theorem contains_hit (I : Index c rank out) [DecidableEq (CutPair H)]
    {q : CutPair H} {a : Nat} (hh : checkedNode? c out q = some a)
    (v : Vertex H) :
    I.contains q v = I.known ⟨a, (checkedNode_occupied I.ok hh).1⟩ v :=
  I.atHit_some v _ hh

theorem contains_miss (I : Index c rank out) [DecidableEq (CutPair H)]
    {q : CutPair H} (hh : checkedNode? c out q = none) (v : Vertex H) :
    I.contains q v = false :=
  I.atHit_none v _ hh

theorem contains_exact (I : Index c rank out) [DecidableEq (CutPair H)]
    {F : JumpForest} (G : Grounded c F out.tables) (q : CutPair H)
    (v : Vertex H) :
    I.contains q v = true ↔
      ∃ a : Nat, out.tables.back[a]? = some (some q) ∧
        IsAncestor F a ((selectors c out).label v) := by
  constructor
  · intro yes
    cases hh : checkedNode? c out q with
    | none => simp [I.contains_miss hh v] at yes
    | some a =>
        rw [I.contains_hit hh v] at yes
        exact ⟨a, (checkedNode_iff_back I.ok).mp hh,
          (I.known_exact G ⟨a, (checkedNode_occupied I.ok hh).1⟩ v).mp yes⟩
  · rintro ⟨a, hb, ha⟩
    have hh := (checkedNode_iff_back I.ok).mpr hb
    rw [I.contains_hit hh v]
    exact (I.known_exact G ⟨a, (checkedNode_occupied I.ok hh).1⟩ v).mpr ha

end Index
end EX24.FinalDFS
end PaperB
