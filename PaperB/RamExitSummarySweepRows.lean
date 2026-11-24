module

public import PaperB.RamExitSummaryStage3
public import PaperB.RamExitSummaryEvalFold

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
open PaperB.BuiltExit (vjoin zero Test get_vjoin test_zero)
open PaperB.ExitSummary (endpointsInside_span_iff)
open PaperB.ForestIncomingRaw (supplied length_supplied)
open PaperB.ForestPreparedBuild (arcTotal_eq_arcCount)
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.WordOps (add sub ltb add_no_wrap sub_val ltb_eq_true)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.ArcParents
open PaperB.ForestHead (Vertex)
open PaperB.ForestPreparedBuild (IsTopologicalOrder)
open PaperB.RetainedProperLoss (encodeBackPair encodeBackPair_eq_iff ofOrderedReader)
open PaperB.ExitActualContract
open PaperB.ExitMap
open PaperB.ExitMap.Retention
open PaperB.ExitMap.CheckedFold
open PaperB.StoredPacking
open PaperB.ExitMap.JumpMapRoute
open PaperB.ExitMap.JumpMapRoute.StoredExit
open PaperB.ExitMap.JumpMapRoute.StoredExit.PriorBase
open PaperB.ExitPhysicalOneSlot
open PaperB.ExitPhysicalDepthColumn
open PaperB.Exit.OrderedReaderResult
open PaperB.EX24.FinalDFS (nodeCount nodeCount_eq_next nodeCount_le)
open _root_.EX24 (selectors)
open _root_.EX24.PreparedSweep (orderedVertexAt orderedConfig)

/-! ### 10. Mathematical & Contract Bridges for Stage 4 (`Step 4A` & `Step 4B`) -/

section Stage4MathBridges

open PaperB.Jumps
open PaperB.EX24.FinalDFS
open _root_.EX24.PreStep

theorem values_ext {a b : Values} (h0 : a.x0 = b.x0) (h1 : a.x1 = b.x1) : a = b := by
  cases a; cases b; cases h0; cases h1; rfl

theorem vjoin_empty_zero (a : Values) : vjoin a zero = a := by
  apply values_ext
  · change Interval.join a.x0 Interval.empty = a.x0
    cases a.x0 <;> rfl
  · change Interval.join a.x1 Interval.empty = a.x1
    cases a.x1 <;> rfl

theorem intervalJoin_empty_right (x : Interval) : Interval.join x Interval.empty = x := by
  cases x <;> rfl

private theorem intervalJoin_empty_left (x : Interval) : Interval.join Interval.empty x = x := by
  cases x <;> rfl

private theorem test_join_local (l h : Nat) (a b : Interval) :
    Test l h (Interval.join a b) ↔ Test l h a ∧ Test l h b := by
  cases a with
  | empty =>
    rw [intervalJoin_empty_left]
    simp [Test]
  | span al ah =>
    cases b with
    | empty =>
      rw [intervalJoin_empty_right]
      simp [Test]
    | span bl bh =>
      simp only [Interval.join, Test, endpointsInside_span_iff, Nat.min_def, Nat.max_def]
      split <;> split <;>
        (constructor
         · rintro ⟨hl, hh⟩; exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
         · rintro ⟨⟨hla, hha⟩, ⟨hlb, hhb⟩⟩; exact ⟨by omega, by omega⟩)

private theorem test_ext_local {a b : Interval}
    (h : ∀ l hh, Test l hh a ↔ Test l hh b) : a = b := by
  cases a with
  | empty =>
    cases b with
    | empty => rfl
    | span bl bh =>
      obtain ⟨bad, _⟩ := (endpointsInside_span_iff (bl + 1) (bh + 1) bl bh).mp
        ((h (bl + 1) (bh + 1)).mp True.intro)
      omega
  | span al ah =>
    cases b with
    | empty =>
      obtain ⟨bad, _⟩ := (endpointsInside_span_iff (al + 1) (ah + 1) al ah).mp
        ((h (al + 1) (ah + 1)).mpr True.intro)
      omega
    | span bl bh =>
      have hA : Test al (ah + 1) (.span al ah) :=
        (endpointsInside_span_iff al (ah + 1) al ah).mpr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
      have hB : Test bl (bh + 1) (.span bl bh) :=
        (endpointsInside_span_iff bl (bh + 1) bl bh).mpr ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
      obtain ⟨hl1, hh1⟩ := (endpointsInside_span_iff al (ah + 1) bl bh).mp ((h al (ah + 1)).mp hA)
      obtain ⟨hl2, hh2⟩ := (endpointsInside_span_iff bl (bh + 1) al ah).mp ((h bl (bh + 1)).mpr hB)
      have hl : al = bl := by omega
      have hh : ah = bh := by omega
      rw [hl, hh]

private theorem two_ext_local {a b : Values} (h : ∀ j : Fin 2, Two.get a j = Two.get b j) :
    a = b := by
  cases a; cases b
  have h0 : _ = _ := h 0
  have h1 : _ = _ := h 1
  simp only [Two.get, Two.get.eq_1] at h0 h1
  cases h0; cases h1; rfl

private theorem foldl_vjoin_test {α : Type} (ts : List α) (f : α → Values)
    (acc : Values) (j : Fin 2) (l h : Nat) :
    Test l h (Two.get (ts.foldl (fun c t => vjoin c (f t)) acc) j) ↔
      Test l h (Two.get acc j) ∧ ∀ t ∈ ts, Test l h (Two.get (f t) j) := by
  induction ts generalizing acc with
  | nil => simp
  | cons t ts ih =>
    rw [List.foldl_cons, ih, get_vjoin, test_join_local]
    constructor
    · rintro ⟨⟨ha, ht⟩, hts⟩
      refine ⟨ha, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ht
      · exact hts b hb
    · rintro ⟨ha, hall⟩
      exact ⟨⟨ha, hall t (List.mem_cons.mpr (Or.inl rfl))⟩,
        fun b hb => hall b (List.mem_cons.mpr (Or.inr hb))⟩

theorem foldl_vjoin_eq_of_image {α β : Type} (xs : List α) (zs : List β)
    (f : α → Values) (g : β → Values)
    (hIm : (∀ x ∈ xs, ∃ z ∈ zs, f x = g z) ∧ (∀ z ∈ zs, ∃ x ∈ xs, g z = f x)) :
    xs.foldl (fun acc x => vjoin acc (f x)) zero =
      zs.foldl (fun acc z => vjoin acc (g z)) zero := by
  apply two_ext_local; intro j
  apply test_ext_local; intro l h
  rw [foldl_vjoin_test, foldl_vjoin_test]
  simp only [test_zero, true_and]
  constructor
  · intro hx z hz
    obtain ⟨x, hxMem, hEq⟩ := hIm.2 z hz
    rw [hEq]; exact hx x hxMem
  · intro hz x hx
    obtain ⟨z, hzMem, hEq⟩ := hIm.1 x hx
    rw [hEq]; exact hz z hzMem

theorem inArcsPrefix_mem_iff_row (H : LabelledQuotient) (y : Vertex H) (e : Nat) :
    e ∈ inArcsPrefix H H.arcCount y.val ↔
      ∃ he : e < H.arcCount, rawHead H ⟨e, he⟩ = y := by
  rw [mem_inArcsPrefix_iff]
  constructor
  · rintro ⟨he, _, hEq⟩
    exact ⟨he, Fin.ext hEq⟩
  · rintro ⟨he, hEq⟩
    exact ⟨he, he, congrArg Fin.val hEq⟩

private theorem rawLength (H : LabelledQuotient) : (supplied H).reverse.length = H.arcCount :=
  List.length_reverse.trans ((length_supplied H).trans (arcTotal_eq_arcCount H))

theorem incomingArc_head {H : LabelledQuotient} {y : Vertex H} {e : Nat}
    (he : e ∈ inArcsPrefix H H.arcCount y.val) (hBound : e < H.arcCount) :
    rawHead H ⟨e, hBound⟩ = y := by
  obtain ⟨_, hHead⟩ := (inArcsPrefix_mem_iff_row H y e).mp he
  exact hHead

theorem rawOccurrence_in_row_iff (H : LabelledQuotient) (y : Vertex H)
    (u : Vertex H) (a : QuotientArc H.origVertexCount H.vertexCount) :
    (u, a) ∈ ForestIncomingRaw.row H (ForestIncomingRaw.prepare H) y ↔
      ∃ e ∈ inArcsPrefix H H.arcCount y.val,
        ∃ he : e < H.arcCount, rawOccurrence H ⟨e, he⟩ = (u, a) := by
  rw [ForestIncomingRaw.mem_row]
  constructor
  · rintro ⟨haOut, haHead⟩
    have hMemSup : (u, a) ∈ supplied H := (ForestIncomingRaw.mem_supplied H u a).mpr haOut
    have hMemRev : (u, a) ∈ (supplied H).reverse := List.mem_reverse.mpr hMemSup
    obtain ⟨e, heLen, heGet⟩ := List.mem_iff_getElem.mp hMemRev
    have he : e < H.arcCount := by rw [← rawLength H]; exact heLen
    have hOcc : rawOccurrence H ⟨e, he⟩ = (u, a) := heGet
    have hHd : rawHead H ⟨e, he⟩ = y := by
      unfold rawHead; rw [hOcc]; exact haHead
    exact ⟨e, (inArcsPrefix_mem_iff_row H y e).mpr ⟨he, hHd⟩, he, hOcc⟩
  · rintro ⟨e, heIn, he, hOcc⟩
    have hHd : rawHead H ⟨e, he⟩ = y := incomingArc_head heIn he
    have hRev : rawOccurrence H ⟨e, he⟩ ∈ (supplied H).reverse :=
      List.getElem_mem (by rw [rawLength H]; exact he)
    rw [hOcc] at hRev
    have hSup : (u, a) ∈ supplied H := List.mem_reverse.mp hRev
    refine ⟨(ForestIncomingRaw.mem_supplied H u a).mp hSup, ?_⟩
    unfold rawHead at hHd
    rw [hOcc] at hHd
    exact hHd

end Stage4MathBridges

end PaperB.RamProgram.ExitSummaryBuild
