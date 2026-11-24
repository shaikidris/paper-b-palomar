module

public import PaperB.RamExitSummaryKahnPop

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 2000000

/-!
The outer queue induction for the word-RAM Kahn traversal.
-/

namespace PaperB.RamProgram.ExitSummaryBuild

open PaperB
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


section Stage2CsrKahn

section KahnLoopPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private theorem foldl_add_shift {α : Type} (f : α → Nat) (xs : List α) (a : Nat) :
    xs.foldl (fun acc x => acc + f x) a = a + (xs.map f).sum := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih (a + f x)]
    omega

private theorem sum_map_erase {f : Nat → Nat} (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    (xs.map f).sum = ((xs.erase a).map f).sum + f a := by
  induction xs with
  | nil => cases ha
  | cons x xs ih =>
    by_cases hx : x = a
    · subst hx
      simp [List.erase_cons_head, Nat.add_comm]
    · have haTail : a ∈ xs := (List.mem_cons.mp ha).resolve_left (Ne.symm hx)
      have hErase : (x :: xs).erase a = x :: xs.erase a := by
        simp [beq_false_of_ne hx]
      rw [hErase, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, ih haTail]
      omega

private theorem range_map_degOut_sum (H : LabelledQuotient) (k : Nat) :
    ((List.range k).map (degOut H)).sum = prefixOut H k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, ih]
    rfl

private theorem list_nodup_sum_degOut_le (H : LabelledQuotient) (xs : List Nat)
    (hNd : xs.Nodup) (hB : ∀ x ∈ xs, x < H.vertexCount) :
    xs.foldl (fun acc x => acc + degOut H x) 0 ≤ H.arcCount := by
  rw [foldl_add_shift, Nat.zero_add, ← prefixOut_vertexCount H, ← range_map_degOut_sum H H.vertexCount]
  suffices h : ∀ n (ys : List Nat), ys.Nodup → (∀ y ∈ ys, y < n) →
      (ys.map (degOut H)).sum ≤ ((List.range n).map (degOut H)).sum from
    h H.vertexCount xs hNd hB
  intro n
  induction n with
  | zero =>
    intro ys _ hBy
    cases ys with
    | nil => simp
    | cons y _ => exact absurd (hBy y (by simp)) (Nat.not_lt_zero _)
  | succ n ih =>
    intro ys hNdY hBy
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    by_cases hnMem : n ∈ ys
    · have hErNd : (ys.erase n).Nodup := hNdY.erase n
      have hErNotMem : n ∉ ys.erase n := List.Nodup.not_mem_erase hNdY
      have hErB : ∀ y ∈ ys.erase n, y < n := fun y hy => by
        have hyOrig := hBy y (List.mem_of_mem_erase hy)
        have hne : y ≠ n := fun he => hErNotMem (he ▸ hy)
        omega
      rw [sum_map_erase ys n hnMem]
      exact Nat.add_le_add_right (ih (ys.erase n) hErNd hErB) _
    · have hB' : ∀ y ∈ ys, y < n := fun y hy => by
        have hyLt := hBy y hy
        have hne : y ≠ n := fun he => hnMem (he ▸ hy)
        omega
      exact Nat.le_trans (ih ys hNdY hB') (Nat.le_add_right _ _)

private theorem kahn_queueTopo_extend {H : LabelledQuotient} {q0 q1 : List Nat} {k : Nat}
    (hkLtQ : k < q0.length) (hkLtQ1 : k < q1.length)
    (hBound : ∀ x ∈ q0, x < H.vertexCount)
    (hBound1 : ∀ x ∈ q1, x < H.vertexCount)
    (hTakeQ1Opt : ∀ i, i < k + 1 → q1[i]? = q0[i]?)
    (hZeroU : remInCount H (q0.take k) [] (q0[k]'hkLtQ) = 0)
    (hTopo : ∀ (i : Nat) (hi : i < k) (x : Vertex H),
      H.HasQuotientArc x ⟨q0[i]'(Nat.lt_trans hi hkLtQ), hBound _ (List.getElem_mem _)⟩ →
      ∃ j < i, q0[j]? = some x.val) :
    ∀ (i : Nat) (hi : i < k + 1) (x : Vertex H),
      H.HasQuotientArc x ⟨q1[i]'(Nat.lt_of_lt_of_le hi hkLtQ1),
        hBound1 _ (List.getElem_mem _)⟩ →
      ∃ j < i, q1[j]? = some x.val := by
  let u := q0[k]'hkLtQ
  have huLt : u < H.vertexCount := hBound _ (List.getElem_mem hkLtQ)
  have hkLeQ := Nat.le_of_lt hkLtQ
  have hTakeQ1Elem : ∀ i (hi : i < k + 1) (hq1 : i < q1.length) (hq0 : i < q0.length),
      q1[i]'hq1 = q0[i]'hq0 := fun i hi hq1 hq0 =>
    list_getElem_eq_of_getElem?_eq hq1 hq0 (hTakeQ1Opt i hi)
  intro i hi x hArc
  by_cases hik : i < k
  · have hiQ0 : q1[i]'(Nat.lt_of_lt_of_le hi hkLtQ1) =
        q0[i]'(Nat.lt_of_lt_of_le hik hkLeQ) :=
      hTakeQ1Elem i (Nat.lt_succ_of_lt hik) _ _
    have hArc0 : H.HasQuotientArc x ⟨q0[i]'(Nat.lt_of_lt_of_le hik hkLeQ), hBound _ (List.getElem_mem _)⟩ := by
      have hV : (⟨q1[i]'(Nat.lt_of_lt_of_le hi hkLtQ1), hBound1 _ (List.getElem_mem _)⟩ : Vertex H) =
          ⟨q0[i]'(Nat.lt_of_lt_of_le hik hkLeQ), hBound _ (List.getElem_mem _)⟩ := Fin.ext hiQ0
      exact hV ▸ hArc
    obtain ⟨j, hj, hjQ0⟩ := hTopo i hik x hArc0
    have hjLt : j < k + 1 := Nat.lt_succ_of_lt (Nat.lt_trans hj hik)
    exact ⟨j, hj, (hTakeQ1Opt j hjLt).trans hjQ0⟩
  · have hikEq : i = k := by omega
    subst i
    have hiQ0 : q1[k]'hkLtQ1 = u :=
      hTakeQ1Elem k (Nat.lt_succ_self _) hkLtQ1 hkLtQ
    have hArcU : H.HasQuotientArc x ⟨u, huLt⟩ := by
      have hV : (⟨q1[k]'hkLtQ1, hBound1 _ (List.getElem_mem _)⟩ : Vertex H) = ⟨u, huLt⟩ := Fin.ext hiQ0
      exact hV ▸ hArc
    have hMemPop : x.val ∈ q0.take k := by
      apply Classical.byContradiction
      intro hNotPop
      obtain ⟨e, heHead, heSrc⟩ := (rawOccurrence_membership H x ⟨u, huLt⟩).mpr hArcU
      have heIn : e.val ∈ inArcsPrefix H H.arcCount u :=
        (mem_inArcsPrefix_iff H H.arcCount u e.val).mpr ⟨e.isLt, e.isLt, congrArg Fin.val heSrc⟩
      have hRemPos : 0 < remInCount H (q0.take k) [] u := by
        apply List.countP_pos_iff.mpr
        refine ⟨e.val, heIn, ?_⟩
        rw [dite_eq_left e.isLt]
        have hEqX : (rawOccurrence H ⟨e.val, e.isLt⟩).1.val = x.val := congrArg Fin.val heHead
        simp [hEqX, hNotPop]
      exact (Nat.ne_of_gt hRemPos) hZeroU
    obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hMemPop
    simp only [List.length_take] at hj
    have hjLt : j < k := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    rw [List.getElem_take] at hjEq
    have hjQ0 : q0[j]? = some x.val :=
      (List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hjLt hkLeQ)).trans (congrArg some hjEq)
    exact ⟨j, hjLt, (hTakeQ1Opt j (Nat.lt_succ_of_lt hjLt)).trans hjQ0⟩

private theorem topoRankBeforeMeta (n m N : Nat) :
    topoRankArrBase n N + n ≤ metaArrBase n m N := by
  rw [metaArrBase_eq]
  unfold topoRankArrBase orderArrBase
  omega

set_option maxHeartbeats 3000000 in
theorem kahnLoopOuter_spec {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap)
    (hWorkFit : workCap ≤ 2 ^ bits)
    (hInputFit : inputCap ≤ 2 ^ bits)
    (hPlOuter : Placed code 20 (kahnLoopOuterInstrs (bits := bits) h100))
    (hPlInner : Placed code 35 (kahnLoopInnerInstrs (bits := bits)))
    (hSz : 51 < code.size) :
    ∀ (rem : Nat) (q0 : List Nat) (k : Nat) (st : State DomL)
      (hkLeQ : k ≤ q0.length) (_hqLenLe : q0.length ≤ H.vertexCount)
      (_hqNd : q0.Nodup) (hBound : ∀ x ∈ q0, x < H.vertexCount),
      k + rem = H.vertexCount →
      (∀ v, v < H.vertexCount → (v ∈ q0 ↔ remInCount H (q0.take k) [] v = 0)) →
      (∀ (i : Nat) (hi : i < k) (x : Vertex H),
        H.HasQuotientArc x ⟨q0[i]'(Nat.lt_of_lt_of_le hi hkLeQ), hBound _ (List.getElem_mem _)⟩ →
        ∃ j < i, q0[j]? = some x.val) →
      st.pc = 20 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg2).val = k →
      (reg st reg3).val = q0.length →
      (reg st reg4).val = orderArrBase H.vertexCount r.out.tables.next →
      (reg st reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next →
      (reg st reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount →
      (reg st reg8).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 →
      (reg st reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 →
      (0 < H.arcCount → (reg st reg10).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount) →
      (st.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxTopoRankBase]?).map Fin.val =
        some (topoRankArrBase H.vertexCount r.out.tables.next) →
      (∀ i < k, (st.data[orderArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = q0[i]?) →
      (∀ i (hi : i < k),
        (st.data[topoRankArrBase H.vertexCount r.out.tables.next +
            (q0[i]'(Nat.lt_of_lt_of_le hi hkLeQ))]?).map Fin.val = some i) →
      (∀ v, v < H.vertexCount →
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
          some (remInCount H (q0.take k) [] v)) →
      (∀ i ≤ H.vertexCount,
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
          some (prefixOut H i)) →
      (∀ i (hi : i < q0.length),
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i]?).map Fin.val =
          some (q0[i]'hi)) →
      (∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
        (st.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
            (prefixOut H u + j.val)]?).map Fin.val =
          some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) →
      ∃ steps : Nat, ∃ q1 : List Nat, ∃ t : State DomL,
        steps ≤ 16 * rem +
          16 * (H.arcCount - (q0.take k).foldl (fun acc x => acc + degOut H x) 0) + 1 ∧
        Steps code input steps st t ∧
        t.pc = 51 ∧
        q1.length ≤ H.vertexCount ∧
        q1.Nodup ∧
        (∀ x ∈ q1, x < H.vertexCount) ∧
        (∀ v, v < H.vertexCount → (v ∈ q1 ↔ remInCount H q1 [] v = 0)) ∧
        (∀ (hB : ∀ x ∈ q1, x < H.vertexCount) (i : Nat) (hi : i < q1.length) (x : Vertex H),
          H.HasQuotientArc x ⟨q1[i]'hi, hB _ (List.getElem_mem hi)⟩ → ∃ j < i, q1[j]? = some x.val) ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (reg t rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
        (∀ i (hi : i < q1.length),
          (t.data[orderArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (q1[i]'hi)) ∧
        (∀ i (hi : i < q1.length),
          (t.data[topoRankArrBase H.vertexCount r.out.tables.next + q1[i]'hi]?).map Fin.val = some i) ∧
        (∀ a, (a < orderArrBase H.vertexCount r.out.tables.next ∨
            (topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ a ∧
              a < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
            (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ≤ a ∧
              a < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1) ∨
            tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤ a) →
          t.data[a]? = st.data[a]?) := by
  intro rem
  induction rem with
  | zero =>
    intro q0 k st hkLeQ hqLenLe hqNd hBound hSum hZeroIff hTopo hpc
      h0 h1 hMeta h2 h3 h4 h6 h7 h8 h9 h10 hMetaTR hOrd hTR hIndeg hOutPref hQMem hOutArc
    have hkEqQ : k = q0.length := by omega
    obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPlOuter 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg2).val < (reg st reg3).val := by rw [h2, h3, hkEqQ]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpct
    have hrtF := reg_of_regs_eq hrt
    have hTakeEq : q0.take k = q0 := by rw [hkEqQ]; exact List.take_length
    rw [hTakeEq] at hZeroIff
    refine ⟨1, q0, t, by omega, steps_1_of_step hs, hpct, hqLenLe, hqNd, hBound, hZeroIff,
      fun _ i hi x harc => hTopo i (hkEqQ ▸ hi) x harc,
      by rw [hrtF, h0], by rw [hrtF, h1], by rw [hrtF, hMeta],
      fun i hi => by rw [hdt, hOrd i (hkEqQ ▸ hi), List.getElem?_eq_getElem hi],
      fun i hi => by rw [hdt]; exact hTR i (hkEqQ ▸ hi),
      fun _ _ => by rw [hdt]⟩
  | succ rem ih =>
    intro q0 k st hkLeQ hqLenLe hqNd hBound hSum hZeroIff hTopo hpc
      h0 h1 hMeta h2 h3 h4 h6 h7 h8 h9 h10 hMetaTR hOrd hTR hIndeg hOutPref hQMem hOutArc
    by_cases hkLtQ : k < q0.length
    · have hB1 : orderArrBase H.vertexCount r.out.tables.next + H.vertexCount =
          topoRankArrBase H.vertexCount r.out.tables.next := rfl
      have hB2 : topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount =
          trigHeadArrBase H.vertexCount r.out.tables.next := rfl
      have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
      have hOrdBound : orderArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
        unfold tempArrBase metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase
          trigHeadArrBase topoRankArrBase
        omega
      have hTRBound : topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
          tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
        unfold tempArrBase metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase trigHeadArrBase
        omega
      let u := q0[k]'hkLtQ
      have huLt : u < H.vertexCount := hBound u (List.getElem_mem hkLtQ)
      have huNotPopped : u ∉ q0.take k := by
        intro huIn
        obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp huIn
        simp only [List.length_take] at hj
        have hjLtK : j < k := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
        rw [List.getElem_take] at hjEq
        have hInj := nodup_getElem_inj hqNd (Nat.lt_trans hjLtK hkLtQ) hkLtQ hjEq
        omega
      obtain ⟨s13, hStep15, hpc13, h2_13, h11_13, h12_13, hPres13, hOrdWrite, hRankWrite, hS13At⟩ :=
        kahn_pop_prefix H r.out.tables.next h100 hTempFit hPlOuter hSz
          st k q0.length u hkLtQ hqLenLe huLt hpc h1 hMeta h2 h3 h4 h7 h9 hMetaTR
          (hQMem k hkLtQ) hOutPref
      have hS13Temp : ∀ a, tempArrBase H.vertexCount H.arcCount r.out.tables.next ≤ a →
          s13.data[a]? = st.data[a]? := fun a ha =>
        hS13At a
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le
            (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hkLtQ hqLenLe) _) (Nat.le_trans hOrdBound ha)))
          (Nat.ne_of_lt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left huLt _) (Nat.le_trans hTRBound ha)))
      have hQHeadBase : 0 < H.arcCount →
          4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount + H.arcCount ≤ inputCap := fun _ => by
        have := hIn.cap_ge; omega
      have hTakeLen : (q0.take k).length = k := List.length_take_of_le hkLeQ
      obtain ⟨kIn, q1, sMid, hkIn, hStepsIn, hpcMid, hPopLe1, hLen1, hNd1, hBound1, _, _, hTakeQ1,
          hZero1, hm0, hm1, hmM, hm2, hm3, hm4, hm6, hm7, hm8, hm9, hm10, hmIndeg, hmQMem, hmFr⟩ :=
        kahnLoopInner_spec hIn hTempFit hWorkFit hPlInner hSz (q0.take k) u huNotPopped hInputFit hQHeadBase
          (degOut H u) 0 q0 s13 (Nat.zero_add _) (by rw [hTakeLen]; exact hkLtQ) hqLenLe hqNd hBound
          (fun x hx => List.mem_of_mem_take hx) (List.getElem_mem hkLtQ)
          (fun v hv => by simpa only [List.take_zero] using hZeroIff v hv)
          hpc13
          (by rw [hPres13 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
          (by rw [hPres13 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
          (by rw [hPres13 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hMeta])
          (by rw [h2_13, hTakeLen])
          (by rw [hPres13 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3])
          (by rw [hPres13 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4])
          (by rw [hPres13 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6])
          (by rw [hPres13 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7])
          (by rw [hPres13 reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h8])
          (by rw [hPres13 reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h9])
          (fun hm => by rw [hPres13 reg10 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h10 hm])
          (by rw [h11_13, Nat.add_zero])
          h12_13
          (fun v hv => by
            rw [hS13Temp _ (Nat.le_add_right _ _), List.take_zero]
            exact hIndeg v hv)
          (fun i hi => by
            rw [hS13Temp _ (by omega)]
            exact hQMem i hi)
          (fun j hj => by
            rw [hS13Temp _ (by omega)]
            exact hOutArc u huLt ⟨j, hj⟩)
      have hkLtQ1 : k < q1.length := by rw [hTakeLen] at hPopLe1; exact hPopLe1
      have hTakeQ1Opt : ∀ i, i < k + 1 → q1[i]? = q0[i]? := fun i hi =>
        hTakeQ1 i (by rw [hTakeLen]; exact hi)
      have hTakeQ1Elem : ∀ i (hi : i < k + 1) (hq1 : i < q1.length) (hq0 : i < q0.length),
          q1[i]'hq1 = q0[i]'hq0 := fun i hi hq1 hq0 =>
        list_getElem_eq_of_getElem?_eq hq1 hq0 (hTakeQ1Opt i hi)
      have hTakeNext : q1.take (k + 1) = q0.take k ++ [u] := by
        rw [List.take_succ_eq_append_getElem hkLtQ1,
          hTakeQ1Elem k (Nat.lt_succ_self _) hkLtQ1 hkLtQ]
        apply congrArg (fun xs => xs ++ [u])
        refine List.ext_getElem (by rw [List.length_take_of_le (Nat.le_of_lt hkLtQ1),
          List.length_take_of_le hkLeQ]) ?_
        intro i hi1 hi2
        rw [List.getElem_take, List.getElem_take]
        exact hTakeQ1Elem i (by simp only [List.length_take] at hi1; omega) _ _
      have hTopoNext := kahn_queueTopo_extend hkLtQ hkLtQ1 hBound hBound1 hTakeQ1Opt
        ((hZeroIff u huLt).mp (List.getElem_mem hkLtQ)) hTopo
      have hMidOrd : ∀ i < k + 1, (sMid.data[orderArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = q1[i]? := by
        intro i hi
        have hiN : i < H.vertexCount := Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi hkLtQ1) hLen1
        have hFrameOrd : orderArrBase H.vertexCount r.out.tables.next + i < tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
          exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hiN _) hOrdBound
        rw [hmFr _ (Or.inl hFrameOrd)]
        by_cases hik : i = k
        · subst i
          rw [hOrdWrite, hTakeQ1Opt k (Nat.lt_succ_self _), List.getElem?_eq_getElem hkLtQ]
        · have hikLt := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hik
          have hNeOrd : orderArrBase H.vertexCount r.out.tables.next + k ≠
              orderArrBase H.vertexCount r.out.tables.next + i :=
            fun h => hik (Nat.add_left_cancel h.symm)
          have hNeTR : topoRankArrBase H.vertexCount r.out.tables.next + u ≠
              orderArrBase H.vertexCount r.out.tables.next + i :=
            Nat.ne_of_gt (Nat.lt_of_lt_of_le
              (Nat.add_lt_add_left hiN _) (hB1.symm ▸ Nat.le_add_right _ _))
          rw [hS13At _ hNeOrd hNeTR, hOrd i hikLt, hTakeQ1Opt i hi, List.getElem?_eq_getElem
            (Nat.lt_of_lt_of_le hikLt hkLeQ)]
      have hMidTR : ∀ i (hi : i < k + 1),
          (sMid.data[topoRankArrBase H.vertexCount r.out.tables.next +
              q1[i]'(Nat.lt_of_lt_of_le hi hkLtQ1)]?).map Fin.val = some i := by
        intro i hi
        have hq1i := Nat.lt_of_lt_of_le hi hkLtQ1
        have hRankArg := hBound1 _ (List.getElem_mem hq1i)
        have hFrameTR : topoRankArrBase H.vertexCount r.out.tables.next + q1[i]'hq1i <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next :=
          Nat.lt_of_lt_of_le (Nat.add_lt_add_left hRankArg _) hTRBound
        rw [hmFr _ (Or.inl hFrameTR)]
        by_cases hik : i = k
        · subst i
          rw [hTakeQ1Elem k (Nat.lt_succ_self _) hkLtQ1 hkLtQ, hRankWrite]
        · have hikLt := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hik
          have hiOld := Nat.lt_of_lt_of_le hikLt hkLeQ
          have hEqQ0 := hTakeQ1Elem i hi hq1i hiOld
          have hNeTR : topoRankArrBase H.vertexCount r.out.tables.next + u ≠
              topoRankArrBase H.vertexCount r.out.tables.next + q1[i]'hq1i := by
            rw [hEqQ0]
            intro h
            exact (Nat.ne_of_lt hikLt)
              (nodup_getElem_inj hqNd hiOld hkLtQ (Nat.add_left_cancel h.symm))
          have hOrdBefore : orderArrBase H.vertexCount r.out.tables.next + k <
              topoRankArrBase H.vertexCount r.out.tables.next := by
            rw [← hB1]
            exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le hkLtQ hqLenLe) _
          rw [hS13At _ (Nat.ne_of_lt (Nat.lt_of_lt_of_le hOrdBefore (Nat.le_add_right _ _)))
            hNeTR, hEqQ0]
          exact hTR i hikLt
      have hMidMeta : (sMid.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxTopoRankBase]?).map Fin.val =
          some (topoRankArrBase H.vertexCount r.out.tables.next) := by
        have hBeforeTemp : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxTopoRankBase <
            tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
          rw [← hB3]
          exact Nat.add_lt_add_left (by decide : mIdxTopoRankBase < 48) _
        have hRankBound : topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
            metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
          exact topoRankBeforeMeta H.vertexCount H.arcCount r.out.tables.next
        have hNeMetaTR : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxTopoRankBase ≠
            topoRankArrBase H.vertexCount r.out.tables.next + u :=
          Nat.ne_of_gt (Nat.lt_of_lt_of_le (Nat.add_lt_add_left huLt _)
            (Nat.le_trans hRankBound (Nat.le_add_right _ _)))
        have hNeOrd : orderArrBase H.vertexCount r.out.tables.next + k ≠
            metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxTopoRankBase :=
          Nat.ne_of_lt (Nat.lt_of_lt_of_le
            (Nat.add_lt_add_left (Nat.lt_of_lt_of_le hkLtQ hqLenLe) _)
            (Nat.le_trans (hB1 ▸ Nat.le_add_right _ _) (Nat.le_trans hRankBound (Nat.le_add_right _ _))))
        rw [hmFr _ (Or.inl hBeforeTemp), hS13At _ hNeOrd hNeMetaTR.symm]
        exact hMetaTR
      have hMidOutPref : ∀ i ≤ H.vertexCount,
          (sMid.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
            some (prefixOut H i) := by
        intro i hi
        rw [hmFr _ (Or.inr (Or.inl ⟨Nat.le_add_right _ _, by rw [Nat.add_assoc]; omega⟩)),
          hS13Temp _ (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))]
        exact hOutPref i hi
      obtain ⟨kRest, q2, t, hkRest, hStepsRest, hpct, hLen2, hNd2, hBound2, hZero2, hTopo2,
          ht0, ht1, htMeta, htOrd, htTR, htFr⟩ :=
        ih q1 (k + 1) sMid hkLtQ1 hLen1 hNd1 hBound1 (by omega)
          (fun v hv => by rw [hTakeNext, ← remInCount_finish_outer]; exact hZero1 v hv)
          hTopoNext hpcMid hm0 hm1 hmM (by rw [hm2, hTakeLen]) hm3 hm4 hm6 hm7 hm8 hm9 hm10
          hMidMeta hMidOrd hMidTR
          (fun v hv => by rw [hTakeNext, ← remInCount_finish_outer]; exact hmIndeg v hv)
          hMidOutPref hmQMem
          (fun w hw j => by
            rw [hmFr _ (Or.inr (Or.inr (by
              have hjLt := j.isLt
              have : prefixOut H w + degOut H w = prefixOut H (w + 1) := rfl
              have : prefixOut H (w + 1) ≤ prefixOut H H.vertexCount := prefixOut_mono H hw
              rw [prefixOut_vertexCount H] at this; omega))),
              hS13Temp _ (Nat.le_trans (Nat.le_add_right _ _)
                (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))]
            exact hOutArc w hw j)
      have hFoldNext : (q1.take (k + 1)).foldl (fun acc x => acc + degOut H x) 0 =
          (q0.take k).foldl (fun acc x => acc + degOut H x) 0 + degOut H u := by
        rw [hTakeNext, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hFoldLeM : (q1.take (k + 1)).foldl (fun acc x => acc + degOut H x) 0 ≤ H.arcCount :=
        list_nodup_sum_degOut_le H (q1.take (k + 1)) ((List.take_sublist _ _).nodup hNd1)
          (fun x hx => hBound1 x (List.mem_of_mem_take hx))
      have hkBound : (15 + kIn) + kRest ≤ 16 * (rem + 1) +
          16 * (H.arcCount - (q0.take k).foldl (fun acc x => acc + degOut H x) 0) + 1 := by
        rw [hFoldNext] at hkRest hFoldLeM; omega
      refine ⟨(15 + kIn) + kRest, q2, t, hkBound, (hStep15.append hStepsIn).append hStepsRest,
        hpct, hLen2, hNd2, hBound2, hZero2, hTopo2, ht0, ht1, htMeta, htOrd, htTR, fun a ha => ?_⟩
      rw [htFr a ha, hmFr a (by
        rcases ha with h | ⟨_, h2⟩ | h | h
        · exact Or.inl (Nat.lt_of_lt_of_le h (Nat.le_trans (Nat.le_add_right _ _) hOrdBound))
        · exact Or.inl h2
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h))]
      have hNe1 : a ≠ topoRankArrBase H.vertexCount r.out.tables.next + u := by
        rcases ha with h | ⟨h1, _⟩ | ⟨h1, _⟩ | h <;> omega
      have hNe2 : a ≠ orderArrBase H.vertexCount r.out.tables.next + k := by
        rcases ha with h | ⟨h1, _⟩ | ⟨h1, _⟩ | h <;> omega
      exact hS13At a hNe2.symm hNe1.symm
    · have hkEqQ : k = q0.length := by omega
      obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
        (by rw [hpc]; exact hPlOuter 0 _ rfl) (by split <;> omega)
      have hF : ¬ (reg st reg2).val < (reg st reg3).val := by rw [h2, h3, hkEqQ]; exact Nat.lt_irrefl _
      rw [ite_eq_right hF] at hpct
      have hrtF := reg_of_regs_eq hrt
      have hTakeEq : q0.take k = q0 := by rw [hkEqQ]; exact List.take_length
      rw [hTakeEq] at hZeroIff
      refine ⟨1, q0, t, by omega, steps_1_of_step hs, hpct, hqLenLe, hqNd, hBound, hZeroIff,
        fun _ i hi x harc => hTopo i (hkEqQ ▸ hi) x harc,
        by rw [hrtF, h0], by rw [hrtF, h1], by rw [hrtF, hMeta],
        fun i hi => by rw [hdt, hOrd i (hkEqQ ▸ hi), List.getElem?_eq_getElem hi],
        fun i hi => by rw [hdt]; exact hTR i (hkEqQ ▸ hi),
        fun _ _ => by rw [hdt]⟩

end KahnLoopPhase

end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
