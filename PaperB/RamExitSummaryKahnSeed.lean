module

public import PaperB.RamExitSummaryTrigger

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
Queue seeding for the word-RAM topological traversal.
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

theorem nodup_getElem_inj {α : Type} {xs : List α} (hNd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length)
    (hEq : xs[i]'hi = xs[j]'hj) : i = j := by
  have hPair := List.pairwise_iff_getElem.mp hNd
  rcases Nat.lt_trichotomy i j with hij | rfl | hji
  · exact False.elim (hPair i j hi hj hij hEq)
  · rfl
  · exact False.elim (hPair j i hj hi hji hEq.symm)

theorem list_getElem_eq_of_getElem?_eq {α : Type} {xs ys : List α} {i : Nat}
    (hx : i < xs.length) (hy : i < ys.length) (h : xs[i]? = ys[i]?) :
    xs[i]'hx = ys[i]'hy := by
  rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy] at h
  exact Option.some.inj h

section KahnMath

theorem list_countP_flip_single {α : Type} (xs : List α) (hNd : xs.Nodup)
    (p q : α → Bool) (x : α) (hxMem : x ∈ xs)
    (hpx : p x = true) (hqx : q x = false)
    (hAgree : ∀ y, y ≠ x → p y = q y) :
    xs.countP p = xs.countP q + 1 := by
  induction xs with
  | nil => cases hxMem
  | cons a as ih =>
    rw [List.nodup_cons] at hNd
    simp only [List.countP_cons]
    rcases List.mem_cons.mp hxMem with rfl | hxAs
    · have hTail : as.countP p = as.countP q := by
        apply List.countP_congr
        intro y hy
        have hne : y ≠ x := fun h => hNd.1 (h ▸ hy)
        exact by rw [hAgree y hne]
      rw [hpx, hqx, hTail]
      simp
    · have hne : a ≠ x := fun h => hNd.1 (h ▸ hxAs)
      have hpa : p a = q a := hAgree a hne
      have ih' := ih hNd.2 hxAs
      rw [hpa, ih']
      cases q a <;> simp [Nat.add_assoc]

theorem list_nodup_length_le_fin {n : Nat} (xs : List Nat)
    (hNd : xs.Nodup) (hBound : ∀ x ∈ xs, x < n) : xs.length ≤ n := by
  have hMap : (xs.map id).length = xs.length := by simp
  rw [← hMap, ← List.length_range (n := n)]
  apply list_nodup_length_le_of_subset
  · simpa using hNd
  · intro y hy
    simp only [List.map_id, List.mem_range] at hy ⊢
    exact hBound y hy

theorem list_nodup_all_mem_of_length_ge {n : Nat} (xs : List Nat)
    (hNd : xs.Nodup) (hBound : ∀ x ∈ xs, x < n)
    (hAll : ∀ x, x < n → x ∈ xs) : xs.length = n := by
  have hLe := list_nodup_length_le_fin xs hNd hBound
  have hGe : n ≤ xs.length := by
    rw [← List.length_range (n := n)]
    apply list_nodup_length_le_of_subset
    · exact List.nodup_range
    · intro y hy
      rw [List.mem_range] at hy
      exact hAll y hy
  exact Nat.le_antisymm hLe hGe

/-- Number of incoming arcs to vertex `v` whose sources have NOT yet been popped
and which have NOT yet been relaxed in the current vertex's outgoing adjacency scan. -/
def remInCount (H : LabelledQuotient) (popped extraRelaxed : List Nat) (v : Nat) : Nat :=
  (inArcsPrefix H H.arcCount v).countP fun e =>
    if h : e < H.arcCount then
      !(decide ((rawOccurrence H ⟨e, h⟩).1.val ∈ popped ∨ e ∈ extraRelaxed))
    else false

theorem remInCount_nil (H : LabelledQuotient) (v : Nat) :
    remInCount H [] [] v = degIn H v := by
  unfold remInCount degIn
  rw [← inArcsPrefix_length H H.arcCount v]
  apply List.countP_eq_length.mpr
  intro e he
  have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount v e he
  rw [dite_eq_left heLt]
  simp

theorem remInCount_pos_exists_arc {H : LabelledQuotient} {q : List Nat} {v : Nat}
    (hv : v < H.vertexCount) (hPos : 0 < remInCount H q [] v) :
    ∃ u : Vertex H, H.HasQuotientArc u ⟨v, hv⟩ ∧ u.val ∉ q := by
  unfold remInCount at hPos
  obtain ⟨e, heMem, hePred⟩ := List.countP_pos_iff.mp hPos
  have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount v e heMem
  rw [dite_eq_left heLt] at hePred
  simp only [List.not_mem_nil, or_false, Bool.not_eq_true', decide_eq_false_iff_not] at hePred
  obtain ⟨_, _, heHead⟩ := (mem_inArcsPrefix_iff H H.arcCount v e).mp heMem
  have hArc : H.HasQuotientArc (rawOccurrence H ⟨e, heLt⟩).1 ⟨v, hv⟩ :=
    (rawOccurrence_membership H (rawOccurrence H ⟨e, heLt⟩).1 ⟨v, hv⟩).mp
      ⟨⟨e, heLt⟩, rfl, Fin.ext heHead⟩
  exact ⟨(rawOccurrence H ⟨e, heLt⟩).1, hArc, hePred⟩

theorem remInCount_relax_step (H : LabelledQuotient) (popped : List Nat) (u j : Nat)
    (_hu : u < H.vertexCount) (huNotMem : u ∉ popped) (hj : j < degOut H u) :
    let e0 := (outArcsPrefix H H.arcCount u)[j]'(by rw [outArcsPrefix_length]; exact hj)
    have he0Lt : e0 < H.arcCount := outArcsPrefix_lt H H.arcCount u e0 (List.getElem_mem _)
    let v0 := (rawHead H ⟨e0, he0Lt⟩).val
    (remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v0 =
      remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v0 + 1) ∧
    (∀ v, v ≠ v0 →
      remInCount H popped ((outArcsPrefix H H.arcCount u).take (j + 1)) v =
      remInCount H popped ((outArcsPrefix H H.arcCount u).take j) v) := by
  intro e0 he0Lt v0
  have hjLen : j < (outArcsPrefix H H.arcCount u).length := by
    rw [outArcsPrefix_length]; exact hj
  have hTakeSucc : (outArcsPrefix H H.arcCount u).take (j + 1) =
      (outArcsPrefix H H.arcCount u).take j ++ [e0] :=
    List.take_succ_eq_append_getElem hjLen
  have he0Src : (rawOccurrence H ⟨e0, he0Lt⟩).1.val = u := by
    have hm := (mem_outArcsPrefix_iff H H.arcCount u e0).mp (List.getElem_mem hjLen)
    exact hm.2.2
  have he0NotTake : e0 ∉ (outArcsPrefix H H.arcCount u).take j := by
    intro hIn
    obtain ⟨i, hi, hiEq⟩ := List.mem_iff_getElem.mp hIn
    simp only [List.length_take] at hi
    have hiLtJ : i < j := Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _)
    have hiLen : i < (outArcsPrefix H H.arcCount u).length := Nat.lt_trans hiLtJ hjLen
    rw [List.getElem_take] at hiEq
    have hNodup := outArcsPrefix_nodup H H.arcCount u
    have hInj := nodup_getElem_inj hNodup (i := i) (j := j) hiLen hjLen hiEq
    omega
  constructor
  · apply list_countP_flip_single _ (inArcsPrefix_nodup H H.arcCount v0)
    · exact (mem_inArcsPrefix_iff H H.arcCount v0 e0).mpr ⟨he0Lt, he0Lt, rfl⟩
    · rw [dite_eq_left he0Lt, he0Src]
      simp [huNotMem, he0NotTake]
    · rw [dite_eq_left he0Lt, hTakeSucc]
      simp
    · intro y hyNe
      by_cases hyLt : y < H.arcCount
      · rw [dite_eq_left hyLt, dite_eq_left hyLt, hTakeSucc]
        simp [List.mem_append, hyNe]
      · rw [dite_eq_right hyLt, dite_eq_right hyLt]
  · intro v hvNe
    unfold remInCount
    apply List.countP_congr
    intro e heMem
    have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount v e heMem
    have heNe : e ≠ e0 := by
      intro heEq
      subst heEq
      obtain ⟨_, _, hvEq⟩ := (mem_inArcsPrefix_iff H H.arcCount v e0).mp heMem
      exact hvNe hvEq.symm
    rw [dite_eq_left heLt, dite_eq_left heLt, hTakeSucc]
    simp [List.mem_append, heNe]

theorem remInCount_finish_outer (H : LabelledQuotient) (popped : List Nat) (u v : Nat) :
    remInCount H popped (outArcsPrefix H H.arcCount u) v =
      remInCount H (popped ++ [u]) [] v := by
  unfold remInCount
  apply List.countP_congr
  intro e heMem
  have heLt : e < H.arcCount := inArcsPrefix_lt H H.arcCount v e heMem
  rw [dite_eq_left heLt, dite_eq_left heLt]
  simp only [List.not_mem_nil, or_false, List.mem_append, List.mem_singleton]
  have heOutIff : e ∈ outArcsPrefix H H.arcCount u ↔ (rawOccurrence H ⟨e, heLt⟩).1.val = u := by
    rw [mem_outArcsPrefix_iff]
    exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨heLt, heLt, h⟩⟩
  simp [heOutIff]

end KahnMath

section KahnSeed

variable {bits : Nat}

def kahnSeedSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg11 mIdxN (by dsimp only [mIdxN]; omega) ++
  (metaLoadInstrs reg3 reg11 mIdxTempBase (by dsimp only [mIdxTempBase]; omega) ++
  (metaLoadInstrs reg4 reg11 mIdxOrderBase (by dsimp only [mIdxOrderBase]; omega) ++
  (metaLoadInstrs reg5 reg11 mIdxTopoRankBase (by dsimp only [mIdxTopoRankBase]; omega) ++
  [ .add reg6 reg3 reg2
  , .add reg6 reg6 reg2
  , .add reg6 reg6 reg1
  , .mov reg7 reg0
  , .mov reg8 reg0
  ])))

def kahnSeedLoopInstrs : List (Instr bits 15) :=
  [ .branchLt reg8 reg2 18 26
  , .add reg9 reg3 reg8
  , .loadData reg9 reg9
  , .branchLt reg0 reg9 24 21
  , .add reg10 reg6 reg7
  , .storeData reg10 reg8
  , .add reg7 reg7 reg1
  , .add reg8 reg8 reg1
  , .goto 17
  ]

def kahnSeedExitInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaStoreInstrs reg7 reg11 mIdxKCursor (by dsimp only [mIdxKCursor]; omega)

def kahnSeedInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  kahnSeedSetupInstrs h100 ++ (kahnSeedLoopInstrs ++ kahnSeedExitInstrs h100)

end KahnSeed

section KahnSeedPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private theorem kahnSeedSetupInstrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (kahnSeedSetupInstrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  simp [kahnSeedSetupInstrs, metaLoadInstrs, nonHalt]

private theorem kahnSeedInstrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (kahnSeedInstrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  simp [kahnSeedInstrs, kahnSeedSetupInstrs, kahnSeedLoopInstrs, kahnSeedExitInstrs,
    metaLoadInstrs, metaStoreInstrs, nonHalt]

def kahnSeedPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (kahnSeedInstrs h100) (kahnSeedInstrs_nonHalt h100)

private theorem kahnSeedLoop_spec {code : Program DomL} {input : Input DomL}
    (H : LabelledQuotient) {m N : Nat}
    (hPl : Placed code 17 (kahnSeedLoopInstrs (bits := bits)))
    (hSz : 26 < code.size)
    (hTempFit : tempArrBase H.vertexCount m N + 3 * H.vertexCount + 1 ≤ workCap)
    (_hWorkFit : workCap ≤ 2 ^ bits) :
    ∀ (rem v : Nat) (q0 : List Nat) (st : State DomL),
      v + rem = H.vertexCount →
      q0.length ≤ v →
      q0.Nodup →
      (∀ x ∈ q0, x < v) →
      (∀ x, x < v → (x ∈ q0 ↔ degIn H x = 0)) →
      st.pc = 17 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase H.vertexCount m N →
      (reg st reg2).val = H.vertexCount →
      (reg st reg3).val = tempArrBase H.vertexCount m N →
      (reg st reg6).val = tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 →
      (reg st reg7).val = q0.length →
      (reg st reg8).val = v →
      (∀ x, x < H.vertexCount →
        (st.data[tempArrBase H.vertexCount m N + x]?).map Fin.val = some (degIn H x)) →
      (∀ i (hi : i < q0.length),
        (st.data[tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + i]?).map Fin.val =
          some (q0[i]'hi)) →
      ∃ k : Nat, ∃ q1 : List Nat, ∃ t : State DomL,
        k ≤ 9 * rem + 1 ∧
        Steps code input k st t ∧
        t.pc = 26 ∧
        q1.length ≤ H.vertexCount ∧
        q1.Nodup ∧
        (∀ x ∈ q1, x < H.vertexCount) ∧
        (∀ x, x < H.vertexCount → (x ∈ q1 ↔ degIn H x = 0)) ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
        (reg t rMeta).val = metaArrBase H.vertexCount m N ∧
        (reg t reg7).val = q1.length ∧
        (∀ i (hi : i < q1.length),
          (t.data[tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + i]?).map Fin.val =
            some (q1[i]'hi)) ∧
        (∀ j, (j < tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 ∨
            tempArrBase H.vertexCount m N + 3 * H.vertexCount + 1 ≤ j) →
          t.data[j]? = st.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro v q0 st hSum hLenLe hNd hBound hZeroIff hpc h0 h1 hMeta h2 h3 h6 h7 h8 hIndeg hQMem
    have hvN : v = H.vertexCount := by omega
    obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg8).val < (reg st reg2).val := by rw [h8, h2, hvN]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpct
    have hrtF := reg_of_regs_eq hrt
    refine ⟨1, q0, t, by omega, steps_1_of_step hs, hpct,
      by omega, hNd, fun x hx => hvN ▸ hBound x hx, fun x hx => hZeroIff x (hvN.symm ▸ hx),
      by rw [hrtF, h0], by rw [hrtF, h1], by rw [hrtF, hMeta], by rw [hrtF, h7],
      fun i hi => by rw [hdt]; exact hQMem i hi, fun j _ => by rw [hdt]⟩
  | succ rem ih =>
    intro v q0 st hSum hLenLe hNd hBound hZeroIff hpc h0 h1 hMeta h2 h3 h6 h7 h8 hIndeg hQMem
    have hvLt : v < H.vertexCount := by omega
    have hBaseEq : tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + H.vertexCount =
        tempArrBase H.vertexCount m N + 3 * H.vertexCount + 1 := by omega
    have hV2 : (reg st reg8).val < (reg st reg2).val := by rw [h8, h2]; exact hvLt
    obtain ⟨s1, hs1, hpc1, hrt1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    rw [ite_eq_left hV2] at hpc1
    have hr1 := reg_of_regs_eq hrt1
    have ha1 : code[s1.pc]? = some (.add reg9 reg3 reg8) := by rw [hpc1]; exact hPl 1 _ rfl
    have hFitIndeg : (reg s1 reg3).val + (reg s1 reg8).val < 2 ^ bits := by
      rw [hr1, hr1, h3, h8]; omega
    obtain ⟨s2, hs2, hpc2, h9_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by omega)
    have hAddrIndeg : (reg s2 reg9).val = tempArrBase H.vertexCount m N + v := by
      rw [h9_2, add_no_wrap _ _ hFitIndeg, hr1, hr1, h3, h8]
    obtain ⟨wDeg, hwDeg, hwDegV⟩ := Option.map_eq_some_iff.mp (hIndeg v hvLt)
    have hMemDeg : s2.data[(reg s2 reg9).val]? = some wDeg := by
      rw [hAddrIndeg, hd2, hd1]; exact hwDeg
    have hl1 : code[s2.pc]? = some (.loadData reg9 reg9) := by rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, hpc3, h9_3, ho3, hd3⟩ := step_loadData_at (input := input) hl1 (by omega) hMemDeg
    have h9Val : (reg s3 reg9).val = degIn H v := by rw [h9_3, hwDegV]
    have h0_3 : (reg s3 reg0).val = 0 := by rw [ho3 reg0 (by intro h; cases h), ho2 reg0 (by intro h; cases h), hr1, h0]
    have h1_3 : (reg s3 reg1).val = 1 := by rw [ho3 reg1 (by intro h; cases h), ho2 reg1 (by intro h; cases h), hr1, h1]
    have hM_3 : (reg s3 rMeta).val = metaArrBase H.vertexCount m N := by
      rw [ho3 rMeta (by intro h; cases h), ho2 rMeta (by intro h; cases h), hr1, hMeta]
    have h2_3 : (reg s3 reg2).val = H.vertexCount := by
      rw [ho3 reg2 (by intro h; cases h), ho2 reg2 (by intro h; cases h), hr1, h2]
    have h3_3 : (reg s3 reg3).val = tempArrBase H.vertexCount m N := by
      rw [ho3 reg3 (by intro h; cases h), ho2 reg3 (by intro h; cases h), hr1, h3]
    have h6_3 : (reg s3 reg6).val = tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 := by
      rw [ho3 reg6 (by intro h; cases h), ho2 reg6 (by intro h; cases h), hr1, h6]
    have h7_3 : (reg s3 reg7).val = q0.length := by
      rw [ho3 reg7 (by intro h; cases h), ho2 reg7 (by intro h; cases h), hr1, h7]
    have h8_3 : (reg s3 reg8).val = v := by
      rw [ho3 reg8 (by intro h; cases h), ho2 reg8 (by intro h; cases h), hr1, h8]
    have hd3' : s3.data = st.data := by rw [hd3, hd2, hd1]
    have hbr2 : code[s3.pc]? = some (.branchLt reg0 reg9 24 21) := by
      rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, hpc4, hrt4, hd4⟩ := step_branchLt_at (input := input) hbr2 (by split <;> omega)
    have hr4 := reg_of_regs_eq hrt4
    by_cases hDegPos : 0 < degIn H v
    · have hCond : (reg s3 reg0).val < (reg s3 reg9).val := by rw [h0_3, h9Val]; exact hDegPos
      rw [ite_eq_left hCond] at hpc4
      have haInc : code[s4.pc]? = some (.add reg8 reg8 reg1) := by rw [hpc4]; exact hPl 7 _ rfl
      have hFitV : (reg s4 reg8).val + (reg s4 reg1).val < 2 ^ bits := by
        rw [hr4, hr4, h8_3, h1_3]; omega
      obtain ⟨s5, hs5, hpc5, h8_5, ho5, hd5⟩ := step_add_at (input := input) haInc (by omega)
      have hg5 : code[s5.pc]? = some (.goto 17) := by rw [hpc5, hpc4]; exact hPl 8 _ rfl
      obtain ⟨s6, hs6, hpc6, hrt6, hd6⟩ := step_goto_at (input := input) hg5 (by omega)
      have hr6 := reg_of_regs_eq hrt6
      have hd6' : s6.data = st.data := by rw [hd6, hd5, hd4, hd3']
      have h8_6 : (reg s6 reg8).val = v + 1 := by
        rw [hr6, h8_5, add_no_wrap _ _ hFitV, hr4, hr4, h8_3, h1_3]
      have hStep6 : Steps code input 6 st s6 :=
        Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (steps_1_of_step hs6)))))
      obtain ⟨kRest, q1, t, hkRest, hStepsRest, hpct, hLen1, hNd1, hBound1, hZero1,
          ht0, ht1, htMeta, ht7, htQMem, htFr⟩ :=
        ih (v + 1) q0 s6 (by omega) (by omega) hNd
          (fun x hx => Nat.lt_succ_of_lt (hBound x hx))
          (fun x hx => by
            by_cases hxv : x = v
            · rw [hxv]; constructor
              · intro hxMem; exact absurd (hBound v hxMem) (Nat.lt_irrefl v)
              · intro hDeg0; omega
            · exact hZeroIff x (by omega))
          hpc6
          (by rw [hr6, ho5 reg0 (by intro h; cases h), hr4, h0_3])
          (by rw [hr6, ho5 reg1 (by intro h; cases h), hr4, h1_3])
          (by rw [hr6, ho5 rMeta (by intro h; cases h), hr4, hM_3])
          (by rw [hr6, ho5 reg2 (by intro h; cases h), hr4, h2_3])
          (by rw [hr6, ho5 reg3 (by intro h; cases h), hr4, h3_3])
          (by rw [hr6, ho5 reg6 (by intro h; cases h), hr4, h6_3])
          (by rw [hr6, ho5 reg7 (by intro h; cases h), hr4, h7_3])
          h8_6
          (fun x hx => by rw [hd6']; exact hIndeg x hx)
          (fun i hi => by rw [hd6']; exact hQMem i hi)
      refine ⟨6 + kRest, q1, t, by omega, hStep6.append hStepsRest, hpct,
        hLen1, hNd1, hBound1, hZero1, ht0, ht1, htMeta, ht7, htQMem,
        fun j hj => by rw [htFr j hj, hd6']⟩
    · have hDegZ : degIn H v = 0 := by omega
      have hCond : ¬ (reg s3 reg0).val < (reg s3 reg9).val := by rw [h0_3, h9Val]; exact hDegPos
      rw [ite_eq_right hCond] at hpc4
      have haQ : code[s4.pc]? = some (.add reg10 reg6 reg7) := by rw [hpc4]; exact hPl 4 _ rfl
      have hQFit : (reg s4 reg6).val + (reg s4 reg7).val < 2 ^ bits := by
        rw [hr4, hr4, h6_3, h7_3]; omega
      obtain ⟨s5, hs5, hpc5, h10_5, ho5, hd5⟩ := step_add_at (input := input) haQ (by omega)
      have hQAddr : (reg s5 reg10).val =
          tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + q0.length := by
        rw [h10_5, add_no_wrap _ _ hQFit, hr4, hr4, h6_3, h7_3]
      have hQLtSz : (reg s5 reg10).val < s5.data.size := by
        rw [hQAddr]; exact lt_data_size (by omega)
      have hstQ : code[s5.pc]? = some (.storeData reg10 reg8) := by
        rw [hpc5, hpc4]; exact hPl 5 _ rfl
      obtain ⟨s6, hs6, hpc6, hreg6, hd6⟩ := step_storeData_opaque (input := input) hstQ hQLtSz (by omega)
      have hr6 := reg_of_regs_eq hreg6
      have h8_6 : (reg s6 reg8).val = v := by
        rw [hr6, ho5 reg8 (by intro h; cases h), hr4, h8_3]
      have h1_6 : (reg s6 reg1).val = 1 := by
        rw [hr6, ho5 reg1 (by intro h; cases h), hr4, h1_3]
      have h7_6 : (reg s6 reg7).val = q0.length := by
        rw [hr6, ho5 reg7 (by intro h; cases h), hr4, h7_3]
      have haQTail : code[s6.pc]? = some (.add reg7 reg7 reg1) := by
        rw [hpc6, hpc5, hpc4]; exact hPl 6 _ rfl
      have hFitQTail : (reg s6 reg7).val + (reg s6 reg1).val < 2 ^ bits := by
        rw [h7_6, h1_6]; omega
      obtain ⟨s7, hs7, hpc7, h7_7, ho7, hd7⟩ := step_add_at (input := input) haQTail (by omega)
      have haV : code[s7.pc]? = some (.add reg8 reg8 reg1) := by
        rw [hpc7, hpc6, hpc5, hpc4]; exact hPl 7 _ rfl
      have h8_7 : (reg s7 reg8).val = v := by rw [ho7 reg8 (by intro h; cases h), h8_6]
      have h1_7 : (reg s7 reg1).val = 1 := by rw [ho7 reg1 (by intro h; cases h), h1_6]
      have hFitV2 : (reg s7 reg8).val + (reg s7 reg1).val < 2 ^ bits := by
        rw [h8_7, h1_7]; omega
      obtain ⟨s8, hs8, hpc8, h8_8, ho8, hd8⟩ := step_add_at (input := input) haV (by omega)
      have hg8 : code[s8.pc]? = some (.goto 17) := by
        rw [hpc8, hpc7, hpc6, hpc5, hpc4]; exact hPl 8 _ rfl
      obtain ⟨s9, hs9, hpc9, hrt9, hd9⟩ := step_goto_at (input := input) hg8 (by omega)
      have hr9 := reg_of_regs_eq hrt9
      have hd5' : s5.data = st.data := by rw [hd5, hd4, hd3']
      have hQLtSt : (reg s5 reg10).val < st.data.size := by rw [← hd5']; exact hQLtSz
      have hs9Data : s9.data = st.data.set (reg s5 reg10).val (reg s5 reg8) hQLtSt := by
        rw [hd9, hd8, hd7, hd6]
        exact array_set_eq_of_data_eq hd5' hQLtSz hQLtSt
      have hPres9 : ∀ r : Fin 15, r ≠ reg7 → r ≠ reg8 → r ≠ reg10 → reg s9 r = reg s3 r := by
        intro r hr7 hr8 hr10
        rw [hr9, ho8 r hr8, ho7 r hr7, hr6, ho5 r hr10, hr4]
      have hvNotMem : v ∉ q0 := fun hm => Nat.lt_irrefl v (hBound v hm)
      have hQ1Nd : (q0 ++ [v]).Nodup := by
        rw [List.nodup_append]
        exact ⟨hNd, (by simp : [v].Nodup), fun a ha b hb hab => by
          simp only [List.mem_singleton] at hb; subst hb; subst hab; exact hvNotMem ha⟩
      have hQ1Bound : ∀ x ∈ q0 ++ [v], x < v + 1 := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact Nat.lt_succ_of_lt (hBound x h)
        · simp only [List.mem_singleton] at h; subst h; exact Nat.lt_succ_self _
      have hQ1Zero : ∀ x, x < v + 1 → (x ∈ q0 ++ [v] ↔ degIn H x = 0) := by
        intro x hx
        rw [List.mem_append, List.mem_singleton]
        by_cases hxv : x = v
        · subst hxv; constructor
          · intro _; exact hDegZ
          · intro _; exact Or.inr rfl
        · have hxLt : x < v := by omega
          constructor
          · rintro (h | rfl)
            · exact (hZeroIff x hxLt).mp h
            · exact absurd rfl hxv
          · intro hz; exact Or.inl ((hZeroIff x hxLt).mpr hz)
      have hStep9 : Steps code input 9 st s9 :=
        Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
          (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (steps_1_of_step hs9))))))))
      have h7_9 : (reg s9 reg7).val = (q0 ++ [v]).length := by
        rw [hr9, ho8 reg7 (by intro h; cases h), h7_7, add_no_wrap _ _ hFitQTail, h7_6, h1_6]
        simp
      have h8_9 : (reg s9 reg8).val = v + 1 := by
        rw [hr9, h8_8, add_no_wrap _ _ hFitV2, h8_7, h1_7]
      have hIndeg9 : ∀ x, x < H.vertexCount →
          (s9.data[tempArrBase H.vertexCount m N + x]?).map Fin.val = some (degIn H x) := by
        intro x hx
        have hNe : tempArrBase H.vertexCount m N + x ≠
            tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + q0.length := by omega
        rw [hs9Data, Array.getElem?_set_ne hQLtSt (by rw [hQAddr]; exact hNe.symm)]
        exact hIndeg x hx
      have hQMem9 : ∀ i (hi : i < (q0 ++ [v]).length),
          (s9.data[tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + i]?).map Fin.val =
            some ((q0 ++ [v])[i]'hi) := by
        intro i hi
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hiLast : i = q0.length
        · subst hiLast
          rw [hs9Data, ← hQAddr]
          simp only [Array.getElem?_set_self hQLtSt, Option.map_some, List.getElem_append_right (Nat.le_refl _),
            Nat.sub_self, List.getElem_singleton]
          exact congrArg some (by rw [ho5 reg8 (by intro h; cases h), hr4, h8_3])
        · have hiLt : i < q0.length := by omega
          have hNe : tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + i ≠
              tempArrBase H.vertexCount m N + 2 * H.vertexCount + 1 + q0.length := by omega
          rw [hs9Data, Array.getElem?_set_ne hQLtSt (by rw [hQAddr]; exact hNe.symm),
            List.getElem_append_left hiLt]
          exact hQMem i hiLt
      obtain ⟨kRest, q1, t, hkRest, hStepsRest, hpct, hLen1, hNd1, hBound1, hZero1,
          ht0, ht1, htMeta, ht7, htQMem, htFr⟩ :=
        ih (v + 1) (q0 ++ [v]) s9 (by omega) (by simp; omega) hQ1Nd hQ1Bound hQ1Zero hpc9
          (by rw [hPres9 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0_3])
          (by rw [hPres9 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1_3])
          (by rw [hPres9 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hM_3])
          (by rw [hPres9 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2_3])
          (by rw [hPres9 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3_3])
          (by rw [hPres9 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6_3])
          h7_9 h8_9 hIndeg9 hQMem9
      refine ⟨9 + kRest, q1, t, by omega, hStep9.append hStepsRest, hpct,
        hLen1, hNd1, hBound1, hZero1, ht0, ht1, htMeta, ht7, htQMem, fun j hj => ?_⟩
      rw [htFr j hj, hs9Data]
      have hNe : j ≠ (reg s5 reg10).val := by rw [hQAddr]; rcases hj with h | h <;> omega
      exact Array.getElem?_set_ne hQLtSt hNe.symm

theorem run_kahnSeed {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (_hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hIndeg : ∀ v < H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v)) :
    ∃ k : Nat, ∃ q0 : List Nat, ∃ t : State DomL,
      k ≤ 9 * H.vertexCount + 25 ∧
      run (kahnSeedPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      q0.length ≤ H.vertexCount ∧
      q0.Nodup ∧
      (∀ x ∈ q0, x < H.vertexCount) ∧
      (∀ x, x < H.vertexCount → (x ∈ q0 ↔ degIn H x = 0)) ∧
      (t.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor]?).map Fin.val =
        some q0.length ∧
      (∀ i (hi : i < q0.length),
        (t.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i]?).map Fin.val =
          some (q0[i]'hi)) ∧
      (∀ j, (j < metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor ∨
          (metaArrBase H.vertexCount H.arcCount r.out.tables.next + (mIdxKCursor + 1) ≤ j ∧
            j < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap := by
    have h1 := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *
    rw [metaArrBase_eq] at *
    omega
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hTempFit : tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤ workCap := by
    omega
  let ph := kahnSeedPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (kahnSeedInstrs (bits := bits) h100).length = 29 := by
    simp [kahnSeedInstrs, kahnSeedSetupInstrs, kahnSeedLoopInstrs, kahnSeedExitInstrs,
      metaLoadInstrs, metaStoreInstrs]
  have hCodeSize : ph.code.size = 30 := by
    dsimp [ph, kahnSeedPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (kahnSeedInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold kahnSeedInstrs at hPlFull; exact hPlFull)
  have hPlRest := Placed_append_right (by unfold kahnSeedInstrs at hPlFull; exact hPlFull)
  rw [show (kahnSeedSetupInstrs (bits := bits) h100).length = 17 by
    simp [kahnSeedSetupInstrs, metaLoadInstrs]] at hPlRest
  have hPlLoop := Placed_append_left hPlRest
  have hPlExit := Placed_append_right hPlRest
  rw [show (kahnSeedLoopInstrs (bits := bits)).length = 9 by rfl] at hPlExit
  have hPlN := Placed_append_left (by unfold kahnSeedSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold kahnSeedSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPlTemp := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
  have hPlOrd := Placed_append_left hPlS2
  have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
  have hPlTR := Placed_append_left hPlS3
  have hPlTail := Placed_append_right hPlS3; rw [hLml] at hPlTail
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlN (by omega) rfl hMeta.rMeta_eq (by dsimp only [mIdxN]; omega) hMeta.meta_n
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlTemp (by omega) hpc1 hMeta1 (by dsimp only [mIdxTempBase]; omega) (by rw [hd1]; exact hMeta.meta_tempBase)
  have hMeta2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho2 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta1
  obtain ⟨s3, hs3, hpc3, hd3, _, ho3⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlOrd (by omega) hpc2 hMeta2 (by dsimp only [mIdxOrderBase]; omega) (by rw [hd2, hd1]; exact hMeta.meta_orderBase)
  have hMeta3 : (reg s3 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho3 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta2
  obtain ⟨s4, hs4, hpc4, hd4, _, ho4⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlTR (by omega) hpc3 hMeta3 (by dsimp only [mIdxTopoRankBase]; omega) (by rw [hd3, hd2, hd1]; exact hMeta.meta_topoRankBase)
  have hMeta4 : (reg s4 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho4 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta3
  have h0_4 : (reg s4 reg0).val = 0 := by
    rw [ho4 reg0 (by intro h; cases h) (by intro h; cases h), ho3 reg0 (by intro h; cases h) (by intro h; cases h),
      ho2 reg0 (by intro h; cases h) (by intro h; cases h), ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_4 : (reg s4 reg1).val = 1 := by
    rw [ho4 reg1 (by intro h; cases h) (by intro h; cases h), ho3 reg1 (by intro h; cases h) (by intro h; cases h),
      ho2 reg1 (by intro h; cases h) (by intro h; cases h), ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have h2_4 : (reg s4 reg2).val = H.vertexCount := by
    rw [ho4 reg2 (by intro h; cases h) (by intro h; cases h), ho3 reg2 (by intro h; cases h) (by intro h; cases h),
      ho2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h3_4 : (reg s4 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho4 reg3 (by intro h; cases h) (by intro h; cases h), ho3 reg3 (by intro h; cases h) (by intro h; cases h), h3_2]
  have ha1 : ph.code[s4.pc]? = some (.add reg6 reg3 reg2) := by
    rw [show s4.pc = 0 + 3 + 3 + 3 + 3 + 0 by omega]; exact hPlTail 0 _ rfl
  obtain ⟨s5, hs5, hpc5, h6_5, ho5, hd5⟩ := step_add_at (input := input) ha1 (by omega)
  have h6Val5 : (reg s5 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [h6_5, add_no_wrap _ _ (by rw [h3_4, h2_4]; omega), h3_4, h2_4]
  have h2_5 : (reg s5 reg2).val = H.vertexCount := by rw [ho5 reg2 (by intro h; cases h), h2_4]
  have ha2 : ph.code[s5.pc]? = some (.add reg6 reg6 reg2) := by
    rw [show s5.pc = 0 + 3 + 3 + 3 + 3 + 1 by omega]; exact hPlTail 1 _ rfl
  obtain ⟨s6, hs6, hpc6, h6_6, ho6, hd6⟩ := step_add_at (input := input) ha2 (by omega)
  have h6Val6 : (reg s6 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount := by
    rw [h6_6, add_no_wrap _ _ (by rw [h6Val5, h2_5]; omega), h6Val5, h2_5]; omega
  have h1_6 : (reg s6 reg1).val = 1 := by rw [ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h), h1_4]
  have ha3 : ph.code[s6.pc]? = some (.add reg6 reg6 reg1) := by
    rw [show s6.pc = 0 + 3 + 3 + 3 + 3 + 2 by omega]; exact hPlTail 2 _ rfl
  obtain ⟨s7, hs7, hpc7, h6_7, ho7, hd7⟩ := step_add_at (input := input) ha3 (by omega)
  have hm1 : ph.code[s7.pc]? = some (.mov reg7 reg0) := by
    rw [show s7.pc = 0 + 3 + 3 + 3 + 3 + 3 by omega]; exact hPlTail 3 _ rfl
  obtain ⟨s8, hs8, hpc8, h7_8, ho8, hd8⟩ := step_mov_at (input := input) hm1 (by omega)
  have hm2 : ph.code[s8.pc]? = some (.mov reg8 reg0) := by
    rw [show s8.pc = 0 + 3 + 3 + 3 + 3 + 4 by omega]; exact hPlTail 4 _ rfl
  obtain ⟨s9, hs9, hpc9, h8_9, ho9, hd9⟩ := step_mov_at (input := input) hm2 (by omega)
  have hd9' : s9.data = s0.data := by
    rw [hd9, hd8, hd7, hd6, hd5, hd4, hd3, hd2, hd1, data_initial]
  have h0_9 : (reg s9 reg0).val = 0 := by
    rw [ho9 reg0 (by intro h; cases h), ho8 reg0 (by intro h; cases h), ho7 reg0 (by intro h; cases h),
      ho6 reg0 (by intro h; cases h), ho5 reg0 (by intro h; cases h), h0_4]
  have h1_9 : (reg s9 reg1).val = 1 := by
    rw [ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h), ho7 reg1 (by intro h; cases h), h1_6]
  have hM_9 : (reg s9 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h), ho7 rMeta (by intro h; cases h),
      ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h), hMeta4]
  have h2_9 : (reg s9 reg2).val = H.vertexCount := by
    rw [ho9 reg2 (by intro h; cases h), ho8 reg2 (by intro h; cases h), ho7 reg2 (by intro h; cases h),
      ho6 reg2 (by intro h; cases h), h2_5]
  have h3_9 : (reg s9 reg3).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho9 reg3 (by intro h; cases h), ho8 reg3 (by intro h; cases h), ho7 reg3 (by intro h; cases h),
      ho6 reg3 (by intro h; cases h), ho5 reg3 (by intro h; cases h), h3_4]
  have h6_9 : (reg s9 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 := by
    rw [ho9 reg6 (by intro h; cases h), ho8 reg6 (by intro h; cases h),
      h6_7, add_no_wrap _ _ (by rw [h6Val6, h1_6]; omega), h6Val6, h1_6]
  have h7_9 : (reg s9 reg7).val = 0 := by
    rw [ho9 reg7 (by intro h; cases h), h7_8, ho7 reg0 (by intro h; cases h),
      ho6 reg0 (by intro h; cases h), ho5 reg0 (by intro h; cases h), h0_4]
  have h8_9' : (reg s9 reg8).val = 0 := by
    rw [h8_9, ← ho9 reg0 (by intro h; cases h), h0_9]
  obtain ⟨kLoop, q0, sLoop, hkLoop, hStepsLoop, hpcLoop, hLenQ, hNdQ, hBoundQ, hZeroQ,
      h0L, h1L, hML, h7L, hQMemL, hFrL⟩ :=
    kahnSeedLoop_spec H hPlLoop (by omega) hTempFit hw H.vertexCount 0 [] s9 (Nat.zero_add _)
      (by simp) List.nodup_nil (fun _ hx => by cases hx) (fun _ hx => absurd hx (Nat.not_lt_zero _))
      (by omega) h0_9 h1_9 hM_9 h2_9 h3_9 h6_9 h7_9 h8_9'
      (fun x hx => by rw [hd9']; exact hIndeg x hx) (fun _ hi => by cases hi)
  have hFitCursor : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor < 2 ^ bits := by
    dsimp only [mIdxKCursor]; omega
  have hLtCursor : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor < sLoop.data.size :=
    lt_data_size (by dsimp only [mIdxKCursor]; omega)
  obtain ⟨t, hsExit, hpct, htCursor, htFrE, hoExit⟩ := run_metaStore_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlExit (by omega) hpcLoop hML hFitCursor hLtCursor
  have hSetupSteps : Steps ph.code input 17 (Phase.initial s0) s9 :=
    hs1.append (hs2.append (hs3.append (hs4.append
      (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (steps_1_of_step hs9))))))))
  have hHalt : step ph.code input t = some (.halted t) :=
    haltAt_mkHaltPhase (hi := hi) (hw := hw) (kahnSeedInstrs (bits := bits) h100) _
      (by rw [hpct, hCodeLen]) (input := input)
  refine ⟨17 + kLoop + 3 + 1, q0, t, by omega, ((hSetupSteps.append hStepsLoop).append hsExit).halts hHalt,
    ?_, hLenQ, hNdQ, hBoundQ, hZeroQ, ?_, ?_, ?_⟩
  · apply hMeta.preserve (by rw [hoExit rMeta (by intro h; cases h), hML])
      (by rw [hoExit reg0 (by intro h; cases h), h0L]) (by rw [hoExit reg1 (by intro h; cases h), h1L])
    intro i hi22
    rw [htFrE _ (by dsimp only [mIdxKCursor]; omega), hFrL _ (Or.inl (by rw [← hB3]; omega)), hd9']
  · rw [htCursor, Option.map_some, h7L]
  · intro i hi
    rw [htFrE _ (by dsimp only [mIdxKCursor]; omega)]
    exact hQMemL i hi
  · intro j hj
    dsimp only [mIdxKCursor] at hj ⊢
    have hNeC : j ≠ metaArrBase H.vertexCount H.arcCount r.out.tables.next + 22 := by
      rcases hj with h | ⟨h1, _⟩ | h <;> try rw [← hB3] at *
      · omega
      · omega
      · omega
    rw [htFrE j hNeC, hFrL j (by
      rcases hj with h | ⟨_, h2⟩ | h
      · exact Or.inl (by rw [← hB3]; omega)
      · exact Or.inl h2
      · exact Or.inr h), hd9']

end KahnSeedPhase

end Stage2CsrKahn

end PaperB.RamProgram.ExitSummaryBuild
