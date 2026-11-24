module

public import PaperB.RamExitSummaryKahnOuter

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 2000000

/-!
Kahn traversal of the quotient and composition with exit-summary initialization.
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

private theorem kahn_all_visited_strong {H : LabelledQuotient}
    (rank : Vertex H → Nat)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {q : List Nat}
    (hZero : ∀ v, v < H.vertexCount → (v ∈ q ↔ remInCount H q [] v = 0)) :
    ∀ v : Vertex H, v.val ∈ q := by
  have hStrong : ∀ bound : Nat, ∀ v : Vertex H, rank v = bound → v.val ∈ q := by
    intro bound
    induction bound using Nat.strongRecOn with
    | _ bound ih =>
      intro v hbv
      apply Classical.byContradiction
      intro hNot
      have hPos : 0 < remInCount H q [] v.val := by
        cases hc : remInCount H q [] v.val with
        | zero => exact False.elim (hNot ((hZero v.val v.isLt).mpr hc))
        | succ _ => exact Nat.zero_lt_succ _
      obtain ⟨u, hArc, huNot⟩ := remInCount_pos_exists_arc v.isLt hPos
      have hlt : rank u < bound := hbv ▸ rankArc u v hArc
      exact huNot (ih (rank u) hlt u rfl)
  intro v
  exact hStrong (rank v) v rfl

private theorem kahnLoop_setup20 {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hTempCap : tempArrBase H.vertexCount H.arcCount r.out.tables.next +
      (3 * H.vertexCount + 2 + H.arcCount) ≤ workCap)
    (hPlSetup : Placed code 0 (kahnLoopSetupInstrs (bits := bits) h100))
    (hSz : 20 < code.size)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (q0 : List Nat)
    (hCurMem : (s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor]?).map Fin.val =
      some q0.length)
    {qhVal : Nat}
    (hQHMem : (s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxQHeadInBase]?).map Fin.val =
      some qhVal) :
    ∃ s10 : State DomL,
      Steps code input 20 (Phase.initial s0) s10 ∧
      s10.pc = 20 ∧
      s10.data = s0.data ∧
      (reg s10 reg0).val = 0 ∧
      (reg s10 reg1).val = 1 ∧
      (reg s10 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next ∧
      (reg s10 reg2).val = 0 ∧
      (reg s10 reg3).val = q0.length ∧
      (reg s10 reg4).val = orderArrBase H.vertexCount r.out.tables.next ∧
      (reg s10 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next ∧
      (reg s10 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ∧
      (reg s10 reg8).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ∧
      (reg s10 reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 ∧
      (0 < H.arcCount → (reg s10 reg10).val = 4 + H.vertexCount + 4 * r.out.tables.next + H.arcCount) := by
  have hB3 : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlTemp := Placed_append_left (by unfold kahnLoopSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold kahnLoopSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPlN := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
  have hPlAdds := Placed_append_left hPlS2
  have hPlS3 := Placed_append_right hPlS2
  rw [show ([Instr.add reg7 reg6 reg13, Instr.add reg9 reg7 reg13,
    Instr.add reg9 reg9 reg1, Instr.add reg8 reg9 reg13] : List (Instr bits 15)).length = 4 by rfl] at hPlS3
  have hPlCur := Placed_append_left hPlS3
  have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
  have hPlOrd := Placed_append_left hPlS4
  have hPlS5 := Placed_append_right hPlS4; rw [hLml] at hPlS5
  have hPlQH := Placed_append_left hPlS5
  have hPlMov := Placed_append_right hPlS5; rw [hLml] at hPlMov
  obtain ⟨s1, hs1, hpc1, hd1, h6_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlTemp (by omega) rfl hMeta.rMeta_eq (by dsimp only [mIdxTempBase]; omega) hMeta.meta_tempBase
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h13_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlN (by omega) hpc1 hMeta1 (by dsimp only [mIdxN]; omega) (by rw [hd1]; exact hMeta.meta_n)
  have h6_2 : (reg s2 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho2 reg6 (by intro h; cases h) (by intro h; cases h), h6_1]
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [ho2 reg1 (by intro h; cases h) (by intro h; cases h),
      ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have ha1 : code[s2.pc]? = some (.add reg7 reg6 reg13) := by
    rw [show s2.pc = 0 + 3 + 3 + 0 by omega]; exact hPlAdds 0 _ rfl
  obtain ⟨s3, hs3, hpc3, h7_3, ho3, hd3⟩ := step_add_at (input := input) ha1 (by omega)
  have h7Val3 : (reg s3 reg7).val =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [h7_3, add_no_wrap _ _ (by rw [h6_2, h13_2]; omega), h6_2, h13_2]
  have h13_3 : (reg s3 reg13).val = H.vertexCount := by rw [ho3 reg13 (by intro h; cases h), h13_2]
  have ha2 : code[s3.pc]? = some (.add reg9 reg7 reg13) := by
    rw [show s3.pc = 0 + 3 + 3 + 1 by omega]; exact hPlAdds 1 _ rfl
  obtain ⟨s4, hs4, hpc4, h9_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by omega)
  have h9Val4 : (reg s4 reg9).val =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount := by
    rw [h9_4, add_no_wrap _ _ (by rw [h7Val3, h13_3]; omega), h7Val3, h13_3]; omega
  have h1_4 : (reg s4 reg1).val = 1 := by
    rw [ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), h1_2]
  have ha3 : code[s4.pc]? = some (.add reg9 reg9 reg1) := by
    rw [show s4.pc = 0 + 3 + 3 + 2 by omega]; exact hPlAdds 2 _ rfl
  obtain ⟨s5, hs5, hpc5, h9_5, ho5, hd5⟩ := step_add_at (input := input) ha3 (by omega)
  have h9Val5 : (reg s5 reg9).val =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 := by
    rw [h9_5, add_no_wrap _ _ (by rw [h9Val4, h1_4]; omega), h9Val4, h1_4]
  have h13_5 : (reg s5 reg13).val = H.vertexCount := by
    rw [ho5 reg13 (by intro h; cases h), ho4 reg13 (by intro h; cases h), h13_3]
  have ha4 : code[s5.pc]? = some (.add reg8 reg9 reg13) := by
    rw [show s5.pc = 0 + 3 + 3 + 3 by omega]; exact hPlAdds 3 _ rfl
  obtain ⟨s6, hs6, hpc6, h8_6, ho6, hd6⟩ := step_add_at (input := input) ha4 (by omega)
  have h8Val6 : (reg s6 reg8).val =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 := by
    rw [h8_6, add_no_wrap _ _ (by rw [h9Val5, h13_5]; omega), h9Val5, h13_5]; omega
  have hd6' : s6.data = s0.data := by rw [hd6, hd5, hd4, hd3, hd2, hd1, data_initial]
  have hMeta6 : (reg s6 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho6 rMeta (by intro h; cases h), ho5 rMeta (by intro h; cases h), ho4 rMeta (by intro h; cases h),
      ho3 rMeta (by intro h; cases h), ho2 rMeta (by intro h; cases h) (by intro h; cases h), hMeta1]
  have h6_6 : (reg s6 reg6).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho6 reg6 (by intro h; cases h), ho5 reg6 (by intro h; cases h), ho4 reg6 (by intro h; cases h),
      ho3 reg6 (by intro h; cases h), h6_2]
  have h7_6 : (reg s6 reg7).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount := by
    rw [ho6 reg7 (by intro h; cases h), ho5 reg7 (by intro h; cases h), ho4 reg7 (by intro h; cases h), h7Val3]
  have h9_6 : (reg s6 reg9).val = tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 := by
    rw [ho6 reg9 (by intro h; cases h), h9Val5]
  have h0_6 : (reg s6 reg0).val = 0 := by
    rw [ho6 reg0 (by intro h; cases h), ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h),
      ho3 reg0 (by intro h; cases h), ho2 reg0 (by intro h; cases h) (by intro h; cases h),
      ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_6 : (reg s6 reg1).val = 1 := by
    rw [ho6 reg1 (by intro h; cases h), ho5 reg1 (by intro h; cases h), h1_4]
  obtain ⟨s7, hs7, hpc7, hd7, h3_7, ho7⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlCur (by omega) (by rw [hpc6]; omega) hMeta6 (by dsimp only [mIdxKCursor]; omega)
    (by rw [hd6']; exact hCurMem)
  have hMeta7 : (reg s7 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho7 rMeta (by intro h; cases h) (by intro h; cases h), hMeta6]
  obtain ⟨s8, hs8, hpc8, hd8, h4_8, ho8⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlOrd (by omega) hpc7 hMeta7 (by dsimp only [mIdxOrderBase]; omega)
    (by rw [hd7, hd6']; exact hMeta.meta_orderBase)
  have hMeta8 : (reg s8 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho8 rMeta (by intro h; cases h) (by intro h; cases h), hMeta7]
  obtain ⟨s9, hs9, hpc9, hd9, h10_9, ho9⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlQH (by omega) hpc8 hMeta8 (by dsimp only [mIdxQHeadInBase]; omega)
    (by rw [hd8, hd7, hd6']; exact hQHMem)
  have h0_9 : (reg s9 reg0).val = 0 := by
    rw [ho9 reg0 (by intro h; cases h) (by intro h; cases h), ho8 reg0 (by intro h; cases h) (by intro h; cases h),
      ho7 reg0 (by intro h; cases h) (by intro h; cases h), h0_6]
  have hm1 : code[s9.pc]? = some (.mov reg2 reg0) := by rw [hpc9]; exact hPlMov 0 _ rfl
  obtain ⟨s10, hs10, hpc10, h2_10, ho10, hd10⟩ := step_mov_at (input := input) hm1 (by omega)
  refine ⟨s10,
    hs1.append (hs2.append (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (hs7.append (hs8.append (hs9.append (steps_1_of_step hs10))))))))),
    by omega, by rw [hd10, hd9, hd8, hd7, hd6'], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ho10 reg0 (by intro h; cases h), h0_9]
  · rw [ho10 reg1 (by intro h; cases h), ho9 reg1 (by intro h; cases h) (by intro h; cases h),
      ho8 reg1 (by intro h; cases h) (by intro h; cases h), ho7 reg1 (by intro h; cases h) (by intro h; cases h), h1_6]
  · rw [ho10 rMeta (by intro h; cases h), ho9 rMeta (by intro h; cases h) (by intro h; cases h), hMeta8]
  · rw [h2_10, h0_9]
  · rw [ho10 reg3 (by intro h; cases h), ho9 reg3 (by intro h; cases h) (by intro h; cases h),
      ho8 reg3 (by intro h; cases h) (by intro h; cases h), h3_7]
  · rw [ho10 reg4 (by intro h; cases h), ho9 reg4 (by intro h; cases h) (by intro h; cases h), h4_8]
  · rw [ho10 reg6 (by intro h; cases h), ho9 reg6 (by intro h; cases h) (by intro h; cases h),
      ho8 reg6 (by intro h; cases h) (by intro h; cases h), ho7 reg6 (by intro h; cases h) (by intro h; cases h), h6_6]
  · rw [ho10 reg7 (by intro h; cases h), ho9 reg7 (by intro h; cases h) (by intro h; cases h),
      ho8 reg7 (by intro h; cases h) (by intro h; cases h), ho7 reg7 (by intro h; cases h) (by intro h; cases h), h7_6]
  · rw [ho10 reg8 (by intro h; cases h), ho9 reg8 (by intro h; cases h) (by intro h; cases h),
      ho8 reg8 (by intro h; cases h) (by intro h; cases h), ho7 reg8 (by intro h; cases h) (by intro h; cases h), h8Val6]
  · rw [ho10 reg9 (by intro h; cases h), ho9 reg9 (by intro h; cases h) (by intro h; cases h),
      ho8 reg9 (by intro h; cases h) (by intro h; cases h), ho7 reg9 (by intro h; cases h) (by intro h; cases h), h9_6]
  · intro hm
    rw [ho10 reg10 (by intro h; cases h), h10_9]
    exact Option.some.inj ((hQHMem.symm).trans (by rw [hMeta.meta_qHeadIn hm]))

private theorem run_kahnLoop_aux {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (hPlSetup : Placed code 0 (kahnLoopSetupInstrs (bits := bits) h100))
    (hPlOuter : Placed code 20 (kahnLoopOuterInstrs (bits := bits) h100))
    (hPlInner : Placed code 35 (kahnLoopInnerInstrs (bits := bits)))
    (hSz : 51 < code.size)
    (hHalt : ∀ t : State DomL, t.pc = 51 → step code input t = some (.halted t))
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (q0 : List Nat) (hqLen : q0.length ≤ H.vertexCount) (hqNd : q0.Nodup)
    (hqBound : ∀ x ∈ q0, x < H.vertexCount)
    (hqZero : ∀ x, x < H.vertexCount → (x ∈ q0 ↔ degIn H x = 0))
    (hCurMem : (s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor]?).map Fin.val =
      some q0.length)
    (hIndeg : ∀ v < H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v))
    (hOutPref : ∀ i ≤ H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i))
    (hQMem : ∀ i (hi : i < q0.length),
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i]?).map Fin.val =
        some (q0[i]'hi))
    (hOutArc : ∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u + j.val)]?).map Fin.val =
        some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) :
    ∃ steps : Nat, ∃ orderKahn : Array (Vertex H), ∃ sizeKahn : orderKahn.size = H.vertexCount,
      ∃ rankKahn : Vertex H → Nat, ∃ t : State DomL,
      steps ≤ 16 * H.vertexCount + 16 * H.arcCount + 25 ∧
      run code input steps (Phase.initial s0) = some ⟨t, steps⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      orderKahn.toList.Nodup ∧
      (∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt orderKahn sizeKahn i = v) ∧
      (∀ i : Fin H.vertexCount, rankKahn (orderedVertexAt orderKahn sizeKahn i) = i.val) ∧
      (∀ i j : Fin H.vertexCount, i.val < j.val →
        rankKahn (orderedVertexAt orderKahn sizeKahn i) <
          rankKahn (orderedVertexAt orderKahn sizeKahn j)) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v) ∧
      (∀ i : Fin H.vertexCount,
        (t.data[orderArrBase H.vertexCount r.out.tables.next + i.val]?).map Fin.val =
          some (orderedVertexAt orderKahn sizeKahn i).val) ∧
      (∀ v : Vertex H,
        (t.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
          some (rankKahn v)) ∧
      (∀ a, (a < orderArrBase H.vertexCount r.out.tables.next ∨
          (topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ a ∧
            a < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ≤ a ∧
            a < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤ a) →
        t.data[a]? = s0.data[a]?) := by
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
  have hQHeadExists : ∃ qhVal : Nat,
      (s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxQHeadInBase]?).map Fin.val =
        some qhVal := by
    have hSzS : metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxQHeadInBase < s0.data.size :=
      lt_data_size (by dsimp only [mIdxQHeadInBase]; omega)
    exact ⟨(s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxQHeadInBase]'hSzS).val,
      by simp [Array.getElem?_eq_getElem hSzS]⟩
  obtain ⟨qhVal, hQHMem⟩ := hQHeadExists
  obtain ⟨s10, hSetupSteps, hpc10, hd10', h0_10, h1_10, hM_10, h2_10', h3_10, h4_10,
      h6_10, h7_10, h8_10, h9_10, h10_10⟩ :=
    kahnLoop_setup20 h100 hTempCap hPlSetup (by omega) s0 hMeta q0 hCurMem hQHMem
  obtain ⟨kOuter, q1, t, hkOuter, hStepsOuter, hpct, hLen1, hNd1, hBound1, hZero1, hTopo1,
      ht0, ht1, htM, htOrd, htTR, htFr⟩ :=
    kahnLoopOuter_spec h100 hIn hTempCap hw hi hPlOuter hPlInner (by omega)
      H.vertexCount q0 0 s10 (Nat.zero_le _) hqLen hqNd hqBound (Nat.zero_add _)
      (fun v hv => by rw [List.take_zero, remInCount_nil]; exact hqZero v hv)
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      hpc10 h0_10 h1_10 hM_10 h2_10' h3_10 h4_10 h6_10 h7_10 h8_10 h9_10 h10_10
      (by rw [hd10']; exact hMeta.meta_topoRankBase)
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun v hv => by rw [hd10', List.take_zero, remInCount_nil]; exact hIndeg v hv)
      (fun i hi => by rw [hd10']; exact hOutPref i hi)
      (fun i hi => by rw [hd10']; exact hQMem i hi)
      (fun u hu j => by rw [hd10']; exact hOutArc u hu j)
  have hAllMem : ∀ v : Vertex H, v.val ∈ q1 := kahn_all_visited_strong rank rankArc hZero1
  have hLenEqN : q1.length = H.vertexCount :=
    list_nodup_all_mem_of_length_ge q1 hNd1 hBound1 (fun x hx => hAllMem ⟨x, hx⟩)
  let orderKahn : Array (Vertex H) :=
    Array.ofFn fun i : Fin H.vertexCount =>
      ⟨q1[i.val]'(Nat.lt_of_lt_of_eq i.isLt hLenEqN.symm),
        hBound1 _ (List.getElem_mem (Nat.lt_of_lt_of_eq i.isLt hLenEqN.symm))⟩
  have sizeKahn : orderKahn.size = H.vertexCount := by simp [orderKahn]
  have hOrdAt : ∀ i : Fin H.vertexCount,
      (orderedVertexAt orderKahn sizeKahn i).val =
        q1[i.val]'(Nat.lt_of_lt_of_eq i.isLt hLenEqN.symm) := fun i => by
    simp [orderedVertexAt, orderKahn]
  have hOrdNodup : orderKahn.toList.Nodup := by
    rw [List.nodup_iff_pairwise_ne, List.pairwise_iff_getElem]
    intro i j hi hj hij hEq
    have hSize : orderKahn.toList.length = H.vertexCount := by simp [orderKahn]
    have hiN : i < H.vertexCount := Nat.lt_of_lt_of_eq hi hSize
    have hjN : j < H.vertexCount := Nat.lt_of_lt_of_eq hj hSize
    have hVal : (orderedVertexAt orderKahn sizeKahn ⟨i, hiN⟩).val =
        (orderedVertexAt orderKahn sizeKahn ⟨j, hjN⟩).val := by
      simpa only [orderedVertexAt, Array.getElem_toList] using congrArg Fin.val hEq
    rw [hOrdAt, hOrdAt] at hVal
    have hIj := nodup_getElem_inj hNd1 (Nat.lt_of_lt_of_eq hiN hLenEqN.symm)
      (Nat.lt_of_lt_of_eq hjN hLenEqN.symm) hVal
    exact Nat.ne_of_lt hij hIj
  let rankKahn : Vertex H → Nat := fun v =>
    Classical.choose (List.mem_iff_getElem.mp (hAllMem v))
  have hRankSpec : ∀ v : Vertex H,
      ∃ hv : rankKahn v < q1.length, q1[rankKahn v]'hv = v.val := fun v =>
    Classical.choose_spec (List.mem_iff_getElem.mp (hAllMem v))
  have hRankLt : ∀ v : Vertex H, rankKahn v < H.vertexCount := fun v =>
    Nat.lt_of_lt_of_eq (hRankSpec v).1 hLenEqN
  have hRankAt : ∀ i : Fin H.vertexCount,
      rankKahn (orderedVertexAt orderKahn sizeKahn i) = i.val := fun i => by
    obtain ⟨hv, hEq⟩ := hRankSpec (orderedVertexAt orderKahn sizeKahn i)
    rw [hOrdAt i] at hEq
    exact nodup_getElem_inj hNd1 hv (Nat.lt_of_lt_of_eq i.isLt hLenEqN.symm) hEq
  refine ⟨20 + kOuter + 1, orderKahn, sizeKahn, rankKahn, t, by omega,
    (hSetupSteps.append hStepsOuter).halts (hHalt t hpct), ?_, hOrdNodup, ?_, hRankAt, ?_, ?_, ?_, ?_,
    fun a ha => by rw [htFr a ha, hd10']⟩
  · apply hMeta.preserve htM ht0 ht1
    intro i hi22
    rw [htFr _ (Or.inr (Or.inl ⟨by
      unfold metaArrBase inArcIdArrBase inStartArrBase
        trigNextArrBase trigHeadArrBase topoRankArrBase
      omega, by unfold tempArrBase; omega⟩)), hd10']
  · intro v
    refine ⟨⟨rankKahn v, hRankLt v⟩, ?_⟩
    apply Fin.ext
    rw [hOrdAt]
    exact (hRankSpec v).2
  · intro i j hij
    rw [hRankAt i, hRankAt j]
    exact hij
  · intro u v hArc
    obtain ⟨hv, hEqV⟩ := hRankSpec v
    have hVFin : (⟨q1[rankKahn v]'hv, hBound1 _ (List.getElem_mem hv)⟩ : Vertex H) = v :=
      Fin.ext hEqV
    obtain ⟨j, hj, hjEq⟩ := hTopo1 hBound1 (rankKahn v) hv u (hVFin.symm ▸ hArc)
    have hjLt : j < q1.length := Nat.lt_trans hj hv
    rw [List.getElem?_eq_getElem hjLt, Option.some.injEq] at hjEq
    obtain ⟨hu, hEqU⟩ := hRankSpec u
    have hRankEq : rankKahn u = j := nodup_getElem_inj hNd1 hu hjLt (hEqU.trans hjEq.symm)
    omega
  · intro i
    have hiQ : i.val < q1.length := Nat.lt_of_lt_of_eq i.isLt hLenEqN.symm
    rw [hOrdAt i]
    exact htOrd i.val hiQ
  · intro v
    obtain ⟨hv, hEqV⟩ := hRankSpec v
    have htr := htTR (rankKahn v) hv
    rwa [hEqV] at htr

theorem run_kahnLoop {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (q0 : List Nat) (hqLen : q0.length ≤ H.vertexCount) (hqNd : q0.Nodup)
    (hqBound : ∀ x ∈ q0, x < H.vertexCount)
    (hqZero : ∀ x, x < H.vertexCount → (x ∈ q0 ↔ degIn H x = 0))
    (hCurMem : (s0.data[metaArrBase H.vertexCount H.arcCount r.out.tables.next + mIdxKCursor]?).map Fin.val =
      some q0.length)
    (hIndeg : ∀ v < H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v))
    (hOutPref : ∀ i ≤ H.vertexCount,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i))
    (hQMem : ∀ i (hi : i < q0.length),
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1 + i]?).map Fin.val =
        some (q0[i]'hi))
    (hOutArc : ∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u + j.val)]?).map Fin.val =
        some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt))) :
    ∃ steps : Nat, ∃ orderKahn : Array (Vertex H), ∃ sizeKahn : orderKahn.size = H.vertexCount,
      ∃ rankKahn : Vertex H → Nat, ∃ t : State DomL,
      steps ≤ 16 * H.vertexCount + 16 * H.arcCount + 25 ∧
      run (kahnLoopPhase (hi := hi) (hw := hw) h100).code input steps (Phase.initial s0) = some ⟨t, steps⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      orderKahn.toList.Nodup ∧
      (∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt orderKahn sizeKahn i = v) ∧
      (∀ i : Fin H.vertexCount, rankKahn (orderedVertexAt orderKahn sizeKahn i) = i.val) ∧
      (∀ i j : Fin H.vertexCount, i.val < j.val →
        rankKahn (orderedVertexAt orderKahn sizeKahn i) <
          rankKahn (orderedVertexAt orderKahn sizeKahn j)) ∧
      (∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v) ∧
      (∀ i : Fin H.vertexCount,
        (t.data[orderArrBase H.vertexCount r.out.tables.next + i.val]?).map Fin.val =
          some (orderedVertexAt orderKahn sizeKahn i).val) ∧
      (∀ v : Vertex H,
        (t.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
          some (rankKahn v)) ∧
      (∀ a, (a < orderArrBase H.vertexCount r.out.tables.next ∨
          (topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ a ∧
            a < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          (tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount ≤ a ∧
            a < tempArrBase H.vertexCount H.arcCount r.out.tables.next + 2 * H.vertexCount + 1) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 ≤ a) →
        t.data[a]? = s0.data[a]?) := by
  let ph := kahnLoopPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (kahnLoopInstrs (bits := bits) h100).length = 51 := by
    unfold kahnLoopInstrs kahnLoopSetupInstrs kahnLoopOuterInstrs kahnLoopInnerInstrs metaLoadInstrs
    rfl
  have hCodeSize : ph.code.size = 52 := by
    dsimp [ph, kahnLoopPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (kahnLoopInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hPlSetup := Placed_append_left (by unfold kahnLoopInstrs at hPlFull; exact hPlFull)
  have hPlLoops := Placed_append_right (by unfold kahnLoopInstrs at hPlFull; exact hPlFull)
  rw [show (kahnLoopSetupInstrs (bits := bits) h100).length = 20 by
    simp [kahnLoopSetupInstrs, metaLoadInstrs]] at hPlLoops
  have hPlOuter := Placed_append_left hPlLoops
  have hPlInner := Placed_append_right hPlLoops
  rw [show (kahnLoopOuterInstrs (bits := bits) h100).length = 15 by
    simp [kahnLoopOuterInstrs, metaLoadInstrs]] at hPlInner
  exact run_kahnLoop_aux h100 hIn hWork rankArc hPlSetup hPlOuter hPlInner (by omega)
    (fun t hpct => haltAt_mkHaltPhase (hi := hi) (hw := hw) (kahnLoopInstrs (bits := bits) h100) _
      (by rw [hpct, hCodeLen]) (input := input))
    s0 hMeta q0 hqLen hqNd hqBound hqZero hCurMem hIndeg hOutPref hQMem hOutArc

end KahnLoopPhase

section Stage2Pipeline

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

structure CsrKahnReady (s : State DomL) {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (nGlobal : Nat)
    (orderKahn : Array (Vertex H)) (sizeKahn : orderKahn.size = H.vertexCount)
    (rankKahn : Vertex H → Nat) : Prop where
  forest_ready : ForestReady s flat increasing covers rankArc r nGlobal
  order_nodup : orderKahn.toList.Nodup
  order_covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount, orderedVertexAt orderKahn sizeKahn i = v
  rank_at : ∀ i : Fin H.vertexCount, rankKahn (orderedVertexAt orderKahn sizeKahn i) = i.val
  rank_increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
    rankKahn (orderedVertexAt orderKahn sizeKahn i) <
      rankKahn (orderedVertexAt orderKahn sizeKahn j)
  rank_arc : ∀ u v : Vertex H, H.HasQuotientArc u v → rankKahn u < rankKahn v
  order_mem : ∀ i : Fin H.vertexCount,
    (s.data[orderArrBase H.vertexCount r.out.tables.next + i.val]?).map Fin.val =
      some (orderedVertexAt orderKahn sizeKahn i).val
  topoRank_mem : ∀ v : Vertex H,
    (s.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
      some (rankKahn v)
  inStart_mem : ∀ i ≤ H.vertexCount,
    (s.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i)
  inArcId_mem : ∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
    (s.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
      some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt))

def csrKahnPhases (h100 : 100 ≤ 2 ^ bits) : List (Phase DomL) :=
  [ csrZeroPhase (hi := hi) (hw := hw) h100
  , csrCountPhase (hi := hi) (hw := hw) h100
  , csrPrefixPhase (hi := hi) (hw := hw) h100
  , csrScatterPhase (hi := hi) (hw := hw) h100
  , kahnSeedPhase (hi := hi) (hw := hw) h100
  , kahnLoopPhase (hi := hi) (hw := hw) h100
  ]

theorem run_stage2 {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL)
    (hForest : ForestReady s0 flat increasing covers rankArc r nGlobal) :
    ∃ steps : Nat, ∃ orderKahn : Array (Vertex H), ∃ sizeKahn : orderKahn.size = H.vertexCount,
      ∃ rankKahn : Vertex H → Nat, ∃ t : State DomL,
      steps ≤ 75 * H.vertexCount + 55 * H.arcCount + 160 ∧
      PhaseChain input (csrKahnPhases (hi := hi) (hw := hw) h100) s0 t steps ∧
      CsrKahnReady t flat increasing covers rankArc r nGlobal orderKahn sizeKahn rankKahn ∧
      (∀ j, (j < orderArrBase H.vertexCount r.out.tables.next ∨
          (topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ j ∧
            j < inStartArrBase H.vertexCount r.out.tables.next)) →
        t.data[j]? = s0.data[j]?) := by
  have hBOrd : 19 * r.out.tables.next ≤ orderArrBase H.vertexCount r.out.tables.next := by
    unfold orderArrBase; omega
  have hBO : orderArrBase H.vertexCount r.out.tables.next =
      19 * r.out.tables.next + 6 * H.vertexCount := rfl
  have hBT : topoRankArrBase H.vertexCount r.out.tables.next =
      orderArrBase H.vertexCount r.out.tables.next + H.vertexCount := rfl
  have hBTH : trigHeadArrBase H.vertexCount r.out.tables.next =
      topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount := rfl
  have hBTN : trigNextArrBase H.vertexCount r.out.tables.next =
      trigHeadArrBase H.vertexCount r.out.tables.next + H.vertexCount := rfl
  have hBIS : inStartArrBase H.vertexCount r.out.tables.next =
      trigNextArrBase H.vertexCount r.out.tables.next + r.out.tables.next := rfl
  have hBIA : inArcIdArrBase H.vertexCount r.out.tables.next =
      inStartArrBase H.vertexCount r.out.tables.next + (H.vertexCount + 1) := rfl
  have hBTR : topoRankArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      inStartArrBase H.vertexCount r.out.tables.next := by omega
  have hBInS : orderArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤
      inStartArrBase H.vertexCount r.out.tables.next := by omega
  have hBMeta : inArcIdArrBase H.vertexCount r.out.tables.next + H.arcCount =
      metaArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hBTemp : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 =
      tempArrBase H.vertexCount H.arcCount r.out.tables.next := rfl
  have hBKC : mIdxKCursor = 22 := rfl
  have hSB : storedBase r.out.tables.next = r.out.tables.next := rfl
  obtain ⟨k1, s1, hk1, hR1, hM1, hInZ1, hTempZ1, hFr1⟩ :=
    run_csrZero h100 hIn hWork s0 hForest.meta_ready
  obtain ⟨k2, s2, hk2, hR2, hM2, hOutD2, hOutZ2, hInD2, hInZ2, hIndeg2, hFr2⟩ :=
    run_csrCount h100 hIn hWork s1 hM1 hInZ1 hTempZ1
  obtain ⟨k3, s3, hk3, hR3, hM3, hInPref3, hOutPref3, hFr3⟩ :=
    run_csrPrefix (_entryRank := entryRank) h100 hWork s2 hM2 hOutD2 hOutZ2 hInD2 hInZ2
  obtain ⟨k4, s4, hk4, hR4, hM4, hInPref4, hOutPref4, hOutArc4, hInArc4, hFr4⟩ :=
    run_csrScatter h100 hIn hWork s3 hM3 hInPref3 hOutPref3
  have hIndeg3 : ∀ v < H.vertexCount,
      (s3.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v) := fun v hv => by
    rw [hFr3 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hIndeg2 v hv
  have hIndeg4 : ∀ v < H.vertexCount,
      (s4.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v) := fun v hv => by
    rw [hFr4 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]
    exact hIndeg3 v hv
  obtain ⟨k5, q0, s5, hk5, hR5, hM5, hqLen5, hqNd5, hqBound5, hqZero5, hCur5, hQMem5, hFr5⟩ :=
    run_kahnSeed h100 hIn hWork s4 hM4 hIndeg4
  have hIndeg5 : ∀ v < H.vertexCount,
      (s5.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + v]?).map Fin.val =
        some (degIn H v) := fun v hv => by
    rw [hFr5 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hIndeg4 v hv
  have hOutPref5 : ∀ i ≤ H.vertexCount,
      (s5.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + H.vertexCount + i]?).map Fin.val =
        some (prefixOut H i) := fun i hi => by
    rw [hFr5 _ (Or.inr (Or.inl ⟨by omega, by omega⟩))]; exact hOutPref4 i hi
  have hOutArc5 : ∀ u < H.vertexCount, ∀ j : Fin (degOut H u),
      (s5.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * H.vertexCount + 1 +
          (prefixOut H u + j.val)]?).map Fin.val =
        some ((outArcsPrefix H H.arcCount u)[j.val]'(by rw [outArcsPrefix_length]; exact j.isLt)) := fun u hu j => by
    have hjLt := j.isLt
    have : prefixOut H u + degOut H u = prefixOut H (u + 1) := rfl
    have : prefixOut H (u + 1) ≤ prefixOut H H.vertexCount := prefixOut_mono H hu
    rw [prefixOut_vertexCount H] at this
    rw [hFr5 _ (Or.inr (Or.inr (by omega)))]; exact hOutArc4 u hu j
  obtain ⟨k6, orderKahn, sizeKahn, rankKahn, t, hk6, hR6, hM6, hNd6, hCov6, hRkAt6, hRkInc6, hRkArc6,
      hOrdMem6, hTRMem6, hFr6⟩ :=
    run_kahnLoop h100 hIn hWork rankArc s5 hM5 q0 hqLen5 hqNd5 hqBound5 hqZero5 hCur5
      hIndeg5 hOutPref5 hQMem5 hOutArc5
  have hPresPreInStart : ∀ j, j < inStartArrBase H.vertexCount r.out.tables.next →
      s4.data[j]? = s0.data[j]? := fun j hj => by
    rw [hFr4 j (Or.inl hj), hFr3 j (Or.inl hj), hFr2 j (Or.inl hj), hFr1 j (Or.inl hj)]
  have hPresPreOrd : ∀ j, j < orderArrBase H.vertexCount r.out.tables.next →
      t.data[j]? = s0.data[j]? := fun j hj => by
    rw [hFr6 j (Or.inl hj), hFr5 j (Or.inl (by omega)), hPresPreInStart j (by omega)]
  have hDepthT : ∀ u : Fin r.out.tables.next,
      (t.data[u.val]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.depthOf u.val) := fun u => by
    rw [hPresPreOrd u.val (by omega)]; exact hForest.depth_at u
  have hParentT : ∀ u : Fin r.out.tables.next,
      (t.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf u.val) := fun u => by
    rw [hPresPreOrd _ (by omega)]; exact hForest.parent_at u
  have hJumpT : ∀ u : Fin r.out.tables.next,
      (t.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.jumpOf u.val) := fun u => by
    rw [hPresPreOrd _ (by omega)]; exact hForest.jump_at u
  have hInStartT : ∀ i ≤ H.vertexCount,
      (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i) := fun i hi => by
    rw [hFr6 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)), hFr5 _ (Or.inl (by omega))]; exact hInPref4 i hi
  have hInArcT : ∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
      (t.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
        some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt)) := fun v hv j => by
    have hjLt := j.isLt
    have : prefixIn H v + degIn H v = prefixIn H (v + 1) := rfl
    have : prefixIn H (v + 1) ≤ prefixIn H H.vertexCount := prefixIn_mono H hv
    rw [prefixIn_vertexCount H] at this
    rw [hFr6 _ (Or.inr (Or.inl ⟨by omega, by omega⟩)), hFr5 _ (Or.inl (by omega))]; exact hInArc4 v hv j
  have hLargeN : 3 ≤ H.vertexCount := large
  refine ⟨k1 + (k2 + (k3 + (k4 + (k5 + (k6 + 0))))), orderKahn, sizeKahn, rankKahn, t,
    by omega,
    PhaseChain.cons hR1 (PhaseChain.cons hR2 (PhaseChain.cons hR3 (PhaseChain.cons hR4
      (PhaseChain.cons hR5 (PhaseChain.cons hR6 (PhaseChain.nil t)))))),
    ⟨⟨hM6, hDepthT, hParentT, hJumpT⟩, hNd6, hCov6, hRkAt6, hRkInc6, hRkArc6,
      hOrdMem6, hTRMem6, hInStartT, hInArcT⟩, fun j hj => ?_⟩
  rcases hj with h | ⟨h1, h2⟩
  · exact hPresPreOrd j h
  · rw [hFr6 j (Or.inr (Or.inl ⟨h1, by omega⟩)), hFr5 j (Or.inl (by omega)), hPresPreInStart j h2]

end Stage2Pipeline

end Stage2CsrKahn

/-! ### 7. Stage 3: `zeroPrior`, `seedStoredMaps`, `buildTrigger`, and `setupPhases` -/

section Stage3SeedTrigger

section Stage3Pipeline

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

structure Stage3Ready (s : State DomL) {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (nGlobal : Nat)
    (orderKahn : Array (Vertex H)) (sizeKahn : orderKahn.size = H.vertexCount)
    (rankKahn : Vertex H → Nat) (buckets : Nat → List Nat) : Prop where
  kahn_ready : CsrKahnReady s flat increasing covers rankArc r nGlobal orderKahn sizeKahn rankKahn
  prior_zero : ∀ y < H.vertexCount, ∀ i < 6,
    (s.data[priorBase r.out.tables.next + 6 * y + i]?).map Fin.val = some 0
  seed_maps : ∀ w < r.out.tables.next, ∀ i < 16,
    (s.data[storedBase r.out.tables.next + 18 * w + 2 + i]?).map Fin.val =
      some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0)
  buckets_spec : ∀ tr < H.vertexCount, (buckets tr).Nodup ∧ ∀ w ∈ buckets tr,
    w < r.out.tables.next ∧
    0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w ∧
    ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
      max (rankKahn P.fst) (rankKahn P.snd) = tr
  buckets_cover : ∀ w < r.out.tables.next,
    0 < (buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w →
    ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
      w ∈ buckets (max (rankKahn P.fst) (rankKahn P.snd))
  buckets_linked : ∀ tr < H.vertexCount, ∃ hd : Nat,
    (s.data[trigHeadArrBase H.vertexCount r.out.tables.next + tr]?).map Fin.val = some hd ∧
    ListLinked s.data (trigNextArrBase H.vertexCount r.out.tables.next) r.out.tables.next hd (buckets tr)

def stage3Phases (h100 : 100 ≤ 2 ^ bits) : List (Phase DomL) :=
  [ zeroPriorPhase (hi := hi) (hw := hw) h100
  , seedStoredMapsPhase (hi := hi) (hw := hw) h100
  , buildTriggerPhase (hi := hi) (hw := hw) h100
  ]

theorem run_stage3 {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    {orderKahn : Array (Vertex H)} {sizeKahn : orderKahn.size = H.vertexCount}
    {rankKahn : Vertex H → Nat}
    (s0 : State DomL)
    (hKahn : CsrKahnReady s0 flat increasing covers rankArc r nGlobal orderKahn sizeKahn rankKahn) :
    ∃ steps : Nat, ∃ buckets : Nat → List Nat, ∃ t : State DomL,
      steps ≤ 105 * H.vertexCount + 125 ∧
      PhaseChain input (stage3Phases (hi := hi) (hw := hw) h100) s0 t steps ∧
      Stage3Ready t flat increasing covers rankArc r nGlobal orderKahn sizeKahn rankKahn buckets ∧
      (∀ j, (j < storedBase r.out.tables.next ∨
          (∃ w < r.out.tables.next,
            j = storedBase r.out.tables.next + 18 * w ∨
            j = storedBase r.out.tables.next + 18 * w + 1) ∨
          (orderArrBase H.vertexCount r.out.tables.next ≤ j ∧
            j < trigHeadArrBase H.vertexCount r.out.tables.next) ∨
          inStartArrBase H.vertexCount r.out.tables.next ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hRkLt : ∀ v : Vertex H, rankKahn v < H.vertexCount := fun v => by
    obtain ⟨i, hiEq⟩ := hKahn.order_covers v
    rw [← hiEq, hKahn.rank_at i]; exact i.isLt
  obtain ⟨k1, s1, hk1, hR1, hM1, hPrior1, hFr1⟩ :=
    run_zeroPrior h100 hIn hWork s0 hKahn.forest_ready.meta_ready
  obtain ⟨k2, s2, hk2, hR2, hM2, hMaps2, hFr2⟩ :=
    run_seedStoredMaps h100 hIn hWork s1 hM1
  have hPar2 : ∀ w : Fin r.out.tables.next,
      (s2.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w.val) := fun w => by
    have := w.isLt
    rw [hFr2 _ (Or.inr (Or.inr ⟨w.val, w.isLt, Or.inl rfl⟩)),
      hFr1 _ (Or.inl (by unfold priorBase storedBase; omega))]
    exact hKahn.forest_ready.parent_at w
  have hTR2 : ∀ v : Vertex H,
      (s2.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
        some (rankKahn v) := fun v => by
    rw [hFr2 _ (Or.inr (Or.inl (by unfold priorBase topoRankArrBase orderArrBase; omega))),
      hFr1 _ (Or.inr (by unfold topoRankArrBase; omega))]
    exact hKahn.topoRank_mem v
  obtain ⟨k3, buckets, t, hk3, hR3, hM3, hB3, hCov3, hLk3, hFr3⟩ :=
    run_buildTrigger flat increasing covers rankArc h100 hIn hWork hw rankKahn hRkLt s2 hM2 hPar2 hTR2
  have hPres : ∀ j, (j < storedBase r.out.tables.next ∨
      (∃ w < r.out.tables.next,
        j = storedBase r.out.tables.next + 18 * w ∨ j = storedBase r.out.tables.next + 18 * w + 1) ∨
      (orderArrBase H.vertexCount r.out.tables.next ≤ j ∧
        j < trigHeadArrBase H.vertexCount r.out.tables.next) ∨
      inStartArrBase H.vertexCount r.out.tables.next ≤ j) →
      t.data[j]? = s0.data[j]? := fun j hj => by
    rcases hj with h | h | ⟨h1, h2⟩ | h
    · rw [hFr3 j (Or.inl (by unfold trigHeadArrBase topoRankArrBase orderArrBase storedBase at *; omega)),
        hFr2 j (Or.inl h), hFr1 j (Or.inl (by unfold priorBase storedBase at *; omega))]
    · rcases h with ⟨w, hw, rfl | rfl⟩
      · rw [hFr3 _ (Or.inl (by unfold trigHeadArrBase topoRankArrBase orderArrBase storedBase; omega)),
          hFr2 _ (Or.inr (Or.inr ⟨w, hw, Or.inl rfl⟩)),
          hFr1 _ (Or.inl (by unfold priorBase storedBase; omega))]
      · rw [hFr3 _ (Or.inl (by unfold trigHeadArrBase topoRankArrBase orderArrBase storedBase; omega)),
          hFr2 _ (Or.inr (Or.inr ⟨w, hw, Or.inr rfl⟩)),
          hFr1 _ (Or.inl (by unfold priorBase storedBase; omega))]
    · rw [hFr3 j (Or.inl h2),
        hFr2 j (Or.inr (Or.inl (by simp only [orderArrBase, priorBase] at h1 ⊢; omega))),
        hFr1 j (Or.inr h1)]
    · have hOrder : orderArrBase H.vertexCount r.out.tables.next ≤
          inStartArrBase H.vertexCount r.out.tables.next :=
        Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans (Nat.le_add_right _ _)
          (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _)))
      have hPrior : priorBase r.out.tables.next ≤ orderArrBase H.vertexCount r.out.tables.next :=
        Nat.le_add_right _ _
      have hOrdJ := Nat.le_trans hOrder h
      rw [hFr3 j (Or.inr h), hFr2 j (Or.inr (Or.inl (Nat.le_trans hPrior hOrdJ))),
        hFr1 j (Or.inr hOrdJ)]
  have hDepthT : ∀ u : Fin r.out.tables.next,
      (t.data[u.val]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.depthOf u.val) := fun u => by
    rw [hPres u.val (Or.inl (by unfold storedBase; exact u.isLt))]; exact hKahn.forest_ready.depth_at u
  have hParentT : ∀ u : Fin r.out.tables.next,
      (t.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf u.val) := fun u => by
    rw [hPres _ (Or.inr (Or.inl ⟨u.val, u.isLt, Or.inl rfl⟩))]; exact hKahn.forest_ready.parent_at u
  have hJumpT : ∀ u : Fin r.out.tables.next,
      (t.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.jumpOf u.val) := fun u => by
    rw [hPres _ (Or.inr (Or.inl ⟨u.val, u.isLt, Or.inr rfl⟩))]; exact hKahn.forest_ready.jump_at u
  have hOrdT : ∀ i : Fin H.vertexCount,
      (t.data[orderArrBase H.vertexCount r.out.tables.next + i.val]?).map Fin.val =
        some (orderedVertexAt orderKahn sizeKahn i).val := fun i => by
    have := i.isLt
    rw [hPres _ (Or.inr (Or.inr (Or.inl ⟨by omega, by unfold trigHeadArrBase topoRankArrBase; omega⟩)))]
    exact hKahn.order_mem i
  have hTRT : ∀ v : Vertex H,
      (t.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
        some (rankKahn v) := fun v => by
    rw [hPres _ (Or.inr (Or.inr (Or.inl ⟨by unfold topoRankArrBase; omega, by unfold trigHeadArrBase; exact Nat.add_lt_add_left v.isLt _⟩)))]
    exact hKahn.topoRank_mem v
  have hInST : ∀ i ≤ H.vertexCount,
      (t.data[inStartArrBase H.vertexCount r.out.tables.next + i]?).map Fin.val = some (prefixIn H i) := fun i hi => by
    rw [hPres _ (Or.inr (Or.inr (Or.inr (by omega))))]; exact hKahn.inStart_mem i hi
  have hInAT : ∀ v < H.vertexCount, ∀ j : Fin (degIn H v),
      (t.data[inArcIdArrBase H.vertexCount r.out.tables.next + (prefixIn H v + j.val)]?).map Fin.val =
        some ((inArcsPrefix H H.arcCount v)[j.val]'(by rw [inArcsPrefix_length]; exact j.isLt)) := fun v hv j => by
    rw [hPres _ (Or.inr (Or.inr (Or.inr (by unfold inArcIdArrBase; omega))))]; exact hKahn.inArcId_mem v hv j
  have hPriorT : ∀ y < H.vertexCount, ∀ i < 6,
      (t.data[priorBase r.out.tables.next + 6 * y + i]?).map Fin.val = some 0 := fun y hy i hi => by
    rw [hFr3 _ (Or.inl (by unfold trigHeadArrBase topoRankArrBase orderArrBase priorBase; omega)),
      hFr2 _ (Or.inr (Or.inl (by omega)))]
    exact hPrior1 y hy i hi
  have hMapsT : ∀ w < r.out.tables.next, ∀ i < 16,
      (t.data[storedBase r.out.tables.next + 18 * w + 2 + i]?).map Fin.val =
        some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0) := fun w hw i hi => by
    rw [hFr3 _ (Or.inl (by unfold trigHeadArrBase topoRankArrBase orderArrBase storedBase; omega))]
    exact hMaps2 w hw i hi
  refine ⟨k1 + (k2 + (k3 + 0)), buckets, t, by omega,
    PhaseChain.cons hR1 (PhaseChain.cons hR2 (PhaseChain.cons hR3 (PhaseChain.nil t))),
    ⟨⟨⟨hM3, hDepthT, hParentT, hJumpT⟩, hKahn.order_nodup, hKahn.order_covers,
      hKahn.rank_at, hKahn.rank_increasing, hKahn.rank_arc, hOrdT, hTRT, hInST, hInAT⟩,
      hPriorT, hMapsT, hB3, hCov3, hLk3⟩, hPres⟩

def setupPhases (h100 : 100 ≤ 2 ^ bits) : List (Phase DomL) :=
  [initMetaPhase (hi := hi) (hw := hw) h100] ++
    stage1Phases (hi := hi) (hw := hw) h100 ++
    csrKahnPhases (hi := hi) (hw := hw) h100 ++
    stage3Phases (hi := hi) (hw := hw) h100

theorem run_setupPhases {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    (flat : H.IsFlat)
    (increasing : ∀ i j : Fin H.vertexCount, i.val < j.val →
      rank (orderedVertexAt data size_data i) < rank (orderedVertexAt data size_data j))
    (covers : ∀ v : Vertex H, ∃ i : Fin H.vertexCount,
      orderedVertexAt data size_data i = v)
    (rankArc : ∀ u v : Vertex H, H.HasQuotientArc u v → rank u < rank v)
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (h100 : 100 ≤ 2 ^ bits)
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap)
    (s0 : State DomL) :
    ∃ steps : Nat, ∃ orderKahn : Array (Vertex H), ∃ sizeKahn : orderKahn.size = H.vertexCount,
      ∃ rankKahn : Vertex H → Nat, ∃ buckets : Nat → List Nat, ∃ t : State DomL,
      steps ≤ 290 * H.vertexCount + 55 * H.arcCount + 500 ∧
      PhaseChain input (setupPhases (hi := hi) (hw := hw) h100) s0 t steps ∧
      Stage3Ready t flat increasing covers rankArc r nGlobal orderKahn sizeKahn rankKahn buckets := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hk0 : (initMetaInstrs (bits := bits) h100).length + 1 = 80 := by
    unfold initMetaInstrs
    have hLA : (initMetaPartA (bits := bits) h100).length = 8 := rfl
    have hLM18 : (mul18Instrs (bits := bits) reg9 reg8 reg6).length = 5 := rfl
    have hLM6 : (mul6Instrs (bits := bits) reg10 reg4).length = 3 := rfl
    have hLB : (initMetaPartB (bits := bits)).length = 9 := rfl
    have hLS1 : (storeSeqInstrs (bits := bits) reg3 reg1 initMetaSeq1Vars).length = 25 := rfl
    have hLC : (initMetaPartC (bits := bits) h100).length = 13 := rfl
    have hLS2 : (storeSeqInstrs (bits := bits) reg3 reg1 initMetaSeq2Vars).length = 15 := rfl
    simp only [List.length_append, hLA, hLM18, List.length_singleton, hLM6, hLB, hLS1, hLC, hLS2]
  obtain ⟨s1, hR0, hM0, _⟩ := run_initMeta h100 hIn hWork s0
  obtain ⟨k1, s2, hk1, hC1, hF1, _⟩ := run_stage1 flat increasing covers rankArc h100 hIn hWork s1 hM0
  obtain ⟨k2, orderKahn, sizeKahn, rankKahn, s3, hk2, hC2, hK2, _⟩ :=
    run_stage2 flat increasing covers rankArc h100 hIn hWork s2 hF1
  obtain ⟨k3, buckets, t, hk3, hC3, hS3, _⟩ :=
    run_stage3 flat increasing covers rankArc h100 hIn hWork s3 hK2
  have hChain : PhaseChain input (setupPhases (hi := hi) (hw := hw) h100) s0 t
      (((initMetaInstrs (bits := bits) h100).length + 1 + 0) + k1 + k2 + k3) := by
    unfold setupPhases
    exact (((PhaseChain.cons hR0 (PhaseChain.nil s1)).append hC1).append hC2).append hC3
  refine ⟨((initMetaInstrs (bits := bits) h100).length + 1 + 0) + k1 + k2 + k3,
    orderKahn, sizeKahn, rankKahn, buckets, t, ?_, hChain, hS3⟩
  rw [Nat.add_zero, hk0]
  have hBudget1 : k1 ≤ 110 * r.out.tables.next + 25 := hk1
  have hBudget2 : k2 ≤ 75 * H.vertexCount + 55 * H.arcCount + 160 := hk2
  have hBudget3 : k3 ≤ 105 * H.vertexCount + 125 := hk3
  clear hk1 hk2 hk3
  omega

end Stage3Pipeline

end Stage3SeedTrigger


end PaperB.RamProgram.ExitSummaryBuild
