module

public import PaperB.RamExitSummaryCsrScatter

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
EX5.1 / EX5.2 Word-RAM exit-summary Stage 1 Part B / DFS forest reconstruction (`PaperB/RamExitSummaryStage1.lean`).

Contains:
1. Input/output memory layout (`exitWorkCap n m ≤ 48 * (n + m + 1)`, metadata slots,
   `ExitBuildInput`).
2. Mathematical specification bridges:
   - DFS `(fEntry, fStop)` stack reconstruction matching `B.F.parentOf`,
     `B.F.depthOf`, and `B.F.jumpOf`;
   - Topological trigger ordering (`triggerRank parent < triggerRank child` and
     `triggerRank owner < topoRank y`);
   - `Occupied` / `DecodedOccupied` / `LiveStoreOK` / `RouteSlotEdges` bridges.
3. 15-register Word-RAM execution helpers, `PhasesExec`, `linkNonEmpty`,
   `initMetaPhase`, Stage 1 (`forestReconPhase`), Stage 2 (`csrKahnPhase`),
   Stage 3 (`seedAndTriggerPhase`), and reusable Stage 4 slices (`intervalJoin`,
   `mapEval`, `eval15`, `mapCompose`, `buildOneSlot`).
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

section Stage1ForestRecon

section Stage1PartBInstrs

variable {bits : Nat}

def dfsSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg6 mIdxNH (by change 2 < 2 ^ bits; omega) ++
  [ .mov reg3 reg0
  , .mov reg4 reg0
  ]

def dfsPopLoopInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  [ .branchLt reg0 reg4 7 18 ] ++
  (metaLoadInstrs reg6 reg7 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  [ .add reg6 reg6 reg2
  , .add reg6 reg6 reg2
  , .add reg6 reg6 reg4
  , .sub reg6 reg6 reg1
  , .loadData reg7 reg6
  , .branchLt reg3 reg7 18 16
  , .sub reg4 reg4 reg1
  , .goto 6
  ])

def dfsDecodeUInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg5 reg6 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  [ .add reg6 reg5 reg3
  , .loadData reg5 reg6
  , .branchLt reg0 reg4 28 24
  ]

def dfsIsEmptyInstrs : List (Instr bits 15) :=
  [ .storeData reg5 reg0
  , .mov reg8 reg5
  , .mov reg9 reg5
  , .goto 66
  ]

def dfsNonEmptyAInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg7 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  ([ .add reg6 reg6 reg2
   , .add reg6 reg6 reg4
   , .sub reg6 reg6 reg1
   , .loadData reg8 reg6
   , .loadData reg6 reg8
   , .add reg7 reg6 reg1
   , .storeData reg5 reg7
   ] ++
  (metaLoadInstrs reg10 reg7 mIdxStoredBase (by change 4 < 2 ^ bits; omega) ++
  (mul18Instrs reg11 reg7 reg8 ++
  [ .add reg11 reg10 reg11
  , .add reg11 reg11 reg1
  , .loadData reg12 reg11
  , .loadData reg7 reg12
  , .sub reg7 reg6 reg7
  , .branchLt reg0 reg7 52 65
  ])))

def dfsCheckLen2Instrs : List (Instr bits 15) :=
  mul18Instrs reg11 reg6 reg12 ++
  [ .add reg11 reg10 reg11
  , .add reg11 reg11 reg1
  , .loadData reg9 reg11
  , .loadData reg6 reg12
  , .loadData reg11 reg9
  , .sub reg6 reg6 reg11
  , .branchLt reg7 reg6 65 64
  , .branchLt reg6 reg7 65 66
  ]

def dfsUsePInstrs : List (Instr bits 15) :=
  [ .mov reg9 reg8 ]

def dfsWritePJInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg10 reg7 mIdxStoredBase (by change 4 < 2 ^ bits; omega) ++
  (mul18Instrs reg11 reg7 reg5 ++
  ([ .add reg10 reg10 reg11
   , .storeData reg10 reg8
   , .add reg10 reg10 reg1
   , .storeData reg10 reg9
   ] ++
  (metaLoadInstrs reg6 reg7 mIdxTempBase (by change 13 < 2 ^ bits; omega) ++
  ([ .add reg6 reg6 reg2
   , .add reg7 reg6 reg4
   , .storeData reg7 reg5
   ] ++
  (metaLoadInstrs reg8 reg7 mIdxFStopInBase (by change 18 < 2 ^ bits; omega) ++
  [ .add reg8 reg8 reg5
  , .loadInput reg8 reg8
  , .add reg6 reg6 reg2
  , .add reg6 reg6 reg4
  , .storeData reg6 reg8
  , .add reg4 reg4 reg1
  , .add reg3 reg3 reg1
  , .goto 5
  ])))))

def dfsStackInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  dfsSetupInstrs h100 ++
  ([ .branchLt reg3 reg2 6 95 ] ++
  (dfsPopLoopInstrs h100 ++
  (dfsDecodeUInstrs h100 ++
  (dfsIsEmptyInstrs ++
  (dfsNonEmptyAInstrs h100 ++
  (dfsCheckLen2Instrs ++
  (dfsUsePInstrs ++
  dfsWritePJInstrs h100)))))))

end Stage1PartBInstrs

section Stage1PartBPhases

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def dfsStackPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (dfsStackInstrs (bits := bits) h100)
    (by
      simp [dfsStackInstrs, dfsSetupInstrs, dfsPopLoopInstrs, dfsDecodeUInstrs,
        dfsIsEmptyInstrs, dfsNonEmptyAInstrs, dfsCheckLen2Instrs, dfsUsePInstrs,
        dfsWritePJInstrs, metaLoadInstrs, mul18Instrs, nonHalt])

structure ForestReady {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (s : State (layout bits inputCap workCap hi hw))
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
    (r : PaperB.OrderedReaderResult p data size_data rank large)
    (nGlobal : Nat) : Prop where
  meta_ready : MetaReady s H.vertexCount H.arcCount r.out.tables.next nGlobal
  depth_at : ∀ u : Fin r.out.tables.next,
    (s.data[u.val]?).map Fin.val =
      some ((buildActualSweepBundle H flat increasing covers rankArc r).F.depthOf u.val)
  parent_at : ∀ u : Fin r.out.tables.next,
    (s.data[storedBase r.out.tables.next + 18 * u.val]?).map Fin.val =
      some ((buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf u.val)
  jump_at : ∀ u : Fin r.out.tables.next,
    (s.data[storedBase r.out.tables.next + 18 * u.val + 1]?).map Fin.val =
      some ((buildActualSweepBundle H flat increasing covers rankArc r).F.jumpOf u.val)

private theorem dfsSetup_spec {code : Program DomL} {input : Input DomL}
    (h100 : 100 ≤ 2 ^ bits) {n m N nGlobal : Nat}
    (hPl : Placed code 0 (dfsSetupInstrs (bits := bits) h100))
    (hSz : 5 < code.size)
    (hTempFit : tempArrBase n m N ≤ 2 ^ bits)
    (st : State DomL) (hpc : st.pc = 0)
    (hMeta : MetaReady st n m N nGlobal) :
    ∃ t : State DomL, Steps code input 5 st t ∧ t.pc = 5 ∧ t.data = st.data ∧
      (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧
      (reg t rMeta).val = metaArrBase n m N ∧ (reg t reg2).val = N ∧
      (reg t reg3).val = 0 ∧ (reg t reg4).val = 0 := by
  have hPl1 : Placed code 0 (metaLoadInstrs reg2 reg6 mIdxNH (by change 2 < 2 ^ bits; omega)) :=
    Placed_append_left hPl
  have hR1 := Placed_append_right hPl
  change Placed code 3 [Instr.mov reg3 reg0, Instr.mov reg4 reg0] at hR1
  have hMetaBits : metaArrBase n m N + mIdxNH < 2 ^ bits := by
    have : tempArrBase n m N = metaArrBase n m N + 48 := rfl
    change metaArrBase n m N + 2 < 2 ^ bits; omega
  obtain ⟨s1, hs1, hpc1, hd1, hr2_1, hro1⟩ := run_metaLoad_slice
    (dst := reg2) (tmp := reg6) (off := mIdxNH) (hOff := by change 2 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc hMeta.rMeta_eq hMetaBits hMeta.meta_NH
  obtain ⟨s2, hs2, hpc2, hr3d, hr3o, hd2⟩ := step_mov_at (input := input)
    (by rw [hpc1]; exact hR1 0 _ rfl) (by rw [hpc1]; omega)
  obtain ⟨s3, hs3, hpc3, hr4d, hr4o, hd3⟩ := step_mov_at (input := input)
    (by rw [hpc2, hpc1]; exact hR1 1 _ rfl) (by rw [hpc2, hpc1]; omega)
  refine ⟨s3, hs1.append (Steps.cons hs2 (steps_1_of_step hs3)),
    by rw [hpc3, hpc2, hpc1], by rw [hd3, hd2, hd1], ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr4o reg0 (by intro h; cases h), hr3o reg0 (by intro h; cases h),
      hro1 reg0 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r0_zero
  · rw [hr4o reg1 (by intro h; cases h), hr3o reg1 (by intro h; cases h),
      hro1 reg1 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r1_one
  · rw [hr4o rMeta (by intro h; cases h), hr3o rMeta (by intro h; cases h),
      hro1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  · rw [hr4o reg2 (by intro h; cases h), hr3o reg2 (by intro h; cases h), hr2_1]
  · rw [hr4o reg3 (by intro h; cases h), hr3d,
      hro1 reg0 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r0_zero
  · rw [hr4d, hr3o reg0 (by intro h; cases h),
      hro1 reg0 (by intro h; cases h) (by intro h; cases h)]; exact hMeta.r0_zero

private theorem dfsPopLoop_spec {code : Program DomL} {input : Input DomL}
    (h100 : 100 ≤ 2 ^ bits) {n m N t : Nat}
    (entryF stopF : Fin N → Nat)
    (hPl : Placed code 6 (dfsPopLoopInstrs (bits := bits) h100))
    (hSz : 18 < code.size)
    (hDataFit : tempArrBase n m N + 3 * N ≤ 2 ^ bits)
    (stk0 : List (Fin N))
    (hStopDec : ∀ i j (hi : i < stk0.length) (hj : j < stk0.length), i ≤ j →
      stopF (stk0[j]'hj) ≤ stopF (stk0[i]'hi))
    (hStkMem : ∀ w : Fin N, w ∈ stk0 ↔ entryF w < t ∧ t ≤ stopF w) :
    ∀ (sp : Nat) (st : State DomL) (hSpLe : sp ≤ stk0.length), sp < N →
      st.pc = 6 →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase n m N →
      (reg st reg2).val = N → (reg st reg3).val = t → (reg st reg4).val = sp →
      (st.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N) →
      (∀ i (hi : i < sp),
        (st.data[tempArrBase n m N + 2 * N + i]?).map Fin.val =
          some (stopF (stk0[i]'(Nat.lt_of_lt_of_le hi hSpLe)))) →
      (∀ w : Fin N, entryF w < t ∧ t < stopF w → w ∈ stk0.take sp) →
      ∃ sp' steps' out, sp' ≤ sp ∧ steps' ≤ 12 * (sp - sp') + 10 ∧
        Steps code input steps' st out ∧ out.pc = 18 ∧ out.data = st.data ∧
        (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
        (reg out rMeta).val = metaArrBase n m N ∧
        (reg out reg2).val = N ∧ (reg out reg3).val = t ∧ (reg out reg4).val = sp' ∧
        (∀ w : Fin N, w ∈ stk0.take sp' ↔ entryF w < t ∧ t < stopF w) := by
  intro sp
  induction sp with
  | zero =>
    intro st hSpLe _ hpc hr0 hr1 hrm hr2 hr3 hr4 _ _ hRem
    have hBrAt : code[st.pc]? = some (.branchLt reg0 reg4 7 18) := by rw [hpc]; exact hPl 0 _ rfl
    obtain ⟨out, hStep, hOutPc, hOutR, hOutD⟩ := step_branchLt_at (input := input) hBrAt
      (by split <;> omega)
    have hFalse : ¬ (reg st reg0).val < (reg st reg4).val := by rw [hr0, hr4]; omega
    rw [ite_eq_right hFalse] at hOutPc
    have hEqR : ∀ r : Fin 15, reg out r = reg st r := fun r => by
      rcases out with ⟨or', _, _, _, _⟩; rcases st with ⟨sr, _, _, _, _⟩
      dsimp only at hOutR; subst or'; rfl
    refine ⟨0, 1, out, Nat.le_refl 0, by omega, steps_1_of_step hStep, hOutPc, hOutD,
      by rw [hEqR]; exact hr0, by rw [hEqR]; exact hr1, by rw [hEqR]; exact hrm,
      by rw [hEqR]; exact hr2, by rw [hEqR]; exact hr3, by rw [hEqR]; exact hr4,
      fun w => ⟨fun hm => by simp at hm, fun hw => hRem w hw⟩⟩
  | succ sp ih =>
    intro st hSpLe hSpLtN hpc hr0 hr1 hrm hr2 hr3 hr4 hMetaT hStops hRem
    have hBrAt : code[st.pc]? = some (.branchLt reg0 reg4 7 18) := by rw [hpc]; exact hPl 0 _ rfl
    obtain ⟨s1, hs1, hpc1, hr1R, hd1⟩ := step_branchLt_at (input := input) hBrAt
      (by split <;> omega)
    have hTrue : (reg st reg0).val < (reg st reg4).val := by rw [hr0, hr4]; omega
    rw [ite_eq_left hTrue] at hpc1
    have h1EqR : ∀ r : Fin 15, reg s1 r = reg st r := fun r => by
      rcases s1 with ⟨ar, _, _, _, _⟩; rcases st with ⟨sr, _, _, _, _⟩
      dsimp only at hr1R; subst ar; rfl
    have hMetaBits : metaArrBase n m N + mIdxTempBase < 2 ^ bits := by
      have : tempArrBase n m N = metaArrBase n m N + 48 := rfl
      change metaArrBase n m N + 13 < 2 ^ bits; omega
    have hR0 := Placed_append_right hPl
    rw [show ([Instr.branchLt reg0 reg4 7 18] : List (Instr bits 15)).length = 1 by rfl] at hR0
    have hPlLoad := Placed_append_left hR0
    have hR2 := Placed_append_right hR0
    rw [show (metaLoadInstrs (bits := bits) reg6 reg7 mIdxTempBase _).length = 3 by rfl] at hR2
    obtain ⟨s4, hs4, hpc4, hd4, h6_4, hro4⟩ := run_metaLoad_slice
      (dst := reg6) (tmp := reg7) (off := mIdxTempBase) (hOff := by change 13 < 2 ^ bits; omega)
      (by intro h; cases h) (by intro h; cases h)
      hPlLoad (by omega) hpc1 (by rw [h1EqR]; exact hrm) hMetaBits (by rw [hd1]; exact hMetaT)
    obtain ⟨s5, hs5, hpc5, hr6_5, hro5, hd5⟩ := step_add_at (input := input)
      (by rw [hpc4]; exact hR2 0 _ rfl) (by rw [hpc4]; omega)
    obtain ⟨s6, hs6, hpc6, hr6_6, hro6, hd6⟩ := step_add_at (input := input)
      (by rw [hpc5, hpc4]; exact hR2 1 _ rfl) (by rw [hpc5, hpc4]; omega)
    obtain ⟨s7, hs7, hpc7, hr6_7, hro7, hd7⟩ := step_add_at (input := input)
      (by rw [hpc6, hpc5, hpc4]; exact hR2 2 _ rfl) (by rw [hpc6, hpc5, hpc4]; omega)
    obtain ⟨s8, hs8, hpc8, hr6_8, hro8, hd8⟩ := step_sub_at (input := input)
      (by rw [hpc7, hpc6, hpc5, hpc4]; exact hR2 3 _ rfl) (by rw [hpc7, hpc6, hpc5, hpc4]; omega)
    have h4Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → reg s4 r = reg st r := fun r h6 h7 => by
      rw [hro4 r h6 h7, h1EqR]
    have h8Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → reg s8 r = reg st r := fun r h6 h7 => by
      rw [hro8 r h6, hro7 r h6, hro6 r h6, hro5 r h6, h4Preserve r h6 h7]
    have hspLtStk : sp < stk0.length := by omega
    have hIdx8 : (reg s8 reg6).val = tempArrBase n m N + 2 * N + sp := by
      have h5V : (reg s5 reg6).val = tempArrBase n m N + N := by
        have hr2_4 : (reg s4 reg2).val = N := by
          rw [h4Preserve reg2 (by intro h; cases h) (by intro h; cases h), hr2]
        rw [hr6_5, add_no_wrap _ _ (by rw [h6_4, hr2_4]; omega), h6_4, hr2_4]
      have h6V : (reg s6 reg6).val = tempArrBase n m N + 2 * N := by
        have hr2_5 : (reg s5 reg2).val = N := by
          rw [hro5 reg2 (by intro h; cases h), h4Preserve reg2 (by intro h; cases h) (by intro h; cases h), hr2]
        rw [hr6_6, add_no_wrap _ _ (by rw [h5V, hr2_5]; omega), h5V, hr2_5]; omega
      have h7V : (reg s7 reg6).val = tempArrBase n m N + 2 * N + (sp + 1) := by
        have hr4_6 : (reg s6 reg4).val = sp + 1 := by
          rw [hro6 reg4 (by intro h; cases h), hro5 reg4 (by intro h; cases h),
            h4Preserve reg4 (by intro h; cases h) (by intro h; cases h), hr4]
        rw [hr6_7, add_no_wrap _ _ (by rw [h6V, hr4_6]; omega), h6V, hr4_6]
      have hr1_7 : (reg s7 reg1).val = 1 := by
        rw [hro7 reg1 (by intro h; cases h), hro6 reg1 (by intro h; cases h), hro5 reg1 (by intro h; cases h),
          h4Preserve reg1 (by intro h; cases h) (by intro h; cases h), hr1]
      rw [hr6_8, sub_no_wrap _ _ (by rw [hr1_7, h7V]; omega), h7V, hr1_7]; omega
    have hTopMem := hStops sp (Nat.lt_succ_self sp)
    obtain ⟨wTop, hwTop, hwTopVal⟩ := Option.map_eq_some_iff.mp hTopMem
    have hwTopS8 : s8.data[(reg s8 reg6).val]? = some wTop := by
      rw [hd8, hd7, hd6, hd5, hd4, hd1, hIdx8]; exact hwTop
    obtain ⟨s9, hs9, hpc9, hr7_9, hro9, hd9⟩ := step_loadData_at (input := input)
      (by rw [hpc8, hpc7, hpc6, hpc5, hpc4]; exact hR2 4 _ rfl)
      (by rw [hpc8, hpc7, hpc6, hpc5, hpc4]; omega) hwTopS8
    have h9_7 : (reg s9 reg7).val = stopF (stk0[sp]'hspLtStk) := by rw [hr7_9, hwTopVal]
    have h9_3 : (reg s9 reg3).val = t := by
      rw [hro9 reg3 (by intro h; cases h), h8Preserve reg3 (by intro h; cases h) (by intro h; cases h), hr3]
    obtain ⟨s10, hs10, hpc10, hr10R, hd10⟩ := step_branchLt_at (input := input)
      (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4]; exact hR2 5 _ rfl) (by split <;> omega)
    have hPreSteps : Steps code input 10 st s10 :=
      Steps.cons hs1 (hs4.append (Steps.cons hs5 (Steps.cons hs6
        (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (steps_1_of_step hs10)))))))
    have h10EqR : ∀ r : Fin 15, reg s10 r = reg s9 r := fun r => by
      rcases s10 with ⟨ar, _, _, _, _⟩; rcases s9 with ⟨br, _, _, _, _⟩
      dsimp only at hr10R; subst ar; rfl
    have h10Data : s10.data = st.data := by rw [hd10, hd9, hd8, hd7, hd6, hd5, hd4, hd1]
    have h10Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → reg s10 r = reg st r := fun r h6 h7 => by
      rw [h10EqR, hro9 r h7, h8Preserve r h6 h7]
    by_cases hCmp : t < stopF (stk0[sp]'hspLtStk)
    · rw [ite_eq_left (by rw [h9_3, h9_7]; exact hCmp)] at hpc10
      refine ⟨sp + 1, 10, s10, Nat.le_refl _, by omega, hPreSteps, hpc10, h10Data,
        by rw [h10Preserve reg0 (by intro h; cases h) (by intro h; cases h), hr0],
        by rw [h10Preserve reg1 (by intro h; cases h) (by intro h; cases h), hr1],
        by rw [h10Preserve rMeta (by intro h; cases h) (by intro h; cases h), hrm],
        by rw [h10Preserve reg2 (by intro h; cases h) (by intro h; cases h), hr2],
        by rw [h10Preserve reg3 (by intro h; cases h) (by intro h; cases h), hr3],
        by rw [h10Preserve reg4 (by intro h; cases h) (by intro h; cases h), hr4],
        fun w => ⟨fun hw => ?_, fun hw => hRem w hw⟩⟩
      obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hw
      simp only [List.length_take] at hj
      have hjLtSp1 : j < sp + 1 := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
      have hjLtStk : j < stk0.length := Nat.lt_of_lt_of_le hjLtSp1 hSpLe
      rw [List.getElem_take] at hjEq
      have hjMem : stk0[j]'hjLtStk ∈ stk0 := List.getElem_mem hjLtStk
      have hEnt := (hStkMem _).mp hjMem |>.1
      have hDec := hStopDec j sp hjLtStk hspLtStk (by omega)
      subst hjEq
      exact ⟨hEnt, Nat.lt_of_lt_of_le hCmp hDec⟩
    · rw [ite_eq_right (by rw [h9_3, h9_7]; exact hCmp)] at hpc10
      obtain ⟨s11, hs11, hpc11, hr4_11, hro11, hd11⟩ := step_sub_at (input := input)
        (by rw [hpc10]; exact hR2 6 _ rfl) (by rw [hpc10]; omega)
      obtain ⟨s12, hs12, hpc12, hr12R, hd12⟩ := step_goto_at (input := input)
        (by rw [hpc11, hpc10]; exact hR2 7 _ rfl) (by omega)
      have h12EqR : ∀ r : Fin 15, reg s12 r = reg s11 r := fun r => by
        rcases s12 with ⟨ar, _, _, _, _⟩; rcases s11 with ⟨br, _, _, _, _⟩
        dsimp only at hr12R; subst ar; rfl
      have h12Data : s12.data = st.data := by rw [hd12, hd11, h10Data]
      have h12Preserve : ∀ r : Fin 15, r ≠ reg4 → r ≠ reg6 → r ≠ reg7 → reg s12 r = reg st r :=
        fun r h4 h6 h7 => by rw [h12EqR, hro11 r h4, h10Preserve r h6 h7]
      have h12_4 : (reg s12 reg4).val = sp := by
        have h10_4 : (reg s10 reg4).val = sp + 1 := by
          rw [h10Preserve reg4 (by intro h; cases h) (by intro h; cases h), hr4]
        have h10_1 : (reg s10 reg1).val = 1 := by
          rw [h10Preserve reg1 (by intro h; cases h) (by intro h; cases h), hr1]
        rw [h12EqR, hr4_11, sub_no_wrap _ _ (by rw [h10_4, h10_1]; omega), h10_4, h10_1]
        omega
      have hRemNext : ∀ w : Fin N, entryF w < t ∧ t < stopF w → w ∈ stk0.take sp := by
        intro w hw
        have hm1 := hRem w hw
        have hTake : stk0.take (sp + 1) = stk0.take sp ++ [stk0[sp]'hspLtStk] := by
          rw [List.take_succ_eq_append_getElem hspLtStk]
        rw [hTake, List.mem_append, List.mem_singleton] at hm1
        rcases hm1 with hm | rfl
        · exact hm
        · exact False.elim (hCmp hw.2)
      obtain ⟨sp', steps', out, hLe, hStLe, hRestSteps, hOutPc, hOutD,
          ho0, ho1, hom, ho2, ho3, ho4, hoMem⟩ :=
        ih s12 (by omega) (by omega) hpc12
          (by rw [h12Preserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0])
          (by rw [h12Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1])
          (by rw [h12Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm])
          (by rw [h12Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2])
          (by rw [h12Preserve reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3])
          h12_4
          (by rw [h12Data]; exact hMetaT)
          (fun i hi => by rw [h12Data]; exact hStops i (Nat.lt_succ_of_lt hi))
          hRemNext
      refine ⟨sp', 12 + steps', out, Nat.le_trans hLe (Nat.le_succ sp), by omega, ?_,
        hOutPc, hOutD.trans h12Data, ho0, ho1, hom, ho2, ho3, ho4, hoMem⟩
      have hStep12 : Steps code input 12 st s12 :=
        hPreSteps.append (Steps.cons hs11 (steps_1_of_step hs12))
      rw [show 12 + steps' = 10 + (1 + 1) + steps' by omega]
      exact hStep12.append hRestSteps

private theorem dfsDecodeU_spec {code : Program DomL} {input : Input DomL}
    (h100 : 100 ≤ 2 ^ bits) {n m N t sp : Nat} (uVal : Nat)
    (hPl : Placed code 18 (dfsDecodeUInstrs (bits := bits) h100))
    (hSz : 28 < code.size)
    (hDataFit : tempArrBase n m N + N ≤ 2 ^ bits)
    (htLtN : t < N)
    (st : State DomL) (hpc : st.pc = 18)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hrm : (reg st rMeta).val = metaArrBase n m N)
    (hr2 : (reg st reg2).val = N) (hr3 : (reg st reg3).val = t) (hr4 : (reg st reg4).val = sp)
    (hMetaT : (st.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N))
    (hInvAt : (st.data[tempArrBase n m N + t]?).map Fin.val = some uVal) :
    ∃ out : State DomL, Steps code input 6 st out ∧
      out.pc = (if 0 < sp then 28 else 24) ∧ out.data = st.data ∧
      (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
      (reg out rMeta).val = metaArrBase n m N ∧
      (reg out reg2).val = N ∧ (reg out reg3).val = t ∧ (reg out reg4).val = sp ∧
      (reg out reg5).val = uVal := by
  have hPl1 : Placed code 18 (metaLoadInstrs reg5 reg6 mIdxTempBase (by change 13 < 2 ^ bits; omega)) :=
    Placed_append_left hPl
  have hR1 := Placed_append_right hPl
  change Placed code 21 [Instr.add reg6 reg5 reg3, Instr.loadData reg5 reg6, Instr.branchLt reg0 reg4 28 24] at hR1
  have hMetaBits : metaArrBase n m N + mIdxTempBase < 2 ^ bits := by
    have : tempArrBase n m N = metaArrBase n m N + 48 := rfl
    change metaArrBase n m N + 13 < 2 ^ bits; omega
  obtain ⟨s3, hs3, hpc3, hd3, hr5_3, hro3⟩ := run_metaLoad_slice
    (dst := reg5) (tmp := reg6) (off := mIdxTempBase) (hOff := by change 13 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc hrm hMetaBits hMetaT
  obtain ⟨s4, hs4, hpc4, hr6_4, hro4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3]; exact hR1 0 _ rfl) (by rw [hpc3]; omega)
  have hIdx4 : (reg s4 reg6).val = tempArrBase n m N + t := by
    have h3_3 : (reg s3 reg3).val = t := by
      rw [hro3 reg3 (by intro h; cases h) (by intro h; cases h), hr3]
    rw [hr6_4, add_no_wrap _ _ (by rw [hr5_3, h3_3]; omega), hr5_3, h3_3]
  obtain ⟨wu, hwu, hwuVal⟩ := Option.map_eq_some_iff.mp hInvAt
  obtain ⟨s5, hs5, hpc5, hr5_5, hro5, hd5⟩ := step_loadData_at (input := input)
    (by rw [hpc4, hpc3]; exact hR1 1 _ rfl) (by rw [hpc4, hpc3]; omega)
    (by rw [hd4, hd3, hIdx4]; exact hwu)
  obtain ⟨s6, hs6, hpc6, hr6R, hd6⟩ := step_branchLt_at (input := input)
    (by rw [hpc5, hpc4, hpc3]; exact hR1 2 _ rfl) (by split <;> omega)
  have h6EqR : ∀ r : Fin 15, reg s6 r = reg s5 r := fun r => by
    rcases s6 with ⟨ar, _, _, _, _⟩; rcases s5 with ⟨br, _, _, _, _⟩
    dsimp only at hr6R; subst ar; rfl
  have h6Preserve : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → reg s6 r = reg st r := fun r h5 h6 => by
    rw [h6EqR, hro5 r h5, hro4 r h6, hro3 r h5 h6]
  have hr4_5 : (reg s5 reg4).val = sp := by
    rw [hro5 reg4 (by intro h; cases h), hro4 reg4 (by intro h; cases h),
      hro3 reg4 (by intro h; cases h) (by intro h; cases h), hr4]
  have hr0_5 : (reg s5 reg0).val = 0 := by
    rw [hro5 reg0 (by intro h; cases h), hro4 reg0 (by intro h; cases h),
      hro3 reg0 (by intro h; cases h) (by intro h; cases h), hr0]
  rw [hr0_5, hr4_5] at hpc6
  refine ⟨s6, hs3.append (Steps.cons hs4 (Steps.cons hs5 (steps_1_of_step hs6))),
    hpc6, by rw [hd6, hd5, hd4, hd3],
    by rw [h6Preserve reg0 (by intro h; cases h) (by intro h; cases h), hr0],
    by rw [h6Preserve reg1 (by intro h; cases h) (by intro h; cases h), hr1],
    by rw [h6Preserve rMeta (by intro h; cases h) (by intro h; cases h), hrm],
    by rw [h6Preserve reg2 (by intro h; cases h) (by intro h; cases h), hr2],
    by rw [h6Preserve reg3 (by intro h; cases h) (by intro h; cases h), hr3],
    by rw [h6Preserve reg4 (by intro h; cases h) (by intro h; cases h), hr4],
    by rw [h6EqR, hr5_5, hwuVal]⟩

private theorem dfsIsEmpty_spec {code : Program DomL} {input : Input DomL}
    {n m N t u : Nat}
    (hPl : Placed code 24 (dfsIsEmptyInstrs (bits := bits)))
    (hSz : 66 < code.size)
    (huLt : u < N) (hNLeW : N ≤ workCap)
    (st : State DomL) (hpc : st.pc = 24)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hrm : (reg st rMeta).val = metaArrBase n m N)
    (hr2 : (reg st reg2).val = N) (hr3 : (reg st reg3).val = t) (hr4 : (reg st reg4).val = 0)
    (hr5 : (reg st reg5).val = u) :
    ∃ out : State DomL, Steps code input 4 st out ∧ out.pc = 66 ∧
      (∀ j, j ≠ u → out.data[j]? = st.data[j]?) ∧
      (out.data[u]?).map Fin.val = some 0 ∧
      (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
      (reg out rMeta).val = metaArrBase n m N ∧
      (reg out reg2).val = N ∧ (reg out reg3).val = t ∧ (reg out reg4).val = 0 ∧
      (reg out reg5).val = u ∧ (reg out reg8).val = u ∧ (reg out reg9).val = u := by
  have hStLt : (reg st reg5).val < st.data.size := by
    rw [hr5, st.data_size]
    change u < workCap
    omega
  obtain ⟨hs1, hpc1, hr1Eq⟩ := step_storeData_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) hStLt (by rw [hpc]; omega)
  let s1 : State DomL :=
    { st with
      data := st.data.set (reg st reg5).val (reg st reg0) hStLt
      pc := st.pc + 1
      data_size := by simp only [Array.size_set, st.data_size] }
  have h1EqR : ∀ r : Fin 15, reg s1 r = reg st r := fun _ => rfl
  obtain ⟨s2, hs2, hpc2, hr8_2, hro2, hd2⟩ := step_mov_at (code := code) (input := input) (s := s1)
    (by change code[st.pc + 1]? = _; rw [hpc]; exact hPl 1 _ rfl)
    (by change st.pc + 1 + 1 < code.size; rw [hpc]; omega)
  obtain ⟨s3, hs3, hpc3, hr9_3, hro3, hd3⟩ := step_mov_at (code := code) (input := input) (s := s2)
    (by rw [hpc2]; change code[st.pc + 1 + 1]? = _; rw [hpc]; exact hPl 2 _ rfl)
    (by rw [hpc2]; change st.pc + 1 + 1 + 1 < code.size; rw [hpc]; omega)
  obtain ⟨s4, hs4, hpc4, hr4R, hd4⟩ := step_goto_at (code := code) (input := input) (s := s3)
    (by rw [hpc3, hpc2]; change code[st.pc + 1 + 1 + 1]? = _; rw [hpc]; exact hPl 3 _ rfl)
    (by omega)
  have h4EqR : ∀ r : Fin 15, reg s4 r = reg s3 r := fun r => by
    rcases s4 with ⟨ar, _, _, _, _⟩; rcases s3 with ⟨br, _, _, _, _⟩
    dsimp only at hr4R; subst ar; rfl
  have hPreserve : ∀ r : Fin 15, r ≠ reg8 → r ≠ reg9 → reg s4 r = reg st r := fun r h8 h9 => by
    rw [h4EqR, hro3 r h9, hro2 r h8, h1EqR]
  have hs4D : s4.data = st.data.set (reg st reg5).val (reg st reg0) hStLt := by
    rw [hd4, hd3, hd2]
  refine ⟨s4, Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (steps_1_of_step hs4))),
    hpc4, fun j hj => ?_, ?_,
    by rw [hPreserve reg0 (by intro h; cases h) (by intro h; cases h), hr0],
    by rw [hPreserve reg1 (by intro h; cases h) (by intro h; cases h), hr1],
    by rw [hPreserve rMeta (by intro h; cases h) (by intro h; cases h), hrm],
    by rw [hPreserve reg2 (by intro h; cases h) (by intro h; cases h), hr2],
    by rw [hPreserve reg3 (by intro h; cases h) (by intro h; cases h), hr3],
    by rw [hPreserve reg4 (by intro h; cases h) (by intro h; cases h), hr4],
    by rw [hPreserve reg5 (by intro h; cases h) (by intro h; cases h), hr5],
    by rw [h4EqR, hro3 reg8 (by intro h; cases h), hr8_2, h1EqR, hr5],
    by rw [h4EqR, hr9_3, hro2 reg5 (by intro h; cases h), h1EqR, hr5]⟩
  · rw [hs4D, Array.getElem?_set_ne hStLt (by rw [hr5]; exact hj.symm)]
  · rw [hs4D, ← hr5]; simp [hStLt]; exact Fin.ext hr0

private theorem dfsNonEmptyA_spec {code : Program DomL} {input : Input DomL}
    (h100 : 100 ≤ 2 ^ bits) {n m N t sp u pVal dPVal aVal dAVal : Nat}
    (hPl : Placed code 28 (dfsNonEmptyAInstrs (bits := bits) h100))
    (hSz : 65 < code.size)
    (hWorkFit : tempArrBase n m N + 3 * N ≤ workCap)
    (huLt : u < N) (hpLt : pVal < N) (haLt : aVal < N) (haNe : aVal ≠ u)
    (hspPos : 0 < sp) (hspLe : sp ≤ N)
    (hdA_le : dAVal ≤ dPVal) (hdP_lt : dPVal + 1 < 2 ^ bits)
    (st : State DomL) (hpc : st.pc = 28)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hrm : (reg st rMeta).val = metaArrBase n m N)
    (hr2 : (reg st reg2).val = N) (hr3 : (reg st reg3).val = t) (hr4 : (reg st reg4).val = sp)
    (hr5 : (reg st reg5).val = u)
    (hMetaT : (st.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N))
    (hMetaS : (st.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N))
    (hStkTop : (st.data[tempArrBase n m N + N + (sp - 1)]?).map Fin.val = some pVal)
    (hDp : (st.data[pVal]?).map Fin.val = some dPVal)
    (hJumpP : (st.data[storedBase N + 18 * pVal + 1]?).map Fin.val = some aVal)
    (hDa : (st.data[aVal]?).map Fin.val = some dAVal) :
    ∃ out : State DomL, Steps code input 24 st out ∧
      out.pc = (if 0 < dPVal - dAVal then 52 else 65) ∧
      (∀ j, j ≠ u → out.data[j]? = st.data[j]?) ∧
      (out.data[u]?).map Fin.val = some (dPVal + 1) ∧
      (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
      (reg out rMeta).val = metaArrBase n m N ∧
      (reg out reg2).val = N ∧ (reg out reg3).val = t ∧ (reg out reg4).val = sp ∧
      (reg out reg5).val = u ∧ (reg out reg8).val = pVal ∧
      (reg out reg10).val = storedBase N ∧ (reg out reg12).val = aVal ∧
      (reg out reg7).val = dPVal - dAVal := by
  have hTempBits : metaArrBase n m N + mIdxTempBase < 2 ^ bits := by
    have : tempArrBase n m N = metaArrBase n m N + 48 := rfl
    change metaArrBase n m N + 13 < 2 ^ bits; omega
  have hStoredBits : metaArrBase n m N + mIdxStoredBase < 2 ^ bits := by
    have : tempArrBase n m N = metaArrBase n m N + 48 := rfl
    change metaArrBase n m N + 4 < 2 ^ bits; omega
  have hMetaEq : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  have hPl1 : Placed code 28 (metaLoadInstrs reg6 reg7 mIdxTempBase (by change 13 < 2 ^ bits; omega)) :=
    Placed_append_left hPl
  have hR1 := Placed_append_right hPl
  rw [show (metaLoadInstrs (bits := bits) reg6 reg7 mIdxTempBase _).length = 3 by rfl] at hR1
  obtain ⟨s3, hs3, hpc3, hd3, hr6_3, hro3⟩ := run_metaLoad_slice
    (dst := reg6) (tmp := reg7) (off := mIdxTempBase) (hOff := by change 13 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc hrm hTempBits hMetaT
  have hPl2 : Placed code 31
      [ .add reg6 reg6 reg2, .add reg6 reg6 reg4, .sub reg6 reg6 reg1,
        .loadData reg8 reg6, .loadData reg6 reg8, .add reg7 reg6 reg1, .storeData reg5 reg7 ] :=
    Placed_append_left hR1
  have hR2 := Placed_append_right hR1
  rw [show ([Instr.add reg6 reg6 reg2, Instr.add reg6 reg6 reg4, Instr.sub reg6 reg6 reg1,
      Instr.loadData reg8 reg6, Instr.loadData reg6 reg8, Instr.add reg7 reg6 reg1,
      Instr.storeData reg5 reg7] : List (Instr bits 15)).length = 7 by rfl] at hR2
  obtain ⟨s4, hs4, hpc4, hr6_4, hro4, hd4⟩ := step_add_at (input := input)
    (by rw [hpc3]; exact hPl2 0 _ rfl) (by rw [hpc3]; omega)
  obtain ⟨s5, hs5, hpc5, hr6_5, hro5, hd5⟩ := step_add_at (input := input)
    (by rw [hpc4, hpc3]; exact hPl2 1 _ rfl) (by rw [hpc4, hpc3]; omega)
  obtain ⟨s6, hs6, hpc6, hr6_6, hro6, hd6⟩ := step_sub_at (input := input)
    (by rw [hpc5, hpc4, hpc3]; exact hPl2 2 _ rfl) (by rw [hpc5, hpc4, hpc3]; omega)
  have h36 : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → reg s3 r = reg st r := fun r h6 h7 => hro3 r h6 h7
  have h66 : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → reg s6 r = reg st r := fun r h6 h7 => by
    rw [hro6 r h6, hro5 r h6, hro4 r h6, h36 r h6 h7]
  have hStkIdx : (reg s6 reg6).val = tempArrBase n m N + N + (sp - 1) := by
    have h4V : (reg s4 reg6).val = tempArrBase n m N + N := by
      have hr2_3 : (reg s3 reg2).val = N := by
        rw [h36 reg2 (by intro h; cases h) (by intro h; cases h), hr2]
      rw [hr6_4, add_no_wrap _ _ (by rw [hr6_3, hr2_3]; omega), hr6_3, hr2_3]
    have h5V : (reg s5 reg6).val = tempArrBase n m N + N + sp := by
      have hr4_4 : (reg s4 reg4).val = sp := by
        rw [hro4 reg4 (by intro h; cases h), h36 reg4 (by intro h; cases h) (by intro h; cases h), hr4]
      rw [hr6_5, add_no_wrap _ _ (by rw [h4V, hr4_4]; omega), h4V, hr4_4]
    have hr1_5 : (reg s5 reg1).val = 1 := by
      rw [hro5 reg1 (by intro h; cases h), hro4 reg1 (by intro h; cases h),
        h36 reg1 (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr6_6, sub_no_wrap _ _ (by rw [hr1_5, h5V]; omega), h5V, hr1_5]; omega
  obtain ⟨wp, hwp, hwpVal⟩ := Option.map_eq_some_iff.mp hStkTop
  obtain ⟨s7, hs7, hpc7, hr8_7, hro7, hd7⟩ := step_loadData_at (input := input)
    (by rw [hpc6, hpc5, hpc4, hpc3]; exact hPl2 3 _ rfl) (by rw [hpc6, hpc5, hpc4, hpc3]; omega)
    (by rw [hd6, hd5, hd4, hd3, hStkIdx]; exact hwp)
  have h7_8 : (reg s7 reg8).val = pVal := by rw [hr8_7, hwpVal]
  obtain ⟨wdp, hwdp, hwdpVal⟩ := Option.map_eq_some_iff.mp hDp
  obtain ⟨s8, hs8, hpc8, hr6_8, hro8, hd8⟩ := step_loadData_at (input := input)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3]; exact hPl2 4 _ rfl)
    (by rw [hpc7, hpc6, hpc5, hpc4, hpc3]; omega)
    (by rw [hd7, hd6, hd5, hd4, hd3, h7_8]; exact hwdp)
  have h8_6 : (reg s8 reg6).val = dPVal := by rw [hr6_8, hwdpVal]
  obtain ⟨s9, hs9, hpc9, hr7_9, hro9, hd9⟩ := step_add_at (input := input)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3]; exact hPl2 5 _ rfl)
    (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3]; omega)
  have h9_7 : (reg s9 reg7).val = dPVal + 1 := by
    have hr1_8 : (reg s8 reg1).val = 1 := by
      rw [hro8 reg1 (by intro h; cases h), hro7 reg1 (by intro h; cases h),
        h66 reg1 (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr7_9, add_no_wrap _ _ (by rw [h8_6, hr1_8]; omega), h8_6, hr1_8]
  have h9Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → reg s9 r = reg st r :=
    fun r h6 h7 h8 => by rw [hro9 r h7, hro8 r h6, hro7 r h8, h66 r h6 h7]
  have hTempEq : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  have hMetaEq := metaArrBase_eq n m N
  have hStLt : (reg s9 reg5).val < s9.data.size := by
    rw [h9Preserve reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr5, s9.data_size]
    change u < workCap
    omega
  obtain ⟨hs10, hpc10, _⟩ := step_storeData_at (input := input)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3]; exact hPl2 6 _ rfl) hStLt
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3]; omega)
  let s10 : State DomL :=
    { s9 with
      data := s9.data.set (reg s9 reg5).val (reg s9 reg7) hStLt
      pc := s9.pc + 1
      data_size := by simp only [Array.size_set, s9.data_size] }
  have h10pc : s10.pc = 38 := by change s9.pc + 1 = 38; rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3]
  have h10_5 : (reg s10 reg5).val = u := by
    change (reg s9 reg5).val = u
    rw [h9Preserve reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr5]
  have h10_data : ∀ j, j ≠ u → s10.data[j]? = st.data[j]? := fun j hj => by
    change (s9.data.set (reg s9 reg5).val (reg s9 reg7) hStLt)[j]? = st.data[j]?
    have h9_5 : (reg s9 reg5).val = u := h10_5
    rw [Array.getElem?_set_ne hStLt (by rw [h9_5]; exact hj.symm),
      hd9, hd8, hd7, hd6, hd5, hd4, hd3]
  have h10_u : (s10.data[u]?).map Fin.val = some (dPVal + 1) := by
    change ((s9.data.set (reg s9 reg5).val (reg s9 reg7) hStLt)[u]?).map Fin.val = _
    have h9_5 : (reg s9 reg5).val = u := h10_5
    rw [← h9_5]
    simp only [Array.getElem?_set_self, Option.map_some]
    exact congrArg some h9_7
  have hPl3 : Placed code 38 (metaLoadInstrs reg10 reg7 mIdxStoredBase (by change 4 < 2 ^ bits; omega)) :=
    Placed_append_left hR2
  have hR3 := Placed_append_right hR2
  rw [show (metaLoadInstrs (bits := bits) reg10 reg7 mIdxStoredBase _).length = 3 by rfl] at hR3
  have h10_m : (reg s10 rMeta).val = metaArrBase n m N := by
    change (reg s9 rMeta).val = metaArrBase n m N
    rw [h9Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm]
  have hMetaS10 : (s10.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N) := by
    rw [h10_data _ (by change metaArrBase n m N + 4 ≠ u; omega)]
    exact hMetaS
  obtain ⟨s13, hs13, hpc13, hd13, hr10_13, hro13⟩ := run_metaLoad_slice
    (dst := reg10) (tmp := reg7) (off := mIdxStoredBase) (hOff := by change 4 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl3 (by omega) h10pc h10_m hStoredBits hMetaS10
  have hPl4 := Placed_append_left hR3
  have hR4 := Placed_append_right hR3
  rw [show (mul18Instrs (bits := bits) reg11 reg7 reg8).length = 5 by rfl] at hR4
  have h13_8 : (reg s13 reg8).val = pVal := by
    rw [hro13 reg8 (by intro h; cases h) (by intro h; cases h)]
    change (reg s10 reg8).val = pVal
    change (reg s9 reg8).val = pVal
    rw [hro9 reg8 (by intro h; cases h), hro8 reg8 (by intro h; cases h), h7_8]
  have hFit18 : 18 * (reg s13 reg8).val < 2 ^ bits := by rw [h13_8]; omega
  obtain ⟨s18, hs18, hpc18, hd18, hr11_18, hro18⟩ := steps_add_mul18 (input := input)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPl4 (by omega) s13 hpc13 hFit18
  have h18pc : s18.pc = 46 := by omega
  have h18_11 : (reg s18 reg11).val = 18 * pVal := by rw [hr11_18, h13_8]
  have h18_10 : (reg s18 reg10).val = storedBase N := by
    rw [hro18 reg10 (by intro h; cases h) (by intro h; cases h), hr10_13]
  obtain ⟨s19, hs19, hpc19, hr11_19, hro19, hd19⟩ := step_add_at (input := input)
    (by rw [h18pc]; exact hR4 0 _ rfl) (by rw [h18pc]; omega)
  have h19_11 : (reg s19 reg11).val = storedBase N + 18 * pVal := by
    rw [hr11_19, add_no_wrap _ _ (by rw [h18_10, h18_11]; unfold storedBase; omega), h18_10, h18_11]
  obtain ⟨s20, hs20, hpc20, hr11_20, hro20, hd20⟩ := step_add_at (input := input)
    (by rw [hpc19, h18pc]; exact hR4 1 _ rfl) (by rw [hpc19, h18pc]; omega)
  have h20_11 : (reg s20 reg11).val = storedBase N + 18 * pVal + 1 := by
    have hr1_19 : (reg s19 reg1).val = 1 := by
      rw [hro19 reg1 (by intro h; cases h), hro18 reg1 (by intro h; cases h) (by intro h; cases h),
        hro13 reg1 (by intro h; cases h) (by intro h; cases h)]
      change (reg s9 reg1).val = 1
      rw [h9Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr11_20, add_no_wrap _ _ (by rw [h19_11, hr1_19]; unfold storedBase; omega), h19_11, hr1_19]
  have hJumpPs20 : (s20.data[storedBase N + 18 * pVal + 1]?).map Fin.val = some aVal := by
    rw [hd20, hd19, hd18, hd13, h10_data _ (by unfold storedBase; omega)]
    exact hJumpP
  obtain ⟨wa, hwa, hwaVal⟩ := Option.map_eq_some_iff.mp hJumpPs20
  obtain ⟨s21, hs21, hpc21, hr12_21, hro21, hd21⟩ := step_loadData_at (input := input)
    (by rw [hpc20, hpc19, h18pc]; exact hR4 2 _ rfl)
    (by rw [hpc20, hpc19, h18pc]; omega) (by rw [h20_11]; exact hwa)
  have h21_12 : (reg s21 reg12).val = aVal := by rw [hr12_21, hwaVal]
  have hDaPs21 : (s21.data[aVal]?).map Fin.val = some dAVal := by
    rw [hd21, hd20, hd19, hd18, hd13, h10_data _ haNe]; exact hDa
  obtain ⟨wda, hwda, hwdaVal⟩ := Option.map_eq_some_iff.mp hDaPs21
  obtain ⟨s22, hs22, hpc22, hr7_22, hro22, hd22⟩ := step_loadData_at (input := input)
    (by rw [hpc21, hpc20, hpc19, h18pc]; exact hR4 3 _ rfl)
    (by rw [hpc21, hpc20, hpc19, h18pc]; omega) (by rw [h21_12]; exact hwda)
  have h22_7 : (reg s22 reg7).val = dAVal := by rw [hr7_22, hwdaVal]
  have h22_6 : (reg s22 reg6).val = dPVal := by
    rw [hro22 reg6 (by intro h; cases h), hro21 reg6 (by intro h; cases h),
      hro20 reg6 (by intro h; cases h), hro19 reg6 (by intro h; cases h),
      hro18 reg6 (by intro h; cases h) (by intro h; cases h),
      hro13 reg6 (by intro h; cases h) (by intro h; cases h)]
    change (reg s9 reg6).val = dPVal
    rw [hro9 reg6 (by intro h; cases h), h8_6]
  obtain ⟨s23, hs23, hpc23, hr7_23, hro23, hd23⟩ := step_sub_at (input := input)
    (by rw [hpc22, hpc21, hpc20, hpc19, h18pc]; exact hR4 4 _ rfl)
    (by rw [hpc22, hpc21, hpc20, hpc19, h18pc]; omega)
  have h23_7 : (reg s23 reg7).val = dPVal - dAVal := by
    rw [hr7_23, sub_no_wrap _ _ (by rw [h22_7, h22_6]; exact hdA_le), h22_6, h22_7]
  obtain ⟨s24, hs24, hpc24, hr24R, hd24⟩ := step_branchLt_at (input := input)
    (by rw [hpc23, hpc22, hpc21, hpc20, hpc19, h18pc]; exact hR4 5 _ rfl)
    (by split <;> omega)
  have h24EqR : ∀ r : Fin 15, reg s24 r = reg s23 r := fun r => by
    rcases s24 with ⟨ar, _, _, _, _⟩; rcases s23 with ⟨br, _, _, _, _⟩
    dsimp only at hr24R; subst ar; rfl
  have h23_0 : (reg s23 reg0).val = 0 := by
    rw [hro23 reg0 (by intro h; cases h), hro22 reg0 (by intro h; cases h),
      hro21 reg0 (by intro h; cases h), hro20 reg0 (by intro h; cases h),
      hro19 reg0 (by intro h; cases h),
      hro18 reg0 (by intro h; cases h) (by intro h; cases h),
      hro13 reg0 (by intro h; cases h) (by intro h; cases h)]
    change (reg s9 reg0).val = 0
    rw [h9Preserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0]
  rw [h23_0, h23_7] at hpc24
  have h10Step : Steps code input 10 st s10 :=
    hs3.append (Steps.cons hs4 (Steps.cons hs5 (Steps.cons hs6
      (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (steps_1_of_step hs10)))))))
  have h14Step : Steps code input 14 s10 s24 :=
    hs13.append (hs18.append (Steps.cons hs19 (Steps.cons hs20 (Steps.cons hs21
      (Steps.cons hs22 (Steps.cons hs23 (steps_1_of_step hs24)))))))
  have h24Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg10 →
      r ≠ reg11 → r ≠ reg12 → reg s24 r = reg st r := fun r h6 h7 h8 h10 h11 h12 => by
    rw [h24EqR, hro23 r h7, hro22 r h7, hro21 r h12, hro20 r h11, hro19 r h11,
      hro18 r h11 h7, hro13 r h10 h7]
    exact h9Preserve r h6 h7 h8
  have hdRest : s24.data = s10.data := by
    rw [hd24, hd23, hd22, hd21, hd20, hd19, hd18, hd13]
  refine ⟨s24, h10Step.append h14Step, hpc24,
    fun j hj => by rw [hdRest]; exact h10_data j hj,
    by rw [hdRest]; exact h10_u,
    by rw [h24Preserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0],
    by rw [h24Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1],
    by rw [h24Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm],
    by rw [h24Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2],
    by rw [h24Preserve reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3],
    by rw [h24Preserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4],
    by rw [h24Preserve reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr5],
    ?_, ?_, ?_, by rw [h24EqR, h23_7]⟩
  · rw [h24EqR, hro23 reg8 (by intro h; cases h), hro22 reg8 (by intro h; cases h),
      hro21 reg8 (by intro h; cases h), hro20 reg8 (by intro h; cases h),
      hro19 reg8 (by intro h; cases h), hro18 reg8 (by intro h; cases h) (by intro h; cases h),
      h13_8]
  · rw [h24EqR, hro23 reg10 (by intro h; cases h), hro22 reg10 (by intro h; cases h),
      hro21 reg10 (by intro h; cases h), hro20 reg10 (by intro h; cases h),
      hro19 reg10 (by intro h; cases h), hro18 reg10 (by intro h; cases h) (by intro h; cases h), hr10_13]
  · rw [h24EqR, hro23 reg12 (by intro h; cases h), hro22 reg12 (by intro h; cases h), h21_12]

private theorem dfsCheckLen2_spec {code : Program DomL} {input : Input DomL}
    {n m N t sp u pVal aVal dAVal bVal dBVal len1 : Nat}
    (hPl : Placed code 52 (dfsCheckLen2Instrs (bits := bits)))
    (hSz : 66 < code.size)
    (hWorkFit : tempArrBase n m N + 3 * N ≤ workCap)
    (haLt : aVal < N) (_hbLt : bVal < N)
    (hdB_le : dBVal ≤ dAVal)
    (st : State DomL) (hpc : st.pc = 52)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hrm : (reg st rMeta).val = metaArrBase n m N)
    (hr2 : (reg st reg2).val = N) (hr3 : (reg st reg3).val = t) (hr4 : (reg st reg4).val = sp)
    (hr5 : (reg st reg5).val = u) (hr7 : (reg st reg7).val = len1) (hr8 : (reg st reg8).val = pVal)
    (hr10 : (reg st reg10).val = storedBase N) (hr12 : (reg st reg12).val = aVal)
    (hJumpA : (st.data[storedBase N + 18 * aVal + 1]?).map Fin.val = some bVal)
    (hDa : (st.data[aVal]?).map Fin.val = some dAVal)
    (hDb : (st.data[bVal]?).map Fin.val = some dBVal) :
    ∃ k out, k ≤ 13 ∧ Steps code input k st out ∧
      out.pc = (if len1 = dAVal - dBVal then 66 else 65) ∧ out.data = st.data ∧
      (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
      (reg out rMeta).val = metaArrBase n m N ∧
      (reg out reg2).val = N ∧ (reg out reg3).val = t ∧ (reg out reg4).val = sp ∧
      (reg out reg5).val = u ∧ (reg out reg8).val = pVal ∧ (reg out reg9).val = bVal := by
  have hPl1 := Placed_append_left hPl
  have hR1 := Placed_append_right hPl
  rw [show (mul18Instrs (bits := bits) reg11 reg6 reg12).length = 5 by rfl] at hR1
  have hTempEq : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  have hMetaEq := metaArrBase_eq n m N
  have hFit18 : 18 * (reg st reg12).val < 2 ^ bits := by rw [hr12]; omega
  obtain ⟨s5, hs5, hpc5, hd5, hr11_5, hro5⟩ := steps_add_mul18 (input := input)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPl1 (by omega) st hpc hFit18
  have h5_11 : (reg s5 reg11).val = 18 * aVal := by rw [hr11_5, hr12]
  have h5_10 : (reg s5 reg10).val = storedBase N := by
    rw [hro5 reg10 (by intro h; cases h) (by intro h; cases h), hr10]
  obtain ⟨s6, hs6, hpc6, hr11_6, hro6, hd6⟩ := step_add_at (input := input)
    (by rw [hpc5]; exact hR1 0 _ rfl) (by rw [hpc5]; omega)
  have h6_11 : (reg s6 reg11).val = storedBase N + 18 * aVal := by
    rw [hr11_6, add_no_wrap _ _ (by rw [h5_10, h5_11]; unfold storedBase; omega), h5_10, h5_11]
  obtain ⟨s7, hs7, hpc7, hr11_7, hro7, hd7⟩ := step_add_at (input := input)
    (by rw [hpc6, hpc5]; exact hR1 1 _ rfl) (by rw [hpc6, hpc5]; omega)
  have h7_11 : (reg s7 reg11).val = storedBase N + 18 * aVal + 1 := by
    have hr1_6 : (reg s6 reg1).val = 1 := by
      rw [hro6 reg1 (by intro h; cases h), hro5 reg1 (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr11_7, add_no_wrap _ _ (by rw [h6_11, hr1_6]; unfold storedBase; omega), h6_11, hr1_6]
  obtain ⟨wb, hwb, hwbVal⟩ := Option.map_eq_some_iff.mp hJumpA
  obtain ⟨s8, hs8, hpc8, hr9_8, hro8, hd8⟩ := step_loadData_at (input := input)
    (by rw [hpc7, hpc6, hpc5]; exact hR1 2 _ rfl) (by rw [hpc7, hpc6, hpc5]; omega)
    (by rw [hd7, hd6, hd5, h7_11]; exact hwb)
  have h8_9 : (reg s8 reg9).val = bVal := by rw [hr9_8, hwbVal]
  have h8_12 : (reg s8 reg12).val = aVal := by
    rw [hro8 reg12 (by intro h; cases h), hro7 reg12 (by intro h; cases h),
      hro6 reg12 (by intro h; cases h), hro5 reg12 (by intro h; cases h) (by intro h; cases h), hr12]
  obtain ⟨wda, hwda, hwdaVal⟩ := Option.map_eq_some_iff.mp hDa
  obtain ⟨s9, hs9, hpc9, hr6_9, hro9, hd9⟩ := step_loadData_at (input := input)
    (by rw [hpc8, hpc7, hpc6, hpc5]; exact hR1 3 _ rfl) (by rw [hpc8, hpc7, hpc6, hpc5]; omega)
    (by rw [hd8, hd7, hd6, hd5, h8_12]; exact hwda)
  have h9_6 : (reg s9 reg6).val = dAVal := by rw [hr6_9, hwdaVal]
  have h9_9 : (reg s9 reg9).val = bVal := by rw [hro9 reg9 (by intro h; cases h), h8_9]
  obtain ⟨wdb, hwdb, hwdbVal⟩ := Option.map_eq_some_iff.mp hDb
  obtain ⟨s10, hs10, hpc10, hr11_10, hro10, hd10⟩ := step_loadData_at (input := input)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5]; exact hR1 4 _ rfl)
    (by rw [hpc9, hpc8, hpc7, hpc6, hpc5]; omega) (by rw [hd9, hd8, hd7, hd6, hd5, h9_9]; exact hwdb)
  have h10_11 : (reg s10 reg11).val = dBVal := by rw [hr11_10, hwdbVal]
  have h10_6 : (reg s10 reg6).val = dAVal := by rw [hro10 reg6 (by intro h; cases h), h9_6]
  obtain ⟨s11, hs11, hpc11, hr6_11, hro11, hd11⟩ := step_sub_at (input := input)
    (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hR1 5 _ rfl)
    (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; omega)
  have h11_6 : (reg s11 reg6).val = dAVal - dBVal := by
    rw [hr6_11, sub_no_wrap _ _ (by rw [h10_6, h10_11]; exact hdB_le), h10_6, h10_11]
  have h11Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg9 → r ≠ reg11 → reg s11 r = reg st r :=
    fun r h6 h9 h11 => by
      rw [hro11 r h6, hro10 r h11, hro9 r h6, hro8 r h9, hro7 r h11, hro6 r h11, hro5 r h11 h6]
  have h11_7 : (reg s11 reg7).val = len1 := by
    rw [h11Preserve reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr7]
  obtain ⟨s12, hs12, hpc12, hr12R, hd12⟩ := step_branchLt_at (input := input)
    (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5]; exact hR1 6 _ rfl)
    (by split <;> omega)
  have h12EqR : ∀ r : Fin 15, reg s12 r = reg s11 r := fun r => by
    rcases s12 with ⟨ar, _, _, _, _⟩; rcases s11 with ⟨br, _, _, _, _⟩
    dsimp only at hr12R; subst ar; rfl
  have h12Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg9 → r ≠ reg11 → reg s12 r = reg st r :=
    fun r h6 h9 h11 => by rw [h12EqR, h11Preserve r h6 h9 h11]
  have h12_6 : (reg s12 reg6).val = dAVal - dBVal := by rw [h12EqR, h11_6]
  have h12_7 : (reg s12 reg7).val = len1 := by rw [h12EqR, h11_7]
  have h12_9 : (reg s12 reg9).val = bVal := by
    rw [h12EqR, hro11 reg9 (by intro h; cases h), hro10 reg9 (by intro h; cases h), h9_9]
  have hSteps12 : Steps code input 12 st s12 :=
    hs5.append (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
      (Steps.cons hs10 (Steps.cons hs11 (steps_1_of_step hs12)))))))
  have hd12Eq : s12.data = st.data := by rw [hd12, hd11, hd10, hd9, hd8, hd7, hd6, hd5]
  by_cases hLt1 : len1 < dAVal - dBVal
  · rw [ite_eq_left (by rw [h11_7, h11_6]; exact hLt1)] at hpc12
    have hNeq : ¬ len1 = dAVal - dBVal := by omega
    rw [ite_eq_right hNeq]
    exact ⟨12, s12, by omega, hSteps12, hpc12, hd12Eq,
      by rw [h12Preserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0],
      by rw [h12Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1],
      by rw [h12Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm],
      by rw [h12Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2],
      by rw [h12Preserve reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3],
      by rw [h12Preserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4],
      by rw [h12Preserve reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr5],
      by rw [h12Preserve reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr8],
      h12_9⟩
  · rw [ite_eq_right (by rw [h11_7, h11_6]; exact hLt1)] at hpc12
    obtain ⟨s13, hs13, hpc13, hr13R, hd13⟩ := step_branchLt_at (input := input)
      (by rw [hpc12]; exact hR1 7 _ rfl) (by split <;> omega)
    have h13EqR : ∀ r : Fin 15, reg s13 r = reg s12 r := fun r => by
      rcases s13 with ⟨ar, _, _, _, _⟩; rcases s12 with ⟨br, _, _, _, _⟩
      dsimp only at hr13R; subst ar; rfl
    rw [h12_6, h12_7] at hpc13
    have hIteEq : (if dAVal - dBVal < len1 then 65 else 66) =
        (if len1 = dAVal - dBVal then 66 else 65) := by
      by_cases h1 : dAVal - dBVal < len1 <;> by_cases h2 : len1 = dAVal - dBVal <;> simp [h1, h2] <;> omega
    rw [hIteEq] at hpc13
    refine ⟨13, s13, by omega, hSteps12.append (steps_1_of_step hs13), hpc13, hd13.trans hd12Eq,
      by rw [h13EqR, h12Preserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0],
      by rw [h13EqR, h12Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1],
      by rw [h13EqR, h12Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm],
      by rw [h13EqR, h12Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2],
      by rw [h13EqR, h12Preserve reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3],
      by rw [h13EqR, h12Preserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4],
      by rw [h13EqR, h12Preserve reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr5],
      by rw [h13EqR, h12Preserve reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr8],
      by rw [h13EqR, h12_9]⟩

private theorem dfsUseP_spec {code : Program DomL} {input : Input DomL}
    {n m N t sp u pVal : Nat}
    (hPl : Placed code 65 (dfsUsePInstrs (bits := bits)))
    (hSz : 66 < code.size)
    (st : State DomL) (hpc : st.pc = 65)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hrm : (reg st rMeta).val = metaArrBase n m N)
    (hr2 : (reg st reg2).val = N) (hr3 : (reg st reg3).val = t) (hr4 : (reg st reg4).val = sp)
    (hr5 : (reg st reg5).val = u) (hr8 : (reg st reg8).val = pVal) :
    ∃ out : State DomL, Steps code input 1 st out ∧ out.pc = 66 ∧ out.data = st.data ∧
      (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
      (reg out rMeta).val = metaArrBase n m N ∧
      (reg out reg2).val = N ∧ (reg out reg3).val = t ∧ (reg out reg4).val = sp ∧
      (reg out reg5).val = u ∧ (reg out reg8).val = pVal ∧ (reg out reg9).val = pVal := by
  obtain ⟨out, hs, hpc1, hr9, hro, hd⟩ := step_mov_at (input := input)
    (by rw [hpc]; exact hPl 0 _ rfl) (by rw [hpc]; omega)
  exact ⟨out, steps_1_of_step hs, by omega, hd,
    by rw [hro reg0 (by intro h; cases h), hr0],
    by rw [hro reg1 (by intro h; cases h), hr1],
    by rw [hro rMeta (by intro h; cases h), hrm],
    by rw [hro reg2 (by intro h; cases h), hr2],
    by rw [hro reg3 (by intro h; cases h), hr3],
    by rw [hro reg4 (by intro h; cases h), hr4],
    by rw [hro reg5 (by intro h; cases h), hr5],
    by rw [hro reg8 (by intro h; cases h), hr8],
    by rw [hr9, hr8]⟩

private theorem dfsWritePJ_spec {code : Program DomL} {input : Input DomL}
    (h100 : 100 ≤ 2 ^ bits) {n m N t sp u pVal jVal stopUVal : Nat}
    (hPl : Placed code 66 (dfsWritePJInstrs (bits := bits) h100))
    (hSz : 95 < code.size)
    (hWorkFit : tempArrBase n m N + 3 * N ≤ workCap)
    (huLt : u < N) (hspLt : sp < N)
    (htLtN : t < N)
    (st : State DomL) (hpc : st.pc = 66)
    (hr0 : (reg st reg0).val = 0) (hr1 : (reg st reg1).val = 1)
    (hrm : (reg st rMeta).val = metaArrBase n m N)
    (hr2 : (reg st reg2).val = N) (hr3 : (reg st reg3).val = t) (hr4 : (reg st reg4).val = sp)
    (hr5 : (reg st reg5).val = u) (hr8 : (reg st reg8).val = pVal) (hr9 : (reg st reg9).val = jVal)
    (hMetaS : (st.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N))
    (hMetaT : (st.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N))
    (hMetaF : (st.data[metaArrBase n m N + mIdxFStopInBase]?).map Fin.val = some (4 + n + 3 * N))
    (hFStop : (input.words[4 + n + 3 * N + u]?).map Fin.val = some stopUVal) :
    ∃ out : State DomL, Steps code input 29 st out ∧ out.pc = 5 ∧
      (∀ j, j ≠ storedBase N + 18 * u → j ≠ storedBase N + 18 * u + 1 →
        j ≠ tempArrBase n m N + N + sp → j ≠ tempArrBase n m N + 2 * N + sp →
        out.data[j]? = st.data[j]?) ∧
      (out.data[storedBase N + 18 * u]?).map Fin.val = some pVal ∧
      (out.data[storedBase N + 18 * u + 1]?).map Fin.val = some jVal ∧
      (out.data[tempArrBase n m N + N + sp]?).map Fin.val = some u ∧
      (out.data[tempArrBase n m N + 2 * N + sp]?).map Fin.val = some stopUVal ∧
      (reg out reg0).val = 0 ∧ (reg out reg1).val = 1 ∧
      (reg out rMeta).val = metaArrBase n m N ∧
      (reg out reg2).val = N ∧ (reg out reg3).val = t + 1 ∧ (reg out reg4).val = sp + 1 := by
  have hTempEq : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  have hMetaEq := metaArrBase_eq n m N
  have hStoredBits : metaArrBase n m N + mIdxStoredBase < 2 ^ bits := by
    change metaArrBase n m N + 4 < 2 ^ bits; omega
  have hTempBits : metaArrBase n m N + mIdxTempBase < 2 ^ bits := by
    change metaArrBase n m N + 13 < 2 ^ bits; omega
  have hFStopBits : metaArrBase n m N + mIdxFStopInBase < 2 ^ bits := by
    change metaArrBase n m N + 18 < 2 ^ bits; omega
  have hPl1 := Placed_append_left hPl
  have hR1 := Placed_append_right hPl
  rw [show (metaLoadInstrs (bits := bits) reg10 reg7 mIdxStoredBase _).length = 3 by rfl] at hR1
  obtain ⟨s3, hs3, hpc3, hd3, hr10_3, hro3⟩ := run_metaLoad_slice
    (dst := reg10) (tmp := reg7) (off := mIdxStoredBase) (hOff := by change 4 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl1 (by omega) hpc hrm hStoredBits hMetaS
  have hPl2 := Placed_append_left hR1
  have hR2 := Placed_append_right hR1
  rw [show (mul18Instrs (bits := bits) reg11 reg7 reg5).length = 5 by rfl] at hR2
  have h3_5 : (reg s3 reg5).val = u := by
    rw [hro3 reg5 (by intro h; cases h) (by intro h; cases h), hr5]
  obtain ⟨s8, hs8, hpc8, hd8, hr11_8, hro8⟩ := steps_add_mul18 (input := input)
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    hPl2 (by omega) s3 hpc3 (by rw [h3_5]; omega)
  have h8pc : s8.pc = 66 + 3 + 5 := by omega
  have h8_11 : (reg s8 reg11).val = 18 * u := by rw [hr11_8, h3_5]
  have h8_10 : (reg s8 reg10).val = storedBase N := by
    rw [hro8 reg10 (by intro h; cases h) (by intro h; cases h), hr10_3]
  have h8Preserve : ∀ r : Fin 15, r ≠ reg7 → r ≠ reg10 → r ≠ reg11 → reg s8 r = reg st r :=
    fun r h7 h10 h11 => by rw [hro8 r h11 h7, hro3 r h10 h7]
  have hPl3 : Placed code 74 [ .add reg10 reg10 reg11, .storeData reg10 reg8,
      .add reg10 reg10 reg1, .storeData reg10 reg9 ] := Placed_append_left hR2
  have hR3 := Placed_append_right hR2
  rw [show ([Instr.add reg10 reg10 reg11, Instr.storeData reg10 reg8,
      Instr.add reg10 reg10 reg1, Instr.storeData reg10 reg9] : List (Instr bits 15)).length = 4 by rfl] at hR3
  obtain ⟨s9, hs9, hpc9, hr10_9, hro9, hd9⟩ := step_add_at (input := input)
    (by rw [h8pc]; exact hPl3 0 _ rfl) (by rw [h8pc]; omega)
  have h9_10 : (reg s9 reg10).val = storedBase N + 18 * u := by
    rw [hr10_9, add_no_wrap _ _ (by rw [h8_10, h8_11]; unfold storedBase; omega), h8_10, h8_11]
  have hSt9Lt : (reg s9 reg10).val < s9.data.size := by
    rw [h9_10, s9.data_size]; unfold storedBase; change N + 18 * u < workCap; omega
  obtain ⟨hs10, hpc10, _⟩ := step_storeData_at (input := input)
    (by rw [hpc9, h8pc]; exact hPl3 1 _ rfl) hSt9Lt (by rw [hpc9, h8pc]; omega)
  let s10 : State DomL :=
    { s9 with
      data := s9.data.set (reg s9 reg10).val (reg s9 reg8) hSt9Lt
      pc := s9.pc + 1
      data_size := by simp only [Array.size_set, s9.data_size] }
  have h10pc : s10.pc = 76 := by change s9.pc + 1 = 76; rw [hpc9, h8pc]
  have h10_8 : (reg s10 reg8).val = pVal := by
    change (reg s9 reg8).val = pVal
    rw [hro9 reg8 (by intro h; cases h), h8Preserve reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr8]
  have h10_P : (s10.data[storedBase N + 18 * u]?).map Fin.val = some pVal := by
    change ((s9.data.set (reg s9 reg10).val (reg s9 reg8) hSt9Lt)[storedBase N + 18 * u]?).map Fin.val = _
    rw [← h9_10]; simp [hSt9Lt]; exact h10_8
  have h10_Fr : ∀ j, j ≠ storedBase N + 18 * u → s10.data[j]? = st.data[j]? := fun j hj => by
    change (s9.data.set (reg s9 reg10).val (reg s9 reg8) hSt9Lt)[j]? = st.data[j]?
    rw [Array.getElem?_set_ne hSt9Lt (by rw [h9_10]; exact hj.symm), hd9, hd8, hd3]
  obtain ⟨s11, hs11, hpc11, hr10_11, hro11, hd11⟩ := step_add_at (input := input)
    (by rw [h10pc]; exact hPl3 2 _ rfl) (by rw [h10pc]; omega)
  have h11_10 : (reg s11 reg10).val = storedBase N + 18 * u + 1 := by
    have h10_10 : (reg s10 reg10).val = storedBase N + 18 * u := h9_10
    have h10_1 : (reg s10 reg1).val = 1 := by
      change (reg s9 reg1).val = 1
      rw [hro9 reg1 (by intro h; cases h), h8Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr10_11, add_no_wrap _ _ (by rw [h10_10, h10_1]; unfold storedBase; omega), h10_10, h10_1]
  have hSt11Lt : (reg s11 reg10).val < s11.data.size := by
    rw [h11_10, s11.data_size]; unfold storedBase; change N + 18 * u + 1 < workCap; omega
  obtain ⟨hs12, hpc12, _⟩ := step_storeData_at (input := input)
    (by rw [hpc11, h10pc]; exact hPl3 3 _ rfl) hSt11Lt (by rw [hpc11, h10pc]; omega)
  let s12 : State DomL :=
    { s11 with
      data := s11.data.set (reg s11 reg10).val (reg s11 reg9) hSt11Lt
      pc := s11.pc + 1
      data_size := by simp only [Array.size_set, s11.data_size] }
  have h12pc : s12.pc = 78 := by change s11.pc + 1 = 78; rw [hpc11, h10pc]
  have h12Preserve : ∀ r : Fin 15, r ≠ reg7 → r ≠ reg10 → r ≠ reg11 → reg s12 r = reg st r :=
    fun r h7 h10 h11 => by
      change reg s11 r = reg st r
      rw [hro11 r h10]
      change reg s9 r = reg st r
      rw [hro9 r h10, h8Preserve r h7 h10 h11]
  have h12_9 : (reg s12 reg9).val = jVal := by
    rw [h12Preserve reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr9]
  have h12_J : (s12.data[storedBase N + 18 * u + 1]?).map Fin.val = some jVal := by
    change ((s11.data.set (reg s11 reg10).val (reg s11 reg9) hSt11Lt)[storedBase N + 18 * u + 1]?).map Fin.val = _
    rw [← h11_10]; simp [hSt11Lt]; exact h12_9
  have h12_P : (s12.data[storedBase N + 18 * u]?).map Fin.val = some pVal := by
    change (s11.data.set (reg s11 reg10).val (reg s11 reg9) hSt11Lt)[storedBase N + 18 * u]?.map Fin.val = _
    rw [Array.getElem?_set_ne hSt11Lt (by rw [h11_10]; omega), hd11]; exact h10_P
  have h12_Fr : ∀ j, j ≠ storedBase N + 18 * u → j ≠ storedBase N + 18 * u + 1 →
      s12.data[j]? = st.data[j]? := fun j h1 h2 => by
    change (s11.data.set (reg s11 reg10).val (reg s11 reg9) hSt11Lt)[j]? = st.data[j]?
    rw [Array.getElem?_set_ne hSt11Lt (by rw [h11_10]; exact h2.symm), hd11]; exact h10_Fr j h1
  have hPl4 := Placed_append_left hR3
  have hR4 := Placed_append_right hR3
  rw [show (metaLoadInstrs (bits := bits) reg6 reg7 mIdxTempBase _).length = 3 by rfl] at hR4
  have h12_m : (reg s12 rMeta).val = metaArrBase n m N := by
    rw [h12Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm]
  have hMetaTs12 : (s12.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N) := by
    rw [h12_Fr _ (by unfold storedBase; omega) (by unfold storedBase; omega)]
    exact hMetaT
  obtain ⟨s15, hs15, hpc15, hd15, hr6_15, hro15⟩ := run_metaLoad_slice
    (dst := reg6) (tmp := reg7) (off := mIdxTempBase) (hOff := by change 13 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl4 (by omega) h12pc h12_m hTempBits hMetaTs12
  have hPl5 : Placed code 81 [ .add reg6 reg6 reg2, .add reg7 reg6 reg4, .storeData reg7 reg5 ] :=
    Placed_append_left hR4
  have hR5 := Placed_append_right hR4
  rw [show ([Instr.add reg6 reg6 reg2, Instr.add reg7 reg6 reg4, Instr.storeData reg7 reg5] :
      List (Instr bits 15)).length = 3 by rfl] at hR5
  have h15Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → r ≠ reg10 → r ≠ reg11 →
      reg s15 r = reg st r := fun r h6 h7 h10 h11 => by
    rw [hro15 r h6 h7, h12Preserve r h7 h10 h11]
  obtain ⟨s16, hs16, hpc16, hr6_16, hro16, hd16⟩ := step_add_at (input := input)
    (by rw [hpc15]; exact hPl5 0 _ rfl) (by rw [hpc15]; omega)
  have h16_6 : (reg s16 reg6).val = tempArrBase n m N + N := by
    have h15_2 : (reg s15 reg2).val = N := by
      rw [h15Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2]
    rw [hr6_16, add_no_wrap _ _ (by rw [hr6_15, h15_2]; omega), hr6_15, h15_2]
  obtain ⟨s17, hs17, hpc17, hr7_17, hro17, hd17⟩ := step_add_at (input := input)
    (by rw [hpc16, hpc15]; exact hPl5 1 _ rfl) (by rw [hpc16, hpc15]; omega)
  have h17_7 : (reg s17 reg7).val = tempArrBase n m N + N + sp := by
    have h16_4 : (reg s16 reg4).val = sp := by
      rw [hro16 reg4 (by intro h; cases h),
        h15Preserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4]
    rw [hr7_17, add_no_wrap _ _ (by rw [h16_6, h16_4]; omega), h16_6, h16_4]
  have hSt17Lt : (reg s17 reg7).val < s17.data.size := by
    rw [h17_7, s17.data_size]; change tempArrBase n m N + N + sp < workCap; omega
  obtain ⟨hs18, hpc18, _⟩ := step_storeData_at (input := input)
    (by rw [hpc17, hpc16, hpc15]; exact hPl5 2 _ rfl) hSt17Lt (by rw [hpc17, hpc16, hpc15]; omega)
  let s18 : State DomL :=
    { s17 with
      data := s17.data.set (reg s17 reg7).val (reg s17 reg5) hSt17Lt
      pc := s17.pc + 1
      data_size := by simp only [Array.size_set, s17.data_size] }
  have h18pc : s18.pc = 84 := by change s17.pc + 1 = 84; rw [hpc17, hpc16, hpc15]
  have h18Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → r ≠ reg10 → r ≠ reg11 →
      reg s18 r = reg st r := fun r h6 h7 h10 h11 => by
    change reg s17 r = reg st r
    rw [hro17 r h7, hro16 r h6, h15Preserve r h6 h7 h10 h11]
  have h18_5 : (reg s18 reg5).val = u := by
    rw [h18Preserve reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr5]
  have h18_6 : (reg s18 reg6).val = tempArrBase n m N + N := by
    change (reg s17 reg6).val = _; rw [hro17 reg6 (by intro h; cases h), h16_6]
  have h18_N : (s18.data[tempArrBase n m N + N + sp]?).map Fin.val = some u := by
    change ((s17.data.set (reg s17 reg7).val (reg s17 reg5) hSt17Lt)[tempArrBase n m N + N + sp]?).map Fin.val = _
    rw [← h17_7]; simp [hSt17Lt]; exact h18_5
  have h18_P : (s18.data[storedBase N + 18 * u]?).map Fin.val = some pVal := by
    change (s17.data.set (reg s17 reg7).val (reg s17 reg5) hSt17Lt)[storedBase N + 18 * u]?.map Fin.val = _
    rw [Array.getElem?_set_ne hSt17Lt (by rw [h17_7]; unfold storedBase; omega), hd17, hd16, hd15]; exact h12_P
  have h18_J : (s18.data[storedBase N + 18 * u + 1]?).map Fin.val = some jVal := by
    change (s17.data.set (reg s17 reg7).val (reg s17 reg5) hSt17Lt)[storedBase N + 18 * u + 1]?.map Fin.val = _
    rw [Array.getElem?_set_ne hSt17Lt (by rw [h17_7]; unfold storedBase; omega), hd17, hd16, hd15]; exact h12_J
  have h18_Fr : ∀ j, j ≠ storedBase N + 18 * u → j ≠ storedBase N + 18 * u + 1 →
      j ≠ tempArrBase n m N + N + sp → s18.data[j]? = st.data[j]? := fun j h1 h2 h3 => by
    change (s17.data.set (reg s17 reg7).val (reg s17 reg5) hSt17Lt)[j]? = st.data[j]?
    rw [Array.getElem?_set_ne hSt17Lt (by rw [h17_7]; exact h3.symm), hd17, hd16, hd15]
    exact h12_Fr j h1 h2
  have hPl6 := Placed_append_left hR5
  have hR6 := Placed_append_right hR5
  rw [show (metaLoadInstrs (bits := bits) reg8 reg7 mIdxFStopInBase _).length = 3 by rfl] at hR6
  have h18_m : (reg s18 rMeta).val = metaArrBase n m N := by
    rw [h18Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm]
  have hMetaFs18 : (s18.data[metaArrBase n m N + mIdxFStopInBase]?).map Fin.val = some (4 + n + 3 * N) := by
    rw [h18_Fr _ (by unfold storedBase; change metaArrBase n m N + 18 ≠ N + 18 * u; omega)
      (by unfold storedBase; change metaArrBase n m N + 18 ≠ N + 18 * u + 1; omega)
      (by change metaArrBase n m N + 18 ≠ tempArrBase n m N + N + sp; omega)]
    exact hMetaF
  obtain ⟨s21, hs21, hpc21, hd21, hr8_21, hro21⟩ := run_metaLoad_slice
    (dst := reg8) (tmp := reg7) (off := mIdxFStopInBase) (hOff := by change 18 < 2 ^ bits; omega)
    (by intro h; cases h) (by intro h; cases h) hPl6 (by omega) h18pc h18_m hFStopBits hMetaFs18
  obtain ⟨s22, hs22, hpc22, hr8_22, hro22, hd22⟩ := step_add_at (input := input)
    (by rw [hpc21]; exact hR6 0 _ rfl) (by rw [hpc21]; omega)
  have h22_8 : (reg s22 reg8).val = 4 + n + 3 * N + u := by
    have h21_5 : (reg s21 reg5).val = u := by
      rw [hro21 reg5 (by intro h; cases h) (by intro h; cases h), h18_5]
    rw [hr8_22, add_no_wrap _ _ (by rw [hr8_21, h21_5]; omega), hr8_21, h21_5]
  obtain ⟨ws, hws, hwsVal⟩ := Option.map_eq_some_iff.mp hFStop
  obtain ⟨s23, hs23, hpc23, hr8_23, hro23, hd23⟩ := step_loadInput_at (input := input)
    (by rw [hpc22, hpc21]; exact hR6 1 _ rfl) (by rw [hpc22, hpc21]; omega)
    (by rw [h22_8]; exact hws)
  have h23_8 : (reg s23 reg8).val = stopUVal := by rw [hr8_23, hwsVal]
  obtain ⟨s24, hs24, hpc24, hr6_24, hro24, hd24⟩ := step_add_at (input := input)
    (by rw [hpc23, hpc22, hpc21]; exact hR6 2 _ rfl) (by rw [hpc23, hpc22, hpc21]; omega)
  have h23Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg10 → r ≠ reg11 →
      reg s23 r = reg st r := fun r h6 h7 h8 h10 h11 => by
    rw [hro23 r h8, hro22 r h8, hro21 r h8 h7, h18Preserve r h6 h7 h10 h11]
  have h24_6 : (reg s24 reg6).val = tempArrBase n m N + 2 * N := by
    have h23_6 : (reg s23 reg6).val = tempArrBase n m N + N := by
      rw [hro23 reg6 (by intro h; cases h), hro22 reg6 (by intro h; cases h),
        hro21 reg6 (by intro h; cases h) (by intro h; cases h), h18_6]
    have h23_2 : (reg s23 reg2).val = N := by
      rw [h23Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2]
    rw [hr6_24, add_no_wrap _ _ (by rw [h23_6, h23_2]; omega), h23_6, h23_2]; omega
  obtain ⟨s25, hs25, hpc25, hr6_25, hro25, hd25⟩ := step_add_at (input := input)
    (by rw [hpc24, hpc23, hpc22, hpc21]; exact hR6 3 _ rfl)
    (by rw [hpc24, hpc23, hpc22, hpc21]; omega)
  have h25_6 : (reg s25 reg6).val = tempArrBase n m N + 2 * N + sp := by
    have h24_4 : (reg s24 reg4).val = sp := by
      rw [hro24 reg4 (by intro h; cases h),
        h23Preserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4]
    rw [hr6_25, add_no_wrap _ _ (by rw [h24_6, h24_4]; omega), h24_6, h24_4]
  have hSt25Lt : (reg s25 reg6).val < s25.data.size := by
    rw [h25_6, s25.data_size]; change tempArrBase n m N + 2 * N + sp < workCap; omega
  obtain ⟨hs26, hpc26, _⟩ := step_storeData_at (input := input)
    (by rw [hpc25, hpc24, hpc23, hpc22, hpc21]; exact hR6 4 _ rfl) hSt25Lt
    (by rw [hpc25, hpc24, hpc23, hpc22, hpc21]; omega)
  let s26 : State DomL :=
    { s25 with
      data := s25.data.set (reg s25 reg6).val (reg s25 reg8) hSt25Lt
      pc := s25.pc + 1
      data_size := by simp only [Array.size_set, s25.data_size] }
  have h26pc : s26.pc = 92 := by change s25.pc + 1 = 92; rw [hpc25, hpc24, hpc23, hpc22, hpc21]
  have h26Preserve : ∀ r : Fin 15, r ≠ reg6 → r ≠ reg7 → r ≠ reg8 → r ≠ reg10 → r ≠ reg11 →
      reg s26 r = reg st r := fun r h6 h7 h8 h10 h11 => by
    change reg s25 r = reg st r
    rw [hro25 r h6, hro24 r h6, h23Preserve r h6 h7 h8 h10 h11]
  have h26_8 : (reg s26 reg8).val = stopUVal := by
    change (reg s25 reg8).val = stopUVal
    rw [hro25 reg8 (by intro h; cases h), hro24 reg8 (by intro h; cases h), h23_8]
  obtain ⟨s27, hs27, hpc27, hr4_27, hro27, hd27⟩ := step_add_at (input := input)
    (by rw [h26pc]; exact hR6 5 _ rfl) (by rw [h26pc]; omega)
  have h27_4 : (reg s27 reg4).val = sp + 1 := by
    have h26_4 : (reg s26 reg4).val = sp := by
      rw [h26Preserve reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr4]
    have h26_1 : (reg s26 reg1).val = 1 := by
      rw [h26Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr4_27, add_no_wrap _ _ (by rw [h26_4, h26_1]; omega), h26_4, h26_1]
  obtain ⟨s28, hs28, hpc28, hr3_28, hro28, hd28⟩ := step_add_at (input := input)
    (by rw [hpc27, h26pc]; exact hR6 6 _ rfl) (by rw [hpc27, h26pc]; omega)
  have h28_3 : (reg s28 reg3).val = t + 1 := by
    have h27_3 : (reg s27 reg3).val = t := by
      rw [hro27 reg3 (by intro h; cases h),
        h26Preserve reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr3]
    have h27_1 : (reg s27 reg1).val = 1 := by
      rw [hro27 reg1 (by intro h; cases h),
        h26Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
    rw [hr3_28, add_no_wrap _ _ (by rw [h27_3, h27_1]; omega), h27_3, h27_1]
  obtain ⟨s29, hs29, hpc29, hr29R, hd29⟩ := step_goto_at (input := input)
    (by rw [hpc28, hpc27, h26pc]; exact hR6 7 _ rfl) (by omega)
  have h29EqR : ∀ r : Fin 15, reg s29 r = reg s28 r := fun r => by
    rcases s29 with ⟨ar, _, _, _, _⟩; rcases s28 with ⟨br, _, _, _, _⟩
    dsimp only at hr29R; subst ar; rfl
  have hSteps29 : Steps code input 29 st s29 := by
    have h1 : Steps code input 12 st s12 :=
      hs3.append (hs8.append (Steps.cons hs9 (Steps.cons hs10 (Steps.cons hs11 (steps_1_of_step hs12)))))
    have h2 : Steps code input 6 s12 s18 :=
      hs15.append (Steps.cons hs16 (Steps.cons hs17 (steps_1_of_step hs18)))
    have h3 : Steps code input 8 s18 s26 :=
      hs21.append (Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24 (Steps.cons hs25 (steps_1_of_step hs26)))))
    have h4 : Steps code input 3 s26 s29 :=
      Steps.cons hs27 (Steps.cons hs28 (steps_1_of_step hs29))
    rw [show 29 = 12 + (6 + (8 + 3)) by omega]
    exact h1.append (h2.append (h3.append h4))
  have hd29Eq : ∀ j : Nat, s29.data[j]? = s26.data[j]? := fun _ => by rw [hd29, hd28, hd27]
  refine ⟨s29, hSteps29, hpc29, fun j hj1 hj2 hj3 hj4 => ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hd29Eq]
    change (s25.data.set (reg s25 reg6).val (reg s25 reg8) hSt25Lt)[j]? = _
    rw [Array.getElem?_set_ne hSt25Lt (by rw [h25_6]; exact hj4.symm),
      hd25, hd24, hd23, hd22, hd21]
    exact h18_Fr j hj1 hj2 hj3
  · rw [hd29Eq]
    change (s25.data.set (reg s25 reg6).val (reg s25 reg8) hSt25Lt)[storedBase N + 18 * u]?.map Fin.val = _
    rw [Array.getElem?_set_ne hSt25Lt (by rw [h25_6]; unfold storedBase; omega),
      hd25, hd24, hd23, hd22, hd21]
    exact h18_P
  · rw [hd29Eq]
    change (s25.data.set (reg s25 reg6).val (reg s25 reg8) hSt25Lt)[storedBase N + 18 * u + 1]?.map Fin.val = _
    rw [Array.getElem?_set_ne hSt25Lt (by rw [h25_6]; unfold storedBase; omega),
      hd25, hd24, hd23, hd22, hd21]
    exact h18_J
  · rw [hd29Eq]
    change (s25.data.set (reg s25 reg6).val (reg s25 reg8) hSt25Lt)[tempArrBase n m N + N + sp]?.map Fin.val = _
    rw [Array.getElem?_set_ne hSt25Lt (by rw [h25_6]; omega),
      hd25, hd24, hd23, hd22, hd21]
    exact h18_N
  · rw [hd29Eq]
    change ((s25.data.set (reg s25 reg6).val (reg s25 reg8) hSt25Lt)[tempArrBase n m N + 2 * N + sp]?).map Fin.val = _
    rw [← h25_6]; simp [hSt25Lt]; exact h26_8
  · rw [h29EqR, hro28 reg0 (by intro h; cases h), hro27 reg0 (by intro h; cases h),
      h26Preserve reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr0]
  · rw [h29EqR, hro28 reg1 (by intro h; cases h), hro27 reg1 (by intro h; cases h),
      h26Preserve reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr1]
  · rw [h29EqR, hro28 rMeta (by intro h; cases h), hro27 rMeta (by intro h; cases h),
      h26Preserve rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hrm]
  · rw [h29EqR, hro28 reg2 (by intro h; cases h), hro27 reg2 (by intro h; cases h),
      h26Preserve reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), hr2]
  · rw [h29EqR, h28_3]
  · rw [h29EqR, hro28 reg4 (by intro h; cases h), h27_4]

theorem run_dfsStack {input : Input DomL}
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
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hInv : ∀ u : Fin r.out.tables.next,
      (s0.data[tempArrBase H.vertexCount H.arcCount r.out.tables.next +
        r.index.reader.entry (Fin.cast (nodeCount_eq_next r.index.ok).symm u)]?).map Fin.val =
          some u.val) :
    ∃ steps : Nat, ∃ t : State DomL, steps ≤ 100 * r.out.tables.next + 10 ∧
      run (dfsStackPhase (hi := hi) (hw := hw) h100).code input steps (Phase.initial s0) =
        some ⟨t, steps⟩ ∧
      ForestReady t flat increasing covers rankArc r nGlobal ∧
      (∀ j, ((19 * r.out.tables.next ≤ j ∧ j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * r.out.tables.next ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  let n := H.vertexCount
  let m := H.arcCount
  let N := r.out.tables.next
  let hN : N = nodeCount (orderedConfig p large) r.out := (nodeCount_eq_next r.index.ok).symm
  let rd := r.index.reader
  let x := PaperB.EX24.FinalDFS.packedInput r.index.ok
  let B := buildActualSweepBundle H flat increasing covers rankArc r
  have hNLe : N ≤ n + 1 := hN ▸ nodeCount_le r.index.ok
  have hStage1 : tempArrBase n m N + 3 * N ≤ workCap :=
    Nat.le_trans (tempArrBase_stage1_le hNLe) hWork
  have hTempEq : tempArrBase n m N = metaArrBase n m N + 48 := rfl
  have hMetaEq := metaArrBase_eq n m N
  have hBSize : B.F.size = N := B.G.size_eq
  have hBValid := B.G.layout.valid
  have hPre := dfs_preorder_bijection r
  have hLtEntry := hPre.1
  have hInjEntry := hPre.2.1
  have hSpanEntry := hPre.2.2
  have hRdEntryLt : ∀ u : Fin N, rd.entry (Fin.cast hN u) < N := hLtEntry
  have hRdEntryInj : ∀ u v : Fin N, rd.entry (Fin.cast hN u) = rd.entry (Fin.cast hN v) → u = v :=
    fun u v he => hInjEntry u v he
  let rdEntryFin : Fin (nodeCount (orderedConfig p large) r.out) → Nat := rd.entry
  have hRdSpan : ∀ u : Fin N,
      rd.entry (Fin.cast hN u) < rd.stop (Fin.cast hN u) ∧ rd.stop (Fin.cast hN u) ≤ N :=
    hSpanEntry
  let ph := dfsStackPhase (hi := hi) (hw := hw) h100
  have hLSetup : (dfsSetupInstrs (bits := bits) h100).length = 5 := rfl
  have hLPop : (dfsPopLoopInstrs (bits := bits) h100).length = 12 := by
    simp [dfsPopLoopInstrs, metaLoadInstrs]
  have hLDec : (dfsDecodeUInstrs (bits := bits) h100).length = 6 := by
    simp [dfsDecodeUInstrs, metaLoadInstrs]
  have hLIse : (dfsIsEmptyInstrs (bits := bits)).length = 4 := rfl
  have hLNea : (dfsNonEmptyAInstrs (bits := bits) h100).length = 24 := by
    simp [dfsNonEmptyAInstrs, metaLoadInstrs, mul18Instrs]
  have hLChk : (dfsCheckLen2Instrs (bits := bits)).length = 13 := by
    simp [dfsCheckLen2Instrs, mul18Instrs]
  have hLUse : (dfsUsePInstrs (bits := bits)).length = 1 := rfl
  have hLWrt : (dfsWritePJInstrs (bits := bits) h100).length = 29 := by
    simp [dfsWritePJInstrs, metaLoadInstrs, mul18Instrs]
  have hTotLen : (dfsStackInstrs (bits := bits) h100).length = 95 := by
    unfold dfsStackInstrs
    simp only [List.length_append, hLSetup, List.length_singleton, hLPop, hLDec, hLIse,
      hLNea, hLChk, hLUse, hLWrt]
  have hCodeSz : ph.code.size = 96 := by
    change ((dfsStackInstrs (bits := bits) h100 ++ [Instr.halt]).toArray : Program DomL).size = 96
    simp [hTotLen]
  have hPhasePl : Placed ph.code 0 (dfsStackInstrs (bits := bits) h100) := Placed_toArray_halt
  have hPlSetup : Placed ph.code 0 (dfsSetupInstrs (bits := bits) h100) := by
    unfold dfsStackInstrs at hPhasePl; exact Placed_append_left hPhasePl
  have hR0 := Placed_append_right (by unfold dfsStackInstrs at hPhasePl; exact hPhasePl)
  rw [hLSetup] at hR0
  have hAtOuter : ph.code[5]? = some (.branchLt reg3 reg2 6 95) := hR0 0 _ rfl
  have hR1 := Placed_append_right hR0
  rw [show ([Instr.branchLt reg3 reg2 6 95] : List (Instr bits 15)).length = 1 by rfl] at hR1
  have hPlPop : Placed ph.code 6 (dfsPopLoopInstrs (bits := bits) h100) := Placed_append_left hR1
  have hR2 := Placed_append_right hR1
  rw [hLPop] at hR2
  have hPlDec : Placed ph.code 18 (dfsDecodeUInstrs (bits := bits) h100) := Placed_append_left hR2
  have hR3 := Placed_append_right hR2
  rw [hLDec] at hR3
  have hPlIse : Placed ph.code 24 (dfsIsEmptyInstrs (bits := bits)) := Placed_append_left hR3
  have hR4 := Placed_append_right hR3
  rw [hLIse] at hR4
  have hPlNea : Placed ph.code 28 (dfsNonEmptyAInstrs (bits := bits) h100) := Placed_append_left hR4
  have hR5 := Placed_append_right hR4
  rw [hLNea] at hR5
  have hPlChk : Placed ph.code 52 (dfsCheckLen2Instrs (bits := bits)) := Placed_append_left hR5
  have hR6 := Placed_append_right hR5
  rw [hLChk] at hR6
  have hPlUse : Placed ph.code 65 (dfsUsePInstrs (bits := bits)) := Placed_append_left hR6
  have hPlWrt : Placed ph.code 66 (dfsWritePJInstrs (bits := bits) h100) := by
    have hR7 := Placed_append_right hR6
    rw [hLUse] at hR7
    exact hR7
  obtain ⟨s1, hs1, hpc1, hd1, hr0_1, hr1_1, hrm_1, hr2_1, hr3_1, hr4_1⟩ :=
    dfsSetup_spec (input := input) (n := n) (m := m) (N := N) (nGlobal := nGlobal)
      h100 hPlSetup (by rw [hCodeSz]; omega) (by omega)
      (Phase.initial s0) rfl (hMeta.preserve hMeta.rMeta_eq hMeta.r0_zero hMeta.r1_one (fun _ _ => rfl))
  have hLoop : ∀ (rem t sp stepsAcc : Nat) (stk0 : List (Fin N)) (st : State DomL),
      t + rem = N → ∀ (hLen : stk0.length = sp), stepsAcc + 12 * sp ≤ 96 * t + 5 →
      st.pc = 5 →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase n m N →
      (reg st reg2).val = N → (reg st reg3).val = t → (reg st reg4).val = sp →
      (∀ i, i < 22 → st.data[metaArrBase n m N + i]? = s0.data[metaArrBase n m N + i]?) →
      (∀ u : Fin N, (st.data[tempArrBase n m N + rd.entry (Fin.cast hN u)]?).map Fin.val = some u.val) →
      (∀ i (hi : i < sp),
        (st.data[tempArrBase n m N + N + i]?).map Fin.val =
          some (stk0[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_eq hLen.symm))).val ∧
        (st.data[tempArrBase n m N + 2 * N + i]?).map Fin.val =
          some (rd.stop (Fin.cast hN (stk0[i]'(Nat.lt_of_lt_of_le hi (Nat.le_of_eq hLen.symm)))))) →
      (∀ i j (hi : i < stk0.length) (hj : j < stk0.length), i < j →
        rd.entry (Fin.cast hN (stk0[i]'hi)) < rd.entry (Fin.cast hN (stk0[j]'hj))) →
      (∀ w : Fin N, w ∈ stk0 ↔ rd.entry (Fin.cast hN w) < t ∧ t ≤ rd.stop (Fin.cast hN w)) →
      (∀ w : Fin N, rd.entry (Fin.cast hN w) < t →
        (st.data[w.val]?).map Fin.val = some (B.F.depthOf w.val) ∧
        (st.data[storedBase N + 18 * w.val]?).map Fin.val = some (B.F.parentOf w.val) ∧
        (st.data[storedBase N + 18 * w.val + 1]?).map Fin.val = some (B.F.jumpOf w.val)) →
      (∀ j, ((19 * N ≤ j ∧ j < tempArrBase n m N) ∨ tempArrBase n m N + 3 * N ≤ j) →
        st.data[j]? = s0.data[j]?) →
      ∃ stepsRem out, stepsAcc + stepsRem ≤ 96 * N + 6 ∧ Steps ph.code input stepsRem st out ∧
        out.pc = 95 ∧ ForestReady out flat increasing covers rankArc r nGlobal ∧
        (∀ j, ((19 * N ≤ j ∧ j < tempArrBase n m N) ∨ tempArrBase n m N + 3 * N ≤ j) →
          out.data[j]? = s0.data[j]?) := by
    intro rem
    induction rem with
    | zero =>
      intro t sp stepsAcc stk0 st hSum hLen hAcc hpc hr0 hr1 hrm hr2 hr3 hr4
        hMetaData hInvSt hStkAt hStkInc hStkMem hVis hFr
      have htN : t = N := by omega
      obtain ⟨out, hsOut, hOutPc, hOutR, hOutD⟩ := step_branchLt_at (input := input)
        (by rw [hpc]; exact hAtOuter) (by split <;> rw [hCodeSz] <;> omega)
      have hFalse : ¬ (reg st reg3).val < (reg st reg2).val := by rw [hr3, hr2]; omega
      rw [ite_eq_right hFalse] at hOutPc
      have hOutEqR : ∀ r : Fin 15, reg out r = reg st r := fun r => by
        rcases out with ⟨ar, _, _, _, _⟩; rcases st with ⟨br, _, _, _, _⟩
        dsimp only at hOutR; subst ar; rfl
      have hForest : ForestReady out flat increasing covers rankArc r nGlobal := by
        refine ⟨hMeta.preserve (by rw [hOutEqR]; exact hrm) (by rw [hOutEqR]; exact hr0)
            (by rw [hOutEqR]; exact hr1) (fun i hi22 => by rw [hOutD]; exact hMetaData i hi22),
          fun u => ?_, fun u => ?_, fun u => ?_⟩
        · rw [hOutD]; exact (hVis u (by rw [htN]; exact hLtEntry u)).1
        · rw [hOutD]; exact (hVis u (by rw [htN]; exact hLtEntry u)).2.1
        · rw [hOutD]; exact (hVis u (by rw [htN]; exact hLtEntry u)).2.2
      exact ⟨1, out, by omega, steps_1_of_step hsOut, hOutPc, hForest,
        fun j hj => by rw [hOutD]; exact hFr j hj⟩
    | succ rem ih =>
      intro t sp stepsAcc stk0 st hSum hLen hAcc hpc hr0 hr1 hrm hr2 hr3 hr4
        hMetaData hInvSt hStkAt hStkInc hStkMem hVis hFr
      have htLtN : t < N := by omega
      obtain ⟨sA, hsA, hpcA, hrAR, hdA⟩ := step_branchLt_at (input := input)
        (by rw [hpc]; exact hAtOuter) (by split <;> rw [hCodeSz] <;> omega)
      have hTrue : (reg st reg3).val < (reg st reg2).val := by rw [hr3, hr2]; omega
      rw [ite_eq_left hTrue] at hpcA
      have hAEqR : ∀ r : Fin 15, reg sA r = reg st r := fun r => by
        rcases sA with ⟨ar, _, _, _, _⟩; rcases st with ⟨br, _, _, _, _⟩
        dsimp only at hrAR; subst ar; rfl
      have hMetaT_A : (sA.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N) := by
        rw [hdA, hMetaData mIdxTempBase (by decide)]; exact hMeta.meta_tempBase
      have hCastEq : ∀ (w : Fin N), Fin.cast hN w = Fin.cast (nodeCount_eq_next r.index.ok).symm w := fun _ => rfl
      have hSpLeT : sp ≤ t := by
        have hMap : ((List.finRange sp).map (fun i : Fin sp =>
            rd.entry (Fin.cast hN (stk0[i.val]'(by omega))))).length = sp := by simp
        rw [← hMap, ← List.length_range (n := t)]
        apply list_nodup_length_le_of_subset
        · dsimp only [List.Nodup]
          rw [List.pairwise_map]
          exact List.Pairwise.imp (fun {a b} (hab : a ≠ b) => by
            rcases Nat.lt_trichotomy a.val b.val with hlt | heq | hgt
            · exact Nat.ne_of_lt (hStkInc a.val b.val (by omega) (by omega) hlt)
            · exact False.elim (hab (Fin.ext heq))
            · exact Nat.ne_of_gt (hStkInc b.val a.val (by omega) (by omega) hgt))
            (List.nodup_finRange sp)
        · intro v hv
          rcases List.mem_map.mp hv with ⟨i, _, rfl⟩
          apply List.mem_range.mpr
          have hiMem : stk0[i.val]'(by omega) ∈ stk0 := List.getElem_mem _
          exact (hStkMem _).mp hiMem |>.1
      have hDecStop : ∀ i j (hi : i < stk0.length) (hj : j < stk0.length), i ≤ j →
          rd.stop (Fin.cast hN (stk0[j]'hj)) ≤ rd.stop (Fin.cast hN (stk0[i]'hi)) := by
        have hDec := dfs_stack_decreasing_stop rd
          (fun w => by
            have h1 := hLtEntry (Fin.cast hN.symm w)
            have h2 : Fin.cast hN (Fin.cast hN.symm w) = w := Fin.ext rfl
            rw [h2] at h1
            exact Nat.lt_of_lt_of_eq h1 hN)
          (fun u v he =>
            Fin.ext (congrArg (fun x : Fin N => x.val) (hInjEntry (Fin.cast hN.symm u) (Fin.cast hN.symm v) (by
              have h1 : Fin.cast hN (Fin.cast hN.symm u) = u := Fin.ext rfl
              have h2 : Fin.cast hN (Fin.cast hN.symm v) = v := Fin.ext rfl
              rw [h1, h2]; exact he))))
          (fun w => by
            have h1 := hSpanEntry (Fin.cast hN.symm w)
            have h2 : Fin.cast hN (Fin.cast hN.symm w) = w := Fin.ext rfl
            rw [h2] at h1
            exact ⟨h1.1, Nat.le_trans h1.2 (Nat.le_of_eq hN)⟩)
          (stk := stk0.map (Fin.cast hN))
          (fun i j hi hj hij => by
            simp only [List.length_map] at hi hj
            rw [List.getElem_map, List.getElem_map]
            exact hStkInc i j hi hj hij)
          (fun w => by
            let wf : Fin N := Fin.cast hN.symm w
            have hwEq : w = Fin.cast hN wf := by apply Fin.ext; rfl
            rw [hwEq, List.mem_map]
            constructor
            · rintro ⟨u, hu, huEq⟩
              have : u = wf := Fin.ext (congrArg (fun z : Fin (nodeCount (orderedConfig p large) r.out) => z.val) huEq)
              subst this; exact (hStkMem wf).mp hu
            · intro hw
              exact ⟨wf, (hStkMem wf).mpr hw, rfl⟩)
        intro i j hi hj hij
        have hRes := hDec i j (by simp [hi]) (by simp [hj]) hij
        rw [List.getElem_map, List.getElem_map] at hRes
        exact hRes
      obtain ⟨sp', popSteps, sB, hSpLe, hPopLe, hsPop, hpcB, hdB, hb0, hb1, hbm, hb2, hb3, hb4, hbMemFin⟩ :=
        dfsPopLoop_spec (input := input) (h100 := h100) (n := n) (m := m) (N := N) (t := t)
          (fun w => rd.entry (Fin.cast hN w)) (fun w => rd.stop (Fin.cast hN w))
          hPlPop (by rw [hCodeSz]; omega) (by omega)
          stk0 hDecStop hStkMem
          sp sA (by omega) (by omega) hpcA
          (by rw [hAEqR]; exact hr0) (by rw [hAEqR]; exact hr1) (by rw [hAEqR]; exact hrm)
          (by rw [hAEqR]; exact hr2) (by rw [hAEqR]; exact hr3) (by rw [hAEqR]; exact hr4)
          hMetaT_A
          (fun i _ => by rw [hdA]; exact (hStkAt i (by omega)).2)
          (fun w ⟨he, hs⟩ => by
            rw [← hLen, List.take_length]
            exact (hStkMem w).mpr ⟨he, Nat.le_of_lt hs⟩)
      have hBData : sB.data = st.data := by rw [hdB, hdA]
      obtain ⟨u, huEntry⟩ := fin_entry_surjective (fun w : Fin N => rd.entry (Fin.cast hN w))
        hLtEntry hInjEntry t htLtN
      have hMetaT_B : (sB.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N) := by
        rw [hBData, hMetaData mIdxTempBase (by decide)]; exact hMeta.meta_tempBase
      have hInvAtU : (sB.data[tempArrBase n m N + t]?).map Fin.val = some u.val := by
        rw [hBData, ← huEntry]; exact hInvSt u
      obtain ⟨sC, hsC, hpcC, hdC, hc0, hc1, hcm, hc2, hc3, hc4, hc5⟩ :=
        dfsDecodeU_spec (input := input) h100 u.val hPlDec (by rw [hCodeSz]; omega) (by omega) htLtN sB hpcB
          hb0 hb1 hbm hb2 hb3 hb4 hMetaT_B hInvAtU
      have hCData : sC.data = st.data := by rw [hdC, hBData]
      have hTopSpec := dfs_stack_top_parent rd
        (fun a b he => Fin.ext (congrArg (fun z : Fin N => z.val)
          (hInjEntry (Fin.cast hN.symm a) (Fin.cast hN.symm b) (by
            have h1 : Fin.cast hN (Fin.cast hN.symm a) = a := Fin.ext rfl
            have h2 : Fin.cast hN (Fin.cast hN.symm b) = b := Fin.ext rfl
            rw [h1, h2]; exact he))))
        (fun a => by
          have h1 := hSpanEntry (Fin.cast hN.symm a)
          have h2 : Fin.cast hN (Fin.cast hN.symm a) = a := Fin.ext rfl
          rw [h2] at h1
          exact ⟨h1.1, Nat.le_trans h1.2 (Nat.le_of_eq hN)⟩)
        (Fin.cast hN u)
        (stk := (stk0.take sp').map (Fin.cast hN))
        (fun i j hi hj hij => by
          simp only [List.length_map, List.length_take] at hi hj
          rw [List.getElem_map, List.getElem_map, List.getElem_take, List.getElem_take]
          exact hStkInc i j (by omega) (by omega) hij)
        (fun w => by
          let wf : Fin N := Fin.cast hN.symm w
          have hwEq : w = Fin.cast hN wf := by apply Fin.ext; rfl
          rw [hwEq, List.mem_map]
          constructor
          · rintro ⟨v, hv, hvEq⟩
            have : v = wf := Fin.ext (congrArg (fun z : Fin (nodeCount (orderedConfig p large) r.out) => z.val) hvEq)
            subst this
            have hm := (hbMemFin wf).mp hv
            rw [huEntry]; exact hm
          · intro hw
            rw [huEntry] at hw
            exact ⟨wf, (hbMemFin wf).mpr hw, rfl⟩)
      have hSp'Le : sp' ≤ stk0.length := by omega
      have hTakeLen : (stk0.take sp').length = sp' := by simp [List.length_take, Nat.min_eq_left hSp'Le]
      -- Now split on `0 < sp'` (`nonEmpty`) vs `sp' = 0` (`isEmpty`):
      have hMid : ∃ (midSteps : Nat) (sM : State DomL), midSteps ≤ 38 ∧
          Steps ph.code input midSteps sC sM ∧ sM.pc = 66 ∧
          (∀ j, j ≠ u.val → sM.data[j]? = st.data[j]?) ∧
          (sM.data[u.val]?).map Fin.val = some (B.F.depthOf u.val) ∧
          (reg sM reg0).val = 0 ∧ (reg sM reg1).val = 1 ∧
          (reg sM rMeta).val = metaArrBase n m N ∧
          (reg sM reg2).val = N ∧ (reg sM reg3).val = t ∧ (reg sM reg4).val = sp' ∧
          (reg sM reg5).val = u.val ∧
          (reg sM reg8).val = B.F.parentOf u.val ∧
          (reg sM reg9).val = B.F.jumpOf u.val := by
        by_cases hSpPos : 0 < sp'
        · rw [ite_eq_left hSpPos] at hpcC
          have hTopNe : 0 < ((stk0.take sp').map (Fin.cast hN)).length := by
            rw [List.length_map, hTakeLen]; exact hSpPos
          obtain ⟨hUnotRoot, hTopPar⟩ := hTopSpec.2 hTopNe
          have huPos : 0 < u.val := by
            have hR0 := dfs_root_eq_zero flat increasing covers rankArc r
            cases hu0 : u.val with
            | zero => exfalso; exact hUnotRoot (Fin.ext (by change u.val = x.root.val; rw [hu0, hR0]))
            | succ _ => omega
          let pFin : Fin N := stk0[sp' - 1]'(by omega)
          have hPEqX : Fin.cast hN pFin = x.parent.read (Fin.cast hN u) := by
            have hG : ((stk0.take sp').map (Fin.cast hN))[(stk0.take sp').length - 1]'(by
                simp; omega) = x.parent.read (Fin.cast hN u) := by
              simpa [List.length_map] using hTopPar
            have hGVal := congrArg (fun z : Fin (nodeCount (orderedConfig p large) r.out) => z.val) hG
            simp only [List.getElem_map, List.getElem_take, hTakeLen] at hGVal
            exact Fin.ext hGVal
          have hPEqB : pFin.val = B.F.parentOf u.val := by
            have hMatch := (reader_matches_bundle_forest flat increasing covers rankArc r u).1
            dsimp only [x] at hPEqX
            rw [← hPEqX] at hMatch
            exact hMatch
          have hPMemTake : pFin ∈ stk0.take sp' := by
            rw [show pFin = (stk0.take sp')[sp' - 1]'(by rw [hTakeLen]; omega) by
              rw [List.getElem_take]]
            exact List.getElem_mem _
          have hPEntLt : rd.entry (Fin.cast hN pFin) < t := (hbMemFin pFin).mp hPMemTake |>.1
          have hPVis := hVis pFin hPEntLt
          let dPVal := B.F.depthOf pFin.val
          have hDUVal : B.F.depthOf u.val = dPVal + 1 := by
            have hM1 : (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN u) =
                B.F.depthOf u.val :=
              (reader_matches_bundle_forest flat increasing covers rankArc r u).2
            have hM2 : (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN pFin) =
                B.F.depthOf pFin.val :=
              (reader_matches_bundle_forest flat increasing covers rankArc r pFin).2
            have hStep := rd.input_ok.depth_step (Fin.cast hN u) hUnotRoot
            dsimp only [x] at hPEqX
            rw [← hPEqX] at hStep
            dsimp only [dPVal]
            rw [← hM1, ← hM2]
            exact hStep
          have hDP_lt : dPVal + 1 < 2 ^ bits := by
            obtain ⟨_, hInvB⟩ := hBValid.exists_forestInvariant
            have hN0 := hInvB.depthOf_le_self (by rw [hBSize]; exact u.isLt)
            omega
          let aVal := B.F.jumpOf pFin.val
          have haLt : aVal < N := by rw [← hBSize]; exact hBValid.jumpOf_lt_size (by rw [hBSize]; exact pFin.isLt)
          let aFin : Fin N := ⟨aVal, haLt⟩
          have hJA : JumpChain B.F aVal pFin.val := jumpForest_jump_ancestor hBValid pFin.val (by rw [hBSize]; exact pFin.isLt)
          have hAncAP : IsForestAncestor x.parent.read (Fin.cast hN aFin) (Fin.cast hN pFin) :=
            isForestAncestor_of_jumpChain flat increasing covers rankArc r hJA haLt pFin.isLt
          have hIntAP := (isForestAncestor_iff_rd_interval rd (Fin.cast hN aFin) (Fin.cast hN pFin)).mp hAncAP
          have hAEntLt : rd.entry (Fin.cast hN aFin) < t := Nat.lt_of_le_of_lt hIntAP.1 hPEntLt
          have haNe : aVal ≠ u.val := by intro he; have hE := congrArg (fun z => rd.entry (Fin.cast hN z)) (Fin.ext he : aFin = u); rw [huEntry] at hE; omega
          have hdA_le : B.F.depthOf aVal ≤ dPVal := by
            have hDl := rd.input_ok.depth_le_of_isForestAncestor hAncAP
            have hMA : (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN aFin) =
                B.F.depthOf aVal :=
              (reader_matches_bundle_forest flat increasing covers rankArc r aFin).2
            have hMP : (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN pFin) =
                B.F.depthOf pFin.val :=
              (reader_matches_bundle_forest flat increasing covers rankArc r pFin).2
            dsimp only [dPVal]
            rw [← hMA, ← hMP]
            exact hDl
          have hAVis := hVis aFin hAEntLt
          have hMetaT_C : (sC.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N) := by
            rw [hCData, hMetaData mIdxTempBase (by decide)]; exact hMeta.meta_tempBase
          have hMetaS_C : (sC.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N) := by
            rw [hCData, hMetaData mIdxStoredBase (by decide)]; exact hMeta.meta_storedBase
          obtain ⟨sD, hsD, hpcD, hDFr, hDU, hd0, hd1, hdm, hd2, hd3, hd4, hd5, hd8, hd10, hd12, hd7⟩ :=
            dfsNonEmptyA_spec (input := input) h100 hPlNea (by rw [hCodeSz]; omega) hStage1
              u.isLt pFin.isLt haLt haNe hSpPos (by omega) hdA_le hDP_lt sC hpcC
              hc0 hc1 hcm hc2 hc3 hc4 hc5
              hMetaT_C hMetaS_C
              (by rw [hCData]; exact (hStkAt (sp' - 1) (by omega)).1)
              (by rw [hCData]; exact hPVis.1)
              (by rw [hCData]; exact hPVis.2.2)
              (by rw [hCData]; exact hAVis.1)
          have hRule := validJumpForest_skew_rule hBValid u.val huPos (by rw [hBSize]; exact u.isLt)
          dsimp only at hRule
          rw [← hPEqB] at hRule
          change B.F.jumpOf u.val =
            (let b := B.F.jumpOf aVal
             let len1 := dPVal - B.F.depthOf aVal
             let len2 := B.F.depthOf aVal - B.F.depthOf b
             if 0 < len1 ∧ len1 = len2 then b else pFin.val) at hRule
          by_cases hLen1Pos : 0 < dPVal - B.F.depthOf aVal
          · rw [ite_eq_left hLen1Pos] at hpcD
            let bVal := B.F.jumpOf aVal
            have hbLt : bVal < N := by rw [← hBSize]; exact hBValid.jumpOf_lt_size (by rw [hBSize]; exact haLt)
            let bFin : Fin N := ⟨bVal, hbLt⟩
            have hJB : JumpChain B.F bVal aVal := jumpForest_jump_ancestor hBValid aVal (by rw [hBSize]; exact haLt)
            have hAncBA : IsForestAncestor x.parent.read (Fin.cast hN bFin) (Fin.cast hN aFin) :=
              isForestAncestor_of_jumpChain flat increasing covers rankArc r hJB hbLt haLt
            have hIntBA := (isForestAncestor_iff_rd_interval rd (Fin.cast hN bFin) (Fin.cast hN aFin)).mp hAncBA
            have hBEntLt : rd.entry (Fin.cast hN bFin) < t := Nat.lt_of_le_of_lt hIntBA.1 hAEntLt
            have hbNe : bVal ≠ u.val := by intro he; have hE := congrArg (fun z => rd.entry (Fin.cast hN z)) (Fin.ext he : bFin = u); rw [huEntry] at hE; omega
            have hdB_le : B.F.depthOf bVal ≤ B.F.depthOf aVal := by
              have hDl := rd.input_ok.depth_le_of_isForestAncestor hAncBA
              have hMA : (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN aFin) =
                  B.F.depthOf aVal :=
                (reader_matches_bundle_forest flat increasing covers rankArc r aFin).2
              have hMB : (PaperB.EX24.FinalDFS.packedInput r.index.ok).depth.read (Fin.cast hN bFin) =
                  B.F.depthOf bVal :=
                (reader_matches_bundle_forest flat increasing covers rankArc r bFin).2
              rw [← hMB, ← hMA]
              exact hDl
            have hBVis := hVis bFin hBEntLt
            have haNe2 : aVal ≠ u.val := haNe
            have hJumpA_D : (sD.data[storedBase N + 18 * aVal + 1]?).map Fin.val = some bVal := by
              rw [hDFr _ (by unfold storedBase; omega), hCData]; exact hAVis.2.2
            have hDa_D : (sD.data[aVal]?).map Fin.val = some (B.F.depthOf aVal) := by
              rw [hDFr _ haNe2, hCData]; exact hAVis.1
            have hDb_D : (sD.data[bVal]?).map Fin.val = some (B.F.depthOf bVal) := by
              rw [hDFr _ hbNe, hCData]; exact hBVis.1
            obtain ⟨chkK, sE, hChkLe, hsChk, hpcE, hdE, he0, he1, hem, he2, he3, he4, he5, he8, he9⟩ :=
              dfsCheckLen2_spec (input := input) hPlChk (by rw [hCodeSz]; omega) hStage1 haLt hbLt hdB_le
                sD hpcD hd0 hd1 hdm hd2 hd3 hd4 hd5 hd7 hd8 hd10 hd12 hJumpA_D hDa_D hDb_D
            by_cases hEqLen : dPVal - B.F.depthOf aVal = B.F.depthOf aVal - B.F.depthOf bVal
            · rw [ite_eq_left hEqLen] at hpcE
              have hJRule : B.F.jumpOf u.val = bVal := by rw [hRule, ite_eq_left ⟨hLen1Pos, hEqLen⟩]
              refine ⟨24 + chkK, sE, by omega, hsD.append hsChk, hpcE,
                fun j hj => by rw [hdE, hDFr j hj, hCData],
                by rw [hdE, hDUVal]; exact hDU,
                he0, he1, hem, he2, he3, he4, he5, by rw [he8, hPEqB], by rw [he9, hJRule]⟩
            · rw [ite_eq_right hEqLen] at hpcE
              obtain ⟨sF, hsF, hpcF, hdF, hf0, hf1, hfm, hf2, hf3, hf4, hf5, hf8, hf9⟩ :=
                dfsUseP_spec (input := input) hPlUse (by rw [hCodeSz]; omega) sE hpcE he0 he1 hem he2 he3 he4 he5 he8
              have hJRule : B.F.jumpOf u.val = pFin.val := by
                rw [hRule, ite_eq_right (fun ⟨_, heq⟩ => hEqLen heq)]
              refine ⟨24 + chkK + 1, sF, by omega, (hsD.append hsChk).append hsF, hpcF,
                fun j hj => by rw [hdF, hdE, hDFr j hj, hCData],
                by rw [hdF, hdE, hDUVal]; exact hDU,
                hf0, hf1, hfm, hf2, hf3, hf4, hf5, by rw [hf8, hPEqB], by rw [hf9, hJRule]⟩
          · rw [ite_eq_right hLen1Pos] at hpcD
            obtain ⟨sF, hsF, hpcF, hdF, hf0, hf1, hfm, hf2, hf3, hf4, hf5, hf8, hf9⟩ :=
              dfsUseP_spec (input := input) hPlUse (by rw [hCodeSz]; omega) sD hpcD hd0 hd1 hdm hd2 hd3 hd4 hd5 hd8
            have hJRule : B.F.jumpOf u.val = pFin.val := by
              rw [hRule, ite_eq_right (fun ⟨hpos, _⟩ => hLen1Pos hpos)]
            refine ⟨25, sF, by omega, hsD.append hsF, hpcF,
              fun j hj => by rw [hdF, hDFr j hj, hCData],
              by rw [hdF, hDUVal]; exact hDU,
              hf0, hf1, hfm, hf2, hf3, hf4, hf5, by rw [hf8, hPEqB], by rw [hf9, hJRule]⟩
        · have hSpZero : sp' = 0 := by omega
          rw [ite_eq_right hSpPos] at hpcC
          have hRootU : Fin.cast hN u = x.root := hTopSpec.1 (by simp [hSpZero])
          have hR0 := dfs_root_eq_zero flat increasing covers rankArc r
          have hu0 : u.val = 0 := by change (Fin.cast hN u).val = 0; rw [hRootU, hR0]
          obtain ⟨hP0, hJ0, hD0⟩ := validJumpForest_root_zero hBValid
          obtain ⟨sD, hsD, hpcD, hDFr, hDU, hd0, hd1, hdm, hd2, hd3, hd4, hd5, hd8, hd9⟩ :=
            dfsIsEmpty_spec (input := input) hPlIse (by rw [hCodeSz]; omega) u.isLt (by omega) sC hpcC
              hc0 hc1 hcm hc2 hc3 (by rw [hc4, hSpZero]) hc5
          refine ⟨4, sD, by omega, hsD, hpcD, fun j hj => by rw [hDFr j hj, hCData],
            by rw [hu0] at hDU ⊢; rw [hD0]; exact hDU,
            hd0, hd1, hdm, hd2, hd3, by rw [hd4, hSpZero], hd5, by rw [hd8, hu0, hP0], by rw [hd9, hu0, hJ0]⟩
      obtain ⟨midSteps, sM, hMidLe, hsMid, hpcM, hMFr, hMDepth, hm0, hm1, hmm, hm2, hm3, hm4, hm5, hm8, hm9⟩ := hMid
      have hSp'LtN : sp' < N := by omega
      have hMDataNeU : ∀ j, j ≠ u.val → sM.data[j]? = st.data[j]? := hMFr
      have hMetaS_M : (sM.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N) := by
        rw [hMDataNeU _ (by change metaArrBase n m N + 4 ≠ u.val; omega), hMetaData mIdxStoredBase (by decide)]
        exact hMeta.meta_storedBase
      have hMetaT_M : (sM.data[metaArrBase n m N + mIdxTempBase]?).map Fin.val = some (tempArrBase n m N) := by
        rw [hMDataNeU _ (by change metaArrBase n m N + 13 ≠ u.val; omega), hMetaData mIdxTempBase (by decide)]
        exact hMeta.meta_tempBase
      have hMetaF_M : (sM.data[metaArrBase n m N + mIdxFStopInBase]?).map Fin.val = some (4 + n + 3 * N) := by
        rw [hMDataNeU _ (by change metaArrBase n m N + 18 ≠ u.val; omega), hMetaData mIdxFStopInBase (by decide)]
        exact hMeta.meta_fStopIn
      obtain ⟨sNext, hsWrt, hpcNext, hNextFr, hNextP, hNextJ, hNextStkN, hNextStkS,
          hn0, hn1, hnm, hn2, hn3, hn4⟩ :=
        dfsWritePJ_spec (input := input) h100 hPlWrt (by rw [hCodeSz]; omega) hStage1 u.isLt hSp'LtN htLtN
          sM hpcM hm0 hm1 hmm hm2 hm3 hm4 hm5 hm8 hm9 hMetaS_M hMetaT_M hMetaF_M (hIn.fStop_at u)
      let stkNext : List (Fin N) := stk0.take sp' ++ [u]
      have hNextLen : stkNext.length = sp' + 1 := by simp [stkNext, hTakeLen]
      have hNextMem : ∀ w : Fin N, w ∈ stkNext ↔
          rd.entry (Fin.cast hN w) < t + 1 ∧ t + 1 ≤ rd.stop (Fin.cast hN w) := by
        intro w
        simp only [stkNext, List.mem_append, List.mem_singleton, hbMemFin]
        constructor
        · rintro (⟨he, hs⟩ | rfl)
          · exact ⟨Nat.lt_succ_of_lt he, hs⟩
          · have hspU := hSpanEntry w
            exact ⟨by rw [huEntry]; exact Nat.lt_succ_self t, by rw [← huEntry]; exact hspU.1⟩
        · rintro ⟨he, hs⟩
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ he) with hlt | heq
          · exact Or.inl ⟨hlt, hs⟩
          · refine Or.inr (hInjEntry w u (by rw [huEntry]; exact heq))
      have hNextInc : ∀ i j (hi : i < stkNext.length) (hj : j < stkNext.length), i < j →
          rd.entry (Fin.cast hN (stkNext[i]'hi)) < rd.entry (Fin.cast hN (stkNext[j]'hj)) := by
        intro i j hi hj hij
        by_cases hjLast : j = sp'
        · have hiLt : i < sp' := by omega
          have hiMem : stkNext[i]'hi ∈ stk0.take sp' := by
            rw [List.getElem_append_left (by rw [hTakeLen]; exact hiLt)]
            exact List.getElem_mem _
          have hjEqU : stkNext[j]'hj = u := by
            subst hjLast
            rw [List.getElem_append_right (Nat.le_of_eq hTakeLen)]
            simp [hTakeLen]
          rw [hjEqU, huEntry]
          exact (hbMemFin _).mp hiMem |>.1
        · have hiLt : i < sp' := by rw [hNextLen] at hj; omega
          have hjLt : j < sp' := by rw [hNextLen] at hj; omega
          rw [List.getElem_append_left (by rw [hTakeLen]; exact hiLt),
            List.getElem_append_left (by rw [hTakeLen]; exact hjLt),
            List.getElem_take, List.getElem_take]
          exact hStkInc i j (by omega) (by omega) hij
      have hNextFrSt : ∀ j, j ≠ u.val → j ≠ storedBase N + 18 * u.val →
          j ≠ storedBase N + 18 * u.val + 1 → j ≠ tempArrBase n m N + N + sp' →
          j ≠ tempArrBase n m N + 2 * N + sp' → sNext.data[j]? = st.data[j]? := by
        intro j h1 h2 h3 h4 h5
        rw [hNextFr j h2 h3 h4 h5, hMDataNeU j h1]
      have hIterSteps : Steps ph.code input (1 + popSteps + 6 + midSteps + 29) st sNext := by
        have hA := (steps_1_of_step hsA).append (hsPop.append hsC)
        have hB := hsMid.append hsWrt
        rw [show 1 + popSteps + 6 + midSteps + 29 = 1 + (popSteps + 6) + (midSteps + 29) by omega]
        exact hA.append hB
      have hPotentialNext : (stepsAcc + (1 + popSteps + 6 + midSteps + 29)) + 12 * (sp' + 1) ≤
          96 * (t + 1) + 5 := by
        omega
      obtain ⟨remSteps, out, hOutLe, hsRem, hOutPc, hOutForest, hOutFr⟩ :=
        ih (t + 1) (sp' + 1) (stepsAcc + (1 + popSteps + 6 + midSteps + 29)) stkNext sNext
          (by omega) hNextLen hPotentialNext hpcNext hn0 hn1 hnm hn2 hn3 hn4
          (fun i hi22 => by
            rw [hNextFrSt _ (by change metaArrBase n m N + i ≠ u.val; omega)
              (by change metaArrBase n m N + i ≠ storedBase N + 18 * u.val; unfold storedBase; omega)
              (by change metaArrBase n m N + i ≠ storedBase N + 18 * u.val + 1; unfold storedBase; omega)
              (by change metaArrBase n m N + i ≠ tempArrBase n m N + N + sp'; omega)
              (by change metaArrBase n m N + i ≠ tempArrBase n m N + 2 * N + sp'; omega)]
            exact hMetaData i hi22)
          (fun w => by
            have hElt := hRdEntryLt w
            rw [hNextFrSt _ (by omega) (by unfold storedBase; omega) (by unfold storedBase; omega)
              (by omega) (by omega)]
            exact hInvSt w)
          (fun idx hi => by
            by_cases hiLast : idx = sp'
            · subst hiLast
              have hiEqU : stkNext[idx]'(by rw [hNextLen]; exact hi) = u := by
                rw [List.getElem_append_right (Nat.le_of_eq hTakeLen)]
                simp [hTakeLen]
              rw [hiEqU]
              exact ⟨hNextStkN, hNextStkS⟩
            · have hiLt : idx < sp' := by omega
              have hEqTake : stkNext[idx]'(by rw [hNextLen]; exact hi) = stk0[idx]'(by omega) := by
                rw [List.getElem_append_left (by rw [hTakeLen]; exact hiLt), List.getElem_take]
              rw [hEqTake]
              refine ⟨?_, ?_⟩
              · rw [hNextFrSt _ (by omega) (by unfold storedBase; omega) (by unfold storedBase; omega)
                  (by omega) (by omega)]
                exact (hStkAt idx (by omega)).1
              · rw [hNextFrSt _ (by omega) (by unfold storedBase; omega) (by unfold storedBase; omega)
                  (by omega) (by omega)]
                exact (hStkAt idx (by omega)).2)
          hNextInc hNextMem
          (fun w hw => by
            by_cases hwu : w = u
            · subst hwu
              refine ⟨?_, hNextP, hNextJ⟩
              rw [hNextFr _ (by unfold storedBase; omega) (by unfold storedBase; omega)
                (by omega) (by omega)]
              exact hMDepth
            · have hwOld : rd.entry (Fin.cast hN w) < t := by
                rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hw) with hlt | heq
                · exact hlt
                · exact False.elim (hwu (hInjEntry w u (by rw [heq, huEntry])))
              have hOldVis := hVis w hwOld
              have hwNeU : w.val ≠ u.val := fun he => hwu (Fin.ext he)
              refine ⟨?_, ?_, ?_⟩
              · rw [hNextFrSt _ hwNeU (by unfold storedBase; omega) (by unfold storedBase; omega)
                  (by omega) (by omega)]
                exact hOldVis.1
              · rw [hNextFrSt _ (by unfold storedBase; omega)
                  (by unfold storedBase; omega) (by unfold storedBase; omega)
                  (by unfold storedBase; omega) (by unfold storedBase; omega)]
                exact hOldVis.2.1
              · rw [hNextFrSt _ (by unfold storedBase; omega)
                  (by unfold storedBase; omega) (by unfold storedBase; omega)
                  (by unfold storedBase; omega) (by unfold storedBase; omega)]
                exact hOldVis.2.2)
          (fun j hj => by
            rw [hNextFrSt j (by omega) (by unfold storedBase; omega) (by unfold storedBase; omega)
              (by omega) (by omega)]
            exact hFr j hj)
      refine ⟨(1 + popSteps + 6 + midSteps + 29) + remSteps, out, by omega,
        hIterSteps.append hsRem, hOutPc, hOutForest, hOutFr⟩
  obtain ⟨remSteps, out, hRemLe, hsLoop, hOutPc, hOutForest, hOutFr⟩ :=
    hLoop N 0 0 5 [] s1 (Nat.zero_add N) rfl (by omega) hpc1 hr0_1 hr1_1 hrm_1 hr2_1 hr3_1 hr4_1
      (fun i _ => by rw [hd1]; rfl)
      (fun u => by rw [hd1]; exact hInv u)
      (fun i hi => False.elim (Nat.not_lt_zero _ hi))
      (fun i _ hi => False.elim (Nat.not_lt_zero _ hi))
      (fun w => ⟨fun hm => by simp at hm, fun ⟨hlt, _⟩ => False.elim (Nat.not_lt_zero _ hlt)⟩)
      (fun w hlt => False.elim (Nat.not_lt_zero _ hlt))
      (fun j _ => by rw [hd1]; rfl)
  have hAllSteps : Steps ph.code input (5 + remSteps) (Phase.initial s0) out := hs1.append hsLoop
  have hHalt : step ph.code input out = some (.halted out) :=
    step_halt_at (by
      rw [hOutPc]
      change ((dfsStackInstrs (bits := bits) h100 ++ [Instr.halt]).toArray : Program DomL)[95]? = some .halt
      rw [Array.getElem?_eq_getElem (by simp [hTotLen])]
      simp [hTotLen])
  exact ⟨5 + remSteps + 1, out, by omega, hAllSteps.halts hHalt, hOutForest, hOutFr⟩

end Stage1PartBPhases

section PipelineComposition

inductive PhaseChain {bits : Nat} {L : Layout bits} (input : Input L) :
    List (Phase L) → State L → State L → Nat → Prop
  | nil (s : State L) : PhaseChain input [] s s 0
  | cons {p : Phase L} {ps : List (Phase L)} {s m t : State L} {a b : Nat} :
      run p.code input a (Phase.initial s) = some ⟨m, a⟩ →
      PhaseChain input ps m t b →
      PhaseChain input (p :: ps) s t (a + b)

theorem PhaseChain.append {bits : Nat} {L : Layout bits} {input : Input L}
    {ps1 ps2 : List (Phase L)} {s m t : State L} {k1 k2 : Nat}
    (h1 : PhaseChain input ps1 s m k1) (h2 : PhaseChain input ps2 m t k2) :
    PhaseChain input (ps1 ++ ps2) s t (k1 + k2) := by
  induction h1 with
  | nil _ => simpa using h2
  | cons first _ ih =>
    rw [List.cons_append, Nat.add_assoc]
    exact PhaseChain.cons first (ih h2)

theorem PhaseChain.toPhasesRun {bits : Nat} {L : Layout bits} {input : Input L}
    {ps : List (Phase L)} {s t : State L} {steps : Nat}
    (h : PhaseChain input ps s t steps) :
    PhasesRun input ps s (Phase.initial t) (steps + 1) := by
  induction h with
  | nil _ => exact PhasesRun.nil
  | cons first _ ih =>
    rw [Nat.add_assoc]
    exact PhasesRun.cons first ih

section Stage1Pipeline

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def stage1Phases (h100 : 100 ≤ 2 ^ bits) : List (Phase DomL) :=
  [invEntryPhase (hi := hi) (hw := hw) h100, dfsStackPhase (hi := hi) (hw := hw) h100]

theorem run_stage1 {input : Input DomL}
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
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal) :
    ∃ steps : Nat, ∃ t : State DomL,
      steps ≤ 110 * r.out.tables.next + 25 ∧
      PhaseChain input (stage1Phases (hi := hi) (hw := hw) h100) s0 t steps ∧
      ForestReady t flat increasing covers rankArc r nGlobal ∧
      (∀ j, ((19 * r.out.tables.next ≤ j ∧ j < tempArrBase H.vertexCount H.arcCount r.out.tables.next) ∨
          tempArrBase H.vertexCount H.arcCount r.out.tables.next + 3 * r.out.tables.next ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  obtain ⟨s1, hRun1, hMeta1, hInv1, hFr1⟩ := run_invEntry h100 hIn hWork s0 hMeta
  obtain ⟨st2, t, hLe2, hRun2, hForest2, hFr2⟩ :=
    run_dfsStack flat increasing covers rankArc h100 hIn hWork s1 hMeta1 hInv1
  refine ⟨(10 + 7 * r.out.tables.next + 2) + (st2 + 0), t, by omega,
    PhaseChain.cons hRun1 (PhaseChain.cons hRun2 (PhaseChain.nil t)), hForest2,
    fun j hj => ?_⟩
  rw [hFr2 j hj, hFr1 j ?_]
  rcases hj with ⟨_, hlt⟩ | hge
  · exact Or.inl hlt
  · exact Or.inr (by omega)

end Stage1Pipeline

end PipelineComposition

end Stage1ForestRecon

end PaperB.RamProgram.ExitSummaryBuild
