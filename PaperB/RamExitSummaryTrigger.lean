module

public import PaperB.RamExitSummaryStage1

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-!
Word-RAM phases that initialize prior rows and stored maps, then link trigger buckets.
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


theorem array_set_eq_of_data_eq {α : Type} {a b : Array α} (hab : a = b)
    {i : Nat} {v : α} (ha : i < a.size) (hb : i < b.size) :
    a.set i v ha = b.set i v hb := by
  subst hab; rfl

theorem list_all_append_true {α : Type _} (p : α → Bool) (xs ys : List α)
    (hx : xs.all p = true) (hy : ys.all p = true) : (xs ++ ys).all p = true := by
  rw [List.all_append, hx, hy]; rfl

theorem metaLoadInstrs_nonHalt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (d t : Fin 15) (off : Nat) (hOff : off < 2 ^ bits) :
    (metaLoadInstrs (bits := bits) d t off hOff).all
      (nonHalt (L := layout bits inputCap workCap hi hw)) = true := by
  simp [metaLoadInstrs, nonHalt]

section Stage3SeedTrigger

section ZeroPrior

variable {bits : Nat}

def zeroPriorSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg7 mIdxPriorBase (by dsimp only [mIdxPriorBase]; omega) ++
  (metaLoadInstrs reg3 reg7 mIdxN (by dsimp only [mIdxN]; omega) ++
  (mul6Instrs reg4 reg3 ++
  [ .mov reg3 reg0 ]))

def zeroPriorLoopInstrs : List (Instr bits 15) :=
  [ .branchLt reg3 reg4 11 15
  , .add reg5 reg2 reg3
  , .storeData reg5 reg0
  , .add reg3 reg3 reg1
  , .goto 10
  ]

def zeroPriorInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  zeroPriorSetupInstrs h100 ++ zeroPriorLoopInstrs

end ZeroPrior

section ZeroPriorPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private theorem zeroPriorInstrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (zeroPriorInstrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  simp [zeroPriorInstrs, zeroPriorSetupInstrs, zeroPriorLoopInstrs, metaLoadInstrs, mul6Instrs, nonHalt]

def zeroPriorPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (zeroPriorInstrs h100) (zeroPriorInstrs_nonHalt h100)

private theorem zeroPriorLoop_spec {code : Program DomL} {input : Input DomL}
    {n N : Nat} (hOutCap : priorBase N + 6 * n ≤ workCap)
    (_hWorkFit : workCap ≤ 2 ^ bits)
    (hPl : Placed code 10 (zeroPriorLoopInstrs (bits := bits)))
    (hSz : 15 < code.size) :
    ∀ (rem k : Nat) (st : State DomL),
      k + rem = 6 * n →
      st.pc = 10 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st reg2).val = priorBase N →
      (reg st reg3).val = k →
      (reg st reg4).val = 6 * n →
      (∀ i < k, (st.data[priorBase N + i]?).map Fin.val = some 0) →
      ∃ steps : Nat, ∃ t : State DomL,
        steps ≤ 5 * rem + 1 ∧
        Steps code input steps st t ∧
        t.pc = 15 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ reg t rMeta = reg st rMeta ∧
        (∀ i < 6 * n, (t.data[priorBase N + i]?).map Fin.val = some 0) ∧
        (∀ j, (j < priorBase N ∨ priorBase N + 6 * n ≤ j) → t.data[j]? = st.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro k st hSum hpc h0 h1 h2 h3 h4 hDone
    have hkEq : k = 6 * n := by omega
    obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg3).val < (reg st reg4).val := by rw [h3, h4, hkEq]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpct
    have hrtF := reg_of_regs_eq hrt
    refine ⟨1, t, by omega, steps_1_of_step hs, hpct,
      by rw [hrtF, h0], by rw [hrtF, h1], hrtF rMeta,
      fun i hi => by rw [hdt]; exact hDone i (hkEq ▸ hi),
      fun _ _ => by rw [hdt]⟩
  | succ rem ih =>
    intro k st hSum hpc h0 h1 h2 h3 h4 hDone
    have hkLt : k < 6 * n := by omega
    obtain ⟨s1, hs1, hpc1, hrt1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    rw [ite_eq_left (by rw [h3, h4]; exact hkLt)] at hpc1
    have hr1 := reg_of_regs_eq hrt1
    have ha1 : code[s1.pc]? = some (.add reg5 reg2 reg3) := by rw [hpc1]; exact hPl 1 _ rfl
    have hFitA : (reg s1 reg2).val + (reg s1 reg3).val < 2 ^ bits := by rw [hr1, hr1, h2, h3]; omega
    obtain ⟨s2, hs2, hpc2, h5_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by omega)
    have hAddr : (reg s2 reg5).val = priorBase N + k := by
      rw [h5_2, add_no_wrap _ _ hFitA, hr1, hr1, h2, h3]
    have hLt2 : (reg s2 reg5).val < s2.data.size := lt_data_size (by rw [hAddr]; omega)
    have hst : code[s2.pc]? = some (.storeData reg5 reg0) := by rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, hpc3, hreg3, hd3⟩ := step_storeData_opaque (input := input) hst hLt2 (by omega)
    have hr3 := reg_of_regs_eq hreg3
    have h3_3 : (reg s3 reg3).val = k := by rw [hr3, ho2 reg3 (by intro h; cases h), hr1, h3]
    have h1_3 : (reg s3 reg1).val = 1 := by rw [hr3, ho2 reg1 (by intro h; cases h), hr1, h1]
    have hFitK : (reg s3 reg3).val + (reg s3 reg1).val < 2 ^ bits := by rw [h3_3, h1_3]; omega
    have haInc : code[s3.pc]? = some (.add reg3 reg3 reg1) := by rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, hpc4, h3_4, ho4, hd4⟩ := step_add_at (input := input) haInc (by omega)
    have hg4 : code[s4.pc]? = some (.goto 10) := by rw [hpc4, hpc3, hpc2, hpc1]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, hpc5, hrt5, hd5⟩ := step_goto_at (input := input) hg4 (by omega)
    have hr5 := reg_of_regs_eq hrt5
    have hd2' : s2.data = st.data := by rw [hd2, hd1]
    have hLt2St : (reg s2 reg5).val < st.data.size := by rw [← hd2']; exact hLt2
    have hs5Data : s5.data = st.data.set (reg s2 reg5).val (reg s2 reg0) hLt2St := by
      rw [hd5, hd4, hd3]; exact array_set_eq_of_data_eq hd2' hLt2 hLt2St
    have hPres5 : ∀ r : Fin 15, r ≠ reg3 → r ≠ reg5 → reg s5 r = reg st r := fun r hr3Ne hr5Ne => by
      rw [hr5, ho4 r hr3Ne, hr3, ho2 r hr5Ne, hr1]
    have h0_2 : (reg s2 reg0).val = 0 := by rw [ho2 reg0 (by intro h; cases h), hr1, h0]
    have hStep5 : Steps code input 5 st s5 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5))))
    obtain ⟨kRest, t, hkRest, hStepsRest, hpct, ht0, ht1, htMetaEq, htDone, htFr⟩ :=
      ih (k + 1) s5 (by omega) hpc5
        (by rw [hPres5 reg0 (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hPres5 reg1 (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hPres5 reg2 (by intro h; cases h) (by intro h; cases h), h2])
        (by rw [hr5, h3_4, add_no_wrap _ _ hFitK, h3_3, h1_3])
        (by rw [hPres5 reg4 (by intro h; cases h) (by intro h; cases h), h4])
        (fun i hi => by
          rw [hs5Data]
          by_cases hik : i = k
          · subst hik; rw [← hAddr, Array.getElem?_set_self hLt2St, Option.map_some, h0_2]
          · have hNe : priorBase N + i ≠ (reg s2 reg5).val := by rw [hAddr]; omega
            rw [Array.getElem?_set_ne hLt2St hNe.symm]; exact hDone i (by omega))
    refine ⟨5 + kRest, t, by omega, hStep5.append hStepsRest, hpct, ht0, ht1,
      htMetaEq.trans (hPres5 rMeta (by intro h; cases h) (by intro h; cases h)), htDone, fun j hj => ?_⟩
    rw [htFr j hj, hs5Data]
    have hNe : j ≠ (reg s2 reg5).val := by rw [hAddr]; rcases hj with h | h <;> omega
    exact Array.getElem?_set_ne hLt2St hNe.symm

theorem run_zeroPrior {input : Input DomL}
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
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 30 * H.vertexCount + 12 ∧
      run (zeroPriorPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ y < H.vertexCount, ∀ i < 6,
        (t.data[priorBase r.out.tables.next + 6 * y + i]?).map Fin.val = some 0) ∧
      (∀ j, (j < priorBase r.out.tables.next ∨ orderArrBase H.vertexCount r.out.tables.next ≤ j) →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hOutCap : priorBase r.out.tables.next + 6 * H.vertexCount ≤ workCap := by
    have : orderArrBase H.vertexCount r.out.tables.next =
        priorBase r.out.tables.next + 6 * H.vertexCount := rfl
    have : metaArrBase H.vertexCount H.arcCount r.out.tables.next =
        20 * r.out.tables.next + 10 * H.vertexCount + H.arcCount + 1 :=
      metaArrBase_eq _ _ _
    unfold priorBase exitWorkCap at *; omega
  have hTempFit : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ workCap := by
    have := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *; rw [metaArrBase_eq] at *; omega
  let ph := zeroPriorPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (zeroPriorInstrs (bits := bits) h100).length = 15 := by
    simp [zeroPriorInstrs, zeroPriorSetupInstrs, zeroPriorLoopInstrs, metaLoadInstrs, mul6Instrs]
  have hCodeSize : ph.code.size = 16 := by
    dsimp [ph, zeroPriorPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (zeroPriorInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold zeroPriorInstrs at hPlFull; exact hPlFull)
  have hPlLoop := Placed_append_right (by unfold zeroPriorInstrs at hPlFull; exact hPlFull)
  rw [show (zeroPriorSetupInstrs (bits := bits) h100).length = 10 by
    simp [zeroPriorSetupInstrs, metaLoadInstrs, mul6Instrs]] at hPlLoop
  have hPlP := Placed_append_left (by unfold zeroPriorSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold zeroPriorSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPlN := Placed_append_left hPlS1
  have hPlMul := Placed_append_right hPlS1; rw [hLml] at hPlMul
  have hNPos : 0 < r.out.tables.next :=
    (nodeCount_eq_next r.index.ok) ▸ (PaperB.EX24.FinalDFS.packedInput r.index.ok).root.pos
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlP (by omega) rfl hMeta.rMeta_eq (by dsimp only [mIdxPriorBase]; omega) hMeta.meta_priorBase
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlN (by omega) hpc1 hMeta1 (by dsimp only [mIdxN]; omega) (by rw [hd1]; exact hMeta.meta_n)
  have hFit2 : (reg s2 reg3).val + (reg s2 reg3).val < 2 ^ bits := by
    rw [h3_2]; unfold priorBase at hOutCap; omega
  have ha1 : ph.code[s2.pc]? = some (.add reg4 reg3 reg3) := by rw [hpc2]; exact hPlMul 0 _ rfl
  obtain ⟨s3, hs3, hpc3, h4_3, ho3, hd3⟩ := step_add_at (input := input) ha1 (by omega)
  have h4Val3 : (reg s3 reg4).val = 2 * H.vertexCount := by
    rw [h4_3, add_no_wrap _ _ hFit2, h3_2]; omega
  have h3_3 : (reg s3 reg3).val = H.vertexCount := by rw [ho3 reg3 (by intro h; cases h), h3_2]
  have hFit3 : (reg s3 reg4).val + (reg s3 reg3).val < 2 ^ bits := by
    rw [h4Val3, h3_3]; unfold priorBase at hOutCap; omega
  have ha2 : ph.code[s3.pc]? = some (.add reg4 reg4 reg3) := by rw [hpc3, hpc2]; exact hPlMul 1 _ rfl
  obtain ⟨s4, hs4, hpc4, h4_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by omega)
  have h4Val4 : (reg s4 reg4).val = 3 * H.vertexCount := by
    rw [h4_4, add_no_wrap _ _ hFit3, h4Val3, h3_3]; omega
  have hFit4 : (reg s4 reg4).val + (reg s4 reg4).val < 2 ^ bits := by
    rw [h4Val4]; unfold priorBase at hOutCap; omega
  have ha3 : ph.code[s4.pc]? = some (.add reg4 reg4 reg4) := by rw [hpc4, hpc3, hpc2]; exact hPlMul 2 _ rfl
  obtain ⟨s5, hs5, hpc5, h4_5, ho5, hd5⟩ := step_add_at (input := input) ha3 (by omega)
  have h4Val5 : (reg s5 reg4).val = 6 * H.vertexCount := by
    rw [h4_5, add_no_wrap _ _ hFit4, h4Val4]; omega
  have hm1 : ph.code[s5.pc]? = some (.mov reg3 reg0) := by rw [hpc5, hpc4, hpc3, hpc2]; exact hPlMul 3 _ rfl
  obtain ⟨s6, hs6, hpc6, h3_6, ho6, hd6⟩ := step_mov_at (input := input) hm1 (by omega)
  have hPres6 : ∀ r : Fin 15, r ≠ reg3 → r ≠ reg4 → reg s6 r = reg s2 r := fun r hr3 hr4 => by
    rw [ho6 r hr3, ho5 r hr4, ho4 r hr4, ho3 r hr4]
  have hd6' : s6.data = s0.data := by rw [hd6, hd5, hd4, hd3, hd2, hd1, data_initial]
  have h0_6 : (reg s6 reg0).val = 0 := by
    rw [hPres6 reg0 (by intro h; cases h) (by intro h; cases h), ho2 reg0 (by intro h; cases h) (by intro h; cases h),
      ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_6 : (reg s6 reg1).val = 1 := by
    rw [hPres6 reg1 (by intro h; cases h) (by intro h; cases h), ho2 reg1 (by intro h; cases h) (by intro h; cases h),
      ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have h2_6 : (reg s6 reg2).val = priorBase r.out.tables.next := by
    unfold priorBase
    rw [hPres6 reg2 (by intro h; cases h) (by intro h; cases h), ho2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have hM_6 : (reg s6 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [hPres6 rMeta (by intro h; cases h) (by intro h; cases h), ho2 rMeta (by intro h; cases h) (by intro h; cases h), hMeta1]
  have h3_6' : (reg s6 reg3).val = 0 := by rw [h3_6, ← ho6 reg0 (by intro h; cases h), h0_6]
  have h4_6 : (reg s6 reg4).val = 6 * H.vertexCount := by rw [ho6 reg4 (by intro h; cases h), h4Val5]
  obtain ⟨kLoop, t, hkLoop, hStepsLoop, hpct, ht0, ht1, htMetaEq, htDone, htFr⟩ :=
    zeroPriorLoop_spec hOutCap hw hPlLoop (by omega) (6 * H.vertexCount) 0 s6 (Nat.zero_add _)
      (by omega) h0_6 h1_6 h2_6 h3_6' h4_6 (fun _ hi => absurd hi (Nat.not_lt_zero _))
  have hSetupSteps : Steps ph.code input 10 (Phase.initial s0) s6 :=
    hs1.append (hs2.append (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (steps_1_of_step hs6)))))
  have hHalt : step ph.code input t = some (.halted t) :=
    haltAt_mkHaltPhase (hi := hi) (hw := hw) (zeroPriorInstrs (bits := bits) h100) _
      (by rw [hpct, hCodeLen]) (input := input)
  refine ⟨10 + kLoop + 1, t, by omega, (hSetupSteps.append hStepsLoop).halts hHalt, ?_, ?_, ?_⟩
  · apply hMeta.preserve (by rw [htMetaEq, hM_6]) ht0 ht1
    intro i hi22
    rw [htFr _ (Or.inr (by
      unfold metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase
        trigHeadArrBase topoRankArrBase orderArrBase priorBase
      omega)), hd6']
  · intro y hy i hi6
    rw [show priorBase r.out.tables.next + 6 * y + i = priorBase r.out.tables.next + (6 * y + i) by omega]
    exact htDone (6 * y + i) (by omega)
  · intro j hj
    rw [htFr j (by rcases hj with h | h; exact Or.inl h; exact Or.inr h), hd6']

end ZeroPriorPhase

section SeedStoredMaps

variable {bits : Nat}

def seedIdentityRegs : List (Fin 15) :=
  [reg0, reg0, reg0, reg1, reg0, reg0, reg0, reg4,
   reg0, reg0, reg0, reg1, reg0, reg0, reg0, reg4]

def seedStoredMapsSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg6 reg8 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega) ++
  (metaLoadInstrs reg3 reg8 mIdxNH (by dsimp only [mIdxNH]; omega) ++
  [ .add reg4 reg1 reg1
  , .add reg6 reg6 reg4
  , .mov reg5 reg0
  ])

def seedStoredMapsLoopInstrs : List (Instr bits 15) :=
  [ .branchLt reg5 reg3 10 45 ] ++
  (storeSeqInstrs reg6 reg1 seedIdentityRegs ++
  [ .add reg6 reg6 reg4
  , .add reg6 reg6 reg1
  , .add reg5 reg5 reg1
  , .goto 9
  ])

def seedStoredMapsInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  seedStoredMapsSetupInstrs h100 ++ seedStoredMapsLoopInstrs

end SeedStoredMaps

section SeedStoredMapsPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

private theorem storeSeqInstrs_nonHalt {bits : Nat} {L : Layout bits}
    (ptr one : Fin L.registerCount) (vs : List (Fin L.registerCount)) :
    (storeSeqInstrs (bits := bits) ptr one vs).all (nonHalt (L := L)) = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => simp [storeSeqInstrs, nonHalt]
    | cons w ws =>
      simp only [storeSeqInstrs, List.all_cons, nonHalt, Bool.true_and]
      exact ih

private theorem seedStoredMapsInstrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (seedStoredMapsInstrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  have hSeq : (storeSeqInstrs (bits := bits) reg6 reg1 seedIdentityRegs).all (nonHalt (L := DomL)) = true :=
    storeSeqInstrs_nonHalt (L := DomL) reg6 reg1 seedIdentityRegs
  unfold seedStoredMapsInstrs
  refine list_all_append_true _ _ _ ?_ ?_
  · unfold seedStoredMapsSetupInstrs
    simp only [List.all_append, List.all_cons, List.all_nil, metaLoadInstrs_nonHalt, nonHalt, Bool.and_true]
  · unfold seedStoredMapsLoopInstrs
    simp only [List.all_append, List.all_cons, List.all_nil, hSeq, nonHalt, Bool.and_true]

def seedStoredMapsPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (seedStoredMapsInstrs h100) (seedStoredMapsInstrs_nonHalt h100)

private theorem seedStoredMapsLoop_spec {code : Program DomL} {input : Input DomL}
    {N : Nat} (hOutCap : storedBase N + 18 * N + 2 < workCap) (_hWorkFit : workCap ≤ 2 ^ bits)
    (hPl : Placed code 9 (seedStoredMapsLoopInstrs (bits := bits)))
    (hSz : 45 < code.size) :
    ∀ (rem u : Nat) (st : State DomL),
      u + rem = N →
      st.pc = 9 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st reg4).val = 2 →
      (reg st reg3).val = N →
      (reg st reg5).val = u →
      (reg st reg6).val = storedBase N + 18 * u + 2 →
      (∀ w < u, ∀ i < 16,
        (st.data[storedBase N + 18 * w + 2 + i]?).map Fin.val =
          some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0)) →
      ∃ steps : Nat, ∃ t : State DomL,
        steps ≤ 36 * rem + 1 ∧
        Steps code input steps st t ∧
        t.pc = 45 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ reg t rMeta = reg st rMeta ∧
        (∀ w < N, ∀ i < 16,
          (t.data[storedBase N + 18 * w + 2 + i]?).map Fin.val =
            some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0)) ∧
        (∀ j, (j < storedBase N ∨ priorBase N ≤ j ∨
            (∃ w < N, j = storedBase N + 18 * w ∨ j = storedBase N + 18 * w + 1)) →
          t.data[j]? = st.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro u st hSum hpc h0 h1 h4 h3 h5 h6 hDone
    have huEq : u = N := by omega
    obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg5).val < (reg st reg3).val := by rw [h5, h3, huEq]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpct
    have hrtF := reg_of_regs_eq hrt
    refine ⟨1, t, by omega, steps_1_of_step hs, hpct,
      by rw [hrtF, h0], by rw [hrtF, h1], hrtF rMeta,
      fun w hw i hi => by rw [hdt]; exact hDone w (huEq ▸ hw) i hi,
      fun _ _ => by rw [hdt]⟩
  | succ rem ih =>
    intro u st hSum hpc h0 h1 h4 h3 h5 h6 hDone
    have huLt : u < N := by omega
    obtain ⟨s1, hs1, hpc1, hrt1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    rw [ite_eq_left (by rw [h5, h3]; exact huLt)] at hpc1
    have hr1 := reg_of_regs_eq hrt1
    have hPlRest := Placed_append_right (by unfold seedStoredMapsLoopInstrs at hPl; exact hPl)
    rw [show ([Instr.branchLt reg5 reg3 10 45] : List (Instr bits 15)).length = 1 by rfl] at hPlRest
    have hPlSeq := Placed_append_left hPlRest
    have hPlTail := Placed_append_right hPlRest
    have hSeqLen : (storeSeqInstrs (bits := bits) reg6 reg1 seedIdentityRegs).length = 31 := rfl
    rw [hSeqLen] at hPlTail
    have hDataFit : (storedBase N + 18 * u + 2) + seedIdentityRegs.length ≤ s1.data.size := by
      rw [s1.data_size]; change storedBase N + 18 * u + 2 + 16 ≤ workCap; omega
    have hBitsFit : (storedBase N + 18 * u + 2) + seedIdentityRegs.length < 2 ^ bits := by
      change storedBase N + 18 * u + 2 + 16 < 2 ^ bits; omega
    obtain ⟨s2, hs2, hpc2, hPtr2, ho2, hFr2, hWr2⟩ :=
      run_storeSeq reg6 reg1 (by intro h; cases h) seedIdentityRegs 10 (storedBase N + 18 * u + 2) s1
        (fun v hv => by
          simp only [seedIdentityRegs, List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
            (subst h; intro hc; cases hc))
        hPlSeq (by rw [hSeqLen]; omega) hpc1 (by rw [hr1, h6]) (by rw [hr1, h1]) hDataFit hBitsFit
    have h6_2 : (reg s2 reg6).val = storedBase N + 18 * u + 17 := by
      have := hPtr2 (by simp [seedIdentityRegs]); change (reg s2 reg6).val = storedBase N + 18 * u + 2 + (16 - 1) at this; omega
    have h4_2 : (reg s2 reg4).val = 2 := by rw [ho2 reg4 (by intro h; cases h), hr1, h4]
    have h1_2 : (reg s2 reg1).val = 1 := by rw [ho2 reg1 (by intro h; cases h), hr1, h1]
    have ha1 : code[s2.pc]? = some (.add reg6 reg6 reg4) := by rw [hpc2, hSeqLen]; exact hPlTail 0 _ rfl
    obtain ⟨s3, hs3, hpc3, h6_3, ho3, hd3⟩ := step_add_at (input := input) ha1 (by omega)
    have h6Val3 : (reg s3 reg6).val = storedBase N + 18 * u + 19 := by
      rw [h6_3, add_no_wrap _ _ (by rw [h6_2, h4_2]; omega), h6_2, h4_2]
    have h1_3 : (reg s3 reg1).val = 1 := by rw [ho3 reg1 (by intro h; cases h), h1_2]
    have ha2 : code[s3.pc]? = some (.add reg6 reg6 reg1) := by rw [hpc3, hpc2, hSeqLen]; exact hPlTail 1 _ rfl
    obtain ⟨s4, hs4, hpc4, h6_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by omega)
    have h6Val4 : (reg s4 reg6).val = storedBase N + 18 * (u + 1) + 2 := by
      rw [h6_4, add_no_wrap _ _ (by rw [h6Val3, h1_3]; omega), h6Val3, h1_3]; omega
    have h5_4 : (reg s4 reg5).val = u := by
      rw [ho4 reg5 (by intro h; cases h), ho3 reg5 (by intro h; cases h), ho2 reg5 (by intro h; cases h), hr1, h5]
    have h1_4 : (reg s4 reg1).val = 1 := by rw [ho4 reg1 (by intro h; cases h), h1_3]
    have ha3 : code[s4.pc]? = some (.add reg5 reg5 reg1) := by rw [hpc4, hpc3, hpc2, hSeqLen]; exact hPlTail 2 _ rfl
    obtain ⟨s5, hs5, hpc5, h5_5, ho5, hd5⟩ := step_add_at (input := input) ha3 (by omega)
    have hg5 : code[s5.pc]? = some (.goto 9) := by rw [hpc5, hpc4, hpc3, hpc2, hSeqLen]; exact hPlTail 3 _ rfl
    obtain ⟨s6, hs6, hpc6, hrt6, hd6⟩ := step_goto_at (input := input) hg5 (by omega)
    have hr6 := reg_of_regs_eq hrt6
    have hs6Data : s6.data = s2.data := by rw [hd6, hd5, hd4, hd3]
    have hPres6 : ∀ r : Fin 15, r ≠ reg5 → r ≠ reg6 → reg s6 r = reg st r := fun r hr5 hr6' => by
      rw [hr6, ho5 r hr5, ho4 r hr6', ho3 r hr6', ho2 r hr6', hr1]
    have hStep36 : Steps code input 36 st s6 := by
      have hT : Steps code input 31 s1 s2 := by rw [← hSeqLen]; exact hs2
      exact Steps.cons hs1 (hT.append (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5 (steps_1_of_step hs6)))))
    have hDoneNext : ∀ w < u + 1, ∀ i < 16,
        (s6.data[storedBase N + 18 * w + 2 + i]?).map Fin.val =
          some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0) := by
      intro w hw i hi16
      by_cases hwu : w = u
      · subst hwu
        rw [hs6Data, show storedBase N + 18 * w + 2 + i = (storedBase N + 18 * w + 2) + i by omega,
          hWr2 i (by simp [seedIdentityRegs]; omega), Option.map_some, Option.some.injEq]
        have h0s : (reg s1 reg0).val = 0 := by rw [hr1, h0]
        have h1s : (reg s1 reg1).val = 1 := by rw [hr1, h1]
        have h4s : (reg s1 reg4).val = 2 := by rw [hr1, h4]
        match i with
        | 0 => simp only [seedIdentityRegs, List.getElem_cons_zero]; rw [h0s]; rfl
        | 1 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 2 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 3 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h1s]; rfl
        | 4 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 5 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 6 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 7 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h4s]; rfl
        | 8 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 9 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 10 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 11 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h1s]; rfl
        | 12 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 13 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 14 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h0s]; rfl
        | 15 => simp only [seedIdentityRegs, List.getElem_cons_succ, List.getElem_cons_zero]; rw [h4s]; rfl
        | _ + 16 => omega
      · rw [hs6Data, hFr2 _ (by simp [seedIdentityRegs]; omega), hd1]
        exact hDone w (by omega) i hi16
    obtain ⟨kRest, t, hkRest, hStepsRest, hpct, ht0, ht1, htMetaEq, htDone, htFr⟩ :=
      ih (u + 1) s6 (by omega) hpc6
        (by rw [hPres6 reg0 (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hPres6 reg1 (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hPres6 reg4 (by intro h; cases h) (by intro h; cases h), h4])
        (by rw [hPres6 reg3 (by intro h; cases h) (by intro h; cases h), h3])
        (by rw [hr6, h5_5, add_no_wrap _ _ (by rw [h5_4, h1_4]; omega), h5_4, h1_4])
        (by rw [hr6, ho5 reg6 (by intro h; cases h), h6Val4])
        hDoneNext
    refine ⟨36 + kRest, t, by omega, hStep36.append hStepsRest, hpct, ht0, ht1,
      htMetaEq.trans (hPres6 rMeta (by intro h; cases h) (by intro h; cases h)), htDone, fun j hj => ?_⟩
    rw [htFr j hj, hs6Data, hFr2 j (by
      simp only [seedIdentityRegs, List.length_cons, List.length_nil]
      rcases hj with h | h | ⟨w, _, hw | hw⟩
      · exact Or.inl (by omega)
      · exact Or.inr (by simp only [priorBase, storedBase] at h ⊢; omega)
      · rw [hw]; rcases Nat.lt_trichotomy w u with hlt | heq | hgt
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      · rw [hw]; rcases Nat.lt_trichotomy w u with hlt | heq | hgt
        · exact Or.inl (by omega)
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)), hd1]

theorem run_seedStoredMaps {input : Input DomL}
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
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal) :
    ∃ k : Nat, ∃ t : State DomL,
      k ≤ 36 * r.out.tables.next + 12 ∧
      run (seedStoredMapsPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t H.vertexCount H.arcCount r.out.tables.next nGlobal ∧
      (∀ w < r.out.tables.next, ∀ i < 16,
        (t.data[storedBase r.out.tables.next + 18 * w + 2 + i]?).map Fin.val =
          some (if i % 8 = 3 then 1 else if i % 8 = 7 then 2 else 0)) ∧
      (∀ j, (j < storedBase r.out.tables.next ∨ priorBase r.out.tables.next ≤ j ∨
          (∃ w < r.out.tables.next,
            j = storedBase r.out.tables.next + 18 * w ∨
            j = storedBase r.out.tables.next + 18 * w + 1)) →
        t.data[j]? = s0.data[j]?) := by
  have hNLe : r.out.tables.next ≤ H.vertexCount + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hOutCap : storedBase r.out.tables.next + 18 * r.out.tables.next + 2 < workCap := by
    have := large
    have : metaArrBase H.vertexCount H.arcCount r.out.tables.next =
        20 * r.out.tables.next + 10 * H.vertexCount + H.arcCount + 1 :=
      metaArrBase_eq _ _ _
    unfold storedBase exitWorkCap at *; omega
  have hTempFit : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ workCap := by
    have := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *; rw [metaArrBase_eq] at *; omega
  let ph := seedStoredMapsPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (seedStoredMapsInstrs (bits := bits) h100).length = 45 := by
    simp [seedStoredMapsInstrs, seedStoredMapsSetupInstrs, seedStoredMapsLoopInstrs,
      metaLoadInstrs, storeSeqInstrs, seedIdentityRegs]
  have hCodeSize : ph.code.size = 46 := by
    dsimp [ph, seedStoredMapsPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (seedStoredMapsInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold seedStoredMapsInstrs at hPlFull; exact hPlFull)
  have hPlLoop := Placed_append_right (by unfold seedStoredMapsInstrs at hPlFull; exact hPlFull)
  rw [show (seedStoredMapsSetupInstrs (bits := bits) h100).length = 9 by
    simp [seedStoredMapsSetupInstrs, metaLoadInstrs]] at hPlLoop
  have hPlSB := Placed_append_left (by unfold seedStoredMapsSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold seedStoredMapsSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPlNH := Placed_append_left hPlS1
  have hPlTail := Placed_append_right hPlS1; rw [hLml] at hPlTail
  obtain ⟨s1, hs1, hpc1, hd1, h6_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPlSB (by omega) rfl hMeta.rMeta_eq (by dsimp only [mIdxStoredBase]; omega) hMeta.meta_storedBase
  have hMeta1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPlNH (by omega) hpc1 hMeta1 (by dsimp only [mIdxNH]; omega) (by rw [hd1]; exact hMeta.meta_NH)
  have h1_2 : (reg s2 reg1).val = 1 := by
    rw [ho2 reg1 (by intro h; cases h) (by intro h; cases h),
      ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have ha1 : ph.code[s2.pc]? = some (.add reg4 reg1 reg1) := by rw [hpc2]; exact hPlTail 0 _ rfl
  obtain ⟨s3, hs3, hpc3, h4_3, ho3, hd3⟩ := step_add_at (input := input) ha1 (by omega)
  have h4Val3 : (reg s3 reg4).val = 2 := by rw [h4_3, add_no_wrap _ _ (by rw [h1_2]; omega), h1_2]
  have h6_3 : (reg s3 reg6).val = storedBase r.out.tables.next := by
    unfold storedBase
    rw [ho3 reg6 (by intro h; cases h), ho2 reg6 (by intro h; cases h) (by intro h; cases h), h6_1]
  have ha2 : ph.code[s3.pc]? = some (.add reg6 reg6 reg4) := by rw [hpc3, hpc2]; exact hPlTail 1 _ rfl
  obtain ⟨s4, hs4, hpc4, h6_4, ho4, hd4⟩ := step_add_at (input := input) ha2 (by omega)
  have h6Val4 : (reg s4 reg6).val = storedBase r.out.tables.next + 2 := by
    rw [h6_4, add_no_wrap _ _ (by rw [h6_3, h4Val3]; omega), h6_3, h4Val3]
  have hm1 : ph.code[s4.pc]? = some (.mov reg5 reg0) := by rw [hpc4, hpc3, hpc2]; exact hPlTail 2 _ rfl
  obtain ⟨s5, hs5, hpc5, h5_5, ho5, hd5⟩ := step_mov_at (input := input) hm1 (by omega)
  have hd5' : s5.data = s0.data := by rw [hd5, hd4, hd3, hd2, hd1, data_initial]
  have h0_5 : (reg s5 reg0).val = 0 := by
    rw [ho5 reg0 (by intro h; cases h), ho4 reg0 (by intro h; cases h), ho3 reg0 (by intro h; cases h),
      ho2 reg0 (by intro h; cases h) (by intro h; cases h),
      ho1 reg0 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r0_zero]
  have h1_5 : (reg s5 reg1).val = 1 := by
    rw [ho5 reg1 (by intro h; cases h), ho4 reg1 (by intro h; cases h), ho3 reg1 (by intro h; cases h), h1_2]
  have hM_5 : (reg s5 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho5 rMeta (by intro h; cases h), ho4 rMeta (by intro h; cases h), ho3 rMeta (by intro h; cases h),
      ho2 rMeta (by intro h; cases h) (by intro h; cases h), hMeta1]
  have h3_5 : (reg s5 reg3).val = r.out.tables.next := by
    rw [ho5 reg3 (by intro h; cases h), ho4 reg3 (by intro h; cases h), ho3 reg3 (by intro h; cases h), h3_2]
  have h4_5 : (reg s5 reg4).val = 2 := by rw [ho5 reg4 (by intro h; cases h), ho4 reg4 (by intro h; cases h), h4Val3]
  have h5_5' : (reg s5 reg5).val = 0 := by rw [h5_5, ← ho5 reg0 (by intro h; cases h), h0_5]
  have h6_5 : (reg s5 reg6).val = storedBase r.out.tables.next + 2 := by rw [ho5 reg6 (by intro h; cases h), h6Val4]
  obtain ⟨kLoop, t, hkLoop, hStepsLoop, hpct, ht0, ht1, htMetaEq, htDone, htFr⟩ :=
    seedStoredMapsLoop_spec hOutCap hw hPlLoop (by omega) r.out.tables.next 0 s5 (Nat.zero_add _)
      (by omega) h0_5 h1_5 h4_5 h3_5 h5_5' h6_5 (fun _ hw0 => absurd hw0 (Nat.not_lt_zero _))
  have hSetupSteps : Steps ph.code input 9 (Phase.initial s0) s5 :=
    hs1.append (hs2.append (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5))))
  have hHalt : step ph.code input t = some (.halted t) :=
    haltAt_mkHaltPhase (hi := hi) (hw := hw) (seedStoredMapsInstrs (bits := bits) h100) _
      (by rw [hpct, hCodeLen]) (input := input)
  refine ⟨9 + kLoop + 1, t, by omega, (hSetupSteps.append hStepsLoop).halts hHalt, ?_, htDone, fun j hj => ?_⟩
  · apply hMeta.preserve (by rw [htMetaEq, hM_5]) ht0 ht1
    intro i hi22
    rw [htFr _ (Or.inr (Or.inl (by
      unfold priorBase metaArrBase inArcIdArrBase inStartArrBase
        trigNextArrBase trigHeadArrBase topoRankArrBase orderArrBase
      omega))), hd5']
  · rw [htFr j hj, hd5']

end SeedStoredMapsPhase

section BuildTrigger

variable {bits : Nat}

def buildTriggerSetupInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  metaLoadInstrs reg2 reg11 mIdxN (by dsimp only [mIdxN]; omega) ++
  (metaLoadInstrs reg3 reg11 mIdxNH (by dsimp only [mIdxNH]; omega) ++
  (metaLoadInstrs reg4 reg11 mIdxTrigHeadBase (by dsimp only [mIdxTrigHeadBase]; omega) ++
  (metaLoadInstrs reg5 reg11 mIdxTrigNextBase (by dsimp only [mIdxTrigNextBase]; omega) ++
  (metaLoadInstrs reg6 reg11 mIdxStoredBase (by dsimp only [mIdxStoredBase]; omega) ++
  (metaLoadInstrs reg7 reg11 mIdxTopoRankBase (by dsimp only [mIdxTopoRankBase]; omega) ++
  (metaLoadInstrs reg8 reg11 mIdxBackFstInBase (by dsimp only [mIdxBackFstInBase]; omega) ++
  (metaLoadInstrs reg9 reg11 mIdxBackSndInBase (by dsimp only [mIdxBackSndInBase]; omega) ++
  [ .mov reg10 reg0 ])))))))

def buildTriggerLoop1Instrs : List (Instr bits 15) :=
  [ .branchLt reg10 reg2 26 30
  , .add reg11 reg4 reg10
  , .storeData reg11 reg3
  , .add reg10 reg10 reg1
  , .goto 25
  , .mov reg10 reg0
  ]

def buildTriggerLoop2Instrs : List (Instr bits 15) :=
  [ .branchLt reg10 reg3 32 58 ] ++
  (mul18Instrs reg11 reg12 reg10 ++
  [ .add reg11 reg6 reg11
  , .loadData reg11 reg11
  , .branchLt reg0 reg11 40 56
  , .add reg11 reg8 reg10
  , .loadInput reg11 reg11
  , .sub reg11 reg11 reg1
  , .add reg11 reg7 reg11
  , .loadData reg11 reg11
  , .add reg12 reg9 reg10
  , .loadInput reg12 reg12
  , .add reg12 reg7 reg12
  , .loadData reg12 reg12
  , .branchLt reg11 reg12 50 51
  , .mov reg11 reg12
  , .add reg11 reg4 reg11
  , .loadData reg12 reg11
  , .add reg13 reg5 reg10
  , .storeData reg13 reg12
  , .storeData reg11 reg10
  , .add reg10 reg10 reg1
  , .goto 31
  ])

def buildTriggerInstrs (h100 : 100 ≤ 2 ^ bits) : List (Instr bits 15) :=
  buildTriggerSetupInstrs h100 ++ (buildTriggerLoop1Instrs ++ buildTriggerLoop2Instrs)

end BuildTrigger

section BuildTriggerPhase

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

def ListLinked (mem : Array (Word bits)) (nextBase sentinel : Nat) : Nat → List Nat → Prop
  | head, [] => head = sentinel
  | head, u :: us =>
    head = u ∧ u < sentinel ∧
    ∃ nxt : Nat, (mem[nextBase + u]?).map Fin.val = some nxt ∧
      ListLinked mem nextBase sentinel nxt us

theorem ListLinked.frame {mem1 mem2 : Array (Word bits)} {nextBase sentinel : Nat} :
    ∀ {head : Nat} {us : List Nat},
      (∀ u ∈ us, mem2[nextBase + u]? = mem1[nextBase + u]?) →
      ListLinked mem1 nextBase sentinel head us →
      ListLinked mem2 nextBase sentinel head us
  | head, [], _, h => h
  | head, u :: us, hEq, ⟨hh, hu, nxt, hNxt, hTail⟩ =>
    ⟨hh, hu, nxt, by rw [hEq u (by simp)]; exact hNxt,
      ListLinked.frame (fun w hw => hEq w (by simp [hw])) hTail⟩

private theorem validJumpForest_parentOf_zero {F : JumpForest} (hV : ValidJumpForest F) :
    F.parentOf 0 = 0 := by
  induction hV with
  | init => rfl
  | @appendLeaf F p hF _ ih =>
    have hPos : 0 < F.size := hF.exists_forestInvariant.choose_spec.size_pos
    rw [parentOf_appendLeaf_old F p hPos]
    exact ih

private theorem buildTriggerInstrs_nonHalt (h100 : 100 ≤ 2 ^ bits) :
    (buildTriggerInstrs (bits := bits) h100).all (nonHalt (L := DomL)) = true := by
  unfold buildTriggerInstrs
  refine list_all_append_true _ _ _ ?_ (list_all_append_true _ _ _ ?_ ?_)
  · unfold buildTriggerSetupInstrs
    simp only [List.all_append, List.all_cons, List.all_nil, metaLoadInstrs_nonHalt, nonHalt, Bool.and_true]
  · unfold buildTriggerLoop1Instrs
    simp only [List.all_cons, List.all_nil, nonHalt, Bool.and_true]
  · unfold buildTriggerLoop2Instrs mul18Instrs
    simp only [List.all_append, List.all_cons, List.all_nil, nonHalt, Bool.and_true]

def buildTriggerPhase (h100 : 100 ≤ 2 ^ bits) : Phase DomL :=
  mkHaltPhase (buildTriggerInstrs h100) (buildTriggerInstrs_nonHalt h100)

private theorem buildTriggerLoop1_spec {code : Program DomL} {input : Input DomL}
    {n N : Nat} (hOutCap : trigHeadArrBase n N + n ≤ workCap) (_hWorkFit : workCap ≤ 2 ^ bits)
    (hPl : Placed code 25 (buildTriggerLoop1Instrs (bits := bits)))
    (hSz : 31 < code.size) :
    ∀ (rem k : Nat) (st : State DomL),
      k + rem = n →
      st.pc = 25 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st reg2).val = n →
      (reg st reg3).val = N →
      (reg st reg4).val = trigHeadArrBase n N →
      (reg st reg5).val = trigNextArrBase n N →
      (reg st reg6).val = storedBase N →
      (reg st reg7).val = topoRankArrBase n N →
      (reg st reg8).val = 4 + n →
      (reg st reg9).val = 4 + n + N →
      (reg st reg10).val = k →
      (∀ i < k, (st.data[trigHeadArrBase n N + i]?).map Fin.val = some N) →
      ∃ steps : Nat, ∃ t : State DomL,
        steps ≤ 5 * rem + 2 ∧
        Steps code input steps st t ∧
        t.pc = 31 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ reg t rMeta = reg st rMeta ∧
        (reg t reg2).val = n ∧ (reg t reg3).val = N ∧
        (reg t reg4).val = trigHeadArrBase n N ∧ (reg t reg5).val = trigNextArrBase n N ∧
        (reg t reg6).val = storedBase N ∧ (reg t reg7).val = topoRankArrBase n N ∧
        (reg t reg8).val = 4 + n ∧ (reg t reg9).val = 4 + n + N ∧
        (reg t reg10).val = 0 ∧
        (∀ i < n, (t.data[trigHeadArrBase n N + i]?).map Fin.val = some N) ∧
        (∀ j, (j < trigHeadArrBase n N ∨ trigHeadArrBase n N + n ≤ j) → t.data[j]? = st.data[j]?) := by
  intro rem
  induction rem with
  | zero =>
    intro k st hSum hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hDone
    have hkEq : k = n := by omega
    obtain ⟨s1, hs1, hpc1, hr1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg10).val < (reg st reg2).val := by rw [h10, h2, hkEq]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpc1
    have hr1F := reg_of_regs_eq hr1
    have hm1 : code[s1.pc]? = some (.mov reg10 reg0) := by rw [hpc1]; exact hPl 5 _ rfl
    obtain ⟨t, hs2, hpct, h10t, hot, hdt⟩ := step_mov_at (input := input) hm1 (by omega)
    have hPres : ∀ r : Fin 15, r ≠ reg10 → reg t r = reg st r := fun r hr => by rw [hot r hr, hr1F]
    refine ⟨2, t, by omega, Steps.cons hs1 (steps_1_of_step hs2), (by rw [hpct, hpc1]),
      by rw [hPres reg0 (by intro h; cases h), h0],
      by rw [hPres reg1 (by intro h; cases h), h1],
      hPres rMeta (by intro h; cases h),
      by rw [hPres reg2 (by intro h; cases h), h2],
      by rw [hPres reg3 (by intro h; cases h), h3],
      by rw [hPres reg4 (by intro h; cases h), h4],
      by rw [hPres reg5 (by intro h; cases h), h5],
      by rw [hPres reg6 (by intro h; cases h), h6],
      by rw [hPres reg7 (by intro h; cases h), h7],
      by rw [hPres reg8 (by intro h; cases h), h8],
      by rw [hPres reg9 (by intro h; cases h), h9],
      by rw [h10t, hr1F, h0],
      fun i hi => by rw [hdt, hd1]; exact hDone i (hkEq ▸ hi),
      fun _ _ => by rw [hdt, hd1]⟩
  | succ rem ih =>
    intro k st hSum hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hDone
    have hkLt : k < n := by omega
    obtain ⟨s1, hs1, hpc1, hr1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    rw [ite_eq_left (by rw [h10, h2]; exact hkLt)] at hpc1
    have hr1F := reg_of_regs_eq hr1
    have ha1 : code[s1.pc]? = some (.add reg11 reg4 reg10) := by rw [hpc1]; exact hPl 1 _ rfl
    have hFitA : (reg s1 reg4).val + (reg s1 reg10).val < 2 ^ bits := by rw [hr1F, hr1F, h4, h10]; omega
    obtain ⟨s2, hs2, hpc2, h11_2, ho2, hd2⟩ := step_add_at (input := input) ha1 (by omega)
    have hAddr : (reg s2 reg11).val = trigHeadArrBase n N + k := by
      rw [h11_2, add_no_wrap _ _ hFitA, hr1F, hr1F, h4, h10]
    have hLt2 : (reg s2 reg11).val < s2.data.size := lt_data_size (by rw [hAddr]; omega)
    have hst : code[s2.pc]? = some (.storeData reg11 reg3) := by rw [hpc2, hpc1]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, hpc3, hreg3, hd3⟩ := step_storeData_opaque (input := input) hst hLt2 (by omega)
    have hr3F := reg_of_regs_eq hreg3
    have h10_3 : (reg s3 reg10).val = k := by rw [hr3F, ho2 reg10 (by intro h; cases h), hr1F, h10]
    have h1_3 : (reg s3 reg1).val = 1 := by rw [hr3F, ho2 reg1 (by intro h; cases h), hr1F, h1]
    have hFitK : (reg s3 reg10).val + (reg s3 reg1).val < 2 ^ bits := by rw [h10_3, h1_3]; omega
    have haInc : code[s3.pc]? = some (.add reg10 reg10 reg1) := by rw [hpc3, hpc2, hpc1]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, hpc4, h10_4, ho4, hd4⟩ := step_add_at (input := input) haInc (by omega)
    have hg4 : code[s4.pc]? = some (.goto 25) := by rw [hpc4, hpc3, hpc2, hpc1]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, hpc5, hr5, hd5⟩ := step_goto_at (input := input) hg4 (by omega)
    have hr5F := reg_of_regs_eq hr5
    have hd2' : s2.data = st.data := by rw [hd2, hd1]
    have hLt2St : (reg s2 reg11).val < st.data.size := by rw [← hd2']; exact hLt2
    have hs5Data : s5.data = st.data.set (reg s2 reg11).val (reg s2 reg3) hLt2St := by
      rw [hd5, hd4, hd3]; exact array_set_eq_of_data_eq hd2' hLt2 hLt2St
    have hPres5 : ∀ r : Fin 15, r ≠ reg10 → r ≠ reg11 → reg s5 r = reg st r := fun r hr10 hr11 => by
      rw [hr5F, ho4 r hr10, hr3F, ho2 r hr11, hr1F]
    have h3_2 : (reg s2 reg3).val = N := by rw [ho2 reg3 (by intro h; cases h), hr1F, h3]
    have hStep5 : Steps code input 5 st s5 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (steps_1_of_step hs5))))
    obtain ⟨kRest, t, hkRest, hStepsRest, hpct, ht0, ht1, htM, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9,
        ht10, htDone, htFr⟩ :=
      ih (k + 1) s5 (by omega) hpc5
        (by rw [hPres5 reg0 (by intro h; cases h) (by intro h; cases h), h0])
        (by rw [hPres5 reg1 (by intro h; cases h) (by intro h; cases h), h1])
        (by rw [hPres5 reg2 (by intro h; cases h) (by intro h; cases h), h2])
        (by rw [hPres5 reg3 (by intro h; cases h) (by intro h; cases h), h3])
        (by rw [hPres5 reg4 (by intro h; cases h) (by intro h; cases h), h4])
        (by rw [hPres5 reg5 (by intro h; cases h) (by intro h; cases h), h5])
        (by rw [hPres5 reg6 (by intro h; cases h) (by intro h; cases h), h6])
        (by rw [hPres5 reg7 (by intro h; cases h) (by intro h; cases h), h7])
        (by rw [hPres5 reg8 (by intro h; cases h) (by intro h; cases h), h8])
        (by rw [hPres5 reg9 (by intro h; cases h) (by intro h; cases h), h9])
        (by rw [hr5F, h10_4, add_no_wrap _ _ hFitK, h10_3, h1_3])
        (fun i hi => by
          rw [hs5Data]
          by_cases hik : i = k
          · subst hik; rw [← hAddr, Array.getElem?_set_self hLt2St, Option.map_some, h3_2]
          · have hNe : trigHeadArrBase n N + i ≠ (reg s2 reg11).val := by rw [hAddr]; omega
            rw [Array.getElem?_set_ne hLt2St hNe.symm]; exact hDone i (by omega))
    refine ⟨5 + kRest, t, by omega, hStep5.append hStepsRest, hpct, ht0, ht1,
      htM.trans (hPres5 rMeta (by intro h; cases h) (by intro h; cases h)),
      ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, ht10, htDone, fun j hj => ?_⟩
    rw [htFr j hj, hs5Data]
    have hNe : j ≠ (reg s2 reg11).val := by rw [hAddr]; rcases hj with h | h <;> omega
    exact Array.getElem?_set_ne hLt2St hNe.symm

private theorem buildTriggerLoop2_push_step {code : Program DomL} {input : Input DomL}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {p : ForestDictionary.Rows H} {data : Array (Vertex H)}
    {size_data : data.size = H.vertexCount} {rank : Vertex H → Nat}
    {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult p data size_data rank large}
    {entryRank : Fin H.origVertexCount → Nat} {nGlobal : Nat}
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (_hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap) (_hWorkFit : workCap ≤ 2 ^ bits)
    (rankKahn : Vertex H → Nat) (hRkLt : ∀ v : Vertex H, rankKahn v < H.vertexCount)
    (hPlBody : Placed code 37 ((buildTriggerLoop2Instrs (bits := bits)).drop 6))
    (hSz : 58 < code.size)
    (_hNLe : r.out.tables.next ≤ H.vertexCount + 1)
    (hInSBound : inStartArrBase H.vertexCount r.out.tables.next ≤ workCap)
    (u : Nat) (huLt : u < r.out.tables.next)
    (P : CutPair H) (hPBack : r.out.tables.back[u]? = some (some P))
    (oldHd : Nat)
    (st s9 : State DomL)
    (hpc9 : s9.pc = 40)
    (hd9' : s9.data = st.data)
    (hPres9 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s9 r = reg st r)
    (h1 : (reg st reg1).val = 1)
    (h4 : (reg st reg4).val = trigHeadArrBase H.vertexCount r.out.tables.next)
    (h5 : (reg st reg5).val = trigNextArrBase H.vertexCount r.out.tables.next)
    (h7 : (reg st reg7).val = topoRankArrBase H.vertexCount r.out.tables.next)
    (h8 : (reg st reg8).val = 4 + H.vertexCount)
    (h9 : (reg st reg9).val = 4 + H.vertexCount + r.out.tables.next)
    (h10 : (reg st reg10).val = u)
    (hTR : ∀ v : Vertex H,
      (st.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
        some (rankKahn v))
    (hOldHd : (st.data[trigHeadArrBase H.vertexCount r.out.tables.next +
        max (rankKahn P.fst) (rankKahn P.snd)]?).map Fin.val = some oldHd) :
    let N := r.out.tables.next
    let n := H.vertexCount
    let tr := max (rankKahn P.fst) (rankKahn P.snd)
    ∃ (kMax : Nat) (s27 : State DomL) (wNew wOld : Word bits),
      kMax ≤ 1 ∧
      Steps code input (10 + kMax + 7) s9 s27 ∧
      s27.pc = 31 ∧
      wNew.val = u ∧
      wOld.val = oldHd ∧
      (∀ a, s27.data[a]? =
        if a = trigHeadArrBase n N + tr then some wNew
        else if a = trigNextArrBase n N + u then some wOld
        else st.data[a]?) ∧
      (∀ r : Fin 15, r ≠ reg10 → r ≠ reg11 → r ≠ reg12 → r ≠ reg13 → reg s27 r = reg st r) ∧
      (reg s27 reg10).val = u + 1 := by
  intro N n tr
  have hB1 : trigHeadArrBase n N + n = trigNextArrBase n N := rfl
  have hB2 : trigNextArrBase n N + N = inStartArrBase n N := rfl
  have hTRBound : topoRankArrBase n N + n = trigHeadArrBase n N := rfl
  have hTrWork : trigNextArrBase n N + N ≤ workCap := by rw [hB2]; exact hInSBound
  have hThWork : trigHeadArrBase n N + n ≤ workCap := by rw [hB1]; omega
  have hToWork : topoRankArrBase n N + n ≤ workCap := by rw [hTRBound]; omega
  obtain ⟨o, hoBack, hBack1, hBack2⟩ := hIn.back_at ⟨u, huLt⟩
  have hoEq : o = some P := Option.some.inj (hoBack.symm.trans hPBack)
  rw [hoEq] at hBack1 hBack2
  have haLt : P.fst.val < n := P.fst.isLt
  have hbLt : P.snd.val < n := P.snd.isLt
  have hRaLt : rankKahn P.fst < n := hRkLt P.fst
  have hRbLt : rankKahn P.snd < n := hRkLt P.snd
  have hTrLt : tr < n := Nat.max_lt.mpr ⟨hRaLt, hRbLt⟩
  have h8_9 : (reg s9 reg8).val = 4 + n := by
    rw [hPres9 reg8 (by intro h; cases h) (by intro h; cases h), h8]
  have h10_9 : (reg s9 reg10).val = u := by
    rw [hPres9 reg10 (by intro h; cases h) (by intro h; cases h), h10]
  have haFst : code[s9.pc]? = some (.add reg11 reg8 reg10) := by
    rw [hpc9]; exact hPlBody 3 _ rfl
  have hCapIn : 4 + n + 4 * N + 3 * H.arcCount ≤ inputCap := hIn.cap_ge
  obtain ⟨s10, hs10, hpc10, h11_10, ho10, hd10⟩ := step_add_at (input := input) haFst (by omega)
  have hFstAddr : (reg s10 reg11).val = 4 + n + u := by
    rw [h11_10, add_no_wrap _ _ (by rw [h8_9, h10_9]; omega), h8_9, h10_9]
  obtain ⟨wBf, hwBf, hwBfV⟩ := Option.map_eq_some_iff.mp hBack1
  have hlFst : code[s10.pc]? = some (.loadInput reg11 reg11) := by
    rw [hpc10, hpc9]; exact hPlBody 4 _ rfl
  obtain ⟨s11, hs11, hpc11, h11_11, ho11, hd11⟩ := step_loadInput_at (input := input) hlFst (by omega)
    (by rw [hFstAddr]; exact hwBf)
  have hBfVal : (reg s11 reg11).val = P.fst.val + 1 := by
    rw [h11_11, hwBfV]; rfl
  have h1_11 : (reg s11 reg1).val = 1 := by
    rw [ho11 reg1 (by intro h; cases h), ho10 reg1 (by intro h; cases h),
      hPres9 reg1 (by intro h; cases h) (by intro h; cases h), h1]
  have hsFst : code[s11.pc]? = some (.sub reg11 reg11 reg1) := by
    rw [hpc11, hpc10, hpc9]; exact hPlBody 5 _ rfl
  obtain ⟨s12, hs12, hpc12, h11_12, ho12, hd12⟩ := step_sub_at (input := input) hsFst (by omega)
  have hAVal : (reg s12 reg11).val = P.fst.val := by
    rw [h11_12, sub_exact (by rw [hBfVal, h1_11]; omega), hBfVal, h1_11]; omega
  have h7_12 : (reg s12 reg7).val = topoRankArrBase n N := by
    rw [ho12 reg7 (by intro h; cases h), ho11 reg7 (by intro h; cases h),
      ho10 reg7 (by intro h; cases h),
      hPres9 reg7 (by intro h; cases h) (by intro h; cases h), h7]
  have haTR1 : code[s12.pc]? = some (.add reg11 reg7 reg11) := by
    rw [hpc12, hpc11, hpc10, hpc9]; exact hPlBody 6 _ rfl
  obtain ⟨s13, hs13, hpc13, h11_13, ho13, hd13⟩ := step_add_at (input := input) haTR1 (by omega)
  have hTR1Addr : (reg s13 reg11).val = topoRankArrBase n N + P.fst.val := by
    rw [h11_13, add_no_wrap _ _ (by rw [h7_12, hAVal]; omega), h7_12, hAVal]
  have hd13' : s13.data = st.data := by rw [hd13, hd12, hd11, hd10, hd9']
  obtain ⟨wRa, hwRa, hwRaV⟩ := Option.map_eq_some_iff.mp (hTR P.fst)
  have hlTR1 : code[s13.pc]? = some (.loadData reg11 reg11) := by
    rw [hpc13, hpc12, hpc11, hpc10, hpc9]; exact hPlBody 7 _ rfl
  obtain ⟨s14, hs14, hpc14, h11_14, ho14, hd14⟩ := step_loadData_at (input := input) hlTR1 (by omega)
    (by rw [hTR1Addr, hd13']; exact hwRa)
  have hRaVal : (reg s14 reg11).val = rankKahn P.fst := by rw [h11_14, hwRaV]
  have h9_14 : (reg s14 reg9).val = 4 + n + N := by
    rw [ho14 reg9 (by intro h; cases h), ho13 reg9 (by intro h; cases h),
      ho12 reg9 (by intro h; cases h), ho11 reg9 (by intro h; cases h),
      ho10 reg9 (by intro h; cases h),
      hPres9 reg9 (by intro h; cases h) (by intro h; cases h), h9]
  have h10_14 : (reg s14 reg10).val = u := by
    rw [ho14 reg10 (by intro h; cases h), ho13 reg10 (by intro h; cases h),
      ho12 reg10 (by intro h; cases h), ho11 reg10 (by intro h; cases h),
      ho10 reg10 (by intro h; cases h), h10_9]
  have haSnd : code[s14.pc]? = some (.add reg12 reg9 reg10) := by
    rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9]; exact hPlBody 8 _ rfl
  obtain ⟨s15, hs15, hpc15, h12_15, ho15, hd15⟩ := step_add_at (input := input) haSnd (by omega)
  have hSndAddr : (reg s15 reg12).val = 4 + n + N + u := by
    rw [h12_15, add_no_wrap _ _ (by rw [h9_14, h10_14]; omega), h9_14, h10_14]
  obtain ⟨wBs, hwBs, hwBsV⟩ := Option.map_eq_some_iff.mp hBack2
  have hlSnd : code[s15.pc]? = some (.loadInput reg12 reg12) := by
    rw [hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9]; exact hPlBody 9 _ rfl
  obtain ⟨s16, hs16, hpc16, h12_16, ho16, hd16⟩ := step_loadInput_at (input := input) hlSnd (by omega)
    (by rw [hSndAddr]; exact hwBs)
  have hBVal : (reg s16 reg12).val = P.snd.val := by rw [h12_16, hwBsV]; rfl
  have h7_16 : (reg s16 reg7).val = topoRankArrBase n N := by
    rw [ho16 reg7 (by intro h; cases h), ho15 reg7 (by intro h; cases h),
      ho14 reg7 (by intro h; cases h), ho13 reg7 (by intro h; cases h), h7_12]
  have haTR2 : code[s16.pc]? = some (.add reg12 reg7 reg12) := by
    rw [hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9]; exact hPlBody 10 _ rfl
  obtain ⟨s17, hs17, hpc17, h12_17, ho17, hd17⟩ := step_add_at (input := input) haTR2 (by omega)
  have hTR2Addr : (reg s17 reg12).val = topoRankArrBase n N + P.snd.val := by
    rw [h12_17, add_no_wrap _ _ (by rw [h7_16, hBVal]; omega), h7_16, hBVal]
  have hd17' : s17.data = st.data := by rw [hd17, hd16, hd15, hd14, hd13']
  obtain ⟨wRb, hwRb, hwRbV⟩ := Option.map_eq_some_iff.mp (hTR P.snd)
  have hlTR2 : code[s17.pc]? = some (.loadData reg12 reg12) := by
    rw [hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9]; exact hPlBody 11 _ rfl
  obtain ⟨s18, hs18, hpc18, h12_18, ho18, hd18⟩ := step_loadData_at (input := input) hlTR2 (by omega)
    (by rw [hTR2Addr, hd17']; exact hwRb)
  have hRbVal : (reg s18 reg12).val = rankKahn P.snd := by rw [h12_18, hwRbV]
  have h11_18 : (reg s18 reg11).val = rankKahn P.fst := by
    rw [ho18 reg11 (by intro h; cases h), ho17 reg11 (by intro h; cases h),
      ho16 reg11 (by intro h; cases h), ho15 reg11 (by intro h; cases h), hRaVal]
  have hPres18 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s18 r = reg st r :=
    fun r hr11 hr12 => by
      rw [ho18 r hr12, ho17 r hr12, ho16 r hr12, ho15 r hr12, ho14 r hr11, ho13 r hr11,
        ho12 r hr11, ho11 r hr11, ho10 r hr11, hPres9 r hr11 hr12]
  have hbrMax : code[s18.pc]? = some (.branchLt reg11 reg12 50 51) := by
    rw [hpc18, hpc17, hpc16, hpc15, hpc14, hpc13, hpc12, hpc11, hpc10, hpc9]; exact hPlBody 12 _ rfl
  obtain ⟨s19, hs19, hpc19, hr19, hd19⟩ := step_branchLt_at (input := input) hbrMax (by split <;> omega)
  have hr19F := reg_of_regs_eq hr19
  have hMaxJoin : ∃ (kMax : Nat) (s20 : State DomL),
      kMax ≤ 1 ∧ Steps code input kMax s19 s20 ∧ s20.pc = 51 ∧
      s20.data = st.data ∧ (reg s20 reg11).val = tr ∧
      ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s20 r = reg st r := by
    by_cases hLtR : rankKahn P.fst < rankKahn P.snd
    · rw [ite_eq_left (by rw [h11_18, hRbVal]; exact hLtR)] at hpc19
      have hmM : code[s19.pc]? = some (.mov reg11 reg12) := by rw [hpc19]; exact hPlBody 13 _ rfl
      obtain ⟨s20, hs20, hpc20, h11_20, ho20, hd20⟩ := step_mov_at (input := input) hmM (by omega)
      refine ⟨1, s20, Nat.le_refl _, steps_1_of_step hs20, (by rw [hpc20, hpc19]),
        by rw [hd20, hd19, hd18, hd17'],
        by rw [h11_20, hr19F, hRbVal]; exact (Nat.max_eq_right (Nat.le_of_lt hLtR)).symm,
        fun r hr11 hr12 => by rw [ho20 r hr11, hr19F, hPres18 r hr11 hr12]⟩
    · rw [ite_eq_right (by rw [h11_18, hRbVal]; exact hLtR)] at hpc19
      refine ⟨0, s19, Nat.zero_le _, Steps.zero s19, hpc19,
        by rw [hd19, hd18, hd17'],
        by rw [hr19F, h11_18]; exact (Nat.max_eq_left (Nat.le_of_not_gt hLtR)).symm,
        fun r hr11 hr12 => by rw [hr19F, hPres18 r hr11 hr12]⟩
  obtain ⟨kMax, s20, hkMax, hStepsMax, hpc20, hd20', h11_20, hPres20⟩ := hMaxJoin
  have h4_20 : (reg s20 reg4).val = trigHeadArrBase n N := by
    rw [hPres20 reg4 (by intro h; cases h) (by intro h; cases h), h4]
  have haTH : code[s20.pc]? = some (.add reg11 reg4 reg11) := by rw [hpc20]; exact hPlBody 14 _ rfl
  obtain ⟨s21, hs21, hpc21, h11_21, ho21, hd21⟩ := step_add_at (input := input) haTH (by omega)
  have hTHAddr : (reg s21 reg11).val = trigHeadArrBase n N + tr := by
    rw [h11_21, add_no_wrap _ _ (by rw [h4_20, h11_20]; omega), h4_20, h11_20]
  obtain ⟨wHd, hwHd, hwHdV⟩ := Option.map_eq_some_iff.mp hOldHd
  have hlTH : code[s21.pc]? = some (.loadData reg12 reg11) := by
    rw [hpc21, hpc20]; exact hPlBody 15 _ rfl
  obtain ⟨s22, hs22, hpc22, h12_22, ho22, hd22⟩ := step_loadData_at (input := input) hlTH (by omega)
    (by rw [hTHAddr, hd21, hd20']; exact hwHd)
  have hOldHdVal : (reg s22 reg12).val = oldHd := by rw [h12_22, hwHdV]
  have h5_22 : (reg s22 reg5).val = trigNextArrBase n N := by
    rw [ho22 reg5 (by intro h; cases h), ho21 reg5 (by intro h; cases h),
      hPres20 reg5 (by intro h; cases h) (by intro h; cases h), h5]
  have h10_22 : (reg s22 reg10).val = u := by
    rw [ho22 reg10 (by intro h; cases h), ho21 reg10 (by intro h; cases h),
      hPres20 reg10 (by intro h; cases h) (by intro h; cases h), h10]
  have haTN : code[s22.pc]? = some (.add reg13 reg5 reg10) := by
    rw [hpc22, hpc21, hpc20]; exact hPlBody 16 _ rfl
  obtain ⟨s23, hs23, hpc23, h13_23, ho23, hd23⟩ := step_add_at (input := input) haTN (by omega)
  have hTNAddr : (reg s23 reg13).val = trigNextArrBase n N + u := by
    rw [h13_23, add_no_wrap _ _ (by rw [h5_22, h10_22]; omega), h5_22, h10_22]
  have hLtTN : (reg s23 reg13).val < s23.data.size := lt_data_size (by rw [hTNAddr]; omega)
  have hstTN : code[s23.pc]? = some (.storeData reg13 reg12) := by
    rw [hpc23, hpc22, hpc21, hpc20]; exact hPlBody 17 _ rfl
  obtain ⟨s24, hs24, hpc24, hreg24, hd24⟩ := step_storeData_opaque (input := input) hstTN hLtTN (by omega)
  have hr24F := reg_of_regs_eq hreg24
  have hTHAddr24 : (reg s24 reg11).val = trigHeadArrBase n N + tr := by
    rw [hr24F, ho23 reg11 (by intro h; cases h), ho22 reg11 (by intro h; cases h), hTHAddr]
  have hLtTH : (reg s24 reg11).val < s24.data.size := lt_data_size (by rw [hTHAddr24]; omega)
  have hstTH : code[s24.pc]? = some (.storeData reg11 reg10) := by
    rw [hpc24, hpc23, hpc22, hpc21, hpc20]; exact hPlBody 18 _ rfl
  obtain ⟨s25, hs25, hpc25, hreg25, hd25⟩ := step_storeData_opaque (input := input) hstTH hLtTH (by omega)
  have hr25F := reg_of_regs_eq hreg25
  have h10_25 : (reg s25 reg10).val = u := by
    rw [hr25F, hr24F, ho23 reg10 (by intro h; cases h), h10_22]
  have h1_25 : (reg s25 reg1).val = 1 := by
    rw [hr25F, hr24F, ho23 reg1 (by intro h; cases h), ho22 reg1 (by intro h; cases h),
      ho21 reg1 (by intro h; cases h),
      hPres20 reg1 (by intro h; cases h) (by intro h; cases h), h1]
  have haInc : code[s25.pc]? = some (.add reg10 reg10 reg1) := by
    rw [hpc25, hpc24, hpc23, hpc22, hpc21, hpc20]; exact hPlBody 19 _ rfl
  obtain ⟨s26, hs26, hpc26, h10_26, ho26, hd26⟩ := step_add_at (input := input) haInc (by omega)
  have hg26 : code[s26.pc]? = some (.goto 31) := by
    rw [hpc26, hpc25, hpc24, hpc23, hpc22, hpc21, hpc20]; exact hPlBody 20 _ rfl
  obtain ⟨s27, hs27, hpc27, hr27, hd27⟩ := step_goto_at (input := input) hg26 (by omega)
  have hr27F := reg_of_regs_eq hr27
  have hd23' : s23.data = st.data := by rw [hd23, hd22, hd21, hd20']
  have hS24At : ∀ a, s24.data[a]? =
      if a = trigNextArrBase n N + u then some (reg s23 reg12) else st.data[a]? := fun a => by
    rw [hd24]
    by_cases ha2 : a = trigNextArrBase n N + u
    · subst ha2; rw [ite_eq_left rfl, ← hTNAddr, Array.getElem?_set_self hLtTN]
    · rw [ite_eq_right ha2, Array.getElem?_set_ne hLtTN (by rw [hTNAddr]; exact Ne.symm ha2), hd23']
  have hS27At : ∀ a, s27.data[a]? =
      if a = trigHeadArrBase n N + tr then some (reg s24 reg10)
      else if a = trigNextArrBase n N + u then some (reg s23 reg12)
      else st.data[a]? := fun a => by
    rw [hd27, hd26, hd25]
    by_cases ha1 : a = trigHeadArrBase n N + tr
    · subst ha1; rw [ite_eq_left rfl, ← hTHAddr24, Array.getElem?_set_self hLtTH]
    · rw [ite_eq_right ha1, Array.getElem?_set_ne hLtTH (by rw [hTHAddr24]; exact Ne.symm ha1), hS24At a]
  have hPres27 : ∀ r : Fin 15, r ≠ reg10 → r ≠ reg11 → r ≠ reg12 → r ≠ reg13 → reg s27 r = reg st r :=
    fun r hr10 hr11 hr12 hr13 => by
      rw [hr27F, ho26 r hr10, hr25F, hr24F, ho23 r hr13, ho22 r hr12, ho21 r hr11, hPres20 r hr11 hr12]
  have hPre10 : Steps code input 10 s9 s19 :=
    Steps.cons hs10 (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14
      (Steps.cons hs15 (Steps.cons hs16 (Steps.cons hs17 (Steps.cons hs18 (steps_1_of_step hs19)))))))))
  have hPost7 : Steps code input 7 s20 s27 :=
    Steps.cons hs21 (Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24
      (Steps.cons hs25 (Steps.cons hs26 (steps_1_of_step hs27))))))
  refine ⟨kMax, s27, reg s24 reg10, reg s23 reg12, hkMax, (hPre10.append hStepsMax).append hPost7,
    hpc27, ?_, ?_, hS27At, hPres27, ?_⟩
  · rw [hr24F, ho23 reg10 (by intro h; cases h), h10_22]
  · rw [ho23 reg12 (by intro h; cases h), hOldHdVal]
  · rw [hr27F, h10_26, add_no_wrap _ _ (by rw [h10_25, h1_25]; omega), h10_25, h1_25]

private theorem buildTriggerLoop2_spec {code : Program DomL} {input : Input DomL}
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
    (hIn : ExitBuildInput input H r entryRank nGlobal)
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap) (hWorkFit : workCap ≤ 2 ^ bits)
    (rankKahn : Vertex H → Nat) (hRkLt : ∀ v : Vertex H, rankKahn v < H.vertexCount)
    (hPl : Placed code 31 (buildTriggerLoop2Instrs (bits := bits)))
    (hSz : 58 < code.size) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let N := r.out.tables.next
    let n := H.vertexCount
    ∀ (rem u : Nat) (buckets : Nat → List Nat) (st : State DomL),
      u + rem = N →
      st.pc = 31 →
      (reg st reg0).val = 0 →
      (reg st reg1).val = 1 →
      (reg st reg2).val = n →
      (reg st reg3).val = N →
      (reg st reg4).val = trigHeadArrBase n N →
      (reg st reg5).val = trigNextArrBase n N →
      (reg st reg6).val = storedBase N →
      (reg st reg7).val = topoRankArrBase n N →
      (reg st reg8).val = 4 + n →
      (reg st reg9).val = 4 + n + N →
      (reg st reg10).val = u →
      (∀ w : Fin N,
        (st.data[storedBase N + 18 * w.val]?).map Fin.val = some (B.F.parentOf w.val)) →
      (∀ v : Vertex H,
        (st.data[topoRankArrBase n N + v.val]?).map Fin.val = some (rankKahn v)) →
      (∀ tr < n, (buckets tr).Nodup ∧ ∀ w ∈ buckets tr,
        w < u ∧ 0 < B.F.parentOf w ∧ ∃ P : CutPair H,
          r.out.tables.back[w]? = some (some P) ∧ max (rankKahn P.fst) (rankKahn P.snd) = tr) →
      (∀ w < u, 0 < B.F.parentOf w →
        ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
          w ∈ buckets (max (rankKahn P.fst) (rankKahn P.snd))) →
      (∀ tr < n, ∃ hd : Nat,
        (st.data[trigHeadArrBase n N + tr]?).map Fin.val = some hd ∧
        ListLinked st.data (trigNextArrBase n N) N hd (buckets tr)) →
      ∃ steps : Nat, ∃ buckets1 : Nat → List Nat, ∃ t : State DomL,
        steps ≤ 27 * rem + 1 ∧
        Steps code input steps st t ∧
        t.pc = 58 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ reg t rMeta = reg st rMeta ∧
        (∀ tr < n, (buckets1 tr).Nodup ∧ ∀ w ∈ buckets1 tr,
          w < N ∧ 0 < B.F.parentOf w ∧ ∃ P : CutPair H,
            r.out.tables.back[w]? = some (some P) ∧ max (rankKahn P.fst) (rankKahn P.snd) = tr) ∧
        (∀ w < N, 0 < B.F.parentOf w →
          ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
            w ∈ buckets1 (max (rankKahn P.fst) (rankKahn P.snd))) ∧
        (∀ tr < n, ∃ hd : Nat,
          (t.data[trigHeadArrBase n N + tr]?).map Fin.val = some hd ∧
          ListLinked t.data (trigNextArrBase n N) N hd (buckets1 tr)) ∧
        (∀ j, (j < trigHeadArrBase n N ∨ inStartArrBase n N ≤ j) →
          t.data[j]? = st.data[j]?) := by
  intro B N n rem
  induction rem with
  | zero =>
    intro u buckets st hSum hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hPar hTR hBInv hCov hLinked
    have huEq : u = N := by omega
    obtain ⟨t, hs, hpct, hrt, hdt⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    have hF : ¬ (reg st reg10).val < (reg st reg3).val := by rw [h10, h3, huEq]; exact Nat.lt_irrefl _
    rw [ite_eq_right hF] at hpct
    have hrtF := reg_of_regs_eq hrt
    refine ⟨1, buckets, t, by omega, steps_1_of_step hs, hpct,
      by rw [hrtF, h0], by rw [hrtF, h1], hrtF rMeta,
      fun tr htr => ⟨(hBInv tr htr).1, fun w hw => by
        obtain ⟨hwu, hP⟩ := (hBInv tr htr).2 w hw
        exact ⟨huEq ▸ hwu, hP⟩⟩,
      fun w hw => hCov w (huEq ▸ hw),
      fun tr htr => by
        obtain ⟨hd, hHd, hLk⟩ := hLinked tr htr
        exact ⟨hd, by rw [hdt]; exact hHd, ListLinked.frame (fun _ _ => by rw [hdt]) hLk⟩,
      fun _ _ => by rw [hdt]⟩
  | succ rem ih =>
    intro u buckets st hSum hpc h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hPar hTR hBInv hCov hLinked
    have huLt : u < N := by omega
    have hNLe : N ≤ n + 1 := by
      have hEq := nodeCount_eq_next r.index.ok
      have hLe := nodeCount_le r.index.ok
      omega
    have h18u : storedBase N + 18 * u < 2 ^ bits := by
      unfold storedBase
      unfold exitWorkCap at hWork
      omega
    have hInSBound : inStartArrBase n N ≤ workCap := by
      have : metaArrBase n H.arcCount N = 20 * N + 10 * n + H.arcCount + 1 := metaArrBase_eq _ _ _
      unfold metaArrBase inArcIdArrBase at this
      unfold exitWorkCap at hWork; omega
    have hB1 : trigHeadArrBase n N + n = trigNextArrBase n N := rfl
    have hB2 : trigNextArrBase n N + N = inStartArrBase n N := rfl
    have hStoredLt : ∀ w : Fin N, storedBase N + 18 * w.val < trigHeadArrBase n N := fun w => by
      have := w.isLt
      unfold storedBase trigHeadArrBase topoRankArrBase orderArrBase
      omega
    have hTRLt : ∀ v : Vertex H, topoRankArrBase n N + v.val < trigHeadArrBase n N := fun v => by
      have := v.isLt
      unfold trigHeadArrBase
      omega
    obtain ⟨s1, hs1, hpc1, hr1, hd1⟩ := step_branchLt_at (input := input)
      (by rw [hpc]; exact hPl 0 _ rfl) (by split <;> omega)
    rw [ite_eq_left (by rw [h10, h3]; exact huLt)] at hpc1
    have hr1F := reg_of_regs_eq hr1
    -- `mul18Instrs reg11 reg12 reg10` at 32..36
    have hPlMul : Placed code 32 (mul18Instrs (bits := bits) reg11 reg12 reg10) := by
      have hR := Placed_append_right (by unfold buildTriggerLoop2Instrs at hPl; exact hPl)
      rw [show ([Instr.branchLt reg10 reg3 32 58] : List (Instr bits 15)).length = 1 by rfl] at hR
      exact Placed_append_left hR
    have hPlBody := Placed_append_right (by
      have hR := Placed_append_right (by unfold buildTriggerLoop2Instrs at hPl; exact hPl)
      rw [show ([Instr.branchLt reg10 reg3 32 58] : List (Instr bits 15)).length = 1 by rfl] at hR
      exact hR)
    rw [show (mul18Instrs (bits := bits) reg11 reg12 reg10).length = 5 by rfl] at hPlBody
    have h10_1 : (reg s1 reg10).val = u := by rw [hr1F, h10]
    have haM0 : code[s1.pc]? = some (.add reg12 reg10 reg10) := by rw [hpc1]; exact hPlMul 0 _ rfl
    obtain ⟨s2, hs2, hpc2, h12_2, ho2, hd2⟩ := step_add_at (input := input) haM0 (by omega)
    have h12Val2 : (reg s2 reg12).val = 2 * u := by
      rw [h12_2, add_no_wrap _ _ (by rw [h10_1]; omega), h10_1]; omega
    have haM1 : code[s2.pc]? = some (.add reg11 reg12 reg12) := by rw [hpc2, hpc1]; exact hPlMul 1 _ rfl
    obtain ⟨s3, hs3, hpc3, h11_3, ho3, hd3⟩ := step_add_at (input := input) haM1 (by omega)
    have h11Val3 : (reg s3 reg11).val = 4 * u := by
      rw [h11_3, add_no_wrap _ _ (by rw [h12Val2]; omega), h12Val2]; omega
    have haM2 : code[s3.pc]? = some (.add reg11 reg11 reg11) := by rw [hpc3, hpc2, hpc1]; exact hPlMul 2 _ rfl
    obtain ⟨s4, hs4, hpc4, h11_4, ho4, hd4⟩ := step_add_at (input := input) haM2 (by omega)
    have h11Val4 : (reg s4 reg11).val = 8 * u := by
      rw [h11_4, add_no_wrap _ _ (by rw [h11Val3]; omega), h11Val3]; omega
    have haM3 : code[s4.pc]? = some (.add reg11 reg11 reg11) := by rw [hpc4, hpc3, hpc2, hpc1]; exact hPlMul 3 _ rfl
    obtain ⟨s5, hs5, hpc5, h11_5, ho5, hd5⟩ := step_add_at (input := input) haM3 (by omega)
    have h11Val5 : (reg s5 reg11).val = 16 * u := by
      rw [h11_5, add_no_wrap _ _ (by rw [h11Val4]; omega), h11Val4]; omega
    have h12_5 : (reg s5 reg12).val = 2 * u := by
      rw [ho5 reg12 (by intro h; cases h), ho4 reg12 (by intro h; cases h),
        ho3 reg12 (by intro h; cases h), h12Val2]
    have haM4 : code[s5.pc]? = some (.add reg11 reg11 reg12) := by
      rw [hpc5, hpc4, hpc3, hpc2, hpc1]; exact hPlMul 4 _ rfl
    obtain ⟨s6, hs6, hpc6, h11_6, ho6, hd6⟩ := step_add_at (input := input) haM4 (by omega)
    have h11Val6 : (reg s6 reg11).val = 18 * u := by
      rw [h11_6, add_no_wrap _ _ (by rw [h11Val5, h12_5]; omega), h11Val5, h12_5]; omega
    have hPres6 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s6 r = reg st r := fun r hr11 hr12 => by
      rw [ho6 r hr11, ho5 r hr11, ho4 r hr11, ho3 r hr11, ho2 r hr12, hr1F]
    have hd6' : s6.data = st.data := by rw [hd6, hd5, hd4, hd3, hd2, hd1]
    have h6_6 : (reg s6 reg6).val = storedBase N := by
      rw [hPres6 reg6 (by intro h; cases h) (by intro h; cases h), h6]
    have haP : code[s6.pc]? = some (.add reg11 reg6 reg11) := by
      rw [show s6.pc = 37 by omega]; exact hPlBody 0 _ rfl
    obtain ⟨s7, hs7, hpc7, h11_7, ho7, hd7⟩ := step_add_at (input := input) haP (by omega)
    have hParAddr : (reg s7 reg11).val = storedBase N + 18 * u := by
      rw [h11_7, add_no_wrap _ _ (by rw [h6_6, h11Val6]; omega), h6_6, h11Val6]
    obtain ⟨wPar, hwPar, hwParV⟩ := Option.map_eq_some_iff.mp (hPar ⟨u, huLt⟩)
    have hlP : code[s7.pc]? = some (.loadData reg11 reg11) := by
      rw [show s7.pc = 38 by omega]; exact hPlBody 1 _ rfl
    obtain ⟨s8, hs8, hpc8, h11_8, ho8, hd8⟩ := step_loadData_at (input := input) hlP (by omega)
      (by rw [hParAddr, hd7, hd6']; exact hwPar)
    have hParVal : (reg s8 reg11).val = B.F.parentOf u := by rw [h11_8, hwParV]
    have hPres8 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s8 r = reg st r := fun r hr11 hr12 => by
      rw [ho8 r hr11, ho7 r hr11, hPres6 r hr11 hr12]
    have h0_8 : (reg s8 reg0).val = 0 := by
      rw [hPres8 reg0 (by intro h; cases h) (by intro h; cases h), h0]
    have hbr : code[s8.pc]? = some (.branchLt reg0 reg11 40 56) := by
      rw [show s8.pc = 39 by omega]; exact hPlBody 2 _ rfl
    obtain ⟨s9, hs9, hpc9, hr9, hd9⟩ := step_branchLt_at (input := input) hbr (by split <;> omega)
    have hr9F := reg_of_regs_eq hr9
    have hd9' : s9.data = st.data := by rw [hd9, hd8, hd7, hd6']
    have hPres9 : ∀ r : Fin 15, r ≠ reg11 → r ≠ reg12 → reg s9 r = reg st r :=
      fun r hr11 hr12 => by rw [hr9F, hPres8 r hr11 hr12]
    by_cases hParPos : 0 < B.F.parentOf u
    · rw [ite_eq_left (by rw [h0_8, hParVal]; exact hParPos)] at hpc9
      have huPos : 0 < u := by
        apply Nat.pos_of_ne_zero
        intro hu0
        subst hu0
        have hz := validJumpForest_parentOf_zero B.G.layout.valid
        omega
      have huB : ∃ P : CutPair H, r.out.tables.back[u]? = some (some P) := by
        have hFSize : B.F.size = N := B.G.size_eq
        let uF : Fin B.F.size := ⟨u, hFSize ▸ huLt⟩
        cases hK : (buildProperLossForest H rank).nodeKey? (B.E.image uF) with
        | some P => exact ⟨P, (B.E.back_eq uF).trans (congrArg some hK)⟩
        | none =>
          exfalso
          have h0Pos : 0 < B.F.size := hFSize ▸ Nat.lt_of_le_of_lt (Nat.zero_le _) huLt
          have hEq := buildProperLossForest_nodeKey?_inj H rank
            (hK.trans (buildProperLossForest_nodeKey?_root H rank).symm)
          rw [← B.E.root_eq h0Pos] at hEq
          have hu0 := congrArg Fin.val (B.E.injective hEq)
          dsimp only [uF] at hu0
          omega
      obtain ⟨P, hPBack⟩ := huB
      let tr := max (rankKahn P.fst) (rankKahn P.snd)
      have hTrLt : tr < n := Nat.max_lt.mpr ⟨hRkLt P.fst, hRkLt P.snd⟩
      obtain ⟨oldHd, hOldHd, hOldLk⟩ := hLinked tr hTrLt
      obtain ⟨kMax, s27, wNew, wOld, hkMax, hStepsBody, hpc27, hwNew, hwOld, hS27At, hPres27, h10_27⟩ :=
        buildTriggerLoop2_push_step hIn hWork hWorkFit rankKahn hRkLt hPlBody hSz hNLe hInSBound
          u huLt P hPBack oldHd st s9 hpc9 hd9' hPres9 h1 h4 h5 h7 h8 h9 h10 hTR hOldHd
      have hHeadLt : trigHeadArrBase n N + tr < trigNextArrBase n N := by rw [← hB1]; omega
      have hNextLe : trigNextArrBase n N ≤ trigNextArrBase n N + u := Nat.le_add_right _ _
      have hNextLt : trigNextArrBase n N + u < inStartArrBase n N := by rw [← hB2]; omega
      have hHeadBeforeNext : ∀ j, trigNextArrBase n N ≤ j → j ≠ trigHeadArrBase n N + tr :=
        fun j hj => Nat.ne_of_gt (Nat.lt_of_lt_of_le hHeadLt hj)
      change ∀ a, s27.data[a]? =
        if a = trigHeadArrBase n N + tr then some wNew
        else if a = trigNextArrBase n N + u then some wOld
        else st.data[a]? at hS27At
      have hPre9 : Steps code input 9 st s9 :=
        Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
          (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (steps_1_of_step hs9))))))))
      have hStepPush : Steps code input (19 + kMax + 7) st s27 := by
        have hS := hPre9.append hStepsBody
        rwa [show 9 + (10 + kMax + 7) = 19 + kMax + 7 by omega] at hS
      let buckets' : Nat → List Nat := fun x => if x = tr then u :: buckets tr else buckets x
      have hBInv' : ∀ tr' < n, (buckets' tr').Nodup ∧ ∀ w ∈ buckets' tr',
          w < u + 1 ∧ 0 < B.F.parentOf w ∧ ∃ P' : CutPair H,
            r.out.tables.back[w]? = some (some P') ∧ max (rankKahn P'.fst) (rankKahn P'.snd) = tr' := by
        intro tr' htr'
        by_cases hEq : tr' = tr
        · subst tr'; dsimp only [buckets']; rw [ite_eq_left rfl]
          have huNotIn : u ∉ buckets tr := fun hm =>
            Nat.lt_irrefl u ((hBInv tr hTrLt).2 u hm).1
          refine ⟨List.nodup_cons.mpr ⟨huNotIn, (hBInv tr hTrLt).1⟩, fun w hw => ?_⟩
          rcases List.mem_cons.mp hw with rfl | hwTail
          · exact ⟨Nat.lt_succ_self _, hParPos, P, hPBack, rfl⟩
          · obtain ⟨hwu, hRest⟩ := (hBInv tr hTrLt).2 w hwTail
            exact ⟨Nat.lt_succ_of_lt hwu, hRest⟩
        · dsimp only [buckets']; rw [ite_eq_right hEq]
          refine ⟨(hBInv tr' htr').1, fun w hw => ?_⟩
          obtain ⟨hwu, hRest⟩ := (hBInv tr' htr').2 w hw
          exact ⟨Nat.lt_succ_of_lt hwu, hRest⟩
      have hCov' : ∀ w < u + 1, 0 < B.F.parentOf w →
          ∃ P' : CutPair H, r.out.tables.back[w]? = some (some P') ∧
            w ∈ buckets' (max (rankKahn P'.fst) (rankKahn P'.snd)) := by
        intro w hw hwPar
        by_cases hwu : w = u
        · subst hwu; refine ⟨P, hPBack, ?_⟩
          dsimp only [buckets']; rw [ite_eq_left rfl]; exact List.mem_cons_self
        · obtain ⟨P', hP'Back, hP'Mem⟩ := hCov w (by omega) hwPar
          refine ⟨P', hP'Back, ?_⟩
          dsimp only [buckets']
          by_cases hEqP : max (rankKahn P'.fst) (rankKahn P'.snd) = tr
          · rw [ite_eq_left hEqP]
            exact List.mem_cons_of_mem _ (hEqP ▸ hP'Mem)
          · rw [ite_eq_right hEqP]
            exact hP'Mem
      have hLinked' : ∀ tr' < n, ∃ hd : Nat,
          (s27.data[trigHeadArrBase n N + tr']?).map Fin.val = some hd ∧
          ListLinked s27.data (trigNextArrBase n N) N hd (buckets' tr') := by
        intro tr' htr'
        by_cases hEq : tr' = tr
        · subst tr'; dsimp only [buckets']; rw [ite_eq_left rfl]
          refine ⟨u, ?_, rfl, huLt, oldHd, ?_, ?_⟩
          · rw [hS27At (trigHeadArrBase n N + tr), ite_eq_left rfl, Option.map_some, hwNew]
          · rw [hS27At (trigNextArrBase n N + u), ite_eq_right (hHeadBeforeNext _ hNextLe), ite_eq_left rfl,
              Option.map_some, hwOld]
          · apply ListLinked.frame _ hOldLk
            intro w hw
            have hwu : w < u := ((hBInv tr hTrLt).2 w hw).1
            rw [hS27At (trigNextArrBase n N + w), ite_eq_right (hHeadBeforeNext _ (Nat.le_add_right _ _)),
              ite_eq_right (by omega)]
        · dsimp only [buckets']; rw [ite_eq_right hEq]
          obtain ⟨hd', hHd', hLk'⟩ := hLinked tr' htr'
          refine ⟨hd', ?_, ?_⟩
          · have hBefore : trigHeadArrBase n N + tr' < trigNextArrBase n N := by rw [← hB1]; omega
            rw [hS27At (trigHeadArrBase n N + tr'), ite_eq_right (by omega), ite_eq_right (by omega)]
            exact hHd'
          · apply ListLinked.frame _ hLk'
            intro w hw
            have hwu : w < u := ((hBInv tr' htr').2 w hw).1
            rw [hS27At (trigNextArrBase n N + w), ite_eq_right (hHeadBeforeNext _ (Nat.le_add_right _ _)),
              ite_eq_right (by omega)]
      obtain ⟨kRest, buckets1, t, hkRest, hStepsRest, hpct, ht0, ht1, htM, htB, htCov, htLk, htFr⟩ :=
        ih (u + 1) buckets' s27 (by omega) hpc27
          (by rw [hPres27 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
          (by rw [hPres27 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
          (by rw [hPres27 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2])
          (by rw [hPres27 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3])
          (by rw [hPres27 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4])
          (by rw [hPres27 reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h5])
          (by rw [hPres27 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6])
          (by rw [hPres27 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7])
          (by rw [hPres27 reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h8])
          (by rw [hPres27 reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h9])
          h10_27
          (fun w => by
            have hLt := hStoredLt w
            rw [hS27At (storedBase N + 18 * w.val), ite_eq_right (by omega), ite_eq_right (by omega)]
            exact hPar w)
          (fun v => by
            have hLt := hTRLt v
            rw [hS27At (topoRankArrBase n N + v.val), ite_eq_right (by omega), ite_eq_right (by omega)]
            exact hTR v)
          hBInv' hCov' hLinked'
      refine ⟨(19 + kMax + 7) + kRest, buckets1, t, by omega, hStepPush.append hStepsRest, hpct,
        ht0, ht1, htM.trans (hPres27 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)),
        htB, htCov, htLk, fun j hj => ?_⟩
      rw [htFr j hj, hS27At j, ite_eq_right (by rcases hj with h | h <;> omega),
        ite_eq_right (by rcases hj with h | h <;> omega)]
    · rw [ite_eq_right (by rw [h0_8, hParVal]; exact hParPos)] at hpc9
      have h10_9 : (reg s9 reg10).val = u := by
        rw [hr9F, hPres8 reg10 (by intro h; cases h) (by intro h; cases h), h10]
      have h1_9 : (reg s9 reg1).val = 1 := by
        rw [hr9F, hPres8 reg1 (by intro h; cases h) (by intro h; cases h), h1]
      have haInc : code[s9.pc]? = some (.add reg10 reg10 reg1) := by rw [hpc9]; exact hPlBody 19 _ rfl
      obtain ⟨s10, hs10, hpc10, h10_10, ho10, hd10⟩ := step_add_at (input := input) haInc (by omega)
      have hg10 : code[s10.pc]? = some (.goto 31) := by rw [hpc10, hpc9]; exact hPlBody 20 _ rfl
      obtain ⟨s11, hs11, hpc11, hr11, hd11⟩ := step_goto_at (input := input) hg10 (by omega)
      have hr11F := reg_of_regs_eq hr11
      have hd11' : s11.data = st.data := by rw [hd11, hd10, hd9']
      have hPres11 : ∀ r : Fin 15, r ≠ reg10 → r ≠ reg11 → r ≠ reg12 → reg s11 r = reg st r :=
        fun r hr10 hr11 hr12 => by rw [hr11F, ho10 r hr10, hr9F, hPres8 r hr11 hr12]
      have hStep11 : Steps code input 11 st s11 :=
        Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
          (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9
            (Steps.cons hs10 (steps_1_of_step hs11))))))))))
      obtain ⟨kRest, buckets1, t, hkRest, hStepsRest, hpct, ht0, ht1, htM, htB, htCov, htLk, htFr⟩ :=
        ih (u + 1) buckets s11 (by omega) hpc11
          (by rw [hPres11 reg0 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h0])
          (by rw [hPres11 reg1 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h1])
          (by rw [hPres11 reg2 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h2])
          (by rw [hPres11 reg3 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h3])
          (by rw [hPres11 reg4 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h4])
          (by rw [hPres11 reg5 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h5])
          (by rw [hPres11 reg6 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h6])
          (by rw [hPres11 reg7 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h7])
          (by rw [hPres11 reg8 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h8])
          (by rw [hPres11 reg9 (by intro h; cases h) (by intro h; cases h) (by intro h; cases h), h9])
          (by rw [hr11F, h10_10, add_no_wrap _ _ (by rw [h10_9, h1_9]; omega), h10_9, h1_9])
          (fun w => by rw [hd11']; exact hPar w)
          (fun v => by rw [hd11']; exact hTR v)
          (fun tr htr => ⟨(hBInv tr htr).1, fun w hw => by
            obtain ⟨hwu, hRest⟩ := (hBInv tr htr).2 w hw
            exact ⟨Nat.lt_succ_of_lt hwu, hRest⟩⟩)
          (fun w hw hParW => by
            have hwu : w < u := by
              by_cases hweq : w = u
              · subst hweq; exfalso; exact hParPos hParW
              · omega
            exact hCov w hwu hParW)
          (fun tr htr => by
            obtain ⟨hd, hHd, hLk⟩ := hLinked tr htr
            exact ⟨hd, by rw [hd11']; exact hHd, ListLinked.frame (fun _ _ => by rw [hd11']) hLk⟩)
      refine ⟨11 + kRest, buckets1, t, by omega, hStep11.append hStepsRest, hpct,
        ht0, ht1, htM.trans (hPres11 rMeta (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)),
        htB, htCov, htLk, fun j hj => by rw [htFr j hj, hd11']⟩

theorem run_buildTrigger {input : Input DomL}
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
    (hWork : exitWorkCap H.vertexCount H.arcCount ≤ workCap) (_hWorkFit : workCap ≤ 2 ^ bits)
    (rankKahn : Vertex H → Nat) (hRkLt : ∀ v : Vertex H, rankKahn v < H.vertexCount)
    (s0 : State DomL)
    (hMeta : MetaReady s0 H.vertexCount H.arcCount r.out.tables.next nGlobal)
    (hPar : ∀ w : Fin r.out.tables.next,
      (s0.data[storedBase r.out.tables.next + 18 * w.val]?).map Fin.val =
        some ((buildActualSweepBundle H flat increasing covers rankArc r).F.parentOf w.val))
    (hTR : ∀ v : Vertex H,
      (s0.data[topoRankArrBase H.vertexCount r.out.tables.next + v.val]?).map Fin.val =
        some (rankKahn v)) :
    let B := buildActualSweepBundle H flat increasing covers rankArc r
    let N := r.out.tables.next
    let n := H.vertexCount
    ∃ k : Nat, ∃ buckets : Nat → List Nat, ∃ t : State DomL,
      k ≤ 5 * n + 27 * N + 30 ∧
      run (buildTriggerPhase (hi := hi) (hw := hw) h100).code input k (Phase.initial s0) = some ⟨t, k⟩ ∧
      MetaReady t n H.arcCount N nGlobal ∧
      (∀ tr < n, (buckets tr).Nodup ∧ ∀ w ∈ buckets tr,
        w < N ∧ 0 < B.F.parentOf w ∧ ∃ P : CutPair H,
          r.out.tables.back[w]? = some (some P) ∧ max (rankKahn P.fst) (rankKahn P.snd) = tr) ∧
      (∀ w < N, 0 < B.F.parentOf w →
        ∃ P : CutPair H, r.out.tables.back[w]? = some (some P) ∧
          w ∈ buckets (max (rankKahn P.fst) (rankKahn P.snd))) ∧
      (∀ tr < n, ∃ hd : Nat,
        (t.data[trigHeadArrBase n N + tr]?).map Fin.val = some hd ∧
        ListLinked t.data (trigNextArrBase n N) N hd (buckets tr)) ∧
      (∀ j, (j < trigHeadArrBase n N ∨ inStartArrBase n N ≤ j) → t.data[j]? = s0.data[j]?) := by
  intro B N n
  have hNLe : N ≤ n + 1 := by
    have hEq := nodeCount_eq_next r.index.ok
    have hLe := nodeCount_le r.index.ok
    omega
  have hTempFit : metaArrBase H.vertexCount H.arcCount r.out.tables.next + 48 ≤ workCap := by
    have := tempArrBase_stage2_le (n := H.vertexCount) (m := H.arcCount) hNLe
    unfold tempArrBase exitWorkCap at *; rw [metaArrBase_eq] at *; omega
  have hTHCap : trigHeadArrBase H.vertexCount r.out.tables.next + H.vertexCount ≤ workCap := by
    have : metaArrBase H.vertexCount H.arcCount r.out.tables.next =
        20 * r.out.tables.next + 10 * H.vertexCount + H.arcCount + 1 := metaArrBase_eq _ _ _
    unfold metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase at this
    unfold exitWorkCap at hWork; omega
  let ph := buildTriggerPhase (hi := hi) (hw := hw) h100
  have hCodeLen : (buildTriggerInstrs (bits := bits) h100).length = 58 := by
    unfold buildTriggerInstrs buildTriggerSetupInstrs buildTriggerLoop1Instrs
      buildTriggerLoop2Instrs metaLoadInstrs mul18Instrs
    rfl
  have hCodeSize : ph.code.size = 59 := by
    dsimp [ph, buildTriggerPhase]; rw [codeSize_mkHaltPhase, hCodeLen]
  have hPlFull : Placed ph.code 0 (buildTriggerInstrs (bits := bits) h100) := Placed_mkHaltPhase _ _
  have hLml : ∀ d t off hOff, (metaLoadInstrs (bits := bits) d t off hOff).length = 3 := fun _ _ _ _ => rfl
  have hPlSetup := Placed_append_left (by unfold buildTriggerInstrs at hPlFull; exact hPlFull)
  have hPlLoops := Placed_append_right (by unfold buildTriggerInstrs at hPlFull; exact hPlFull)
  rw [show (buildTriggerSetupInstrs (bits := bits) h100).length = 25 by
    simp [buildTriggerSetupInstrs, metaLoadInstrs]] at hPlLoops
  have hPlL1 := Placed_append_left hPlLoops
  have hPlL2 := Placed_append_right hPlLoops
  rw [show (buildTriggerLoop1Instrs (bits := bits)).length = 6 by rfl] at hPlL2
  have hPl2 := Placed_append_left (by unfold buildTriggerSetupInstrs at hPlSetup; exact hPlSetup)
  have hPlS1 := Placed_append_right (by unfold buildTriggerSetupInstrs at hPlSetup; exact hPlSetup); rw [hLml] at hPlS1
  have hPl3 := Placed_append_left hPlS1
  have hPlS2 := Placed_append_right hPlS1; rw [hLml] at hPlS2
  have hPl4 := Placed_append_left hPlS2
  have hPlS3 := Placed_append_right hPlS2; rw [hLml] at hPlS3
  have hPl5 := Placed_append_left hPlS3
  have hPlS4 := Placed_append_right hPlS3; rw [hLml] at hPlS4
  have hPl6 := Placed_append_left hPlS4
  have hPlS5 := Placed_append_right hPlS4; rw [hLml] at hPlS5
  have hPl7 := Placed_append_left hPlS5
  have hPlS6 := Placed_append_right hPlS5; rw [hLml] at hPlS6
  have hPl8 := Placed_append_left hPlS6
  have hPlS7 := Placed_append_right hPlS6; rw [hLml] at hPlS7
  have hPl9 := Placed_append_left hPlS7
  have hPlMov := Placed_append_right hPlS7; rw [hLml] at hPlMov
  obtain ⟨s1, hs1, hpc1, hd1, h2_1, ho1⟩ := run_metaLoad_slice (input := input) (st := Phase.initial s0)
    (by intro h; cases h) (by intro h; cases h) hPl2 (by omega) rfl hMeta.rMeta_eq (by dsimp only [mIdxN]; omega) hMeta.meta_n
  have hM1 : (reg s1 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho1 rMeta (by intro h; cases h) (by intro h; cases h)]; exact hMeta.rMeta_eq
  obtain ⟨s2, hs2, hpc2, hd2, h3_2, ho2⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl3 (by omega) hpc1 hM1 (by dsimp only [mIdxNH]; omega) (by rw [hd1]; exact hMeta.meta_NH)
  have hM2 : (reg s2 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho2 rMeta (by intro h; cases h) (by intro h; cases h), hM1]
  obtain ⟨s3, hs3, hpc3, hd3, h4_3, ho3⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl4 (by omega) hpc2 hM2 (by dsimp only [mIdxTrigHeadBase]; omega) (by rw [hd2, hd1]; exact hMeta.meta_trigHeadBase)
  have hM3 : (reg s3 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho3 rMeta (by intro h; cases h) (by intro h; cases h), hM2]
  obtain ⟨s4, hs4, hpc4, hd4, h5_4, ho4⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl5 (by omega) hpc3 hM3 (by dsimp only [mIdxTrigNextBase]; omega) (by rw [hd3, hd2, hd1]; exact hMeta.meta_trigNextBase)
  have hM4 : (reg s4 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho4 rMeta (by intro h; cases h) (by intro h; cases h), hM3]
  obtain ⟨s5, hs5, hpc5, hd5, h6_5, ho5⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl6 (by omega) hpc4 hM4 (by dsimp only [mIdxStoredBase]; omega) (by rw [hd4, hd3, hd2, hd1]; exact hMeta.meta_storedBase)
  have hM5 : (reg s5 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho5 rMeta (by intro h; cases h) (by intro h; cases h), hM4]
  obtain ⟨s6, hs6, hpc6, hd6, h7_6, ho6⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl7 (by omega) hpc5 hM5 (by dsimp only [mIdxTopoRankBase]; omega) (by rw [hd5, hd4, hd3, hd2, hd1]; exact hMeta.meta_topoRankBase)
  have hM6 : (reg s6 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho6 rMeta (by intro h; cases h) (by intro h; cases h), hM5]
  obtain ⟨s7, hs7, hpc7, hd7, h8_7, ho7⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl8 (by omega) hpc6 hM6 (by dsimp only [mIdxBackFstInBase]; omega) (by rw [hd6, hd5, hd4, hd3, hd2, hd1]; exact hMeta.meta_backFstIn)
  have hM7 : (reg s7 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho7 rMeta (by intro h; cases h) (by intro h; cases h), hM6]
  obtain ⟨s8, hs8, hpc8, hd8, h9_8, ho8⟩ := run_metaLoad_slice (input := input)
    (by intro h; cases h) (by intro h; cases h) hPl9 (by omega) hpc7 hM7 (by dsimp only [mIdxBackSndInBase]; omega) (by rw [hd7, hd6, hd5, hd4, hd3, hd2, hd1]; exact hMeta.meta_backSndIn)
  have h0_8 : (reg s8 reg0).val = 0 := by
    rw [ho8 reg0 (by intro h; cases h) (by intro h; cases h), ho7 reg0 (by intro h; cases h) (by intro h; cases h),
      ho6 reg0 (by intro h; cases h) (by intro h; cases h), ho5 reg0 (by intro h; cases h) (by intro h; cases h),
      ho4 reg0 (by intro h; cases h) (by intro h; cases h), ho3 reg0 (by intro h; cases h) (by intro h; cases h),
      ho2 reg0 (by intro h; cases h) (by intro h; cases h), ho1 reg0 (by intro h; cases h) (by intro h; cases h),
      reg_initial, hMeta.r0_zero]
  have hm1 : ph.code[s8.pc]? = some (.mov reg10 reg0) := by rw [hpc8]; exact hPlMov 0 _ rfl
  obtain ⟨s9, hs9, hpc9, h10_9, ho9, hd9⟩ := step_mov_at (input := input) hm1 (by omega)
  have hd9' : s9.data = s0.data := by rw [hd9, hd8, hd7, hd6, hd5, hd4, hd3, hd2, hd1, data_initial]
  have h0_9 : (reg s9 reg0).val = 0 := by rw [ho9 reg0 (by intro h; cases h), h0_8]
  have h1_9 : (reg s9 reg1).val = 1 := by
    rw [ho9 reg1 (by intro h; cases h), ho8 reg1 (by intro h; cases h) (by intro h; cases h),
      ho7 reg1 (by intro h; cases h) (by intro h; cases h), ho6 reg1 (by intro h; cases h) (by intro h; cases h),
      ho5 reg1 (by intro h; cases h) (by intro h; cases h), ho4 reg1 (by intro h; cases h) (by intro h; cases h),
      ho3 reg1 (by intro h; cases h) (by intro h; cases h), ho2 reg1 (by intro h; cases h) (by intro h; cases h),
      ho1 reg1 (by intro h; cases h) (by intro h; cases h), reg_initial, hMeta.r1_one]
  have hM_9 : (reg s9 rMeta).val = metaArrBase H.vertexCount H.arcCount r.out.tables.next := by
    rw [ho9 rMeta (by intro h; cases h), ho8 rMeta (by intro h; cases h) (by intro h; cases h), hM7]
  have h2_9 : (reg s9 reg2).val = H.vertexCount := by
    rw [ho9 reg2 (by intro h; cases h), ho8 reg2 (by intro h; cases h) (by intro h; cases h),
      ho7 reg2 (by intro h; cases h) (by intro h; cases h), ho6 reg2 (by intro h; cases h) (by intro h; cases h),
      ho5 reg2 (by intro h; cases h) (by intro h; cases h), ho4 reg2 (by intro h; cases h) (by intro h; cases h),
      ho3 reg2 (by intro h; cases h) (by intro h; cases h), ho2 reg2 (by intro h; cases h) (by intro h; cases h), h2_1]
  have h3_9 : (reg s9 reg3).val = r.out.tables.next := by
    rw [ho9 reg3 (by intro h; cases h), ho8 reg3 (by intro h; cases h) (by intro h; cases h),
      ho7 reg3 (by intro h; cases h) (by intro h; cases h), ho6 reg3 (by intro h; cases h) (by intro h; cases h),
      ho5 reg3 (by intro h; cases h) (by intro h; cases h), ho4 reg3 (by intro h; cases h) (by intro h; cases h),
      ho3 reg3 (by intro h; cases h) (by intro h; cases h), h3_2]
  have h4_9 : (reg s9 reg4).val = trigHeadArrBase H.vertexCount r.out.tables.next := by
    rw [ho9 reg4 (by intro h; cases h), ho8 reg4 (by intro h; cases h) (by intro h; cases h),
      ho7 reg4 (by intro h; cases h) (by intro h; cases h), ho6 reg4 (by intro h; cases h) (by intro h; cases h),
      ho5 reg4 (by intro h; cases h) (by intro h; cases h), ho4 reg4 (by intro h; cases h) (by intro h; cases h), h4_3]
  have h5_9 : (reg s9 reg5).val = trigNextArrBase H.vertexCount r.out.tables.next := by
    rw [ho9 reg5 (by intro h; cases h), ho8 reg5 (by intro h; cases h) (by intro h; cases h),
      ho7 reg5 (by intro h; cases h) (by intro h; cases h), ho6 reg5 (by intro h; cases h) (by intro h; cases h),
      ho5 reg5 (by intro h; cases h) (by intro h; cases h), h5_4]
  have h6_9 : (reg s9 reg6).val = storedBase r.out.tables.next := by
    unfold storedBase
    rw [ho9 reg6 (by intro h; cases h), ho8 reg6 (by intro h; cases h) (by intro h; cases h),
      ho7 reg6 (by intro h; cases h) (by intro h; cases h), ho6 reg6 (by intro h; cases h) (by intro h; cases h), h6_5]
  have h7_9 : (reg s9 reg7).val = topoRankArrBase H.vertexCount r.out.tables.next := by
    rw [ho9 reg7 (by intro h; cases h), ho8 reg7 (by intro h; cases h) (by intro h; cases h),
      ho7 reg7 (by intro h; cases h) (by intro h; cases h), h7_6]
  have h8_9 : (reg s9 reg8).val = 4 + H.vertexCount := by
    rw [ho9 reg8 (by intro h; cases h), ho8 reg8 (by intro h; cases h) (by intro h; cases h), h8_7]
  have h9_9 : (reg s9 reg9).val = 4 + H.vertexCount + r.out.tables.next := by rw [ho9 reg9 (by intro h; cases h), h9_8]
  have h10_9' : (reg s9 reg10).val = 0 := by rw [h10_9, ← ho9 reg0 (by intro h; cases h), h0_9]
  obtain ⟨k1, sL1, hk1, hStepsL1, hpcL1, h0L1, h1L1, hML1, h2L1, h3L1, h4L1, h5L1, h6L1, h7L1, h8L1, h9L1,
      h10L1, hHeadZ, hFrL1⟩ :=
    buildTriggerLoop1_spec hTHCap hw hPlL1 (by omega) H.vertexCount 0 s9 (Nat.zero_add _)
      (by omega) h0_9 h1_9 h2_9 h3_9 h4_9 h5_9 h6_9 h7_9 h8_9 h9_9 h10_9'
      (fun _ hi => absurd hi (Nat.not_lt_zero _))
  obtain ⟨k2, buckets, t, hk2, hStepsL2, hpct, ht0, ht1, htM, htB, htCov, htLk, htFr2⟩ :=
    buildTriggerLoop2_spec flat increasing covers rankArc hIn hWork hw rankKahn hRkLt hPlL2 (by omega)
      N 0 (fun _ => []) sL1 (Nat.zero_add _) hpcL1 h0L1 h1L1 h2L1 h3L1 h4L1 h5L1 h6L1 h7L1 h8L1 h9L1 h10L1
      (fun w => by
        have := w.isLt
        rw [hFrL1 _ (Or.inl (by unfold trigHeadArrBase topoRankArrBase orderArrBase storedBase; omega)), hd9']
        exact hPar w)
      (fun v => by
        have := v.isLt
        rw [hFrL1 _ (Or.inl (by unfold trigHeadArrBase topoRankArrBase; omega)), hd9']
        exact hTR v)
      (fun tr _ => ⟨List.nodup_nil, fun _ hx => by cases hx⟩)
      (fun _ hw0 => absurd hw0 (Nat.not_lt_zero _))
      (fun tr htr => ⟨N, hHeadZ tr htr, rfl⟩)
  have hSetupSteps : Steps ph.code input 25 (Phase.initial s0) s9 :=
    hs1.append (hs2.append (hs3.append (hs4.append (hs5.append (hs6.append (hs7.append (hs8.append (steps_1_of_step hs9))))))))
  have hHalt : step ph.code input t = some (.halted t) :=
    haltAt_mkHaltPhase (hi := hi) (hw := hw) (buildTriggerInstrs (bits := bits) h100) _
      (by rw [hpct, hCodeLen]) (input := input)
  refine ⟨25 + k1 + k2 + 1, buckets, t, by omega, ((hSetupSteps.append hStepsL1).append hStepsL2).halts hHalt,
    ?_, htB, htCov, htLk, fun j hj => ?_⟩
  · apply hMeta.preserve (by rw [htM, hML1, hM_9]) ht0 ht1
    intro i hi22
    rw [htFr2 _ (Or.inr (by unfold metaArrBase inArcIdArrBase inStartArrBase; omega)),
      hFrL1 _ (Or.inr (by unfold metaArrBase inArcIdArrBase inStartArrBase trigNextArrBase trigHeadArrBase; omega)), hd9']
  · rw [htFr2 j hj, hFrL1 j (by
      rcases hj with h | h
      · exact Or.inl h
      · exact Or.inr (Nat.le_trans
          (show trigHeadArrBase n N + n ≤ inStartArrBase n N from Nat.le_add_right _ _) h)), hd9']

end BuildTriggerPhase

end Stage3SeedTrigger

end PaperB.RamProgram.ExitSummaryBuild
