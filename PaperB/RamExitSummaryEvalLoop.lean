module

public import PaperB.RamExitSummaryEvalHeader
public import PaperB.RamExitSummaryEvalSelect
public import PaperB.RamExitSummaryEvalApply

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

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

/-! Execute the packed jump-map evaluator, counting the initial branch and all hop work. -/

variable {bits inputCap workCap : Nat}
variable {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
local notation "DomL" => layout bits inputCap workCap hi hw

theorem run_eval15 {code : Program DomL} {input : Input DomL}
    (basePc : Nat) (h100 : 100 ≤ 2 ^ bits)
    (hPl : Placed code basePc (eval15Instrs (bits := bits) basePc h100))
    (hSz : basePc + 161 < code.size)
    {F : JumpForest} {ref : Store} {live : Nat → Prop}
    (valid : ValidJumpForest F) (ok : LiveStoreOK F ref live)
    {n m N targetD : Nat} (_hNLe : N ≤ n + 1)
    (hMetaFit : metaArrBase n m N + 48 ≤ workCap) (_hWorkFit : workCap ≤ 2 ^ bits)
    (hFSize : F.size = N) :
    ∀ (rem u : Nat), live u → u < N → ∀ (xs : Values) (st : State DomL),
      F.depthOf u - targetD = rem →
      st.pc = basePc →
      (reg st reg0).val = 0 → (reg st reg1).val = 1 →
      (reg st rMeta).val = metaArrBase n m N →
      (st.data[metaArrBase n m N + mIdxStoredBase]?).map Fin.val = some (storedBase N) →
      (st.data[metaArrBase n m N + mIdxEvalU]?).map Fin.val = some u →
      (st.data[metaArrBase n m N + mIdxEvalD]?).map Fin.val = some targetD →
      ValuesWordsAt st.data (metaArrBase n m N + mIdxEval0) xs →
      (∀ w : Fin N, (st.data[w.val]?).map Fin.val = some (F.depthOf w.val)) →
      (∀ w : Fin N, live w.val →
        (st.data[storedBase N + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
        (st.data[storedBase N + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
        MapWordsAt st.data (storedBase N + 18 * w.val + 2) (ref w.val).parentMap ∧
        MapWordsAt st.data (storedBase N + 18 * w.val + 10) (ref w.val).jumpMap) →
      let res := foldFused F ref u targetD
      ∃ k : Nat, ∃ t : State DomL,
        k ≤ 165 * res.steps + 8 ∧
        Steps code input k st t ∧
        t.pc = basePc + 161 ∧
        (reg t reg0).val = 0 ∧ (reg t reg1).val = 1 ∧ (reg t rMeta).val = metaArrBase n m N ∧
        ValuesWordsAt t.data (metaArrBase n m N + mIdxEval0) (Map.eval res.composed xs) ∧
        (∀ j, (j < metaArrBase n m N + mIdxEvalU ∨
            (metaArrBase n m N + (mIdxEvalU + 1) ≤ j ∧ j < metaArrBase n m N + mIdxEval0) ∨
            metaArrBase n m N + 48 ≤ j) →
          t.data[j]? = st.data[j]?) := by
  have hStBound : storedBase N + 18 * N ≤ metaArrBase n m N := by
    unfold storedBase
    rw [metaArrBase_eq]
    omega
  have hStoreStart : N ≤ storedBase N := Nat.le_refl _
  intro rem
  induction rem using Nat.strongRecOn with
  | _ rem ih =>
    intro u huLive huLt xs st hRem hpc h0 h1 hM hMetaSB hEvalU hEvalD hEvalXs hDepth hStored
    obtain ⟨sHead, hHead, hpcHead, hdHead, hUHead, hDHead, hPresHead⟩ :=
      run_eval15Header (input := input) hPl hSz hpc hM
        (by dsimp only [mIdxEvalD]; omega) hEvalU hEvalD (hDepth ⟨u, huLt⟩)
    have hPres0 : (reg sHead reg0).val = 0 := by
      rw [hPresHead reg0 (by decide) (by decide) (by decide) (by decide), h0]
    have hPres1 : (reg sHead reg1).val = 1 := by
      rw [hPresHead reg1 (by decide) (by decide) (by decide) (by decide), h1]
    have hPresM : (reg sHead rMeta).val = metaArrBase n m N := by
      rw [hPresHead rMeta (by decide) (by decide) (by decide) (by decide), hM]
    by_cases hCmp : targetD < F.depthOf u
    · rw [ite_eq_left hCmp] at hpcHead
      let mv := selectAtDepth F.depthOf targetD (ref u)
      let mapAddr :=
        if targetD ≤ F.depthOf (ref u).jump then storedBase N + 18 * u + 10
        else storedBase N + 18 * u + 2
      have hSlot := hStored ⟨u, huLt⟩ huLive
      have hRecords : (sHead.data[storedBase N + 18 * u]?).map Fin.val = some (ref u).parent ∧
          (sHead.data[storedBase N + 18 * u + 1]?).map Fin.val = some (ref u).jump := by
        rw [hdHead]
        exact ⟨hSlot.1, hSlot.2.1⟩
      obtain ⟨sSel, hSel, hpcSel, h0Sel, h1Sel, hMSel, hMapSel, hUSel, hSelFr⟩ :=
        run_eval15Select (input := input) hPl hSz valid ok huLive huLt hFSize hMetaFit
          hpcHead hPres0 hPres1 hPresM hUHead hDHead (by rw [hdHead]; exact hMetaSB)
          (fun w => by rw [hdHead]; exact hDepth w) hRecords
      change (reg sSel reg2).val = mapAddr at hMapSel
      change (sSel.data[metaArrBase n m N + mIdxEvalU]?).map Fin.val = some mv.dst at hUSel
      have hMapBound : mapAddr + 8 ≤ metaArrBase n m N + mIdxEval0 := by
        dsimp only [mapAddr, mIdxEval0]
        split <;> omega
      have hMap : MapWordsAt st.data mapAddr mv.map := by
        by_cases hJump : targetD ≤ F.depthOf (ref u).jump
        · simpa only [mapAddr, mv, selectAtDepth, ite_eq_left hJump, Stored.select] using hSlot.2.2.2
        · simpa only [mapAddr, mv, selectAtDepth, ite_eq_right hJump, Stored.select] using hSlot.2.2.1
      have hMapSelAt : MapWordsAt sSel.data mapAddr mv.map :=
        mapWordsAt_frame (fun i hi => by
          rw [hSelFr _ (by dsimp only [mapAddr, mIdxEvalU]; split <;> omega), hdHead]) hMap
      have hValsAt : ValuesWordsAt sSel.data (metaArrBase n m N + mIdxEval0) xs :=
        valuesWordsAt_frame (fun i hi => by
          rw [hSelFr _ (by dsimp only [mIdxEval0, mIdxEvalU]; omega), hdHead]) hEvalXs
      obtain ⟨kHop, sEnd, hkHop, hApply, hpcEnd, h0End, h1End, hMEnd, hValsEnd, hApplyFr⟩ :=
        run_eval15Apply (input := input) hPl hSz hMetaFit hMapBound hpcSel
          h0Sel h1Sel hMSel hMapSel hMapSelAt hValsAt
      have hEndFr : ∀ j, (j < metaArrBase n m N + mIdxEvalU ∨
          (metaArrBase n m N + (mIdxEvalU + 1) ≤ j ∧ j < metaArrBase n m N + mIdxEval0) ∨
          metaArrBase n m N + 48 ≤ j) → sEnd.data[j]? = st.data[j]? := by
        intro j hj
        have hAP : j < metaArrBase n m N + mIdxEval0 ∨ metaArrBase n m N + 48 ≤ j := by
          dsimp only [mIdxEvalU, mIdxEval0] at *
          rcases hj with h | ⟨_, h⟩ | h <;> omega
        have hSF : j ≠ metaArrBase n m N + mIdxEvalU := by
          dsimp only [mIdxEvalU] at *
          rcases hj with h | ⟨h, _⟩ | h <;> omega
        rw [hApplyFr _ hAP, hSelFr _ hSF, hdHead]
      have hUStep : (sEnd.data[metaArrBase n m N + mIdxEvalU]?).map Fin.val = some mv.dst := by
        rw [hApplyFr _ (Or.inl (by dsimp only [mIdxEvalU, mIdxEval0]; omega))]
        exact hUSel
      have hDepthEnd : ∀ w : Fin N, (sEnd.data[w.val]?).map Fin.val = some (F.depthOf w.val) := by
        intro w
        rw [hEndFr _ (Or.inl (by have := w.isLt; omega))]
        exact hDepth w
      have hStoredEnd : ∀ w : Fin N, live w.val →
          (sEnd.data[storedBase N + 18 * w.val]?).map Fin.val = some (ref w.val).parent ∧
          (sEnd.data[storedBase N + 18 * w.val + 1]?).map Fin.val = some (ref w.val).jump ∧
          MapWordsAt sEnd.data (storedBase N + 18 * w.val + 2) (ref w.val).parentMap ∧
          MapWordsAt sEnd.data (storedBase N + 18 * w.val + 10) (ref w.val).jumpMap := by
        intro w hwLive
        have hFrame : ∀ i < 18, sEnd.data[storedBase N + 18 * w.val + i]? =
            st.data[storedBase N + 18 * w.val + i]? := by
          intro i hi
          have := w.isLt
          apply hEndFr
          exact Or.inl (by omega)
        obtain ⟨hp, hj, hmP, hmJ⟩ := hStored w hwLive
        exact ⟨by simpa using congrArg (Option.map Fin.val) (hFrame 0 (by decide)) |>.trans hp,
          by rw [hFrame 1 (by decide)]; exact hj,
          mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hFrame (2 + i) (by omega)) hmP,
          mapWordsAt_frame (fun i hi => by rw [Nat.add_assoc]; exact hFrame (10 + i) (by omega)) hmJ⟩
      obtain ⟨hNextLive, hNextDown⟩ := eval_selected_live_down valid ok huLive hCmp
      change live mv.dst at hNextLive
      change F.depthOf mv.dst < F.depthOf u at hNextDown
      have hNextLt : mv.dst < N := hFSize ▸ ok.live_lt _ hNextLive
      obtain ⟨kRest, t, hkRest, hRest, hpcT, h0T, h1T, hMT, hValsT, hFrRest⟩ :=
        ih (F.depthOf mv.dst - targetD) (by omega) mv.dst hNextLive hNextLt (Map.eval mv.map xs)
          sEnd rfl hpcEnd h0End h1End hMEnd
          (by rw [hEndFr _ (Or.inl (by dsimp only [mIdxStoredBase, mIdxEvalU]; omega))]; exact hMetaSB)
          hUStep
          (by rw [hEndFr _ (Or.inr (Or.inl ⟨by dsimp only [mIdxEvalU, mIdxEvalD]; omega,
              by dsimp only [mIdxEvalD, mIdxEval0]; omega⟩))]; exact hEvalD)
          hValsEnd hDepthEnd hStoredEnd
      have hFoldStep := foldFused_step_values valid ok huLive hCmp xs
      change Map.eval (foldFused F ref u targetD).composed xs =
        Map.eval (foldFused F ref mv.dst targetD).composed (Map.eval mv.map xs) ∧
        (foldFused F ref u targetD).steps = 1 + (foldFused F ref mv.dst targetD).steps at hFoldStep
      refine ⟨(8 + 19 + kHop) + kRest, t, ?_, (((hHead.append hSel).append hApply).append hRest),
        hpcT, h0T, h1T, hMT, ?_, fun j hj => (hFrRest j hj).trans (hEndFr j hj)⟩
      · rw [hFoldStep.2]
        omega
      · rw [hFoldStep.1]
        exact hValsT
    · rw [ite_eq_right hCmp] at hpcHead
      obtain ⟨hVal, hCount⟩ := foldFused_stop_values valid ok huLive hCmp xs
      refine ⟨8, sHead, ?_, hHead, hpcHead, hPres0, hPres1, hPresM, ?_, fun j _ => ?_⟩
      · rw [hCount]
        decide
      · rw [hVal, hdHead]
        exact hEvalXs
      · rw [hdHead]

end PaperB.RamProgram.ExitSummaryBuild
