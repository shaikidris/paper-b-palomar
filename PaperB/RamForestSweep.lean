module

public import PaperB.RamForestSweepInit
public import PaperB.RamForestSweepDriver
public import PaperB.RamForestSweepStage2c

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

namespace PaperB.RamForestProgram.Sweep

open PaperB
open PaperB.LabelledQuotient
open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.RamForestProgram
open PaperB.RamForestProgram.Finish
open PaperB.RamForestProgram.RawBuild
open PaperB.RamForestProgram.DictSort
open PaperB.ForestHead _root_.EX24 _root_.EX24.PreStep _root_.EX24.PreparedSweep
open PaperB.ForestDictionary (Rows)
open PaperB.EX24.FinalDFS (nodeCount)

/-! ### Full Linked Stage 2 RAM Phase & Top-Level Theorem (`sweepPhase`, `sweepProgram`, `run_sweep`) -/

section TopLevelSweep

private noncomputable def stage2Output_of_regs_data {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {H : LabelledQuotient} [DecidableEq (CutPair H)]
    {dictRows : Rows H} {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {large : 3 ≤ H.vertexCount}
    {r : PaperB.OrderedReaderResult dictRows order size_order rank large}
    {width : 1 + 18 * H.vertexCount < 2 ^ bits}
    {u v : State (layout bits inputCap workCap hi hw)}
    (hRegs : v.regs = u.regs) (hData : v.data = u.data)
    (out : Stage2Output H r width u) :
    Stage2Output H r width v :=
  let hRegEq : ∀ regId : Fin 15, reg v regId = reg u regId := fun regId => by
    cases u; cases v; dsimp at hRegs; subst hRegs; rfl
  { arena := out.arena
    ctrl :=
      { count_eq := (congrArg Fin.val (hRegEq count)).trans out.ctrl.count_eq
        one := (congrArg Fin.val (hRegEq registers.one)).trans out.ctrl.one
        zero := (congrArg Fin.val (hRegEq registers.zero)).trans out.ctrl.zero
        stackBase_eq := (congrArg Fin.val (hRegEq registers.stackBase)).trans out.ctrl.stackBase_eq
        tin_eq := (congrArg Fin.val (hRegEq tinBase)).trans out.ctrl.tin_eq
        tout_eq := (congrArg Fin.val (hRegEq toutBase)).trans out.ctrl.tout_eq
        offset_eq := (congrArg Fin.val (hRegEq offsetBase)).trans out.ctrl.offset_eq
        child_eq := (congrArg Fin.val (hRegEq childrenBase)).trans out.ctrl.child_eq }
    rootVal := (congrArg Fin.val (hRegEq cmd)).trans out.rootVal
    parents := fun a => by rw [hData]; exact out.parents a
    mass := out.mass
    children := out.children
    place := out.place
    src := out.src
    fits := out.fits
    apart := out.apart
    params :=
      { cursor := (congrArg Fin.val (hRegEq registers.ptr)).trans out.params.cursor
        src := (congrArg Fin.val (hRegEq registers.childBase)).trans out.params.src
        unit := (congrArg Fin.val (hRegEq clk)).trans out.params.unit
        count := (congrArg Fin.val (hRegEq registers.remain)).trans out.params.count }
    sourceAt := fun j hj => by rw [hData]; exact out.sourceAt j hj }

def sweepPhase {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Phase (layout bits inputCap workCap hi hw) :=
  (sweepInitPhase hi hw h8).link ((sweepLoopPhase hi hw h8).link (sweepStage2cPhase hi hw h8))

def sweepProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h8 : 8 ≤ 2 ^ bits) :
    Program (layout bits inputCap workCap hi hw) :=
  (sweepPhase hi hw h8).code

theorem run_sweep {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h8 : 8 ≤ 2 ^ bits)
    (H : LabelledQuotient) [DecidableEq (CutPair H)]
    (input : Input (layout bits inputCap workCap hi hw))
    (hRaw : RawQuotientInput input H)
    (hCap : rawWorkCap H.vertexCount H.arcCount ≤ workCap)
    (dictRows : Rows H) (large : 3 ≤ H.vertexCount)
    {order : Array (Vertex H)} {size_order : order.size = H.vertexCount}
    {rank : Vertex H → Nat} {rows : Rows H}
    {s : State (layout bits inputCap workCap hi hw)}
    (dso : DictSortOutput H s order size_order rank rows (Nat.le_trans hCap hw))
    (r : PaperB.OrderedReaderResult dictRows order size_order rank large)
    (width : 1 + 18 * H.vertexCount < 2 ^ bits) :
    ∃ t : State (layout bits inputCap workCap hi hw),
    ∃ states : List (State (layout bits inputCap workCap hi hw)),
    ∃ work : Nat,
      work ≤ 5200 * ((H.vertexCount + H.arcCount + 1) * (OracleContract.L H.vertexCount) ^ 2) ∧
      run (sweepProgram hi hw h8) input work (Phase.initial s) = some ⟨t, work⟩ ∧
      SuccessfulTrace (sweepProgram hi hw h8) input (Phase.initial s) states ⟨t, work⟩ ∧
      tracePeakWords input states = inputCap + workCap + 15 ∧
      Nonempty (Stage2Output H r width t) := by
  let p1 := sweepInitPhase hi hw h8
  let p2 := sweepLoopPhase hi hw h8
  let p3 := sweepStage2cPhase hi hw h8
  obtain ⟨t1, _, c1, hc1, run1, _, _, _, _, _, inv1⟩ :=
    run_sweepInit h8 H input hRaw hCap dictRows large dso
  obtain ⟨F2, t2, _, c2, hc2, run2, _, _, _, inv2⟩ :=
    run_sweepLoop h8 H input hCap dictRows large r inv1
  obtain ⟨t3, _, c3, hc3, run3, _, _, _, ⟨out3⟩⟩ :=
    run_sweepStage2c h8 H input hCap r width inv2
  have hp3Pos : 0 < p3.code.size := by have := p3.haltFits; omega
  obtain ⟨t23, _, rt23, dt23, run23, _, _⟩ :=
    run_linked_pair p2 p3.code hp3Pos run2 run3
  have hp23Pos : 0 < (p2.link p3).code.size := by have := (p2.link p3).haltFits; omega
  obtain ⟨t, states, rt, dt, runAll, chkAll, peakAll⟩ :=
    run_linked_pair p1 (p2.link p3).code hp23Pos run1 run23
  have hLPos : 1 ≤ OracleContract.L H.vertexCount := by
    unfold OracleContract.L; omega
  have hL1Sq : (OracleContract.L H.vertexCount + 1) ^ 2 ≤ 4 * (OracleContract.L H.vertexCount) ^ 2 := by
    have hLe : OracleContract.L H.vertexCount + 1 ≤ 2 * OracleContract.L H.vertexCount := by omega
    calc (OracleContract.L H.vertexCount + 1) ^ 2
        = (OracleContract.L H.vertexCount + 1) * (OracleContract.L H.vertexCount + 1) := by rw [Nat.pow_two]
      _ ≤ (2 * OracleContract.L H.vertexCount) * (2 * OracleContract.L H.vertexCount) :=
        Nat.mul_le_mul hLe hLe
      _ = 4 * (OracleContract.L H.vertexCount) ^ 2 := by
        rw [Nat.pow_two, Nat.mul_assoc 2 _ _, Nat.mul_left_comm (OracleContract.L H.vertexCount) 2 _,
          ← Nat.mul_assoc 2 2 _]
  have hWorkLe : c1 + (c2 + c3) ≤
      5200 * ((H.vertexCount + H.arcCount + 1) * (OracleContract.L H.vertexCount) ^ 2) := by
    let n := H.vertexCount
    let m := H.arcCount
    let LSq := (OracleContract.L n) ^ 2
    have hLSqPos : 1 ≤ LSq := Nat.pow_pos hLPos
    have hA : c1 + c3 ≤ 240 * (n + 1) := by omega
    have hB : 240 * (n + 1) ≤ 240 * ((n + m + 1) * LSq) := by
      have h1 : n + 1 ≤ (n + m + 1) * LSq :=
        Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ hLSqPos)
      exact Nat.mul_le_mul_left _ h1
    have hC : 36 ≤ 36 * ((n + m + 1) * LSq) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos (by omega) hLSqPos)
    have hD : 1200 * (n + m) * (OracleContract.L n + 1) ^ 2 ≤ 4800 * ((n + m + 1) * LSq) := by
      calc 1200 * (n + m) * (OracleContract.L n + 1) ^ 2
          ≤ 1200 * (n + m + 1) * (4 * LSq) := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hL1Sq
        _ = 4800 * ((n + m + 1) * LSq) := by
          rw [← Nat.mul_assoc (1200 * (n + m + 1)) 4 LSq, Nat.mul_right_comm 1200 (n + m + 1) 4,
            Nat.mul_assoc (1200 * 4) (n + m + 1) LSq]
    dsimp only [n, m, LSq] at hA hB hC hD
    have hSum : c1 + (c2 + c3) ≤ 5076 * ((H.vertexCount + H.arcCount + 1) * (OracleContract.L H.vertexCount) ^ 2) := by
      omega
    have h52 : 5076 * ((H.vertexCount + H.arcCount + 1) * (OracleContract.L H.vertexCount) ^ 2) ≤
        5200 * ((H.vertexCount + H.arcCount + 1) * (OracleContract.L H.vertexCount) ^ 2) :=
      Nat.mul_le_mul_right _ (by decide)
    exact Nat.le_trans hSum h52
  exact ⟨t, states, c1 + (c2 + c3), hWorkLe, runAll, chkAll, peakAll,
    ⟨stage2Output_of_regs_data (rt.trans rt23) (dt.trans dt23) out3⟩⟩

end TopLevelSweep

end PaperB.RamForestProgram.Sweep
