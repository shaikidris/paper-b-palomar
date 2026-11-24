module

public import PaperB.SealedBuild
public import PaperB.OracleContract
public import PaperB.OracleSealedIndexLayout
public import PaperB.RamDagReachSetup
public import PaperB.RamPrefixAndForestLoop
public import PaperB.RamExitFamilyInduction
public import PaperB.RamSealedPacker
public import PaperB.RamOracleQuery

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option linter.unusedVariables false
set_option relaxedAutoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

/-!
Word-RAM composition of the sealed oracle builder.

Combines the three 16-register Word-RAM programs in sequence via `RamAppendLink.join`:
1. `prefixAndForestLoopProgram` (`RamPrefixAndForestLoop`)
2. `exitFamilyLoopProgram` (`RamExitFamilyLoopRun`)
3. `sealedPackAndShiftProgram` (`RamSealedPacker`)

into a single deterministic `sealedOracleBuildProgram` under `oracleWordSlack = 10`
and `masterWorkCap n m := 800 * (n + m + 1)`, proving `SealedBuild.build` resource
bounds given the composed exit-family execution proof.
-/

namespace PaperB.RamSealedOracleAssembly

open PaperB
open PaperB.Machine (Word)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.OracleContract
open PaperB.OracleSealedIndexLayout
open PaperB.ExitMap.Retention (TagsFit)
open PaperB.RamDagReach
open PaperB.RamBuildPrefix
open PaperB.RamPrefixAndForestLoop
open PaperB.RamFamilyForestLoop
open PaperB.RamExitFamilyLoop
open PaperB.RamQuotientEmitter
open PaperB.RamStaticReaderBridge (MatchesPackedLayout)
open PaperB.RamSealedPacker
open PaperB.RamOracleQuery

section MasterCapacityAndJoin

private theorem phase_initial_eq {bits : Nat} {L : Layout bits} {a b : State L}
    (hr : a.regs = b.regs) (hd : a.data = b.data) :
    Phase.initial a = Phase.initial b := by
  cases a; cases b
  dsimp [Phase.initial] at hr hd ⊢
  subst hr hd
  rfl

private theorem step_next_ne_halt {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s u : State L}
    (hs : step code input s = some (.next u))
    {haltIdx : Nat} (hAt : code[haltIdx]? = some .halt) :
    s.pc ≠ haltIdx := by
  intro hEq
  unfold step at hs
  rw [hEq, hAt] at hs
  cases hs

private theorem step_next_of_fetch_size_le {bits : Nat} {L : Layout bits}
    {p q : Program L} {input : Input L} {s a : State L}
    (hSz : p.size ≤ q.size)
    (hf : q[s.pc]? = p[s.pc]?)
    (h : step p input s = some (.next a)) :
    step q input s = some (.next a) := by
  unfold step at h ⊢
  rw [hf]
  cases hp : p[s.pc]? with
  | none => rw [hp] at h; cases h
  | some op =>
    rw [hp] at h
    have advMono : ∀ {s' : State L} {pc : Nat},
        (if pc < p.size then some (Transition.next { s' with pc := pc }) else none) =
          some (.next a) →
        (if pc < q.size then some (Transition.next { s' with pc := pc }) else none) =
          some (.next a) := by
      intro s' pc hAdv
      by_cases hlt : pc < p.size
      · rw [ite_eq_left hlt] at hAdv
        rw [ite_eq_left (Nat.lt_of_lt_of_le hlt hSz)]
        exact hAdv
      · rw [ite_eq_right hlt] at hAdv
        cases hAdv
    cases op with
    | halt => simp [Option.bind_eq_bind, Option.bind] at h
    | imm _ _ => exact advMono h
    | mov _ _ => exact advMono h
    | add _ _ _ => exact advMono h
    | sub _ _ _ => exact advMono h
    | band _ _ _ => exact advMono h
    | branchLt _ _ _ _ => exact advMono h
    | goto _ => exact advMono h
    | shr1 _ _ => exact advMono h
    | loadInput _ addr =>
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases hmem : input.words[(reg s addr).val]? with
      | none => rw [hmem] at h; cases h
      | some w =>
        rw [hmem] at h
        exact advMono h
    | loadData _ addr =>
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases hmem : s.data[(reg s addr).val]? with
      | none => rw [hmem] at h; cases h
      | some w =>
        rw [hmem] at h
        exact advMono h
    | storeData addr _ =>
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      by_cases hmem : (reg s addr).val < s.data.size
      · rw [dite_eq_left hmem] at h ⊢
        exact advMono h
      · rw [dite_eq_right hmem] at h
        cases h

private theorem steps_join_left {bits : Nat} {L : Layout bits}
    (left right : Program L) {haltIdx : Nat} (hHalt : haltIdx < left.size)
    (hAt : left[haltIdx]? = some .halt)
    {input : Input L} {k : Nat} {s t : State L}
    (hSteps : Steps left input k s t) :
    Steps (join left right haltIdx hHalt) input k s t := by
  have hSzLe : left.size ≤ (join left right haltIdx hHalt).size := by
    unfold join
    rw [Array.size_append, Array.size_set, Array.size_map]
    omega
  induction hSteps with
  | zero s => exact Steps.zero s
  | @cons n s a t head tail ih =>
    have hNe : s.pc ≠ haltIdx := step_next_ne_halt head hAt
    have hHead : step (join left right haltIdx hHalt) input s = some (.next a) := by
      cases hFetch : left[s.pc]? with
      | none =>
        unfold step at head
        rw [hFetch] at head
        cases head
      | some op =>
        have hJ := fetch_left left right hHalt hNe hFetch
        exact step_next_of_fetch_size_le hSzLe (hJ.trans hFetch.symm) head
    exact Steps.cons hHead ih

theorem join_size {bits : Nat} {L : Layout bits}
    (left right : Program L) {haltIdx : Nat} (hHalt : haltIdx < left.size) :
    (join left right haltIdx hHalt).size = left.size + right.size := by
  unfold join
  rw [Array.size_append, Array.size_set, Array.size_map]

theorem join_pos {bits : Nat} {L : Layout bits}
    (left right : Program L) {haltIdx : Nat} (hHalt : haltIdx < left.size)
    (hPosR : 0 < right.size) :
    0 < (join left right haltIdx hHalt).size := by
  rw [join_size]
  omega

theorem join_last_halt {bits : Nat} {L : Layout bits}
    (left right : Program L) {haltIdx : Nat} (hHalt : haltIdx < left.size)
    (hPosR : 0 < right.size)
    (hRightHalt : right[right.size - 1]? = some .halt) :
    (join left right haltIdx hHalt)[(join left right haltIdx hHalt).size - 1]? = some .halt := by
  have hEqIdx : (join left right haltIdx hHalt).size - 1 = left.size + (right.size - 1) := by
    rw [join_size]; omega
  rw [hEqIdx]
  exact relocated_right left right hHalt (right.size - 1) .halt hRightHalt

theorem run_join_at_halt {bits : Nat} {L : Layout bits}
    (left right : Program L) {haltIdx : Nat} (hHalt : haltIdx < left.size)
    (hAt : left[haltIdx]? = some .halt) (hPosR : 0 < right.size)
    {input : Input L} {start t1 t2 : State L} {k1 k2 : Nat}
    (hLeft : run left input k1 (Phase.initial start) = some ⟨t1, k1⟩)
    (hPc1 : t1.pc = haltIdx)
    (hRight : run right input k2 (Phase.initial t1) = some ⟨t2, k2⟩) :
    let code := join left right haltIdx hHalt
    ∃ t states,
      t.regs = t2.regs ∧
      t.data = t2.data ∧
      t.pc = left.size + t2.pc ∧
      run code input (k1 + k2) (Phase.initial start) = some ⟨t, k1 + k2⟩ ∧
      SuccessfulTrace code input (Phase.initial start) states ⟨t, k1 + k2⟩ ∧
      tracePeakWords input states = footprint L := by
  intro code
  obtain ⟨m1, last1, route1, halt1, cost1⟩ := run_has_steps_then_halt hLeft
  obtain ⟨atHalt1, same1⟩ := halted_fetch_and_state halt1
  have hLastPc : last1.pc = haltIdx := by
    change t1 = last1 at same1
    rw [← same1]
    exact hPc1
  have hPre : Steps code input m1 (Phase.initial start) last1 :=
    steps_join_left left right hHalt hAt route1
  have hGotoFetch : code[last1.pc]? = some (.goto left.size) := by
    rw [hLastPc]
    exact (fetch_halt left right hHalt).1
  have hLeftLt : left.size < code.size := (fetch_halt left right hHalt).2 hPosR
  have hJumpStep : step code input last1 = some (.next { last1 with pc := left.size }) :=
    step_goto_at hGotoFetch hLeftLt
  have hJmp : Steps code input (m1 + 1) (Phase.initial start) { last1 with pc := left.size } :=
    hPre.append (Steps.cons hJumpStep (Steps.zero _))
  obtain ⟨m2, last2, route2, halt2, cost2⟩ := run_has_steps_then_halt hRight
  obtain ⟨atHalt2, same2⟩ := halted_fetch_and_state halt2
  have placed : RelocatedSlice right code left.size := relocated_right left right hHalt
  have after := route2.relocate placed
  have sameEntry : relocateStatePC left.size (Phase.initial t1) = { last1 with pc := left.size } := by
    change t1 = last1 at same1
    rw [same1]
    simp only [relocateStatePC, Phase.initial, Nat.add_zero]
  rw [sameEntry] at after
  have terminal : step code input (relocateStatePC left.size last2) =
      some (.halted (relocateStatePC left.size t2)) := by
    change t2 = last2 at same2
    rw [same2]
    exact step_halt_at (s := relocateStatePC left.size last2) (placed last2.pc .halt atHalt2)
  have execution := (hJmp.append after).halts terminal
  have hTot : (m1 + 1) + m2 + 1 = k1 + k2 := by
    change k1 = m1 + 1 at cost1
    change k2 = m2 + 1 at cost2
    omega
  rw [hTot] at execution
  obtain ⟨states, checked⟩ := run_has_successfulTrace execution
  exact ⟨relocateStatePC left.size t2, states, rfl, rfl, rfl, execution, checked, checked.peak_eq⟩

end MasterCapacityAndJoin

section UnifiedBuildProgram

def stage12Program {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  join (prefixAndForestLoopProgram hi hw h32) (exitFamilyLoopProgram hi hw h100)
    ((prefixAndForestLoopProgram hi hw h32).size - 1)
    (Nat.sub_lt (prefixAndForestLoopProgram_pos hi hw h32) (by decide))

theorem stage12Program_pos {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    0 < (stage12Program hi hw h32 h100).size :=
  join_pos _ _ _ (exitFamilyLoopProgram_pos hi hw h100)

theorem stage12Program_last_halt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    (stage12Program hi hw h32 h100)[(stage12Program hi hw h32 h100).size - 1]? = some .halt :=
  join_last_halt _ _ _ (exitFamilyLoopProgram_pos hi hw h100)
    (exitFamilyLoopProgram_last_halt hi hw h100)

/-- Complete EX5.1 + EX5.2 deterministic 16-register Word-RAM builder program:
prefix + emitter + family forest loop -> exit-summary family loop -> sealed packer + shift. -/
def sealedOracleBuildProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  join (stage12Program hi hw h32 h100) (sealedPackAndShiftProgram (hi := hi) (hw := hw) h32)
    ((stage12Program hi hw h32 h100).size - 1)
    (Nat.sub_lt (stage12Program_pos hi hw h32 h100) (by decide))

theorem sealedOracleBuildProgram_pos {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits) (h100 : 100 ≤ 2 ^ bits) :
    0 < (sealedOracleBuildProgram hi hw h32 h100).size :=
  join_pos _ _ _ (Nat.zero_lt_of_lt (sealedPackAndShiftPhase (hi := hi) (hw := hw) h32).haltFits)

private theorem copyPrefix_of_data_eq {bits : Nat} {L : Layout bits}
    (cfg : SealedBuild.SealLayout L) {a b : State L} (hd : a.data = b.data) :
    SealedBuild.copyPrefix cfg a = SealedBuild.copyPrefix cfg b := by
  apply Array.ext
  · rw [SealedBuild.copyPrefix_size, SealedBuild.copyPrefix_size]
  · intro i hi1 hi2
    have hiK : i < cfg.k := by rw [SealedBuild.copyPrefix_size] at hi1; exact hi1
    rw [SealedBuild.copyPrefix_getElem cfg a ⟨i, hiK⟩,
      SealedBuild.copyPrefix_getElem cfg b ⟨i, hiK⟩]
    cases a; cases b
    dsimp at hd ⊢
    subst hd
    rfl

variable (run_exit_family_loop : ∀ {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}

    (h100 : 100 ≤ 2 ^ bits) (input : Input (layout16 bits inputCap workCap hi hw))
    {s₀ : State (layout16 bits inputCap workCap hi hw)}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice s₀.data (prefixTreeBase workCap) g r dense)
    {n m Q forestUsed : Nat}
    (hn : n = g.vertexCount) (hm : m = g.arcCount) (hQ : Q = dense.length)
    (hFlat : ∀ d : Fin dense.length, (S.ramQuotient d).IsFlat)
    (hCap : 800 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits)
    (hSz : s₀.data.size = workCap)
    (hRegs : LoopIterRegs n m r.val Q (prefixTreeBase workCap) (emitBaseOf workCap)
      (loopBaseOf workCap) Q forestUsed s₀)
    (hForestLe : forestUsed ≤ 38 * n)
    (hQStarts : ∀ j ≤ Q, (s₀.data[emitBaseOf workCap + 2 * n + j]?).map Fin.val = some (qStartFn S j))
    (hArcs : ∀ (d : Fin dense.length) (p : Nat) (hp : p < (S.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds d hx).2.1)).symm)
      (s₀.data[emitBaseOf workCap + 3 * n + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (s₀.data[emitBaseOf workCap + 3 * n + m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (s₀.data[emitBaseOf workCap + 3 * n + 2 * m + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry)
    (hRecs : ∀ d : Fin dense.length,
      OwnerForestPackedRecordAt S d (loopBaseOf workCap) n m forestUsed s₀.data),
    let code := exitFamilyLoopProgram hi hw h100
    ∃ (t : State (layout16 bits inputCap workCap hi hw)) (states : List (State (layout16 bits inputCap workCap hi hw))) (steps exitUsed : Nat),
      steps ≤ 30000 * ((n + m + 1) * OracleContract.L n) ∧
      steps ≤ 30000 * ((n + m + 1) * OracleContract.L n ^ 2) ∧
      Steps code input (steps - 1) (Phase.initial s₀) t ∧
      run code input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (Phase.initial s₀) states ⟨t, steps⟩ ∧
      tracePeakWords input states = inputCap + workCap + 16 ∧
      t.pc = code.size - 1 ∧
      exitUsed ≤ 48 * n ∧
      t.data.size = workCap ∧
      SealedPackEntryRegs n m r.val Q (prefixTreeBase workCap)
        (ownerForestPtrsBase (loopBaseOf workCap) n m)
        (exitPtrsBase (loopBaseOf workCap) n m) (5 * n) t ∧
      SealedDisjointLayout n Q (prefixTreeBase workCap)
        (ownerForestPtrsBase (loopBaseOf workCap) n m)
        (forestArenaBase (loopBaseOf workCap) n m) forestUsed
        (exitPtrsBase (loopBaseOf workCap) n m)
        (exitArenaBase (loopBaseOf workCap) n m) exitUsed (5 * n) workCap ∧
      (∀ d : Fin dense.length,
        OwnerExitArenaAt S d (ownerForestPtrsBase (loopBaseOf workCap) n m)
          (forestArenaBase (loopBaseOf workCap) n m) forestUsed
          (exitPtrsBase (loopBaseOf workCap) n m)
          (exitArenaBase (loopBaseOf workCap) n m) exitUsed t.data) ∧
      (∀ addr, 3 ≤ addr → addr < exitPtrsBase (loopBaseOf workCap) n m →
        t.data[addr]? = s₀.data[addr]?))

include run_exit_family_loop

/-- End-to-end execution of `sealedOracleBuildProgram` from `SealedBuild.initialState`
on `rawInputOfDigraph g r hi hw` for any acyclic digraph `g`, producing a valid
sealed index `I = SealedBuild.copyPrefix cfg t` in `steps ≤ master_buildFuel n m`
with `totalWords ≤ retainedLinearFactor * n`. -/
theorem run_sealed_oracle_build_of_exit (g : Digraph) (r : Fin g.vertexCount) (acyc : g.IsAcyclic) :
    let n := g.vertexCount
    let m := g.arcCount
    let bits := wordBits oracleWordSlack n m
    let inCap := rawDagInputCap n m
    let workCap := masterWorkCap n m
    let hi := rawDagInputCap_fits n m
    let hw := masterWorkCap_fits n m
    let h32 := master_h32 n m
    let h100 := master_h100 n m
    let L16 := layout16 bits inCap workCap hi hw
    let code := sealedOracleBuildProgram hi hw h32 h100
    let input := rawInputOfDigraph g r hi hw
    ∃ (t : State L16) (states : List (State L16)) (steps totalWords : Nat)
      (cfg : SealedBuild.SealLayout L16),
      cfg.k = totalWords ∧
      totalWords ≤ retainedLinearFactor * n ∧
      steps ≤ master_buildFuel n m ∧
      run code input steps (SealedBuild.initialState L16) = some ⟨t, steps⟩ ∧
      SuccessfulTrace code input (SealedBuild.initialState L16) states ⟨t, steps⟩ ∧
      tracePeakWords input states = footprint L16 ∧
      t.data.size = workCap ∧
      ValidSealedOracleIndex g r (SealedBuild.copyPrefix cfg t) ∧
      (SealedBuild.copyPrefix cfg t).size = totalWords ∧
      ((SealedBuild.copyPrefix cfg t)[hdrTotalWords]?).map Fin.val = some totalWords := by
  intro n m bits inCap workCap hi hw h32 h100 L16 code input
  let s₀ := SealedBuild.initialState L16
  have hRaw := rawInputOfDigraph_valid g r hi hw
  have hBits : workCap < 2 ^ bits := masterWorkCap_lt n m
  have hCap512 : 512 * (n + m + 1) ≤ workCap := masterWorkCap_ge_512 n m
  have hCap800 : 800 * (n + m + 1) ≤ workCap := masterWorkCap_ge_800 n m
  obtain ⟨t1, _, k1, forestUsed, order, hLen, hTopo, S1, hPack1, hk1, hRun1, _, _,
      ht1Pc, hLoopRegs1, hForestLe, ht1Sz, _, _, hD2O1, hO2D1, hZero1, hQStart1, hArcs1,
      hRecs1, hFlatAcyc1⟩ :=
    run_prefix_and_forest_loop_packed input hRaw acyc hCap512 hBits s₀
  have hFlat1 : ∀ d : Fin (denseVertices g r order hTopo).length, (S1.ramQuotient d).IsFlat := fun d =>
    (hFlatAcyc1 d).1
  obtain ⟨t2, _, k2, exitUsed, _, hk2, _, hRun2, _, _, ht2Pc, hExitLe, ht2Sz,
      hSealedRegs2, hDisj2, hArena2, hOuterFr2⟩ :=
    run_exit_family_loop h100 input S1 (n := n) (m := m) rfl rfl rfl hFlat1 hCap800 hBits ht1Sz
      hLoopRegs1 hForestLe hQStart1 hArcs1 hRecs1
  have hTreeFit2 : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤ workCap := by
    have hFit := S1.fit
    rw [ht1Sz] at hFit
    exact hFit
  have hExitPtrsBase : 5 * n ≤ exitPtrsBase (loopBaseOf workCap) n m := by
    unfold exitPtrsBase loopBaseOf prefixQuarter workCap masterWorkCap
    omega
  have hnPos : 1 ≤ n := Fin.pos r
  have hDenseLe : (denseVertices g r order hTopo).length ≤ n := S1.length_le
  have hExitWorkEnd := exitSubWorkEnd_le_workCap hCap800
  have hArenaEnd : exitArenaBase (loopBaseOf workCap) n m + 48 * n ≤ workCap := by
    unfold exitSubWorkBase exitSubInBase exitSubStateBase at hExitWorkEnd
    omega
  have hEPend : exitPtrsBase (loopBaseOf workCap) n m + 3 * n =
      exitArenaBase (loopBaseOf workCap) n m := rfl
  have hFAend : forestArenaBase (loopBaseOf workCap) n m + 38 * n =
      exitPtrsBase (loopBaseOf workCap) n m := by
    exact forestArenaEnd_eq (loopBaseOf workCap) n m
  have hFPend : ownerForestPtrsBase (loopBaseOf workCap) n m + 6 * n =
      forestArenaBase (loopBaseOf workCap) n m := rfl
  have hOrigToDense2 : ∀ v : Fin g.vertexCount,
      (t2.data[3 * n + v.val]?).map Fin.val =
        some (if _ : v ∈ denseVertices g r order hTopo then (denseVertices g r order hTopo).idxOf v + 1 else 0) := by
    intro v
    have hFrV : t2.data[3 * n + v.val]? = t1.data[3 * n + v.val]? :=
      hOuterFr2 (3 * n + v.val) (by omega) (Nat.lt_of_lt_of_le (by have hv : v.val < n := v.isLt; omega) hExitPtrsBase)
    rw [hFrV]
    by_cases hv : v ∈ denseVertices g r order hTopo
    · rw [dite_eq_left hv]
      have hIdxLt := List.idxOf_lt_length_of_mem hv
      have hGet : (denseVertices g r order hTopo)[(denseVertices g r order hTopo).idxOf v]'hIdxLt = v :=
        List.getElem_idxOf hIdxLt
      have hO2D := hO2D1 ((denseVertices g r order hTopo).idxOf v) hIdxLt
      rw [hGet] at hO2D
      simpa only [origToDensePlusOneBase, Nat.zero_mul, Nat.add_zero] using hO2D
    · rw [dite_eq_right hv]
      have hNotReach : ¬ g.InitiallyReachable r v := fun hR => hv (S1.mem_reach v hR)
      have hZ := hZero1 v hNotReach
      simpa only [origToDensePlusOneBase, Nat.zero_mul, Nat.add_zero] using hZ
  have hDenseToOrig2 : ∀ d : Fin (denseVertices g r order hTopo).length,
      (t2.data[4 * n + d.val]?).map Fin.val =
        some ((denseVertices g r order hTopo)[d.val]'d.isLt).val := by
    intro d
    have hD_le : (denseVertices g r order hTopo).length ≤ n := S1.length_le
    have hFrD : t2.data[4 * n + d.val]? = t1.data[4 * n + d.val]? :=
      hOuterFr2 (4 * n + d.val) (by omega) (Nat.lt_of_lt_of_le (by have hLt := Nat.lt_of_lt_of_le d.isLt hDenseLe; omega) hExitPtrsBase)
    rw [hFrD]
    have hD := hD2O1 d.val d.isLt
    simpa only [denseToOrigBase, Nat.zero_mul, Nat.add_zero] using hD
  have hTag : TagsFit bits := oracle_tagsFit n m
  have hQWork : queryWorkCap ≤ 2 ^ bits :=
    Nat.le_trans (by decide : queryWorkCap ≤ 32) (master_h32 n m)
  have hTreeEnd : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤
      exitPtrsBase (loopBaseOf workCap) n m := by
    unfold prefixTreeBase exitPtrsBase loopBaseOf prefixQuarter staticTreeWords loopWorkWords
    omega
  have hStableTree (addr : Nat) (ha1 : prefixTreeBase workCap ≤ addr)
      (ha2 : addr < prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length) :
      t2.data[addr]? = t1.data[addr]? :=
    hOuterFr2 addr
      (by unfold prefixTreeBase prefixQuarter at ha1; omega)
      (Nat.lt_of_lt_of_le ha2 hTreeEnd)
  let S2 : StaticTreeSlice t2.data (prefixTreeBase workCap) g r (denseVertices g r order hTopo) :=
    S1.ofMemEq (ht2Sz.trans ht1Sz.symm) hStableTree
  have hPack2 : MatchesPackedLayout S2 :=
    ⟨hPack1.head_eq, hPack1.heavy_eq, hPack1.entry_eq, hPack1.stop_eq, hPack1.childSlice_eq⟩
  let Q := (denseVertices g r order hTopo).length
  have hFPfit : ownerForestPtrsBase (loopBaseOf workCap) n m + 6 * Q ≤ workCap := by
    change Q ≤ n at hDenseLe
    omega
  have hFAfit : forestArenaBase (loopBaseOf workCap) n m + forestUsed ≤ workCap := by omega
  have hEPfit : exitPtrsBase (loopBaseOf workCap) n m + 3 * Q ≤ workCap := by
    change Q ≤ n at hDenseLe
    omega
  have hEAfit : exitArenaBase (loopBaseOf workCap) n m + exitUsed ≤ workCap := by omega
  obtain ⟨t3, _, k3, totalWords, cfg, hCfgK, hTot128, hk3, hRun3, _, _, ht3Sz, hValid3, hCpSz3, hCpTot3⟩ :=
    run_sealed_pack_and_shift (input := input) h32 hBits hLen hTopo S2 hPack2 rfl rfl rfl rfl
      hSealedRegs2 ht2Sz hDisj2 hTreeFit2
      hFPfit hFAfit hEPfit hEAfit
      hOrigToDense2 hDenseToOrig2 hArena2 hTag hQWork
  obtain ⟨t12, _, ht12Regs, ht12Data, ht12Pc, hRun12, _, _⟩ :=
    run_join_at_halt (prefixAndForestLoopProgram hi hw h32) (exitFamilyLoopProgram hi hw h100)
      (Nat.sub_lt (prefixAndForestLoopProgram_pos hi hw h32) (by decide))
      (prefixAndForestLoopProgram_last_halt hi hw h32)
      (exitFamilyLoopProgram_pos hi hw h100)
      hRun1 ht1Pc hRun2
  have hPc12 : t12.pc = (stage12Program hi hw h32 h100).size - 1 := by
    rw [ht12Pc, stage12Program, join_size, ht2Pc]
    have := exitFamilyLoopProgram_pos hi hw h100
    omega
  have hRun3' : run (sealedPackAndShiftProgram (hi := hi) (hw := hw) h32) input k3 (Phase.initial t12) = some ⟨t3, k3⟩ := by
    rw [phase_initial_eq ht12Regs ht12Data]
    exact hRun3
  obtain ⟨t, states, _, htData, _, hRunTot, hTraceTot, hPeakTot⟩ :=
    run_join_at_halt (stage12Program hi hw h32 h100) (sealedPackAndShiftProgram (hi := hi) (hw := hw) h32)
      (Nat.sub_lt (stage12Program_pos hi hw h32 h100) (by decide))
      (stage12Program_last_halt hi hw h32 h100)
      (Nat.zero_lt_of_lt (sealedPackAndShiftPhase (hi := hi) (hw := hw) h32).haltFits)
      hRun12 hPc12 hRun3'
  have hLPos : 1 ≤ L n := one_le_L n
  have hLSqPos : 1 ≤ L n ^ 2 := by simpa only [Nat.pow_two] using Nat.mul_le_mul hLPos hLPos
  have hk3Sq : k3 ≤ 1700 * ((n + m + 1) * L n ^ 2) := by
    have h1 := Nat.le_mul_of_pos_right k3 hLSqPos
    have h2 := Nat.le_trans h1 (Nat.mul_le_mul_right (L n ^ 2) hk3)
    rw [Nat.mul_assoc] at h2
    exact h2
  have hStepsLe : k1 + k2 + k3 ≤ master_buildFuel n m := by
    change k1 ≤ 100000 * ((n + m + 1) * L n ^ 2) at hk1
    change k2 ≤ 30000 * ((n + m + 1) * L n ^ 2) at hk2
    unfold master_buildFuel
    omega
  have hCpEq : SealedBuild.copyPrefix cfg t = SealedBuild.copyPrefix cfg t3 :=
    copyPrefix_of_data_eq cfg htData
  refine ⟨t, states, k1 + k2 + k3, totalWords, cfg, hCfgK, hTot128, hStepsLe,
    hRunTot, hTraceTot, hPeakTot, by rw [htData]; exact ht3Sz,
    ?_, ?_, ?_⟩
  · rw [hCpEq]; exact hValid3
  · rw [hCpEq]; exact hCpSz3
  · rw [hCpEq]; exact hCpTot3

end UnifiedBuildProgram

end PaperB.RamSealedOracleAssembly
