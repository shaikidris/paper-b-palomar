module

public import PaperB.RamBuildPrefix
public import PaperB.RamQuotientEmitter
public import PaperB.RamFamilyForestLoop
public import PaperB.RamStaticReaderBridge

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-!
EX5.1 Unified Prefix + Quotient Emitter + Family Forest Loop Composition
(`prefixAndForestLoopProgram`, `run_prefix_and_forest_loop`):

Composes into ONE fixed 16-register Word-RAM program depending ONLY on
`(bits, inputCap, workCap)`:
1. `buildPrefixProgram`: Kahn DAG reachability + dense incoming CSR copy +
   dominator & static tree construction (`[3*n..5*n)` reachability maps and
   `[treeBase..treeBase + 11*Q)` static tree layout, `treeBase = quarter`),
2. `adapter1Phase`: reloads `ConstRegs n m r.val` from immutable `input[0..2]`
   and sets `r7 := 2 * r6 = emitBase` (`emitBase = 2 * quarter`),
3. `quotientEmitProgram`: emits quotient arcs + `qStartFn` in `[emitBase .. 3 * quarter)`,
4. `adapter2Phase`: sets `r8 := r6 + r7 = loopBase` (`loopBase = 3 * quarter`),
5. `familyForestLoopProgram`: counting-sorts emitted arcs in place inside
   `emitBase` and builds serialized `WordColumns` proper-loss forests (for
   large quotients `3 ≤ n_d`) and zero records (for `n_d < 3`) in
   `[loopBase .. loopBase + loopWorkWords n m)` inside `[3 * quarter .. workCap)`.

Under `512 * (n + m + 1) ≤ workCap < 2 ^ bits`, halts in
`≤ 100000 * ((n + m + 1) * (OracleContract.L n)^2)` operations with peak live
words `inputCap + workCap + 16`.
-/

namespace PaperB.RamPrefixAndForestLoop

open PaperB
open PaperB.Machine (Word)
open PaperB.WordOps (add)
open PaperB.RamProgram
open PaperB.RamProgram.FixedROM
open PaperB.Digraph
open PaperB.LabelledQuotient
open PaperB.ForestHead (Vertex)
open PaperB.RamDagReach
open PaperB.RamBuildPrefix
open PaperB.RamQuotientEmitter
open PaperB.RamFamilyForestLoop
open PaperB.RetainedProperLoss
open PaperB.RamForestProgram.Finish
open PaperB.RamStaticReaderBridge (MatchesPackedLayout)

section FixedProgram

/-- Quarter-slice layout bases for the combined EX5.1 prefix + emitter + loop pipeline. -/
def emitBaseOf (workCap : Nat) : Nat := 2 * prefixQuarter workCap
def loopBaseOf (workCap : Nat) : Nat := 3 * prefixQuarter workCap

theorem hTenOf32 {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : 10 ≤ 2 ^ bits :=
  Nat.le_trans (by decide : 10 ≤ 32) h32

theorem h8Of32' {bits : Nat} (h32 : 32 ≤ 2 ^ bits) : 8 ≤ 2 ^ bits :=
  Nat.le_trans (by decide : 8 ≤ 32) h32

/-- Adapter 1 (`size = 8`): loads `(0, 1, n, m, r)` from `input[0..2]` into `r0..r4`,
preserves `r5 = Q` and `r6 = treeBase = quarter`, and sets `r7 := 2 * r6 = emitBase`. -/
def adapter1Code {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (hTen : 10 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[.imm rZero ⟨0, by omega⟩,
    .imm rOne ⟨1, by omega⟩,
    .loadInput rN rZero,
    .loadInput rM rOne,
    .imm rRoot ⟨2, by omega⟩,
    .loadInput rRoot rRoot,
    .add r7 r6 r6,
    .halt]

def adapter1Phase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (hTen : 10 ≤ 2 ^ bits) :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast (adapter1Code hTen) 7 rfl rfl rfl

/-- Adapter 2 (`size = 2`): sets `r8 := r6 + r7 = loopBase` (`3 * quarter`),
preserving `r0..r7` (`EmitterRegs`). -/
def adapter2Code {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Program (layout16 bits inputCap workCap hi hw) :=
  #[.add r8 r6 r7,
    .halt]

def adapter2Phase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} :
    Phase (layout16 bits inputCap workCap hi hw) :=
  Phase.ofLast adapter2Code 1 rfl rfl rfl

/-- Composite `Phase` linking `adapter1Phase`, `quotientEmitProgram`, and `adapter2Phase`. -/
def midEmitPhase {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} (h32 : 32 ≤ 2 ^ bits) :
    Phase (layout16 bits inputCap workCap hi hw) :=
  (adapter1Phase (hTenOf32 h32)).link
    ((pipelinePhase (quotientEmitPhases (hi := hi) (hw := hw))).link adapter2Phase)

/-- Combined suffix program (`adapter1` -> `quotientEmit` -> `adapter2` -> `familyForestLoop`). -/
def rightAllCode {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  let mid := midEmitPhase (hi := hi) (hw := hw) h32
  join mid.code (familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32)
    mid.haltPC mid.haltFits

theorem rightAllCode_pos {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    0 < (rightAllCode hi hw h32).size := by
  unfold rightAllCode join
  rw [Array.size_append, Array.size_set, Array.size_map]
  have hp := (midEmitPhase (hi := hi) (hw := hw) h32).haltFits
  omega

theorem rightAllCode_last_halt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    (rightAllCode hi hw h32)[(rightAllCode hi hw h32).size - 1]? = some .halt := by
  let mid := midEmitPhase (hi := hi) (hw := hw) h32
  let rCode := familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32
  have hr := familyForestLoopProgram_last_halt (hi := hi) (hw := hw) hw hw h32
  have hrPos : 0 < rCode.size := by
    unfold rCode familyForestLoopProgram
    rw [familyForestLoopCode_size]
    omega
  have hSz : (rightAllCode hi hw h32).size = mid.code.size + rCode.size := by
    unfold rightAllCode join
    rw [Array.size_append, Array.size_set, Array.size_map]
  have hIdx : (rightAllCode hi hw h32).size - 1 = mid.code.size + (rCode.size - 1) := by
    rw [hSz]
    omega
  rw [hIdx]
  exact relocated_right mid.code rCode mid.haltFits (rCode.size - 1) .halt hr

theorem buildPrefixProgram_pos {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    0 < (buildPrefixProgram hi hw hTen).size := by
  unfold buildPrefixProgram join
  rw [Array.size_append, Array.size_set, Array.size_map]
  have hp := prefixRightCode_pos (hi := hi) hw hTen
  omega

theorem buildPrefixProgram_last_lt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (buildPrefixProgram hi hw hTen).size - 1 < (buildPrefixProgram hi hw hTen).size := by
  have hPos := buildPrefixProgram_pos hi hw hTen
  omega

/-- **EX5.1 Unified Prefix + Emitter + Family-Forest Loop ROM**:
Single fixed 16-register Word-RAM program depending ONLY on `(bits, inputCap, workCap)`. -/
def prefixAndForestLoopProgram {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    Program (layout16 bits inputCap workCap hi hw) :=
  let hTen := hTenOf32 h32
  let pref := buildPrefixProgram hi hw hTen
  join pref (rightAllCode hi hw h32) (pref.size - 1) (buildPrefixProgram_last_lt hi hw hTen)

theorem prefixAndForestLoopProgram_pos {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    0 < (prefixAndForestLoopProgram hi hw h32).size := by
  unfold prefixAndForestLoopProgram join
  rw [Array.size_append, Array.size_set, Array.size_map]
  have hp := rightAllCode_pos hi hw h32
  omega

theorem prefixAndForestLoopProgram_last_halt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    (prefixAndForestLoopProgram hi hw h32)[(prefixAndForestLoopProgram hi hw h32).size - 1]? = some .halt := by
  let hTen := hTenOf32 h32
  let pref := buildPrefixProgram hi hw hTen
  let rCode := rightAllCode hi hw h32
  have hrPos : 0 < rCode.size := rightAllCode_pos hi hw h32
  have hr := rightAllCode_last_halt hi hw h32
  have hSz : (prefixAndForestLoopProgram hi hw h32).size = pref.size + rCode.size := by
    unfold prefixAndForestLoopProgram join
    rw [Array.size_append, Array.size_set, Array.size_map]
  have hIdx : (prefixAndForestLoopProgram hi hw h32).size - 1 = pref.size + (rCode.size - 1) := by
    rw [hSz]
    omega
  rw [hIdx]
  exact relocated_right pref rCode (buildPrefixProgram_last_lt hi hw hTen) (rCode.size - 1) .halt hr

end FixedProgram

section LinkingAndAdapters

private theorem nodup_getElem_inj {α : Type} {xs : List α} (hnd : xs.Nodup)
    {i j : Nat} (hi : i < xs.length) (hj : j < xs.length) (heq : xs[i]'hi = xs[j]'hj) :
    i = j := by
  have hpw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
  rcases Nat.lt_trichotomy i j with hlt | rfl | hgt
  · exact False.elim (hpw i j hi hj hlt heq)
  · rfl
  · exact False.elim (hpw j i hj hi hgt heq.symm)

private theorem word_mem_eq_of_map_val {bits : Nat} {a : Array (Word bits)} {j v : Nat}
    (h : (a[j]?).map Fin.val = some v) : ∃ w : Word bits, a[j]? = some w ∧ w.val = v := by
  cases hq : a[j]? with
  | none => simp [hq] at h
  | some w => exact ⟨w, rfl, by simpa [hq] using h⟩

private theorem run_add_step {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {a b : Nat} {s t u : State L}
    (h1 : run code input a s = some ⟨t, a⟩)
    (h2 : run code input b s = some ⟨u, b⟩) :
    a = b ∧ t = u := by
  induction a generalizing b s with
  | zero =>
    simp only [run] at h1
    cases h1
  | succ a ih =>
    cases b with
    | zero =>
      simp only [run] at h2
      cases h2
    | succ b =>
      simp only [run] at h1 h2
      cases hstep : step code input s with
      | none =>
        rw [hstep] at h1
        cases h1
      | some tr =>
        rw [hstep] at h1 h2
        cases tr with
        | halted s' =>
          simp only [Option.some.injEq] at h1 h2
          have ha : a + 1 = 1 := congrArg Result.executed h1.symm
          have hb : b + 1 = 1 := congrArg Result.executed h2.symm
          have ht : s' = t := congrArg Result.finalState h1
          have hu : s' = u := congrArg Result.finalState h2
          exact ⟨by omega, ht.symm.trans hu⟩
        | next s' =>
          dsimp only at h1 h2
          cases hrec1 : run code input a s' with
          | none =>
            rw [hrec1] at h1
            cases h1
          | some r1 =>
            cases hrec2 : run code input b s' with
            | none =>
              rw [hrec2] at h2
              cases h2
            | some r2 =>
              rw [hrec1] at h1
              rw [hrec2] at h2
              simp only [Option.some.injEq] at h1 h2
              have hr1 : r1 = ⟨t, a⟩ := by
                cases r1
                simp only [Result.mk.injEq] at h1 ⊢
                exact ⟨h1.1, by have := h1.2; omega⟩
              have hr2 : r2 = ⟨u, b⟩ := by
                cases r2
                simp only [Result.mk.injEq] at h2 ⊢
                exact ⟨h2.1, by have := h2.2; omega⟩
              obtain ⟨hab, htu⟩ := ih (hrec1.trans (congrArg some hr1)) (hrec2.trans (congrArg some hr2))
              exact ⟨congrArg Nat.succ hab, htu⟩

private theorem step_next_ne_halt {bits : Nat} {L : Layout bits}
    {code : Program L} {input : Input L} {s u : State L}
    (hs : step code input s = some (.next u))
    {haltIdx : Nat} (hAt : code[haltIdx]? = some .halt) :
    s.pc ≠ haltIdx := by
  intro hEq
  unfold step at hs
  rw [hEq, hAt] at hs
  simp at hs

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
    | loadInput dst addr =>
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases hmem : input.words[(reg s addr).val]? with
      | none => rw [hmem] at h; cases h
      | some w =>
        rw [hmem] at h
        exact advMono h
    | loadData dst addr =>
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      cases hmem : s.data[(reg s addr).val]? with
      | none => rw [hmem] at h; cases h
      | some w =>
        rw [hmem] at h
        exact advMono h
    | storeData addr src =>
      simp only [Option.bind_eq_bind, Option.bind] at h ⊢
      by_cases hmem : (reg s addr).val < s.data.size
      · simp only [dite_eq_left hmem] at h ⊢
        exact advMono h
      · simp only [dite_eq_right hmem] at h
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

private theorem run_join_at_last {bits : Nat} {L : Layout bits}
    (left right : Program L) {haltIdx : Nat} (hHalt : haltIdx < left.size)
    (hAt : left[haltIdx]? = some .halt) (hPosR : 0 < right.size)
    {input : Input L} {start last u : State L} {k b : Nat}
    (hLeft : Steps left input k (Phase.initial start) last)
    (hLastPc : last.pc = haltIdx)
    (hRight : run right input b (Phase.initial last) = some ⟨u, b⟩) :
    let code := join left right haltIdx hHalt
    ∃ v states, v.pc = left.size + u.pc ∧ v.regs = u.regs ∧ v.data = u.data ∧
      run code input (k + 1 + b) (Phase.initial start) = some ⟨v, k + 1 + b⟩ ∧
      SuccessfulTrace code input (Phase.initial start) states ⟨v, k + 1 + b⟩ ∧
      tracePeakWords input states = footprint L := by
  let code := join left right haltIdx hHalt
  have hPre : Steps code input k (Phase.initial start) last :=
    steps_join_left left right hHalt hAt hLeft
  have hGotoFetch : code[last.pc]? = some (.goto left.size) := by
    rw [hLastPc]
    exact (fetch_halt left right hHalt).1
  have hLeftLt : left.size < code.size := (fetch_halt left right hHalt).2 hPosR
  have hJumpStep : step code input last = some (.next { last with pc := left.size }) :=
    step_goto_at hGotoFetch hLeftLt
  have hJmp : Steps code input (k + 1) (Phase.initial start) { last with pc := left.size } :=
    hPre.append (Steps.cons hJumpStep (Steps.zero _))
  obtain ⟨kr, lastR, routeR, haltR, costR⟩ := run_has_steps_then_halt hRight
  have placed : RelocatedSlice right code left.size := relocated_right left right hHalt
  have after := routeR.relocate placed
  have sameEntry : relocateStatePC left.size (Phase.initial last) = { last with pc := left.size } := by
    simp only [relocateStatePC, Phase.initial, Nat.add_zero]
  rw [sameEntry] at after
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state haltR
  have terminal : step code input (relocateStatePC left.size lastR) =
      some (.halted (relocateStatePC left.size u)) := by
    change u = lastR at sameHalt
    rw [sameHalt]
    exact step_halt_at (s := relocateStatePC left.size lastR) (placed lastR.pc .halt atHalt)
  have execution := (hJmp.append after).halts terminal
  change b = kr + 1 at costR
  rw [Nat.add_assoc, ← costR] at execution
  obtain ⟨states, checked⟩ := run_has_successfulTrace execution
  exact ⟨relocateStatePC left.size u, states, rfl, rfl, rfl, execution, checked, checked.peak_eq⟩

private theorem run_linked_pair_pc {bits : Nat} {L : Layout bits}
    (p : Phase L) (right : Program L) (nonempty : 0 < right.size)
    {input : Input L} {start middle u : State L} {a b : Nat}
    (first : run p.code input a (Phase.initial start) = some ⟨middle, a⟩)
    (second : run right input b (Phase.initial middle) = some ⟨u, b⟩) :
    let code := join p.code right p.haltPC p.haltFits
    ∃ v states, v.pc = p.code.size + u.pc ∧ v.regs = u.regs ∧ v.data = u.data ∧
      run code input (a + b) (Phase.initial start) = some ⟨v, a + b⟩ ∧
      SuccessfulTrace code input (Phase.initial start) states ⟨v, a + b⟩ ∧
      tracePeakWords input states = footprint L := by
  let code := join p.code right p.haltPC p.haltFits
  have jmp : Steps code input a (Phase.initial start)
      {middle with pc := p.code.size} := by
    have src : relocateStatePC 0 (Phase.initial start) = Phase.initial start := rfl
    have link := linked_return_of_run_multi (linked := code) (base := 0)
      (ret := fun _ => p.code.size) first
      (fun i op h nonhalt => by
        have neq : i ≠ p.haltPC := fun e => nonhalt
          (Option.some.inj (h.symm.trans (e.symm ▸ p.haltAt)))
        have same : relocateInstr 0 op = op := by cases op <;> simp only [relocateInstr, Nat.zero_add]
        simpa only [code, Nat.zero_add, same] using fetch_left p.code right p.haltFits neq h)
      (fun i h => by
        rw [p.uniqueHalt i h, Nat.zero_add]
        have patched := fetch_halt p.code right p.haltFits
        exact ⟨patched.1, patched.2 nonempty⟩)
    rw [src] at link
    exact link
  obtain ⟨k, last, route, halt, cost⟩ := run_has_steps_then_halt second
  have placed : RelocatedSlice right code p.code.size :=
    relocated_right p.code right p.haltFits
  have after := route.relocate placed
  have sameEntry : relocateStatePC p.code.size (Phase.initial middle) =
      {middle with pc := p.code.size} := by
    simp only [relocateStatePC, Phase.initial, Nat.add_zero]
  rw [sameEntry] at after
  obtain ⟨atHalt, sameHalt⟩ := halted_fetch_and_state halt
  have terminal : step code input (relocateStatePC p.code.size last) =
      some (.halted (relocateStatePC p.code.size u)) := by
    change u = last at sameHalt
    rw [sameHalt]
    exact step_halt_at (s := relocateStatePC p.code.size last) (placed last.pc .halt atHalt)
  have execution := (jmp.append after).halts terminal
  change b = k + 1 at cost
  rw [Nat.add_assoc, ← cost] at execution
  obtain ⟨states, checked⟩ := run_has_successfulTrace execution
  exact ⟨relocateStatePC p.code.size u, states, rfl, rfl, rfl, execution, checked, checked.peak_eq⟩

private theorem run_adapter1 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r)
    {Q quarter : Nat} (hEmitLt : 2 * quarter < 2 ^ bits)
    (s : State (layout16 bits inputCap workCap hi hw))
    (hr5 : (reg s r5).val = Q)
    (hr6 : (reg s r6).val = quarter) :
    ∃ t : State (layout16 bits inputCap workCap hi hw),
      run (adapter1Phase (hi := hi) (hw := hw) hTen).code input 8 (Phase.initial s) = some ⟨t, 8⟩ ∧
      t.data = s.data ∧
      EmitterRegs g.vertexCount g.arcCount r.val Q quarter (2 * quarter) t := by
  let code := (adapter1Phase (hi := hi) (hw := hw) hTen).code
  let st0 := Phase.initial s
  have hpc0 : st0.pc = 0 := rfl
  have hSz : code.size = 8 := rfl
  have hf0 : code[st0.pc]? = some (.imm rZero ⟨0, by omega⟩) := by rw [hpc0]; rfl
  obtain ⟨st1, hs1, hpc1, h1r0, h1keep, h1data⟩ :=
    step_imm16 (input := input) hf0 (by rw [hpc0, hSz]; omega)
  have h1r0v : (reg st1 rZero).val = 0 := by rw [h1r0]
  have hf1 : code[st1.pc]? = some (.imm rOne ⟨1, by omega⟩) := by rw [hpc1, hpc0]; rfl
  obtain ⟨st2, hs2, hpc2, h2r1, h2keep, h2data⟩ :=
    step_imm16 (input := input) hf1 (by rw [hpc1, hpc0, hSz]; omega)
  have h2r1v : (reg st2 rOne).val = 1 := by rw [h2r1]
  have h2r0v : (reg st2 rZero).val = 0 := by rw [h2keep rZero (by decide)]; exact h1r0v
  obtain ⟨wN, hwN, hwNv⟩ := word_mem_eq_of_map_val raw.hdr_n
  have hf2 : code[st2.pc]? = some (.loadInput rN rZero) := by rw [hpc2, hpc1, hpc0]; rfl
  obtain ⟨st3, hs3, hpc3, h3rN, h3keep, h3data⟩ :=
    step_loadInput16 (input := input) hf2 (by rw [hpc2, hpc1, hpc0, hSz]; omega)
      (by rw [h2r0v]; exact hwN)
  have h3r1v : (reg st3 rOne).val = 1 := by rw [h3keep rOne (by decide)]; exact h2r1v
  obtain ⟨wM, hwM, hwMv⟩ := word_mem_eq_of_map_val raw.hdr_m
  have hf3 : code[st3.pc]? = some (.loadInput rM rOne) := by rw [hpc3, hpc2, hpc1, hpc0]; rfl
  obtain ⟨st4, hs4, hpc4, h4rM, h4keep, h4data⟩ :=
    step_loadInput16 (input := input) hf3 (by rw [hpc3, hpc2, hpc1, hpc0, hSz]; omega)
      (by rw [h3r1v]; exact hwM)
  have hf4 : code[st4.pc]? = some (.imm rRoot ⟨2, by omega⟩) := by
    rw [hpc4, hpc3, hpc2, hpc1, hpc0]; rfl
  obtain ⟨st5, hs5, hpc5, h5rRoot, h5keep, h5data⟩ :=
    step_imm16 (input := input) hf4 (by rw [hpc4, hpc3, hpc2, hpc1, hpc0, hSz]; omega)
  have h5rRootv : (reg st5 rRoot).val = 2 := by rw [h5rRoot]
  obtain ⟨wR, hwR, hwRv⟩ := word_mem_eq_of_map_val raw.hdr_r
  have hf5 : code[st5.pc]? = some (.loadInput rRoot rRoot) := by
    rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]; rfl
  obtain ⟨st6, hs6, hpc6, h6rRoot, h6keep, h6data⟩ :=
    step_loadInput16 (input := input) hf5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc0, hSz]; omega)
      (by rw [h5rRootv]; exact hwR)
  have h6r6v : (reg st6 r6).val = quarter := by
    rw [h6keep r6 (by decide), h5keep r6 (by decide), h4keep r6 (by decide),
        h3keep r6 (by decide), h2keep r6 (by decide), h1keep r6 (by decide)]
    exact hr6
  have hf6 : code[st6.pc]? = some (.add r7 r6 r6) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]; rfl
  obtain ⟨st7, hs7, hpc7, h7r7, h7keep, h7data⟩ :=
    step_add16 (input := input) hf6 (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0, hSz]; omega)
  have hf7 : code[st7.pc]? = some .halt := by
    rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc0]; rfl
  have hSteps7 : Steps code input 7 st0 st7 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
      (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero _)))))))
  have hRun8 : run code input 8 st0 = some ⟨st7, 8⟩ := hSteps7.halts (step_halt_at hf7)
  have hConst7 : ConstRegs g.vertexCount g.arcCount r.val st7 := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [h7keep rZero (by decide), h6keep rZero (by decide), h5keep rZero (by decide),
          h4keep rZero (by decide), h3keep rZero (by decide)]
      exact h2r0v
    · rw [h7keep rOne (by decide), h6keep rOne (by decide), h5keep rOne (by decide),
          h4keep rOne (by decide)]
      exact h3r1v
    · rw [h7keep rN (by decide), h6keep rN (by decide), h5keep rN (by decide),
          h4keep rN (by decide), h3rN]
      exact hwNv
    · rw [h7keep rM (by decide), h6keep rM (by decide), h5keep rM (by decide), h4rM]
      exact hwMv
    · rw [h7keep rRoot (by decide), h6rRoot]
      exact hwRv
  refine ⟨st7, hRun8, ?_, ⟨hConst7, ?_, ?_, ?_⟩⟩
  · rw [h7data, h6data, h5data, h4data, h3data, h2data, h1data]; rfl
  · rw [h7keep r5 (by decide), h6keep r5 (by decide), h5keep r5 (by decide),
        h4keep r5 (by decide), h3keep r5 (by decide), h2keep r5 (by decide), h1keep r5 (by decide)]
    exact hr5
  · rw [h7keep r6 (by decide)]
    exact h6r6v
  · rw [h7r7, WordOps.add_no_wrap _ _ (by rw [h6r6v]; omega), h6r6v]
    omega

private theorem run_adapter2 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q quarter : Nat} (hLoopLt : 3 * quarter < 2 ^ bits)
    (s : State (layout16 bits inputCap workCap hi hw))
    (hEmit : EmitterRegs n m root Q quarter (2 * quarter) s) :
    ∃ t : State (layout16 bits inputCap workCap hi hw),
      run (adapter2Phase (hi := hi) (hw := hw)).code input 2 (Phase.initial s) = some ⟨t, 2⟩ ∧
      t.data = s.data ∧
      LoopEntryRegs n m root Q quarter (2 * quarter) (3 * quarter) t := by
  let code := (adapter2Phase (hi := hi) (hw := hw)).code
  let st0 := Phase.initial s
  have hpc0 : st0.pc = 0 := rfl
  have hSz : code.size = 2 := rfl
  have hf0 : code[st0.pc]? = some (.add r8 r6 r7) := by rw [hpc0]; rfl
  obtain ⟨st1, hs1, hpc1, h1r8, h1keep, h1data⟩ :=
    step_add16 (input := input) hf0 (by rw [hpc0, hSz]; omega)
  have hf1 : code[st1.pc]? = some .halt := by rw [hpc1, hpc0]; rfl
  have hRun2 : run code input 2 st0 = some ⟨st1, 2⟩ :=
    (Steps.cons hs1 (Steps.zero _)).halts (step_halt_at hf1)
  have hConst1 : ConstRegs n m root st1 :=
    { zero := by rw [h1keep rZero (by decide)]; exact hEmit.consts.zero
      one := by rw [h1keep rOne (by decide)]; exact hEmit.consts.one
      nVal := by rw [h1keep rN (by decide)]; exact hEmit.consts.nVal
      mVal := by rw [h1keep rM (by decide)]; exact hEmit.consts.mVal
      rootVal := by rw [h1keep rRoot (by decide)]; exact hEmit.consts.rootVal }
  refine ⟨st1, hRun2, h1data,
    ⟨hConst1,
      by rw [h1keep r5 (by decide)]; exact hEmit.qVal,
      by rw [h1keep r6 (by decide)]; exact hEmit.treeBaseVal,
      by rw [h1keep r7 (by decide)]; exact hEmit.emitBaseVal,
      ?_⟩⟩
  have h06 : (reg st0 r6).val = quarter := hEmit.treeBaseVal
  have h07 : (reg st0 r7).val = 2 * quarter := hEmit.emitBaseVal
  rw [h1r8, WordOps.add_no_wrap _ _ (by rw [h06, h07]; omega), h06, h07]
  omega

end LinkingAndAdapters

section LargeBuildIndep

theorem familyForestLoopProgram_sub_indep {bits inputCap workCap c₁ d₁ c₂ d₂ : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (h₁ : c₁ ≤ 2 ^ bits) (k₁ : d₁ ≤ 2 ^ bits)
    (h₂ : c₂ ≤ 2 ^ bits) (k₂ : d₂ ≤ 2 ^ bits) (h32 : 32 ≤ 2 ^ bits) :
    familyForestLoopProgram (hi := hi) (hw := hw) h₁ k₁ h32 =
      familyForestLoopProgram (hi := hi) (hw := hw) h₂ k₂ h32 := by
  unfold familyForestLoopProgram
  rw [PaperB.RamForestProgram.RawBuild.largeBuildProgram_cap_indep h₁ k₁ h₂ k₂ (h8Of32' h32)]

end LargeBuildIndep

section PrefixStepsAtLast

private theorem placed_extract_left {bits k : Nat}
    (xs : Array (Instr bits k)) (n : Nat) (hn : n ≤ xs.size) (i : Nat) (hi : i < n) :
    (xs.extract 0 n)[i]? = xs[i]? := by
  have hsz : (xs.extract 0 n).size = n := by rw [Array.size_extract]; omega
  rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega), Array.getElem_extract]
  simp only [Nat.zero_add]

private theorem prefixRightCode_bodyRelocated {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
    RamDataSliceAdapter.BodyRelocated (bigL := layout16 bits inputCap workCap hi hw) rfl
      ⟨0, by omega⟩ ⟨1, by omega⟩ subCode (prefixRightCode hw hTen) 0 := by
  intro subCode i hiLt op hop
  have hrel : relocateInstr 0 op = op := by cases op <;> simp [relocateInstr]
  have hExt : ((RamDataSliceAdapter.liftCode ⟨0, by omega⟩ ⟨1, by omega⟩ subCode).extract 0
      (4 * subCode.size)).size = 4 * subCode.size := by
    rw [Array.size_extract, RamDataSliceAdapter.liftCode_size]; omega
  rw [prefixRightCode, Nat.zero_add, cast_eq, hrel]
  rw [Array.getElem?_append_left (by rw [hExt]; exact hiLt)]
  change ((RamDataSliceAdapter.liftCode ⟨0, by omega⟩ ⟨1, by omega⟩ subCode).extract 0
      (4 * subCode.size))[i]? = some op
  rw [placed_extract_left _ _ (by rw [RamDataSliceAdapter.liftCode_size]; omega) i hiLt]
  exact hop

private theorem prefixRightCode_epilogue_placed {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
    Placed (prefixRightCode (hi := hi) hw hTen) (4 * subCode.size)
      (epilogueCode (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw) hTen).toList := by
  intro subCode i op hop
  have hExt : ((RamDataSliceAdapter.liftCode ⟨0, by omega⟩ ⟨1, by omega⟩ subCode).extract 0
      (4 * subCode.size)).size = 4 * subCode.size := by
    rw [Array.size_extract, RamDataSliceAdapter.liftCode_size]; omega
  unfold prefixRightCode
  rw [Array.getElem?_append_right (by rw [hExt]; omega), hExt, Nat.add_sub_cancel_left]
  rw [← Array.getElem?_toList]
  exact hop

private theorem prefixRightCode_size {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
    (prefixRightCode (hi := hi) hw hTen).size = 4 * subCode.size + 8 := by
  intro subCode
  unfold prefixRightCode
  rw [Array.size_append, Array.size_extract, RamDataSliceAdapter.liftCode_size]
  have hEp : (epilogueCode (bits := bits) (inputCap := inputCap) (workCap := workCap)
      (hi := hi) (hw := hw) hTen).size = 8 := rfl
  have hMin : min (4 * subCode.size) (4 * subCode.size + 1) = 4 * subCode.size :=
    Nat.min_eq_left (Nat.le_succ _)
  rw [Nat.sub_zero, hMin, hEp]

private theorem prefixRightCode_last_halt {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (prefixRightCode (hi := hi) hw hTen)[(prefixRightCode (hi := hi) hw hTen).size - 1]? = some .halt := by
  have hSz := prefixRightCode_size (hi := hi) hw hTen
  rw [show (prefixRightCode (hi := hi) hw hTen).size - 1 =
      4 * (RamDomAndStaticTree.domAndStaticTreeProgram
        (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen).size + 7 by omega]
  exact prefixRightCode_epilogue_placed (hi := hi) hw hTen 7 .halt rfl

private theorem buildPrefixProgram_last_halt {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    (buildPrefixProgram hi hw hTen)[(buildPrefixProgram hi hw hTen).size - 1]? = some .halt := by
  let p12 := buildPrefixPhase12 hi hw hTen
  let rCode := prefixRightCode (hi := hi) hw hTen
  have hPos : 0 < rCode.size := prefixRightCode_pos (hi := hi) hw hTen
  have hr := prefixRightCode_last_halt (hi := hi) hw hTen
  have hSzPref : (buildPrefixProgram hi hw hTen).size = p12.code.size + rCode.size := by
    unfold buildPrefixProgram join
    rw [Array.size_append, Array.size_set, Array.size_map]
  have hIdx : (buildPrefixProgram hi hw hTen).size - 1 = p12.code.size + (rCode.size - 1) := by
    rw [hSzPref]
    omega
  rw [hIdx]
  exact relocated_right p12.code rCode p12.haltFits (rCode.size - 1) .halt hr

private theorem copyBankLoop_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {code : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    (loopPC exitPC : Nat) (limitReg srcBaseReg dstBaseReg : Fin 16)
    (srcBase dstBase limit : Nat)
    (hlFit : limit < 2 ^ bits)
    (hDiff1 : r11 ≠ r12) (hDiff2 : r11 ≠ r13) (hDiff3 : r12 ≠ r13)
    (hKeepLimit : limitReg ≠ r11 ∧ limitReg ≠ r12 ∧ limitReg ≠ r13)
    (hKeepOne : rOne ≠ r11 ∧ rOne ≠ r12 ∧ rOne ≠ r13)
    (hKeepSrc : srcBaseReg ≠ r11 ∧ srcBaseReg ≠ r12 ∧ srcBaseReg ≠ r13)
    (hKeepDst : dstBaseReg ≠ r11 ∧ dstBaseReg ≠ r12 ∧ dstBaseReg ≠ r13)
    (hSz : loopPC + 7 ≤ code.size) (hExitSz : exitPC < code.size)
    (hPl : Placed code loopPC
      [ .branchLt r11 limitReg (loopPC + 1) exitPC,
        .add r12 srcBaseReg r11,
        .loadData r13 r12,
        .add r12 dstBaseReg r11,
        .storeData r12 r13,
        .add r11 r11 rOne,
        .goto loopPC ])
    (hSrcBound : srcBase + limit ≤ workCap)
    (hDstBound : dstBase + limit ≤ workCap)
    (hDisj : srcBase + limit ≤ dstBase ∨ dstBase + limit ≤ srcBase)
    (srcFn : Nat → Nat) :
    ∀ (rem i : Nat) (s : State (layout16 bits inputCap workCap hi hw)),
      i + rem = limit →
      s.pc = loopPC →
      s.data.size = workCap →
      (reg s rOne).val = 1 →
      (reg s limitReg).val = limit →
      (reg s srcBaseReg).val = srcBase →
      (reg s dstBaseReg).val = dstBase →
      (reg s r11).val = i →
      (∀ k, k < limit → (s.data[srcBase + k]?).map Fin.val = some (srcFn k)) →
      (∀ k, k < i → (s.data[dstBase + k]?).map Fin.val = some (srcFn k)) →
      ∃ t : State (layout16 bits inputCap workCap hi hw),
        Steps code input (7 * rem + 1) s t ∧
        t.pc = exitPC ∧
        t.data.size = workCap ∧
        reg t rZero = reg s rZero ∧
        reg t rOne = reg s rOne ∧
        reg t rN = reg s rN ∧
        reg t rM = reg s rM ∧
        reg t r5 = reg s r5 ∧
        reg t r6 = reg s r6 ∧
        reg t r7 = reg s r7 ∧
        reg t r9 = reg s r9 ∧
        reg t r10 = reg s r10 ∧
        (∀ k, k < limit → (t.data[dstBase + k]?).map Fin.val = some (srcFn k)) ∧
        (∀ w : Nat, (w < dstBase ∨ dstBase + limit ≤ w) → t.data[w]? = s.data[w]?) := by
  intro rem
  induction rem with
  | zero =>
    intro i s hiEq hpc hDsz h1 hLim hSrc hDst hI hSrcData hDstData
    have hiLim : i = limit := by omega
    subst hiLim
    have hf0 : code[s.pc]? = some (.branchLt r11 limitReg (loopPC + 1) exitPC) := by
      rw [hpc]; exact hPl 0 _ rfl
    have hCmp : WordOps.ltb (reg s r11) (reg s limitReg) = false :=
      branchLt_false (by rw [hI, hLim]; exact Nat.le_refl _)
    have ht0 : (if WordOps.ltb (reg s r11) (reg s limitReg) then loopPC + 1 else exitPC) < code.size := by
      rw [hCmp]; exact hExitSz
    have hs1 := step_branchLt_at (input := input) hf0 ht0
    rw [hCmp] at hs1
    refine ⟨{ s with pc := exitPC }, Steps.cons hs1 (Steps.zero _), rfl, hDsz,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hDstData, fun _ _ => rfl⟩
  | succ rem ih =>
    intro i s hiEq hpc hDsz h1 hLim hSrc hDst hI hSrcData hDstData
    have hiLt : i < limit := by omega
    have hf0 : code[s.pc]? = some (.branchLt r11 limitReg (loopPC + 1) exitPC) := by
      rw [hpc]; exact hPl 0 _ rfl
    have hCmp : WordOps.ltb (reg s r11) (reg s limitReg) = true :=
      branchLt_true (by rw [hI, hLim]; exact hiLt)
    have hs1 := step_branchLt_at (input := input) hf0 (by rw [hCmp]; simp only [↓reduceIte]; omega)
    rw [hCmp] at hs1
    let s1 : State (layout16 bits inputCap workCap hi hw) := { s with pc := loopPC + 1 }
    have h1pc : s1.pc = loopPC + 1 := rfl
    have hf1 : code[s1.pc]? = some (.add r12 srcBaseReg r11) := hPl 1 _ rfl
    obtain ⟨s2, hs2, h2pc, h2r12, h2keep, h2data⟩ := step_add16 (input := input) hf1 (by rw [h1pc]; omega)
    have h2srcAddr : (reg s2 r12).val = srcBase + i := by
      have hFit : srcBase + i < 2 ^ bits := by
        have := hw; omega
      rw [h2r12, WordOps.add_no_wrap _ _ (by change (reg s srcBaseReg).val + (reg s r11).val < 2 ^ bits; rw [hSrc, hI]; exact hFit)]
      change (reg s srcBaseReg).val + (reg s r11).val = srcBase + i
      rw [hSrc, hI]
    obtain ⟨wVal, hwVal, hwValEq⟩ : ∃ w, s2.data[(reg s2 r12).val]? = some w ∧ w.val = srcFn i := by
      rw [h2srcAddr, h2data]
      have hGet := hSrcData i hiLt
      cases hq : s.data[srcBase + i]? with
      | none => simp [hq] at hGet
      | some w => exact ⟨w, rfl, by simpa [hq] using hGet⟩
    have hf2 : code[s2.pc]? = some (.loadData r13 r12) := by
      rw [h2pc]; exact hPl 2 _ rfl
    obtain ⟨s3, hs3, h3pc, h3r13, h3keep, h3data⟩ :=
      step_loadData16 (input := input) hf2 hwVal (by rw [h2pc, h1pc]; omega)
    have hf3 : code[s3.pc]? = some (.add r12 dstBaseReg r11) := by
      rw [h3pc, h2pc]; exact hPl 3 _ rfl
    obtain ⟨s4, hs4, h4pc, h4r12, h4keep, h4data⟩ :=
      step_add16 (input := input) hf3 (by rw [h3pc, h2pc, h1pc]; omega)
    have h3dstBase : (reg s3 dstBaseReg).val = dstBase := by
      rw [h3keep dstBaseReg hKeepDst.2.2, h2keep dstBaseReg hKeepDst.2.1]; exact hDst
    have h3i : (reg s3 r11).val = i := by
      rw [h3keep r11 hDiff2, h2keep r11 hDiff1]; exact hI
    have h4dstAddr : (reg s4 r12).val = dstBase + i := by
      have hFit : dstBase + i < 2 ^ bits := by
        have := hw; omega
      rw [h4r12, WordOps.add_no_wrap _ _ (by rw [h3dstBase, h3i]; exact hFit), h3dstBase, h3i]
    have h4r13 : (reg s4 r13).val = srcFn i := by
      rw [h4keep r13 hDiff3.symm, h3r13]; exact hwValEq
    have h4bound : (reg s4 r12).val < s4.data.size := by
      rw [h4dstAddr, h4data, h3data, h2data, hDsz]; omega
    have hf4 : code[s4.pc]? = some (.storeData r12 r13) := by
      rw [h4pc, h3pc, h2pc]; exact hPl 4 _ rfl
    obtain ⟨s5, hs5, h5pc, h5regs, h5data⟩ :=
      step_storeData16 (input := input) hf4 (by rw [h4pc, h3pc, h2pc, h1pc]; omega) h4bound
    have hf5 : code[s5.pc]? = some (.add r11 r11 rOne) := by
      rw [h5pc, h4pc, h3pc, h2pc]; exact hPl 5 _ rfl
    obtain ⟨s6, hs6, h6pc, h6r11, h6keep, h6data⟩ :=
      step_add16 (input := input) hf5 (by rw [h5pc, h4pc, h3pc, h2pc, h1pc]; omega)
    have h5r11 : (reg s5 r11).val = i := by
      rw [reg_eq_of_regs_eq h5regs, h4keep r11 hDiff1]; exact h3i
    have h5one : (reg s5 rOne).val = 1 := by
      rw [reg_eq_of_regs_eq h5regs, h4keep rOne hKeepOne.2.1, h3keep rOne hKeepOne.2.2,
          h2keep rOne hKeepOne.2.1]; exact h1
    have h6i : (reg s6 r11).val = i + 1 := by
      have hFit : i + 1 < 2 ^ bits := by omega
      rw [h6r11, WordOps.add_no_wrap _ _ (by rw [h5r11, h5one]; exact hFit), h5r11, h5one]
    have hf6 : code[s6.pc]? = some (.goto loopPC) := by
      rw [h6pc, h5pc, h4pc, h3pc, h2pc]; exact hPl 6 _ rfl
    have hs7 := step_goto_at (input := input) hf6 (by omega)
    let s7 : State (layout16 bits inputCap workCap hi hw) := { s6 with pc := loopPC }
    have h7data : s7.data = s.data.set (dstBase + i) (reg s4 r13) (by rw [hDsz]; omega) := by
      change s6.data = _
      have h4d : s4.data = s.data := by rw [h4data, h3data, h2data]
      simp only [h6data, h5data, h4d, h4dstAddr]
    have hKeepReg : ∀ r : Fin 16, r ≠ r11 → r ≠ r12 → r ≠ r13 → reg s7 r = reg s r := by
      intro r hr11 hr12 hr13
      change reg s6 r = reg s r
      rw [h6keep r hr11, reg_eq_of_regs_eq h5regs, h4keep r hr12, h3keep r hr13, h2keep r hr12]
      rfl
    have h7Dsz : s7.data.size = workCap := by rw [h7data, Array.size_set, hDsz]
    have h7srcData : ∀ k, k < limit → (s7.data[srcBase + k]?).map Fin.val = some (srcFn k) := by
      intro k hk
      have hNe : dstBase + i ≠ srcBase + k := by
        rcases hDisj with hL | hR <;> omega
      rw [h7data, Array.getElem?_set_ne _ hNe]
      exact hSrcData k hk
    have h7dstData : ∀ k, k < i + 1 → (s7.data[dstBase + k]?).map Fin.val = some (srcFn k) := by
      intro k hk
      by_cases hEq : k = i
      · subst hEq
        rw [h7data, getElem?_pos _ _ (by rw [Array.size_set, hDsz]; omega)]
        simp only [Array.getElem_set_self, Option.map_some]
        exact congrArg some h4r13
      · have hk' : k < i := by omega
        rw [h7data, Array.getElem?_set_ne _ (by omega)]
        exact hDstData k hk'
    have hLoop7 : Steps code input 7 s s7 :=
      Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
        (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero _)))))))
    obtain ⟨t, hRest, htpc, htDsz, ht0, ht1, htN, htM, ht5, ht6, ht7, ht9, ht10, htDst, htFrame⟩ :=
      ih (i + 1) s7 (by omega) rfl h7Dsz
        (by rw [hKeepReg rOne hKeepOne.1 hKeepOne.2.1 hKeepOne.2.2]; exact h1)
        (by rw [hKeepReg limitReg hKeepLimit.1 hKeepLimit.2.1 hKeepLimit.2.2]; exact hLim)
        (by rw [hKeepReg srcBaseReg hKeepSrc.1 hKeepSrc.2.1 hKeepSrc.2.2]; exact hSrc)
        (by rw [hKeepReg dstBaseReg hKeepDst.1 hKeepDst.2.1 hKeepDst.2.2]; exact hDst)
        h6i h7srcData h7dstData
    have hStepsEq : 7 * (rem + 1) + 1 = 7 + (7 * rem + 1) := by omega
    rw [hStepsEq]
    refine ⟨t, hLoop7.append hRest, htpc, htDsz, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htDst, ?_⟩
    · exact ht0.trans (hKeepReg rZero (by decide) (by decide) (by decide))
    · exact ht1.trans (hKeepReg rOne (by decide) (by decide) (by decide))
    · exact htN.trans (hKeepReg rN (by decide) (by decide) (by decide))
    · exact htM.trans (hKeepReg rM (by decide) (by decide) (by decide))
    · exact ht5.trans (hKeepReg r5 (by decide) (by decide) (by decide))
    · exact ht6.trans (hKeepReg r6 (by decide) (by decide) (by decide))
    · exact ht7.trans (hKeepReg r7 (by decide) (by decide) (by decide))
    · exact ht9.trans (hKeepReg r9 (by decide) (by decide) (by decide))
    · exact ht10.trans (hKeepReg r10 (by decide) (by decide) (by decide))
    · intro w hw
      rw [htFrame w hw, h7data, Array.getElem?_set_ne _ (by omega)]

private theorem run_copyDenseIn_pre14 {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q mReach : Nat}
    (hnPos : 1 ≤ n) (hQPos : 1 ≤ Q) (hQLe : Q ≤ n) (hmLe : mReach ≤ m)
    (hCap : 64 * (n + m + 1) ≤ workCap)
    (s1 : State (layout16 bits inputCap workCap hi hw))
    (hConst : ConstRegs n m root s1)
    (hr5 : (reg s1 r5).val = Q)
    (hr6 : (reg s1 r6).val = mReach) :
    let quarter := prefixQuarter workCap
    let denseInBase := prefixDenseInBase workCap
    let code := (copyDenseInPhase (hi := hi) hw hTen).code
    ∃ st14 : State (layout16 bits inputCap workCap hi hw),
      Steps code input 14 (Phase.initial s1) st14 ∧
      st14.pc = 14 ∧
      st14.data.size = workCap ∧
      (∀ idx, 2 ≤ idx → idx < denseInBase → st14.data[idx]? = s1.data[idx]?) ∧
      (reg st14 rZero).val = 0 ∧
      (reg st14 rOne).val = 1 ∧
      (reg st14 rN).val = n ∧
      (reg st14 r5).val = Q ∧
      (reg st14 r6).val = mReach ∧
      (reg st14 r7).val = denseInBase + 2 ∧
      (reg st14 r9).val = 6 * n ∧
      (reg st14 r10).val = Q + 1 ∧
      (reg st14 r11).val = 0 ∧
      st14.data[0]? = some ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩ ∧
      st14.data[1]? = some ⟨quarter, quarter_lt_pow2 hw hTen⟩ ∧
      (st14.data[denseInBase]?).map Fin.val = some Q ∧
      (st14.data[denseInBase + 1]?).map Fin.val = some mReach := by
  intro quarter denseInBase code
  have hQuarterGe : 16 * (n + m + 1) ≤ quarter := by
    unfold quarter prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hInBaseGe : 48 * (n + m + 1) ≤ denseInBase := by
    unfold denseInBase prefixDenseInBase
    omega
  have hDenseInEnd : denseInBase + 3 + Q + mReach ≤ workCap := by
    unfold denseInBase prefixDenseInBase prefixQuarter
    omega
  have hLtPow : workCap ≤ 2 ^ bits := hw
  let st0 := Phase.initial s1
  have hst0pc : st0.pc = 0 := rfl
  have hDsz0 : st0.data.size = workCap := s1.data_size
  have hCodeSz : code.size = 33 := rfl
  have hf0 : code[st0.pc]? = some (.imm r7 ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩) := by
    rw [hst0pc]; rfl
  obtain ⟨st1, hs1, hpc1, h1r7, h1keep, h1data⟩ :=
    step_imm16 (input := input) hf0 (by rw [hst0pc, hCodeSz]; omega)
  have h1r0 : (reg st1 rZero).val = 0 := by
    rw [h1keep rZero (by decide)]; exact hConst.zero
  have hf1 : code[st1.pc]? = some (.storeData rZero r7) := by rw [hpc1, hst0pc]; rfl
  obtain ⟨st2, hs2, hpc2, h2regs, h2data⟩ :=
    step_storeData16 (input := input) hf1 (by rw [hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h1r0, h1data, hDsz0]; omega)
  have h2r7 : (reg st2 r7).val = denseInBase := by
    rw [reg_eq_of_regs_eq h2regs, h1r7]
  have hf2 : code[st2.pc]? = some (.imm r8 ⟨quarter, quarter_lt_pow2 hw hTen⟩) := by
    rw [hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st3, hs3, hpc3, h3r8, h3keep, h3data⟩ :=
    step_imm16 (input := input) (s := st2) (d := r8)
      (w := ⟨quarter, quarter_lt_pow2 hw hTen⟩) hf2 (by rw [hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h3r1 : (reg st3 rOne).val = 1 := by
    rw [h3keep rOne (by decide), reg_eq_of_regs_eq h2regs, h1keep rOne (by decide)]; exact hConst.one
  have hf3 : code[st3.pc]? = some (.storeData rOne r8) := by rw [hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st4, hs4, hpc4, h4regs, h4data⟩ :=
    step_storeData16 (input := input) hf3 (by rw [hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h3r1, h3data, h2data, Array.size_set, h1data, hDsz0]; omega)
  have h4r7 : (reg st4 r7).val = denseInBase := by
    rw [reg_eq_of_regs_eq h4regs, h3keep r7 (by decide)]; exact h2r7
  have h4r1 : (reg st4 rOne).val = 1 := by rw [reg_eq_of_regs_eq h4regs]; exact h3r1
  have h4Dsz : st4.data.size = workCap := by
    rw [h4data, Array.size_set, h3data, h2data, Array.size_set, h1data, hDsz0]
  have hf4 : code[st4.pc]? = some (.storeData r7 r5) := by rw [hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st5, hs5, hpc5, h5regs, h5data⟩ :=
    step_storeData16 (input := input) hf4 (by rw [hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h4r7, h4Dsz]; omega)
  have h5r7 : (reg st5 r7).val = denseInBase := by rw [reg_eq_of_regs_eq h5regs]; exact h4r7
  have h5r1 : (reg st5 rOne).val = 1 := by rw [reg_eq_of_regs_eq h5regs]; exact h4r1
  have hf5 : code[st5.pc]? = some (.add r7 r7 rOne) := by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st6, hs6, hpc6, h6r7, h6keep, h6data⟩ :=
    step_add16 (input := input) hf5 (by rw [hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h6r7v : (reg st6 r7).val = denseInBase + 1 := by
    rw [h6r7, WordOps.add_no_wrap _ _ (by rw [h5r7, h5r1]; omega), h5r7, h5r1]
  have h6Dsz : st6.data.size = workCap := by
    rw [h6data, h5data, Array.size_set, h4Dsz]
  have hf6 : code[st6.pc]? = some (.storeData r7 r6) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st7, hs7, hpc7, h7regs, h7data⟩ :=
    step_storeData16 (input := input) hf6
      (by rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
      (by rw [h6r7v, h6Dsz]; omega)
  have h7const : ∀ r : Fin 16, r = rZero ∨ r = rOne ∨ r = rN ∨ r = rM ∨ r = r5 ∨ r = r6 →
      reg st7 r = reg s1 r := by
    intro r hr
    have hNe7 : r ≠ r7 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe8 : r ≠ r8 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [reg_eq_of_regs_eq h7regs, h6keep r hNe7, reg_eq_of_regs_eq h5regs, reg_eq_of_regs_eq h4regs,
        h3keep r hNe8, reg_eq_of_regs_eq h2regs, h1keep r hNe7]
    rfl
  have h7rN : (reg st7 rN).val = n := by rw [h7const rN (Or.inr (Or.inr (Or.inl rfl)))]; exact hConst.nVal
  have h7r5 : (reg st7 r5).val = Q := by rw [h7const r5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hr5
  have h7r1 : (reg st7 rOne).val = 1 := by rw [h7const rOne (Or.inr (Or.inl rfl))]; exact hConst.one
  have h7r0 : (reg st7 rZero).val = 0 := by rw [h7const rZero (Or.inl rfl)]; exact hConst.zero
  have h7r7 : (reg st7 r7).val = denseInBase + 1 := by rw [reg_eq_of_regs_eq h7regs]; exact h6r7v
  have hf7 : code[st7.pc]? = some (.add r9 rN rN) := by
    rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st8, hs8, hpc8, h8r9, h8keep, h8data⟩ :=
    step_add16 (input := input) hf7
      (by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h8r9v : (reg st8 r9).val = 2 * n := by
    rw [h8r9, WordOps.add_no_wrap _ _ (by rw [h7rN]; omega), h7rN]; omega
  have hf8 : code[st8.pc]? = some (.add r9 r9 r9) := by
    rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st9, hs9, hpc9, h9r9, h9keep, h9data⟩ :=
    step_add16 (input := input) hf8
      (by rw [hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h9r9v : (reg st9 r9).val = 4 * n := by
    rw [h9r9, WordOps.add_no_wrap _ _ (by rw [h8r9v]; omega), h8r9v]; omega
  have h9rN : (reg st9 rN).val = n := by rw [h9keep rN (by decide), h8keep rN (by decide)]; exact h7rN
  have hf9 : code[st9.pc]? = some (.add r9 r9 rN) := by
    rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st10, hs10, hpc10, h10r9, h10keep, h10data⟩ :=
    step_add16 (input := input) hf9
      (by rw [hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h10r9v : (reg st10 r9).val = 5 * n := by
    rw [h10r9, WordOps.add_no_wrap _ _ (by rw [h9r9v, h9rN]; omega), h9r9v, h9rN]; omega
  have h10rN : (reg st10 rN).val = n := by rw [h10keep rN (by decide)]; exact h9rN
  have hf10 : code[st10.pc]? = some (.add r9 r9 rN) := by
    rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st11, hs11, hpc11, h11r9, h11keep, h11data⟩ :=
    step_add16 (input := input) hf10
      (by rw [hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h11r9v : (reg st11 r9).val = 6 * n := by
    rw [h11r9, WordOps.add_no_wrap _ _ (by rw [h10r9v, h10rN]; omega), h10r9v, h10rN]; omega
  have h11r5 : (reg st11 r5).val = Q := by
    rw [h11keep r5 (by decide), h10keep r5 (by decide), h9keep r5 (by decide), h8keep r5 (by decide)]; exact h7r5
  have h11r1 : (reg st11 rOne).val = 1 := by
    rw [h11keep rOne (by decide), h10keep rOne (by decide), h9keep rOne (by decide), h8keep rOne (by decide)]; exact h7r1
  have hf11 : code[st11.pc]? = some (.add r10 r5 rOne) := by
    rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st12, hs12, hpc12, h12r10, h12keep, h12data⟩ :=
    step_add16 (input := input) hf11
      (by rw [hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h12r10v : (reg st12 r10).val = Q + 1 := by
    rw [h12r10, WordOps.add_no_wrap _ _ (by rw [h11r5, h11r1]; omega), h11r5, h11r1]
  have h12r7 : (reg st12 r7).val = denseInBase + 1 := by
    rw [h12keep r7 (by decide), h11keep r7 (by decide), h10keep r7 (by decide),
        h9keep r7 (by decide), h8keep r7 (by decide)]; exact h7r7
  have h12r1 : (reg st12 rOne).val = 1 := by rw [h12keep rOne (by decide)]; exact h11r1
  have hf12 : code[st12.pc]? = some (.add r7 r7 rOne) := by
    rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st13, hs13, hpc13, h13r7, h13keep, h13data⟩ :=
    step_add16 (input := input) hf12
      (by rw [hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h13r7v : (reg st13 r7).val = denseInBase + 2 := by
    rw [h13r7, WordOps.add_no_wrap _ _ (by rw [h12r7, h12r1]; omega), h12r7, h12r1]
  have h13r0 : (reg st13 rZero).val = 0 := by
    rw [h13keep rZero (by decide), h12keep rZero (by decide), h11keep rZero (by decide),
        h10keep rZero (by decide), h9keep rZero (by decide), h8keep rZero (by decide)]; exact h7r0
  have hf13 : code[st13.pc]? = some (.mov r11 rZero) := by
    rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]; rfl
  obtain ⟨st14, hs14, hpc14, h14r11, h14keep, h14data⟩ :=
    step_mov16 (input := input) hf13
      (by rw [hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc, hCodeSz]; omega)
  have h14pc : st14.pc = 14 := by
    rw [hpc14, hpc13, hpc12, hpc11, hpc10, hpc9, hpc8, hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hst0pc]
  have hPre14 : Steps code input 14 st0 st14 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4 (Steps.cons hs5
      (Steps.cons hs6 (Steps.cons hs7 (Steps.cons hs8 (Steps.cons hs9 (Steps.cons hs10
        (Steps.cons hs11 (Steps.cons hs12 (Steps.cons hs13 (Steps.cons hs14 (Steps.zero _))))))))))))))
  have h14Dsz : st14.data.size = workCap := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data, Array.size_set, h6Dsz]
  have h14dataEq : ∀ idx, 2 ≤ idx → idx < denseInBase → st14.data[idx]? = s1.data[idx]? := by
    intro idx hLo hHi
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data,
        h7data, Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data, Array.getElem?_set_ne _ (by rw [h4r7]; omega),
        h4data, Array.getElem?_set_ne _ (by rw [h3r1]; omega),
        h3data, h2data, Array.getElem?_set_ne _ (by rw [h1r0]; omega), h1data]
    rfl
  have h14keepConst : ∀ r : Fin 16, r = rZero ∨ r = rOne ∨ r = rN ∨ r = rM ∨ r = r5 ∨ r = r6 →
      reg st14 r = reg s1 r := by
    intro r hr
    have hNe7 : r ≠ r7 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe9 : r ≠ r9 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe10 : r ≠ r10 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have hNe11 : r ≠ r11 := by rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [h14keep r hNe11, h13keep r hNe7, h12keep r hNe10, h11keep r hNe9,
        h10keep r hNe9, h9keep r hNe9, h8keep r hNe9]
    exact h7const r hr
  have h14_0 : st14.data[0]? = some ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩ := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data,
        Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data, Array.getElem?_set_ne _ (by rw [h4r7]; omega),
        h4data, Array.getElem?_set_ne _ (by rw [h3r1]; omega),
        h3data, h2data]
    simp only [h1r0, Array.getElem?_set_self, h1r7]
  have h14_1 : st14.data[1]? = some ⟨quarter, quarter_lt_pow2 hw hTen⟩ := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data,
        Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data, Array.getElem?_set_ne _ (by rw [h4r7]; omega),
        h4data]
    simp only [h3r1, Array.getElem?_set_self, h3r8]
  have h14_d0 : (st14.data[denseInBase]?).map Fin.val = some Q := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data,
        Array.getElem?_set_ne _ (by rw [h6r7v]; omega),
        h6data, h5data]
    simp only [h4r7, Array.getElem?_set_self, Option.map_some]
    exact congrArg some (by rw [reg_eq_of_regs_eq h4regs, h3keep r5 (by decide),
      reg_eq_of_regs_eq h2regs, h1keep r5 (by decide)]; exact hr5)
  have h14_d1 : (st14.data[denseInBase + 1]?).map Fin.val = some mReach := by
    rw [h14data, h13data, h12data, h11data, h10data, h9data, h8data, h7data]
    simp only [h6r7v, Array.getElem?_set_self, Option.map_some]
    exact congrArg some (by rw [h6keep r6 (by decide), reg_eq_of_regs_eq h5regs,
      reg_eq_of_regs_eq h4regs, h3keep r6 (by decide), reg_eq_of_regs_eq h2regs,
      h1keep r6 (by decide)]; exact hr6)
  have h14r10v : (reg st14 r10).val = Q + 1 := by
    rw [h14keep r10 (by decide), h13keep r10 (by decide)]; exact h12r10v
  have h14r9v : (reg st14 r9).val = 6 * n := by
    rw [h14keep r9 (by decide), h13keep r9 (by decide), h12keep r9 (by decide)]; exact h11r9v
  have h14r7v : (reg st14 r7).val = denseInBase + 2 := by
    rw [h14keep r7 (by decide)]; exact h13r7v
  have h14r11v : (reg st14 r11).val = 0 := by
    rw [h14r11]; exact h13r0
  exact ⟨st14, hPre14, h14pc, h14Dsz, h14dataEq,
    by rw [h14keepConst rZero (Or.inl rfl)]; exact hConst.zero,
    by rw [h14keepConst rOne (Or.inr (Or.inl rfl))]; exact hConst.one,
    by rw [h14keepConst rN (Or.inr (Or.inr (Or.inl rfl)))]; exact hConst.nVal,
    by rw [h14keepConst r5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))]; exact hr5,
    by rw [h14keepConst r6 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))]; exact hr6,
    h14r7v, h14r9v, h14r10v, h14r11v, h14_0, h14_1, h14_d0, h14_d1⟩

private theorem run_copyDenseIn {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m root Q mReach : Nat}
    (hnPos : 1 ≤ n) (hQPos : 1 ≤ Q) (hQLe : Q ≤ n) (hmLe : mReach ≤ m)
    (hCap : 64 * (n + m + 1) ≤ workCap)
    (inStart inSrc : Nat → Nat)
    (s1 : State (layout16 bits inputCap workCap hi hw))
    (hConst : ConstRegs n m root s1)
    (hr5 : (reg s1 r5).val = Q)
    (hr6 : (reg s1 r6).val = mReach)
    (hStart1 : ∀ i, i ≤ Q → (s1.data[6 * n + i]?).map Fin.val = some (inStart i))
    (hSrc1 : ∀ k, k < mReach → (s1.data[7 * n + 1 + k]?).map Fin.val = some (inSrc k)) :
    let quarter := prefixQuarter workCap
    let denseInBase := prefixDenseInBase workCap
    ∃ (s2 : State (layout16 bits inputCap workCap hi hw)) (steps2 : Nat),
      steps2 ≤ 7 * Q + 7 * mReach + 28 ∧
      run (copyDenseInPhase (hi := hi) hw hTen).code input steps2 (Phase.initial s1) =
        some ⟨s2, steps2⟩ ∧
      s2.data.size = workCap ∧
      s2.data[0]? = some ⟨denseInBase, three_quarter_lt_pow2 hw hTen⟩ ∧
      s2.data[1]? = some ⟨quarter, quarter_lt_pow2 hw hTen⟩ ∧
      (s2.data[denseInBase]?).map Fin.val = some Q ∧
      (s2.data[denseInBase + 1]?).map Fin.val = some mReach ∧
      (∀ i, i ≤ Q → (s2.data[denseInBase + 2 + i]?).map Fin.val = some (inStart i)) ∧
      (∀ k, k < mReach → (s2.data[denseInBase + 3 + Q + k]?).map Fin.val = some (inSrc k)) ∧
      (∀ idx, 3 * n ≤ idx → idx < 5 * n → s2.data[idx]? = s1.data[idx]?) := by
  intro quarter denseInBase
  let code := (copyDenseInPhase (hi := hi) hw hTen).code
  let st0 := Phase.initial s1
  have hCodeSz : code.size = 33 := rfl
  have hQuarterGe : 16 * (n + m + 1) ≤ quarter := by
    unfold quarter prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hInBaseGe : 48 * (n + m + 1) ≤ denseInBase := by
    unfold denseInBase prefixDenseInBase
    omega
  have hDenseInEnd : denseInBase + 3 + Q + mReach ≤ workCap := by
    unfold denseInBase prefixDenseInBase prefixQuarter
    omega
  have hFit7n1 : 7 * n + 1 + mReach ≤ workCap := by omega
  obtain ⟨st14, hPre14, h14pc, h14Dsz, h14dataEq, h14r0v, h14r1v, h14rNv, h14r5v, h14r6v,
      h14r7v, h14r9v, h14r10v, h14r11v, h14_0, h14_1, h14_d0, h14_d1⟩ :=
    run_copyDenseIn_pre14 input hnPos hQPos hQLe hmLe hCap s1 hConst hr5 hr6
  have hPl1 : Placed code 14
      [ .branchLt r11 r10 15 21, .add r12 r9 r11, .loadData r13 r12, .add r12 r7 r11,
        .storeData r12 r13, .add r11 r11 rOne, .goto 14 ] := by
    intro j op hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp at hj <;> subst hj <;> rfl
  obtain ⟨st21, hLoop1, h21pc, h21Dsz, h21_0, h21_1, h21_N, h21_M, h21_5, h21_6, h21_7, h21_9, h21_10,
      h21_inStart, h21_frame⟩ :=
    copyBankLoop_steps (input := input) 14 21 r10 r9 r7 (6 * n) (denseInBase + 2) (Q + 1)
      (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) hPl1 (by omega) (by omega) (Or.inl (by omega)) inStart
      (Q + 1) 0 st14 (Nat.zero_add _) h14pc h14Dsz
      h14r1v h14r10v h14r9v h14r7v h14r11v
      (fun k hk => by
        have hlt : 6 * n + k < denseInBase := by omega
        have hlo : 2 ≤ 6 * n + k := by omega
        rw [h14dataEq _ hlo hlt]; exact hStart1 k (by omega))
      (fun k hk => by omega)
  have hf21 : code[st21.pc]? = some (.add r9 r9 rN) := by rw [h21pc]; rfl
  obtain ⟨st22, hs22, hpc22, h22r9, h22keep, h22data⟩ :=
    step_add16 (input := input) hf21 (by rw [h21pc, hCodeSz]; omega)
  have h21_9v : (reg st21 r9).val = 6 * n := by rw [h21_9]; exact h14r9v
  have h21_Nv : (reg st21 rN).val = n := by rw [h21_N]; exact h14rNv
  have h22r9v : (reg st22 r9).val = 7 * n := by
    rw [h22r9, WordOps.add_no_wrap _ _ (by rw [h21_9v, h21_Nv]; omega), h21_9v, h21_Nv]; omega
  have h22r1 : (reg st22 rOne).val = 1 := by
    rw [h22keep rOne (by decide), h21_1]; exact h14r1v
  have hf22 : code[st22.pc]? = some (.add r9 r9 rOne) := by rw [hpc22, h21pc]; rfl
  obtain ⟨st23, hs23, hpc23, h23r9, h23keep, h23data⟩ :=
    step_add16 (input := input) hf22 (by rw [hpc22, h21pc, hCodeSz]; omega)
  have h23r9v : (reg st23 r9).val = 7 * n + 1 := by
    rw [h23r9, WordOps.add_no_wrap _ _ (by rw [h22r9v, h22r1]; omega), h22r9v, h22r1]
  have h23r7v : (reg st23 r7).val = denseInBase + 2 := by
    rw [h23keep r7 (by decide), h22keep r7 (by decide), h21_7]; exact h14r7v
  have h23r10v : (reg st23 r10).val = Q + 1 := by
    rw [h23keep r10 (by decide), h22keep r10 (by decide), h21_10]; exact h14r10v
  have hf23 : code[st23.pc]? = some (.add r7 r7 r10) := by rw [hpc23, hpc22, h21pc]; rfl
  obtain ⟨st24, hs24, hpc24, h24r7, h24keep, h24data⟩ :=
    step_add16 (input := input) hf23 (by rw [hpc23, hpc22, h21pc, hCodeSz]; omega)
  have hDenseInLt : denseInBase + 3 + Q < workCap := by
    unfold denseInBase prefixDenseInBase prefixQuarter
    omega
  have h24r7v : (reg st24 r7).val = denseInBase + 3 + Q := by
    rw [h24r7, WordOps.add_no_wrap _ _ (by rw [h23r7v, h23r10v]; omega), h23r7v, h23r10v]; omega
  have h24r0v : (reg st24 rZero).val = 0 := by
    rw [h24keep rZero (by decide), h23keep rZero (by decide), h22keep rZero (by decide), h21_0]
    exact h14r0v
  have hf24 : code[st24.pc]? = some (.mov r11 rZero) := by rw [hpc24, hpc23, hpc22, h21pc]; rfl
  obtain ⟨st25, hs25, hpc25, h25r11, h25keep, h25data⟩ :=
    step_mov16 (input := input) hf24 (by rw [hpc24, hpc23, hpc22, h21pc, hCodeSz]; omega)
  have h25pc : st25.pc = 25 := by rw [hpc25, hpc24, hpc23, hpc22, h21pc]
  have hMid4 : Steps code input 4 st21 st25 :=
    Steps.cons hs22 (Steps.cons hs23 (Steps.cons hs24 (Steps.cons hs25 (Steps.zero _))))
  have h25Dsz : st25.data.size = workCap := by
    rw [h25data, h24data, h23data, h22data, h21Dsz]
  have h25dataEq : st25.data = st21.data := by
    rw [h25data, h24data, h23data, h22data]
  have hPl2 : Placed code 25
      [ .branchLt r11 r6 26 32, .add r12 r9 r11, .loadData r13 r12, .add r12 r7 r11,
        .storeData r12 r13, .add r11 r11 rOne, .goto 25 ] := by
    intro j op hj
    rcases j with _ | _ | _ | _ | _ | _ | _ | j <;> simp at hj <;> subst hj <;> rfl
  have h25_6 : (reg st25 r6).val = mReach := by
    rw [h25keep r6 (by decide), h24keep r6 (by decide), h23keep r6 (by decide),
        h22keep r6 (by decide), h21_6]; exact h14r6v
  have h25_1 : (reg st25 rOne).val = 1 := by
    rw [h25keep rOne (by decide), h24keep rOne (by decide), h23keep rOne (by decide)]; exact h22r1
  have h25_9 : (reg st25 r9).val = 7 * n + 1 := by
    rw [h25keep r9 (by decide), h24keep r9 (by decide)]; exact h23r9v
  have h25_7 : (reg st25 r7).val = denseInBase + 3 + Q := by
    rw [h25keep r7 (by decide)]; exact h24r7v
  obtain ⟨st32, hLoop2, h32pc, h32Dsz, _, _, _, _, _, _, _, _, _, h32_inSrc, h32_frame⟩ :=
    copyBankLoop_steps (input := input) 25 32 r6 r9 r7 (7 * n + 1) (denseInBase + 3 + Q) mReach
      (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega) (by omega) hPl2 (by omega) (by omega) (Or.inl (by omega)) inSrc
      mReach 0 st25 (Nat.zero_add _) h25pc h25Dsz h25_1 h25_6 h25_9 h25_7
      (by rw [h25r11]; exact h24r0v)
      (fun k hk => by
        have hkLt48 : 7 * n + 1 + k < 48 * (n + m + 1) := by
          have := Nat.lt_of_lt_of_le hk hmLe
          omega
        have hlt : 7 * n + 1 + k < denseInBase := Nat.lt_of_lt_of_le hkLt48 hInBaseGe
        have hlo : 2 ≤ 7 * n + 1 + k := by omega
        rw [h25dataEq, h21_frame _ (Or.inl (by omega)), h14dataEq _ hlo hlt]
        exact hSrc1 k hk)
      (fun k hk => by omega)
  have hf32 : code[st32.pc]? = some .halt := by rw [h32pc]; rfl
  have hTotalSteps : Steps code input (14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1)) st0 st32 := by
    simpa only [Nat.add_assoc] using (hPre14.append (hLoop1.append (hMid4.append hLoop2)))
  have hRun : run code input (14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1) + 1) st0 =
      some ⟨st32, 14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1) + 1⟩ :=
    hTotalSteps.halts (step_halt_at hf32)
  refine ⟨st32, 14 + (7 * (Q + 1) + 1) + 4 + (7 * mReach + 1) + 1, by omega, hRun, h32Dsz,
    ?_, ?_, ?_, ?_, ?_, h32_inSrc, ?_⟩
  · rw [h32_frame 0 (Or.inl (by omega)), h25dataEq, h21_frame 0 (Or.inl (by omega))]; exact h14_0
  · rw [h32_frame 1 (Or.inl (by omega)), h25dataEq, h21_frame 1 (Or.inl (by omega))]; exact h14_1
  · rw [h32_frame denseInBase (Or.inl (by omega)), h25dataEq, h21_frame denseInBase (Or.inl (by omega))]
    exact h14_d0
  · rw [h32_frame (denseInBase + 1) (Or.inl (by omega)), h25dataEq,
        h21_frame (denseInBase + 1) (Or.inl (by omega))]
    exact h14_d1
  · intro i hi
    rw [h32_frame (denseInBase + 2 + i) (Or.inl (by omega)), h25dataEq]
    exact h21_inStart i (by omega)
  · intro idx h3n h5n
    have hGe2 : 2 ≤ idx := by omega
    have hLtQ : idx < denseInBase := by omega
    rw [h32_frame idx (Or.inl (by omega)), h25dataEq, h21_frame idx (Or.inl (by omega))]
    exact h14dataEq idx hGe2 hLtQ

private theorem run_epilogue_steps {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    {linkedCode : Program (layout16 bits inputCap workCap hi hw)}
    {input : Input (layout16 bits inputCap workCap hi hw)}
    (base Q mReach : Nat)
    (hPl : Placed linkedCode base (epilogueCode (hi := hi) (hw := hw) hTen).toList)
    (hSz : base + 8 ≤ linkedCode.size)
    (s : State (layout16 bits inputCap workCap hi hw))
    (hpc : s.pc = base)
    (hPtr0 : s.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩)
    (hPtr1 : s.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩)
    (hQ : (s.data[prefixDenseInBase workCap]?).map Fin.val = some Q)
    (hM : (s.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach)
    (hFit : prefixDenseInBase workCap + 1 < 2 ^ bits) :
    ∃ u : State (layout16 bits inputCap workCap hi hw),
      Steps linkedCode input 7 s u ∧
      u.pc = base + 7 ∧
      linkedCode[u.pc]? = some .halt := by
  have hf0 : linkedCode[s.pc]? = some (.imm r15 ⟨0, by omega⟩) := by rw [hpc]; exact hPl 0 _ rfl
  obtain ⟨s1, hs1, hpc1, h1r15, h1keep, h1data⟩ := step_imm16 (input := input) hf0 (by omega)
  have h1r15v : (reg s1 r15).val = 0 := by rw [h1r15]
  have hf1 : linkedCode[s1.pc]? = some (.loadData r15 r15) := by rw [hpc1, hpc]; exact hPl 1 _ rfl
  obtain ⟨s2, hs2, hpc2, h2r15, h2keep, h2data⟩ :=
    step_loadData16 (input := input) hf1 (by rw [h1r15v, h1data]; exact hPtr0) (by omega)
  have h2r15v : (reg s2 r15).val = prefixDenseInBase workCap := by rw [h2r15]
  obtain ⟨wQ, hwQ, _⟩ : ∃ w, s2.data[(reg s2 r15).val]? = some w ∧ w.val = Q := by
    rw [h2r15v, h2data, h1data]
    cases hq : s.data[prefixDenseInBase workCap]? with
    | none => simp [hq] at hQ
    | some w => exact ⟨w, rfl, by simpa [hq] using hQ⟩
  have hf2 : linkedCode[s2.pc]? = some (.loadData r5 r15) := by rw [hpc2, hpc1, hpc]; exact hPl 2 _ rfl
  obtain ⟨s3, hs3, hpc3, _, h3keep, h3data⟩ := step_loadData16 (input := input) hf2 hwQ (by omega)
  have hf3 : linkedCode[s3.pc]? = some (.imm r7 ⟨1, by omega⟩) := by
    rw [hpc3, hpc2, hpc1, hpc]; exact hPl 3 _ rfl
  obtain ⟨s4, hs4, hpc4, h4r7, h4keep, h4data⟩ := step_imm16 (input := input) hf3 (by omega)
  have h4r15v : (reg s4 r15).val = prefixDenseInBase workCap := by
    rw [h4keep r15 (by decide), h3keep r15 (by decide)]; exact h2r15v
  have h4r7v : (reg s4 r7).val = 1 := by rw [h4r7]
  have hf4 : linkedCode[s4.pc]? = some (.add r15 r15 r7) := by
    rw [hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 4 _ rfl
  obtain ⟨s5, hs5, hpc5, h5r15, h5keep, h5data⟩ := step_add16 (input := input) hf4 (by omega)
  have h5r15v : (reg s5 r15).val = prefixDenseInBase workCap + 1 := by
    rw [h5r15, WordOps.add_no_wrap _ _ (by rw [h4r15v, h4r7v]; exact hFit), h4r15v, h4r7v]
  obtain ⟨wM, hwM, _⟩ : ∃ w, s5.data[(reg s5 r15).val]? = some w ∧ w.val = mReach := by
    rw [h5r15v, h5data, h4data, h3data, h2data, h1data]
    cases hm : s.data[prefixDenseInBase workCap + 1]? with
    | none => simp [hm] at hM
    | some w => exact ⟨w, rfl, by simpa [hm] using hM⟩
  have hf5 : linkedCode[s5.pc]? = some (.loadData r8 r15) := by
    rw [hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 5 _ rfl
  obtain ⟨s6, hs6, hpc6, _, h6keep, h6data⟩ := step_loadData16 (input := input) hf5 hwM (by omega)
  have h6r7v : (reg s6 r7).val = 1 := by rw [h6keep r7 (by decide), h5keep r7 (by decide)]; exact h4r7v
  have hf6 : linkedCode[s6.pc]? = some (.loadData r6 r7) := by
    rw [hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 6 _ rfl
  obtain ⟨s7, hs7, hpc7, _, _, _⟩ :=
    step_loadData16 (input := input) hf6
      (by rw [h6r7v, h6data, h5data, h4data, h3data, h2data, h1data]; exact hPtr1) (by omega)
  have hf7 : linkedCode[s7.pc]? = some .halt := by
    rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc]; exact hPl 7 _ rfl
  have hSteps7 : Steps linkedCode input 7 s s7 :=
    Steps.cons hs1 (Steps.cons hs2 (Steps.cons hs3 (Steps.cons hs4
      (Steps.cons hs5 (Steps.cons hs6 (Steps.cons hs7 (Steps.zero _)))))))
  exact ⟨s7, hSteps7, by rw [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2, hpc1, hpc], hf7⟩

private theorem build_denseSpec' {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    {g : Digraph} {r : Fin g.vertexCount}
    (order : List (Fin g.vertexCount)) (hTopo : g.IsTopologicalList order)
    (hCap : 64 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (s1 s12 : State (layout16 bits inputCap workCap hi hw))
    (h2Dsz : s12.data.size = workCap)
    (h2_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val =
      some (denseVertices g r order hTopo).length)
    (h2_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val =
      some (denseReachArcCount g (denseVertices g r order hTopo)))
    (h2_start : ∀ i ≤ (denseVertices g r order hTopo).length,
      (s12.data[prefixDenseInBase workCap + 2 + i]?).map Fin.val =
        some (denseInPrefix g (denseVertices g r order hTopo) i))
    (inSrc : Nat → Nat)
    (h2_src : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s12.data[prefixDenseInBase workCap + 3 + (denseVertices g r order hTopo).length + k]?).map Fin.val =
        some (inSrc k))
    (hQPos : 1 ≤ (denseVertices g r order hTopo).length)
    (hQLe : (denseVertices g r order hTopo).length ≤ g.vertexCount)
    (hmLe : denseReachArcCount g (denseVertices g r order hTopo) ≤ g.arcCount)
    (hHead : (denseVertices g r order hTopo)[0]'(denseVertices_length_pos g r order hTopo) = r)
    (hReach : ∀ i (hi₁ : i < (denseVertices g r order hTopo).length),
      g.InitiallyReachable r ((denseVertices g r order hTopo)[i]'hi₁))
    (hArcOrder : ∀ u v : Fin (denseVertices g r order hTopo).length,
      g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
        ((denseVertices g r order hTopo)[v.val]'v.isLt) → u.val < v.val)
    (hStartBounds : denseInPrefix g (denseVertices g r order hTopo) 0 = 0 ∧
      denseInPrefix g (denseVertices g r order hTopo) (denseVertices g r order hTopo).length =
        denseReachArcCount g (denseVertices g r order hTopo))
    (hSrcFin1 : ∀ (v : Fin (denseVertices g r order hTopo).length) (k : Nat),
      denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k →
      k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) →
      ∃ u : Fin (denseVertices g r order hTopo).length,
        (s1.data[inSrcBase g.vertexCount g.arcCount + k]?).map Fin.val = some u.val)
    (hDenseIff1 : ∀ u v : Fin (denseVertices g r order hTopo).length,
      g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
        ((denseVertices g r order hTopo)[v.val]'v.isLt) ↔
        ∃ k, denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k ∧
          k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) ∧
          (s1.data[inSrcBase g.vertexCount g.arcCount + k]?).map Fin.val = some u.val)
    (hSrcRead1 : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s1.data[7 * g.vertexCount + 1 + k]?).map Fin.val = some (inSrc k)) :
    let subL := prefixSubLayout bits workCap hw
    let subInput : Input subL :=
      ⟨Array.ofFn (fun j : Fin (prefixSubInCap workCap) =>
        s12.data[prefixDenseInBase workCap + j.val]'(by
          rw [h2Dsz]
          unfold prefixDenseInBase prefixSubInCap prefixQuarter
          omega)),
       Array.size_ofFn⟩
    (∀ j : Nat, j < prefixSubInCap workCap →
      s12.data[prefixDenseInBase workCap + j]? = subInput.words[j]?) ∧
    RamDomBuild.DenseIncomingSpec subInput (denseVertices g r order hTopo).length
      (denseReachArcCount g (denseVertices g r order hTopo))
      (denseInPrefix g (denseVertices g r order hTopo)) inSrc := by
  intro subL subInput
  have hQuarterGe : 16 * (g.vertexCount + g.arcCount + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hSubInRead : ∀ j : Nat, j < prefixSubInCap workCap →
      s12.data[prefixDenseInBase workCap + j]? = subInput.words[j]? := by
    intro j hj
    have hjDom : prefixDenseInBase workCap + j < s12.data.size := by
      rw [h2Dsz]; unfold prefixDenseInBase prefixSubInCap prefixQuarter at *; omega
    rw [Array.getElem?_eq_getElem hjDom]
    have hjSub : j < subInput.words.size := by simpa only [subInput.size_eq] using hj
    rw [Array.getElem?_eq_getElem hjSub]
    simp only [subInput, Array.getElem_ofFn]
  refine ⟨hSubInRead, hQPos, ?_, ?_, ?_, ?_, hStartBounds.1, hStartBounds.2, ?_, ?_, ?_, ?_, ?_⟩
  · change 3 + (denseVertices g r order hTopo).length +
      denseReachArcCount g (denseVertices g r order hTopo) ≤ prefixSubInCap workCap
    unfold prefixSubInCap prefixQuarter at *
    omega
  · change 5 * (denseVertices g r order hTopo).length + 10 ≤ prefixSubWorkCap workCap
    unfold prefixSubWorkCap prefixQuarter at *
    omega
  · rw [← hSubInRead 0 (by unfold prefixSubInCap prefixQuarter at *; omega)]; exact h2_d0
  · rw [← hSubInRead 1 (by unfold prefixSubInCap prefixQuarter at *; omega)]; exact h2_d1
  · intro v _
    exact denseInPrefix_mono g (denseVertices g r order hTopo) (Nat.le_succ v)
  · intro v hv1 hvQ
    obtain ⟨d0, hd0⟩ : ∃ x, x = (denseVertices g r order hTopo)[v]'hvQ := ⟨_, rfl⟩
    have hR := hReach v hvQ
    rw [← hd0] at hR
    rcases AvoidPath.eq_or_exists_last_arc hR with hEq | ⟨u, huReach, huArc⟩
    · exfalso
      have hNd := denseVertices_nodup g r order hTopo
      have hPair := (List.pairwise_iff_getElem.mp hNd) 0 v
        (denseVertices_length_pos g r order hTopo) hvQ hv1
      exact hPair (hHead.trans (hEq.trans hd0))
    · have huMem : u ∈ denseVertices g r order hTopo :=
        (denseVertices_mem_iff g r order hTopo u).mpr huReach
      obtain ⟨ui, huiLt, huiEq⟩ := List.mem_iff_getElem.mp huMem
      have hArcD : g.HasArc ((denseVertices g r order hTopo)[ui]'huiLt)
          ((denseVertices g r order hTopo)[v]'hvQ) := by
        simpa only [huiEq, ← hd0] using huArc
      obtain ⟨pos, hpLo, hpHi, _⟩ := (hDenseIff1 ⟨ui, huiLt⟩ ⟨v, hvQ⟩).mp hArcD
      dsimp only at hpLo hpHi
      omega
  · intro v k hv1 hvQ hkLo hkHi
    obtain ⟨u, hu⟩ := hSrcFin1 ⟨v, hvQ⟩ k hkLo hkHi
    have hkLt : k < denseReachArcCount g (denseVertices g r order hTopo) :=
      Nat.lt_of_lt_of_le hkHi (by
        rw [← hStartBounds.2]
        exact denseInPrefix_mono g (denseVertices g r order hTopo) (Nat.succ_le_of_lt hvQ))
    have hRead := hSrcRead1 k hkLt
    have hu' : (s1.data[7 * g.vertexCount + 1 + k]?).map Fin.val = some u.val := by
      simpa only [inSrcBase_eq] using hu
    have hInSrcK : inSrc k = u.val := Option.some.inj (hRead.symm.trans hu')
    have hArcD : g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
        ((denseVertices g r order hTopo)[v]'hvQ) :=
      (hDenseIff1 u ⟨v, hvQ⟩).mpr ⟨k, hkLo, hkHi, hu⟩
    rw [hInSrcK]
    exact hArcOrder u ⟨v, hvQ⟩ hArcD
  · intro i hi
    rw [← hSubInRead (2 + i) (by unfold prefixSubInCap prefixQuarter at *; omega)]
    simpa only [Nat.add_assoc] using h2_start i hi
  · intro k hk
    rw [← hSubInRead (3 + (denseVertices g r order hTopo).length + k)
      (by unfold prefixSubInCap prefixQuarter at *; omega)]
    simpa only [Nat.add_assoc] using h2_src k hk

private theorem run_phase3_lift_epilogue_steps' {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {Q mReach : Nat}
    (s12 : State (layout16 bits inputCap workCap hi hw))
    (h12_0 : s12.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩)
    (h12_1 : s12.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩)
    (h12_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val = some Q)
    (h12_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach)
    (hDenseFit : prefixDenseInBase workCap + 1 < 2 ^ bits)
    (subInput : Input (prefixSubLayout bits workCap hw))
    (subCode : Program (prefixSubLayout bits workCap hw))
    (right : Program (layout16 bits inputCap workCap hi hw))
    (subS0 tSub : State (prefixSubLayout bits workCap hw))
    (work3 : Nat)
    (hRun3 : run subCode subInput work3 (Phase.initial subS0) = some ⟨tSub, work3⟩)
    (hCfg3 : RamDataSliceAdapter.SliceConfig (prefixSubLayout bits workCap hw)
      (layout16 bits inputCap workCap hi hw)
      ⟨0, by omega⟩ ⟨1, by omega⟩ (prefixDenseInBase workCap) (prefixTreeBase workCap)
      subInput (Phase.initial s12).data)
    (hBody3 : RamDataSliceAdapter.BodyRelocated
      (bigL := layout16 bits inputCap workCap hi hw) rfl
      ⟨0, by omega⟩ ⟨1, by omega⟩ subCode right 0)
    (hPlEp : Placed right (4 * subCode.size)
      (epilogueCode (inputCap := inputCap) (workCap := workCap) (hi := hi) (hw := hw) hTen).toList)
    (hRightSz : right.size = 4 * subCode.size + 8)
    (hSim3 : RamDataSliceAdapter.SliceSim (subL := prefixSubLayout bits workCap hw)
      (bigL := layout16 bits inputCap workCap hi hw) rfl rfl (prefixTreeBase workCap) 0
      (Phase.initial s12).data (Phase.initial subS0) (Phase.initial s12))
    (hTreeGt1 : 1 < prefixTreeBase workCap)
    (hSubDenseLo : prefixTreeBase workCap + prefixSubWorkCap workCap ≤ prefixDenseInBase workCap) :
    ∃ (sEndRight : State (layout16 bits inputCap workCap hi hw)) (m3 : Nat),
      Steps right input (m3 + 7) (Phase.initial s12) sEndRight ∧
      sEndRight.pc = right.size - 1 := by
  have hExitLt3 : 0 + 4 * subCode.size < right.size := by omega
  obtain ⟨m3, sMid3, _, hSteps3, hpcMid3, _, _, hMid3Frame⟩ :=
    RamDataSliceAdapter.liftProgram_relocated_steps
      (subL := prefixSubLayout bits workCap hw)
      (bigL := layout16 bits inputCap workCap hi hw) rfl rfl subCode subInput right input
      ⟨0, by omega⟩ ⟨1, by omega⟩ (prefixDenseInBase workCap) (prefixTreeBase workCap) 0
      work3 (Phase.initial subS0) ⟨tSub, work3⟩ (Phase.initial s12)
      hRun3 hCfg3 hBody3 hExitLt3 hSim3
  have hMid3_0 : sMid3.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩ := by
    rw [hMid3Frame 0 (Or.inl (by omega))]; exact h12_0
  have hMid3_1 : sMid3.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩ := by
    rw [hMid3Frame 1 (Or.inl hTreeGt1)]; exact h12_1
  have hMid3_d0 : (sMid3.data[prefixDenseInBase workCap]?).map Fin.val = some Q := by
    rw [hMid3Frame (prefixDenseInBase workCap) (Or.inr (by dsimp only [prefixSubLayout]; exact hSubDenseLo))]
    exact h12_d0
  have hMid3_d1 : (sMid3.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach := by
    rw [hMid3Frame (prefixDenseInBase workCap + 1) (Or.inr (by dsimp only [prefixSubLayout]; omega))]
    exact h12_d1
  obtain ⟨sEndRight, hStepsEp, hEpPc, _⟩ :=
    run_epilogue_steps (4 * subCode.size) Q mReach hPlEp (by omega)
      sMid3 (by simpa only [Nat.zero_add] using hpcMid3)
      hMid3_0 hMid3_1 hMid3_d0 hMid3_d1 hDenseFit
  refine ⟨sEndRight, m3, hSteps3.append hStepsEp, ?_⟩
  rw [hEpPc, hRightSz]
  omega

private theorem run_phase3_and_epilogue_steps' {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits} {hTen : 10 ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {n m Q mReach : Nat}
    (_hnPos : 1 ≤ n) (hQPos : 1 ≤ Q) (hQLe : Q ≤ n) (_hmLe : mReach ≤ m)
    (hCap : 64 * (n + m + 1) ≤ workCap)
    {inStart inSrc : Nat → Nat}
    (s12 : State (layout16 bits inputCap workCap hi hw))
    (h12Dsz : s12.data.size = workCap)
    (h12_0 : s12.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩)
    (h12_1 : s12.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩)
    (h12_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val = some Q)
    (h12_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val = some mReach)
    (subInput : Input (prefixSubLayout bits workCap hw))
    (hSubInRead : ∀ j : Nat, j < prefixSubInCap workCap →
      s12.data[prefixDenseInBase workCap + j]? = subInput.words[j]?)
    (hSp : RamDomBuild.DenseIncomingSpec subInput Q mReach inStart inSrc) :
    let right := prefixRightCode (hi := hi) hw hTen
    ∃ (sEndRight : State (layout16 bits inputCap workCap hi hw)) (m3 : Nat),
      Steps right input (m3 + 7) (Phase.initial s12) sEndRight ∧
      sEndRight.pc = right.size - 1 := by
  intro right
  have hQuarterGe : 16 * (n + m + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  let subL := prefixSubLayout bits workCap hw
  let subCode := RamDomAndStaticTree.domAndStaticTreeProgram
    (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) hTen
  let subS0 : State subL :=
    { regs := Array.ofFn fun i : Fin 15 =>
        s12.regs[i.val]'(by rw [s12.regs_size]; exact Nat.lt_succ_of_lt i.isLt)
      data := Array.ofFn fun j : Fin (prefixSubWorkCap workCap) =>
        s12.data[prefixTreeBase workCap + j.val]'(by
          rw [h12Dsz]; unfold prefixTreeBase prefixSubWorkCap prefixQuarter; omega)
      pc := 0
      regs_size := Array.size_ofFn
      data_size := Array.size_ofFn }
  have hSubDataCap : 17 * Q ≤ prefixSubWorkCap workCap := by
    unfold prefixSubWorkCap; omega
  have hSubWordCap : 17 * Q < 2 ^ bits := by
    have : 17 * Q ≤ 2 * prefixQuarter workCap := hSubDataCap
    unfold prefixQuarter at this
    omega
  obtain ⟨tSub, _, work3, _, _, _, hRun3, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ :=
    RamDomAndStaticTree.run_domAndStaticTree (input := subInput) hSp hSubDataCap hSubWordCap subS0
  have hCfg3 : RamDataSliceAdapter.SliceConfig subL (layout16 bits inputCap workCap hi hw)
      ⟨0, by omega⟩ ⟨1, by omega⟩ (prefixDenseInBase workCap) (prefixTreeBase workCap)
      subInput (Phase.initial s12).data := by
    refine ⟨three_quarter_lt_pow2 hw hTen, quarter_lt_pow2 hw hTen, ?_, ?_, ?_, ?_,
      h12_0, h12_1, Or.inl ?_, Or.inl ?_, Or.inr ?_, hSubInRead⟩
    · change 0 < workCap; omega
    · change 1 < workCap; omega
    · change prefixDenseInBase workCap + prefixSubInCap workCap ≤ workCap
      unfold prefixDenseInBase prefixSubInCap prefixQuarter; omega
    · change prefixTreeBase workCap + prefixSubWorkCap workCap ≤ workCap
      unfold prefixTreeBase prefixSubWorkCap prefixQuarter; omega
    · change 0 < prefixTreeBase workCap
      unfold prefixTreeBase prefixQuarter at *; omega
    · change 1 < prefixTreeBase workCap
      unfold prefixTreeBase prefixQuarter at *; omega
    · change prefixTreeBase workCap + prefixSubWorkCap workCap ≤ prefixDenseInBase workCap
      unfold prefixTreeBase prefixSubWorkCap prefixDenseInBase prefixQuarter; omega
  have hSim3 : RamDataSliceAdapter.SliceSim (subL := subL)
      (bigL := layout16 bits inputCap workCap hi hw) rfl rfl (prefixTreeBase workCap) 0
      (Phase.initial s12).data (Phase.initial subS0) (Phase.initial s12) := by
    refine ⟨rfl, ?_, ?_, fun _ _ => rfl⟩
    · intro i
      have hi16 : i.val < (Phase.initial s12).regs.size := by
        rw [(Phase.initial s12).regs_size]; exact Nat.lt_succ_of_lt i.isLt
      have hi15 : i.val < (Phase.initial subS0).regs.size := by
        rw [(Phase.initial subS0).regs_size]; exact i.isLt
      rw [Array.getElem?_eq_getElem hi16, Array.getElem?_eq_getElem hi15]
      simp only [Phase.initial, subS0, Array.getElem_ofFn]
    · intro j hj
      have hjWork : prefixTreeBase workCap + j < (Phase.initial s12).data.size := by
        rw [Phase.initial_data, h12Dsz]
        dsimp only [subL, prefixSubLayout] at hj
        unfold prefixTreeBase prefixSubWorkCap prefixQuarter at *; omega
      have hjSub : j < (Phase.initial subS0).data.size := by
        simpa only [Phase.initial_data, subS0.data_size] using hj
      rw [Array.getElem?_eq_getElem hjWork, Array.getElem?_eq_getElem hjSub]
      simp only [Phase.initial, subS0, Array.getElem_ofFn]
  have hBody3 := prefixRightCode_bodyRelocated (hi := hi) hw hTen
  have hRightSz : right.size = 4 * subCode.size + 8 :=
    prefixRightCode_size (hi := hi) hw hTen
  have hTenSubEq :
      RamDomAndStaticTree.domAndStaticTreeProgram
        (prefixSubInCap_le hw) (prefixSubWorkCap_le hw) (by have := hSp.qPos; omega) = subCode :=
    congrArg (RamDomAndStaticTree.domAndStaticTreeProgram
      (prefixSubInCap_le hw) (prefixSubWorkCap_le hw)) (Subsingleton.elim _ hTen)
  have hRun3' : run subCode subInput work3 (Phase.initial subS0) = some ⟨tSub, work3⟩ := by
    rw [← hTenSubEq]; exact hRun3
  exact run_phase3_lift_epilogue_steps' input s12 h12_0 h12_1 h12_d0 h12_d1
    (by unfold prefixDenseInBase prefixQuarter; omega)
    subInput subCode right subS0 tSub work3 hRun3' hCfg3 hBody3
    (prefixRightCode_epilogue_placed (hi := hi) hw hTen) hRightSz hSim3
    (by unfold prefixTreeBase prefixQuarter at *; omega)
    (by unfold prefixTreeBase prefixSubWorkCap prefixDenseInBase prefixQuarter; omega)

private theorem hTenOfCap {n m workCap bits : Nat} (hn : 1 ≤ n)
    (hCap : 64 * (n + m + 1) ≤ workCap) (hw : workCap ≤ 2 ^ bits) : 10 ≤ 2 ^ bits :=
  Nat.le_trans
    (Nat.le_trans (by decide : 10 ≤ 64 * 1)
      (Nat.mul_le_mul_left 64 (Nat.le_trans hn (Nat.le_trans (Nat.le_add_right n m) (Nat.le_succ _)))))
    (Nat.le_trans hCap hw)

private theorem buildPrefixProgram_code_eq {bits inputCap workCap : Nat}
    (hi : inputCap ≤ 2 ^ bits) (hw : workCap ≤ 2 ^ bits) (hTen : 10 ≤ 2 ^ bits) :
    buildPrefixProgram hi hw hTen =
      join (buildPrefixPhase12 hi hw hTen).code (prefixRightCode (hi := hi) hw hTen)
        (buildPrefixPhase12 hi hw hTen).haltPC (buildPrefixPhase12 hi hw hTen).haltFits := rfl

private theorem buildPrefixProgram_halts_at_last {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (hCap : 64 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (s₀ : State (layout16 bits inputCap workCap hi hw)) :
    let hTen : 10 ≤ 2 ^ bits := hTenOfCap (Fin.pos r) hCap hw
    let code := buildPrefixProgram hi hw hTen
    ∃ (k : Nat) (last : State (layout16 bits inputCap workCap hi hw)),
      Steps code input k (Phase.initial s₀) last ∧
      last.pc = code.size - 1 := by
  intro hTen code
  have hnPos : 1 ≤ g.vertexCount := Fin.pos r
  have h5 : 5 ≤ 2 ^ bits := by omega
  have hWorkRoom : rawDagWorkCap g.vertexCount g.arcCount ≤ workCap := by
    unfold rawDagWorkCap; omega
  obtain ⟨s1, _, steps1, order, _, hTopo, _, hRun1, _, _, hConst1, hr5_1, hr6_1,
      hQPos, hQLe, hmLe, hHead, _, _, _, hReach, _, _, _,
      hArcOrder, hStart1, hStartBounds, _, hSrcFin1, _, hDenseIff1⟩ :=
    run_dag_reach_kahn input raw acyc hWorkRoom s₀
  let inSrc : Nat → Nat := fun k => ((s1.data[inSrcBase g.vertexCount g.arcCount + k]?).map Fin.val).getD 0
  have hSrcRead1 : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s1.data[7 * g.vertexCount + 1 + k]?).map Fin.val = some (inSrc k) := by
    intro k hk
    have hIn : ∃ v : Fin (denseVertices g r order hTopo).length,
        denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k ∧
        k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) := by
      have aux : ∀ bound : Nat, bound ≤ (denseVertices g r order hTopo).length →
          k < denseInPrefix g (denseVertices g r order hTopo) bound →
          ∃ v : Fin (denseVertices g r order hTopo).length,
            denseInPrefix g (denseVertices g r order hTopo) v.val ≤ k ∧
            k < denseInPrefix g (denseVertices g r order hTopo) (v.val + 1) := by
        intro bound
        induction bound with
        | zero => intro _ h0; rw [hStartBounds.1] at h0; omega
        | succ b ih =>
          intro hb hSb
          by_cases hkPrev : k < denseInPrefix g (denseVertices g r order hTopo) b
          · exact ih (by omega) hkPrev
          · exact ⟨⟨b, by omega⟩, Nat.not_lt.mp hkPrev, hSb⟩
      exact aux (denseVertices g r order hTopo).length (Nat.le_refl _) (by rw [hStartBounds.2]; exact hk)
    obtain ⟨v, hvLo, hvHi⟩ := hIn
    obtain ⟨u, hu⟩ := hSrcFin1 v k hvLo hvHi
    dsimp only [inSrc]
    rw [inSrcBase_eq] at hu ⊢
    rw [hu]
    rfl
  obtain ⟨s2, steps2, _, hRun2, h2Dsz, h2_0, h2_1, h2_d0, h2_d1, h2_start, h2_src, _⟩ :=
    run_copyDenseIn input hnPos hQPos hQLe hmLe hCap
      (denseInPrefix g (denseVertices g r order hTopo)) inSrc s1 hConst1 hr5_1 hr6_1
      (fun i hi => by simpa [inStartBase] using hStart1 i hi) hSrcRead1
  have hRun1' : run (dagReachKahnPhase h5).code input steps1 (Phase.initial s₀) = some ⟨s1, steps1⟩ := by
    rw [dagReachKahnPhase_code]; exact hRun1
  obtain ⟨s12, _, _, h12Data, hRun12, _, _⟩ :=
    run_linked_pair (dagReachKahnPhase h5) (copyDenseInPhase hw hTen).code
      (by rw [copyDenseInPhase_code]; simp [copyDenseInCode]) hRun1' hRun2
  have h12Dsz : s12.data.size = workCap := by rw [h12Data, h2Dsz]
  have h12_0 : s12.data[0]? = some ⟨prefixDenseInBase workCap, three_quarter_lt_pow2 hw hTen⟩ := by
    rw [h12Data]; exact h2_0
  have h12_1 : s12.data[1]? = some ⟨prefixTreeBase workCap, quarter_lt_pow2 hw hTen⟩ := by
    rw [h12Data]; exact h2_1
  have h12_d0 : (s12.data[prefixDenseInBase workCap]?).map Fin.val =
      some (denseVertices g r order hTopo).length := by
    rw [h12Data]; exact h2_d0
  have h12_d1 : (s12.data[prefixDenseInBase workCap + 1]?).map Fin.val =
      some (denseReachArcCount g (denseVertices g r order hTopo)) := by
    rw [h12Data]; exact h2_d1
  have h12_start : ∀ i ≤ (denseVertices g r order hTopo).length,
      (s12.data[prefixDenseInBase workCap + 2 + i]?).map Fin.val =
        some (denseInPrefix g (denseVertices g r order hTopo) i) := by
    intro i hi; rw [h12Data]; exact h2_start i hi
  have h12_src : ∀ k < denseReachArcCount g (denseVertices g r order hTopo),
      (s12.data[prefixDenseInBase workCap + 3 + (denseVertices g r order hTopo).length + k]?).map Fin.val =
        some (inSrc k) := by
    intro k hk; rw [h12Data]; exact h2_src k hk
  obtain ⟨hSubInRead, hSp⟩ := build_denseSpec' (hi := hi) (hw := hw) order hTopo hCap
    s1 s12 h12Dsz h12_d0 h12_d1 h12_start inSrc h12_src
    hQPos hQLe hmLe hHead hReach hArcOrder hStartBounds hSrcFin1 hDenseIff1 hSrcRead1
  obtain ⟨sEndRight, m3, hStepsRight, hEndPcRight⟩ :=
    run_phase3_and_epilogue_steps' input hnPos hQPos hQLe hmLe hCap s12 h12Dsz
      h12_0 h12_1 h12_d0 h12_d1 _ hSubInRead hSp
  let p12 := buildPrefixPhase12 hi hw hTen
  let right := prefixRightCode (hi := hi) hw hTen
  have hCodeEq : code = join p12.code right p12.haltPC p12.haltFits :=
    buildPrefixProgram_code_eq hi hw hTen
  have hJmp12 : Steps code input (steps1 + steps2) (Phase.initial s₀) { s12 with pc := p12.code.size } := by
    have src : relocateStatePC 0 (Phase.initial s₀) = Phase.initial s₀ := rfl
    have link := linked_return_of_run_multi (linked := code) (base := 0)
      (ret := fun _ => p12.code.size) hRun12
      (fun i op h nonhalt => by
        rw [hCodeEq]
        have neq : i ≠ p12.haltPC := fun e => nonhalt
          (Option.some.inj (h.symm.trans (e.symm ▸ p12.haltAt)))
        have same : relocateInstr 0 op = op := by cases op <;> simp only [relocateInstr, Nat.zero_add]
        have hf := fetch_left p12.code right p12.haltFits neq h
        rw [Nat.zero_add, same]
        exact hf)
      (fun i h => by
        rw [hCodeEq]
        rw [p12.uniqueHalt i h, Nat.zero_add]
        have patched := fetch_halt p12.code right p12.haltFits
        exact ⟨patched.1, patched.2 (prefixRightCode_pos (hi := hi) hw hTen)⟩)
    rwa [src] at link
  have placed := relocated_right p12.code right p12.haltFits
  have after := hStepsRight.relocate placed
  have sameEntry : relocateStatePC p12.code.size (Phase.initial s12) = { s12 with pc := p12.code.size } := by
    simp only [relocateStatePC, Phase.initial, Nat.add_zero]
  rw [sameEntry] at after
  rw [← hCodeEq] at after
  have hSzCode : code.size = p12.code.size + right.size := by
    rw [hCodeEq]
    unfold join
    rw [Array.size_append, Array.size_set, Array.size_map]
  have hRightPos : 0 < right.size := prefixRightCode_pos (hi := hi) hw hTen
  refine ⟨steps1 + steps2 + (m3 + 7), relocateStatePC p12.code.size sEndRight,
    hJmp12.append after, ?_⟩
  change p12.code.size + sEndRight.pc = code.size - 1
  change sEndRight.pc = right.size - 1 at hEndPcRight
  rw [hEndPcRight, hSzCode]
  omega

end PrefixStepsAtLast

section StaticTreeBridge

private theorem avoidPath_mono {V : Type} {edge : V → V → Prop}
    {f₁ f₂ : V → Prop} (hsub : ∀ z, f₂ z → f₁ z) {u v : V}
    (p : AvoidPath edge f₁ u v) : AvoidPath edge f₂ u v := by
  induction p with
  | refl u hal => exact AvoidPath.refl u (fun h => hal (hsub u h))
  | step u w v hal harc _ ih => exact AvoidPath.step u w v (fun h => hal (hsub u h)) harc ih

private theorem denseDigraph_survivingPath_to_g
    {g : Digraph} {Q : Nat} {dense : List (Fin g.vertexCount)}
    (hlen : Q = dense.length) {inStart inSrc : Nat → Nat}
    (hArc : ∀ u v : Fin Q,
      (RamDomBuild.denseDigraph Q inStart inSrc).HasArc u v ↔
        g.HasArc (dense[u.val]'(hlen ▸ u.isLt)) (dense[v.val]'(hlen ▸ v.isLt)))
    {failed : Fin g.vertexCount → Prop} {a b : Fin Q}
    (p : (RamDomBuild.denseDigraph Q inStart inSrc).SurvivingPath
      (fun z => failed (dense[z.val]'(hlen ▸ z.isLt))) a b) :
    g.SurvivingPath failed (dense[a.val]'(hlen ▸ a.isLt)) (dense[b.val]'(hlen ▸ b.isLt)) := by
  induction p with
  | refl u hal => exact AvoidPath.refl _ hal
  | step u w _ hal harc _ ih =>
    exact AvoidPath.step _ _ _ hal ((hArc u w).mp harc) ih

private theorem g_survivingPath_to_denseDigraph
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hTopo : g.IsTopologicalList order}
    {inStart inSrc : Nat → Nat}
    (hArc : ∀ u v : Fin (denseVertices g r order hTopo).length,
      (RamDomBuild.denseDigraph (denseVertices g r order hTopo).length inStart inSrc).HasArc u v ↔
        g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
          ((denseVertices g r order hTopo)[v.val]'v.isLt))
    (hReach : ∀ i (hi : i < (denseVertices g r order hTopo).length),
      g.InitiallyReachable r ((denseVertices g r order hTopo)[i]'hi))
    {failed : Fin g.vertexCount → Prop} {u v : Fin g.vertexCount}
    (p : g.SurvivingPath failed u v) :
    ∀ a : Fin (denseVertices g r order hTopo).length,
      (denseVertices g r order hTopo)[a.val]'a.isLt = u →
      ∃ b : Fin (denseVertices g r order hTopo).length,
        (denseVertices g r order hTopo)[b.val]'b.isLt = v ∧
        (RamDomBuild.denseDigraph (denseVertices g r order hTopo).length inStart inSrc).SurvivingPath
          (fun z => failed ((denseVertices g r order hTopo)[z.val]'z.isLt)) a b := by
  induction p with
  | refl x hal =>
    intro a ha
    refine ⟨a, ha, AvoidPath.refl a (by
      change ¬ failed ((denseVertices g r order hTopo)[a.val]'a.isLt)
      rw [ha]; exact hal)⟩
  | step x w y hal harc _ ih =>
    intro a ha
    have hwReach : g.InitiallyReachable r w :=
      Digraph.initiallyReachable_extend (ha ▸ hReach a.val a.isLt) harc
    have hwMem : w ∈ denseVertices g r order hTopo :=
      (denseVertices_mem_iff g r order hTopo w).mpr hwReach
    obtain ⟨wi, hwiLt, hwiEq⟩ := List.mem_iff_getElem.mp hwMem
    let aw : Fin (denseVertices g r order hTopo).length := ⟨wi, hwiLt⟩
    obtain ⟨b, hbEq, hRest⟩ := ih aw hwiEq
    have hArcD : (RamDomBuild.denseDigraph (denseVertices g r order hTopo).length inStart inSrc).HasArc a aw :=
      (hArc a aw).mpr (by dsimp only [aw]; rw [ha, hwiEq]; exact harc)
    exact ⟨b, hbEq, AvoidPath.step a aw b (by
      change ¬ failed ((denseVertices g r order hTopo)[a.val]'a.isLt)
      rw [ha]; exact hal) hArcD hRest⟩

private theorem fin_surjective_of_injective {Q : Nat} (f : Fin Q → Fin Q)
    (hinj : ∀ a b : Fin Q, f a = f b → a = b) (k : Fin Q) :
    ∃ v : Fin Q, f v = k := by
  refine Classical.byContradiction fun hNo => ?_
  let img := (List.finRange Q).map f
  have hNdImg : img.Nodup :=
    List.Pairwise.map f (fun _ _ hne he => hne (hinj _ _ he)) (List.nodup_finRange Q)
  have hKNotMem : k ∉ img := by
    intro hm
    obtain ⟨v, _, hv⟩ := List.mem_map.mp hm
    exact hNo ⟨v, hv⟩
  have hNdCons : (k :: img).Nodup := List.nodup_cons.mpr ⟨hKNotMem, hNdImg⟩
  have hLe := hNdCons.length_le_of_subset (fun z _ => List.mem_finRange z)
  simp only [img, List.length_cons, List.length_map, List.length_finRange] at hLe
  exact Nat.not_succ_le_self Q hLe

private theorem ancestor_iff_isForestAncestor {n : Nat} (parent : Fin n → Fin n) (a v : Fin n) :
    Digraph.Ancestor parent a v ↔ LabelledQuotient.IsForestAncestor parent a v := by
  constructor
  · intro h
    induction h with
    | refl => exact LabelledQuotient.IsForestAncestor.refl
    | step w _ ih => exact LabelledQuotient.IsForestAncestor.step w ih
  · intro h
    induction h with
    | refl => exact Digraph.Ancestor.refl
    | step w _ ih => exact Digraph.Ancestor.step w ih

private def staticTreeSlice_of_prefix {bits : Nat}
    (mem : Array (Word bits)) (treeBase : Nat)
    {g : Digraph} {r : Fin g.vertexCount} (acyc : g.IsAcyclic)
    {order : List (Fin g.vertexCount)} {hTopo : g.IsTopologicalList order}
    (hFit : treeBase + staticTreeWords (denseVertices g r order hTopo).length ≤ mem.size)
    {inStart inSrc : Nat → Nat}
    {parent : Fin (denseVertices g r order hTopo).length → Fin (denseVertices g r order hTopo).length}
    {depth : Fin (denseVertices g r order hTopo).length → Nat}
    (hQPos : 1 ≤ (denseVertices g r order hTopo).length)
    (hDense0 : (denseVertices g r order hTopo)[0]'(denseVertices_length_pos g r order hTopo) = r)
    (hDenseReach : ∀ i (hi : i < (denseVertices g r order hTopo).length),
      g.InitiallyReachable r ((denseVertices g r order hTopo)[i]'hi))
    (hDenseDigraph : ∀ u v : Fin (denseVertices g r order hTopo).length,
      (RamDomBuild.denseDigraph (denseVertices g r order hTopo).length inStart inSrc).HasArc u v ↔
        g.HasArc ((denseVertices g r order hTopo)[u.val]'u.isLt)
          ((denseVertices g r order hTopo)[v.val]'v.isLt))
    (hParSpec : ParentSpec
      (RamDomBuild.denseDigraph (denseVertices g r order hTopo).length inStart inSrc) ⟨0, hQPos⟩ parent)
    (hTree : ValidDepthTree ⟨0, hQPos⟩ parent depth)
    (hParLt : ∀ v : Fin (denseVertices g r order hTopo).length, 1 ≤ v.val → (parent v).val < v.val)
    (hMemPar : ∀ v : Fin (denseVertices g r order hTopo).length,
      (mem[treeBase + v.val]?).map Fin.val = some (parent v).val)
    (hMemDep : ∀ v : Fin (denseVertices g r order hTopo).length,
      (mem[treeBase + (denseVertices g r order hTopo).length + v.val]?).map Fin.val = some (depth v))
    (hMemHeavy : ∀ u : Fin (denseVertices g r order hTopo).length,
      (mem[treeBase + 2 * (denseVertices g r order hTopo).length + u.val]?).map Fin.val =
        some (match (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed.heavy.read u with
          | none => (denseVertices g r order hTopo).length
          | some h => h.val))
    (hMemHead : ∀ v : Fin (denseVertices g r order hTopo).length,
      (mem[treeBase + 3 * (denseVertices g r order hTopo).length + v.val]?).map Fin.val =
        some ((StaticHeadSweep.tables (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed).head v).val)
    (hMemEnt : ∀ v : Fin (denseVertices g r order hTopo).length,
      (mem[treeBase + 4 * (denseVertices g r order hTopo).length + v.val]?).map Fin.val =
        some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v))
    (hMemStop : ∀ v : Fin (denseVertices g r order hTopo).length,
      (mem[treeBase + 5 * (denseVertices g r order hTopo).length + v.val]?).map Fin.val =
        some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v))
    (hMemDofE : ∀ v : Fin (denseVertices g r order hTopo).length,
      (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v <
        (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v ∧
      (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v ≤
        (denseVertices g r order hTopo).length ∧
      (mem[treeBase + 6 * (denseVertices g r order hTopo).length +
        (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v]?).map Fin.val =
        some v.val)
    (hMemCsr0 : (mem[treeBase + 7 * (denseVertices g r order hTopo).length]?).map Fin.val = some 0)
    (hMemCsrLast : (mem[treeBase + 8 * (denseVertices g r order hTopo).length]?).map Fin.val =
      some ((denseVertices g r order hTopo).length - 1))
    (hMemBuckets : ∀ u : Fin (denseVertices g r order hTopo).length,
      ∃ lo hi : Nat,
        (mem[treeBase + 7 * (denseVertices g r order hTopo).length + u.val]?).map Fin.val = some lo ∧
        (mem[treeBase + 7 * (denseVertices g r order hTopo).length + u.val + 1]?).map Fin.val = some hi ∧
        hi = lo + (bucketChildren ⟨0, hQPos⟩ parent u).length ∧
        hi ≤ (denseVertices g r order hTopo).length - 1 ∧
        (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, hQPos⟩ parent u).length,
          let c := (bucketChildren ⟨0, hQPos⟩ parent u)[j]'hj
          (mem[treeBase + 10 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val = some c.val ∧
          (mem[treeBase + 8 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val =
            some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read c) ∧
          (mem[treeBase + 9 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val =
            some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read c)) ∧
        (∀ i j : Nat, i < j → j < hi - lo →
          ∃ ei ej : Nat,
            (mem[treeBase + 8 * (denseVertices g r order hTopo).length + 1 + lo + i]?).map Fin.val = some ei ∧
            (mem[treeBase + 8 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val = some ej ∧
            ei < ej)) :
    StaticTreeSlice mem treeBase g r (denseVertices g r order hTopo) := by
  let dense := denseVertices g r order hTopo
  let Q := dense.length
  let x := RamDomAndStaticTree.staticInput hQPos parent depth
  let built := PackedStaticLayout.build x
  let tables := StaticHeadSweep.tables built.packed
  let entryFin : Fin Q → Fin Q := fun v =>
    ⟨built.endpoints.entry.read v, Nat.lt_of_lt_of_le (hMemDofE v).1 (hMemDofE v).2.1⟩
  have hEntryInj : ∀ a b : Fin Q, entryFin a = entryFin b → a = b := by
    intro a b hab
    have hEqVal : built.endpoints.entry.read a = built.endpoints.entry.read b :=
      congrArg Fin.val hab
    have ha := (hMemDofE a).2.2
    have hb := (hMemDofE b).2.2
    rw [hEqVal] at ha
    have hSome : some a.val = some b.val := ha.symm.trans hb
    exact Fin.ext (Option.some.inj hSome)
  let denseOfEntryFn : Fin Q → Fin Q := fun k =>
    ((List.finRange Q).find? (fun v => decide (built.endpoints.entry.read v = k.val))).getD ⟨0, hQPos⟩
  have hDenseOfEntry_entry : ∀ v : Fin Q, ∀ hv : built.endpoints.entry.read v < Q,
      denseOfEntryFn ⟨built.endpoints.entry.read v, hv⟩ = v := by
    intro v hv
    have hFind : (List.finRange Q).find? (fun w => decide (built.endpoints.entry.read w = built.endpoints.entry.read v)) = some v := by
      have hAux : ∀ xs : List (Fin Q), xs.Nodup → v ∈ xs →
          (∀ w ∈ xs, built.endpoints.entry.read w = built.endpoints.entry.read v → w = v) →
          xs.find? (fun w => decide (built.endpoints.entry.read w = built.endpoints.entry.read v)) = some v := by
        intro xs hnd hmem huniq
        induction xs with
        | nil => cases hmem
        | cons y ys ih =>
          simp only [List.find?]
          by_cases hy : built.endpoints.entry.read y = built.endpoints.entry.read v
          · have hyv : y = v := huniq y List.mem_cons_self hy
            simp [hy]
            exact hyv
          · have hFalse : decide (built.endpoints.entry.read y = built.endpoints.entry.read v) = false :=
              decide_eq_false hy
            rw [hFalse]
            dsimp only
            have hvYs : v ∈ ys := by
              rcases List.mem_cons.mp hmem with rfl | hm
              · exact False.elim (hy rfl)
              · exact hm
            exact ih (List.nodup_cons.mp hnd).2 hvYs (fun w hw => huniq w (List.mem_cons.mpr (Or.inr hw)))
      exact hAux (List.finRange Q) (List.nodup_finRange Q) (List.mem_finRange v)
        (fun w _ hwe => hEntryInj w v (Fin.ext hwe))
    simp only [denseOfEntryFn, hFind, Option.getD_some]
  have hDenseOfEntry_mem : ∀ k : Fin Q,
      (mem[treeBase + 6 * Q + k.val]?).map Fin.val = some (denseOfEntryFn k).val := by
    intro k
    obtain ⟨v, hv⟩ := fin_surjective_of_injective entryFin hEntryInj k
    have hvLt : built.endpoints.entry.read v < Q :=
      Nat.lt_of_lt_of_le (hMemDofE v).1 (hMemDofE v).2.1
    have hKVal : k.val = built.endpoints.entry.read v := congrArg Fin.val hv.symm
    have hDns : denseOfEntryFn k = v := by
      rw [← hv]
      exact hDenseOfEntry_entry v hvLt
    rw [hDns, hKVal]
    exact (hMemDofE v).2.2
  let childStartFn : Nat → Nat := fun d =>
    if _ : d < Q then ((mem[treeBase + 7 * Q + d]?).map Fin.val).getD 0 else Q - 1
  have hChildStart_mem : ∀ d : Nat, d ≤ Q →
      (mem[treeBase + 7 * Q + d]?).map Fin.val = some (childStartFn d) := by
    intro d hd
    by_cases hlt : d < Q
    · obtain ⟨lo, _, hLo, _, _, _, _, _⟩ := hMemBuckets ⟨d, hlt⟩
      have hVal : childStartFn d = lo := by
        dsimp only [childStartFn]
        rw [dite_eq_left hlt, hLo]
        rfl
      rw [hVal]
      exact hLo
    · have hdQ : d = Q := by omega
      subst hdQ
      have hNot : ¬ Q < Q := Nat.lt_irrefl Q
      have hVal : childStartFn Q = Q - 1 := by
        dsimp only [childStartFn]
        rw [dite_eq_right hNot]
      rw [hVal]
      rw [show treeBase + 7 * Q + Q = treeBase + 8 * Q by omega]
      exact hMemCsrLast
  have hChildStart_bucket : ∀ u : Fin Q,
      childStartFn (u.val + 1) = childStartFn u.val + (bucketChildren ⟨0, hQPos⟩ parent u).length ∧
      childStartFn (u.val + 1) ≤ Q - 1 := by
    intro u
    obtain ⟨lo, hiB, hLo, hHi, hLen, hHiLe, _, _⟩ := hMemBuckets u
    have hLoEq : childStartFn u.val = lo := by
      have hm := hChildStart_mem u.val (Nat.le_of_lt u.isLt)
      have : some (childStartFn u.val) = some lo := hm.symm.trans hLo
      exact Option.some.inj this
    have hHiEq : childStartFn (u.val + 1) = hiB := by
      have hm := hChildStart_mem (u.val + 1) u.isLt
      have hHi' : (mem[treeBase + 7 * Q + (u.val + 1)]?).map Fin.val = some hiB := by
        rw [show treeBase + 7 * Q + (u.val + 1) = treeBase + 7 * Q + u.val + 1 by omega]
        exact hHi
      have : some (childStartFn (u.val + 1)) = some hiB := hm.symm.trans hHi'
      exact Option.some.inj this
    rw [hLoEq, hHiEq]
    exact ⟨hLen, hHiLe⟩
  have hChildStart_mono : ∀ i j : Nat, i ≤ j → j ≤ Q → childStartFn i ≤ childStartFn j := by
    intro i j hij hjQ
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    induction k with
    | zero => exact Nat.le_refl _
    | succ k ih =>
      have hk1 : childStartFn i ≤ childStartFn (i + k) := ih (by omega) (by omega)
      have hStep := (hChildStart_bucket ⟨i + k, by omega⟩).1
      rw [← Nat.add_assoc]
      exact Nat.le_trans hk1 (by rw [hStep]; exact Nat.le_add_right _ _)
  have hChildStart_zero : childStartFn 0 = 0 := by
    have hm := hChildStart_mem 0 (Nat.zero_le Q)
    simp only [Nat.add_zero] at hm
    exact Option.some.inj (hm.symm.trans hMemCsr0)
  have hChildStart_end : childStartFn Q = Q - 1 := by
    have hNot : ¬ Q < Q := Nat.lt_irrefl Q
    dsimp only [childStartFn]
    rw [dite_eq_right hNot]
  have hBucketOfPos : ∀ pos : Nat, pos < Q - 1 →
      ∃ u : Fin Q, childStartFn u.val ≤ pos ∧ pos < childStartFn (u.val + 1) := by
    intro pos hpos
    have aux : ∀ bound : Nat, bound ≤ Q → pos < childStartFn bound →
        ∃ u : Fin Q, childStartFn u.val ≤ pos ∧ pos < childStartFn (u.val + 1) := by
      intro bound
      induction bound with
      | zero => intro _ h0; rw [hChildStart_zero] at h0; omega
      | succ b ih =>
        intro hb hSb
        by_cases hpPrev : pos < childStartFn b
        · exact ih (by omega) hpPrev
        · exact ⟨⟨b, by omega⟩, Nat.not_lt.mp hpPrev, by simpa only [Nat.succ_eq_add_one] using hSb⟩
    exact aux Q (Nat.le_refl _) (by rw [hChildStart_end]; exact hpos)
  let childIdFn : Fin (Q - 1) → Fin Q := fun pos =>
    match mem[treeBase + (10 * Q + 1) + pos.val]? with
    | some w => if hw : w.val < Q then ⟨w.val, hw⟩ else ⟨0, hQPos⟩
    | none => ⟨0, hQPos⟩
  have hChildPosSpec : ∀ (u : Fin Q) (pos : Nat)
      (hlo : childStartFn u.val ≤ pos) (hhi : pos < childStartFn (u.val + 1))
      (hp : pos < Q - 1),
      ∃ hj : pos - childStartFn u.val < (bucketChildren ⟨0, hQPos⟩ parent u).length,
        let c := (bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj
        childIdFn ⟨pos, hp⟩ = c ∧
        (mem[treeBase + (8 * Q + 1) + pos]?).map Fin.val = some (built.endpoints.entry.read c) ∧
        (mem[treeBase + (9 * Q + 1) + pos]?).map Fin.val = some (built.endpoints.stop.read c) ∧
        (mem[treeBase + (10 * Q + 1) + pos]?).map Fin.val = some c.val := by
    intro u pos hlo hhi hp
    obtain ⟨lo, hiB, hLo, hHi, hLen, _, hKids, _⟩ := hMemBuckets u
    have hLoEq : childStartFn u.val = lo :=
      Option.some.inj ((hChildStart_mem u.val (Nat.le_of_lt u.isLt)).symm.trans hLo)
    have hHiEq : childStartFn (u.val + 1) = hiB := by
      have hm := hChildStart_mem (u.val + 1) u.isLt
      have hHi' : (mem[treeBase + 7 * Q + (u.val + 1)]?).map Fin.val = some hiB := by
        rw [show treeBase + 7 * Q + (u.val + 1) = treeBase + 7 * Q + u.val + 1 by omega]
        exact hHi
      exact Option.some.inj (hm.symm.trans hHi')
    have hj : pos - childStartFn u.val < (bucketChildren ⟨0, hQPos⟩ parent u).length := by
      omega
    obtain ⟨hId, hEn, hSt⟩ := hKids (pos - childStartFn u.val) hj
    have hAddrId : treeBase + 10 * Q + 1 + lo + (pos - childStartFn u.val) =
        treeBase + (10 * Q + 1) + pos := by omega
    have hAddrEn : treeBase + 8 * Q + 1 + lo + (pos - childStartFn u.val) =
        treeBase + (8 * Q + 1) + pos := by omega
    have hAddrSt : treeBase + 9 * Q + 1 + lo + (pos - childStartFn u.val) =
        treeBase + (9 * Q + 1) + pos := by omega
    have hId' : (mem[treeBase + (10 * Q + 1) + pos]?).map Fin.val =
        some ((bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj).val := by
      rw [← hAddrId]; exact hId
    have hEn' : (mem[treeBase + (8 * Q + 1) + pos]?).map Fin.val =
        some (built.endpoints.entry.read ((bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj)) := by
      rw [← hAddrEn]; exact hEn
    have hSt' : (mem[treeBase + (9 * Q + 1) + pos]?).map Fin.val =
        some (built.endpoints.stop.read ((bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj)) := by
      rw [← hAddrSt]; exact hSt
    have hIdEq : childIdFn ⟨pos, hp⟩ = (bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj := by
      dsimp only [childIdFn]
      cases hq : mem[treeBase + (10 * Q + 1) + pos]? with
      | none => simp [hq] at hId'
      | some w =>
        have hwVal : w.val = ((bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj).val := by
          simpa [hq] using hId'
        have hwLt : w.val < Q := by
          rw [hwVal]; exact ((bucketChildren ⟨0, hQPos⟩ parent u)[pos - childStartFn u.val]'hj).isLt
        dsimp only
        rw [dite_eq_left hwLt]
        exact Fin.ext hwVal
    exact ⟨hj, hIdEq, hEn', hSt', hId'⟩
  have hDReachAll : ∀ v : Fin Q,
      (RamDomBuild.denseDigraph Q inStart inSrc).InitiallyReachable ⟨0, hQPos⟩ v := by
    intro v
    have hRg : g.InitiallyReachable r (dense[v.val]'v.isLt) := hDenseReach v.val v.isLt
    obtain ⟨b, hbEq, hpD⟩ := g_survivingPath_to_denseDigraph hDenseDigraph hDenseReach hRg ⟨0, hQPos⟩ hDense0
    have hbV : b = v :=
      Fin.ext (nodup_getElem_inj (denseVertices_nodup g r order hTopo) b.isLt v.isLt hbEq)
    rw [← hbV]
    exact hpD
  have hDomIffD : ∀ a b : Fin Q,
      (RamDomBuild.denseDigraph Q inStart inSrc).Dominates ⟨0, hQPos⟩ a b ↔
        g.Dominates r (dense[a.val]'a.isLt) (dense[b.val]'b.isLt) := by
    intro a b
    constructor
    · intro hDomD hgPath
      obtain ⟨b', hb'Eq, hdPath⟩ :=
        g_survivingPath_to_denseDigraph hDenseDigraph hDenseReach hgPath ⟨0, hQPos⟩ hDense0
      have hb' : b' = b :=
        Fin.ext (nodup_getElem_inj (denseVertices_nodup g r order hTopo) b'.isLt b.isLt hb'Eq)
      have hdPath0 : (RamDomBuild.denseDigraph Q inStart inSrc).SurvivingPath
          (fun z : Fin Q => dense[z.val]'z.isLt = dense[a.val]'a.isLt) ⟨0, hQPos⟩ b' := hdPath
      have hdPath' : (RamDomBuild.denseDigraph Q inStart inSrc).SurvivingPath
          (fun z => z = a) ⟨0, hQPos⟩ b :=
        hb' ▸ avoidPath_mono (fun _ hz => hz ▸ rfl) hdPath0
      exact hDomD hdPath'
    · intro hDomG hdPath
      have hdPathG : (RamDomBuild.denseDigraph Q inStart inSrc).SurvivingPath
          (fun z : Fin Q => dense[z.val]'z.isLt = dense[a.val]'a.isLt) ⟨0, hQPos⟩ b :=
        avoidPath_mono
          (fun z hz => Fin.ext (nodup_getElem_inj (denseVertices_nodup g r order hTopo) z.isLt a.isLt hz))
          hdPath
      have hgPath := denseDigraph_survivingPath_to_g (Q := Q) (dense := dense) rfl
        (fun u v => hDenseDigraph u v) (failed := fun z => z = dense[a.val]'a.isLt) hdPathG
      rw [hDense0] at hgPath
      exact hDomG hgPath
  have hDAcyc : ∃ qRank : Fin Q → Nat,
      ∀ u v : Fin Q, (RamDomBuild.denseDigraph Q inStart inSrc).HasArc u v → qRank u < qRank v := by
    obtain ⟨rank, progress⟩ := acyc
    exact ⟨fun u => rank (dense[u.val]'u.isLt), fun u v huv => progress _ _ ((hDenseDigraph u v).mp huv)⟩
  refine
    { qPos := hQPos
      nodup := denseVertices_nodup g r order hTopo
      head_eq := hDense0
      reach_mem := hDenseReach
      mem_reach := fun v hv => (denseVertices_mem_iff g r order hTopo v).mpr hv
      domParent := parent
      domDepth := depth
      heavy := fun u => match built.packed.heavy.read u with | none => Q | some h => h.val
      head := tables.head
      entry := built.endpoints.entry.read
      stop := built.endpoints.stop.read
      denseOfEntry := denseOfEntryFn
      childStart := childStartFn
      childIds := childIdFn
      fit := hFit
      domParent_mem := hMemPar
      domDepth_mem := hMemDep
      heavy_mem := hMemHeavy
      head_mem := hMemHead
      entry_mem := hMemEnt
      stop_mem := hMemStop
      denseOfEntry_mem := hDenseOfEntry_mem
      childStart_mem := hChildStart_mem
      childEntries_mem := fun pos => by
        obtain ⟨u, hlo, hhi⟩ := hBucketOfPos pos.val pos.isLt
        obtain ⟨_, hIdEq, hEn, _, _⟩ := hChildPosSpec u pos.val hlo hhi pos.isLt
        rw [hIdEq]
        exact hEn
      childStops_mem := fun pos => by
        obtain ⟨u, hlo, hhi⟩ := hBucketOfPos pos.val pos.isLt
        obtain ⟨_, hIdEq, _, hSt, _⟩ := hChildPosSpec u pos.val hlo hhi pos.isLt
        rw [hIdEq]
        exact hSt
      childIds_mem := fun pos => by
        obtain ⟨u, hlo, hhi⟩ := hBucketOfPos pos.val pos.isLt
        obtain ⟨_, hIdEq, _, _, hId⟩ := hChildPosSpec u pos.val hlo hhi pos.isLt
        rw [hIdEq]
        exact hId
      domParent_root := by rw [hTree.parent_root]
      domParent_lt := fun v hv => hParLt v hv
      domDepth_root := hTree.depth_root
      domDepth_step := fun v hv => hTree.depth_step v (fun e => by rw [e] at hv; exact Nat.lt_irrefl 0 hv)
      domParent_spec := fun v hv => by
        have hvNe : v ≠ ⟨0, hQPos⟩ := fun e => by rw [e] at hv; exact Nat.lt_irrefl 0 hv
        have himmD := hParSpec.immediate (hDReachAll v) hvNe
        refine ⟨fun e => himmD.1 (Fin.ext (nodup_getElem_inj (denseVertices_nodup g r order hTopo)
            (parent v).isLt v.isLt e)),
          (hDomIffD (parent v) v).mp himmD.2.1, ?_⟩
        intro a haNe haDom
        have haReach := initiallyReachable_of_dominates (hDenseReach v.val v.isLt) haDom
        obtain ⟨ai, haiLt, haiEq⟩ := List.mem_iff_getElem.mp ((denseVertices_mem_iff g r order hTopo a).mpr haReach)
        let aD : Fin Q := ⟨ai, haiLt⟩
        have haNeD : aD ≠ v := fun e =>
          haNe (haiEq.symm.trans (congrArg (fun z : Fin Q => dense[z.val]'z.isLt) e))
        have haDomD : (RamDomBuild.denseDigraph Q inStart inSrc).Dominates ⟨0, hQPos⟩ aD v :=
          (hDomIffD aD v).mpr (by dsimp only [aD]; rw [haiEq]; exact haDom)
        have hRes := himmD.2.2 aD haNeD haDomD
        rw [← haiEq]
        exact (hDomIffD aD (parent v)).mp hRes
      entry_lt_stop := fun v => ⟨(hMemDofE v).1, (hMemDofE v).2.1⟩
      denseOfEntry_entry := hDenseOfEntry_entry
      dominates_iff_interval := fun a v => by
        obtain ⟨qRank, qProg⟩ := hDAcyc
        have hParSpecQ : ParentSpec (RamDomBuild.denseDigraph Q inStart inSrc) ⟨0, hQPos⟩ parent := hParSpec
        have hAncDom : Ancestor (parent : Fin (RamDomBuild.denseDigraph Q inStart inSrc).vertexCount → _) a v ↔
            (RamDomBuild.denseDigraph Q inStart inSrc).Dominates ⟨0, hQPos⟩ a v :=
          ancestor_iff_dominates (d := a) qProg hParSpecQ (hDReachAll v)
        have hAncFor : Ancestor parent a v ↔ IsForestAncestor parent a v :=
          ancestor_iff_isForestAncestor parent a v
        rw [← hDomIffD a v, ← hAncDom]
        change Ancestor parent a v ↔ _
        rw [hAncFor, isForestAncestor_iff_dfsIntervalContains hTree a v]
        have hOk := RamDomAndStaticTree.staticInputOK hQPos hTree
        have hTabRead : ∀ {α : Type} (f : Fin Q → α), (PackedStaticLayout.tabulate f).read = f :=
          fun f => funext (PackedStaticLayout.read_tabulate f)
        have hEntA := PackedStaticLayout.entry_exact x hOk a
        have hEntV := PackedStaticLayout.entry_exact x hOk v
        have hStopA := PackedStaticLayout.stop_exact x hOk a
        simp only [x, RamDomAndStaticTree.staticInput, hTabRead] at hEntA hEntV hStopA
        change dfsIntervalContains ⟨0, hQPos⟩ parent depth a v ↔ _
        unfold dfsIntervalContains
        rw [← hStopA, ← hEntA, ← hEntV]
        rfl
      childStart_zero := hChildStart_zero
      childStart_end := hChildStart_end
      childStart_mono := hChildStart_mono
      childIds_mem_iff := fun d c => by
        constructor
        · rintro ⟨pos, hlo, hhi, hp, hEq⟩
          obtain ⟨_, hIdEq, _, _, _⟩ := hChildPosSpec d pos hlo hhi hp
          have hcMem : c ∈ bucketChildren ⟨0, hQPos⟩ parent d := by
            rw [← hEq, hIdEq]
            exact List.getElem_mem _
          have hcProp := (mem_bucketChildren_iff ⟨0, hQPos⟩ parent d c).mp hcMem
          exact ⟨fun e => hcProp.1 (Fin.ext e), hcProp.2⟩
        · rintro ⟨hc0, hpc⟩
          have hcNe : c ≠ ⟨0, hQPos⟩ := fun e => hc0 (congrArg Fin.val e)
          have hcMem : c ∈ bucketChildren ⟨0, hQPos⟩ parent d :=
            (mem_bucketChildren_iff ⟨0, hQPos⟩ parent d c).mpr ⟨hcNe, hpc⟩
          obtain ⟨j, hj, hjEq⟩ := List.mem_iff_getElem.mp hcMem
          have hStep := hChildStart_bucket d
          let pos := childStartFn d.val + j
          have hlo : childStartFn d.val ≤ pos := Nat.le_add_right _ _
          have hhi : pos < childStartFn (d.val + 1) := by dsimp only [pos]; omega
          have hp : pos < Q - 1 := by dsimp only [pos]; omega
          obtain ⟨hj', hIdEq, _, _, _⟩ := hChildPosSpec d pos hlo hhi hp
          have hSub : pos - childStartFn d.val = j := Nat.add_sub_cancel_left _ _
          refine ⟨pos, hlo, hhi, hp, ?_⟩
          have hGet : (bucketChildren ⟨0, hQPos⟩ parent d)[pos - childStartFn d.val]'hj' =
              (bucketChildren ⟨0, hQPos⟩ parent d)[j]'hj := by congr 1
          exact hIdEq.trans (hGet.trans hjEq)
      childEntries_strict := fun d i j hlo hij hhi hi hj => by
        obtain ⟨lo, hiB, hLo, hHi, _, _, _, hMon⟩ := hMemBuckets d
        have hLoEq : childStartFn d.val = lo :=
          Option.some.inj ((hChildStart_mem d.val (Nat.le_of_lt d.isLt)).symm.trans hLo)
        have hHiEq : childStartFn (d.val + 1) = hiB := by
          have hm := hChildStart_mem (d.val + 1) d.isLt
          have hHi' : (mem[treeBase + 7 * Q + (d.val + 1)]?).map Fin.val = some hiB := by
            rw [show treeBase + 7 * Q + (d.val + 1) = treeBase + 7 * Q + d.val + 1 by omega]
            exact hHi
          exact Option.some.inj (hm.symm.trans hHi')
        have hi0 : i - childStartFn d.val < j - childStartFn d.val := by omega
        have hj0 : j - childStartFn d.val < hiB - lo := by omega
        obtain ⟨ei, ej, hei, hej, hlt⟩ := hMon (i - childStartFn d.val) (j - childStartFn d.val) hi0 hj0
        have hAddrI : treeBase + 8 * Q + 1 + lo + (i - childStartFn d.val) =
            treeBase + (8 * Q + 1) + i := by omega
        have hAddrJ : treeBase + 8 * Q + 1 + lo + (j - childStartFn d.val) =
            treeBase + (8 * Q + 1) + j := by omega
        obtain ⟨_, hIdI, hEnI, _, _⟩ := hChildPosSpec d i hlo (by omega) hi
        obtain ⟨_, hIdJ, hEnJ, _, _⟩ := hChildPosSpec d j (by omega) hhi hj
        have hEiEq : built.endpoints.entry.read (childIdFn ⟨i, hi⟩) = ei := by
          rw [hIdI]
          rw [hAddrI] at hei
          exact Option.some.inj (hEnI.symm.trans hei)
        have hEjEq : built.endpoints.entry.read (childIdFn ⟨j, hj⟩) = ej := by
          rw [hIdJ]
          rw [hAddrJ] at hej
          exact Option.some.inj (hEnJ.symm.trans hej)
        rw [hEiEq, hEjEq]
        exact hlt }

private theorem matchesPackedLayout_of_prefix {bits : Nat}
    {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {order : List (Fin g.vertexCount)}
    {hTopo : g.IsTopologicalList order}
    {parent : Fin (denseVertices g r order hTopo).length → Fin (denseVertices g r order hTopo).length}
    {depth : Fin (denseVertices g r order hTopo).length → Nat}
    (S : StaticTreeSlice mem treeBase g r (denseVertices g r order hTopo))
    (hQPos : 1 ≤ (denseVertices g r order hTopo).length)
    (hParent : S.domParent = parent)
    (hDepth : S.domDepth = depth)
    (hHeadEq : ∀ v, S.head v =
      (StaticHeadSweep.tables (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed).head v)
    (hHeavyEq : ∀ u, S.heavy u =
      match (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed.heavy.read u with
      | none => (denseVertices g r order hTopo).length
      | some h => h.val)
    (hEntryEq : ∀ v, S.entry v =
      (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read v)
    (hStopEq : ∀ v, S.stop v =
      (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read v)
    (hMemBuckets : ∀ u : Fin (denseVertices g r order hTopo).length,
      ∃ lo hi : Nat,
        (mem[treeBase + 7 * (denseVertices g r order hTopo).length + u.val]?).map Fin.val = some lo ∧
        (mem[treeBase + 7 * (denseVertices g r order hTopo).length + u.val + 1]?).map Fin.val = some hi ∧
        hi = lo + (bucketChildren ⟨0, hQPos⟩ parent u).length ∧
        hi ≤ (denseVertices g r order hTopo).length - 1 ∧
        (∀ j : Nat, ∀ hj : j < (bucketChildren ⟨0, hQPos⟩ parent u).length,
          let c := (bucketChildren ⟨0, hQPos⟩ parent u)[j]'hj
          (mem[treeBase + 10 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val = some c.val ∧
          (mem[treeBase + 8 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val =
            some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.entry.read c) ∧
          (mem[treeBase + 9 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val =
            some ((PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).endpoints.stop.read c)) ∧
        (∀ i j : Nat, i < j → j < hi - lo →
          ∃ ei ej : Nat,
            (mem[treeBase + 8 * (denseVertices g r order hTopo).length + 1 + lo + i]?).map Fin.val = some ei ∧
            (mem[treeBase + 8 * (denseVertices g r order hTopo).length + 1 + lo + j]?).map Fin.val = some ej ∧
            ei < ej)) :
    MatchesPackedLayout S := by
  have hInput : S.packedInput = RamDomAndStaticTree.staticInput hQPos parent depth := by
    cases hParent
    cases hDepth
    rfl
  refine
    { head_eq := fun v => by rw [hInput]; exact hHeadEq v
      heavy_eq := fun u => by
        rw [hInput]
        have h := hHeavyEq u
        cases hRead : (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos parent depth)).packed.heavy.read u <;>
          simpa only [hRead] using h
      entry_eq := fun v => by rw [hInput]; exact hEntryEq v
      stop_eq := fun v => by rw [hInput]; exact hStopEq v
      childSlice_eq := fun d => by
        rw [PackedStaticLayout.bucket_read]
        have hP : S.packedInput.parent.read = parent := by
          rw [hInput]
          exact funext (PackedStaticLayout.read_tabulate parent)
        change S.childSlice d = bucketChildren S.packedInput.root S.packedInput.parent.read d
        rw [hP]
        change S.childSlice d = bucketChildren ⟨0, hQPos⟩ parent d
        obtain ⟨lo, hi, hLo, hHi, hLen, hHiLe, hKids, _⟩ := hMemBuckets d
        have hStartLo : S.childStart d.val = lo :=
          Option.some.inj ((S.childStart_mem d.val (Nat.le_of_lt d.isLt)).symm.trans hLo)
        have hStartHi : S.childStart (d.val + 1) = hi := by
          have hm := S.childStart_mem (d.val + 1) d.isLt
          have hHi' : (mem[treeBase + 7 * (denseVertices g r order hTopo).length + (d.val + 1)]?).map Fin.val = some hi := by
            rw [show treeBase + 7 * (denseVertices g r order hTopo).length + (d.val + 1) =
                treeBase + 7 * (denseVertices g r order hTopo).length + d.val + 1 by omega]
            exact hHi
          exact Option.some.inj (hm.symm.trans hHi')
        apply List.ext_getElem
        · simp only [StaticTreeSlice.childSlice, List.length_ofFn]
          omega
        · intro j hj1 hj2
          simp only [StaticTreeSlice.childSlice, List.getElem_ofFn]
          have hj : j < (bucketChildren ⟨0, hQPos⟩ parent d).length := hj2
          have hIdMem := S.childIds_mem ⟨S.childStart d.val + j, by omega⟩
          have hKid := (hKids j hj).1
          have hAddr : treeBase + 10 * (denseVertices g r order hTopo).length + 1 + lo + j =
              treeBase + (10 * (denseVertices g r order hTopo).length + 1) + (S.childStart d.val + j) := by
            omega
          rw [hAddr] at hKid
          exact Fin.ext (Option.some.inj (hIdMem.symm.trans hKid)) }

private theorem matchesPackedLayout_ofMemEq {bits : Nat}
    {mem₁ mem₂ : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {S : StaticTreeSlice mem₁ treeBase g r dense}
    (hMatch : MatchesPackedLayout S)
    (hSz : mem₂.size = mem₁.size)
    (hPres : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords dense.length → mem₂[k]? = mem₁[k]?) :
    MatchesPackedLayout (S.ofMemEq hSz hPres) :=
  ⟨hMatch.head_eq, hMatch.heavy_eq, hMatch.entry_eq, hMatch.stop_eq, hMatch.childSlice_eq⟩

end StaticTreeBridge

section DirectFlatness

private theorem avoidPath_snoc {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {a b c : V} (p : AvoidPath edge failed a b) (hbc : edge b c) (hc : ¬ failed c) :
    AvoidPath edge failed a c := by
  revert hbc hc
  induction p with
  | refl x hx => intro hbc hc; exact AvoidPath.step x c c hx hbc (AvoidPath.refl c hc)
  | step x w y hx hxw _ ih => intro hbc hc; exact AvoidPath.step x w c hx hxw (ih hbc hc)

private theorem avoidPath_trans {V : Type} {edge : V → V → Prop} {failed : V → Prop}
    {a b c : V} (p : AvoidPath edge failed a b) (q : AvoidPath edge failed b c) :
    AvoidPath edge failed a c := by
  revert q
  induction p with
  | refl _ _ => intro q; exact q
  | step x w y hx hxw _ ih => intro q; exact AvoidPath.step x w c hx hxw (ih q)

private theorem suffix_from_dom {g : Digraph} {P : Fin g.vertexCount → Prop}
    (d₀ : Fin g.vertexCount) :
    ∀ {a y : Fin g.vertexCount}, y ≠ d₀ → g.SurvivingPath P a y →
      AvoidPath g.HasArc (fun z => P z ∨ z = d₀) a y ∨
      (¬ P d₀ ∧ ∃ w : Fin g.vertexCount, g.HasArc d₀ w ∧
        AvoidPath g.HasArc (fun z => P z ∨ z = d₀) w y) := by
  intro a y hyd p
  revert hyd
  induction p with
  | refl x hx =>
    intro hyd
    exact Or.inl (AvoidPath.refl x (fun h => h.elim hx hyd))
  | step x w z hx hxw _ ih =>
    intro hyd
    rcases ih hyd with hRest | hRight
    · by_cases hxd : x = d₀
      · subst hxd
        exact Or.inr ⟨hx, w, hxw, hRest⟩
      · exact Or.inl (AvoidPath.step x w z (fun h => h.elim hx hxd) hxw hRest)
    · exact Or.inr hRight

private theorem avoid_dom_of_avoid_vertex {g : Digraph} (r u₀ : Fin g.vertexCount) :
    ∀ {a y : Fin g.vertexCount},
      AvoidPath g.HasArc (fun z => z = u₀) r a →
      AvoidPath g.HasArc (fun z => z = u₀) a y →
      AvoidPath g.HasArc (fun z => g.Dominates r u₀ z) a y := by
  intro a y hPref p
  revert hPref
  induction p with
  | refl x _ => intro hPref; exact AvoidPath.refl x (fun hd => hd hPref)
  | step x w y _ hxw rest ih =>
    intro hPref
    have hwAlive : w ≠ u₀ := by
      cases rest with
      | refl _ h => exact h
      | step _ _ _ h _ _ => exact h
    exact AvoidPath.step x w y (fun hd => hd hPref) hxw
      (ih (avoidPath_snoc hPref hxw hwAlive))

private theorem dom_along_suffix {g : Digraph} {r d₀ y : Fin g.vertexCount}
    {P : Fin g.vertexCount → Prop} (hDomY : g.Dominates r d₀ y) :
    ∀ {w : Fin g.vertexCount}, AvoidPath g.HasArc (fun z => P z ∨ z = d₀) w y →
      g.Dominates r d₀ w := by
  intro w p hp
  have hWy : AvoidPath g.HasArc (fun z => z = d₀) w y :=
    avoidPath_mono (fun _ hz => Or.inr hz) p
  exact hDomY (avoidPath_trans hp hWy)

private theorem childSlice_same_dom {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c₁ c₂ : Fin dense.length)
    (hc₁ : c₁ ∈ S.childSlice d) (hc₂ : c₂ ∈ S.childSlice d)
    {x : Fin dense.length}
    (h1 : g.Dominates r (dense[c₁.val]'c₁.isLt) (dense[x.val]'x.isLt))
    (h2 : g.Dominates r (dense[c₂.val]'c₂.isLt) (dense[x.val]'x.isLt)) :
    c₁ = c₂ := by
  have hi1 := (S.dominates_iff_interval c₁ x).mp h1
  have hi2 := (S.dominates_iff_interval c₂ x).mp h2
  rcases Nat.lt_trichotomy (S.entry c₁) (S.entry c₂) with hLt | hEq | hGt
  · have hDisj := S.child_interval_disjoint acyc d c₁ c₂ hc₁ hc₂ hLt
    omega
  · have hLt1 : S.entry c₁ < dense.length :=
      Nat.lt_of_lt_of_le (S.entry_lt_stop c₁).1 (S.entry_lt_stop c₁).2
    have hLt2 : S.entry c₂ < dense.length :=
      Nat.lt_of_lt_of_le (S.entry_lt_stop c₂).1 (S.entry_lt_stop c₂).2
    have h1' := S.denseOfEntry_entry c₁ hLt1
    have h2' := S.denseOfEntry_entry c₂ hLt2
    rw [← h1', ← h2']
    congr 1
    exact Fin.ext hEq
  · have hDisj := S.child_interval_disjoint acyc d c₂ c₁ hc₂ hc₁ hGt
    omega

private theorem srcLocal_eq_of_child_dom {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c x : Fin dense.length) (hc : c ∈ S.childSlice d)
    (hdx : g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt))
    (hcx : g.Dominates r (dense[c.val]'c.isLt) (dense[x.val]'x.isLt)) :
    S.srcLocalOf d x = (S.childSlice d).idxOf c + 1 := by
  rcases S.srcLocalOf_spec acyc d x hdx with ⟨hxd, _⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
  · subst x
    exfalso
    obtain ⟨hcPos, hcP⟩ := (S.mem_childSlice_iff d c).mp hc
    have hcPos' : 0 < c.val := Nat.pos_of_ne_zero hcPos
    have himm := S.domParent_spec c hcPos'
    rw [hcP] at himm
    have hcNeD : c ≠ d := by rw [← hcP]; exact (S.domParent_ne_self c hcPos').symm
    have hcdNe : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt := fun e => hcNeD (S.dense_injective e)
    obtain ⟨rank, progress⟩ := acyc
    have hlt1 := rank_lt_of_strict_dominator progress (S.reach_mem c.val c.isLt) himm.2.1 hcdNe.symm
    have hlt2 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hcx hcdNe
    omega
  · have hEqC : c = c' := childSlice_same_dom S acyc d c c' hc hc'Mem hcx hc'Dom
    rw [hc'Idx, hEqC]

private theorem selfSlot_eq_of_child {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d) :
    S.selfSlotFn c = (S.childSlice d).idxOf c + 1 := by
  obtain ⟨hcPos, hcP⟩ := (S.mem_childSlice_iff d c).mp hc
  unfold StaticTreeSlice.selfSlotFn
  rw [dite_eq_right hcPos]
  dsimp only
  rw [hcP]

private theorem ramQuotient_arc_of_step {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d wDense midDense : Fin dense.length)
    (hArc : g.HasArc (dense[wDense.val]'wDense.isLt) (dense[midDense.val]'midDense.isLt))
    (hDomW : g.Dominates r (dense[d.val]'d.isLt) (dense[wDense.val]'wDense.isLt))
    (hDomMid : g.Dominates r (dense[d.val]'d.isLt) (dense[midDense.val]'midDense.isLt))
    (hMidNeD : midDense ≠ d)
    (hLocNe : S.srcLocalOf d wDense ≠ S.srcLocalOf d midDense) :
    (S.ramQuotient d).HasQuotientArc
      ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
      ⟨S.srcLocalOf d midDense, S.srcLocalOf_lt d midDense⟩ := by
  rcases S.srcLocalOf_spec acyc d midDense hDomMid with ⟨hm, _⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
  · exact False.elim (hMidNeD hm)
  · have hMidEqC' : midDense = c' := Classical.byContradiction fun hNe => by
      have hMidNeOrig : dense[midDense.val]'midDense.isLt ≠ dense[c'.val]'c'.isLt :=
        fun e => hNe (S.dense_injective e)
      have hDomW_c' : g.Dominates r (dense[c'.val]'c'.isLt) (dense[wDense.val]'wDense.isLt) :=
        dominates_reachable_predecessor_of_ne hArc (S.reach_mem wDense.val wDense.isLt) hMidNeOrig hc'Dom
      have hSrcW := srcLocal_eq_of_child_dom S acyc d c' wDense hc'Mem hDomW hDomW_c'
      exact hLocNe (hSrcW.trans hc'Idx.symm)
    subst hMidEqC'
    obtain ⟨_, hc'P⟩ := (S.mem_childSlice_iff d midDense).mp hc'Mem
    have hSelf : S.selfSlotFn midDense = S.srcLocalOf d midDense :=
      (selfSlot_eq_of_child S d midDense hc'Mem).trans hc'Idx.symm
    let locW : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
    let locMid : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d midDense, S.srcLocalOf_lt d midDense⟩
    refine ⟨⟨locMid, dense[wDense.val]'wDense.isLt⟩, ?_, rfl⟩
    rw [S.mem_outArcs_ramQuotient_iff d locW ⟨locMid, dense[wDense.val]'wDense.isLt⟩]
    exact ⟨wDense, midDense, hArc, hc'P, rfl, hSelf, rfl⟩

private theorem ramQuotient_surviving_of_suffix_aux {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d)
    (failedG : Fin g.vertexCount → Prop)
    (failedQ : Fin (S.ramQuotient d).vertexCount → Prop)
    (hNoFail : ∀ x : Fin dense.length,
      g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt) →
      ¬ failedG (dense[x.val]'x.isLt) →
      ¬ failedQ ⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩)
    (hDomC : g.Dominates r (dense[d.val]'d.isLt) (dense[c.val]'c.isLt))
    {w y : Fin g.vertexCount}
    (p : AvoidPath g.HasArc (fun z => failedG z ∨ z = dense[d.val]'d.isLt) w y) :
    y = dense[c.val]'c.isLt →
    ∀ (wDense : Fin dense.length), dense[wDense.val]'wDense.isLt = w →
      g.Dominates r (dense[d.val]'d.isLt) w →
      (S.ramQuotient d).SurvivingPath failedQ
        ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
        ⟨(S.childSlice d).idxOf c + 1, by
          have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩ := by
  let vLocal : Fin (S.ramQuotient d).vertexCount :=
    ⟨(S.childSlice d).idxOf c + 1, by
      have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩
  have hSrcC : S.srcLocalOf d c = vLocal.val := srcLocal_eq_of_child_dom S acyc d c c hc hDomC dominates_refl
  induction p with
  | refl x hx =>
    intro hy wDense hwEq hDomW
    have hwc : wDense = c := S.dense_injective (hwEq.trans hy)
    subst hwc
    have hxAlive : ¬ failedG (dense[wDense.val]'wDense.isLt) := fun h => hx (hwEq ▸ Or.inl h)
    have hQAlive : ¬ failedQ ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩ :=
      hNoFail wDense hDomC hxAlive
    have hLocEq : (⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩ :
        Fin (S.ramQuotient d).vertexCount) = vLocal := Fin.ext hSrcC
    rw [hLocEq] at hQAlive ⊢
    exact AvoidPath.refl vLocal hQAlive
  | step x mid z hx hxw rest ih =>
    intro hz wDense hwEq hDomW
    have hxAlive : ¬ failedG (dense[wDense.val]'wDense.isLt) := fun h => hx (hwEq ▸ Or.inl h)
    have hMidReach : g.InitiallyReachable r mid :=
      Digraph.initiallyReachable_extend (hwEq ▸ S.reach_mem wDense.val wDense.isLt) (hwEq ▸ hxw)
    obtain ⟨mi, hmiLt, hmiEq⟩ := List.mem_iff_getElem.mp (S.mem_reach mid hMidReach)
    let midDense : Fin dense.length := ⟨mi, hmiLt⟩
    have hDomMid : g.Dominates r (dense[d.val]'d.isLt) mid := dom_along_suffix hDomC (hz ▸ rest)
    have hRestQ := ih hz midDense hmiEq hDomMid
    have hMidNeD : midDense ≠ d := by
      intro hEq
      have hDead : failedG mid ∨ mid = dense[d.val]'d.isLt :=
        Or.inr (hmiEq.symm.trans (congrArg (fun z : Fin dense.length => dense[z.val]'z.isLt) hEq))
      cases rest with
      | refl _ hal => exact hal hDead
      | step _ _ _ hal _ _ => exact hal hDead
    let locW : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
    let locMid : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d midDense, S.srcLocalOf_lt d midDense⟩
    by_cases hLocEq : locW = locMid
    · change (S.ramQuotient d).SurvivingPath failedQ locMid vLocal at hRestQ
      rw [← hLocEq] at hRestQ
      exact hRestQ
    · have hLocNe : S.srcLocalOf d wDense ≠ S.srcLocalOf d midDense := fun e => hLocEq (Fin.ext e)
      have harcQ := ramQuotient_arc_of_step S acyc d wDense midDense
        (by dsimp only [midDense]; rw [hwEq, hmiEq]; exact hxw)
        (hwEq ▸ hDomW) (hmiEq ▸ hDomMid) hMidNeD hLocNe
      have hQAlive : ¬ failedQ locW := hNoFail wDense (hwEq ▸ hDomW) hxAlive
      exact AvoidPath.step locW locMid vLocal hQAlive harcQ hRestQ

private theorem ramQuotient_surviving_of_suffix {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d)
    (failedG : Fin g.vertexCount → Prop)
    (failedQ : Fin (S.ramQuotient d).vertexCount → Prop)
    (hNoFail : ∀ x : Fin dense.length,
      g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt) →
      ¬ failedG (dense[x.val]'x.isLt) →
      ¬ failedQ ⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩)
    (hDomC : g.Dominates r (dense[d.val]'d.isLt) (dense[c.val]'c.isLt))
    {w : Fin g.vertexCount}
    (p : AvoidPath g.HasArc (fun z => failedG z ∨ z = dense[d.val]'d.isLt) w (dense[c.val]'c.isLt)) :
    ∀ (wDense : Fin dense.length), dense[wDense.val]'wDense.isLt = w →
      g.Dominates r (dense[d.val]'d.isLt) w →
      (S.ramQuotient d).SurvivingPath failedQ
        ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
        ⟨(S.childSlice d).idxOf c + 1, by
          have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩ :=
  ramQuotient_surviving_of_suffix_aux S acyc d c hc failedG failedQ hNoFail hDomC p rfl

private theorem ramQuotient_surviving_of_g_path {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d c : Fin dense.length) (hc : c ∈ S.childSlice d)
    (failedG : Fin g.vertexCount → Prop)
    (failedQ : Fin (S.ramQuotient d).vertexCount → Prop)
    (hNoFail : ∀ x : Fin dense.length,
      g.Dominates r (dense[d.val]'d.isLt) (dense[x.val]'x.isLt) →
      ¬ failedG (dense[x.val]'x.isLt) →
      ¬ failedQ ⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩)
    (pG : g.SurvivingPath failedG r (dense[c.val]'c.isLt)) :
    (S.ramQuotient d).SurvivingPath failedQ (S.ramQuotient d).root
      ⟨(S.childSlice d).idxOf c + 1, by
        have := List.idxOf_lt_length_of_mem hc; change _ < 1 + (S.childSlice d).length; omega⟩ := by
  obtain ⟨hcPos, hcP⟩ := (S.mem_childSlice_iff d c).mp hc
  have hcPos' : 0 < c.val := Nat.pos_of_ne_zero hcPos
  have himm := S.domParent_spec c hcPos'
  rw [hcP] at himm
  have hcNeD : c ≠ d := by rw [← hcP]; exact (S.domParent_ne_self c hcPos').symm
  have hcdNe : dense[c.val]'c.isLt ≠ dense[d.val]'d.isLt := fun e => hcNeD (S.dense_injective e)
  rcases suffix_from_dom (dense[d.val]'d.isLt) hcdNe pG with hAvoidD | ⟨hNotFailD, w, harcDW, pSuf⟩
  · exfalso
    exact himm.2.1 (avoidPath_mono (fun _ hz => Or.inr hz) hAvoidD)
  · have hwReach : g.InitiallyReachable r w :=
      Digraph.initiallyReachable_extend (S.reach_mem d.val d.isLt) harcDW
    obtain ⟨wi, hwiLt, hwiEq⟩ := List.mem_iff_getElem.mp (S.mem_reach w hwReach)
    let wDense : Fin dense.length := ⟨wi, hwiLt⟩
    have hDomW : g.Dominates r (dense[d.val]'d.isLt) w := dom_along_suffix himm.2.1 pSuf
    have hSufQ := ramQuotient_surviving_of_suffix S acyc d c hc failedG failedQ hNoFail
      himm.2.1 pSuf wDense hwiEq hDomW
    have hWNeD : wDense ≠ d := by
      intro hEq
      have hDead : failedG w ∨ w = dense[d.val]'d.isLt :=
        Or.inr (hwiEq.symm.trans (congrArg (fun z : Fin dense.length => dense[z.val]'z.isLt) hEq))
      cases pSuf with
      | refl _ hal => exact hal hDead
      | step _ _ _ hal _ _ => exact hal hDead
    let locD : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d d, S.srcLocalOf_lt d d⟩
    let locW : Fin (S.ramQuotient d).vertexCount := ⟨S.srcLocalOf d wDense, S.srcLocalOf_lt d wDense⟩
    have hLocDEq : locD = (S.ramQuotient d).root := by
      apply Fin.ext
      change S.srcLocalOf d d = 0
      unfold StaticTreeSlice.srcLocalOf
      simp
    rw [← hLocDEq]
    by_cases hLocEq : locD = locW
    · rw [hLocEq]
      exact hSufQ
    · have hLocNe : S.srcLocalOf d d ≠ S.srcLocalOf d wDense := fun e => hLocEq (Fin.ext e)
      have harcQ := ramQuotient_arc_of_step S acyc d d wDense
        (by dsimp only [wDense]; rw [hwiEq]; exact harcDW) dominates_refl (hwiEq ▸ hDomW) hWNeD hLocNe
      have hQAlive : ¬ failedQ locD := hNoFail d dominates_refl hNotFailD
      exact AvoidPath.step locD locW _ hQAlive harcQ hSufQ

private theorem ramQuotient_isFlat_of_staticTreeSlice
    {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (acyc : g.IsAcyclic)
    (d : Fin dense.length) :
    (S.ramQuotient d).IsFlat := by
  have hChildOfNonroot : ∀ x : Fin (S.ramQuotient d).vertexCount,
      x ≠ (S.ramQuotient d).root →
      ∃ hx : x.val - 1 < (S.childSlice d).length,
        let c := (S.childSlice d)[x.val - 1]'hx
        x = ⟨(S.childSlice d).idxOf c + 1, by
          have hIdxLt : (S.childSlice d).idxOf c < (S.childSlice d).length :=
            List.idxOf_lt_length_of_mem (List.getElem_mem hx)
          change _ < 1 + (S.childSlice d).length
          omega⟩ := by
    intro x hxNe
    have hxPos : 0 < x.val := Nat.pos_of_ne_zero (fun e => hxNe (Fin.ext e))
    have hxLt : x.val - 1 < (S.childSlice d).length := by
      have := x.isLt
      change x.val < 1 + (S.childSlice d).length at this
      omega
    refine ⟨hxLt, ?_⟩
    dsimp only
    have hnd := S.childSlice_nodup d
    have hmem := List.getElem_mem hxLt
    have hltIdx := List.idxOf_lt_length_of_mem hmem
    have hEqGet := List.getElem_idxOf hltIdx
    have hPw := List.pairwise_iff_getElem.mp (List.nodup_iff_pairwise_ne.mp hnd)
    have hIdxEq : (S.childSlice d).idxOf ((S.childSlice d)[x.val - 1]'hxLt) = x.val - 1 := by
      by_cases he : (S.childSlice d).idxOf ((S.childSlice d)[x.val - 1]'hxLt) = x.val - 1
      · exact he
      · rcases Nat.lt_or_gt_of_ne he with h1 | h2
        · exact False.elim (hPw _ _ hltIdx hxLt h1 hEqGet)
        · exact False.elim (hPw _ _ hxLt hltIdx h2 hEqGet.symm)
    apply Fin.ext
    dsimp only
    omega
  constructor
  · intro v
    by_cases hv : v = (S.ramQuotient d).root
    · rw [hv]; exact AvoidPath.refl _ not_false
    · obtain ⟨hvLt, hvEq⟩ := hChildOfNonroot v hv
      rw [hvEq]
      exact ramQuotient_surviving_of_g_path S acyc d ((S.childSlice d)[v.val - 1]'hvLt)
        (List.getElem_mem hvLt) (fun _ => False) (fun _ => False)
        (fun _ _ _ => not_false) (S.reach_mem _ _)
  · intro u v hu hvu
    by_cases hv : v = (S.ramQuotient d).root
    · rw [hv]; exact AvoidPath.refl _ hu.symm
    · obtain ⟨huLt, huEq⟩ := hChildOfNonroot u hu
      obtain ⟨hvLt, hvEq⟩ := hChildOfNonroot v hv
      let uChild := (S.childSlice d)[u.val - 1]'huLt
      let vChild := (S.childSlice d)[v.val - 1]'hvLt
      have huMem : uChild ∈ S.childSlice d := List.getElem_mem huLt
      have hvMem : vChild ∈ S.childSlice d := List.getElem_mem hvLt
      have huvChild : uChild ≠ vChild := by
        intro hEq
        apply hvu
        rw [hvEq, huEq]
        congr 1
        simp only [uChild, vChild] at hEq
        rw [hEq]
      have hNotDomUV : ¬ g.Dominates r (dense[uChild.val]'uChild.isLt) (dense[vChild.val]'vChild.isLt) := by
        intro hDom
        obtain ⟨hvPos, hvP⟩ := (S.mem_childSlice_iff d vChild).mp hvMem
        obtain ⟨huPos, huP⟩ := (S.mem_childSlice_iff d uChild).mp huMem
        have himmV := S.domParent_spec vChild (Nat.pos_of_ne_zero hvPos)
        rw [hvP] at himmV
        have himmU := S.domParent_spec uChild (Nat.pos_of_ne_zero huPos)
        rw [huP] at himmU
        have huvOrig : dense[uChild.val]'uChild.isLt ≠ dense[vChild.val]'vChild.isLt :=
          fun e => huvChild (S.dense_injective e)
        have hDomUD := himmV.2.2 (dense[uChild.val]'uChild.isLt) huvOrig hDom
        have huNeD : uChild ≠ d := by
          rw [← huP]; exact (S.domParent_ne_self uChild (Nat.pos_of_ne_zero huPos)).symm
        have huOrigD : dense[uChild.val]'uChild.isLt ≠ dense[d.val]'d.isLt :=
          fun e => huNeD (S.dense_injective e)
        obtain ⟨rank, progress⟩ := acyc
        have hlt1 := rank_lt_of_strict_dominator progress (S.reach_mem uChild.val uChild.isLt) himmU.2.1 huOrigD.symm
        have hlt2 := rank_lt_of_strict_dominator progress (S.reach_mem d.val d.isLt) hDomUD huOrigD
        omega
      have hpAvoidU : AvoidPath g.HasArc (fun z => z = dense[uChild.val]'uChild.isLt) r
          (dense[vChild.val]'vChild.isLt) :=
        Classical.byContradiction fun hDom => hNotDomUV hDom
      have hRNeU : r ≠ dense[uChild.val]'uChild.isLt := by
        obtain ⟨huPos, _⟩ := (S.mem_childSlice_iff d uChild).mp huMem
        intro e
        have : (⟨0, S.qPos⟩ : Fin dense.length) = uChild := S.dense_injective (S.head_eq.trans e)
        have : 0 = uChild.val := congrArg Fin.val this
        omega
      have hpG := avoid_dom_of_avoid_vertex r (dense[uChild.val]'uChild.isLt)
        (AvoidPath.refl r hRNeU) hpAvoidU
      rw [hvEq]
      refine ramQuotient_surviving_of_g_path S acyc d vChild hvMem
        (fun z => g.Dominates r (dense[uChild.val]'uChild.isLt) z) (fun z => z = u)
        ?_ hpG
      intro x hdx hxNotDom hEqU
      apply hxNotDom
      have hLocVal : S.srcLocalOf d x = (S.childSlice d).idxOf uChild + 1 := by
        have h1 : (⟨S.srcLocalOf d x, S.srcLocalOf_lt d x⟩ : Fin (S.ramQuotient d).vertexCount).val = u.val :=
          congrArg Fin.val hEqU
        have h2 : u.val = (S.childSlice d).idxOf uChild + 1 := by
          have := congrArg Fin.val huEq
          simpa only using this
        exact h1.trans h2
      rcases S.srcLocalOf_spec acyc d x hdx with ⟨_, h0⟩ | ⟨c', hc'Mem, hc'Dom, hc'Idx⟩
      · omega
      · have hc'Eq : c' = uChild := by
          rw [hc'Idx] at hLocVal
          have hIdxEq : (S.childSlice d).idxOf c' = (S.childSlice d).idxOf uChild := by omega
          have h1 := List.getElem_idxOf (List.idxOf_lt_length_of_mem hc'Mem)
          have h2 := List.getElem_idxOf (List.idxOf_lt_length_of_mem huMem)
          have hGet : (S.childSlice d)[(S.childSlice d).idxOf c']'(List.idxOf_lt_length_of_mem hc'Mem) =
              (S.childSlice d)[(S.childSlice d).idxOf uChild]'(List.idxOf_lt_length_of_mem huMem) := by
            congr 1
          exact h1.symm.trans (hGet.trans h2)
        rwa [← hc'Eq]

end DirectFlatness

section EndToEnd

/-- Public owner forest record specification produced by `prefixAndForestLoopProgram`
in `t.data`: six zeros for `n_d < 3`, or a verified `SerializedProperLossIndex` with
`w.wordCount ≤ 19 * n_d`, 6 bank pointers, and `packedPayload w` in `forestArenaBase`. -/
def OwnerForestRecordAt {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (loopBase n m forestUsed : Nat) (data : Array (Word bits)) : Prop :=
  let n_d := 1 + (S.childSlice d).length
  if n_d < 3 then
    ∀ k < 6, (data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
  else
    ∃ (w : WordColumns bits) (ptrBase : Nat),
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      PaperB.RamForestProgram.RawBuild.SerializedProperLossIndex (S.ramQuotient d) w ∧
      w.wordCount ≤ 19 * n_d ∧
      forestArenaBase loopBase n m ≤ ptrBase ∧
      ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
      (∀ k < w.wordCount, data[ptrBase + k]? = (packedPayload w)[k]?)

/-- Packed-witness variant of `OwnerForestRecordAt` exposing the `OrderedReaderResult`
and `packWordColumns` data for each large owner (`3 ≤ 1 + (S.childSlice d).length`). -/
def OwnerForestPackedRecord {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem treeBase g r dense) (d : Fin dense.length)
    (loopBase n m forestUsed : Nat) (data : Array (Word bits)) : Prop :=
  let n_d := 1 + (S.childSlice d).length
  if n_d < 3 then
    ∀ k < 6, (data[ownerForestPtrsBase loopBase n m + 6 * d.val + k]?).map Fin.val = some 0
  else
    ∃ (pH : PaperB.ForestDictionary.Rows (S.ramQuotient d))
      (dataH : Array (Vertex (S.ramQuotient d)))
      (sizeH : dataH.size = (S.ramQuotient d).vertexCount)
      (rankH : Vertex (S.ramQuotient d) → Nat)
      (hlarge : 3 ≤ (S.ramQuotient d).vertexCount)
      (_incH : ∀ i j : Fin (S.ramQuotient d).vertexCount, i.val < j.val →
        rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i) <
          rankH (_root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH j))
      (_covH : ∀ v : Vertex (S.ramQuotient d), ∃ i : Fin (S.ramQuotient d).vertexCount,
        _root_.EX24.PreparedSweep.orderedVertexAt dataH sizeH i = v)
      (_rArcH : ∀ u v : Vertex (S.ramQuotient d), (S.ramQuotient d).HasQuotientArc u v →
        rankH u < rankH v)
      (ordResH : PaperB.OrderedReaderResult pH dataH sizeH rankH hlarge)
      (hWidth : 1 + 18 * (S.ramQuotient d).vertexCount < 2 ^ bits)
      (ptrBase : Nat),
      let w := packWordColumns ordResH hWidth
      let D := ((w.dictionary[0]?).map Fin.val).getD 0
      PaperB.RamForestProgram.RawBuild.SerializedProperLossIndex (S.ramQuotient d) w ∧
      w.wordCount ≤ 19 * n_d ∧
      forestArenaBase loopBase n m ≤ ptrBase ∧
      ptrBase + w.wordCount ≤ forestArenaBase loopBase n m + forestUsed ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val]?).map Fin.val = some ptrBase ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 1]?).map Fin.val = some (ptrBase + (1 + 3 * D)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 2]?).map Fin.val = some (ptrBase + (1 + 3 * D) + (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 3]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1)) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 4]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d) ∧
      (data[ownerForestPtrsBase loopBase n m + 6 * d.val + 5]?).map Fin.val = some (ptrBase + (1 + 3 * D) + 2 * (n_d + 1) + n_d + w.entry.size) ∧
      (∀ k < w.wordCount, data[ptrBase + k]? = (packedPayload w)[k]?)

theorem ownerForestPackedRecord_to_record {bits : Nat} {mem : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {S : StaticTreeSlice mem treeBase g r dense} {d : Fin dense.length}
    {loopBase n m forestUsed : Nat} {data : Array (Word bits)}
    (h : OwnerForestPackedRecord S d loopBase n m forestUsed data) :
    OwnerForestRecordAt S d loopBase n m forestUsed data := by
  dsimp only [OwnerForestPackedRecord] at h
  dsimp only [OwnerForestRecordAt]
  by_cases hSm : 1 + (S.childSlice d).length < 3
  · rw [ite_eq_left hSm] at h ⊢
    exact h
  · rw [ite_eq_right hSm] at h ⊢
    rcases h with ⟨pH, dataH, sizeH, rankH, hlarge, incH, covH, rArcH, ordResH, hWidth, ptrBase, hRest⟩
    exact ⟨packWordColumns ordResH hWidth, ptrBase, hRest⟩

private theorem ownerForestPackedRecord_ofMemEq {bits : Nat}
    {mem₁ mem₂ : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem₁ treeBase g r dense)
    (hSz : mem₂.size = mem₁.size)
    (hPres : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords dense.length → mem₂[k]? = mem₁[k]?)
    {d : Fin dense.length} {loopBase n m forestUsed : Nat}
    {data₁ data₂ : Array (Word bits)} (hData : data₂ = data₁)
    (h : OwnerForestPackedRecord S d loopBase n m forestUsed data₁) :
    OwnerForestPackedRecord (S.ofMemEq hSz hPres) d loopBase n m forestUsed data₂ := by
  subst hData
  exact h

/-- **EX5.1 Unified Prefix + Emitter + Family Forest Loop Specification**:
From raw outgoing-CSR input `RawDagInput input g r` on any acyclic `g` with source `r`
and linear workspace `512 * (n + m + 1) ≤ workCap < 2 ^ bits`, the single fixed
16-register program `prefixAndForestLoopProgram hi hw h32` halts cleanly in
`steps ≤ 100000 * ((n + m + 1) * (OracleContract.L n)^2)` operations with peak live
words `inputCap + workCap + 16`, preserving `[3*n..5*n)` reachability maps and
`[treeBase..treeBase + 11*Q)` (`StaticTreeSlice`), keeping `qStartFn` and
`countingSortedArcs` in `emitBase`, and producing `OwnerForestRecordAt` for every
owner `d : Fin Q` with `forestUsed ≤ 38 * n`. -/
theorem h32OfCap {n m workCap bits : Nat} (hn : 1 ≤ n)
    (hCap : 512 * (n + m + 1) ≤ workCap) (hBits : workCap < 2 ^ bits) : 32 ≤ 2 ^ bits :=
  Nat.le_of_lt (Nat.lt_of_le_of_lt
    (Nat.le_trans (by decide : 32 ≤ 512 * 1)
      (Nat.mul_le_mul_left 512 (Nat.le_trans hn (Nat.le_trans (Nat.le_add_right n m) (Nat.le_succ _)))))
    (Nat.lt_of_le_of_lt hCap hBits))

private theorem staticTreeSlice_ofMemEq_eq {bits : Nat}
    {mem₁ mem₂ : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    (S : StaticTreeSlice mem₁ treeBase g r dense)
    (hSz : mem₂.size = mem₁.size)
    (hPres : ∀ k, treeBase ≤ k → k < treeBase + staticTreeWords dense.length → mem₂[k]? = mem₁[k]?) :
    (S.ofMemEq hSz hPres).childSlice = S.childSlice ∧
    (S.ofMemEq hSz hPres).ramQuotient = S.ramQuotient ∧
    (S.ofMemEq hSz hPres).emittedArcs = S.emittedArcs ∧
    qStartFn (S.ofMemEq hSz hPres) = qStartFn S :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem ownerForestRecordAt_transfer {bits : Nat}
    {mem₁ mem₂ : Array (Word bits)} {treeBase : Nat}
    {g : Digraph} {r : Fin g.vertexCount} {dense : List (Fin g.vertexCount)}
    {S₁ : StaticTreeSlice mem₁ treeBase g r dense}
    {S₂ : StaticTreeSlice mem₂ treeBase g r dense}
    (hChild : S₂.childSlice = S₁.childSlice)
    (hQuot : S₂.ramQuotient = S₁.ramQuotient)
    {d : Fin dense.length} {loopBase n m forestUsed : Nat}
    {data₁ data₂ : Array (Word bits)} (hData : data₂ = data₁)
    (h : OwnerForestRecordAt S₁ d loopBase n m forestUsed data₁) :
    OwnerForestRecordAt S₂ d loopBase n m forestUsed data₂ := by
  subst hData
  dsimp only [OwnerForestRecordAt] at h ⊢
  rw [hChild, hQuot]
  exact h

private theorem run_prefix_emit_mid {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (hCap : 512 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits)
    (s₀ : State (layout16 bits inputCap workCap hi hw)) :
    ∃ (tPref tMid : State (layout16 bits inputCap workCap hi hw))
      (kPref stepsEmit : Nat)
      (order : List (Fin g.vertexCount)) (_hlen : order.length = g.vertexCount)
      (hTopo : g.IsTopologicalList order),
      let dense := denseVertices g r order hTopo
      let Q := dense.length
      ∃ (S₀ : StaticTreeSlice tPref.data (prefixTreeBase workCap) g r dense),
        tPref.data.size = workCap ∧
        tPref.pc = (buildPrefixProgram hi hw (hTenOf32 h32)).size - 1 ∧
        Steps (buildPrefixProgram hi hw (hTenOf32 h32)) input kPref (Phase.initial s₀) tPref ∧
        kPref + 1 ≤ 4326 * (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2 ∧
        stepsEmit ≤ 128 * (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ∧
        run (midEmitPhase (hi := hi) (hw := hw) h32).code input (8 + (stepsEmit + 2)) (Phase.initial tPref) =
          some ⟨tMid, 8 + (stepsEmit + 2)⟩ ∧
        (dense[0]'(denseVertices_length_pos g r order hTopo)) = r ∧
        (∀ i : Nat, (hi₁ : i < Q) → g.InitiallyReachable r (dense[i]'hi₁)) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (tPref.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val =
            some (dense[i]'hi₁).val) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (tPref.data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi₁).val]?).map Fin.val =
            some (i + 1)) ∧
        (∀ v : Fin g.vertexCount, ¬ g.InitiallyReachable r v →
          (tPref.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val = some 0) ∧
        MatchesPackedLayout S₀ ∧
        (∀ d : Fin Q, (S₀.ramQuotient d).IsFlat) ∧
        LoopEntryRegs g.vertexCount g.arcCount r.val Q
          (prefixTreeBase workCap) (emitBaseOf workCap) (loopBaseOf workCap) tMid ∧
        (∀ k, prefixTreeBase workCap ≤ k → k < prefixTreeBase workCap + staticTreeWords Q →
          tMid.data[k]? = tPref.data[k]?) ∧
        (∀ j ≤ Q, (tMid.data[emitBaseOf workCap + 2 * g.vertexCount + j]?).map Fin.val =
          some (qStartFn S₀ j)) ∧
        (∀ (d : Fin Q) (p : Nat) (hp : p < (S₀.emittedArcs d).length),
          let ea := (S₀.emittedArcs d)[p]'hp
          (tMid.data[emitBaseOf workCap + 3 * g.vertexCount + 1 + (qStartFn S₀ d.val + p)]?).map Fin.val =
            some ea.srcLocal ∧
          (tMid.data[emitBaseOf workCap + 3 * g.vertexCount + g.arcCount + 1 + (qStartFn S₀ d.val + p)]?).map Fin.val =
            some ea.headLocal ∧
          (tMid.data[emitBaseOf workCap + 3 * g.vertexCount + 2 * g.arcCount + 1 + (qStartFn S₀ d.val + p)]?).map Fin.val =
            some ea.tailEntry) ∧
        (∀ addr, addr < emitBaseOf workCap → tMid.data[addr]? = tPref.data[addr]?) := by
  have hTen : 10 ≤ 2 ^ bits := hTenOf32 h32
  have hQuarterGe : 128 * (g.vertexCount + g.arcCount + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  have hCap64 : 64 * (g.vertexCount + g.arcCount + 1) ≤ workCap := by omega
  obtain ⟨tPref, _, stepsPref, order, hlen, hTopo, _inSrc, _parent, _depth, hQPos,
      hStepsPrefLe, hRunPref, _, _, hr5Pref, hr6Pref, _, hQLe, hmLe, hHead, hReach,
      hDenseToOrigPref, hOrigToDensePref, hZeroPref, hDenseDigraph, hParSpec, hTree, _,
      hParLt, hMemPar, hMemDep, hMemHeavy, hMemHead, hMemEnt, hMemStop, hMemDofE,
      hMemCsr0, hMemCsrLast, hMemBuckets⟩ :=
    run_build_prefix input raw acyc hCap64 s₀
  obtain ⟨kPref, lastPref, hStepsLastPref, hLastPc⟩ :=
    buildPrefixProgram_halts_at_last input raw acyc hCap64 s₀
  have hRunLastPref :
      run (buildPrefixProgram hi hw hTen) input (kPref + 1) (Phase.initial s₀) =
        some ⟨lastPref, kPref + 1⟩ := by
    refine hStepsLastPref.halts (step_halt_at ?_)
    rw [hLastPc]
    exact buildPrefixProgram_last_halt hi hw hTen
  obtain ⟨hStepsPrefEq, hStateEq⟩ := run_add_step hRunLastPref hRunPref
  have htPrefPc : tPref.pc = (buildPrefixProgram hi hw hTen).size - 1 := by
    rw [← hStateEq]; exact hLastPc
  have hStepsLastPref' :
      Steps (buildPrefixProgram hi hw hTen) input kPref (Phase.initial s₀) tPref := by
    rw [← hStateEq]; exact hStepsLastPref
  have hPrefDsz : tPref.data.size = workCap := tPref.data_size
  have hTreeFitPref : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤ tPref.data.size := by
    rw [hPrefDsz]
    unfold prefixTreeBase staticTreeWords prefixQuarter
    have := hQLe
    omega
  let S₀ : StaticTreeSlice tPref.data (prefixTreeBase workCap) g r (denseVertices g r order hTopo) :=
    staticTreeSlice_of_prefix tPref.data (prefixTreeBase workCap) acyc hTreeFitPref hQPos hHead hReach
      hDenseDigraph hParSpec hTree hParLt hMemPar hMemDep
      (fun u => by
        rw [hMemHeavy u]
        apply congrArg some
        cases hOpt : (PackedStaticLayout.build (RamDomAndStaticTree.staticInput hQPos _parent _depth)).packed.heavy.read u <;> rfl)
      (fun v => by simpa only using hMemHead v)
      (fun v => by simpa only using hMemEnt v)
      (fun v => by simpa only using hMemStop v)
      (fun v => by simpa only using hMemDofE v)
      hMemCsr0 hMemCsrLast
      (fun u => by simpa only using hMemBuckets u)
  have hMatchS₀ : MatchesPackedLayout S₀ :=
    matchesPackedLayout_of_prefix (parent := _parent) (depth := _depth) S₀ hQPos rfl rfl
      (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) (fun _ => rfl) hMemBuckets
  have hFlatS₀ : ∀ d : Fin (denseVertices g r order hTopo).length, (S₀.ramQuotient d).IsFlat :=
    ramQuotient_isFlat_of_staticTreeSlice S₀ acyc
  have hEmitLt : emitBaseOf workCap < 2 ^ bits := by
    unfold emitBaseOf prefixQuarter; omega
  obtain ⟨tA1, hRunA1, hDataA1, hRegsA1⟩ :=
    run_adapter1 input raw (Q := (denseVertices g r order hTopo).length) (quarter := prefixQuarter workCap)
      (hEmitLt := hEmitLt) tPref hr5Pref hr6Pref
  have hA1SzEq : tA1.data.size = tPref.data.size := by rw [hDataA1]
  have hA1Pres : ∀ k, prefixTreeBase workCap ≤ k →
      k < prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length →
      tA1.data[k]? = tPref.data[k]? := fun k _ _ => by rw [hDataA1]
  let SA1 : StaticTreeSlice tA1.data (prefixTreeBase workCap) g r (denseVertices g r order hTopo) :=
    S₀.ofMemEq hA1SzEq hA1Pres
  have hDenseToOrigA1 : ∀ u' : Fin (denseVertices g r order hTopo).length,
      (tA1.data[denseToOrigBase g.vertexCount g.arcCount + u'.val]?).map Fin.val =
        some ((denseVertices g r order hTopo)[u'.val]'u'.isLt).val := by
    intro u'; rw [hDataA1]; exact hDenseToOrigPref u'.val u'.isLt
  have hOrigToDenseA1 : ∀ v : Fin g.vertexCount, g.InitiallyReachable r v →
      (tA1.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val =
        some ((denseVertices g r order hTopo).idxOf v + 1) := by
    intro v hv
    have hvMem : v ∈ denseVertices g r order hTopo := (denseVertices_mem_iff g r order hTopo v).mpr hv
    have hvIdxLt : (denseVertices g r order hTopo).idxOf v < (denseVertices g r order hTopo).length :=
      List.idxOf_lt_length_of_mem hvMem
    have hvGet : (denseVertices g r order hTopo)[(denseVertices g r order hTopo).idxOf v]'hvIdxLt = v :=
      List.getElem_idxOf hvIdxLt
    have hOrig := hOrigToDensePref ((denseVertices g r order hTopo).idxOf v) hvIdxLt
    rw [hDataA1]
    simpa only [hvGet] using hOrig
  have hFitEmitA1 : emitBaseOf workCap + emitterWorkWords g.vertexCount g.arcCount ≤ tA1.data.size := by
    rw [hDataA1, hPrefDsz]
    unfold emitBaseOf emitterWorkWords prefixQuarter
    omega
  have hDisjReachEmit : 5 * g.vertexCount ≤ emitBaseOf workCap := by
    unfold emitBaseOf; omega
  have hDisjTreeEmit : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤ emitBaseOf workCap ∨
      emitBaseOf workCap + emitterWorkWords g.vertexCount g.arcCount ≤ prefixTreeBase workCap := by
    left; unfold prefixTreeBase emitBaseOf staticTreeWords; omega
  obtain ⟨tEmit, _, stepsEmit, hStepsEmitLe, hRunEmit, _, _, hRegsEmit, _, _,
      hEmitFrame, _, hQStartsEmit, _, hArcsEmit⟩ :=
    run_quotient_emit input raw acyc hRegsA1 SA1 hDenseToOrigA1 hOrigToDenseA1
      hFitEmitA1 hDisjReachEmit hDisjTreeEmit
  have hLoopLt : loopBaseOf workCap < 2 ^ bits := by
    unfold loopBaseOf prefixQuarter; omega
  obtain ⟨tA2, hRunA2, hDataA2, hRegsA2⟩ :=
    run_adapter2 input (Q := (denseVertices g r order hTopo).length) (quarter := prefixQuarter workCap)
      hLoopLt tEmit hRegsEmit
  have hEmitPos : 0 < ((pipelinePhase (quotientEmitPhases (hi := hi) (hw := hw))).link
      (adapter2Phase (hi := hi) (hw := hw))).code.size := by
    have := ((pipelinePhase (quotientEmitPhases (hi := hi) (hw := hw))).link
      (adapter2Phase (hi := hi) (hw := hw))).haltFits
    omega
  have hA2Pos : 0 < (adapter2Phase (hi := hi) (hw := hw)).code.size :=
    (adapter2Phase (hi := hi) (hw := hw)).haltFits |> fun h => by omega
  have hRunEmit' :
      run (pipelinePhase (quotientEmitPhases (hi := hi) (hw := hw))).code
        input stepsEmit (Phase.initial tA1) = some ⟨tEmit, stepsEmit⟩ := by
    rw [pipelinePhase_code]; exact hRunEmit
  obtain ⟨tMid2, _, hMid2Regs, hMid2Data, hRunMid2, _, _⟩ :=
    run_linked_pair (pipelinePhase (quotientEmitPhases (hi := hi) (hw := hw)))
      (adapter2Phase (hi := hi) (hw := hw)).code hA2Pos hRunEmit' hRunA2
  obtain ⟨tMid, _, hMidRegs, hMidData, hRunMid, _, _⟩ :=
    run_linked_pair (adapter1Phase (hi := hi) (hw := hw) hTen)
      ((pipelinePhase (quotientEmitPhases (hi := hi) (hw := hw))).link
        (adapter2Phase (hi := hi) (hw := hw))).code
      hEmitPos hRunA1 hRunMid2
  have hMidDataEq : tMid.data = tEmit.data := hMidData.trans (hMid2Data.trans hDataA2)
  have hMidRegsEq : LoopEntryRegs g.vertexCount g.arcCount r.val (denseVertices g r order hTopo).length
      (prefixTreeBase workCap) (emitBaseOf workCap) (loopBaseOf workCap) tMid :=
    { consts :=
        { zero := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.consts.zero
          one := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.consts.one
          nVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.consts.nVal
          mVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.consts.mVal
          rootVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.consts.rootVal }
      qVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.qVal
      treeBaseVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.treeBaseVal
      emitBaseVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.emitBaseVal
      loopBaseVal := by rw [reg_eq_of_regs_eq hMidRegs, reg_eq_of_regs_eq hMid2Regs]; exact hRegsA2.loopBaseVal }
  have hkPrefBnd : kPref + 1 ≤ 4326 * (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2 := by
    rw [hStepsPrefEq]; exact hStepsPrefLe
  have hSA1 := staticTreeSlice_ofMemEq_eq S₀ hA1SzEq hA1Pres
  refine ⟨tPref, tMid, kPref, stepsEmit, order, hlen, hTopo, S₀,
    hPrefDsz, htPrefPc, hStepsLastPref', hkPrefBnd, hStepsEmitLe, hRunMid,
    hHead, hReach, hDenseToOrigPref, hOrigToDensePref, hZeroPref, hMatchS₀, hFlatS₀, hMidRegsEq,
    fun k hk1 hk2 => by
      rw [hMidDataEq, hEmitFrame k (by left; unfold prefixTreeBase staticTreeWords at hk2; omega), hDataA1],
    fun j hj => by rw [hMidDataEq]; exact hQStartsEmit j hj,
    fun d p hp => by
      rw [hMidDataEq]
      unfold emitBaseOf
      exact hArcsEmit d p hp,
    fun addr hLt => by rw [hMidDataEq, hEmitFrame addr (Or.inl hLt), hDataA1]⟩

private theorem run_prefix_and_forest_loop_aux {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (hCap : 512 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    (h32 : 32 ≤ 2 ^ bits)
    (s₀ : State (layout16 bits inputCap workCap hi hw)) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (trace : List (State (layout16 bits inputCap workCap hi hw)))
      (steps forestUsed : Nat)
      (order : List (Fin g.vertexCount)) (_hlen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order),
      let dense := denseVertices g r order hTopo
      let Q := dense.length
      ∃ (S : StaticTreeSlice t.data (prefixTreeBase workCap) g r dense),
        MatchesPackedLayout S ∧
        steps ≤ 100000 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) ∧
        run (prefixAndForestLoopProgram hi hw h32) input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
        SuccessfulTrace (prefixAndForestLoopProgram hi hw h32) input (Phase.initial s₀) trace ⟨t, steps⟩ ∧
        tracePeakWords input trace = inputCap + workCap + 16 ∧
        t.pc = (prefixAndForestLoopProgram hi hw h32).size - 1 ∧
        LoopIterRegs g.vertexCount g.arcCount r.val Q
          (prefixTreeBase workCap) (emitBaseOf workCap) (loopBaseOf workCap) Q forestUsed t ∧
        forestUsed ≤ 38 * g.vertexCount ∧
        t.data.size = workCap ∧
        (dense[0]'(denseVertices_length_pos g r order hTopo)) = r ∧
        (∀ i : Nat, (hi₁ : i < Q) → g.InitiallyReachable r (dense[i]'hi₁)) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (t.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val = some (dense[i]'hi₁).val) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (t.data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi₁).val]?).map Fin.val = some (i + 1)) ∧
        (∀ v : Fin g.vertexCount, ¬ g.InitiallyReachable r v →
          (t.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val = some 0) ∧
        (∀ j ≤ Q, (t.data[emitBaseOf workCap + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j)) ∧
        (∀ (d : Fin Q) (p : Nat) (hp : p < (S.emittedArcs d).length),
          let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(
            Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds d hx).2.1)).symm)
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + g.arcCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + 2 * g.arcCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) ∧
        (∀ d : Fin Q, OwnerForestPackedRecord S d (loopBaseOf workCap) g.vertexCount g.arcCount forestUsed t.data) ∧
        (∀ d : Fin Q, (S.ramQuotient d).IsFlat ∧ (S.ramQuotient d).IsAcyclic) := by
  have hnPos : 1 ≤ g.vertexCount := Fin.pos r
  have hTen : 10 ≤ 2 ^ bits := hTenOf32 h32
  have hQuarterGe : 128 * (g.vertexCount + g.arcCount + 1) ≤ prefixQuarter workCap := by
    unfold prefixQuarter
    exact Nat.le_div_iff_mul_le (by decide : 0 < 4) |>.mpr (by omega)
  obtain ⟨tPref, tMid, kPref, stepsEmit, order, hlen, hTopo, S₀,
      hPrefDsz, htPrefPc, hStepsLastPref', hkPrefBnd, hStepsEmitLe, hRunMid,
      hHead, hReach, hDenseToOrigPref, hOrigToDensePref, hZeroPref, hMatchS₀, hFlatS₀,
      hMidRegsEq, hTreeMemMid, hQStartsMid, hArcsMid, hMidPrePres⟩ :=
    run_prefix_emit_mid input raw acyc hCap hBits h32 s₀
  have hsi : PaperB.RamForestProgram.RawBuild.rawInputCap g.arcCount ≤ 2 ^ bits := by
    unfold PaperB.RamForestProgram.RawBuild.rawInputCap; omega
  have hsw : PaperB.RamForestProgram.RawBuild.rawWorkCap g.vertexCount g.arcCount ≤ 2 ^ bits := by
    unfold PaperB.RamForestProgram.RawBuild.rawWorkCap; omega
  have hTree3 : 3 ≤ prefixTreeBase workCap := by unfold prefixTreeBase; omega
  have hEmit3 : 3 ≤ emitBaseOf workCap := by unfold emitBaseOf; omega
  have hLoop3 : 3 ≤ loopBaseOf workCap := by unfold loopBaseOf; omega
  have hLoopFit : loopBaseOf workCap + loopWorkWords g.vertexCount g.arcCount ≤ workCap := by
    unfold loopBaseOf loopWorkWords prefixQuarter; omega
  have hTreeFitW : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤ workCap := by
    unfold prefixTreeBase staticTreeWords prefixQuarter
    have := S₀.length_le
    omega
  have hEmitFitW : emitBaseOf workCap + emitterWorkWords g.vertexCount g.arcCount ≤ workCap := by
    unfold emitBaseOf emitterWorkWords prefixQuarter; omega
  have hDisjTE : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤ emitBaseOf workCap ∨
      emitBaseOf workCap + emitterWorkWords g.vertexCount g.arcCount ≤ prefixTreeBase workCap := by
    left; unfold prefixTreeBase emitBaseOf staticTreeWords; have := S₀.length_le; omega
  have hDisjTL : prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length ≤ loopBaseOf workCap ∨
      loopBaseOf workCap + loopWorkWords g.vertexCount g.arcCount ≤ prefixTreeBase workCap := by
    left; unfold prefixTreeBase loopBaseOf staticTreeWords; have := S₀.length_le; omega
  have hDisjLE : loopBaseOf workCap + loopWorkWords g.vertexCount g.arcCount ≤ emitBaseOf workCap ∨
      emitBaseOf workCap + emitterWorkWords g.vertexCount g.arcCount ≤ loopBaseOf workCap := by
    right; unfold emitBaseOf loopBaseOf emitterWorkWords; omega
  obtain ⟨tLoop, _, stepsLoop, forestUsed, hStepsLoopLe, hRunLoop, _, _, hLoopPc,
      hRegsLoop, hForestUsedLe, hLoopDsz, hTreePresLoop, hQStartsLoop, hArcsLoop, hRecsLoop, hFrameLoop⟩ :=
    run_family_forest_loop_packed hsi hsw h32 input S₀ rfl rfl rfl acyc hFlatS₀
      hTree3 hEmit3 hLoop3 hLoopFit hTreeFitW hEmitFitW hDisjTE hDisjTL hDisjLE hBits
      hMidRegsEq hTreeMemMid hQStartsMid hArcsMid
  have hRunLoop' :
      run (familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32) input stepsLoop (Phase.initial tMid) =
        some ⟨tLoop, stepsLoop⟩ := by
    rw [familyForestLoopProgram_sub_indep hw hw hsi hsw h32]; exact hRunLoop
  have hLoopPc' :
      tLoop.pc = (familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32).size - 1 := by
    rw [← familyForestLoopProgram_sub_indep hw hw hsi hsw h32] at hLoopPc
    exact hLoopPc
  have hLoopProgPos : 0 < (familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32).size := by
    rw [familyForestLoopProgram_sub_indep hw hw hsi hsw h32]
    unfold familyForestLoopProgram
    rw [familyForestLoopCode_size]
    omega
  obtain ⟨tRight, _, hRightPc, hRightRegs, hRightData, hRunRight, _, _⟩ :=
    run_linked_pair_pc (midEmitPhase (hi := hi) (hw := hw) h32)
      (familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32)
      hLoopProgPos hRunMid hRunLoop'
  obtain ⟨tFinal, traceFinal, hFinalPc, hFinalRegs, hFinalData, hRunFinal, hTraceFinal, hPeakFinal⟩ :=
    run_join_at_last (buildPrefixProgram hi hw hTen) (rightAllCode hi hw h32)
      (buildPrefixProgram_last_lt hi hw hTen) (buildPrefixProgram_last_halt hi hw hTen)
      (rightAllCode_pos hi hw h32) hStepsLastPref' htPrefPc hRunRight
  have hPcFinal : tFinal.pc = (prefixAndForestLoopProgram hi hw h32).size - 1 := by
    have hPrefSz : (prefixAndForestLoopProgram hi hw h32).size =
        (buildPrefixProgram hi hw hTen).size + (rightAllCode hi hw h32).size := by
      unfold prefixAndForestLoopProgram join
      rw [Array.size_append, Array.size_set, Array.size_map]
    have hRightSz : (rightAllCode hi hw h32).size =
        (midEmitPhase (hi := hi) (hw := hw) h32).code.size +
          (familyForestLoopProgram (hi := hi) (hw := hw) hw hw h32).size := by
      unfold rightAllCode join
      rw [Array.size_append, Array.size_set, Array.size_map]
    have hPosRight : 0 < (rightAllCode hi hw h32).size := rightAllCode_pos hi hw h32
    rw [hFinalPc, hRightPc, hLoopPc', hPrefSz, hRightSz]
    omega
  have hFinalToLoopData : tFinal.data = tLoop.data := hFinalData.trans hRightData
  have hFinalDsz : tFinal.data.size = workCap := by rw [hFinalToLoopData, hLoopDsz]
  have hFinalSzEq : tFinal.data.size = tPref.data.size := by rw [hFinalDsz, hPrefDsz]
  have hFinalTreePres : ∀ k, prefixTreeBase workCap ≤ k →
      k < prefixTreeBase workCap + staticTreeWords (denseVertices g r order hTopo).length →
      tFinal.data[k]? = tPref.data[k]? := by
    intro k hk1 hk2; rw [hFinalToLoopData]; exact hTreePresLoop k hk1 hk2
  have hSEq := staticTreeSlice_ofMemEq_eq S₀ hFinalSzEq hFinalTreePres
  let SFinal : StaticTreeSlice tFinal.data (prefixTreeBase workCap) g r (denseVertices g r order hTopo) :=
    S₀.ofMemEq hFinalSzEq hFinalTreePres
  have hReach35Pres : ∀ addr, 3 * g.vertexCount ≤ addr → addr < 5 * g.vertexCount →
      tFinal.data[addr]? = tPref.data[addr]? := by
    intro addr hLo hHi
    rw [hFinalToLoopData]
    have hFrame : tLoop.data[addr]? = tMid.data[addr]? :=
      hFrameLoop addr
        (by unfold inPtrAddr; omega)
        (by unfold dataPtrAddr; omega)
        (by unfold statePtrAddr; omega)
        (by left; unfold emitBaseOf; omega)
        (by left; unfold loopBaseOf; omega)
    rw [hFrame, hMidPrePres addr (by unfold emitBaseOf; omega)]
  have hLPos : 1 ≤ OracleContract.L g.vertexCount := OracleContract.one_le_L g.vertexCount
  have hLSqPos : 1 ≤ OracleContract.L g.vertexCount ^ 2 := by
    simpa only [Nat.pow_two] using Nat.mul_le_mul hLPos hLPos
  have hPrefN : kPref + 1 ≤ 4326 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := by
    rw [← Nat.mul_assoc]; exact hkPrefBnd
  have hEmitN : stepsEmit ≤ 128 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := by
    have h0 := Nat.le_mul_of_pos_right stepsEmit hLPos
    have h1 := Nat.le_trans h0 (Nat.mul_le_mul_right (OracleContract.L g.vertexCount) hStepsEmitLe)
    rw [Nat.mul_assoc (128 * (g.vertexCount + g.arcCount + 1)), ← Nat.pow_two, Nat.mul_assoc] at h1
    exact h1
  have hLoopN : stepsLoop ≤ 94500 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := hStepsLoopLe
  have hA1N : (8 : Nat) ≤ 8 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := by
    have h1 : 1 ≤ (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2 := Nat.mul_pos (by omega) hLSqPos
    exact Nat.le_trans (by omega : 8 ≤ 8 * 1) (Nat.mul_le_mul_left 8 h1)
  have hA2N : (2 : Nat) ≤ 2 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := by
    have h1 : 1 ≤ (g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2 := Nat.mul_pos (by omega) hLSqPos
    exact Nat.le_trans (by omega : 2 ≤ 2 * 1) (Nat.mul_le_mul_left 2 h1)
  have hTotalBound : kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop) ≤
      100000 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := by
    have hSum : kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop) ≤
        (4326 + (8 + (128 + 2) + 94500)) * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) := by
      have hComb := Nat.add_le_add hPrefN
        (Nat.add_le_add (Nat.add_le_add hA1N (Nat.add_le_add hEmitN hA2N)) hLoopN)
      simpa only [← Nat.add_mul] using hComb
    exact Nat.le_trans hSum (Nat.mul_le_mul_right _ (by decide))
  have hRunFinal' :
      run (prefixAndForestLoopProgram hi hw h32) input
        (kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop)) (Phase.initial s₀) =
        some ⟨tFinal, kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop)⟩ := by
    change run (join (buildPrefixProgram hi hw hTen) (rightAllCode hi hw h32)
        ((buildPrefixProgram hi hw hTen).size - 1) (buildPrefixProgram_last_lt hi hw hTen))
      input (kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop)) (Phase.initial s₀) =
      some ⟨tFinal, kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop)⟩
    exact hRunFinal
  have hTraceFinal' :
      SuccessfulTrace (prefixAndForestLoopProgram hi hw h32) input (Phase.initial s₀) traceFinal
        ⟨tFinal, kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop)⟩ := by
    change SuccessfulTrace (join (buildPrefixProgram hi hw hTen) (rightAllCode hi hw h32)
        ((buildPrefixProgram hi hw hTen).size - 1) (buildPrefixProgram_last_lt hi hw hTen))
      input (Phase.initial s₀) traceFinal
      ⟨tFinal, kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop)⟩
    exact hTraceFinal
  have hPeakFinal' : tracePeakWords input traceFinal = inputCap + workCap + 16 := by
    simpa only [footprint, layout16] using hPeakFinal
  have hRegsFinal : LoopIterRegs g.vertexCount g.arcCount r.val (denseVertices g r order hTopo).length
      (prefixTreeBase workCap) (emitBaseOf workCap) (loopBaseOf workCap) (denseVertices g r order hTopo).length forestUsed tFinal :=
    { entry :=
        { consts :=
            { zero := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.consts.zero
              one := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.consts.one
              nVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.consts.nVal
              mVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.consts.mVal
              rootVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.consts.rootVal }
          qVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.qVal
          treeBaseVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.treeBaseVal
          emitBaseVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.emitBaseVal
          loopBaseVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.entry.loopBaseVal }
      dVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.dVal
      usedVal := by rw [reg_eq_of_regs_eq hFinalRegs, reg_eq_of_regs_eq hRightRegs]; exact hRegsLoop.usedVal }
  have hDenseToOrigFinal : ∀ i : Nat, (hi₁ : i < (denseVertices g r order hTopo).length) →
      (tFinal.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val =
        some ((denseVertices g r order hTopo)[i]'hi₁).val := by
    intro i hi₁
    have hLo : 3 * g.vertexCount ≤ denseToOrigBase g.vertexCount g.arcCount + i := by
      unfold denseToOrigBase; omega
    have hHi : denseToOrigBase g.vertexCount g.arcCount + i < 5 * g.vertexCount := by
      unfold denseToOrigBase; have := S₀.length_le; omega
    rw [hReach35Pres _ hLo hHi]; exact hDenseToOrigPref i hi₁
  have hOrigToDenseFinal : ∀ i : Nat, (hi₁ : i < (denseVertices g r order hTopo).length) →
      (tFinal.data[origToDensePlusOneBase g.vertexCount g.arcCount +
          ((denseVertices g r order hTopo)[i]'hi₁).val]?).map Fin.val = some (i + 1) := by
    intro i hi₁
    have hvLt := ((denseVertices g r order hTopo)[i]'hi₁).isLt
    have hLo : 3 * g.vertexCount ≤ origToDensePlusOneBase g.vertexCount g.arcCount +
        ((denseVertices g r order hTopo)[i]'hi₁).val := by unfold origToDensePlusOneBase; omega
    have hHi : origToDensePlusOneBase g.vertexCount g.arcCount +
        ((denseVertices g r order hTopo)[i]'hi₁).val < 5 * g.vertexCount := by unfold origToDensePlusOneBase; omega
    rw [hReach35Pres _ hLo hHi]; exact hOrigToDensePref i hi₁
  have hZeroFinal : ∀ v : Fin g.vertexCount, ¬ g.InitiallyReachable r v →
      (tFinal.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val = some 0 := by
    intro v hv
    have hvLt := v.isLt
    have hLo : 3 * g.vertexCount ≤ origToDensePlusOneBase g.vertexCount g.arcCount + v.val := by
      unfold origToDensePlusOneBase; omega
    have hHi : origToDensePlusOneBase g.vertexCount g.arcCount + v.val < 5 * g.vertexCount := by
      unfold origToDensePlusOneBase; omega
    rw [hReach35Pres _ hLo hHi]; exact hZeroPref v hv
  have hQStartsFinal : ∀ j ≤ (denseVertices g r order hTopo).length,
      (tFinal.data[emitBaseOf workCap + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn SFinal j) := by
    intro j hj
    have hTmp := hQStartsLoop j hj
    rw [← hSEq.2.2.2, ← hFinalToLoopData] at hTmp
    exact hTmp
  have hArcsFinal : ∀ (d : Fin (denseVertices g r order hTopo).length) (p : Nat)
      (hp : p < (SFinal.emittedArcs d).length),
      let ea := (countingSortedArcs (1 + (SFinal.childSlice d).length) (SFinal.emittedArcs d))[p]'(
        Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (SFinal.emittedArc_bounds d hx).2.1)).symm)
      (tFinal.data[emitBaseOf workCap + 3 * g.vertexCount + 1 + (qStartFn SFinal d.val + p)]?).map Fin.val = some ea.srcLocal ∧
      (tFinal.data[emitBaseOf workCap + 3 * g.vertexCount + g.arcCount + 1 + (qStartFn SFinal d.val + p)]?).map Fin.val = some ea.headLocal ∧
      (tFinal.data[emitBaseOf workCap + 3 * g.vertexCount + 2 * g.arcCount + 1 + (qStartFn SFinal d.val + p)]?).map Fin.val = some ea.tailEntry := by
    intro d p hp
    have hp0 : p < (S₀.emittedArcs d).length := by rw [← hSEq.2.2.1]; exact hp
    simpa only [SFinal, hFinalToLoopData, hSEq.1, hSEq.2.2.1, hSEq.2.2.2] using hArcsLoop d p hp0
  have hMatchFinal : MatchesPackedLayout SFinal :=
    matchesPackedLayout_ofMemEq hMatchS₀ hFinalSzEq hFinalTreePres
  have hRecsFinal : ∀ d : Fin (denseVertices g r order hTopo).length,
      OwnerForestPackedRecord SFinal d (loopBaseOf workCap) g.vertexCount g.arcCount forestUsed tFinal.data :=
    fun d => ownerForestPackedRecord_ofMemEq S₀ hFinalSzEq hFinalTreePres hFinalToLoopData (hRecsLoop d)
  have hQuotFinal : ∀ d : Fin (denseVertices g r order hTopo).length,
      (SFinal.ramQuotient d).IsFlat ∧ (SFinal.ramQuotient d).IsAcyclic :=
    fun d => ⟨hSEq.2.1 ▸ hFlatS₀ d, SFinal.ramQuotient_isAcyclic acyc d⟩
  exact ⟨tFinal, traceFinal, kPref + 1 + (8 + (stepsEmit + 2) + stepsLoop), forestUsed,
    order, hlen, hTopo, SFinal, hMatchFinal, hTotalBound, hRunFinal', hTraceFinal', hPeakFinal',
    hPcFinal, hRegsFinal, hForestUsedLe, hFinalDsz, hHead, hReach,
    hDenseToOrigFinal, hOrigToDenseFinal, hZeroFinal, hQStartsFinal, hArcsFinal, hRecsFinal, hQuotFinal⟩

/-- Packed-witness variant of `run_prefix_and_forest_loop` exposing `MatchesPackedLayout S`,
`t.pc = code.size - 1`, and `OwnerForestPackedRecord S d ...` for every owner `d`. -/
theorem run_prefix_and_forest_loop_packed {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (hCap : 512 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    (s₀ : State (layout16 bits inputCap workCap hi hw)) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (trace : List (State (layout16 bits inputCap workCap hi hw)))
      (steps forestUsed : Nat)
      (order : List (Fin g.vertexCount)) (_hlen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order),
      let dense := denseVertices g r order hTopo
      let Q := dense.length
      ∃ (S : StaticTreeSlice t.data (prefixTreeBase workCap) g r dense),
        MatchesPackedLayout S ∧
        steps ≤ 100000 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) ∧
        run (prefixAndForestLoopProgram hi hw (h32OfCap (Fin.pos r) hCap hBits)) input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
        SuccessfulTrace (prefixAndForestLoopProgram hi hw (h32OfCap (Fin.pos r) hCap hBits)) input (Phase.initial s₀) trace ⟨t, steps⟩ ∧
        tracePeakWords input trace = inputCap + workCap + 16 ∧
        t.pc = (prefixAndForestLoopProgram hi hw (h32OfCap (Fin.pos r) hCap hBits)).size - 1 ∧
        LoopIterRegs g.vertexCount g.arcCount r.val Q
          (prefixTreeBase workCap) (emitBaseOf workCap) (loopBaseOf workCap) Q forestUsed t ∧
        forestUsed ≤ 38 * g.vertexCount ∧
        t.data.size = workCap ∧
        (dense[0]'(denseVertices_length_pos g r order hTopo)) = r ∧
        (∀ i : Nat, (hi₁ : i < Q) → g.InitiallyReachable r (dense[i]'hi₁)) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (t.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val = some (dense[i]'hi₁).val) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (t.data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi₁).val]?).map Fin.val = some (i + 1)) ∧
        (∀ v : Fin g.vertexCount, ¬ g.InitiallyReachable r v →
          (t.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val = some 0) ∧
        (∀ j ≤ Q, (t.data[emitBaseOf workCap + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j)) ∧
        (∀ (d : Fin Q) (p : Nat) (hp : p < (S.emittedArcs d).length),
          let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(
            Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds d hx).2.1)).symm)
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + g.arcCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + 2 * g.arcCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) ∧
        (∀ d : Fin Q, OwnerForestPackedRecord S d (loopBaseOf workCap) g.vertexCount g.arcCount forestUsed t.data) ∧
        (∀ d : Fin Q, (S.ramQuotient d).IsFlat ∧ (S.ramQuotient d).IsAcyclic) :=
  run_prefix_and_forest_loop_aux input raw acyc hCap hBits (h32OfCap (Fin.pos r) hCap hBits) s₀

theorem run_prefix_and_forest_loop {bits inputCap workCap : Nat}
    {hi : inputCap ≤ 2 ^ bits} {hw : workCap ≤ 2 ^ bits}
    (input : Input (layout16 bits inputCap workCap hi hw))
    {g : Digraph} {r : Fin g.vertexCount}
    (raw : RawDagInput input g r) (acyc : g.IsAcyclic)
    (hCap : 512 * (g.vertexCount + g.arcCount + 1) ≤ workCap)
    (hBits : workCap < 2 ^ bits)
    (s₀ : State (layout16 bits inputCap workCap hi hw)) :
    ∃ (t : State (layout16 bits inputCap workCap hi hw))
      (trace : List (State (layout16 bits inputCap workCap hi hw)))
      (steps forestUsed : Nat)
      (order : List (Fin g.vertexCount)) (_hlen : order.length = g.vertexCount) (hTopo : g.IsTopologicalList order),
      let dense := denseVertices g r order hTopo
      let Q := dense.length
      ∃ (S : StaticTreeSlice t.data (prefixTreeBase workCap) g r dense),
        steps ≤ 100000 * ((g.vertexCount + g.arcCount + 1) * OracleContract.L g.vertexCount ^ 2) ∧
        run (prefixAndForestLoopProgram hi hw (h32OfCap (Fin.pos r) hCap hBits)) input steps (Phase.initial s₀) = some ⟨t, steps⟩ ∧
        SuccessfulTrace (prefixAndForestLoopProgram hi hw (h32OfCap (Fin.pos r) hCap hBits)) input (Phase.initial s₀) trace ⟨t, steps⟩ ∧
        tracePeakWords input trace = inputCap + workCap + 16 ∧
        LoopIterRegs g.vertexCount g.arcCount r.val Q
          (prefixTreeBase workCap) (emitBaseOf workCap) (loopBaseOf workCap) Q forestUsed t ∧
        forestUsed ≤ 38 * g.vertexCount ∧
        t.data.size = workCap ∧
        (dense[0]'(denseVertices_length_pos g r order hTopo)) = r ∧
        (∀ i : Nat, (hi₁ : i < Q) → g.InitiallyReachable r (dense[i]'hi₁)) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (t.data[denseToOrigBase g.vertexCount g.arcCount + i]?).map Fin.val = some (dense[i]'hi₁).val) ∧
        (∀ i : Nat, (hi₁ : i < Q) →
          (t.data[origToDensePlusOneBase g.vertexCount g.arcCount + (dense[i]'hi₁).val]?).map Fin.val = some (i + 1)) ∧
        (∀ v : Fin g.vertexCount, ¬ g.InitiallyReachable r v →
          (t.data[origToDensePlusOneBase g.vertexCount g.arcCount + v.val]?).map Fin.val = some 0) ∧
        (∀ j ≤ Q, (t.data[emitBaseOf workCap + 2 * g.vertexCount + j]?).map Fin.val = some (qStartFn S j)) ∧
        (∀ (d : Fin Q) (p : Nat) (hp : p < (S.emittedArcs d).length),
          let ea := (countingSortedArcs (1 + (S.childSlice d).length) (S.emittedArcs d))[p]'(
            Nat.lt_of_lt_of_eq hp (countingSortedArcs_length _ (fun _ hx => (S.emittedArc_bounds d hx).2.1)).symm)
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.srcLocal ∧
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + g.arcCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.headLocal ∧
          (t.data[emitBaseOf workCap + 3 * g.vertexCount + 2 * g.arcCount + 1 + (qStartFn S d.val + p)]?).map Fin.val = some ea.tailEntry) ∧
        (∀ d : Fin Q, OwnerForestRecordAt S d (loopBaseOf workCap) g.vertexCount g.arcCount forestUsed t.data) ∧
        (∀ d : Fin Q, (S.ramQuotient d).IsFlat ∧ (S.ramQuotient d).IsAcyclic) := by
  obtain ⟨t, trace, steps, forestUsed, order, hlen, hTopo, S,
      _, hSteps, hRun, hTrace, hPeak, _, hRegs, hFu, hSz, hHead, hReach,
      hD2O, hO2D, hZero, hQS, hArcs, hRecs, hQuot⟩ :=
    run_prefix_and_forest_loop_packed input raw acyc hCap hBits s₀
  exact ⟨t, trace, steps, forestUsed, order, hlen, hTopo, S,
    hSteps, hRun, hTrace, hPeak, hRegs, hFu, hSz, hHead, hReach,
    hD2O, hO2D, hZero, hQS, hArcs, fun d => ownerForestPackedRecord_to_record (hRecs d), hQuot⟩

end EndToEnd

end PaperB.RamPrefixAndForestLoop
